"""
Custom ProverInterface that converts pre-computed patches into the XML format
expected by the VeriSoftBench evaluation pipeline.

Patches are fetched from the AlephProver API using request IDs stored in
a results JSON file. GPT-5.4 then extracts proof body + auxiliary lemmas.
"""

import os
import json
import time
import subprocess
from pathlib import Path
from typing import Dict, Any, List, Optional
from datetime import datetime

import openai

from core.prover_interface import ProverInterface
from config.paths import PROJECT_ROOT, get_debug_prompt_dir, get_debug_output_dir


EXTRACTION_SYSTEM_PROMPT = """\
You are a Lean 4 proof extraction assistant. You will be given:
1. A git diff (patch) that modifies a Lean 4 source file to prove a theorem.
2. The theorem name and statement that was proved.
3. The verification context (the code that appears BEFORE the theorem in the source file).

Your job is to extract:
- The proof body for the target theorem.
- Any auxiliary declarations needed for the proof that are NOT already in the verification context.

Rules for the PROOF BODY:
- The "proof body" is everything after the `:=` (or `where`, or `by`) in the target theorem.
  Include the leading `by` or `where` keyword if the proof uses tactic mode or where-bindings.
- Do NOT include the theorem signature in the proof body — only the proof itself.

Rules for AUXILIARY LEMMAS:
- Include any new `theorem`, `lemma`, `def`, `instance`, `abbrev`, `private def`, or
  `noncomputable def` declarations that the proof depends on and that are NOT already present
  in the verification context.
- This includes declarations that were ADDED by the patch (lines starting with `+`).
- This also includes declarations that already exist in the original file but appear AFTER
  the target theorem. If the new proof references a function/lemma that exists in the file
  but comes after the theorem, you MUST include it as an auxiliary lemma so it's available
  during verification.
- Also include any new `open` or `set_option` or `attribute` statements that were added.

Rules for OUTPUT FORMAT:
- CRITICAL: Output clean Lean 4 code. Do NOT include diff markers like `+` or `-` at the
  beginning of lines. Strip ALL diff prefixes. The output must be valid Lean 4 syntax.
- Do NOT put `import` statements in auxiliary lemmas (they are handled separately).
- If there are no auxiliary lemmas, leave that section empty.

Output format (use these exact XML tags):
<lean4_invented_lemmas>
(auxiliary lemmas here, or empty)
</lean4_invented_lemmas>
<lean4_proof>
(proof body here)
</lean4_proof>
"""


class PatchProverInterface(ProverInterface):
    """
    ProverInterface that fetches patches from AlephProver API and uses
    GPT-5.4 to extract proofs in the XML format the benchmark expects.
    """

    def __init__(self, model_config: Dict[str, Any]):
        # Override model_name to openai for the extraction call
        model_config = dict(model_config)
        model_config["model_name"] = "openai"
        model_config["model_id"] = model_config.get("extraction_model_id", "gpt-5.4")
        if not model_config.get("api_key"):
            model_config["api_key"] = os.environ.get("OPENAI_API_KEY")

        super().__init__(model_config)

        self.results_path = Path(model_config.get("results_json"))
        self.patches_dir = Path(model_config.get("patches_dir"))

        # Load results to map task_id -> request metadata
        with open(self.results_path) as f:
            results = json.load(f)
        self.results_by_id = {r["task_id"]: r for r in results}

        # Build thm_name -> task_id mapping
        self.thm_to_task = {}
        for r in results:
            self.thm_to_task[r["thm_name"]] = r["task_id"]

        # Docker container name for reading source files
        self.docker_container = model_config.get("docker_container", "verisoftbench-lean")

        # Caches
        self._extraction_cache: Dict[int, str] = {}

    # ------------------------------------------------------------------
    # Patch loading
    # ------------------------------------------------------------------

    def _get_patch(self, task_id: int) -> Optional[str]:
        """Load patch from local disk. Run download_patches.py first."""
        patch_file = self.patches_dir / f"task_{task_id:03d}.patch"
        if patch_file.exists():
            return patch_file.read_text()
        return None

    # ------------------------------------------------------------------
    # Source file helpers
    # ------------------------------------------------------------------

    def _read_file_from_docker(self, lean_root: str, rel_path: str) -> Optional[str]:
        """Read a source file from the Docker container."""
        container_path = f"/workspace/lean_repos/{lean_root}/{rel_path}"
        try:
            result = subprocess.run(
                ["docker", "exec", self.docker_container, "cat", container_path],
                capture_output=True, text=True, timeout=10
            )
            if result.returncode == 0:
                return result.stdout
        except Exception:
            pass
        return None

    def _get_post_theorem_code(self, lean_root: str, rel_path: str, thm_name: str) -> str:
        """Get code that appears AFTER the target theorem in the source file."""
        full_file = self._read_file_from_docker(lean_root, rel_path)
        if not full_file:
            return ""

        simple_name = thm_name.rsplit('.', 1)[-1]
        lines = full_file.split('\n')

        thm_start = -1
        for i, line in enumerate(lines):
            stripped = line.strip()
            if any(stripped.startswith(f"{kw} {simple_name}")
                   for kw in ("theorem", "lemma", "def", "private theorem", "private lemma")):
                thm_start = i
                break

        if thm_start < 0:
            return ""

        # Find end of the theorem
        thm_end = len(lines)
        indent_level = len(lines[thm_start]) - len(lines[thm_start].lstrip())
        for i in range(thm_start + 1, len(lines)):
            stripped = lines[i].strip()
            if not stripped:
                continue
            current_indent = len(lines[i]) - len(lines[i].lstrip())
            if current_indent <= indent_level and any(
                stripped.startswith(kw) for kw in
                ("theorem ", "lemma ", "def ", "noncomputable ", "instance ",
                 "abbrev ", "private ", "end ", "section ", "namespace ",
                 "open ", "set_option ", "attribute ", "#", "@[")
            ):
                thm_end = i
                break

        post_lines = lines[thm_end:]
        if len(post_lines) > 300:
            post_lines = post_lines[:300]
        return '\n'.join(post_lines)

    def _extract_new_imports(self, patch: str, verif_context: str) -> List[str]:
        """Extract import statements added by the patch but not in the verification context."""
        existing_imports = set()
        for line in verif_context.split('\n'):
            stripped = line.strip()
            if stripped.startswith('import '):
                existing_imports.add(stripped)

        new_imports = []
        for line in patch.split('\n'):
            if line.startswith('+') and not line.startswith('+++'):
                content = line[1:].strip()
                if content.startswith('import ') and content not in existing_imports:
                    new_imports.append(content)
                    existing_imports.add(content)

        return new_imports

    # ------------------------------------------------------------------
    # GPT extraction
    # ------------------------------------------------------------------

    def _extract_proof_from_patch(
        self, patch: str, thm_name: str, thm_stmt: str,
        verif_context: str = "",
        post_theorem_code: str = ""
    ) -> str:
        """Use GPT to extract proof body and aux lemmas from a patch."""
        context_section = ""
        if verif_context:
            ctx_lines = verif_context.strip().split('\n')
            if len(ctx_lines) > 200:
                ctx_lines = ctx_lines[-200:]
            context_section = f"""## Verification context (code BEFORE the theorem — already available)
```lean4
{chr(10).join(ctx_lines)}
```

"""

        post_section = ""
        if post_theorem_code:
            post_section = f"""## Code AFTER the theorem in the original file (NOT available during verification — copy anything the proof needs)
```lean4
{post_theorem_code}
```

"""

        user_prompt = f"""## Theorem name
{thm_name}

## Theorem statement
{thm_stmt}

{context_section}{post_section}## Git patch
```diff
{patch}
```

Extract the proof body and auxiliary lemmas from this patch for the theorem above.

IMPORTANT:
- Any definition, lemma, or theorem used in the new proof that is NOT in the verification context must be included as an auxiliary lemma.
- If the proof uses definitions from the "Code AFTER" section, copy them verbatim into auxiliary lemmas.
- Do NOT put `import` statements in auxiliary lemmas. Only include Lean declarations (theorem, lemma, def, etc.).
- Output clean Lean 4 code without diff markers (`+`/`-`).
"""
        self.rate_limiter.acquire()

        max_retries = 3
        for attempt in range(max_retries):
            try:
                response = self.client.responses.create(
                    model=self.model_id,
                    input=EXTRACTION_SYSTEM_PROMPT + "\n\n" + user_prompt,
                    reasoning={"effort": "xhigh"},
                )
                return response.output_text
            except Exception as e:
                if attempt < max_retries - 1:
                    print(f"  GPT extraction failed (attempt {attempt+1}): {e}")
                    time.sleep(2 ** attempt)
                else:
                    print(f"  GPT extraction failed after {max_retries} attempts: {e}")
                    raise

    # ------------------------------------------------------------------
    # Main interface
    # ------------------------------------------------------------------

    async def generate_proof(
        self,
        sys_prompt: str,
        user_prompt: str,
        theorem_entry: dict,
        max_tokens: int = 32768,
        temperature: float = 1.0,
        num_samples: int = 1
    ) -> List[str]:
        """
        Override: fetch the pre-computed patch from API, then use GPT
        to extract the proof in the expected XML format.
        """
        thm_name = theorem_entry.get("thm_name", "")
        thm_stmt = theorem_entry.get("thm_stmt", "")
        task_id = theorem_entry.get("id")

        if task_id is None:
            task_id = self.thm_to_task.get(thm_name)

        if task_id is None:
            print(f"  [PatchProver] No task_id found for {thm_name}, returning empty proof")
            return [self._empty_response()]

        # Fetch patch (API -> local disk fallback)
        patch = self._get_patch(task_id)
        if patch is None:
            result_entry = self.results_by_id.get(task_id, {})
            status = result_entry.get("status", "unknown")
            print(f"  [PatchProver] No patch for task {task_id} ({thm_name}), status={status}")
            return [self._empty_response()]

        # Check extraction cache
        if task_id in self._extraction_cache:
            print(f"  [PatchProver] Using cached extraction for task {task_id}")
            return [self._extraction_cache[task_id]]

        # Get verification context
        verif_context = theorem_entry.get("verif_local_ctxs", "")

        # Inject new imports from the patch
        new_imports = self._extract_new_imports(patch, verif_context)
        if new_imports:
            ctx_lines = verif_context.split('\n')
            last_import_idx = -1
            for i, line in enumerate(ctx_lines):
                if line.strip().startswith('import '):
                    last_import_idx = i
            if last_import_idx >= 0:
                for imp in reversed(new_imports):
                    ctx_lines.insert(last_import_idx + 1, imp)
            else:
                ctx_lines = new_imports + ctx_lines
            verif_context = '\n'.join(ctx_lines)
            theorem_entry['verif_local_ctxs'] = verif_context
            print(f"  [PatchProver] Added {len(new_imports)} new imports: {new_imports}")

        # Get post-theorem code for context
        lean_root = theorem_entry.get("lean_root", "")
        rel_path = theorem_entry.get("rel_path", "")
        post_code = self._get_post_theorem_code(lean_root, rel_path, thm_name) if lean_root and rel_path else ""

        # Extract proof from patch using GPT
        print(f"  [PatchProver] Extracting proof from patch for task {task_id} ({thm_name})")
        try:
            result = self._extract_proof_from_patch(patch, thm_name, thm_stmt, verif_context, post_code)
            self._extraction_cache[task_id] = result

            timestamp = self._log_prompt(f"[PATCH EXTRACTION] task={task_id} thm={thm_name}\n\n{patch}")
            self._log_outputs(timestamp, [result])

            return [result]
        except Exception as e:
            print(f"  [PatchProver] Extraction failed for task {task_id}: {e}")
            return [self._empty_response()]

    def _empty_response(self) -> str:
        return (
            "<lean4_invented_lemmas>\n</lean4_invented_lemmas>\n"
            "<lean4_proof>\nby sorry\n</lean4_proof>"
        )

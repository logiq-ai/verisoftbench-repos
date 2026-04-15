"""Global constants for the VeriSoftBench evaluation connector."""

import json
import os
from pathlib import Path

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------
CONNECTOR_DIR = Path(__file__).resolve().parent
REPO_ROOT = CONNECTOR_DIR.parent

TASKS_JSONL = REPO_ROOT / "data" / "verisoftbench.jsonl"
PATCHES_DIR = REPO_ROOT / "patches"
RESULTS_JSON = REPO_ROOT / "results.json"
EVAL_RESULTS_DIR = REPO_ROOT / "eval_results"

# ---------------------------------------------------------------------------
# AlephProver API
# ---------------------------------------------------------------------------
ALEPH_API_URL = "https://alephprover.logicalintelligence.com"
ALEPH_API_KEY_ENV = "ALEPH_API_KEY"

REPO_URL = "https://github.com/logiq-ai/verisoftbench-repos"
BRANCH = "clean-eval-v3"

# ---------------------------------------------------------------------------
# Task overrides
# ---------------------------------------------------------------------------
# Task 132: benchmark JSONL has wrong FQN U32.ByteVector.bitwise_componentwise,
# actual name in source is bitwise_componentwise (namespace was closed)
THEOREM_NAME_OVERRIDES = {132: "bitwise_componentwise"}

# ---------------------------------------------------------------------------
# Budgets
# ---------------------------------------------------------------------------
DEFAULT_TIME_BUDGET_MINUTES = 180
DEFAULT_COST_BUDGET_USD = 100

# ---------------------------------------------------------------------------
# Prompt
# ---------------------------------------------------------------------------
EVAL_PROMPT = (
    "You are being evaluated on the benchmark for the proof. "
    "Don't leave sorry in the proof. Don't cheat, "
    "do your best to prove original statements."
)

# ---------------------------------------------------------------------------
# Evaluation
# ---------------------------------------------------------------------------
OPENAI_API_KEY_ENV = "OPENAI_API_KEY"
EXTRACTION_MODEL = "gpt-5.4"
NUM_SAMPLES = 3
DOCKER_CONTAINER = "verisoftbench-lean"

# ---------------------------------------------------------------------------
# Retry / polling
# ---------------------------------------------------------------------------
MAX_SUBMIT_RETRIES = 10
SUBMIT_RETRY_DELAY = 30       # seconds
POLL_INTERVAL = 60             # seconds
MAX_POLL_TIME = 14400          # seconds (4 hours)

# Proof request retries: resubmit tasks that fail at prover level
# (sorry in patch, timeout, build error)
MAX_PROOF_RETRIES = 2          # 0 = no retries


# ---------------------------------------------------------------------------
# Task loading
# ---------------------------------------------------------------------------

def _build_hints(entry: dict) -> str:
    """Build a hints string from upstream JSONL structured fields."""
    parts = []

    lib_lemmas = entry.get("lib_lemmas", [])
    if lib_lemmas:
        items = "\n".join(f"  {l['name']} (from {l.get('module', '')})" for l in lib_lemmas)
        parts.append(f"## Relevant library lemmas:\n{items}")

    repo_lemmas = entry.get("repo_lemmas", [])
    if repo_lemmas:
        items = "\n".join(f"  {l['content']}" for l in repo_lemmas)
        parts.append(f"## Relevant project lemmas:\n{items}")

    used_lib_defs = entry.get("used_lib_defs", [])
    if used_lib_defs:
        items = "\n".join(f"  {d['name']} (from {d.get('module', '')})" for d in used_lib_defs)
        parts.append(f"## Relevant library definitions:\n{items}")

    used_repo_defs = entry.get("used_repo_defs", [])
    if used_repo_defs:
        items = "\n".join(f"  {d['content']}" for d in used_repo_defs)
        parts.append(f"## Same-file definitions:\n{items}")

    return "\n\n".join(parts)


def load_tasks():
    """Load Aristotle subset tasks from the upstream JSONL.

    Returns dict of {task_id: task_dict} with fields:
      id, theorem_name, lean_root, file_path, hints, category,
      nesting_depth, transitive_dep_count
    """
    tasks = {}
    with open(TASKS_JSONL) as f:
        for line in f:
            entry = json.loads(line)
            if not entry.get("subset_aristotle"):
                continue
            tid = entry["id"]
            tasks[tid] = {
                "id": tid,
                "theorem_name": entry["thm_name"],
                "lean_root": entry["lean_root"],
                "file_path": entry["rel_path"],
                "hints": _build_hints(entry),
                "category": entry.get("category", ""),
                "nesting_depth": entry.get("nesting_depth", 0),
                "transitive_dep_count": entry.get("transitive_dep_count", 0),
            }
    return tasks

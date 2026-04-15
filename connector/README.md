# Evaluation Connector

Autonomous pipeline that submits Lean 4 theorem proving tasks to [AlephProver](https://alephprover.logicalintelligence.com), collects proof patches, and evaluates them against the [VeriSoftBench](https://github.com/utopia-group/VeriSoftBench) benchmark.

## Entry Point

```bash
cd verisoftbench-repos

ALEPH_API_KEY="sk-aleph-..." \
OPENAI_API_KEY="sk-proj-..." \
python3 -m connector.run --run-dir runs/my_experiment
```

This runs the full pipeline: **submit → collect → evaluate**, with up to 2 automatic retries for failed tasks. All artifacts are stored in the run directory:

```
runs/my_experiment/
├── results.json          # Submission tracking (request IDs, statuses)
├── patches/              # Downloaded proof patches (task_NNN.patch)
├── eval_config.yaml      # Generated VeriSoftBench config
├── eval_results_compat.json
└── run_YYYYMMDD_HHMMSS.log  # Full pipeline log
```

If the run directory already contains data from a previous run, you'll be prompted to confirm before overwriting. Use `--skip-submit` or `--skip-collect` to resume from an existing run without the prompt.

## What Each File Does

| File | Role |
|---|---|
| `run.py` | **Orchestrator.** Runs submit → collect → evaluate in sequence. Retries failed tasks by resubmitting them for a fresh proof. |
| `submit.py` | **Submit.** Sends `POST /api/v1/requests` to AlephProver for each task. Payload includes the repo URL, branch, file path, theorem name, task-specific hints, and budget. Retries on 402/5xx. |
| `collect.py` | **Collect.** Polls `GET /api/v1/requests/{id}` every 60s until all tasks complete or 4h timeout. Downloads proof patches (git diffs) to `patches/task_NNN.patch`. |
| `evaluate.py` | **Evaluate.** Generates a VeriSoftBench-compatible config and runs the benchmark's `evaluate.py` as a subprocess. Parses per-theorem pass/fail results from the output. |
| `config.py` | **Configuration.** All constants in one place: API URLs, budgets, prompts, retry settings, model config. |
| `patch_prover.py` | **Proof extraction.** `PatchProverInterface` — reads `.patch` files and uses GPT-5.4 (xhigh reasoning, 3 samples) to extract proof body + auxiliary lemmas into XML format for the benchmark. Extractions are saved to `{run-dir}/extractions/` for human review and replay. |

## How It Works

```
  submit.py                collect.py              evaluate.py
  ─────────                ──────────              ───────────
  POST /api/v1/requests    GET /api/v1/requests/   GPT-5.4 extracts proof
  → request_id             {id} → status           from .patch into XML
                           GET /api/v1/requests/   Lean compiles proof
                           {id}/diff → .patch      in Docker container
```

1. **Submit**: For each task in `aristotle_tasks.json`, sends the theorem to AlephProver with the repo URL (`clean-eval-v3` branch where proofs are stripped to `by sorry`), task-specific hints (relevant lemmas/definitions from the benchmark), and a budget (120 min, $100).

2. **Collect**: Polls the API until each task completes or fails. Downloads the proof patch — a git diff showing how AlephProver modified the source file to prove the theorem.

3. **Evaluate**: The patch is a raw diff, but VeriSoftBench expects proofs in a specific XML format (`<lean4_proof>` + `<lean4_invented_lemmas>`). `PatchProverInterface` sends each patch to GPT-5.4 which extracts the proof body and any auxiliary declarations. The benchmark then compiles this against a clean Docker container with all Lean repos pre-built. Pass = compiles without errors or `sorry`.

4. **Import injection**: AlephProver may add new `import` statements to the source file. These are not part of the proof body, but the benchmark needs them in the verification context. `PatchProverInterface` detects imports added by the patch and injects them into the theorem's `verif_local_ctxs` before compilation. This is deterministic (reads the patch) and happens regardless of whether extractions are cached.

5. **Retry**: If evaluation fails (bad extraction, prover timeout, etc.), the orchestrator deletes the old patch, resubmits to AlephProver for a fresh proof, and re-evaluates. Up to `MAX_PROOF_RETRIES` (default 2) rounds.

## Prerequisites

1. **Docker container** with pre-built Lean repos (one-time, ~1h, ~130 GB):
   ```bash
   git clone -b connector https://github.com/logiq-ai/verisoftbench-repos.git
   cd verisoftbench-repos
   docker build -t verisoftbench/lean:latest .
   docker run -d --name verisoftbench-lean verisoftbench/lean:latest
   ```

2. **Python packages**: `pip install pyyaml openai requests tqdm`

3. **Environment variables**:
   - `ALEPH_API_KEY` — AlephProver API key (for submit + collect)
   - `OPENAI_API_KEY` — OpenAI API key (for GPT-5.4 proof extraction during evaluation)

## Usage

```bash
# Full run — all 100 tasks
python3 -m connector.run --run-dir runs/full

# Specific tasks
python3 -m connector.run --run-dir runs/test3 --task-ids 4 29 277

# Resume from collect (already submitted)
python3 -m connector.run --run-dir runs/test3 --skip-submit

# Resume from evaluate (patches already downloaded)
python3 -m connector.run --run-dir runs/test3 --skip-submit --skip-collect

# Re-evaluate using saved GPT extractions (no OpenAI calls)
python3 -m connector.run --run-dir runs/test3 --skip-submit --skip-collect --skip-extraction

# No retries
python3 -m connector.run --run-dir runs/full --no-retries

# Use dev API
python3 -m connector.run --run-dir runs/dev --api-url https://prover-dev.logicalintelligence.com
```

Each step can also run independently:

```bash
python3 -m connector.submit --task-ids 4 29
python3 -m connector.collect --task-ids 4 29
python3 -m connector.evaluate --task-ids 4 29
```

## Configuration

All settings live in `config.py`:

| Setting | Default | Description |
|---|---|---|
| `ALEPH_API_URL` | `https://alephprover.logicalintelligence.com` | API endpoint |
| `BRANCH` | `clean-eval-v3` | Branch with proofs stripped to `by sorry` |
| `DEFAULT_TIME_BUDGET_MINUTES` | 180 | Proving time limit per task |
| `DEFAULT_COST_BUDGET_USD` | 100 | Cost limit per task |
| `EXTRACTION_MODEL` | `gpt-5.4` | Model for proof extraction |
| `NUM_SAMPLES` | 3 | Extraction attempts per task |
| `MAX_PROOF_RETRIES` | 2 | Resubmit retries for failed tasks |
| `POLL_INTERVAL` | 60s | Status check frequency |
| `MAX_POLL_TIME` | 14400s (4h) | Max wait for tasks to complete |

## Output

All artifacts are stored in the `--run-dir` directory:

- **`results.json`** — request IDs, statuses, timestamps for each submitted task
- **`patches/task_NNN.patch`** — downloaded proof patches, one per task
- **`extractions/task_NNN.xml`** — GPT-5.4 extracted proofs (XML with `<lean4_proof>` + `<lean4_invented_lemmas>`) for human review
- **`run_*.log`** — full pipeline log (also printed to stdout)
- **`eval_config.yaml`** — generated VeriSoftBench config for this run

VeriSoftBench also writes detailed per-theorem results to `results/data/aleph-prover-eval_*/details/*.json`.

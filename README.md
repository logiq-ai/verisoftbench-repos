# VeriSoftBench — Aleph Prover Evaluation

Evaluation of [Aleph Prover](https://alephprover.logicalintelligence.com) on the [VeriSoftBench](https://github.com/utopia-group/VeriSoftBench) benchmark (Aristotle subset, 100 Lean 4 theorem proving tasks).

## Results

**91/100 verified** on the official VeriSoftBench evaluation pipeline (Pass@1).

| System | Score |
|---|---|
| **Aleph Prover** | **91% (Pass@1)** |
| Aristotle (with local lemmas) | 69% (Pass@8) |
| Gemini-3-Pro | 65% (Pass@8) |

## Repository Layout

```
verisoftbench-repos/
├── connector/                  # Evaluation pipeline (submit → collect → evaluate)
│   ├── config.py               # All constants: API URLs, budgets, prompts, retry settings
│   ├── run.py                  # Main orchestrator — runs full pipeline with retries
│   ├── submit.py               # Submit tasks to AlephProver API
│   ├── collect.py              # Poll for results, download patches
│   ├── evaluate.py             # Run VeriSoftBench evaluation on collected patches
│   ├── patch_prover.py         # PatchProverInterface — GPT-5.4 proof extraction
│   └── aleph_patch.yaml        # Standalone evaluation config (alternative to connector)
├── aristotle_tasks.json        # 100 tasks: theorem names, file paths, hints
├── patches/                    # Downloaded proof patches (task_NNN.patch)
├── results.json                # Submission tracking (request IDs, statuses)
└── eval_results/               # Logs and evaluation configs
```

### Branches

| Branch | Purpose |
|---|---|
| `clean-eval-v3` | 11 Lean repos with benchmark overlays, proofs stripped to `by sorry` |
| `strip-ground-truth-proofs` | Same + connector pipeline code |
| `verisoftbench` | Fork of [utopia-group/VeriSoftBench](https://github.com/utopia-group/VeriSoftBench) with PatchProverInterface and evaluation fixes |

## Quick Start — Full Evaluation

Run all 100 tasks end-to-end with a single command:

```bash
cd verisoftbench-repos

ALEPH_API_KEY="sk-aleph-..." \
OPENAI_API_KEY="sk-proj-..." \
python3 -m connector.run
```

This will:
1. Submit all 100 tasks to AlephProver (each gets up to 2h and $100 budget)
2. Poll until all proofs complete (~30 min per task, up to 4h timeout)
3. Download proof patches
4. Run VeriSoftBench evaluation (GPT-5.4 extracts proofs, Lean verifies in Docker)
5. Retry failed tasks up to 2 times
6. Log everything to `eval_results/run_*.log`

## Prerequisites

### 1. Clone Repositories

```bash
# Main repo (tasks, patches, connector)
git clone -b strip-ground-truth-proofs \
  https://github.com/logiq-ai/verisoftbench-repos.git

# VeriSoftBench evaluation framework (fork with PatchProverInterface)
git clone -b verisoftbench \
  https://github.com/logiq-ai/verisoftbench-repos.git VeriSoftBench-eval
```

The connector expects the evaluation repo at `../VeriSoftBench-eval/` or `../VeriSoftBench-clean/` relative to `verisoftbench-repos/`.

### 2. Build Docker Image

The benchmark compiles proofs against a clean Docker container with all 11 Lean repos pre-built. This is a one-time setup (~1 hour, ~130 GB disk).

```bash
cd VeriSoftBench-eval
docker build -t verisoftbench/lean:latest .
docker run -d --name verisoftbench-lean verisoftbench/lean:latest
```

Verify the container is running:

```bash
docker ps --filter name=verisoftbench-lean
```

### 3. Install Python Dependencies

```bash
pip install pyyaml openai requests tqdm
```

### 4. Environment Variables

| Variable | Required For | Description |
|---|---|---|
| `ALEPH_API_KEY` | Submit + Collect | AlephProver API key |
| `OPENAI_API_KEY` | Evaluate | GPT-5.4 proof extraction |

## Running the Pipeline

### Full Run (All 100 Tasks)

```bash
ALEPH_API_KEY="sk-aleph-..." \
OPENAI_API_KEY="sk-proj-..." \
python3 -m connector.run
```

### Specific Tasks

```bash
python3 -m connector.run --task-ids 4 29 277
```

### Skip Steps (Resume)

```bash
# Already submitted — skip to collect + evaluate
python3 -m connector.run --task-ids 4 29 --skip-submit

# Patches already downloaded — skip to evaluate
python3 -m connector.run --task-ids 4 29 --skip-submit --skip-collect

# No retries
python3 -m connector.run --no-retries
```

### Run Steps Independently

```bash
# Submit only
python3 -m connector.submit --task-ids 4 29

# Collect only (polls until done)
python3 -m connector.collect --task-ids 4 29

# Evaluate only (requires patches/ on disk + Docker running)
python3 -m connector.evaluate --task-ids 4 29
```

## How It Works

### Pipeline Flow

```
                    ┌──────────────────────────────────────────┐
                    │              connector/run.py             │
                    │         (orchestrator + retry loop)       │
                    └──────┬───────────┬───────────┬───────────┘
                           │           │           │
                    ┌──────▼──┐  ┌─────▼────┐  ┌──▼────────┐
                    │ submit  │  │ collect   │  │ evaluate  │
                    │         │  │           │  │           │
                    │ POST    │  │ GET /api  │  │ GPT-5.4   │
                    │ /api/v1 │  │ /v1/req/  │  │ extracts  │
                    │ /req    │  │ {id}      │  │ proof     │
                    │         │  │           │  │ from diff │
                    │ → req ID│  │ → .patch  │  │ → XML     │
                    └─────────┘  └──────────┘  │           │
                                                │ Lean      │
                                                │ compiles  │
                                                │ in Docker │
                                                └───────────┘
```

### Step 1: Submit

For each task, sends a `POST /api/v1/requests` to AlephProver with:
- **Repository**: `https://github.com/logiq-ai/verisoftbench-repos` branch `clean-eval-v3`
- **File path** and **theorem name** from `aristotle_tasks.json`
- **Hints**: task-specific context (relevant lemmas, definitions) + generic evaluation prompt
- **Budget**: 120 min, $100 per task

Retries on HTTP 402 (concurrent limit) and 5xx errors.

### Step 2: Collect

Polls `GET /api/v1/requests/{id}` every 60 seconds until all tasks complete or 4-hour timeout. Downloads proof patches (git diffs) to `patches/task_NNN.patch`.

### Step 3: Evaluate

1. Generates a VeriSoftBench-compatible config pointing to the downloaded patches
2. Runs `VeriSoftBench-eval/evaluate.py` as a subprocess
3. **PatchProverInterface** reads each `.patch` file and sends it to GPT-5.4 (xhigh reasoning, 3 samples) to extract:
   - Proof body (everything after `:=` / `by` / `where`)
   - Auxiliary lemmas (new definitions the proof depends on)
4. The extracted proof is compiled against the clean Docker container
5. Pass = compiles without errors or `sorry`

### Retries

If evaluation fails for a task (GPT extraction error, prover timeout, etc.), the orchestrator:
1. Deletes the old patch
2. Resubmits the task to AlephProver for a fresh proof
3. Re-evaluates

Up to 2 retries (configurable via `MAX_PROOF_RETRIES` in `config.py`).

## Configuration

All settings are in `connector/config.py`:

| Setting | Default | Description |
|---|---|---|
| `ALEPH_API_URL` | `https://alephprover.logicalintelligence.com` | AlephProver API endpoint |
| `BRANCH` | `clean-eval-v3` | Git branch with stripped proofs |
| `DEFAULT_TIME_BUDGET_MINUTES` | 120 | Max proving time per task |
| `DEFAULT_COST_BUDGET_USD` | 100 | Max cost per task |
| `EXTRACTION_MODEL` | `gpt-5.4` | Model for proof extraction from patches |
| `NUM_SAMPLES` | 3 | GPT extraction attempts per task |
| `MAX_PROOF_RETRIES` | 2 | Full resubmit retries for failed tasks |
| `POLL_INTERVAL` | 60s | Seconds between status checks |
| `MAX_POLL_TIME` | 14400s (4h) | Max wait for all tasks to complete |

## Task 132 Override

The benchmark JSONL has the wrong fully-qualified name `U32.ByteVector.bitwise_componentwise` for task 132. The actual name in the source is `bitwise_componentwise` (the namespace was closed). This is handled automatically via `THEOREM_NAME_OVERRIDES` in `config.py`.

## Unsolved Tasks (9/100)

| Task | Theorem | Reason |
|---|---|---|
| 121 | InductiveTable.table_soundness_aux | Prover produced incomplete proof (sorry) |
| 122, 127, 155, 161, 171 | Circomlib.MultiAND.* | Namespace shadowing (`open Circuit` resolves to wrong namespace) |
| 265, 266, 268 | eval_*_completeness, arstep_preserve_eval | Theorems inside `mutual` block, extraction not supported |

# VeriSoftBench — Aleph Prover Evaluation

Evaluation of [Aleph Prover](https://alephprover.logicalintelligence.com) on the [VeriSoftBench](https://github.com/utopia-group/VeriSoftBench) benchmark (Aristotle subset, 100 tasks).

## Current Results

**85/100 (85%) verified** on the official VeriSoftBench evaluation pipeline (Pass@1).

| System | Score |
|---|---|
| **Aleph Prover** | **85% (Pass@1)** |
| Aristotle (with local lemmas) | 69% (Pass@8) |
| Gemini-3-Pro | 65% (Pass@8) |

## What's Already Here

This repo contains everything needed to reproduce the evaluation:

- **`verisoftbench_final_results.json`** — results for all 100 tasks, including:
  - `request_id` — AlephProver proof request UUID
  - `api_url` — link to track each request (e.g. `https://alephprover.logicalintelligence.com/requests/<id>`)
  - `pr_url` — GitHub PR with the proven code
  - `status` — `completed` (92 tasks) or `failed` (8 tasks)
- **`patches/`** — 92 `.patch` files already committed, one per completed task. These are the raw git diffs produced by AlephProver showing the proven theorems.
- **`aristotle_tasks.json`** — the 100 tasks with metadata, theorem names, file paths, and hints

So for existing results, **you don't need API access** — the patches are already in the repo. You only need the API to submit new tasks or re-download patches.

## Repository Structure

Two branches:

- **`main`** — results, patches, scripts, Lean project repos
- **`verisoftbench`** — fork of [utopia-group/VeriSoftBench](https://github.com/utopia-group/VeriSoftBench) with the Aleph Prover connector pre-applied

### `main` branch

```
verisoftbench-repos/
├── README.md
├── aristotle_tasks.json              # 100 Aristotle tasks with metadata + hints
├── verisoftbench_final_results.json  # Results: request IDs, API URLs, PR URLs, status
├── verisoftbench_final_results.csv
├── patches/                          # .patch files (92 committed, more via download_patches.py)
├── submit.py                         # Submit tasks to AlephProver API
├── download_patches.py               # Download patches from API to local disk
├── connector/                        # Connector source (already applied in verisoftbench branch)
│   ├── patch_prover.py
│   ├── aleph_patch.yaml
│   ├── evaluator.patch
│   └── evaluate.patch
├── ArkLib/                           # Lean project repos (used by submit.py)
├── clean/
├── veil/
└── ...                               # (23 repos total)
```

### `verisoftbench` branch

Fork of the official benchmark with connector applied. Contains:
- `core/patch_prover.py` — PatchProverInterface
- `configs/aleph_patch.yaml` — evaluation config
- Modified `core/evaluator.py` and `evaluate.py` (minimal changes to route `model_name: patch`)

## Reproducing the Evaluation (fresh server)

### Prerequisites

- **Docker** (with ~130 GB free disk for the Lean image)
- **Python 3.10+** with pip
- **Git**
- **`OPENAI_API_KEY`** — for GPT-5.4 proof extraction during evaluation

### Step 1: Environment variables

```bash
export OPENAI_API_KEY=sk-proj-...     # GPT-5.4 (proof extraction during eval)
```

(`ALEPH_API_KEY` is only needed if you want to submit new tasks or re-download patches — not needed for reproducing existing results.)

### Step 2: Clone repos

```bash
cd ~

# This repo — main branch (results, patches, Lean project sources)
git clone https://github.com/logiq-ai/verisoftbench-repos.git

# Benchmark with connector — verisoftbench branch (fork of official repo + connector pre-applied)
git clone -b verisoftbench https://github.com/logiq-ai/verisoftbench-repos.git VeriSoftBench-eval

# Python deps for the benchmark
pip install pyyaml openai anthropic google-genai tqdm requests
```

The expected directory layout is:

```
~/
├── verisoftbench-repos/       # main branch — results, patches, submit scripts
└── VeriSoftBench-eval/        # verisoftbench branch — benchmark + connector
```

The connector config uses relative paths (`../verisoftbench-repos/...`) based on this layout. If you use different directories, update `VeriSoftBench-eval/configs/aleph_patch.yaml`.

### Step 3: Build Docker verification environment

The official benchmark compiles proofs inside a Docker container with all 23 Lean repos pre-built. This is a one-time build.

```bash
cd ~/VeriSoftBench-eval
docker build -t verisoftbench/lean:latest .
```

This takes **~1 hour** and produces a **~127 GB image** (Mathlib cache downloads dominate).

Then start the container:

```bash
docker run -d --name verisoftbench-lean verisoftbench/lean:latest
```

Verify it's clean (no modifications from previous runs):

```bash
docker diff verisoftbench-lean
# Should show nothing, or just /root/.bash_history
```

If you need a fresh container later:

```bash
docker rm -f verisoftbench-lean
docker run -d --name verisoftbench-lean verisoftbench/lean:latest
```

### Step 4: Run the evaluation

The 92 `.patch` files are already committed in the repo — no download step needed for existing results.

```bash
cd ~/VeriSoftBench-eval

# Full run — all 100 Aristotle tasks
python3 evaluate.py \
    --config configs/aleph_patch.yaml \
    --task-ids "4,5,14,15,29,121,122,123,124,125,126,127,128,129,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,152,153,154,155,156,157,158,159,160,161,163,164,165,168,169,171,176,178,194,222,245,246,247,249,250,265,266,268,271,272,273,274,275,277,281,356,357,359,361,378,381,392,396,444,445,446,447,450,451,452,453,454,455,456,457,458,459,460,462,466,467,468,469,471,472,473" \
    --save-debug-lean \
    --refresh-cache
```

This will:
1. Load each task from `data/verisoftbench.jsonl`
2. Read the `.patch` file from `patches/` for each task (8 unsolved tasks have no patch — they'll score 0)
3. Call GPT-5.4 to extract proof body + auxiliary lemmas into XML
4. Compile the proof against the clean Docker container
5. Report pass/fail

Expected output: `Success rate w/o fix: 85/100 (85.0%)`

Single task test (good for verifying your setup works):

```bash
python3 evaluate.py --config configs/aleph_patch.yaml --task-ids "29" --save-debug-lean --refresh-cache
# Expected: Success rate w/o fix: 1/1 (100.0%)
```

## Proving New Tasks

To solve tasks that Aleph Prover hasn't proven yet (or to re-run failed ones with more budget):

### Step 1: Submit to AlephProver

```bash
export ALEPH_API_KEY=sk-aleph-...
cd ~/verisoftbench-repos

# Single task — prints tracking URL
python3 submit.py 122
# https://alephprover.logicalintelligence.com/requests/<id>

# Multiple tasks
python3 submit.py 122 127 155

# Higher budget
python3 submit.py 122 --cost-budget 50 --time-budget 600

# Submit to dev
python3 submit.py 122 --env dev
```

### Step 2: Wait for completion

Visit the tracking URL printed by `submit.py`, or query the API directly:

```bash
curl -s -H "Authorization: Bearer $ALEPH_API_KEY" \
    https://alephprover.logicalintelligence.com/api/v1/requests/<id>
```

### Step 3: Update results and download patch

Once a task completes, update `verisoftbench_final_results.json` with the new request ID and status:

```json
{
    "task_id": 122,
    ...
    "request_id": "<new-uuid>",
    "status": "completed",
    "api_url": "https://alephprover.logicalintelligence.com/requests/<new-uuid>",
    "pr_url": "https://github.com/logiq-ai/verisoftbench-repos/pull/<N>"
}
```

Then download the patch:

```bash
python3 download_patches.py --task-id 122
# Downloads to patches/task_122.patch
```

### Step 4: Verify with the benchmark

```bash
cd ~/VeriSoftBench-eval
python3 evaluate.py --config configs/aleph_patch.yaml --task-ids "122" --save-debug-lean --refresh-cache
```

### Step 5: Commit the new results

```bash
cd ~/verisoftbench-repos
git add patches/task_122.patch verisoftbench_final_results.json
git commit -m "Add task 122: Circomlib.MultiAND.soundness"
git push
```

## How It Works

### Evaluation flow

```
patches/ (committed)          evaluate.py + patch_prover.py
   or                                  │
download_patches.py                    │  OPENAI_API_KEY
   │  ALEPH_API_KEY                    ▼
   ▼                             GPT-5.4 extracts proof
AlephProver API ──► patches/     from patch into XML    ──► Lean compiler
(fetch .patch)     (on disk)                                verifies in Docker
```

1. `.patch` files are either already committed or fetched via `download_patches.py`
2. `evaluate.py` loads each task from the benchmark's `verisoftbench.jsonl`
3. `PatchProverInterface` reads the local `.patch` file for that task
4. GPT-5.4 extracts proof body + auxiliary lemmas into XML:
   ```xml
   <lean4_invented_lemmas>
   (helper lemmas here)
   </lean4_invented_lemmas>
   <lean4_proof>
   by
     (tactic proof here)
   </lean4_proof>
   ```
5. The benchmark compiles the proof against the clean Docker container
6. Result: pass (proof compiles without sorry) or fail

### Why GPT-5.4 for extraction?

Patches are complex whole-file diffs that may add helper lemmas, new imports, rearrange code, or reference definitions from after the theorem. A regex parser would miss these cases. GPT-5.4 reads the patch + verification context + post-theorem code and produces clean Lean 4 in the expected format.

## Config Reference

`VeriSoftBench-eval/configs/aleph_patch.yaml`:

| Key | Description | Default |
|---|---|---|
| `extraction_model_id` | Model for patch→XML extraction | `gpt-5.4` |
| `patches_dir` | Directory with `task_NNN.patch` files | `../verisoftbench-repos/patches` |
| `results_json` | Path to results JSON | `../verisoftbench-repos/verisoftbench_final_results.json` |
| `docker_container` | Docker container name | `verisoftbench-lean` |
| `fix_enabled` | Enable iterative proof fixing | `false` |
| `max_workers` | Parallel evaluation workers | `8` |

## Troubleshooting

**`docker build` fails or is very slow**: The build downloads Mathlib caches (~50 GB). Ensure stable internet and sufficient disk space (~130 GB for the image).

**`evaluate.py` hangs on GPT calls**: GPT-5.4 reasoning calls can take 10-60 seconds each. With `max_workers: 8`, 100 tasks take ~10-15 minutes total.

**Proofs fail that previously passed**: GPT-5.4 extraction is non-deterministic. Re-run with `--refresh-cache` to get a fresh extraction. The 85% rate is typical; individual tasks may flip between runs.

**`download_patches.py` fails with 401/403**: Check that `ALEPH_API_KEY` is set correctly. The API key must have access to the proof requests.

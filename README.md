# VeriSoftBench — Aleph Prover Evaluation

Evaluation of [Aleph Prover](https://alephprover.logicalintelligence.com) on the [VeriSoftBench](https://github.com/utopia-group/VeriSoftBench) benchmark (Aristotle subset, 100 tasks).

## Current Results

**85/100 (85%) verified** on the official VeriSoftBench evaluation pipeline (Pass@1).

| System | Score |
|---|---|
| **Aleph Prover** | **85% (Pass@1)** |
| Aristotle (with local lemmas) | 69% (Pass@8) |
| Gemini-3-Pro | 65% (Pass@8) |

## Repository Structure

```
verisoftbench-repos/
├── README.md
├── aristotle_tasks.json              # 100 Aristotle tasks with metadata + hints
├── verisoftbench_final_results.json  # Results: request IDs, PR URLs, status
├── verisoftbench_final_results.csv
├── patches/                          # Downloaded .patch files (via download_patches.py)
├── submit.py                         # Submit tasks to AlephProver API
├── download_patches.py               # Download patches from API to local disk
├── connector/                        # Connector for VeriSoftBench eval pipeline
│   ├── patch_prover.py               # PatchProverInterface (reads patches, calls GPT-5.4)
│   ├── aleph_patch.yaml              # Config for evaluate.py
│   ├── evaluator.patch               # Patch for core/evaluator.py
│   └── evaluate.patch                # Patch for evaluate.py
├── ArkLib/                           # Lean project repos (used by submit.py)
├── clean/
├── veil/
└── ...                               # (23 repos total)
```

## Fresh Server Setup (from scratch)

### Prerequisites

- **Docker** (with ~130 GB free disk for the Lean image)
- **Python 3.10+**
- **Git**

### Step 1: Environment variables

```bash
export ALEPH_API_KEY=sk-aleph-...     # AlephProver API (submit + download patches)
export OPENAI_API_KEY=sk-proj-...     # GPT-5.4 (proof extraction during eval)
```

### Step 2: Clone repos

```bash
cd ~

# This repo (results, patches, connector, Lean project sources)
git clone https://github.com/logiq-ai/verisoftbench-repos.git

# Official VeriSoftBench benchmark
git clone https://github.com/utopia-group/VeriSoftBench.git VeriSoftBench-eval

# Python deps for the benchmark
pip install pyyaml openai anthropic google-genai tqdm requests
```

The expected directory layout is:

```
~/
├── verisoftbench-repos/       # this repo
└── VeriSoftBench-eval/        # official benchmark
```

The connector config uses relative paths (`../verisoftbench-repos/...`) based on this layout. If you use different directories, update `configs/aleph_patch.yaml` after step 4.

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

### Step 4: Apply connector to benchmark

The connector is a custom `ProverInterface` that reads `.patch` files and uses GPT-5.4 to extract proofs into the XML format the benchmark expects. It requires two small patches to the official benchmark code.

```bash
cd ~/VeriSoftBench-eval

# Copy connector
cp ~/verisoftbench-repos/connector/patch_prover.py core/
cp ~/verisoftbench-repos/connector/aleph_patch.yaml configs/

# Patch evaluation scripts (adds 'patch' model_name support + config passthrough)
patch -p1 < ~/verisoftbench-repos/connector/evaluator.patch
patch -p1 < ~/verisoftbench-repos/connector/evaluate.patch
```

To verify patches applied correctly:

```bash
grep "PatchProverInterface" core/evaluator.py    # should find the import
grep "patches_dir" evaluate.py                   # should find the config key
```

### Step 5: Download patches from AlephProver API

Patches are fetched from the API using request IDs in `verisoftbench_final_results.json`:

```bash
cd ~/verisoftbench-repos
python3 download_patches.py
```

This downloads `.patch` files for all completed tasks into `patches/`. Already-downloaded patches are skipped (use `--force` to re-download).

### Step 6: Run the evaluation

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
2. Read the `.patch` file for each task
3. Call GPT-5.4 to extract proof body + auxiliary lemmas
4. Compile against the clean Docker container
5. Report pass/fail

Expected output: `Success rate w/o fix: 85/100 (85.0%)`

Single task test (good for verifying setup):

```bash
python3 evaluate.py --config configs/aleph_patch.yaml --task-ids "29" --save-debug-lean --refresh-cache
# Expected: Success rate w/o fix: 1/1 (100.0%)
```

## Submitting New Tasks to AlephProver

### Submit

```bash
cd ~/verisoftbench-repos

# Single task
python3 submit.py --task-id 4

# Multiple tasks
python3 submit.py --task-id 4,5,14

# All unsolved tasks with custom budget
python3 submit.py --unsolved --cost-budget 50 --time-budget 600

# Submit to dev environment
python3 submit.py --task-id 4 --env dev

# Dry run (show what would be submitted)
python3 submit.py --unsolved --dry-run
```

### Check status

```bash
python3 submit.py --status <request-id>
python3 submit.py --status <request-id> --env dev
```

### After a submission completes

1. Update `verisoftbench_final_results.json` with the new request ID and status
2. Download the patch:
   ```bash
   python3 download_patches.py --task-id <id>
   ```
3. Re-run evaluation to verify:
   ```bash
   cd ~/VeriSoftBench-eval
   python3 evaluate.py --config configs/aleph_patch.yaml --task-ids "<id>" --save-debug-lean --refresh-cache
   ```

## How It Works

### Evaluation flow

```
download_patches.py              evaluate.py + patch_prover.py
        │                                │
        │  ALEPH_API_KEY                 │  OPENAI_API_KEY
        ▼                                ▼
  AlephProver API ──► patches/     GPT-5.4 extracts proof ──► Lean compiler
  (fetch .patch)     (on disk)     from patch into XML        verifies in Docker
```

1. `download_patches.py` fetches `.patch` files from AlephProver API
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

`configs/aleph_patch.yaml`:

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

**`patch -p1` fails**: The patches are against the latest VeriSoftBench commit (`ad1591d`). If upstream has changed, you may need to apply manually — the changes are minimal (3 lines in `evaluator.py`, 8 lines in `evaluate.py`).

**`evaluate.py` hangs on GPT calls**: GPT-5.4 reasoning calls can take 10-60 seconds each. With `max_workers: 8`, 100 tasks take ~10-15 minutes total.

**Proofs fail that previously passed**: GPT-5.4 extraction is non-deterministic. Re-run with `--refresh-cache` to get a fresh extraction. The 85% rate is typical; individual tasks may flip between runs.

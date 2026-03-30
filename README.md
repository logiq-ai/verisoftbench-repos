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
verisoftbench-repos/               # main branch
├── README.md
├── aristotle_tasks.json           # 100 Aristotle tasks with metadata + hints
├── verisoftbench_final_results.json  # Results: request IDs, PR URLs, status
├── verisoftbench_final_results.csv
├── patches/                       # Downloaded .patch files (via download_patches.py)
├── submit.py                      # Submit tasks to AlephProver API
├── download_patches.py            # Download patches from API to local disk
├── connector/                     # Connector for VeriSoftBench eval pipeline
│   ├── patch_prover.py            # PatchProverInterface (reads patches, calls GPT-5.4)
│   ├── aleph_patch.yaml           # Config for evaluate.py
│   ├── evaluator.patch            # Patch for core/evaluator.py
│   └── evaluate.patch             # Patch for evaluate.py
├── ArkLib/                        # Lean project repos (used by submit.py)
├── clean/
├── veil/
└── ...
```

There is also a `verisoftbench` branch which is a fork of the [original benchmark](https://github.com/utopia-group/VeriSoftBench) with the connector pre-applied.

## Setup

### 1. Environment variables

```bash
export ALEPH_API_KEY=sk-aleph-...     # AlephProver API (submit + download patches)
export OPENAI_API_KEY=sk-proj-...     # GPT-5.4 (proof extraction during eval)
```

### 2. Clone repos

```bash
# This repo
git clone https://github.com/logiq-ai/verisoftbench-repos.git
cd verisoftbench-repos

# Official benchmark
cd ~
git clone https://github.com/utopia-group/VeriSoftBench.git VeriSoftBench-eval
pip install pyyaml openai anthropic google-genai tqdm
```

### 3. Build Docker verification environment

```bash
cd ~/VeriSoftBench-eval
docker build -t verisoftbench/lean:latest .     # ~1 hour
docker run -d --name verisoftbench-lean verisoftbench/lean:latest
```

Or if the image already exists:

```bash
docker run -d --name verisoftbench-lean verisoftbench/lean:latest
```

Verify it's clean: `docker diff verisoftbench-lean` should show nothing.

### 4. Apply connector to benchmark

```bash
cd ~/VeriSoftBench-eval

# Copy connector files
cp ~/verisoftbench-repos/connector/patch_prover.py core/
cp ~/verisoftbench-repos/connector/aleph_patch.yaml configs/

# Apply patches to evaluation scripts
patch -p1 < ~/verisoftbench-repos/connector/evaluator.patch
patch -p1 < ~/verisoftbench-repos/connector/evaluate.patch
```

### 5. Download patches

```bash
cd ~/verisoftbench-repos
python3 download_patches.py           # downloads all completed tasks
python3 download_patches.py --force   # re-download everything
```

## Running the Evaluation

### Full run (100 Aristotle tasks)

```bash
cd ~/VeriSoftBench-eval

python3 evaluate.py \
    --config configs/aleph_patch.yaml \
    --task-ids "4,5,14,15,29,121,122,123,124,125,126,127,128,129,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,152,153,154,155,156,157,158,159,160,161,163,164,165,168,169,171,176,178,194,222,245,246,247,249,250,265,266,268,271,272,273,274,275,277,281,356,357,359,361,378,381,392,396,444,445,446,447,450,451,452,453,454,455,456,457,458,459,460,462,466,467,468,469,471,472,473" \
    --save-debug-lean \
    --refresh-cache
```

### Single task

```bash
python3 evaluate.py --config configs/aleph_patch.yaml --task-ids "29" --save-debug-lean --refresh-cache
```

## Submitting New Tasks

### Submit to AlephProver

```bash
cd ~/verisoftbench-repos

# Single task
python3 submit.py --task-id 4

# All unsolved tasks
python3 submit.py --unsolved --cost-budget 50 --time-budget 600

# To dev
python3 submit.py --task-id 4 --env dev

# Dry run
python3 submit.py --unsolved --dry-run
```

### After submission completes

1. Update `verisoftbench_final_results.json` with the new request ID/status
2. Download the new patch:
   ```bash
   python3 download_patches.py --task-id 4
   ```
3. Re-run evaluation to verify:
   ```bash
   cd ~/VeriSoftBench-eval
   python3 evaluate.py --config configs/aleph_patch.yaml --task-ids "4" --save-debug-lean --refresh-cache
   ```

## How It Works

### Evaluation flow

```
download_patches.py          evaluate.py + patch_prover.py
        │                              │
        │  ALEPH_API_KEY               │  OPENAI_API_KEY
        ▼                              ▼
  AlephProver API ──► patches/   GPT-5.4 extracts proof ──► Lean compiler
  (fetch .patch)     (on disk)   from patch into XML        verifies in Docker
```

1. `download_patches.py` fetches `.patch` files from AlephProver API using request IDs in the results JSON
2. `evaluate.py` loads each task from `verisoftbench.jsonl`
3. `PatchProverInterface` reads the local `.patch` file for that task
4. GPT-5.4 extracts proof body + auxiliary lemmas into the XML format the benchmark expects
5. The benchmark compiles the proof against the clean Docker container

### Why GPT-5.4 for extraction?

Patches are complex whole-file diffs that may add helper lemmas, new imports, rearrange code, or use definitions from after the theorem. GPT-5.4 with reasoning reads the patch + surrounding context and produces clean Lean 4 in the right format.

## Config Reference

`aleph_patch.yaml`:

| Key | Description |
|---|---|
| `extraction_model_id` | Model for patch→XML extraction (default: `gpt-5.4`) |
| `patches_dir` | Directory with `task_NNN.patch` files |
| `results_json` | Path to `verisoftbench_final_results.json` |
| `docker_container` | Docker container name for Lean verification |
| `fix_enabled` | Enable iterative proof fixing (default: false) |

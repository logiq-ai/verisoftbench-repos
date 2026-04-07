# VeriSoftBench — Aleph Prover Evaluation

Evaluation of [Aleph Prover](https://alephprover.logicalintelligence.com) on the [VeriSoftBench](https://github.com/utopia-group/VeriSoftBench) benchmark (Aristotle subset, 100 tasks).

## Results

**91/100 verified** on the official VeriSoftBench evaluation pipeline (Pass@1).

| System | Score |
|---|---|
| **Aleph Prover** | **91% (Pass@1)** |
| Aristotle (with local lemmas) | 69% (Pass@8) |
| Gemini-3-Pro | 65% (Pass@8) |

## Key Files

| File | Description |
|---|---|
| `successful_submissions.json` | 91 successful proof requests with request IDs, API URLs, PR links, and hints used |
| `aristotle_tasks.json` | 100 Aristotle tasks with metadata, theorem names, file paths, and hints |
| `submit.py` | Submit tasks to AlephProver API (uses GitHub repo URL endpoint) |
| `download_patches.py` | Download .patch files from API to local disk |
| `update_results.py` | Check proof request status, update results JSON, download patches |

## Branches

- **`main`** — Lean project repos (proofs stripped to `by sorry`), results, scripts
- **`verisoftbench`** — fork of [utopia-group/VeriSoftBench](https://github.com/utopia-group/VeriSoftBench) with evaluation connector pre-applied

## Reproducing the Evaluation

### Prerequisites

- Docker (130 GB disk for Lean image)
- Python 3.10+ with `pip install pyyaml openai anthropic google-genai tqdm requests`
- `OPENAI_API_KEY` environment variable (for GPT-5.4 proof extraction)

### Steps

```bash
# 1. Clone repos
git clone https://github.com/logiq-ai/verisoftbench-repos.git
git clone -b verisoftbench https://github.com/logiq-ai/verisoftbench-repos.git VeriSoftBench-eval

# 2. Build Docker (one-time, ~1 hour)
cd VeriSoftBench-eval
docker build -t verisoftbench/lean:latest .
docker run -d --name verisoftbench-lean verisoftbench/lean:latest

# 3. Download patches
cd ../verisoftbench-repos
export ALEPH_API_KEY=sk-aleph-...
python3 download_patches.py

# 4. Evaluate
cd ../VeriSoftBench-eval
export OPENAI_API_KEY=sk-proj-...
python3 evaluate.py \
    --config configs/aleph_patch.yaml \
    --task-ids "4,5,14,15,29,121,122,123,124,125,126,127,128,129,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,152,153,154,155,156,157,158,159,160,161,163,164,165,168,169,171,176,178,194,222,245,246,247,249,250,265,266,268,271,272,273,274,275,277,281,356,357,359,361,378,381,392,396,444,445,446,447,450,451,452,453,454,455,456,457,458,459,460,462,466,467,468,469,471,472,473" \
    --save-debug-lean \
    --refresh-cache
```

### Submitting New Tasks

```bash
export ALEPH_API_KEY=sk-aleph-...
python3 submit.py 4 --env prod                    # submit single task
python3 submit.py 4 --env dev --hints "extra hint" # with hints
python3 submit.py 4 -o runs.json                   # track submission
```

## How Evaluation Works

1. Each task has a `.patch` file (diff from AlephProver showing the proven theorem)
2. GPT-5.4 extracts proof body + auxiliary lemmas from the patch into XML format
3. The benchmark compiles the proof against a clean Docker container with all Lean repos pre-built
4. Pass = compiles without `sorry`

## Unsolved Tasks (9/100)

| Task | Theorem | Reason |
|---|---|---|
| 121 | InductiveTable.table_soundness_aux | Prover produced incomplete proof (sorry) |
| 122, 127, 155, 161, 171 | Circomlib.MultiAND.* | Namespace shadowing bug prevents blueprint compilation |
| 265, 266, 268 | eval_*_completeness, arstep_preserve_eval | Theorems inside `mutual` block, extraction fails |

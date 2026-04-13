"""Global constants for the VeriSoftBench evaluation connector."""

import os
from pathlib import Path

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------
CONNECTOR_DIR = Path(__file__).resolve().parent
REPO_ROOT = CONNECTOR_DIR.parent

TASKS_JSON = REPO_ROOT / "aristotle_tasks.json"
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
DEFAULT_TIME_BUDGET_MINUTES = 120
DEFAULT_COST_BUDGET_USD = 50

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
MAX_POLL_TIME = 7200           # seconds (2 hours)

# Proof request retries: resubmit tasks that fail at prover level
# (sorry in patch, timeout, build error)
MAX_PROOF_RETRIES = 2          # 0 = no retries

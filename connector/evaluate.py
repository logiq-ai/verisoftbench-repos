#!/usr/bin/env python3
"""Evaluate collected patches against VeriSoftBench.

Usage:
    python -m connector.evaluate
    python -m connector.evaluate --task-ids 4 29
    python -m connector.evaluate --patches-dir /path/to/patches
"""

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

from connector.config import (
    DOCKER_CONTAINER, EVAL_RESULTS_DIR, EXTRACTION_MODEL, NUM_SAMPLES,
    OPENAI_API_KEY_ENV, PATCHES_DIR, REPO_ROOT, RESULTS_JSON, TASKS_JSON,
)


def get_all_task_ids():
    with open(TASKS_JSON) as f:
        return sorted(t["id"] for t in json.load(f))


def get_task_ids_with_patches(patches_dir):
    ids = []
    for f in patches_dir.glob("task_*.patch"):
        try:
            tid = int(f.stem.replace("task_", ""))
            ids.append(tid)
        except ValueError:
            pass
    return sorted(ids)


def write_eval_config(patches_dir, output_path):
    """Write a temporary evaluation config for VeriSoftBench."""
    config = {
        "model_name": "patch",
        "model_id": "aleph-prover-patch",
        "extraction_model_id": EXTRACTION_MODEL,
        "num_samples": NUM_SAMPLES,
        "results_json": str(RESULTS_JSON),
        "patches_dir": str(patches_dir),
        "fix_enabled": False,
        "mode": "filtered_context",
        "locator_file": "verisoftbench.jsonl",
        "max_workers": 8,
        "lean_backend": "docker",
        "docker_container": DOCKER_CONTAINER,
        "run_name": "aleph-prover-eval",
    }

    # Write as YAML
    with open(output_path, "w") as f:
        for k, v in config.items():
            if isinstance(v, bool):
                f.write(f"{k}: {'true' if v else 'false'}\n")
            elif isinstance(v, int):
                f.write(f"{k}: {v}\n")
            else:
                f.write(f"{k}: {v}\n")

    return output_path


def find_eval_repo():
    """Find the VeriSoftBench evaluation repo (verisoftbench branch)."""
    candidates = [
        REPO_ROOT.parent / "VeriSoftBench-eval",
        REPO_ROOT.parent / "VeriSoftBench-clean",
        Path.home() / "VeriSoftBench-eval",
    ]
    for c in candidates:
        if (c / "evaluate.py").exists() and (c / "core" / "patch_prover.py").exists():
            return c
    return None


def main():
    p = argparse.ArgumentParser(description="Evaluate patches against VeriSoftBench")
    p.add_argument("--task-ids", nargs="*", type=int, help="Task IDs (default: all with patches)")
    p.add_argument("--patches-dir", type=Path, default=PATCHES_DIR, help=f"Patches directory (default: {PATCHES_DIR})")
    p.add_argument("--eval-repo", type=Path, default=None, help="Path to VeriSoftBench evaluation repo")
    args = p.parse_args()

    if not os.environ.get(OPENAI_API_KEY_ENV):
        print(f"ERROR: Set {OPENAI_API_KEY_ENV} environment variable", file=sys.stderr)
        sys.exit(1)

    eval_repo = args.eval_repo or find_eval_repo()
    if not eval_repo or not (eval_repo / "evaluate.py").exists():
        print("ERROR: VeriSoftBench evaluation repo not found.", file=sys.stderr)
        print("Clone it: git clone -b verisoftbench https://github.com/logiq-ai/verisoftbench-repos.git VeriSoftBench-eval")
        sys.exit(1)

    if args.task_ids:
        task_ids = args.task_ids
    else:
        task_ids = get_task_ids_with_patches(args.patches_dir)

    if not task_ids:
        print("No patches to evaluate. Run connector.collect first.")
        return

    # Write eval config
    EVAL_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    config_path = EVAL_RESULTS_DIR / "eval_config.yaml"
    write_eval_config(args.patches_dir, config_path)

    task_ids_str = ",".join(str(t) for t in task_ids)

    print(f"Evaluating {len(task_ids)} tasks from {args.patches_dir}")
    print(f"Evaluation repo: {eval_repo}")

    cmd = [
        sys.executable, str(eval_repo / "evaluate.py"),
        "--config", str(config_path),
        "--task-ids", task_ids_str,
        "--save-debug-lean",
        "--refresh-cache",
    ]

    result = subprocess.run(cmd, cwd=str(eval_repo))

    if result.returncode != 0:
        print(f"Evaluation failed with exit code {result.returncode}", file=sys.stderr)
        sys.exit(result.returncode)


if __name__ == "__main__":
    main()

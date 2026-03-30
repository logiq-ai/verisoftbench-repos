#!/usr/bin/env python3
"""
Submit a VeriSoftBench task to AlephProver and print the tracking URL.

Usage:
    python submit.py 4
    python submit.py 4 --env dev
    python submit.py 4 --cost-budget 50 --time-budget 600
    python submit.py 4 5 14 --env dev
"""

import argparse
import io
import json
import os
import shutil
import sys
import tarfile
import tempfile
from pathlib import Path

import requests

ENVS = {
    "prod": "https://alephprover.logicalintelligence.com",
    "dev": "https://prover-dev.logicalintelligence.com",
}

SCRIPT_DIR = Path(__file__).resolve().parent
TASKS_JSON = SCRIPT_DIR / "aristotle_tasks.json"


def create_archive(task: dict, repo_base: Path, cost_budget: float, time_budget: int) -> bytes:
    lean_root = task["lean_root"]
    project_dir = repo_base / lean_root

    if not project_dir.exists():
        raise FileNotFoundError(f"Project directory not found: {project_dir}")

    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        shutil.copytree(project_dir, tmp / "project", symlinks=True)

        params = {
            "request_type": "PROVE_SINGLE_THEOREM",
            "job_id": f"verisoftbench-task-{task['id']}",
            "file_path": task["file_path"],
            "theorem_name": task["theorem_name"],
            "cost_budget_dollars": cost_budget,
            "time_budget_minutes": time_budget,
        }
        if task.get("hints"):
            params["hints"] = task["hints"]

        with open(tmp / "user_request_parameters.json", "w") as f:
            json.dump(params, f, indent=2)

        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w:gz") as tar:
            for item in tmp.iterdir():
                tar.add(item, arcname=item.name)
        return buf.getvalue()


def main():
    p = argparse.ArgumentParser(description="Submit VeriSoftBench tasks to AlephProver")
    p.add_argument("task_ids", nargs="+", type=int, help="Task IDs to submit")
    p.add_argument("--env", choices=["prod", "dev"], default="prod")
    p.add_argument("--cost-budget", type=float, default=30.0, help="Cost budget in dollars (default: 30)")
    p.add_argument("--time-budget", type=int, default=60, help="Time budget in minutes (default: 60)")
    p.add_argument("--repo-base", type=Path, default=SCRIPT_DIR, help="Base dir with Lean repos")
    args = p.parse_args()

    api_key = os.environ.get("ALEPH_API_KEY")
    if not api_key:
        print("ERROR: Set ALEPH_API_KEY environment variable", file=sys.stderr)
        sys.exit(1)

    with open(TASKS_JSON) as f:
        tasks_by_id = {t["id"]: t for t in json.load(f)}

    base_url = ENVS[args.env]

    for tid in args.task_ids:
        task = tasks_by_id.get(tid)
        if not task:
            print(f"ERROR: task {tid} not found in {TASKS_JSON}", file=sys.stderr)
            continue

        try:
            archive = create_archive(task, args.repo_base, args.cost_budget, args.time_budget)
            resp = requests.post(
                f"{base_url}/api/v1/requests/upload",
                headers={"Authorization": f"Bearer {api_key}"},
                files={"file": ("archive.tar.gz", archive, "application/gzip")},
                timeout=120,
            )
            resp.raise_for_status()
            request_id = resp.json().get("id", "unknown")
            print(f"{base_url}/requests/{request_id}")
        except Exception as e:
            print(f"ERROR: task {tid}: {e}", file=sys.stderr)


if __name__ == "__main__":
    main()

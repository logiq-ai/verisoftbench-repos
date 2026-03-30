#!/usr/bin/env python3
"""
Submit VeriSoftBench tasks to AlephProver (prod or dev).

Usage:
    # Submit a single task by ID
    python submit.py --task-id 4

    # Submit multiple tasks
    python submit.py --task-id 4,5,14

    # Submit all unsolved tasks
    python submit.py --unsolved

    # Submit to dev instead of prod
    python submit.py --task-id 4 --env dev

    # Custom budget
    python submit.py --task-id 4 --cost-budget 50 --time-budget 600

    # Dry run (show what would be submitted)
    python submit.py --task-id 4 --dry-run
"""

import argparse
import io
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

ENVS = {
    "prod": "https://alephprover.logicalintelligence.com",
    "dev": "https://prover-dev.logicalintelligence.com",
}

API_KEY_ENV = "ALEPH_API_KEY"

SCRIPT_DIR = Path(__file__).resolve().parent
TASKS_JSON = SCRIPT_DIR / "aristotle_tasks.json"
RESULTS_JSON = SCRIPT_DIR / "verisoftbench_final_results.json"


def load_tasks():
    with open(TASKS_JSON) as f:
        return json.load(f)


def load_results():
    with open(RESULTS_JSON) as f:
        return json.load(f)


def save_results(results):
    with open(RESULTS_JSON, "w") as f:
        json.dump(results, f, indent=2)


def get_api_key():
    key = os.environ.get(API_KEY_ENV)
    if not key:
        print(f"ERROR: Set {API_KEY_ENV} environment variable")
        print(f"  export {API_KEY_ENV}=sk-aleph-...")
        sys.exit(1)
    return key


# ---------------------------------------------------------------------------
# Archive creation
# ---------------------------------------------------------------------------

def create_archive(task: dict, repo_base: Path, cost_budget: float, time_budget: int) -> bytes:
    """
    Create a tar.gz archive for submission to AlephProver.

    Structure:
      project/           — the Lean project directory
      user_request_parameters.json  — request config
    """
    lean_root = task["lean_root"]
    project_dir = repo_base / lean_root

    if not project_dir.exists():
        raise FileNotFoundError(f"Project directory not found: {project_dir}")

    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)

        # Copy project
        shutil.copytree(project_dir, tmp / "project", symlinks=True)

        # Create request parameters
        params = {
            "request_type": "PROVE_SINGLE_THEOREM",
            "job_id": f"verisoftbench-task-{task['id']}",
            "file_path": task["file_path"],
            "theorem_name": task["theorem_name"],
            "cost_budget_dollars": cost_budget,
            "time_budget_minutes": time_budget,
        }

        # Add hints if available
        if task.get("hints"):
            params["hints"] = task["hints"]

        with open(tmp / "user_request_parameters.json", "w") as f:
            json.dump(params, f, indent=2)

        # Create tar.gz
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w:gz") as tar:
            for item in tmp.iterdir():
                tar.add(item, arcname=item.name)
        return buf.getvalue()


# ---------------------------------------------------------------------------
# API submission
# ---------------------------------------------------------------------------

def submit_task(archive_bytes: bytes, env: str, api_key: str) -> dict:
    """Submit archive to AlephProver API. Returns the response JSON."""
    import requests

    base_url = ENVS[env]
    url = f"{base_url}/api/v1/requests/upload"

    headers = {"Authorization": f"Bearer {api_key}"}
    files = {"file": ("archive.tar.gz", archive_bytes, "application/gzip")}

    resp = requests.post(url, headers=headers, files=files, timeout=120)
    resp.raise_for_status()
    return resp.json()


def check_status(request_id: str, env: str, api_key: str) -> dict:
    """Check status of a proof request."""
    import requests

    base_url = ENVS[env]
    url = f"{base_url}/api/v1/requests/{request_id}"
    headers = {"Authorization": f"Bearer {api_key}"}

    resp = requests.get(url, headers=headers, timeout=30)
    resp.raise_for_status()
    return resp.json()


def get_patch(request_id: str, env: str, api_key: str) -> str:
    """Download the .patch file for a completed proof request."""
    import requests

    base_url = ENVS[env]
    url = f"{base_url}/api/v1/requests/{request_id}/patch"
    headers = {"Authorization": f"Bearer {api_key}"}

    resp = requests.get(url, headers=headers, timeout=30)
    resp.raise_for_status()
    return resp.text


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args():
    p = argparse.ArgumentParser(description="Submit VeriSoftBench tasks to AlephProver")
    group = p.add_mutually_exclusive_group(required=True)
    group.add_argument("--task-id", type=str, help="Comma-separated task IDs (e.g. 4,5,14)")
    group.add_argument("--unsolved", action="store_true", help="Submit all unsolved tasks")
    group.add_argument("--status", type=str, help="Check status of a request ID")

    p.add_argument("--env", choices=["prod", "dev"], default="prod", help="Target environment (default: prod)")
    p.add_argument("--cost-budget", type=float, default=30.0, help="Cost budget in dollars (default: 30)")
    p.add_argument("--time-budget", type=int, default=60, help="Time budget in minutes (default: 60)")
    p.add_argument("--repo-base", type=Path, default=SCRIPT_DIR, help="Base directory containing Lean repos")
    p.add_argument("--dry-run", action="store_true", help="Show what would be submitted without submitting")
    p.add_argument("--update-results", action="store_true", help="Update verisoftbench_final_results.json with new request IDs")
    return p.parse_args()


def main():
    args = parse_args()

    # Handle status check
    if args.status:
        api_key = get_api_key()
        result = check_status(args.status, args.env, api_key)
        print(json.dumps(result, indent=2))
        return

    # Load tasks
    all_tasks = load_tasks()
    tasks_by_id = {t["id"]: t for t in all_tasks}

    # Determine which tasks to submit
    if args.unsolved:
        results = load_results()
        unsolved_ids = [r["task_id"] for r in results if r["status"] != "completed"]
        task_ids = unsolved_ids
    else:
        task_ids = [int(x.strip()) for x in args.task_id.split(",")]

    # Validate
    for tid in task_ids:
        if tid not in tasks_by_id:
            print(f"ERROR: Task {tid} not found in {TASKS_JSON}")
            sys.exit(1)

    print(f"Tasks to submit: {len(task_ids)}")
    print(f"Environment: {args.env} ({ENVS[args.env]})")
    print(f"Budget: ${args.cost_budget} / {args.time_budget}min")
    print()

    if args.dry_run:
        for tid in task_ids:
            task = tasks_by_id[tid]
            print(f"  [{tid:>3}] {task['theorem_name']:50s} ({task['lean_root']})")
        print(f"\nDry run — nothing submitted.")
        return

    api_key = get_api_key()
    results_data = load_results() if args.update_results else None
    results_by_id = {r["task_id"]: r for r in results_data} if results_data else {}

    submitted = []
    for tid in task_ids:
        task = tasks_by_id[tid]
        print(f"  [{tid:>3}] {task['theorem_name'][:50]:50s} ", end="", flush=True)

        try:
            archive = create_archive(task, args.repo_base, args.cost_budget, args.time_budget)
            resp = submit_task(archive, args.env, api_key)
            request_id = resp.get("id", "unknown")
            base_url = ENVS[args.env]
            track_url = f"{base_url}/requests/{request_id}"
            print(f"OK  {track_url}")

            submitted.append({
                "task_id": tid,
                "theorem_name": task["theorem_name"],
                "request_id": request_id,
                "env": args.env,
                "track_url": track_url,
                "api_url": f"{base_url}/requests/{request_id}",
            })

            # Update results JSON
            if results_data and tid in results_by_id:
                entry = results_by_id[tid]
                entry["request_id"] = request_id
                entry["env"] = args.env
                entry["api_url"] = f"{base_url}/requests/{request_id}"
                entry["status"] = "running"
                entry["failure_reason"] = None

        except Exception as e:
            print(f"FAIL  {e}")

    print(f"\nSubmitted: {len(submitted)}/{len(task_ids)}")

    if args.update_results and results_data:
        save_results(results_data)
        print(f"Updated {RESULTS_JSON}")

    # Print summary
    if submitted:
        print("\n--- Submission Summary ---")
        for s in submitted:
            print(f"  Task {s['task_id']:>3}: {s['track_url']}")


if __name__ == "__main__":
    main()

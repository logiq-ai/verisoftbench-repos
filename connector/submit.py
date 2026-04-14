#!/usr/bin/env python3
"""Submit VeriSoftBench tasks to AlephProver.

Usage:
    python -m connector.submit
    python -m connector.submit --task-ids 4 29 122
    python -m connector.submit --api-url https://prover-dev.logicalintelligence.com
"""

import argparse
import json
import logging
import os
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import requests

log = logging.getLogger(__name__)

from connector.config import (
    ALEPH_API_KEY_ENV, ALEPH_API_URL, BRANCH, DEFAULT_COST_BUDGET_USD,
    DEFAULT_TIME_BUDGET_MINUTES, EVAL_PROMPT, MAX_SUBMIT_RETRIES,
    REPO_URL, RESULTS_JSON, SUBMIT_RETRY_DELAY, TASKS_JSON,
    THEOREM_NAME_OVERRIDES,
)


def load_tasks():
    with open(TASKS_JSON) as f:
        return {t["id"]: t for t in json.load(f)}


def submit_task(task, api_url, api_key):
    """Submit a single task. Retries on 402 (concurrent limit)."""
    tid = task["id"]
    theorem_name = THEOREM_NAME_OVERRIDES.get(tid, task["theorem_name"])
    file_path = f"{task['lean_root']}/{task['file_path']}"

    # Combine task-specific hints from the benchmark with the generic eval prompt
    task_hints = task.get("hints", "")
    hints = f"{task_hints}\n\n{EVAL_PROMPT}" if task_hints else EVAL_PROMPT

    payload = {
        "repository_url": REPO_URL,
        "branch": BRANCH,
        "file_path": file_path,
        "theorem_name": theorem_name,
        "hints": hints,
        "time_budget_minutes": DEFAULT_TIME_BUDGET_MINUTES,
        "cost_budget_usd": DEFAULT_COST_BUDGET_USD,
    }

    for attempt in range(MAX_SUBMIT_RETRIES):
        resp = requests.post(
            f"{api_url}/api/v1/requests",
            headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
            json=payload,
            timeout=120,
        )
        if resp.status_code == 201:
            request_id = resp.json()["id"]
            return {
                "task_id": tid,
                "theorem_name": theorem_name,
                "lean_root": task["lean_root"],
                "request_id": request_id,
                "api_url": f"{api_url}/requests/{request_id}",
                "status": "submitted",
                "submitted_at": datetime.now(timezone.utc).isoformat(),
            }
        elif resp.status_code in (402, 500, 502, 503, 504):
            log.warning(f"[{tid}] HTTP {resp.status_code}, retry {attempt+1}/{MAX_SUBMIT_RETRIES}")
            time.sleep(SUBMIT_RETRY_DELAY)
        else:
            log.error(f"[{tid}] HTTP {resp.status_code}: {resp.text[:100]}")
            return None

    log.error(f"[{tid}] gave up after {MAX_SUBMIT_RETRIES} retries")
    return None


def save_results(results, path):
    with open(path, "w") as f:
        json.dump(results, f, indent=2)


def main():
    p = argparse.ArgumentParser(description="Submit VeriSoftBench tasks to AlephProver")
    p.add_argument("--task-ids", nargs="*", type=int, help="Task IDs (default: all 100)")
    p.add_argument("--api-url", default=ALEPH_API_URL, help=f"API URL (default: {ALEPH_API_URL})")
    p.add_argument("--output", type=Path, default=RESULTS_JSON, help=f"Results JSON (default: {RESULTS_JSON})")
    args = p.parse_args()

    api_key = os.environ.get(ALEPH_API_KEY_ENV)
    if not api_key:
        print(f"ERROR: Set {ALEPH_API_KEY_ENV} environment variable", file=sys.stderr)
        sys.exit(1)

    tasks = load_tasks()
    task_ids = args.task_ids or sorted(tasks.keys())

    # Load existing results (append-only)
    results = []
    if args.output.exists():
        with open(args.output) as f:
            results = json.load(f)

    print(f"Submitting {len(task_ids)} tasks to {args.api_url}")

    for tid in task_ids:
        task = tasks.get(tid)
        if not task:
            print(f"[{tid}] not found in {TASKS_JSON}", file=sys.stderr)
            continue

        result = submit_task(task, args.api_url, api_key)
        if result:
            print(f"[{tid:>3}] {result['api_url']}")
            results.append(result)
            save_results(results, args.output)

    print(f"\n{len(results)} total entries in {args.output}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Check status of proof requests and update results + patches.

Queries the AlephProver API for each tracked request. Updates
verisoftbench_final_results.json and downloads .patch files for
completed tasks.

Usage:
    # Check all non-completed tasks in results JSON
    python update_results.py

    # Check specific tasks
    python update_results.py 122 127

    # Import runs from a tracking file (written by submit.py -o),
    # then check their status
    python update_results.py --from-file runs.json

    # Check everything, including already-completed tasks
    python update_results.py --all

    # Just print status, don't write anything
    python update_results.py --dry-run
"""

import argparse
import json
import os
import sys
from collections import defaultdict
from pathlib import Path

import requests

SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_JSON = SCRIPT_DIR / "verisoftbench_final_results.json"
PATCHES_DIR = SCRIPT_DIR / "patches"

ENVS = {
    "prod": "https://alephprover.logicalintelligence.com",
    "dev": "https://prover-dev.logicalintelligence.com",
}


def get_base_url(entry: dict) -> str:
    api_url = entry.get("api_url", "")
    if "/requests/" in api_url:
        return api_url.split("/requests/")[0]
    return ENVS.get(entry.get("env", "prod"), ENVS["prod"])


def fetch_status(request_id: str, base_url: str, api_key: str) -> dict | None:
    url = f"{base_url}/api/v1/requests/{request_id}"
    try:
        resp = requests.get(url, headers={"Authorization": f"Bearer {api_key}"}, timeout=30)
        if resp.status_code == 200:
            return resp.json()
    except Exception as e:
        print(f"    fetch error: {e}", file=sys.stderr)
    return None


def fetch_patch(request_id: str, base_url: str, api_key: str) -> str | None:
    url = f"{base_url}/api/v1/requests/{request_id}/patch"
    try:
        resp = requests.get(url, headers={"Authorization": f"Bearer {api_key}"}, timeout=30)
        if resp.status_code == 200 and resp.text.strip():
            return resp.text
    except Exception as e:
        print(f"    patch fetch error: {e}", file=sys.stderr)
    return None


def main():
    p = argparse.ArgumentParser(description="Check proof request status and update results + patches")
    p.add_argument("task_ids", nargs="*", type=int, help="Task IDs to check (default: all non-completed)")
    p.add_argument("--all", action="store_true", help="Check all tasks, including completed ones")
    p.add_argument("--from-file", type=Path, default=None,
                   help="Import runs from tracking JSON (written by submit.py -o). "
                        "Supports multiple runs per task.")
    p.add_argument("--dry-run", action="store_true", help="Print status without writing files")
    args = p.parse_args()

    api_key = os.environ.get("ALEPH_API_KEY")
    if not api_key:
        print("ERROR: Set ALEPH_API_KEY environment variable", file=sys.stderr)
        sys.exit(1)

    with open(RESULTS_JSON) as f:
        results = json.load(f)
    results_by_id = {r["task_id"]: r for r in results}

    # Collect all runs to check: {task_id: [{request_id, base_url, ...}, ...]}
    runs_to_check: dict[int, list[dict]] = defaultdict(list)

    # Import from tracking file (may have multiple runs per task)
    if args.from_file and args.from_file.exists():
        with open(args.from_file) as f:
            tracking = json.load(f)
        for run in tracking:
            tid = run["task_id"]
            runs_to_check[tid].append({
                "request_id": run["request_id"],
                "base_url": get_base_url(run),
                "env": run.get("env", "prod"),
                "api_url": run.get("api_url", ""),
            })
        print(f"Loaded {len(tracking)} runs from {args.from_file}")

    # Also include runs from results JSON
    for r in results:
        tid = r["task_id"]
        if r.get("request_id"):
            runs_to_check[tid].append({
                "request_id": r["request_id"],
                "base_url": get_base_url(r),
                "env": r.get("env", "prod"),
                "api_url": r.get("api_url", ""),
            })

    # Determine which tasks to check
    if args.task_ids:
        check_ids = set(args.task_ids)
    elif args.all:
        check_ids = set(runs_to_check.keys())
    else:
        check_ids = {tid for tid in runs_to_check
                     if results_by_id.get(tid, {}).get("status") != "completed"}

    if not check_ids:
        print("Nothing to check.")
        return

    PATCHES_DIR.mkdir(parents=True, exist_ok=True)
    changed = False

    for tid in sorted(check_ids):
        runs = runs_to_check.get(tid, [])
        if not runs:
            continue

        entry = results_by_id.get(tid)
        thm = entry.get("thm_name", "?") if entry else "?"

        # Deduplicate by request_id
        seen_ids = set()
        unique_runs = []
        for run in runs:
            if run["request_id"] not in seen_ids:
                seen_ids.add(run["request_id"])
                unique_runs.append(run)

        # Check each run, find best result
        best_status = None
        best_run = None

        for run in unique_runs:
            status_data = fetch_status(run["request_id"], run["base_url"], api_key)
            if not status_data:
                env_label = f"[{run['env']}]" if len(unique_runs) > 1 else ""
                print(f"  {tid:>3}  {thm[:45]:45s}  {env_label} fetch failed")
                continue

            api_status = status_data.get("status", "unknown")
            stage = status_data.get("stage", "")
            pr_url = status_data.get("pr_url")

            env_label = f"[{run['env']}]" if len(unique_runs) > 1 else ""
            status_str = api_status
            if stage:
                status_str += f" ({stage})"
            print(f"  {tid:>3}  {thm[:45]:45s}  {env_label} {status_str}")

            # Prefer completed, then running, then anything
            if api_status == "completed" and best_status != "completed":
                best_status = "completed"
                best_run = {**run, "pr_url": pr_url}
            elif best_status is None:
                best_status = api_status
                best_run = {**run, "pr_url": pr_url}

        if args.dry_run or not best_run or not entry:
            continue

        # Update results entry with best run
        old_status = entry.get("status")
        if best_status and best_status != old_status:
            entry["status"] = best_status
            changed = True
        if best_run.get("request_id") != entry.get("request_id"):
            entry["request_id"] = best_run["request_id"]
            entry["api_url"] = best_run.get("api_url", "")
            entry["env"] = best_run.get("env", "prod")
            changed = True
        if best_run.get("pr_url") and best_run["pr_url"] != entry.get("pr_url"):
            entry["pr_url"] = best_run["pr_url"]
            changed = True

        # Download patch if completed and not on disk
        if best_status == "completed":
            patch_file = PATCHES_DIR / f"task_{tid:03d}.patch"
            if not patch_file.exists():
                patch = fetch_patch(best_run["request_id"], best_run["base_url"], api_key)
                if patch:
                    patch_file.write_text(patch)
                    print(f"        -> downloaded {patch_file.name} ({len(patch)} bytes)")

    if changed and not args.dry_run:
        with open(RESULTS_JSON, "w") as f:
            json.dump(results, f, indent=2)
        print(f"\nUpdated {RESULTS_JSON}")
    elif not args.dry_run:
        print("\nNo changes.")


if __name__ == "__main__":
    main()

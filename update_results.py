#!/usr/bin/env python3
"""
Check status of proof requests and update results + patches.

For each task in verisoftbench_final_results.json that has a request_id,
queries the AlephProver API for current status. If completed, downloads
the .patch file. Updates the JSON with latest status/PR URL.

Usage:
    # Check and update all tasks that aren't completed yet
    python update_results.py

    # Check specific tasks
    python update_results.py 122 127

    # Check all tasks (including already-completed ones)
    python update_results.py --all

    # Just print status, don't write anything
    python update_results.py --dry-run
"""

import argparse
import json
import os
import sys
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
    p.add_argument("--dry-run", action="store_true", help="Print status without writing files")
    args = p.parse_args()

    api_key = os.environ.get("ALEPH_API_KEY")
    if not api_key:
        print("ERROR: Set ALEPH_API_KEY environment variable", file=sys.stderr)
        sys.exit(1)

    with open(RESULTS_JSON) as f:
        results = json.load(f)

    results_by_id = {r["task_id"]: r for r in results}

    # Determine which tasks to check
    if args.task_ids:
        task_ids = args.task_ids
    elif args.all:
        task_ids = [r["task_id"] for r in results if r.get("request_id")]
    else:
        task_ids = [r["task_id"] for r in results if r.get("request_id") and r.get("status") != "completed"]

    if not task_ids:
        print("Nothing to check.")
        return

    PATCHES_DIR.mkdir(parents=True, exist_ok=True)
    changed = False

    for tid in sorted(task_ids):
        entry = results_by_id.get(tid)
        if not entry or not entry.get("request_id"):
            continue

        request_id = entry["request_id"]
        base_url = get_base_url(entry)
        thm = entry.get("thm_name", "?")

        status_data = fetch_status(request_id, base_url, api_key)
        if not status_data:
            print(f"  {tid:>3}  {thm[:45]:45s}  fetch failed")
            continue

        api_status = status_data.get("status", "unknown")
        stage = status_data.get("stage", "")
        pr_url = status_data.get("pr_url") or entry.get("pr_url")
        old_status = entry.get("status")

        # Status line
        status_str = api_status
        if stage:
            status_str += f" ({stage})"
        marker = ""
        if old_status != api_status:
            marker = f"  <- was {old_status}"
        print(f"  {tid:>3}  {thm[:45]:45s}  {status_str}{marker}")

        if args.dry_run:
            continue

        # Update entry
        if api_status != old_status:
            entry["status"] = api_status
            changed = True
        if pr_url and pr_url != entry.get("pr_url"):
            entry["pr_url"] = pr_url
            changed = True

        # Download patch if completed and not on disk
        if api_status == "completed":
            patch_file = PATCHES_DIR / f"task_{tid:03d}.patch"
            if not patch_file.exists():
                patch = fetch_patch(request_id, base_url, api_key)
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

#!/usr/bin/env python3
"""Poll AlephProver for results and download patches.

Usage:
    python -m connector.collect
    python -m connector.collect --task-ids 4 29
    python -m connector.collect --status-only
"""

import argparse
import json
import os
import sys
import time
from pathlib import Path

import requests

from connector.config import (
    ALEPH_API_KEY_ENV, MAX_POLL_TIME, PATCHES_DIR, POLL_INTERVAL, RESULTS_JSON,
)


def load_results():
    if not RESULTS_JSON.exists():
        return []
    with open(RESULTS_JSON) as f:
        return json.load(f)


def save_results(results):
    with open(RESULTS_JSON, "w") as f:
        json.dump(results, f, indent=2)


def get_base_url(entry):
    api_url = entry.get("api_url", "")
    if "/requests/" in api_url:
        return api_url.split("/requests/")[0]
    return "https://alephprover.logicalintelligence.com"


def fetch_status(request_id, base_url, api_key):
    try:
        resp = requests.get(
            f"{base_url}/api/v1/requests/{request_id}",
            headers={"Authorization": f"Bearer {api_key}"},
            timeout=15,
        )
        if resp.status_code == 200:
            return resp.json()
    except Exception as e:
        print(f"  fetch error: {e}", file=sys.stderr)
    return None


def download_patch(request_id, base_url, api_key, task_id):
    """Download .patch file. Returns path or None."""
    PATCHES_DIR.mkdir(parents=True, exist_ok=True)
    patch_file = PATCHES_DIR / f"task_{task_id:03d}.patch"

    try:
        resp = requests.get(
            f"{base_url}/api/v1/requests/{request_id}/diff",
            headers={"Authorization": f"Bearer {api_key}"},
            timeout=30,
        )
        if resp.status_code == 200 and resp.text.strip():
            patch_file.write_text(resp.text)
            return patch_file
    except Exception as e:
        print(f"  patch download error: {e}", file=sys.stderr)
    return None


def main():
    p = argparse.ArgumentParser(description="Collect AlephProver results and download patches")
    p.add_argument("--task-ids", nargs="*", type=int, help="Task IDs (default: all non-completed)")
    p.add_argument("--status-only", action="store_true", help="Print status without downloading")
    p.add_argument("--wait", action="store_true", help="Poll until all tasks complete or timeout")
    args = p.parse_args()

    api_key = os.environ.get(ALEPH_API_KEY_ENV)
    if not api_key:
        print(f"ERROR: Set {ALEPH_API_KEY_ENV} environment variable", file=sys.stderr)
        sys.exit(1)

    results = load_results()
    if not results:
        print("No results to collect. Run connector.submit first.")
        return

    # Deduplicate: keep latest entry per task_id
    by_id = {}
    for r in results:
        by_id[r["task_id"]] = r

    if args.task_ids:
        check_ids = set(args.task_ids)
    else:
        check_ids = {tid for tid, r in by_id.items() if r.get("status") not in ("completed", "failed")}

    if not check_ids:
        print("All tasks already completed/failed.")
        return

    start_time = time.time()

    while True:
        completed = running = failed = 0

        for tid in sorted(check_ids):
            entry = by_id.get(tid)
            if not entry or not entry.get("request_id"):
                continue

            base_url = get_base_url(entry)
            data = fetch_status(entry["request_id"], base_url, api_key)
            if not data:
                continue

            status = data.get("status", "?")
            stage = data.get("stage", "")
            pr_url = data.get("pr_url")

            entry["status"] = status
            if pr_url:
                entry["pr_url"] = pr_url

            if status == "completed":
                completed += 1
                if not args.status_only:
                    patch = download_patch(entry["request_id"], base_url, api_key, tid)
                    if patch:
                        print(f"[{tid:>3}] completed  {patch.name}")
                    else:
                        print(f"[{tid:>3}] completed  (patch download failed)")
                else:
                    print(f"[{tid:>3}] completed  {stage}")
            elif status == "running":
                running += 1
                print(f"[{tid:>3}] running    {stage}")
            elif status == "failed":
                failed += 1
                print(f"[{tid:>3}] failed     {stage}")
            else:
                print(f"[{tid:>3}] {status}")

        # Save updated statuses
        save_results(list(by_id.values()))

        print(f"\nCompleted: {completed}, Running: {running}, Failed: {failed}")

        if not args.wait or running == 0:
            break

        elapsed = time.time() - start_time
        if elapsed > MAX_POLL_TIME:
            print(f"Timeout after {elapsed:.0f}s")
            break

        print(f"Waiting {POLL_INTERVAL}s...")
        time.sleep(POLL_INTERVAL)

    patches = len(list(PATCHES_DIR.glob("task_*.patch"))) if PATCHES_DIR.exists() else 0
    print(f"Patches on disk: {patches}")


if __name__ == "__main__":
    main()

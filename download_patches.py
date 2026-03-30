#!/usr/bin/env python3
"""
Download patches from AlephProver API for completed proof requests.

Reads verisoftbench_final_results.json, fetches .patch files for all
completed tasks, and stores them in patches/ directory. Skips tasks
that already have a patch on disk.

Usage:
    # Download all completed patches
    python download_patches.py

    # Download specific tasks
    python download_patches.py --task-id 4,5,14

    # Force re-download (overwrite existing)
    python download_patches.py --force

    # Download from dev environment
    python download_patches.py --task-id 4 --env dev
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

API_KEY_ENV = "ALEPH_API_KEY"

ENVS = {
    "prod": "https://alephprover.logicalintelligence.com",
    "dev": "https://prover-dev.logicalintelligence.com",
}


def load_results():
    with open(RESULTS_JSON) as f:
        return json.load(f)


def get_api_key():
    key = os.environ.get(API_KEY_ENV)
    if not key:
        print(f"ERROR: Set {API_KEY_ENV} environment variable")
        sys.exit(1)
    return key


def fetch_patch(request_id: str, base_url: str, api_key: str) -> str | None:
    """Fetch .patch content from the API. Returns None on failure."""
    url = f"{base_url}/api/v1/requests/{request_id}/patch"
    headers = {"Authorization": f"Bearer {api_key}"}
    try:
        resp = requests.get(url, headers=headers, timeout=30)
        if resp.status_code == 200 and resp.text.strip():
            return resp.text
        return None
    except Exception as e:
        print(f"    fetch error: {e}")
        return None


def main():
    p = argparse.ArgumentParser(description="Download patches from AlephProver API")
    p.add_argument("--task-id", type=str, help="Comma-separated task IDs (default: all completed)")
    p.add_argument("--env", choices=["prod", "dev", "auto"], default="auto",
                   help="Environment (default: auto, uses env from results JSON)")
    p.add_argument("--force", action="store_true", help="Re-download even if patch exists on disk")
    p.add_argument("--patches-dir", type=Path, default=PATCHES_DIR, help="Output directory")
    args = p.parse_args()

    results = load_results()
    results_by_id = {r["task_id"]: r for r in results}
    api_key = get_api_key()

    # Determine which tasks to download
    if args.task_id:
        task_ids = [int(x.strip()) for x in args.task_id.split(",")]
    else:
        task_ids = [r["task_id"] for r in results if r["status"] == "completed"]

    args.patches_dir.mkdir(parents=True, exist_ok=True)

    downloaded = 0
    skipped = 0
    failed = 0

    for tid in sorted(task_ids):
        patch_file = args.patches_dir / f"task_{tid:03d}.patch"
        entry = results_by_id.get(tid)

        if not entry:
            print(f"  [{tid:>3}] not found in results JSON")
            failed += 1
            continue

        request_id = entry.get("request_id")
        if not request_id:
            print(f"  [{tid:>3}] no request_id")
            failed += 1
            continue

        # Skip if already on disk (unless --force)
        if patch_file.exists() and not args.force:
            skipped += 1
            continue

        # Determine base URL
        if args.env == "auto":
            api_url = entry.get("api_url", "")
            if "/requests/" in api_url:
                base_url = api_url.split("/requests/")[0]
            else:
                base_url = ENVS.get(entry.get("env", "prod"), ENVS["prod"])
        else:
            base_url = ENVS[args.env]

        thm_name = entry.get("thm_name", "?")
        print(f"  [{tid:>3}] {thm_name[:50]:50s} ", end="", flush=True)

        patch = fetch_patch(request_id, base_url, api_key)
        if patch:
            patch_file.write_text(patch)
            size = len(patch)
            print(f"OK ({size} bytes)")
            downloaded += 1
        else:
            print(f"FAIL")
            failed += 1

    print(f"\nDone: {downloaded} downloaded, {skipped} skipped (exist), {failed} failed")
    print(f"Patches dir: {args.patches_dir}")


if __name__ == "__main__":
    main()

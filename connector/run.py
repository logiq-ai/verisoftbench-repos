#!/usr/bin/env python3
"""Main orchestrator: submit → collect → evaluate, with optional proof retries.

Usage:
    python3 -m connector.run
    python3 -m connector.run --skip-submit
    python3 -m connector.run --skip-submit --skip-collect
    python3 -m connector.run --task-ids 4 29 122
    python3 -m connector.run --no-retries
"""

import argparse
import json
import logging
import sys
from datetime import datetime
from pathlib import Path

from connector.config import (
    ALEPH_API_URL, EVAL_RESULTS_DIR, MAX_PROOF_RETRIES, PATCHES_DIR, RESULTS_JSON,
)

LOG_FORMAT = "%(asctime)s %(levelname)s %(message)s"


def setup_logging():
    EVAL_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = EVAL_RESULTS_DIR / f"run_{timestamp}.log"

    logging.basicConfig(
        level=logging.INFO,
        format=LOG_FORMAT,
        handlers=[
            logging.StreamHandler(sys.stdout),
            logging.FileHandler(log_file),
        ],
    )
    logging.info(f"Log file: {log_file}")
    return log_file


def run_submit(task_ids, api_url):
    logging.info(f"Submitting {len(task_ids) if task_ids else 'all'} tasks to {api_url}")
    from connector.submit import load_tasks, submit_task, save_results
    import os
    from connector.config import ALEPH_API_KEY_ENV

    api_key = os.environ.get(ALEPH_API_KEY_ENV)
    tasks = load_tasks()
    ids = task_ids or sorted(tasks.keys())

    results = []
    if RESULTS_JSON.exists():
        with open(RESULTS_JSON) as f:
            results = json.load(f)

    submitted = 0
    for tid in ids:
        task = tasks.get(tid)
        if not task:
            logging.warning(f"Task {tid} not found")
            continue
        result = submit_task(task, api_url, api_key)
        if result:
            logging.info(f"[{tid:>3}] submitted: {result['request_id']}")
            results.append(result)
            save_results(results, RESULTS_JSON)
            submitted += 1
        else:
            logging.error(f"[{tid:>3}] submission failed")

    logging.info(f"Submitted {submitted}/{len(ids)} tasks")
    return submitted


def run_collect(task_ids):
    logging.info("Collecting results and downloading patches")
    from connector.collect import load_results, save_results, get_base_url, fetch_status, download_patch
    import time
    from connector.config import POLL_INTERVAL, MAX_POLL_TIME

    # Wait briefly for newly submitted tasks to register
    time.sleep(10)

    results = load_results()
    by_id = {}
    for r in results:
        by_id[r["task_id"]] = r

    check_ids = set(task_ids) if task_ids else {tid for tid, r in by_id.items() if r.get("status") not in ("completed", "failed")}

    if not check_ids:
        logging.info("All tasks already completed/failed")
        return

    import os
    from connector.config import ALEPH_API_KEY_ENV
    api_key = os.environ.get(ALEPH_API_KEY_ENV)

    start = time.time()
    first_poll = True
    while True:
        completed = running = failed = pending = 0
        for tid in sorted(check_ids):
            entry = by_id.get(tid)
            if not entry:
                continue
            base_url = get_base_url(entry)
            data = fetch_status(entry["request_id"], base_url, api_key)
            if not data:
                pending += 1
                continue

            status = data.get("status", "?")
            entry["status"] = status
            if data.get("pr_url"):
                entry["pr_url"] = data["pr_url"]

            if status == "completed":
                completed += 1
                patch = download_patch(entry["request_id"], base_url, api_key, tid)
                if patch:
                    logging.info(f"[{tid:>3}] completed, patch: {patch.name}")
                else:
                    logging.warning(f"[{tid:>3}] completed but patch download failed")
            elif status in ("running", "submitted"):
                running += 1
            elif status == "failed":
                failed += 1
                logging.warning(f"[{tid:>3}] failed at {data.get('stage', '?')}")
            else:
                pending += 1

        save_results(list(by_id.values()))
        logging.info(f"Status: completed={completed} running={running} failed={failed} pending={pending}")

        if running == 0 and pending == 0 and not first_poll:
            break
        first_poll = False
        if time.time() - start > MAX_POLL_TIME:
            logging.warning(f"Timeout after {MAX_POLL_TIME}s, {running} still running")
            break

        time.sleep(POLL_INTERVAL)


def run_evaluate(task_ids):
    """Run evaluation, return dict of {task_id: passed}."""
    logging.info("Evaluating patches")
    from connector.evaluate import get_task_ids_with_patches, write_eval_config, find_eval_repo
    import subprocess

    eval_repo = find_eval_repo()
    if not eval_repo:
        logging.error("VeriSoftBench evaluation repo not found")
        return {}

    ids = task_ids or get_task_ids_with_patches(PATCHES_DIR)
    if not ids:
        logging.info("No patches to evaluate")
        return {}

    EVAL_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    config_path = EVAL_RESULTS_DIR / "eval_config.yaml"
    write_eval_config(PATCHES_DIR, config_path)

    task_ids_str = ",".join(str(t) for t in ids)
    logging.info(f"Evaluating {len(ids)} tasks")

    cmd = [
        sys.executable, str(eval_repo / "evaluate.py"),
        "--config", str(config_path),
        "--task-ids", task_ids_str,
        "--save-debug-lean",
        "--refresh-cache",
    ]
    subprocess.run(cmd, cwd=str(eval_repo))

    # Parse results — scan ALL run dirs for the latest results per theorem
    results = {}
    results_dir = eval_repo / "results" / "data"
    if results_dir.exists():
        for run_dir in sorted([d for d in results_dir.iterdir() if d.is_dir()], key=lambda p: p.name):
            details_dir = run_dir / "details"
            if not details_dir.exists():
                continue
            for f in details_dir.glob("*.json"):
                try:
                    d = json.loads(f.read_text())
                    thm = d.get("thm_name", "")
                    success = d.get("success", False)
                    results[thm] = success

                    if success:
                        proofs = d.get("generated_proofs", [])
                        for i, p in enumerate(proofs):
                            if p.get("err_msg") is None:
                                if i > 0:
                                    logging.info(f"  {thm}: passed on sample {i} (earlier samples failed)")
                                else:
                                    logging.info(f"  {thm}: passed")
                                break
                    else:
                        proofs = d.get("generated_proofs", [])
                        err = proofs[0].get("err_msg", "")[:80] if proofs else "no proof"
                        logging.info(f"  {thm}: FAILED — {err}")
                except Exception:
                    pass

    passed = sum(1 for v in results.values() if v)
    total = len(results)
    logging.info(f"Evaluation: {passed}/{total} passed")
    return results


def get_failed_task_ids(eval_results, task_ids_attempted):
    """Find task IDs that failed evaluation (have patches but didn't pass)."""
    from connector.config import TASKS_JSON
    with open(TASKS_JSON) as f:
        tasks = {t["theorem_name"]: t["id"] for t in json.load(f)}

    failed = []
    for thm_name, passed in eval_results.items():
        if not passed:
            tid = tasks.get(thm_name)
            if tid and tid in task_ids_attempted:
                failed.append(tid)
    return failed


def main():
    p = argparse.ArgumentParser(description="Run full VeriSoftBench evaluation pipeline")
    p.add_argument("--task-ids", nargs="*", type=int, help="Task IDs (default: all 100)")
    p.add_argument("--api-url", default=ALEPH_API_URL)
    p.add_argument("--skip-submit", action="store_true")
    p.add_argument("--skip-collect", action="store_true")
    p.add_argument("--no-retries", action="store_true", help="Disable proof request retries")
    args = p.parse_args()

    log_file = setup_logging()
    logging.info(f"Pipeline started. API: {args.api_url}")
    logging.info(f"Retries: {'disabled' if args.no_retries else f'up to {MAX_PROOF_RETRIES}'}")

    task_ids = args.task_ids
    max_retries = 0 if args.no_retries else MAX_PROOF_RETRIES

    for attempt in range(1 + max_retries):
        if attempt > 0:
            logging.info(f"\n{'='*60}")
            logging.info(f"RETRY {attempt}/{max_retries}: resubmitting {len(task_ids)} failed tasks")
            logging.info(f"{'='*60}")

        # Step 1: Submit
        if not args.skip_submit:
            logging.info(f"\n{'='*60}\nSTEP 1: Submit\n{'='*60}")
            run_submit(task_ids, args.api_url)

        # Step 2: Collect
        if not args.skip_collect:
            logging.info(f"\n{'='*60}\nSTEP 2: Collect\n{'='*60}")
            run_collect(task_ids)

        # Step 3: Evaluate
        logging.info(f"\n{'='*60}\nSTEP 3: Evaluate\n{'='*60}")
        eval_results = run_evaluate(task_ids)

        # Check for failures to retry
        attempted = set(task_ids) if task_ids else set(range(1, 501))
        failed_ids = get_failed_task_ids(eval_results, attempted)

        if not failed_ids or attempt >= max_retries:
            break

        logging.info(f"{len(failed_ids)} tasks failed evaluation, will retry: {failed_ids}")
        task_ids = failed_ids
        args.skip_submit = False
        args.skip_collect = False

    passed = sum(1 for v in eval_results.values() if v) if eval_results else 0
    total = len(eval_results) if eval_results else 0
    logging.info(f"\n{'='*60}")
    logging.info(f"FINAL: {passed}/{total} passed")
    logging.info(f"Log: {log_file}")
    logging.info(f"{'='*60}")


if __name__ == "__main__":
    main()

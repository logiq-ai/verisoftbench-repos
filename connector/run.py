#!/usr/bin/env python3
"""Main orchestrator: submit → collect → evaluate, with optional proof retries.

Usage:
    python3 -m connector.run
    python3 -m connector.run --run-dir runs/my_experiment
    python3 -m connector.run --skip-submit --skip-collect
    python3 -m connector.run --task-ids 4 29 122
    python3 -m connector.run --no-retries
"""

import argparse
import json
import logging
import os
import sys
import time
from datetime import datetime
from pathlib import Path

import connector.config as config

LOG_FORMAT = "%(asctime)s %(levelname)s %(message)s"


def setup_run_dir(run_dir, resuming=False):
    """Set up the run directory, overriding config paths.

    Returns the run_dir Path. Prompts for confirmation if the directory
    already has data and we're not resuming.
    """
    run_dir = Path(run_dir)

    # Check if directory has existing data from a previous run
    has_data = (
        (run_dir / "results.json").exists()
        or (run_dir / "patches").exists() and any((run_dir / "patches").glob("task_*.patch"))
    )

    if has_data and not resuming:
        print(f"Run directory '{run_dir}' already contains data.")
        answer = input("Overwrite? [y/N] ").strip().lower()
        if answer != "y":
            print("Aborted.")
            sys.exit(0)
        # Clean previous data
        if (run_dir / "results.json").exists():
            (run_dir / "results.json").unlink()
        patches_dir = run_dir / "patches"
        if patches_dir.exists():
            for p in patches_dir.glob("task_*.patch"):
                p.unlink()

    # Create directories
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "patches").mkdir(exist_ok=True)

    # Override config paths so all modules use this run directory
    config.RESULTS_JSON = run_dir / "results.json"
    config.PATCHES_DIR = run_dir / "patches"
    config.EVAL_RESULTS_DIR = run_dir

    return run_dir


def setup_logging():
    config.EVAL_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = config.EVAL_RESULTS_DIR / f"run_{timestamp}.log"

    logging.basicConfig(
        level=logging.INFO,
        format=LOG_FORMAT,
        handlers=[
            logging.StreamHandler(sys.stdout),
            logging.FileHandler(log_file),
        ],
    )
    logging.captureWarnings(True)
    logging.info(f"Log file: {log_file}")
    return log_file


def run_submit(task_ids, api_url):
    logging.info(f"Submitting {len(task_ids) if task_ids else 'all'} tasks to {api_url}")
    from connector.submit import load_tasks, submit_task, save_results

    api_key = os.environ.get(config.ALEPH_API_KEY_ENV)
    tasks = load_tasks()
    ids = task_ids or sorted(tasks.keys())

    results = []
    if config.RESULTS_JSON.exists():
        with open(config.RESULTS_JSON) as f:
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
            save_results(results, config.RESULTS_JSON)
            submitted += 1
        else:
            logging.error(f"[{tid:>3}] submission failed")

    logging.info(f"Submitted {submitted}/{len(ids)} tasks")
    return submitted


def run_collect(task_ids):
    """Poll until all tasks complete, download patches."""
    logging.info("Collecting results and downloading patches")
    from connector.collect import get_base_url, fetch_status, download_patch

    api_key = os.environ.get(config.ALEPH_API_KEY_ENV)

    with open(config.RESULTS_JSON) as f:
        results = json.load(f)

    # Deduplicate: keep latest entry per task_id
    by_id = {}
    for r in results:
        by_id[r["task_id"]] = r

    if task_ids:
        check_ids = set(task_ids)
    else:
        check_ids = set(by_id.keys())

    # Wait for newly submitted tasks to register
    time.sleep(10)

    start = time.time()
    downloaded = set()

    while True:
        completed = running = failed = 0

        for tid in sorted(check_ids):
            entry = by_id.get(tid)
            if not entry or not entry.get("request_id"):
                if tid not in downloaded:
                    logging.warning(f"[{tid:>3}] no submission record, skipping")
                    downloaded.add(tid)
                    failed += 1
                continue

            if tid in downloaded:
                completed += 1
                continue

            base_url = get_base_url(entry)
            data = fetch_status(entry["request_id"], base_url, api_key)
            if not data:
                running += 1
                continue

            status = data.get("status", "?")
            entry["status"] = status
            if data.get("pr_url"):
                entry["pr_url"] = data["pr_url"]

            if status == "completed":
                patch = download_patch(entry["request_id"], base_url, api_key, tid)
                if patch:
                    logging.info(f"[{tid:>3}] completed, patch: {patch.name}")
                    downloaded.add(tid)
                    completed += 1
                else:
                    logging.warning(f"[{tid:>3}] completed but patch download failed")
                    running += 1
            elif status == "failed":
                failed += 1
                downloaded.add(tid)
                logging.warning(f"[{tid:>3}] failed at {data.get('stage', '?')}")
            else:
                running += 1

        with open(config.RESULTS_JSON, "w") as f:
            json.dump(list(by_id.values()), f, indent=2)

        logging.info(f"Status: completed={completed} running={running} failed={failed} (downloaded={len(downloaded)}/{len(check_ids)})")

        if len(downloaded) >= len(check_ids):
            break
        if time.time() - start > config.MAX_POLL_TIME:
            logging.warning(f"Timeout after {config.MAX_POLL_TIME}s, {running} still running")
            break

        time.sleep(config.POLL_INTERVAL)

    logging.info(f"Collection done: {len(downloaded)} tasks resolved, {len(list(config.PATCHES_DIR.glob('task_*.patch')))} patches on disk")


def run_evaluate(task_ids, skip_extraction=False):
    """Run evaluation, return dict of {thm_name: passed}."""
    logging.info("Evaluating patches")
    from connector.evaluate import get_task_ids_with_patches, write_eval_config, find_eval_repo
    import subprocess

    eval_repo = find_eval_repo()
    if not eval_repo:
        logging.error("VeriSoftBench evaluation repo not found")
        return {}

    ids = task_ids or get_task_ids_with_patches(config.PATCHES_DIR)
    if not ids:
        logging.info("No patches to evaluate")
        return {}

    config.EVAL_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    extractions_dir = config.EVAL_RESULTS_DIR / "extractions"
    config_path = config.EVAL_RESULTS_DIR / "eval_config.yaml"
    write_eval_config(config.PATCHES_DIR, config_path,
                      extractions_dir=extractions_dir,
                      skip_extraction=skip_extraction)

    task_ids_str = ",".join(str(t) for t in ids)
    logging.info(f"Evaluating {len(ids)} tasks")

    cmd = [
        sys.executable, str(eval_repo / "evaluate.py"),
        "--config", str(config_path),
        "--task-ids", task_ids_str,
        "--save-debug-lean",
        "--refresh-cache",
    ]
    proc = subprocess.run(cmd, cwd=str(eval_repo), stderr=subprocess.STDOUT)
    logging.info(f"Evaluation subprocess exited with code {proc.returncode}")

    # Parse results from the latest aleph-prover-eval run directory
    RUN_PREFIX = "aleph-prover-eval_"
    results = {}
    results_dir = eval_repo / "results" / "data"
    if results_dir.exists():
        run_dirs = sorted(
            [d for d in results_dir.iterdir() if d.is_dir() and d.name.startswith(RUN_PREFIX)],
            key=lambda p: p.name,
        )
        if run_dirs:
            latest = run_dirs[-1]
            logging.info(f"Reading results from {latest.name}")
            details_dir = latest / "details"
            if details_dir.exists():
                for f in details_dir.glob("*.json"):
                    try:
                        d = json.loads(f.read_text())
                        thm = d.get("thm_name", "")
                        success = d.get("success", False)
                        results[thm] = success

                        proofs = d.get("generated_proofs", [])
                        n_samples = len(proofs)
                        if success:
                            for i, p in enumerate(proofs):
                                if p.get("err_msg") is None:
                                    if i > 0:
                                        logging.info(f"  {thm}: PASS (sample {i}/{n_samples}, earlier failed)")
                                    else:
                                        logging.info(f"  {thm}: PASS ({n_samples} samples)")
                                    break
                        else:
                            err = proofs[0].get("err_msg", "")[:80] if proofs else "no proof"
                            logging.info(f"  {thm}: FAIL ({n_samples} samples) — {err}")
                    except Exception as e:
                        logging.warning(f"  Failed to parse {f.name}: {e}")
        else:
            logging.error(f"No run directories matching '{RUN_PREFIX}*' found in {results_dir}")
    else:
        logging.error(f"Results directory not found: {results_dir}")

    passed = sum(1 for v in results.values() if v)
    total = len(results)
    logging.info(f"Evaluation: {passed}/{total} passed")
    return results


def get_failed_task_ids(eval_results):
    """Find task IDs that failed evaluation."""
    with open(config.TASKS_JSON) as f:
        tasks = json.load(f)

    thm_to_tid = {}
    for t in tasks:
        tid = t["id"]
        name = config.THEOREM_NAME_OVERRIDES.get(tid, t["theorem_name"])
        thm_to_tid[name] = tid
        thm_to_tid[t["theorem_name"]] = tid

    failed = []
    for thm_name, passed in eval_results.items():
        if not passed:
            tid = thm_to_tid.get(thm_name)
            if tid:
                failed.append(tid)
    return failed


def main():
    p = argparse.ArgumentParser(description="Run full VeriSoftBench evaluation pipeline")
    p.add_argument("--run-dir", type=Path, default=Path("runs/default"),
                    help="Directory for all run artifacts: results.json, patches/, logs (default: runs/default)")
    p.add_argument("--task-ids", nargs="*", type=int, help="Task IDs (default: all 100)")
    p.add_argument("--api-url", default=config.ALEPH_API_URL)
    p.add_argument("--skip-submit", action="store_true")
    p.add_argument("--skip-collect", action="store_true")
    p.add_argument("--skip-extraction", action="store_true",
                    help="Use saved GPT extractions from a previous run instead of calling GPT again")
    p.add_argument("--no-retries", action="store_true", help="Disable proof request retries")
    args = p.parse_args()

    # Set up run directory and override config paths
    resuming = args.skip_submit or args.skip_collect or args.skip_extraction
    run_dir = setup_run_dir(args.run_dir, resuming=resuming)

    log_file = setup_logging()
    logging.info(f"Pipeline started. API: {args.api_url}")
    logging.info(f"Run directory: {run_dir.resolve()}")
    logging.info(f"Retries: {'disabled' if args.no_retries else f'up to {config.MAX_PROOF_RETRIES}'}")

    task_ids = args.task_ids
    max_retries = 0 if args.no_retries else config.MAX_PROOF_RETRIES

    # Accumulate results across retry attempts
    all_results = {}

    for attempt in range(1 + max_retries):
        if attempt > 0:
            logging.info(f"\n{'='*60}")
            logging.info(f"RETRY {attempt}/{max_retries}: resubmitting {len(task_ids)} failed tasks")
            logging.info(f"{'='*60}")
            for tid in task_ids:
                patch = config.PATCHES_DIR / f"task_{tid:03d}.patch"
                if patch.exists():
                    patch.unlink()
            args.skip_submit = False
            args.skip_collect = False

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
        eval_results = run_evaluate(task_ids, skip_extraction=args.skip_extraction)

        if not eval_results:
            logging.warning("No evaluation results")
            break

        all_results.update(eval_results)

        failed_ids = get_failed_task_ids(eval_results)

        if not failed_ids or attempt >= max_retries:
            break

        logging.info(f"{len(failed_ids)} tasks failed, will retry: {failed_ids}")
        task_ids = failed_ids

    passed = sum(1 for v in all_results.values() if v)
    total = len(all_results)
    logging.info(f"\n{'='*60}")
    logging.info(f"FINAL RESULT: {passed}/{total} passed")
    logging.info(f"Run directory: {run_dir.resolve()}")
    logging.info(f"Log: {log_file}")
    logging.info(f"{'='*60}")


if __name__ == "__main__":
    main()

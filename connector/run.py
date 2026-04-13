#!/usr/bin/env python3
"""Main orchestrator: submit → collect → evaluate.

Usage:
    python -m connector.run
    python -m connector.run --skip-submit
    python -m connector.run --skip-submit --skip-collect
    python -m connector.run --task-ids 4 29 122
"""

import argparse
import sys

from connector.config import ALEPH_API_URL


def main():
    p = argparse.ArgumentParser(description="Run full VeriSoftBench evaluation pipeline")
    p.add_argument("--task-ids", nargs="*", type=int, help="Task IDs (default: all 100)")
    p.add_argument("--api-url", default=ALEPH_API_URL)
    p.add_argument("--skip-submit", action="store_true", help="Skip submission (tasks already submitted)")
    p.add_argument("--skip-collect", action="store_true", help="Skip collection (patches already downloaded)")
    args = p.parse_args()

    task_args = ["--task-ids"] + [str(t) for t in args.task_ids] if args.task_ids else []

    # Step 1: Submit
    if not args.skip_submit:
        print("=" * 60)
        print("STEP 1: Submitting tasks")
        print("=" * 60)
        from connector.submit import main as submit_main
        sys.argv = ["submit"] + task_args + ["--api-url", args.api_url]
        submit_main()

    # Step 2: Collect
    if not args.skip_collect:
        print("\n" + "=" * 60)
        print("STEP 2: Collecting results and patches")
        print("=" * 60)
        from connector.collect import main as collect_main
        sys.argv = ["collect", "--wait"] + task_args
        collect_main()

    # Step 3: Evaluate
    print("\n" + "=" * 60)
    print("STEP 3: Evaluating patches")
    print("=" * 60)
    from connector.evaluate import main as evaluate_main
    sys.argv = ["evaluate"] + task_args
    evaluate_main()


if __name__ == "__main__":
    main()

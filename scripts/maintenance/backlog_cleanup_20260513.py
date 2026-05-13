#!/usr/bin/env python3
"""Classify the open PR backlog for HO-31.

The script is intentionally conservative: it does not close or reopen PRs.
It prints the cleanup buckets from issue #3682 so a maintainer can review
the live state before taking action.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass
from typing import Any


PR_FIELDS = (
    "number,title,headRefName,createdAt,updatedAt,mergeable,"
    "statusCheckRollup,closingIssuesReferences"
)


@dataclass(frozen=True)
class BucketedPr:
    number: int
    title: str
    bucket: str
    reason: str


def run_gh_pr_list() -> list[dict[str, Any]]:
    cmd = [
        "gh",
        "pr",
        "list",
        "--state",
        "open",
        "--limit",
        "200",
        "--json",
        PR_FIELDS,
    ]
    proc = subprocess.run(cmd, check=True, text=True, capture_output=True)
    return json.loads(proc.stdout)


def load_prs(path: str | None) -> list[dict[str, Any]]:
    if path is None:
        return run_gh_pr_list()
    with open(path, encoding="utf-8") as handle:
        return json.load(handle)


def check_name(check: dict[str, Any]) -> str:
    for key in ("name", "workflowName", "context"):
        value = check.get(key)
        if value:
            return str(value)
    return "unknown"


def check_state(check: dict[str, Any]) -> str:
    for key in ("conclusion", "status", "state"):
        value = check.get(key)
        if value:
            return str(value).upper()
    return "PENDING"


def classify(pr: dict[str, Any]) -> BucketedPr:
    checks = pr.get("statusCheckRollup") or []
    states = [check_state(check) for check in checks]
    issues = pr.get("closingIssuesReferences") or []

    if checks and all(state == "SUCCESS" for state in states):
        return BucketedPr(
            number=pr["number"],
            title=pr["title"],
            bucket="already green",
            reason="all reported checks are SUCCESS",
        )

    failed = [
        check_name(check)
        for check in checks
        if check_state(check) in {"FAILURE", "ERROR", "TIMED_OUT", "ACTION_REQUIRED"}
    ]
    if failed:
        return BucketedPr(
            number=pr["number"],
            title=pr["title"],
            bucket="real and active",
            reason="failing checks: " + ", ".join(failed),
        )

    if not issues:
        return BucketedPr(
            number=pr["number"],
            title=pr["title"],
            bucket="real and active",
            reason="no closing issue; requires human review before cleanup",
        )

    pending = [check_name(check) for check in checks if check_state(check) != "SUCCESS"]
    reason = "pending checks: " + ", ".join(pending) if pending else "no check data"
    return BucketedPr(
        number=pr["number"],
        title=pr["title"],
        bucket="real and active",
        reason=reason,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--json-file",
        help="Use a saved gh pr list JSON payload instead of querying GitHub.",
    )
    args = parser.parse_args()

    prs = load_prs(args.json_file)
    buckets: dict[str, list[BucketedPr]] = defaultdict(list)
    for pr in prs:
        item = classify(pr)
        buckets[item.bucket].append(item)

    print(f"Open PR baseline: {len(prs)}")
    for bucket in ("already green", "stale / superseded", "real and active"):
        items = buckets.get(bucket, [])
        print(f"\n{bucket}: {len(items)}")
        for item in items:
            print(f"- #{item.number} {item.title} -- {item.reason}")

    if len(prs) <= 25:
        print("\nStop condition met: open PR count is at or below 25.")
    else:
        print("\nStop condition not met: review buckets and apply cleanup actions.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

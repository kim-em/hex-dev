#!/usr/bin/env python3
"""Independently recheck every complete native campaign output with Python/PARI."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

from ecpp_pari import check_step, pari_group_check, pari_isprime


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("campaign", type=Path)
    args = parser.parse_args()
    campaign = json.loads(args.campaign.read_text())
    checked = []
    pattern = re.compile(r"Hex\.ECPP\.Cert\.step\s+" + r"(\d+)\s+" * 6 + r"\[([\d,\s]*)\]")
    steps = []
    subjects = set()
    for case in campaign["cases"]:
        native = case["native"]
        if native["verdict"] != "success":
            continue
        assert native["checked"] and native["converted"], case["id"]
        subjects.add(native["subject"])
        rows = json.loads(native["rows"])
        matches = list(pattern.finditer(native["expanded"]))
        assert len(matches) == len(rows) == native["steps"], case["id"]
        for row, match in zip(rows, matches, strict=True):
            n, a, b, x, y, inverse = map(int, match.groups()[:6])
            assert n == row[0] and a == row[3] and [x, y] == row[4], case["id"]
            q = n + 1 - row[1]
            assert row[2] == 1
            witnesses = [int(v) for v in match[7].split(",") if v.strip()]
            step = dict(kind="step", n=n, a=a, b=b, x=x, y=y, d=inverse,
                        q=q, witnesses=witnesses, accepted=True)
            assert check_step(step), case["id"]
            subjects.update((n, q))
            steps.append(step)
        checked.append(case["id"])
    for subject in sorted(subjects):
        assert pari_isprime(subject), subject
    pari_group_check(steps)
    print(json.dumps(dict(native_successes=len(checked), steps=len(steps),
                          independently_prime_subjects=len(subjects), cases=checked)))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact Z3 checks of all permitted RootSet policies and multiplicities."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.real_closure_isolation import multiply, parse_record, verify_assembly
from scripts.oracle.sign_det_common import require
from scripts.oracle.sign_det_z3 import check_version

POLICIES = ["Hex.RealClosure.Isolation.Policy." + p for p in ["standard", "bounded", "whole"]]
CASES = ["zero", "constant", "pure power", "repeated factors", "root-free factor",
         "simple zero", "cut point", "infinitesimal repeated pair", "inverse infinitesimal"]
INDICES = [10, 11, 12, 13, 14, 15, 18]


def infinitesimal_pair(rcf):
    epsilon = rcf.levels[0]
    p = [2 * rcf.one]
    for a in [epsilon, epsilon, 2*epsilon, 2*epsilon, 2*epsilon]:
        p = multiply(rcf, p, [-a, rcf.one])
    return p


def verify(rows):
    check_version()
    require(len(rows) == len(POLICIES)*len(CASES), "missing or extra policy fixture")
    for row, (policy, name) in zip(rows, [(p, c) for p in POLICIES for c in CASES]):
        require(isinstance(row, dict) and set(row) == {"policy", "result"} and
                row["policy"] == policy and isinstance(row["result"], dict) and
                row["result"].get("case") == name, "wrong policy or case binding")
        result = row["result"]
        if name in CASES[:7]:
            verify_assembly(result, INDICES[CASES.index(name)],
                            require_cut_point=policy == POLICIES[0])
        else:
            expected = infinitesimal_pair if name == CASES[7] else \
                lambda rcf: [(-rcf.one).__div__(rcf.levels[0]), rcf.one]
            verify_assembly(result, None, depth=1, expected=expected, require_cut_point=False)


def main():
    rows = [parse_record(line) for line in sys.stdin if line.strip()]
    verify(rows)
    print(f"verified {len(rows)} policy RootSets with exact Z3 RCF")


if __name__ == "__main__":
    main()

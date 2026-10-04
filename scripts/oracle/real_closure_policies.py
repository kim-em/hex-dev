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
         "simple zero", "cut point", "infinitesimal repeated pair", "inverse infinitesimal",
         "infinitesimal squarefree pair", "infinitesimal same-label pair"]
INDICES = [10, 11, 12, 13, 14, 15, 18]


def infinitesimal_pair(rcf):
    epsilon = rcf.levels[0]
    p = [2 * rcf.one]
    for a in [epsilon, epsilon, 2*epsilon, 2*epsilon, 2*epsilon]:
        p = multiply(rcf, p, [-a, rcf.one])
    return p


def close_pair(rcf, repeated=False):
    epsilon = rcf.levels[0]
    pair = multiply(rcf, [-epsilon, rcf.one], [-2*epsilon, rcf.one])
    return [3*c for c in multiply(rcf, pair, pair)] if repeated else pair


def verify_shape(result, policy, name):
    from scripts.oracle.sign_det_z3 import RCF
    if result["output"].get("kind") != "finite":
        return
    rcf = RCF({"id": 10377, "levels": ["epsilon1"],
               "order": "each-new-level-smaller-than-positive-base-elements"})
    depth = 0 if name in CASES[:7] else 1
    bounded_cells = {}
    for entry in result["output"]["entries"]:
        root = entry["root"]
        if root["kind"] == "point":
            if policy != POLICIES[0]:
                require(rcf.coeff(root["value"], depth) == 0,
                        "nonbisection policy emitted nonzero point")
        elif policy == POLICIES[2]:
            require(root["lower"] == [0] and root["upper"] == [2],
                    "whole policy retained finite bounds")
        if policy == POLICIES[1] and root["kind"] == "selected" and name != CASES[8]:
            require(root["lower"][0] == 1 and root["upper"][0] == 1,
                    "bounded policy lost a finite bound")
            require(rcf.coeff(root["lower"][1], depth) == -rcf.coeff(root["upper"][1], depth),
                    "bounded policy subdivided its symmetric initial cell")
            key = repr(root["head"])
            cell = (root["lower"], root["upper"])
            require(key not in bounded_cells or bounded_cells[key] == cell,
                    "bounded policy subdivided one squarefree factor")
            bounded_cells[key] = cell
        if name in CASES[9:]:
            require(root["kind"] == "selected" and root["indices"] == [1, 2],
                    "close squarefree pair did not exercise derivative-sign selection")


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
            expected = {
                CASES[7]: infinitesimal_pair,
                CASES[8]: lambda rcf: [(-rcf.one).__div__(rcf.levels[0]), rcf.one],
                CASES[9]: close_pair,
                CASES[10]: lambda rcf: close_pair(rcf, repeated=True),
            }[name]
            verify_assembly(result, None, depth=1, expected=expected, require_cut_point=False)
        verify_shape(result, policy, name)


def main():
    rows = [parse_record(line) for line in sys.stdin if line.strip()]
    verify(rows)
    print(f"verified {len(rows)} policy RootSets with exact Z3 RCF")


if __name__ == "__main__":
    main()

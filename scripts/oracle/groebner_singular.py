#!/usr/bin/env python3
"""Independent reduced-basis oracle using Singular when available.

Orders lp, Dp and dp match lex, grlex and grevlex with the written variable
precedence. The ring is an ordinary polynomial ring, including characteristic
two. SymPy separately checks the canonical basis ordering. This oracle compares
every coefficient and exponent in each reduced basis, ignoring only the order
of basis polynomials and the order of terms in Singular's printed expressions.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.common import write_failure


def expression(terms):
    return "+".join(str(c) + "".join(f"*x{i}^{e}" for i, e in enumerate(powers) if e)
                    for powers, c in terms) or "0"


def polynomial(text, variables, p):
    """Parse expanded Singular output with integer coefficients; never eval it."""
    text = re.sub(r"\s+", "", text)
    if not re.fullmatch(r"[A-Za-z0-9_+*^-]+", text):
        raise ValueError(f"unexpected polynomial syntax: {text}")
    coefficients = {}
    for term in re.findall(r"[+-]?[^+-]+", text):
        coefficient = -1 if term.startswith("-") else 1
        term = term.lstrip("+-")
        powers = [0] * variables
        # Singular omits '*' between a scalar and a variable (e.g. 3x0).
        term = re.sub(r"(\d)(x)", r"\1*\2", term)
        # Singular omits '^' for exponents only with single-letter variables;
        # our multi-character x0 names force explicit powers.
        for factor in term.split("*"):
            if factor.isdigit():
                coefficient *= int(factor)
            else:
                match = re.fullmatch(r"x(\d+)(?:\^(\d+))?", factor)
                if not match or int(match[1]) >= variables:
                    raise ValueError(f"unexpected factor: {factor}")
                powers[int(match[1])] += int(match[2] or 1)
        key = tuple(powers)
        coefficients[key] = (coefficients.get(key, 0) + coefficient) % p
    return sorted((powers, c) for powers, c in coefficients.items() if c)


def canonical(basis):
    return sorted(sorted((tuple(powers), c) for powers, c in f) for f in basis if f)


def run(records, binary):
    commands = ["option(redSB);", "ring host=0,t,dp;", "int k;"]
    for i, record in enumerate(records):
        value = record["value"]
        n = value["variables"]
        if n == 0:
            continue
        names = ",".join(f"x{k}" for k in range(n))
        order = {"lex": "lp", "grlex": "Dp", "grevlex": "dp"}[value["order"]]
        inputs = ",".join(expression(f) for f in value["generators"]) or "0"
        commands += [f"ring r={value['p']},({names}),{order};", f"ideal I={inputs};",
                     "ideal B=interred(std(I));", f'print("CASE {i}");',
                     'for(k=1;k<=ncols(B);k++){if(B[k]!=0){print("POLY "+string(B[k]/leadcoef(B[k])));}}',
                     'print("END");', "setring host;", "kill r;"]
    commands.append("quit;")
    result = subprocess.run([binary, "-q"], input="\n".join(commands) + "\n", text=True,
                            capture_output=True, timeout=120, check=True)
    if result.stderr:
        raise ValueError(f"Singular diagnostics: {result.stderr}")
    observed, current = {}, None
    for line in result.stdout.splitlines():
        if line.startswith("CASE "):
            current = int(line[5:])
            if current in observed:
                raise ValueError("duplicate Singular case")
            observed[current] = []
        elif line.startswith("POLY ") and current is not None:
            value = records[current]["value"]
            observed[current].append(polynomial(line[5:], value["variables"], value["p"]))
        elif line == "END" and current is not None:
            current = None
        elif line.strip():
            raise ValueError(f"unexpected Singular output: {line}")
    if current is not None:
        raise ValueError("truncated Singular output")
    for i, record in enumerate(records):
        value = record["value"]
        if value["variables"] == 0:
            expected = [[((), 1)]] if any(sum(c for _, c in f) % value['p']
                                         for f in value["generators"]) else []
        else:
            if i not in observed:
                raise ValueError(f"missing Singular case {record['case']}")
            expected = sorted(observed[i])
        if canonical(value["basis"]) != expected:
            path = write_failure(Path("conformance-failures"), library="HexGroebner", profile="oracle",
                                 seed=0, case_id=record["case"], kind="f4", input_record=record,
                                 lean_output=value["basis"], oracle_output=expected,
                                 oracle_name="Singular", oracle_version="see executable --version",
                                 diff="different reduced basis")
            raise ValueError(f"{record['case']}: different reduced basis; replay: {path}")
    return len(records)


def check_available(records, required=False):
    binary = shutil.which("Singular")
    if binary is None:
        if required or os.environ.get("HEX_REQUIRE_ORACLES") == "1":
            raise RuntimeError("Singular required but unavailable")
        print("SKIP: Singular unavailable (if_available oracle)")
        return
    print(f"OK: {run(records, binary)} reduced bases match Singular")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path)
    parser.add_argument("--require-oracles", action="store_true")
    args = parser.parse_args()
    records = [json.loads(line) for line in
               (args.check.read_text() if args.check else sys.stdin.read()).splitlines()]
    if len(records) != 567:
        raise ValueError(f"incomplete F4 corpus: {len(records)}")
    check_available(records, args.require_oracles)


if __name__ == "__main__":
    main()

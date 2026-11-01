#!/usr/bin/env python3
"""Check the standalone candidate driver against the independently checked corpus.

No timing threshold or scientific performance claim belongs in this check.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def check(binary: Path) -> None:
    with tempfile.TemporaryDirectory(prefix="groebner-driver-") as directory:
        path = Path(directory) / "input.json"

        def invoke(payload, options=(), code=0, kind="unchecked_candidate"):
            path.write_text(json.dumps(payload) + "\n")
            result = subprocess.run([str(binary), *options, str(path)], capture_output=True,
                                    text=True, timeout=30)
            assert result.returncode == code, (result.returncode, result.stdout, result.stderr)
            value = json.loads(result.stdout)
            assert value["kind"] == kind, value
            assert "basis" in value if code == 0 else "basis" not in value, value
            return value

        records = [json.loads(line) for line in
                   (ROOT / "conformance-fixtures/HexGroebner/f4.jsonl").read_text().splitlines()]
        assert len(records) == 567
        for record in records:
            expected = record["value"]
            value = invoke({key: expected[key] for key in ["p", "variables", "order", "generators"]})
            assert value["basis"] == expected["basis"], record["case"]
            assert (value["p"], value["variables"], value["order"], value["randomState"]) == (
                expected["p"], expected["variables"], expected["order"], 0)
            for key in ["work", "pairs", "rounds", "largestBatch", "peakMatrixRows", "peakMatrixEntries"]:
                assert value["statistics"][key] == expected[key], (record["case"], key)

        unit = {"p": 7, "variables": 1, "order": "grevlex", "generators": [[[[0], 2]]]}
        assert invoke(unit)["basis"] == [[[[0], 1]]]
        assert invoke({**unit, "generators": []})["basis"] == []
        assert invoke({**unit, "generators": [[]]})["basis"] == []
        ordinary_two = {**unit, "p": 2, "generators": [[[[2], 1], [[1], 1]]]}
        assert invoke(ordinary_two)["basis"] == ordinary_two["generators"]
        for order in ["lex", "grlex", "grevlex"]:
            assert invoke({**unit, "order": order})["order"] == order
        for modulus in [0, 1, 4, 2**31, 2**200]:
            invoke({**unit, "p": modulus}, code=2, kind="invalid_input")
        for malformed in [{}, {**unit, "order": "unknown"}, {**unit, "p": -7},
                          {**unit, "generators": [[[[0], 2**64]]]},
                          {**unit, "generators": [[[[0], 7]]]},
                          {**unit, "generators": [[[[0, 0], 1]]]},
                          {**unit, "generators": [[[[0], -1]]]}]:
            invoke(malformed, code=2, kind="invalid_input")
        invoke({**unit, "generators": [[[[2**32], 1]]]}, code=4, kind="representation")
        for option in ["--work", "--packed-bytes", "--monomials", "--matrix-entries", "--matrix-rows"]:
            invoke(unit, [option, "0"], code=3, kind="exhausted")
        pair_input = {"p": 7, "variables": 2, "order": "grevlex", "generators": [
            [[[2, 0], 1], [[0, 1], 6]], [[[1, 1], 1], [[0, 0], 6]]]}
        for option in ["--pairs", "--rounds"]:
            invoke(pair_input, [option, "0"], code=3, kind="exhausted")
        invoke({**unit, "variables": 10001, "generators": []}, code=3, kind="exhausted")
        for options in [["--unknown", "1"], ["--work", "bad"], ["--work", "-1"]]:
            invoke(unit, options, code=2, kind="invalid_input")
        result = subprocess.run([str(binary), str(path.with_name("missing.json"))],
                                capture_output=True, text=True, timeout=30)
        assert result.returncode == 2 and json.loads(result.stdout)["kind"] == "invalid_input"
        path.write_text("{malformed json")
        result = subprocess.run([str(binary), str(path)], capture_output=True, text=True, timeout=30)
        assert result.returncode == 2 and json.loads(result.stdout)["kind"] == "invalid_input"
        assert invoke(unit, ["--batch-size", "1"])["batchSize"] == 1
    print("candidate driver: 567 complete corpus outputs/counters and input/resource boundaries passed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, action="append")
    args = parser.parse_args()
    binaries = args.binary or [ROOT / ".lake/build/bin/hexgroebner_compute",
                               ROOT / ".lake/build/bin/hexgroebner_compute_full"]
    for binary in binaries:
        print(f"Checking {binary.name}", flush=True)
        check(binary.resolve())


if __name__ == "__main__":
    main()

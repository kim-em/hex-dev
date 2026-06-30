#!/usr/bin/env python3
"""Validate the Lean lattice-basis generators against fplll's `latticegen`.

Entry-for-entry equality is impossible (fplll draws from GMP's generator, the
Lean ports from a committed POSIX LCG), so this checks the *structural
envelope* both must satisfy. The deterministic diagonal bit-length profile is
compared per generator: fplll uses a float `(int)pow(2d-i, 1.2)`, the Lean port
an exact integer `floor((2d-i)^(6/5))`; the two agree to within 1 bit at
exact-power boundaries (e.g. 32^1.2 = 64), and that <=1-bit tolerance is an
explicit asserted invariant. Writes golden metadata for provenance.

Covers the Ajtai-style family (fplll `gen_trg`, `latticegen t`).

The Lean cross-check reads pre-emitted matrices from
`scripts/dev/.lean-ajtai-matrices.jsonl` (decoupled from `lake`). Regenerate:
  lake env lean --run scripts/dev/emit_latticegen_family.lean ajtai 6 8 10 12 16 20 \
    > scripts/dev/.lean-ajtai-matrices.jsonl
If absent, only the latticegen reference envelope is validated.

Usage:
  python3 scripts/dev/validate_latticegen.py            # validate + write golden
  python3 scripts/dev/validate_latticegen.py --check     # validate only (CI)
"""
from __future__ import annotations
import json, os, re, subprocess, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
CACHE = os.environ.get("HEX_ORACLE_CACHE", str(ROOT / ".cache/oracles"))
LATTICEGEN = pathlib.Path(CACHE) / "fplll-ffi/src/vendor/fplll/fplll/latticegen"
LEAN_MATS = ROOT / "scripts/dev/.lean-ajtai-matrices.jsonl"
ALPHA = 1.2
SEED = 1
DIMS = [6, 8, 10, 12, 16, 20]
GOLDEN = ROOT / "scripts/dev/latticegen-golden.json"

def _iroot(k: int, n: int) -> int:
    r = int(round(n ** (1.0 / k))) if n > 0 else 0
    while r > 0 and r ** k > n:
        r -= 1
    while (r + 1) ** k <= n:
        r += 1
    return r

def bits_float(d: int) -> list[int]:
    return [int((2 * d - i) ** ALPHA) for i in range(d)]          # fplll (int)pow

def bits_exact(d: int) -> list[int]:
    return [_iroot(5, (2 * d - i) ** 6) for i in range(d)]        # Lean ajtaiBits

def parse_matrix(text: str) -> list[list[int]]:
    rows = []
    for line in text.splitlines():
        nums = re.findall(r"-?\d+", line)
        if nums:
            rows.append([int(x) for x in nums])
    return rows

def check_envelope(name: str, d: int, M: list[list[int]], prof: list[int]) -> list[int]:
    assert len(M) == d and all(len(r) == d for r in M), f"{name} d={d}: not {d}x{d}"
    diag_bitlens = []
    for i in range(d):
        Di = abs(M[i][i])
        assert Di >= 1, f"{name} d={d}: zero diagonal at {i}"
        bl = Di.bit_length()
        diag_bitlens.append(bl)
        assert bl <= prof[i], f"{name} d={d}: diag[{i}] bitlen {bl} > profile {prof[i]}"
        for j in range(i + 1, d):
            assert M[i][j] == 0, f"{name} d={d}: upper entry [{i}][{j}] != 0"
        for j in range(0, i):
            assert 2 * abs(M[i][j]) < abs(M[j][j]), \
                f"{name} d={d}: |off[{i}][{j}]| >= diag[{j}]/2"
    return diag_bitlens

def run_latticegen(d: int) -> list[list[int]]:
    out = subprocess.run([str(LATTICEGEN), "-randseed", str(SEED), "t", str(d), str(ALPHA)],
                         capture_output=True, text=True, check=True).stdout
    return parse_matrix(out)

def lean_matrices() -> dict[int, list[list[int]]]:
    if not LEAN_MATS.exists():
        return {}
    res = {}
    for line in LEAN_MATS.read_text().splitlines():
        line = line.strip()
        if line.startswith('{"family"'):
            obj = json.loads(line)
            res[obj["d"]] = obj["basis"]
    return res

def main() -> int:
    check_only = "--check" in sys.argv
    if not LATTICEGEN.exists():
        print(f"latticegen not found at {LATTICEGEN}", file=sys.stderr)
        return 2
    lean = lean_matrices()
    if not lean:
        print("note: no Lean matrices file; validating latticegen reference only.")
    golden = {"provenance": {"tool": "fplll latticegen t", "alpha": ALPHA, "seed": SEED,
                             "note": "structural envelope only; entries differ (GMP vs LCG RNG); "
                                     "fplll float bits vs Lean exact bits agree to within 1 bit"},
              "ajtai": {}}
    for d in DIMS:
        pf, pe = bits_float(d), bits_exact(d)
        # the two profiles must agree to within 1 bit (the documented tolerance)
        for i in range(d):
            assert abs(pf[i] - pe[i]) <= 1, f"d={d}: bits profiles differ by >1 at {i}: {pf[i]} vs {pe[i]}"
        ref_bl = check_envelope("latticegen", d, run_latticegen(d), pf)
        entry = {"bits_float": pf, "bits_exact": pe, "latticegen_diag_bitlens": ref_bl}
        tag = "latticegen"
        if d in lean:
            entry["lean_diag_bitlens"] = check_envelope("lean", d, lean[d], pe)
            entry["lean_row0"] = lean[d][0]
            tag = "lean+latticegen"
        golden["ajtai"][str(d)] = entry
        print(f"d={d:3d}  OK ({tag})  bits_float={pf}")
    if not check_only:
        GOLDEN.write_text(json.dumps(golden, indent=2) + "\n")
        print(f"wrote golden metadata -> {GOLDEN.relative_to(ROOT)}")
    print("validate_latticegen: structural envelope holds (<=1-bit profile tolerance).")
    return 0

if __name__ == "__main__":
    sys.exit(main())

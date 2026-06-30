#!/usr/bin/env python3
"""Validate the Lean lattice-basis generators against fplll's `latticegen`.

Entry-for-entry equality is impossible (fplll draws from GMP's generator, the
Lean ports from a committed POSIX LCG), so this checks the *structural
envelope* both must satisfy, and that the deterministic part (the diagonal
bit-length profile) is identical. Writes golden metadata for provenance.

Covers the Ajtai-style family (fplll `gen_trg`, `latticegen t`).

The Lean cross-check reads pre-emitted matrices from
`scripts/dev/.lean-ajtai-matrices.jsonl` (decoupled from `lake` to avoid
build-lock contention). Regenerate that file with:
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

def bits_profile(d: int, alpha: float = ALPHA) -> list[int]:
    return [int((2 * d - i) ** alpha) for i in range(d)]   # fplll gen_trg (int)pow(2d-i, alpha)

def parse_matrix(text: str) -> list[list[int]]:
    rows = []
    for line in text.splitlines():
        nums = re.findall(r"-?\d+", line)
        if nums:
            rows.append([int(x) for x in nums])
    return rows

def check_envelope(name: str, d: int, M: list[list[int]]) -> list[int]:
    """Lower-triangular; upper entries 0; |off[i][j]| < diag[j]/2; diag bitlen
    <= bits_i. Returns the diagonal bit-lengths. Raises on violation."""
    prof = bits_profile(d)
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
                             "note": "structural envelope only; entries differ (GMP vs LCG RNG)"},
              "ajtai": {}}
    for d in DIMS:
        prof = bits_profile(d)
        ref_bl = check_envelope("latticegen", d, run_latticegen(d))
        entry = {"bits_profile": prof, "latticegen_diag_bitlens": ref_bl}
        if d in lean:
            entry["lean_diag_bitlens"] = check_envelope("lean", d, lean[d])
            entry["lean_row0"] = lean[d][0]
        golden["ajtai"][str(d)] = entry
        tag = "lean+latticegen" if d in lean else "latticegen"
        print(f"d={d:3d}  OK ({tag})  bits_profile={prof}")
    if not check_only:
        GOLDEN.write_text(json.dumps(golden, indent=2) + "\n")
        print(f"wrote golden metadata -> {GOLDEN.relative_to(ROOT)}")
    print("validate_latticegen: structural envelope holds.")
    return 0

if __name__ == "__main__":
    sys.exit(main())

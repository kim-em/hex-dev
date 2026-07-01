#!/usr/bin/env python3
"""Validate the Lean lattice-basis generators structurally.

The four Phase-4 worst-case families are faithful Lean ports of fplll's
`gen_trg`/`gen_qary`/`gen_ntrulike`/`gen_intrel` (see the citations in
`bench/HexLLLBench/Inputs.lean`). Entry-for-entry equality with fplll is
impossible — fplll draws from GMP's RNG, the Lean ports from a committed POSIX
LCG — so this checks the *structural envelope* each generator must satisfy,
reproducibly, from committed Lean matrices in `scripts/dev/lattice-matrices.jsonl`
(regenerate with `scripts/dev/gen_lattice_matrices.sh`).

For the `ajtai`/`gen_trg` family the fplll output is additionally cross-checked
against `latticegen t <d> 1.2`: the deterministic diagonal bit-length profile is
compared per generator (fplll's float `(int)pow(2d-i, 1.2)` vs the Lean exact
integer `floor((2d-i)^(6/5))`), which agree to within 1 bit at exact-power
boundaries (e.g. 32^1.2 = 64) — an explicitly asserted tolerance. `latticegen`'s
`q`/`n` argument forms are not exercised (their extra parameter is not verifiable
without the vendored source), so those families are validated structurally only.

Usage:
  python3 scripts/dev/validate_latticegen.py            # validate + write golden
  python3 scripts/dev/validate_latticegen.py --check     # validate only (CI)
"""
from __future__ import annotations
import json, os, re, subprocess, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
CACHE = os.environ.get("HEX_ORACLE_CACHE", str(ROOT / ".cache/oracles"))
LATTICEGEN = pathlib.Path(CACHE) / "fplll-ffi/src/vendor/fplll/fplll/latticegen"
LEAN_MATS = ROOT / "scripts/dev/lattice-matrices.jsonl"
GOLDEN = ROOT / "scripts/dev/latticegen-golden.json"
ALPHA = 1.2
SEED = 1
AJTAI_DIMS = [6, 8, 10, 12, 16, 20]
QARY_BITS = 30          # bench qaryBits
NTRU_BITS = 30          # bench ntruBits

# ---- ajtai bits profiles (fplll float pow vs Lean exact integer root) --------

def _iroot(k: int, n: int) -> int:
    r = int(round(n ** (1.0 / k))) if n > 0 else 0
    while r > 0 and r ** k > n:
        r -= 1
    while (r + 1) ** k <= n:
        r += 1
    return r

def bits_float(d: int) -> list[int]:
    return [int((2 * d - i) ** ALPHA) for i in range(d)]        # fplll (int)pow

def bits_exact(d: int) -> list[int]:
    return [_iroot(5, (2 * d - i) ** 6) for i in range(d)]      # Lean ajtaiBits

# ---- per-family structural validators (raise AssertionError on violation) ----

def check_ajtai(name: str, d: int, M: list[list[int]], prof: list[int]) -> None:
    assert len(M) == d and all(len(r) == d for r in M), f"{name} ajtai d={d}: not {d}x{d}"
    for i in range(d):
        Di = abs(M[i][i])
        assert Di >= 1, f"{name} ajtai d={d}: zero diagonal at {i}"
        assert Di.bit_length() <= prof[i], \
            f"{name} ajtai d={d}: diag[{i}] bitlen {Di.bit_length()} > profile {prof[i]}"
        for j in range(i + 1, d):
            assert M[i][j] == 0, f"{name} ajtai d={d}: upper entry [{i}][{j}] != 0"
        for j in range(i):
            assert 2 * abs(M[i][j]) < abs(M[j][j]), \
                f"{name} ajtai d={d}: |off[{i}][{j}]| >= diag[{j}]/2"

def check_qary(d: int, M: list[list[int]]) -> None:
    assert len(M) == d and all(len(r) == d for r in M), f"q-ary d={d}: not {d}x{d}"
    k = d // 2
    q = M[d - k][d - k]
    assert q >= 2, f"q-ary d={d}: q={q} < 2"
    for i in range(d):
        for j in range(d):
            if i < d - k and j < d - k:                 # A00 = I
                assert M[i][j] == (1 if i == j else 0), f"q-ary d={d}: A00[{i}][{j}]"
            elif i < d - k and j >= d - k:              # A01 = H, uniform mod q
                assert 0 <= M[i][j] < q, f"q-ary d={d}: H[{i}][{j}]={M[i][j]} not in [0,q)"
            elif i >= d - k:                            # A10 = 0, A11 = qI
                assert M[i][j] == (q if i == j else 0), f"q-ary d={d}: bottom[{i}][{j}]"

def check_ntru(param: int, M: list[list[int]]) -> None:
    d, d2 = param, 2 * param                       # ntruBasis param -> 2*param square
    assert len(M) == d2 and all(len(r) == d2 for r in M), f"ntru param={param}: not {d2}x{d2}"
    q = M[d][d]
    assert q >= 2, f"ntru d={d}: q={q} < 2"
    for i in range(d2):
        for j in range(d2):
            if i < d and j < d:                         # I
                assert M[i][j] == (1 if i == j else 0), f"ntru: A00[{i}][{j}]"
            elif i >= d and j < d:                      # 0
                assert M[i][j] == 0, f"ntru: A10[{i}][{j}]"
            elif i >= d and j >= d:                     # qI
                assert M[i][j] == (q if i == j else 0), f"ntru: A11[{i}][{j}]"
            else:                                       # A01 = circulant Rot(h)
                assert 0 <= M[i][j] < q, f"ntru: h[{i}][{j}]={M[i][j]} not in [0,q)"
                assert M[i][j] == M[0][d + ((j - d - i) % d)], f"ntru: not circulant at [{i}][{j}]"
    hsum = sum(M[0][d + t] for t in range(d)) % q       # h(1) = sum of h, must be 0 mod q
    assert hsum == 0, f"ntru d={d}: h(1) = {hsum} != 0 mod q"

def check_knapsack(d: int, M: list[list[int]]) -> None:
    assert len(M) == d and all(len(r) == d + 1 for r in M), f"knapsack d={d}: not {d}x{d+1}"
    for i in range(d):
        assert M[i][0] >= 0, f"knapsack d={d}: weight[{i}] < 0"
        for j in range(1, d + 1):
            assert M[i][j] == (1 if j == i + 1 else 0), f"knapsack d={d}: unit block [{i}][{j}]"

# ---- latticegen reference (ajtai only) ---------------------------------------

def parse_matrix(text: str) -> list[list[int]]:
    rows = []
    for line in text.splitlines():
        nums = re.findall(r"-?\d+", line)
        if nums:
            rows.append([int(x) for x in nums])
    return rows

def run_latticegen_ajtai(d: int) -> list[list[int]]:
    out = subprocess.run([str(LATTICEGEN), "-randseed", str(SEED), "t", str(d), str(ALPHA)],
                         capture_output=True, text=True, check=True).stdout
    return parse_matrix(out)

def lean_matrices() -> dict[str, dict[int, list[list[int]]]]:
    res: dict[str, dict[int, list[list[int]]]] = {}
    if not LEAN_MATS.exists():
        return res
    for line in LEAN_MATS.read_text().splitlines():
        line = line.strip()
        if line.startswith('{"family"'):
            obj = json.loads(line)
            res.setdefault(obj["family"], {})[obj["d"]] = obj["basis"]
    return res

CHECKERS = {"q-ary": check_qary, "ntru": check_ntru, "knapsack": check_knapsack}

def main() -> int:
    check_only = "--check" in sys.argv
    lean = lean_matrices()
    if not lean:
        print(f"error: committed Lean matrices missing at {LEAN_MATS}", file=sys.stderr)
        return 2

    golden: dict = {"provenance": {"note": "structural envelope only; entries differ "
                    "(GMP vs LCG RNG). ajtai fplll bits profile cross-checked to <=1 bit.",
                    "alpha": ALPHA, "seed": SEED, "qary_bits": QARY_BITS, "ntru_bits": NTRU_BITS},
                    "ajtai": {}}

    # ajtai: Lean structure + fplll latticegen cross-check with <=1-bit bits tolerance
    have_lg = LATTICEGEN.exists()
    if not have_lg:
        print(f"note: latticegen absent at {LATTICEGEN}; ajtai fplll cross-check skipped.")
    for d in AJTAI_DIMS:
        pf, pe = bits_float(d), bits_exact(d)
        for i in range(d):
            assert abs(pf[i] - pe[i]) <= 1, f"ajtai d={d}: bits profiles differ by >1 at {i}"
        entry = {"bits_float": pf, "bits_exact": pe}
        assert d in lean.get("ajtai", {}), f"ajtai d={d}: missing Lean matrix"
        check_ajtai("lean", d, lean["ajtai"][d], pe)
        tag = "lean"
        if have_lg:
            check_ajtai("latticegen", d, run_latticegen_ajtai(d), pf)
            tag = "lean+latticegen"
        golden["ajtai"][str(d)] = entry
        print(f"ajtai d={d:3d}  OK ({tag})")

    # q-ary / ntru / knapsack: structural validation of the committed Lean matrices
    for fam, checker in CHECKERS.items():
        dims = sorted(lean.get(fam, {}))
        assert dims, f"{fam}: no committed Lean matrices"
        for d in dims:
            checker(d, lean[fam][d])
            print(f"{fam:9s} d={d:3d}  OK (lean structure)")
        golden[fam] = {"dims": dims}

    if not check_only:
        GOLDEN.write_text(json.dumps(golden, indent=2) + "\n")
        print(f"wrote golden metadata -> {GOLDEN.relative_to(ROOT)}")
    print("validate_latticegen: all four families satisfy their structural envelopes.")
    return 0

if __name__ == "__main__":
    sys.exit(main())

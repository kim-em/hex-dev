# HexArith Nat API Phase 6 Review

Scope: `HexArith/Nat/ModArith.lean` and `HexArith/Nat/Pow.lean`, checked
against `SPEC/Libraries/hex-arith.md` and `PLAN/Phase6.md`.

## Findings

No follow-up findings.

- `Nat.coprime_pow_two_of_odd` has a precise Montgomery-facing name and
  statement. Its only direct production caller,
  `HexArith/Montgomery/Context.lean`, discharges the `Nat.Coprime p (2 ^ k)`
  side condition by applying the public theorem directly, without unfolding
  Montgomery internals or local proof witnesses.
- `Hex.Nat.sub_one_dvd_pow_sub_one` exposes the geometric-series divisibility
  bridge directly and hides the private witness construction
  `pow_eq_succ_mul_sub_one_add_one_of_one_le`.
- `Hex.Nat.pow_sub_one_dvd_pow_sub_one_of_dvd` has the downstream theorem shape
  needed by `HexBerlekamp/RabinSoundness.lean`; the caller uses it directly to
  bridge exponent divisibility into polynomial divisibility.
- The public exponent-divisibility lemmas are tagged `@[simp, grind .]`, which
  matches their normalization role. The coprimality lemma is intentionally not a
  simplification rule because it requires an oddness hypothesis and is used as a
  named side-condition bridge.
- Public declarations and the non-obvious private helper have docstrings. The
  modules keep namespace scope narrow and introduce no extra imports.

## Residual Risk Checked

The audit was limited to API polish for the Nat-level arithmetic helpers. It did
not review Barrett, Montgomery, FFI, or benchmark behavior beyond confirming the
direct callers above are not forced to unfold these helper implementations.

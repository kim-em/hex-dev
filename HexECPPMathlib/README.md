# hex-ecpp-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4. The aim is fast executable code, fully verified, built with
spec-driven development.

Use elliptic curve primality proving (ECPP) to obtain Lean proofs of
`Nat.Prime n`. You can check a saved primality certificate or ask Hex's
built-in search or PARI/GP to find one. Each certificate records elliptic
curve points and proofs of smaller primes; Hasse's bound shows that accepted
data excludes every possible small prime divisor of `n`.

This companion supplies that mathematical proof and the certificate tactics.
It depends on
[`hex-ecpp`](https://github.com/leanprover/hex-ecpp),
[`hex-primality-mathlib`](https://github.com/leanprover/hex-primality-mathlib),
Mathlib and [AINTLIB](https://github.com/CBirkbeck/AINTLIB). The computational
partner supplies the arithmetic checker and built-in search. See the
[manual](https://kim-em.github.io/hex-dev/HexECPP___-bounded-elliptic-curve-certificates/Introduction/)
for a first proof and an explanation of the mathematics.

# Quickstart

```toml
[[require]]
name = "hex-ecpp-mathlib"
git = "https://github.com/leanprover/hex-ecpp-mathlib.git"
rev = "main"
```

```lean
module
public import HexECPPMathlib

namespace MyPrimes
@[expose] public def seventeen : Hex.ECPP.Cert :=
  .step 17 2 3 3 6 6 [10, 13, 3, 13] (.base (.small 11))

example : Nat.Prime 17 := by ecpp using seventeen
example : Nat.Prime 17 := by
  ecpp using (ecpp_cert% "[[17,7,1,2,[3,6]]]" using (.small 11))
end MyPrimes
```

# Functionality

- `Hex.ECPP.natPrime_of_check` and `natPrime_of_checkAt` turn raw checker
  acceptance into primality, with no extra mathematical premise.
- `startingPoint_rep`, `add_rep` and `replayBits_rep` interpret the checker
  over every prime divisor of the subject, including composite subjects.
- `hasse_sq_zmod` supplies the proved Hasse bound; `rationalPointsEquivFixed`
  and `rationalPointsEquivKer` describe the independent Frobenius correspondence.
- `ecpp using` replays closed constructor data. `ecpp_cert%` decodes compact
  frozen rows with an explicit terminal `Hex.Nat.PrimeCert`.
- Import `HexECPPMathlib.Native` for `primality? (method := ecpp)` and
  `#ecpp_export (method := ecpp) MyCertificates.Prime cert for n`.
- Import `HexECPPMathlib.Pari` for `primality? (method := pari)` and
  `#ecpp_export MyCertificates.Prime cert for n`. Generation requires PARI/GP
  on POSIX; importing and replaying its exported certificate does not.

Export once in a batch build, remove the command, then add
`public import MyCertificates.Prime` and use
`ecpp using MyCertificates.Prime.cert`. Exports create new files exclusively.
The language server displays build instructions instead of writing a file.

# Verification

Every successful primality proof uses the proved soundness theorem and
kernel replay of the arithmetic checker. The Hasse theorem is imported from
the pinned AINTLIB development. Guarded dependency audits permit only
`propext`, `Classical.choice` and `Quot.sound`. Search and external proposals
are untrusted; suggestions and exports are kernel-checked before publication.

Replay and explicitly selected native production are admitted through 512 bits.
Native generation defaults to 256 bits; select `primality? (method := ecpp)
(bits := 512) (seed := 0)` or `#ecpp_export (method := ecpp) (bits := 512)
(seed := 0) MyCertificates.Prime cert for n` for the finite 512-bit policy.
Only 256 and 512 are accepted policy choices. Search can exhaust its allocation. Replay allows
32 total certificate nodes, counting the ECPP base and every terminal node,
with independent syntax and inverse-transcript limits. The 512-bit search accounts for the 20-row and 32-node ceilings while
backtracking; generation also validates the exact frozen representation before
suggesting or exporting it.
Exhaustion proves nothing about compositeness. There is no automatic ECPP
fallback or `norm_num` registration.

Use [`hex-ecpp`](https://github.com/leanprover/hex-ecpp) alone for
Mathlib-free computation. See the [SPEC](SPEC/hex-ecpp-mathlib.md) for
constructor policy, process cleanup, exact allocations and failure semantics.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in the published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.

# Mixed factorization integration

`HexIntFactorMathlib.Mixed` uses `Hex.ECPP.natPrime_of_checkAt` to discharge the
optional computational factorization extension's ECPP soundness hypothesis.
Complete and partial Mathlib factorization correspondence lives in that
companion. Shared auditing and reification now live in `HexECPP.ElabData`;
`HexECPPMathlib.Policy` remains a compatibility import of `HexECPP.Policy`.

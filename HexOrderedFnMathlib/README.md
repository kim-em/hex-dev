# hex-ordered-fn-mathlib

`HexOrderedFnMathlib` is part of [Hex](https://github.com/kim-em/hex-dev), a computer
algebra library for Lean 4. The aim is fast executable code, fully verified,
built with spec-driven development.

It proves containment, evaluation and ordered-extension laws for `HexOrderedFn`,
using `HexRationalFnMathlib` and `HexPolyMathlib`. This Mathlib companion is an
unreleased development library.
The [manual](https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-ordered-fn)
explains the proofs alongside their computational operations.

# Quickstart

Use this import from the `hex-dev` monorepo; there is no released package yet.
Provider validity gives the resulting registration a linear order without
requiring callers to extract its existential semantic witnesses.

```lean
import HexOrderedFnMathlib
open Hex.OrderedFn Hex.OrderedFn.Oracle

example {K : Type} [Field K] [DecidableEq K]
    {a : Approximation K} (h : Real.Valid a) :
    LinearOrder (Real.Extension (Real.registration h)) :=
  Real.Extension.linearOrder h.orderValid
```

# Functionality

- `Oracle.Contains` proves containment through the actual bound operations.
  `ApproximationCorrect` binds the precise provider, embedding and subject.
- `Infinitesimal.embed` injects canonical fractions into ordered Laurent/Hahn
  series. Lowest-coefficient signs, normalization and comparisons agree with
  that model. Scoped order instances give an ordered field.
- `Infinitesimal.X_pos`, `X_lt_C` and `X_lt_pow` characterize positive and
  successive infinitesimals. `mapHom_sign` and `mapHom_strictMono` preserve
  signs and order through an ordered coefficient-field embedding.
- `Real.eval` is total real division. `evalHom` is an injective field
  homomorphism under relative transcendence over the whole predecessor field.
- `Real.horner_converges`, `attempt_progress` and `approx_progress` prove
  shrinking bounds and total-search progress from containment, width guarantees
  and relative transcendence. `sign_of_attempt` uses a finite successful trial
  without reducing an opaque accessibility proof.
- `Real.registration` derives erased termination proofs from `Valid`.
  `registration_source` identifies its provider; `Valid.orderValid` supplies
  its order hypothesis. `Extension.coreField_eq` preserves the native field
  dictionary, while `transport_lt` checks both providers against one subject.

# Verification

Containment suffices for successful-trial soundness. Total field registration
additionally needs shrinking widths and relative transcendence. Preserving an
already chosen predecessor order also requires a strictly monotone embedding;
`Valid` does not impose that extra hypothesis.

`finiteAttempt_sound` and `sign?_sound` certify the stored denominator is nonzero.
They do not discharge source-expression divisor guards erased by cancellation.
Infinitesimal interpretation uses Hahn series; it does not give a global
ordinary-real embedding of a positive infinitesimal.

`HexOrderedFnTests` builds ordinary-kernel examples and axiom guards.
`hexorderedfn_liouville_test` runs registered searches after proof erasure using a
test-local Liouville provider; no named constant provider is exported.
The computational [performance report](../reports/hex-ordered-fn-performance.md)
is separate from these proof checks. See [the specification](SPEC/hex-ordered-fn-mathlib.md)
for the full hypotheses.

# Contributing

Development happens in [hex-dev](https://github.com/kim-em/hex-dev).
Contributions are welcome as PRs to `SPEC/`: describe the behavior you want.

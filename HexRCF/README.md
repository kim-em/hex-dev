# hex-rcf

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

A proof-producing Lean tactic, `rcf`, deciding the univariate fragment of
real-closed-field arithmetic: Boolean combinations of polynomial
(in)equalities in one real variable under a single quantifier over `ℝ` or
over a half-open dyadic interval. The package builds on
[`hex-real-roots`](https://github.com/leanprover/hex-real-roots),
[`hex-real-roots-mathlib`](https://github.com/leanprover/hex-real-roots-mathlib),
[`hex-poly-z`](https://github.com/leanprover/hex-poly-z), and Mathlib. The
tactic targets `ℝ`, so its soundness theorem lives in this same package;
there is no separate `hex-rcf-mathlib`.

# Quickstart

```toml
[[require]]
name = "hex-rcf"
git = "https://github.com/leanprover/hex-rcf.git"
rev = "main"
```

```lean
import HexRCF

example : ∀ x : ℝ, x ^ 2 + 1 > 0 := by rcf
example : ∀ x : ℝ, 0 < x → x ^ 2 + 1 ≥ 2 * x := by rcf
example : ∃ x : ℝ, x ^ 3 - x - 1 = 0 ∧ 1 < x ∧ x < 2 := by rcf
```

# Functionality

For an in-fragment sentence the compiled builder constructs a squarefree
carrier polynomial, isolates its real roots with Sturm certificates, and
decides the sentence on the resulting cell decomposition of `ℝ`, the
one-variable case of Tarski's theorem. Neither `polyrith` nor `nlinarith`
is complete on this fragment, and `decide` does not apply to quantifiers
over `ℝ`.

- The `rcf` tactic reifies a goal, runs the builder, and replays the
  returned certificate through a small kernel checker.
- `Hex.RCF.decide`, `Hex.RCF.build?`, and the certificate types are the
  programmatic surface beneath the tactic.
- A `false` verdict is diagnostic only: the tactic reports the failing cell
  but never proves a negation. Builder failure is a separate error channel
  and is never reported as `false`.

# Verification

Every `true` verdict is kernel-checked. The headline theorem
`Hex.RCF.check_sound` states that any certificate accepted by the public
Boolean checker proves its sentence (`cert.check s = true → s.toProp`), and
the kernel checks that Boolean reduction together with the reifier's
equivalence with the original goal, so no unverified output of the compiled
builder or reifier is trusted. Operational totality of the builder on
in-fragment sentences follows from the completeness theorems of
[`hex-real-roots-mathlib`](https://github.com/leanprover/hex-real-roots-mathlib);
no completeness theorem is stated for `false` verdicts.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.

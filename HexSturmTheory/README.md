# hex-sturm-theory

`HexSturmTheory` is part of [Hex](https://github.com/kim-em/hex-dev), a computer
algebra library for Lean 4. The aim is fast executable code, fully verified,
built with spec-driven development.

It proves the domain, root-sum and certificate contracts for `HexSturm`, using
`HexPolyTheory` and `HexRealRootsTheory`. Mathlib and Tau Ceti belong to this
proof layer. This development library is unreleased.
The [manual](https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-sturm)
documents the computations alongside their correspondence theorems.

# Quickstart

Use these imports from the `hex-dev` monorepo; there is no released package yet.
The real-roots companion supplies the real-closed-field instance for `ℝ`.
The equivalence below characterizes both success and the returned signed sum.

```lean
import HexSturmTheory
import HexRealRootsTheory
open Hex HexPolyTheory.Interpret HexRealRootsTheory
open scoped Classical
noncomputable section

example (p q : DensePoly ℝ) (a b : Endpoint ℝ) (v : Int) :
    Sturm.query Sturm.orderSign p q a b = some v ↔
      HexSturmTheory.Domain id (fun _ => Iff.rfl) p a b ∧
      v = Tarski.rootSum (interpret id (fun _ => Iff.rfl) p)
        (interpret id (fun _ => Iff.rfl) q) (a.map id) (b.map id) :=
  HexSturmTheory.query_iff id (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    Sturm.orderSign HexSturmTheory.orderSign_eq
    (fun _ => rfl) (fun _ => rfl) p q a b v
```

# Functionality

- `Domain` states a nonzero squarefree interpreted head, strictly ordered
  endpoints and nonvanishing at finite endpoints. `query_isSome`, `prepare_isSome`
  and `query_iff` characterize that domain exactly.
- `check_sound` proves domain validity and the signed root sum for arbitrary
  accepted certificates. `certify_checks` and its prepared variants prove
  acceptance of produced evidence, independently of arbitrary replay soundness.
- `queryPrepared_sound`, `countPrepared_sound` and `countPrepared_nonneg`
  identify prepared results on their current interval. `withEndpoints_isSome`
  and `withEndpoints_domain` characterize endpoint retargeting.
- `query_count`, `query_sign` and `query_bound` give distinct-root counts,
  singleton-root signs and degree bounds. `query_nonneg` justifies natural-number
  conversion; `rootCount_sturm` bridges successful finite-dyadic counts to the
  existing half-open integer count with root-free endpoints.
- `queryReduced_eq` preserves the whole ordinary query result under lawful
  division. `query_congr` compares representations at corresponding endpoints,
  allowing independent positive scaling of both input polynomials.
- `query_rat_eq` proves whole-`Option` rational/integer agreement on finite dyadic
  intervals after positive denominator clearing. `DenominatorClearing.certificate_checks` and
  `IntCast.certificate_checks` preserve acceptance when translating certificates,
  retaining literal contexts and values without rerunning the producer.

# Verification

Root-sum semantics and arbitrary-certificate soundness are proved over an ordered
real closed field. Generic correspondence theorems permit noninjective coefficient
interpretations: storage needs lawful operations and zero reflection, not its own
field or order instance. Producer results additionally require lawful negation and
inversion. Representation transport compares supplied interpretations; it does not
construct a common field or ordinary-real realization of arbitrary extensions.

`HexSturmTheoryTests` and `HexQuerySemantics` build semantic regression tests and
ordinary-kernel axiom guards. Those guards admit only `propext`, `Classical.choice`
and `Quot.sound`. Executable translations remain in Mathlib-free `HexSturm.Transport`.
See [the specification](SPEC/hex-sturm-theory.md) for the full hypotheses.

# Contributing

Development happens in [hex-dev](https://github.com/kim-em/hex-dev).
Contributions are welcome as PRs to `SPEC/`: describe the behavior you want.

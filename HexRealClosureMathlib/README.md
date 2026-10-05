# hex-real-closure-mathlib

`HexRealClosureMathlib` is part of [Hex](https://github.com/kim-em/hex-dev), a
computer algebra library for Lean 4. The aim is fast executable code, fully
verified, built with spec-driven development.

This unreleased Mathlib companion supplies base interpretation proofs.
Development semantic modules in the `HexQuerySemantics` Lake target additionally
prove root completeness, multiplicity, order and transport laws for the native
real-closure family.
The [manual](https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-real-closure)
explains these laws beside their computational operations.

# Quickstart

Use these imports inside `hex-dev`. The umbrella supplies the base-model APIs;
`HexRealClosureMathlib.TowerRoots` supplies tower-root semantics through the
currently built development modules under `adapters/`. Those modules are not
therefore available from a published companion package.

```lean
import HexRealClosureMathlib.TowerRoots
open Hex Hex.RealClosure Hex.RealClosure.Tower

example {registry : BaseContext.Registry}
    {parent : Context registry} {K : Type}
    [Field K] [LinearOrder K] [DecidableEq K]
    [IsStrictOrderedRing K] [IsRealClosed K]
    (model : Model parent K) (p : DensePoly parent.Value) :
    parent.roots? p = .ok (parent.roots p) :=
  Context.roots?_success model p
```

# Functionality

- `Model` binds a native context's actual operations and sign to a field with a
  linear order. Root theorems additionally require ordered-ring laws and real
  closedness. The `TowerRoots` development import supplies `Model`,
  `Model.base` and `Model.adjoin`; the constructors use their base and
  selected-root hypotheses. Executable constructors do not take a model.
- `Context.roots_all`, `roots?_success`, `roots_spec` and `roots_sorted`
  characterize zero, prove actual producer success, recover original
  multiplicities and establish strict ordering.
- `Root.embed_value`, `convertedValue_value` and `signAt_value` identify the
  actual cached coefficient embedding and selected value.
- Selected-root arithmetic proves zero reflection and inversion using the
  appropriate cofactor, including reducible defining polynomials.
- Conversion, enlargement and sample-family proofs retain their explicit
  model, dependency and selected-embedding hypotheses.

# Verification

A common ordered real-closed model can be non-Archimedean. These correspondence
laws do not give an ordinary-real embedding of a positive infinitesimal or
construct the whole joint realization of an arbitrary serialized tower.
Producer totality is distinct from soundness of arbitrary accepted evidence.
Source-expression divisors erased by cancellation remain the consumer's guards.

The existing tests and conformance suites check actual native roots, selected
embeddings, zero/all cases, multiplicities, transport and sample semantics.
Small transport guards execute during builds; the deep four-level fixture
is type-checked, with its execution outside routine CI. Ordinary-kernel axiom
guards accompany representative proofs; exact Z3 and
python-flint oracles check fixtures. Computational tower performance is recorded
separately from theorem applications. See [the specification](../SPEC/Libraries/hex-real-closure-mathlib.md).

# Contributing

Development happens in [hex-dev](https://github.com/kim-em/hex-dev).
Contributions are welcome as PRs to `SPEC/`: describe the behavior you want.

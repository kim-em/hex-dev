# HexGFqField Phase 6 API Review

## Scope

Audited surfaces:

- `SPEC/Libraries/hex-gfq-field.md`
- `SPEC/Libraries/hex-gfq-ring.md`
- `PLAN/Phase6.md`
- `HexGFqField/Basic.lean`
- `HexGFqField/Operations.lean`
- `HexGFqField/Conformance.lean`
- `HexGFqField/Bench.lean`
- `reports/hex-gfq-field-performance.md`

The review focused on API quality rather than implementation changes:
public theorem shape, quotient-wrapper conversions, inverse/division and
Frobenius characterising lemmas, automation annotations, and SPEC layering.

## Prioritized Findings

### P1: Remove the duplicate prime-evidence burden from the public operations API

`FiniteField f hf hp hirr` already carries explicit prime evidence as a
type parameter, and `Basic.lean` shows the intended pattern by deriving
`ZMod64.PrimeModulus p` locally from `hp` in `degree_repr_lt_degree`.
`Operations.lean`, however, declares a global section variable:

```lean
variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] {hp : Hex.Nat.Prime p}
```

That means users of the field API must supply both the explicit `hp` in
the field type and an ambient `[ZMod64.PrimeModulus p]` instance for
operations and algebra instances. The extra typeclass is derivable from
`hp` via `ZMod64.primeModulusOfPrime hp`, so this is avoidable API
friction and makes the wrapper feel less self-contained than the SPEC
description.

Worker-sized follow-up:

- Change `HexGFqField/Operations.lean` to avoid requiring an external
  `[ZMod64.PrimeModulus p]` wherever the explicit `hp` can derive it.
- Keep the user-facing surface centered on the parameters of
  `FiniteField f hf hp hirr`.
- Rebuild `HexGFqField` and check downstream conformance/bench files for
  any places that were relying on the ambient instance by accident.

### P1: Hide inverse implementation details behind field-level characterising lemmas

The public inverse API currently exposes `invPoly` and two public lemmas
that mention the xgcd-derived polynomial witness directly:

- `invPoly`
- `toQuotient_inv_of_ne_zero`
- `repr_inv_of_ne_zero`

This is useful for proving `mul_inv_cancel`, but it is not the natural
API expected by downstream users of `FiniteField`. It also leaks a
quotient-level implementation detail from `HexGFqField` into public
statements. The important public facts are field-level facts:
`x * x⁻¹ = 1`, `x⁻¹ * x = 1`, `0⁻¹ = 0`, and division as multiplication
by inverse.

Worker-sized follow-up:

- Move `invPoly` and the xgcd-shaped projection lemmas to an `Internal`
  namespace or make them private if no downstream module needs them.
- Keep or add public field-level lemmas whose statements do not mention
  the xgcd witness:
  `inv_zero`, `mul_inv_cancel`, `inv_mul_cancel`, `div_eq_mul_inv`, plus
  any projection lemmas stated in terms of these field-level facts rather
  than `invPoly`.
- If a projection lemma for inverse remains public, prefer a statement
  that characterises its behaviour by multiplication in the quotient,
  not by naming the selected Bezout coefficient.

### P2: Add Phase 6 docstrings to the remaining public declarations

`Basic.lean` is mostly documented, but `Operations.lean` still has
several public declarations without docstrings, including:

- `zero_ne_one`
- `repr_natCast`
- the `natCast_*` equality theorems
- `inv_zero`
- `div_eq_mul_inv`
- `mul_inv_cancel`
- `inv_mul_cancel`
- `repr_add`, `repr_mul`, `repr_pow`, `repr_div`,
  `repr_zpow_ofNat`, `repr_zpow_negSucc`
- the `Lean.Grind.*` instances
- `frob_eq_pow`
- `repr_frob`

These declarations are part of the downstream reasoning surface, so they
fall under Phase 6's public-docstring rule. The missing comments are
small, mechanical, and can be handled without changing proofs.

Worker-sized follow-up:

- Add concise docstrings describing when a lemma is a quotient-projection
  lemma, a representative-normalisation lemma, a field law, or an
  automation instance.
- Keep private proof scaffolding private; only document private helpers
  whose purpose is not obvious from the name.

### P2: Tighten import layering in `Basic.lean`

`HexGFqField/Basic.lean` imports `HexGFqRing.Operations`, but the
definitions and lemmas it uses are the quotient representation, `ofPoly`,
`repr`, `reduceMod`, and `degree_repr_lt_degree`, all provided by the
basic quotient layer. Importing the ring operations into the basic field
wrapper makes the foundational wrapper heavier than necessary and blurs
the intended split between representation and operation layers.

Worker-sized follow-up:

- Try replacing `import HexGFqRing.Operations` in
  `HexGFqField/Basic.lean` with `import HexGFqRing.Basic`.
- Keep `HexGFqField/Operations.lean` as the module that imports quotient
  operations and defines field operations.
- Verify with `lake build HexGFqField`.

### P3: Review automation annotations after hiding inverse internals

The quotient-projection lemmas for zero, one, casts, addition,
multiplication, negation, subtraction, powers, division, signed powers,
and Frobenius are consistently marked with `@[simp, grind =]`.
Representative lemmas are mostly `@[simp]`. This is a good baseline.

The one area to revisit is inverse: once `invPoly` is hidden, the public
automation surface should still make common goals easy:

- simplify `0⁻¹` to `0`;
- rewrite `x / y` to `x * y⁻¹` when useful;
- allow `grind` to use nonzero inverse cancellation through the
  `Lean.Grind.Field` instance.

Worker-sized follow-up:

- After the inverse API cleanup, add tiny examples or conformance checks
  that `simp` and `grind` still close the expected inverse/division goals.
- Avoid adding a broad `[simp]` rewrite for `div_eq_mul_inv` unless it is
  known not to create loops in local automation.

## Audited Surfaces With No Follow-Up Needed

- Representation layering: `FiniteField` is a thin wrapper over
  `GFqRing.PolyQuotient`; equality, `repr`, and `ofQuotient` all preserve
  the single canonical quotient-representative story.
- Ring-operation delegation: addition, multiplication, negation,
  subtraction, casts, scalar multiplication, and natural powers delegate
  to `GFqRing.PolyQuotient` and rewrap reduced representatives.
- Exponentiation shape: natural powers use the quotient-ring
  square-and-multiply implementation. Frobenius is definitionally
  `pow x p` and has both field-level and projection lemmas.
- Field laws: the public surface includes `Lean.Grind.Semiring`,
  `Lean.Grind.Ring`, `Lean.Grind.CommRing`, `Lean.Grind.Field`, and
  `Lean.Grind.IsCharP` instances for `FiniteField`.
- Finiteness/cardinality layering: no `Fintype`, cardinality, or
  Mathlib finite-field classification facts are exposed by
  `HexGFqField/Basic.lean` or `HexGFqField/Operations.lean`; those remain
  appropriate future `HexGFqMathlib` work.
- Oracle boundary: core field declarations do not depend on an external
  oracle. Conformance and benchmarks use Lean-checked Berlekamp/Rabin
  certificates for irreducibility witnesses. FLINT is confined to
  informational benchmark comparator code and the performance report.
- Runtime bans: the audited field files contain no `axiom`, no `sorry`,
  and no `native_decide`.

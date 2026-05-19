## Current state

`HexGfq/Basic.lean` exposes the Conway-specialized convenience type `GFq p n h`
as an `abbrev` for `GFqField.FiniteField (Conway.conwayPoly p n h) ...`. The
namespace currently carries the representative simp wrappers for the basic
ring constructors:

```lean
@[simp] theorem GFq.repr_zero (h : Conway.SupportedEntry p n) :
    repr (0 : GFq p n h) = GFqRing.reduceMod (modulus h) 0 := rfl
@[simp] theorem GFq.repr_one (h : Conway.SupportedEntry p n) :
    repr (1 : GFq p n h) = GFqRing.reduceMod (modulus h) 1 := rfl
@[simp] theorem GFq.repr_add {h : Conway.SupportedEntry p n} (x y : GFq p n h) :
    repr (x + y) = GFqRing.reduceMod (modulus h) (repr x + repr y) := rfl
@[simp] theorem GFq.repr_mul {h : Conway.SupportedEntry p n} (x y : GFq p n h) :
    repr (x * y) = GFqRing.reduceMod (modulus h) (repr x * repr y) := rfl
```

The underlying generic `GFqField.FiniteField` API in
`HexGfqField/Operations.lean` exposes the `repr_pow` simp lemma:

```lean
@[simp] theorem GFqField.repr_pow
    (x : FiniteField f hf hp hirr) (n : Nat) :
    repr (x ^ n) = GFqRing.repr (x.toQuotient ^ n) :=
  rfl
```

`GFq` does not yet expose the analogous `repr_pow` wrapper. The simp chain
`repr_eq_field_repr` then `GFqField.repr_pow` works in principle, but a direct
wrapper named in the `Hex.GFq` namespace matches the existing
`GFq.repr_zero`/`one`/`add`/`mul` pattern and keeps the simp normal form
uniform across the four ring constructors and exponentiation.

## Deliverables

1. Extend namespace `Hex.GFq` in `HexGfq/Basic.lean`, immediately after the
   existing `@[simp] theorem repr_mul` declaration, with:

   ```lean
   /-- The canonical representative of a natural power in `GFq` lifts the
   quotient-ring power of the underlying quotient representative. -/
   @[simp] theorem repr_pow {h : Conway.SupportedEntry p n}
       (x : GFq p n h) (k : Nat) :
       repr (x ^ k) = GFqRing.repr (x.toQuotient ^ k) :=
     rfl
   ```

2. Proof shape: `rfl`, matching the underlying `GFqField.repr_pow`. No
   unfolding of Conway-table machinery or non-`rfl` reasoning.

## Library placement

Target file: `HexGfq/Basic.lean`.

SPEC section: `SPEC/Libraries/hex-gfq.md`. Quote:
"`GFq p n` is the canonical, always-available constructor, with a uniform
generic representation for every `p`."

Placement questions:

- **Which SPEC § governs this file?** The `hex-gfq.md` snippet above pins
  generic `GFq` to `HexGfq/Basic.lean` and pins canonical representative
  conversions to that file.
- **Does the natural strategy use Mathlib?** No. This is Mathlib-free API
  polishing over the existing executable backend.
- **Is this result already in Mathlib?** No analog (`GFq`/`FiniteField` is
  hex-specific). The closed-form RHS is the underlying `GFqRing.repr`.
- **Does the deliverable presuppose missing infrastructure?** No.
  `GFqField.repr_pow`, `Pow (FiniteField …) Nat`, and the canonical
  `Hex.GFq` namespace already exist.

## Context

- `PLAN/Phase6.md` (proof polishing rules).
- `SPEC/Libraries/hex-gfq.md` and `SPEC/Libraries/hex-gfq-field.md` for the
  canonical-field abstraction shape.
- `HexGfq/Basic.lean` around the existing `GFq.repr_zero` /
  `GFq.repr_one` / `GFq.repr_add` / `GFq.repr_mul` block (lines ~259–282).
- `HexGfqField/Operations.lean` `GFqField.repr_pow` (line ~791) for the
  underlying `rfl`-shaped lemma being lifted.
- Related closed issues:
  - #5246 (`GFq.repr_add` and `GFq.repr_mul`).
  - #5250 / PR #5272 (`GFq.repr_neg` and `GFq.repr_sub`, in flight).

## Verification

- `lake build HexGfq.Basic`
- `lake build HexGfq`
- `lake build`
- `python3 scripts/check_dag.py`
- `git diff --check`
- `git grep -nE '^@\[simp\] theorem repr_pow\b' HexGfq/Basic.lean` finds the
  new declaration inside namespace `Hex.GFq`.
- `git diff -- HexGfq/Basic.lean | rg -nE '^\+.*(sorry|axiom|native_decide|TODO|FIXME)'`
  is empty.

## Out of scope

- `GF2q.repr_pow`; the packed `p = 2` namespace has a different underlying
  representation and gets its own issue.
- `GFq.repr_inv_of_ne_zero`, `repr_div`, `repr_zpow`, `repr_natCast`,
  `repr_intCast`, `repr_nsmul`, `repr_zsmul`, `repr_frob`. Each is a separate
  atomic wrapper that mirrors a distinct underlying `GFqField` lemma.
- Editing `SPEC/`, top-level `PLAN.md`, or top-level `.claude/CLAUDE.md`.

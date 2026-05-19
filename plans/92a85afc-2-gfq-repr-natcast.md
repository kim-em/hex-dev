## Current state

`HexGfq/Basic.lean` exposes the Conway-specialized convenience type `GFq p n h`
as an `abbrev` for `GFqField.FiniteField (Conway.conwayPoly p n h) ...`. The
namespace currently carries the representative simp wrappers for the basic
ring constructors `GFq.repr_zero`, `GFq.repr_one`, `GFq.repr_add`,
`GFq.repr_mul`. The negation and subtraction wrappers `GFq.repr_neg` and
`GFq.repr_sub` are in flight via PR #5272.

The underlying generic `GFqField.FiniteField` API in
`HexGfqField/Operations.lean` exposes `repr_natCast`:

```lean
@[simp] theorem GFqField.repr_natCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p)
    (hirr : FpPoly.Irreducible f) (n : Nat) :
    repr (n : FiniteField f hf hp hirr) =
      GFqRing.reduceMod f (FpPoly.C (n : ZMod64 p)) :=
  rfl
```

`GFq` does not yet expose the analogous `repr_natCast` wrapper. The simp
chain `repr_eq_field_repr` then `GFqField.repr_natCast` reaches the same
normal form indirectly, but a direct wrapper named in the `Hex.GFq` namespace
matches the existing `GFq.repr_zero`/`one`/`add`/`mul` block and keeps the
canonical-field constructor surface uniform across `Nat`-literal inputs and
the basic ring constructors.

## Deliverables

1. Extend namespace `Hex.GFq` in `HexGfq/Basic.lean`, immediately after the
   existing `@[simp] theorem repr_mul` declaration (or after `repr_sub` once
   #5272 lands), with:

   ```lean
   /-- The canonical representative of a natural literal in `GFq` is the
   reduction modulo the selected Conway polynomial of the constant
   polynomial carrying the literal as a `ZMod64` coefficient. -/
   @[simp] theorem repr_natCast (h : Conway.SupportedEntry p n) (k : Nat) :
       repr ((k : GFq p n h)) =
         GFqRing.reduceMod (modulus h) (FpPoly.C (k : ZMod64 p)) :=
     rfl
   ```

2. Proof shape: `rfl`, matching the underlying `GFqField.repr_natCast`. No
   unfolding of Conway-table machinery or non-`rfl` reasoning.

3. If `GFq.repr_neg` / `GFq.repr_sub` (PR #5272) have already landed at the
   time this is implemented, insert the new declaration after them so the
   namespace order is `_zero, _one, _add, _mul, _neg, _sub, _natCast`. If
   not, insert after `_mul` and keep the same convention.

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
- **Is this result already in Mathlib?** No analog. The closed-form RHS is
  the constant `FpPoly.C ((k : ZMod64 p))` reduced via `GFqRing.reduceMod`.
- **Does the deliverable presuppose missing infrastructure?** No.
  `GFqField.repr_natCast`, `NatCast (FiniteField …)`, `FpPoly.C`, and
  `GFqRing.reduceMod` already exist.

## Context

- `PLAN/Phase6.md` (proof polishing rules).
- `SPEC/Libraries/hex-gfq.md` and `SPEC/Libraries/hex-gfq-field.md` for the
  canonical-field abstraction shape.
- `HexGfq/Basic.lean` around the existing `GFq.repr_zero` /
  `GFq.repr_one` / `GFq.repr_add` / `GFq.repr_mul` block (lines ~259–282).
- `HexGfqField/Operations.lean` `GFqField.repr_natCast` (line ~554) for the
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
- `git grep -nE '^@\[simp\] theorem repr_natCast\b' HexGfq/Basic.lean` finds
  the new declaration inside namespace `Hex.GFq`.
- `git diff -- HexGfq/Basic.lean | rg -nE '^\+.*(sorry|axiom|native_decide|TODO|FIXME)'`
  is empty.

## Out of scope

- `GFq.repr_intCast`; the integer-literal wrapper is a separate atomic
  follow-up.
- `GFq.repr_pow`, `repr_inv_of_ne_zero`, `repr_div`, `repr_zpow`,
  `repr_nsmul`, `repr_zsmul`, `repr_frob`. Each is a separate atomic wrapper.
- `GF2q.repr_natCast`; the packed `p = 2` namespace has a different
  underlying representation and gets its own issue.
- Editing `SPEC/`, top-level `PLAN.md`, or top-level `.claude/CLAUDE.md`.

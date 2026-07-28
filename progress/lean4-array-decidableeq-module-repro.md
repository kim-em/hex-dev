# lean4 bug: `Array.instDecidableEq` does not reduce under the module system (nonempty arrays)

Toolchain: `leanprover/lean4:v4.32.0-rc1` (also present on nightlies through 2026-07-03).

## Minimal repro

```lean
module
example : (#[0, 1] : Array Nat) ≠ #[1] := by decide
```

fails:

```
error: Tactic `decide` failed for proposition
  #[0, 1] ≠ #[1]
because its `Decidable` instance `instDecidableNot` did not reduce to `isTrue` or `isFalse`.
After unfolding the instances `instDecidableNot` and `Array.instDecidableEq`, reduction got
stuck at the `Decidable` instance
  { toList := [0, 1] }.instDecidableEqImpl { toList := [1] }
```

The identical statement **without** `module` succeeds. `decide` also succeeds under
`module` whenever at least one array is empty (`#[] = #[]`, `#[] = #[1]`, `#[0,1] = #[]`),
and for `List` (`[0,1] ≠ [1]`).

## Root cause

In `Init/Data/Array/DecidableEq.lean`:

```lean
def instDecidableEqImpl [DecidableEq α] : DecidableEq (Array α) := fun xs ys =>
  match h : isEqv xs ys (fun a b => a = b) with
  | true  => isTrue (eq_of_isEqv xs ys h)
  | false => isFalse (by subst ·; rw [isEqv_self] at h; contradiction)

instance instDecidableEq [DecidableEq α] : DecidableEq (Array α) := fun xs ys =>
  match xs with
  | ⟨[]⟩ => match ys with | ⟨[]⟩ => isTrue rfl | ⟨_ :: _⟩ => isFalse …
  | ⟨a :: as⟩ => match ys with
    | ⟨[]⟩ => isFalse …
    | ⟨b :: bs⟩ => instDecidableEqImpl ⟨a :: as⟩ ⟨b :: bs⟩   -- delegates to the impl
```

`instDecidableEq` is exposed (`@[implicit_reducible, expose]`) and its empty/empty and
empty/nonempty cases are inlined, so they reduce. The nonempty/nonempty case delegates to
`instDecidableEqImpl`, which is a **plain `def` with no `@[expose]`**. Under the module
system a public non-`@[expose]` `def` exports only its signature, so `instDecidableEqImpl`'s
body is unavailable to the kernel downstream — `#print Array.instDecidableEqImpl` reports
`<not imported>` — and reduction stalls for every pair of nonempty arrays.

## Two further instances of the same defect

Chasing the `Vector` case turned up two more, both with the same shape and neither
fixable from the consumer side.

**Every `deriving DecidableEq` instance.** `Lean.Elab.Deriving.DecEq.mkAuxFunction`
emits the generated `decEq` as a plain `def`, so its body is opaque across a module
boundary. This is not specific to any type:

```lean
-- A.lean
module
public section
structure P where
  x : Nat
deriving DecidableEq

-- B.lean
module
public import A
example : (⟨1⟩ : P) ≠ ⟨2⟩ := by decide   -- stuck at instDecidableEqP.decEq
```

`Vector`'s instance is derived, which is why `Vector` equality stalls even once
`Array` is fixed. There is no workaround: `@[expose]` cannot be attached to a
structure, and `attribute [expose] …` after the fact is rejected ("can only be
added when declaring a `def`").

**`Array.ofFn`.** Delegates to its `ofFn.go` auxiliary, so
`(Array.ofFn f).size = n` does not reduce. `Vector.ofFn` is already `@[expose]`
but calls `Array.ofFn`, so it inherits the stall. Marking `Array.ofFn` itself
`@[expose]` is sufficient, because exposure extends to a definition's `where`
bindings; `@[expose]` directly on the `where` binding is rejected.

## Fix

All three are fixed by
[leanprover/lean4#14270](https://github.com/leanprover/lean4/pull/14270):
`@[expose]` on `Array.instDecidableEqImpl` (plus `isEqv` / `isEqvAux`), on the
`decEq` emitted by the deriving handler, and on `Array.ofFn`.

## Consumer-side workarounds (no toolchain change)

- `HexBasic.ArrayDecEq` provides higher-priority `DecidableEq` instances for
  `Array` and `Vector` that route through the fully exposed `List` equality.
  This is what the tree uses now; `public import HexBasic.ArrayDecEq` in any
  module that needs to `decide` such an equality.
- `import all Init.Data.Array.DecidableEq` also works for the `Array` case, and
  was what the tree used previously.
- Route a wrapper type's `DecidableEq` through `List` instead of `Array`, e.g.
  `decidable_of_iff (a.toList = b.toList) …`. This is what `HexPoly.Dense`'s
  `DecidableEq (DensePoly R)` does, and it has to stay local there because
  `hex-poly` has no dependencies and therefore cannot import `HexBasic`.
- `HexBasic.OfFn` provides `Hex.Array.ofFn'` and `Hex.Vector.ofFn'`, which go
  through the fully exposed `List.ofFn` and do reduce. They are proved equal to
  the core versions (`ofFn'_eq_ofFn`), so the swap back is a rewrite.

## Cleanup once #14270 lands

After the toolchain is bumped past the fix:

1. Delete `HexBasic/ArrayDecEq.lean` and `HexBasic/OfFn.lean`, and their entries
   in `HexBasic.lean`.
2. Remove the `public import HexBasic.ArrayDecEq` line and its two-line comment
   from every module that carries it (`grep -rl HexBasic.ArrayDecEq`), and
   replace every `Array.ofFn'` / `Vector.ofFn'` use with the core version
   (`grep -rl "ofFn'"`); `ofFn'_eq_ofFn` makes that a rewrite.
3. Replace `HexPoly.Dense`'s hand-written `DecidableEq (DensePoly R)` with the
   ordinary `Array`-based comparison, and drop the explanatory comment.
4. Reconsider `HexPoly.Euclid.leadingCoeff`, which avoids `Array.back?` for the
   related reason below, and any code that avoids `Array.ofFn` for kernel
   reasons.
5. Re-run the kernel-facing conformance and bench targets, since the point of
   all of this is reduction behaviour rather than elaboration.

## Related

The sibling `Array.back?` non-reduction under `module` (worked around in
`HexPoly.Euclid.leadingCoeff` by using `coeffs.getD (size - 1)` instead of
`coeffs.back?.getD 0`) is the same class of issue: a core `Array` helper whose body is not
available to the kernel downstream under the module system.

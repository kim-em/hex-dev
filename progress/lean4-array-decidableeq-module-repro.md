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

Chasing the `Vector` case turned up two more, both with the same shape.

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
`Array` is fixed. The generated `decEq` cannot be exposed retrospectively:
`@[expose]` cannot be attached to a structure, and `attribute [expose] …` after
the fact is rejected ("can only be added when declaring a `def`"). A consumer
can still supply a replacement instance, which is what `HexBasic.ArrayDecEq`
does.

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

## Audit: existing `Array.ofFn` / `Vector.ofFn` call sites

Done 2026-07-28, to decide whether the tree should adopt `ofFn'` ahead of the
upstream fix. **Conclusion: no, apart from any site with a demonstrated kernel
need.** Recorded so it is not re-litigated from scratch.

**Scale.** 297 raw occurrences across 48 files, but only about 100 sit in
`def` / `abbrev` / `instance` bodies, which is the only position where kernel
reduction is affected; the other ~200 are theorem statements. Of the ~100, 93
are in libraries that already reach `hex-basic` and could adopt `ofFn'` with no
dependency change. `hex-poly` accounts for 13 and cannot, having no
dependencies.

**The defect is real, not hypothetical.** `Hex.Vector.unit` in `HexMatrix.Basic`
is `@[expose]`, is built with core `Vector.ofFn`, and does not reduce from a
downstream module:

```lean
module
public import HexMatrix.Basic
public import HexBasic.ArrayDecEq
open scoped Hex
example : (Vector.unit Nat (n := 3) 1) = #v[0, 1, 0] := by decide +kernel
-- reduction gets stuck; passes after switching that one definition to `ofFn'`
```

`hex-matrix` is a released library, so this ships.

**Why a blanket migration still fails.** Rewriting all 62 mechanically
reachable sites produced 29 build errors in three distinct classes:

1. **Not every file is a module file.** `HexGF2Mathlib/Basic.lean` uses plain
   `import`, so `public import` is a syntax error there and the exposure
   question does not arise at all.
2. **`ofFn'` is not definitionally equal to `ofFn`.** `HexMatrix/Basic.lean`
   proofs that closed by `rfl` after `simp only [..., Vector.getElem_ofFn, ...]`
   stop working, because the core simp lemma no longer matches.
3. **The shim has no lemma ecosystem.** Core's `Vector.getElem_ofFn`,
   `size_ofFn`, and friends are stated about `ofFn`; `ofFn'` has only
   `ofFn'_eq_ofFn`. Anything reasoning about a migrated definition needs that
   rewrite inserted by hand, which is the type-mismatch class in
   `HexRealRootsMathlib/IsolateRoots.lean`.

So each migrated site costs local proof churn proportional to how much its
callers reason about the array's contents. That is affordable for a definition
with a real kernel consumer and pure waste otherwise.

**Recommendation.** Fix it upstream and leave the tree alone. Migrate an
individual definition only when something concretely needs it to reduce, and
expect to repair its lemma uses at the same time. Do not migrate `*Impl`
definitions, which are runtime implementations behind `@[csimp]` where core
`ofFn` is correct.

## Cleanup once #14270 lands

After the toolchain is bumped past the fix:

Record the first toolchain containing the fix, then, **in this order** (call
sites before deletions, so nothing is briefly unbuildable):

1. Re-point `HexBasic/ModuleBoundaryTests.lean` at the core definitions
   (`Array.ofFn`, `Vector.ofFn`, and core equality) and confirm it still
   passes. This is the check that the upstream fix actually landed; do not
   skip it.
2. Replace Lean call sites:
   `rg -l "ofFn'" --glob '*.lean'` and rewrite each to the core version;
   `ofFn'_eq_ofFn` makes that a rewrite rather than a reproof.
3. Remove the `public import HexBasic.ArrayDecEq` line and its two-line
   comment from every module carrying it:
   `rg -l "HexBasic.ArrayDecEq" --glob '*.lean'`.
4. Replace `HexPoly.Dense`'s hand-written `DecidableEq (DensePoly R)` with
   `fun a b => decEq a.coeffs b.coeffs` lifted through proof irrelevance on the
   `normalized` field, and drop its explanatory comment. Update the
   `beqCoeffs` docstring, which describes the pre-workaround behaviour.
5. Delete `HexBasic/ArrayDecEq.lean`, `HexBasic/OfFn.lean`, and
   `HexBasic/ModuleBoundaryTests.lean`, and their entries in `HexBasic.lean`.
6. Assert the cleanup is complete: `rg "ofFn'|HexBasic.ArrayDecEq" --glob
   '*.lean'` must return nothing.
7. Run a full `lake build` plus the kernel-facing conformance and bench
   targets, since the point of all of this is reduction behaviour rather than
   elaboration.

`HexPoly.Euclid.leadingCoeff` avoids `Array.back?`, which is a related
exposure gap but is **not** fixed by #14270. Leave it alone; it needs its own
upstream change.

## Related

The sibling `Array.back?` non-reduction under `module` (worked around in
`HexPoly.Euclid.leadingCoeff` by using `coeffs.getD (size - 1)` instead of
`coeffs.back?.getD 0`) is the same class of issue: a core `Array` helper whose body is not
available to the kernel downstream under the module system.

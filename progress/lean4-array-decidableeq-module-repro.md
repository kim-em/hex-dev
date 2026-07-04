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

## Proposed fix

Add `@[expose]` to `Array.instDecidableEqImpl` (and verify its reduction closure,
`Array.isEqv` / `Array.isEqvAux`, is likewise exposed). That restores kernel reduction of
`decide`/`rfl` over `Array` equality under `module`.

## Consumer-side workarounds (no toolchain change)

- `import all Init.Data.Array.DecidableEq` in the module performing the `decide` — pulls the
  impl body in and reduces (verified).
- Route a wrapper type's `DecidableEq` through `List` instead of `Array`, e.g.
  `decidable_of_iff (a.toList = b.toList) …`; `List.instDecidableEq` is fully exposed.
  (This is what `HexPoly.Dense`'s `DecidableEq (DensePoly R)` now does.)

## Related

The sibling `Array.back?` non-reduction under `module` (worked around in
`HexPoly.Euclid.leadingCoeff` by using `coeffs.getD (size - 1)` instead of
`coeffs.back?.getD 0`) is the same class of issue: a core `Array` helper whose body is not
available to the kernel downstream under the module system.

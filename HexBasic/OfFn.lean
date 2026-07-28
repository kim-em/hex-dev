/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std

public section

/-!
Kernel-reducible `ofFn` for `Array` and `Vector`.

`Array.ofFn` delegates to its `ofFn.go` auxiliary, which is not exposed, so
under the module system its body is unavailable downstream and
`(Array.ofFn f)` does not reduce in the kernel. `Vector.ofFn` is itself
`@[expose]` but calls `Array.ofFn`, so it inherits the stall.

`List.ofFn` is fully exposed and reduces, so the definitions below go through
it. That is the wrong shape for compiled code, which wants to push into an
array of known capacity rather than build a linked list and convert, so each
carries a `@[csimp]` lemma redirecting the compiler back to the core version.
The `List` route is then paid only in the kernel, which is where it is needed.

**Delete this file** once
[leanprover/lean4#14270](https://github.com/leanprover/lean4/pull/14270) lands
and the toolchain is bumped past it, replacing uses with `Array.ofFn` and
`Vector.ofFn`. See `progress/lean4-array-decidableeq-module-repro.md` for the
full cleanup checklist.
-/

namespace Hex

/-- `Array.ofFn` that reduces in the kernel under the module system. -/
@[expose] def Array.ofFn' {α : Type u} {n : Nat} (f : Fin n → α) : Array α :=
  (List.ofFn f).toArray

/-- `Vector.ofFn` that reduces in the kernel under the module system. -/
@[expose] def Vector.ofFn' {n : Nat} {α : Type u} (f : Fin n → α) : Vector α n :=
  ⟨(List.ofFn f).toArray, by simp⟩

@[simp] theorem Array.ofFn'_eq_ofFn {α : Type u} {n : Nat} (f : Fin n → α) :
    Array.ofFn' f = Array.ofFn f := by
  simp [Array.ofFn']

@[simp] theorem Vector.ofFn'_eq_ofFn {n : Nat} {α : Type u} (f : Fin n → α) :
    Vector.ofFn' f = Vector.ofFn f := by
  simp [Vector.ofFn', _root_.Vector.ofFn]

/-! ## Compatibility lemmas

Core's lemmas (`Array.size_ofFn`, `Vector.getElem_ofFn`, …) are stated about
`ofFn` and do not apply to `ofFn'`. `ofFn'_eq_ofFn` is `@[simp]`, so ordinary
`simp` bridges the gap on its own; these exist so that `simp only` proofs and
`rfl`-closing steps keep working after a definition is migrated, without having
to thread the equality in by hand. -/

@[simp] theorem Array.size_ofFn' {α : Type u} {n : Nat} (f : Fin n → α) :
    (Array.ofFn' f).size = n := by
  simp [Array.ofFn']

@[simp] theorem Array.getElem_ofFn' {α : Type u} {n : Nat} (f : Fin n → α) (i : Nat)
    (h : i < (Array.ofFn' f).size) :
    (Array.ofFn' f)[i] = f ⟨i, by simpa using h⟩ := by
  simp [Array.ofFn']

@[simp] theorem Vector.toArray_ofFn' {n : Nat} {α : Type u} (f : Fin n → α) :
    (Vector.ofFn' f).toArray = Array.ofFn' f := rfl

@[simp] theorem Vector.getElem_ofFn' {n : Nat} {α : Type u} (f : Fin n → α) (i : Nat)
    (h : i < n) : (Vector.ofFn' f)[i] = f ⟨i, h⟩ := by
  simp [Vector.ofFn']

/-- Compiled code uses the core `Array.ofFn`, which fills an array of known
capacity instead of building a `List` first. The `List` route exists only so
that the kernel can reduce it. -/
@[csimp] theorem Array.ofFn'_eq_ofFn' : @Array.ofFn' = @_root_.Array.ofFn := by
  funext α n f; exact Array.ofFn'_eq_ofFn f

/-- As `Array.ofFn'_eq_ofFn'`. -/
@[csimp] theorem Vector.ofFn'_eq_ofFn' : @Vector.ofFn' = @_root_.Vector.ofFn := by
  funext n α f; exact Vector.ofFn'_eq_ofFn f

end Hex

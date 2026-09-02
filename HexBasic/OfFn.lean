/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std

public section

/-!
Kernel-reducible function tabulation for {name}`Array` and {name}`Vector`.

{name}`Array.ofFn` delegates to its `ofFn.go` auxiliary, which is not exposed, so
under the module system its body is unavailable downstream and
`(Array.ofFn f)` does not reduce in the kernel. {name}`Vector.ofFn` is itself
`@[expose]` but calls {name}`Array.ofFn`, so it inherits the stall.

{name}`List.ofFn` is fully exposed and reduces, so the definitions below go through
it. That is the wrong shape for compiled code, which wants to push into an
array of known capacity rather than build a linked list and convert, so each
carries a `@[csimp]` lemma redirecting the compiler back to the core version.
The {name}`List` route is then paid only in the kernel, which is where it is
needed.
-/

namespace Hex

/-- An {name}`Array.ofFn` equivalent that reduces in the kernel under the
module system. -/
@[expose] def Array.ofFn' {α : Type u} {n : Nat} (f : Fin n → α) : Array α :=
  (List.ofFn f).toArray

/-- A {name}`Vector.ofFn` equivalent that reduces in the kernel under the
module system. -/
@[expose] def Vector.ofFn' {n : Nat} {α : Type u} (f : Fin n → α) : Vector α n :=
  ⟨(List.ofFn f).toArray, by simp⟩

@[simp] theorem Array.ofFn'_eq_ofFn {α : Type u} {n : Nat} (f : Fin n → α) :
    Array.ofFn' f = Array.ofFn f := by
  simp [Array.ofFn']

@[simp] theorem Vector.ofFn'_eq_ofFn {n : Nat} {α : Type u} (f : Fin n → α) :
    Vector.ofFn' f = Vector.ofFn f := by
  simp [Vector.ofFn', _root_.Vector.ofFn]

/-! # Compatibility lemmas

Core's lemmas ({name}`Array.size_ofFn`, {name}`Vector.getElem_ofFn`, …) are
stated about {name}`Array.ofFn` and {name}`Vector.ofFn` and do not apply
directly to {name}`Hex.Array.ofFn'` or {name}`Hex.Vector.ofFn'`.
{name}`Hex.Array.ofFn'_eq_ofFn` is `@[simp]`, so ordinary `simp` bridges the
gap; these lemmas also support `simp only` proofs and `rfl`-closing steps. -/

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

/-- Compiled code uses the core {name}`Array.ofFn`, which fills an array of known
capacity instead of building a {name}`List` first. The {name}`List` route exists
only so that the kernel can reduce it. -/
@[csimp] theorem Array.ofFn'_eq_ofFn' : @Array.ofFn' = @_root_.Array.ofFn := by
  funext α n f; exact Array.ofFn'_eq_ofFn f

/-- The {name}`Hex.Vector.ofFn'` analogue of
{name}`Hex.Array.ofFn'_eq_ofFn'`. -/
@[csimp] theorem Vector.ofFn'_eq_ofFn' : @Vector.ofFn' = @_root_.Vector.ofFn := by
  funext n α f; exact Vector.ofFn'_eq_ofFn f

/-! # `Array.map` -/

/-- An {name}`Array.map` equivalent that reduces in the kernel under the
module system: core {name}`Array.map`'s implementation loop is not exposed,
so `(a.map f)` stalls downstream exactly like {name}`Array.ofFn`. -/
@[expose] def Array.map' {α : Type u} {β : Type v} (f : α → β)
    (a : Array α) : Array β :=
  (a.toList.map f).toArray

@[simp] theorem Array.map'_eq_map {α : Type u} {β : Type v} (f : α → β)
    (a : Array α) : Array.map' f a = a.map f := by
  rw [Array.map', ← Array.toList_map, Array.toArray_toList]

@[simp] theorem Array.size_map' {α : Type u} {β : Type v} (f : α → β)
    (a : Array α) : (Array.map' f a).size = a.size := by
  simp [Array.map']

@[simp] theorem Array.getElem_map' {α : Type u} {β : Type v} (f : α → β)
    (a : Array α) (i : Nat) (h : i < (Array.map' f a).size) :
    (Array.map' f a)[i] = f (a[i]'(by simpa using h)) := by
  simp [Array.map']

/-- Compiled code uses the core {name}`Array.map`, which writes into an
array in place when uniquely referenced; the {name}`List` route exists only
so that the kernel can reduce it. -/
@[csimp] theorem Array.map'_eq_map' : @Array.map' = @_root_.Array.map := by
  funext α β f a; exact Array.map'_eq_map f a

end Hex

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
it. They are otherwise defeq to the core versions.

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
@[expose] def Vector.ofFn' {α : Type u} {n : Nat} (f : Fin n → α) : Vector α n :=
  ⟨(List.ofFn f).toArray, by simp⟩

@[simp] theorem Array.ofFn'_eq_ofFn {α : Type u} {n : Nat} (f : Fin n → α) :
    Array.ofFn' f = Array.ofFn f := by
  simp [Array.ofFn']

@[simp] theorem Vector.ofFn'_eq_ofFn {α : Type u} {n : Nat} (f : Fin n → α) :
    Vector.ofFn' f = Vector.ofFn f := by
  simp [Vector.ofFn', _root_.Vector.ofFn]

end Hex

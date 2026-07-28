/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std

public section

/-!
Kernel-reducible `DecidableEq` for `Array` and `Vector`.

Three exposure gaps in core stop `decide` / `rfl` reducing over these types
across a module boundary. In each case an exposed definition delegates to a
plain `def` whose body is unavailable downstream, so reduction stalls:

* `Array.instDecidableEq` delegates its nonempty/nonempty case to
  `Array.instDecidableEqImpl`;
* every `deriving DecidableEq` instance delegates to a generated `decEq`,
  which is how `Vector` gets its instance;
* `Array.ofFn` delegates to its `ofFn.go` auxiliary.

The instances below route through `List` equality, which is fully exposed, and
take priority over the core ones.

**Delete this file** once
[leanprover/lean4#14270](https://github.com/leanprover/lean4/pull/14270) lands
and the toolchain is bumped past it. The `Array.ofFn` gap is fixed there too,
and has no workaround here: a definition built with `Array.ofFn` or
`Vector.ofFn` still will not reduce, so kernel-facing code must build its arrays
another way until then.
-/

namespace Hex

/-- `DecidableEq (Array α)` that reduces in the kernel under the module system,
routing through the fully exposed `List` equality. -/
instance (priority := 1100) instDecidableEqArray
    {α : Type u} [DecidableEq α] : DecidableEq (Array α) := fun a b =>
  match h : decEq a.toList b.toList with
  | isTrue ht => isTrue (by cases a; cases b; exact congrArg Array.mk ht)
  | isFalse hf => isFalse (by intro hab; exact hf (congrArg Array.toList hab))

/-- `DecidableEq (Vector α n)` that reduces in the kernel under the module
system. `Vector`'s core instance is derived, and derived instances are opaque
across a module boundary. -/
instance (priority := 1100) instDecidableEqVector
    {α : Type u} {n : Nat} [DecidableEq α] : DecidableEq (Vector α n) := fun a b =>
  match h : decEq a.toArray.toList b.toArray.toList with
  | isTrue ht => isTrue (by
      cases a with | mk ba ha => cases b with | mk bb hb =>
      have hba : ba = bb := by cases ba; cases bb; exact congrArg Array.mk ht
      subst hba; rfl)
  | isFalse hf => isFalse (by intro hab; subst hab; exact hf rfl)

end Hex

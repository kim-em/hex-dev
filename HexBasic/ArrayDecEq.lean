/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std

public section

/-!
Kernel-reducible {name}`DecidableEq` instances for {name}`Array` and
{name}`Vector`.

Three exposure gaps in core stop `decide` / `rfl` reducing over these types
across a module boundary. In each case an exposed definition delegates to a
plain `def` whose body is unavailable downstream, so reduction stalls:

* {name}`Array.instDecidableEq` delegates its nonempty/nonempty case to
  {name}`Array.instDecidableEqImpl`;
* every `deriving DecidableEq` instance delegates to a generated `decEq`,
  which is how {name}`Vector` gets its instance;
* {name}`Array.ofFn` delegates to its `ofFn.go` auxiliary.

The instances below route through {name}`List` equality, which is fully exposed, and
take priority over the core ones. They are `scoped`, so they apply only inside
`namespace Hex` or after `open scoped Hex`, and never leak into the released
libraries that depend on `hex-basic` or into their consumers. A module that
forgets to activate them gets a stuck `decide`, which is loud. {name}`List` is
the wrong shape for compiled code, where {name}`Array.toList` is an `O(n)`
conversion that allocates both lists in full
before comparison begins and gives up early exit, so each carries a `@[csimp]`
redirect back to the core instance. The `List` route is then paid only in the
kernel, which is where it is needed.
-/

namespace Hex

/-- `DecidableEq (Array α)` that reduces in the kernel under the module system,
routing through the fully exposed `List` equality. -/
scoped instance (priority := 1100) instDecidableEqArray
    {α : Type u} [DecidableEq α] : DecidableEq (Array α) := fun a b =>
  match h : decEq a.toList b.toList with
  | isTrue ht => isTrue (by cases a; cases b; exact congrArg Array.mk ht)
  | isFalse hf => isFalse (by intro hab; exact hf (congrArg Array.toList hab))

/-- `DecidableEq (Vector α n)` that reduces in the kernel under the module
system. `Vector`'s core instance is derived, and derived instances are opaque
across a module boundary. -/
scoped instance (priority := 1100) instDecidableEqVector
    {α : Type u} {n : Nat} [DecidableEq α] : DecidableEq (Vector α n) := fun a b =>
  match h : decEq a.toArray.toList b.toArray.toList with
  | isTrue ht => isTrue (by
      cases a with | mk ba ha => cases b with | mk bb hb =>
      have hba : ba = bb := by cases ba; cases bb; exact congrArg Array.mk ht
      subst hba; rfl)
  | isFalse hf => isFalse (by intro hab; subst hab; exact hf rfl)

/-- Compiled code uses the core {name}`Array` decider, which compares in place. The
{name}`List` route exists only so that the kernel can reduce it.
{name}`DecidableEq` is a
subsingleton, so the two agree. -/
@[csimp] theorem instDecidableEqArray_eq :
    @instDecidableEqArray = @_root_.Array.instDecidableEq := by
  funext α _ a b; exact Subsingleton.elim _ _

/-- The {name}`Hex.instDecidableEqVector` analogue of
{name}`Hex.instDecidableEqArray_eq`. -/
@[csimp] theorem instDecidableEqVector_eq :
    @instDecidableEqVector = @_root_.instDecidableEqVector := by
  funext α n _ a b; exact Subsingleton.elim _ _

end Hex

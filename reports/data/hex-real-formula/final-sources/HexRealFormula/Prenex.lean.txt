/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealFormula.Kernel

@[expose] public section

/-! Prefix views and checked permutations of adjacent equal quantifiers. -/

namespace Hex.RealFormula

/-- A serialized prefix and a matrix whose arity includes the whole prefix. -/
structure Prenex.View (n : Nat) where
  «prefix» : List Quantifier
  matrix : QF (n + prefix.length)
  deriving DecidableEq, BEq

/-- Prepend one quantifier, confining arity transport to the list view. -/
def Prenex.View.cons (q : Quantifier) (v : Prenex.View (n + 1)) : Prenex.View n :=
  ⟨q :: v.prefix, (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using v.matrix)⟩

/-- Flatten a prefix, preserving outermost-to-innermost coordinate order. -/
def Prenex.toView : Prenex n → Prenex.View n
  | .matrix p => ⟨[], p⟩
  | .quant q p => p.toView.cons q

/-- Reconstruct structural binding from a checked prefix view. -/
def Prenex.ofPrefix : (qs : List Quantifier) → QF (n + qs.length) → Prenex n
  | [], p => .matrix p
  | q :: qs, p => .quant q (ofPrefix qs (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using p))

/-- Interpret a checked prefix view as inductive syntax. -/
def Prenex.ofView (v : Prenex.View n) : Prenex n := ofPrefix v.prefix v.matrix

/-- The list view transports coordinates without changing the formula. -/
theorem Prenex.ofView_toView (p : Prenex n) : ofView p.toView = p := by
  induction p with
  | matrix p => rfl
  | quant q p ih => simpa [ofView, toView, View.cons, ofPrefix] using congrArg (quant q) ih

/-- Every well-typed prefix view is recovered by structural reconstruction. -/
theorem Prenex.toView_ofPrefix (qs : List Quantifier) (p : QF (n + qs.length)) :
    (ofPrefix qs p).toView = ⟨qs, p⟩ := by
  induction qs generalizing n with
  | nil => rfl
  | cons q qs ih =>
    simp only [ofPrefix, toView, ih]
    simp [View.cons]

/-- Swap the final two coordinates, fixing all earlier parameters. -/
def swapLast (i : Fin (n + 1 + 1)) : Fin (n + 1 + 1) :=
  if i.val = n then ⟨n + 1, by omega⟩
  else if i.val = n + 1 then ⟨n, by omega⟩ else i

/-- Only two adjacent quantifiers of the same kind may be commuted.
The remaining prefix renames the exchanged coordinates and fixes later binders. -/
def Prenex.swap? (depth : Nat) : Prenex n → Option (Prenex n)
  | .matrix _ => none
  | .quant q p => match depth with
    | 0 => match p with
      | .matrix _ => none
      | .quant r p => if q == r then
          some (.quant r (.quant q (p.rename swapLast))) else none
    | k + 1 => return .quant q (← p.swap? k)

/-- Serialized prenex data uses the matrix's explicit total arity. -/
structure Kernel.Prenex where
  version : Nat := 1
  freeArity : Nat
  «prefix» : List Quantifier
  matrix : Kernel.QF
  deriving DecidableEq, BEq, Repr

/-- Encode the matrix and its total arity with the ordered prefix. -/
def Prenex.toKernel (p : Prenex n) : Kernel.Prenex :=
  let v := p.toView
  ⟨1, n, v.prefix, v.matrix.toKernel⟩

/-- Check the free and total arities before interpreting the prefix. -/
def Prenex.ofKernel? (p : Kernel.Prenex) : Option (Prenex n) := do
  if p.version != 1 || p.freeArity != n then none else do
    let matrix : QF (n + p.prefix.length) ← QF.ofKernel? p.matrix
    return ofView ⟨p.prefix, matrix⟩

/-- The checked prenex wire format is a structural round trip. -/
theorem Prenex.ofKernel_toKernel (p : Prenex n) : ofKernel? p.toKernel = some p := by
  simp [ofKernel?, toKernel, QF.ofKernel_toKernel, ← ofView_toView p, ofView]

end Hex.RealFormula

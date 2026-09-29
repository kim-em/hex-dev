/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootOrder
public import HexRealClosure.ZeroFactor
public import HexRealClosure.Yun

public section

namespace Hex.RealClosure.Roots

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [Div E]
variable [DecidableEq Ctx]

/-- One selected output value with its original positive multiplicity. -/
structure Entry (sign : E → Int) (context : Ctx) where
  root : Isolation.Root sign context
  multiplicity : Nat
  positive : 0 < multiplicity

/-- Intermediate root assembly. The zero polynomial retains its separate
all-roots case, without attaching finite multiplicities. Strict order and
producer success remain separate proof obligations. -/
inductive Output (sign : E → Int) (context : Ctx) where
  | all
  | finite (entries : List (Entry sign context))

/-- Complete each actual Yun factor and attach its emitted label. An absent
factor domain or a zero label is an internal error, never an empty result. -/
@[expose] def factorEntries (sign : E → Int) (context : Ctx) :
    List (DensePoly E × Nat) → Except SignDet.BuildError (List (Entry sign context))
  | [] => .ok []
  | (factor, label) :: rest =>
    if positive : 0 < label then
      match Isolation.complete? sign context factor with
      | .error error => .error error
      | .ok none => .error .system
      | .ok (some completion) =>
        match factorEntries sign context rest with
        | .error error => .error error
        | .ok entries => .ok
            (completion.roots.entries.map (fun root => ⟨root, label, positive⟩) ++ entries)
    else .error .system

/-- Successful recursion retains the actual completion of the first factor
and the actual result of completing every remaining factor. -/
theorem factorEntries_cons {sign : E → Int} {context : Ctx}
    {factor : DensePoly E} {label : Nat} {rest : List (DensePoly E × Nat)}
    {out : List (Entry sign context)}
    (accepted : factorEntries sign context ((factor, label) :: rest) = .ok out) :
    ∃ positive : 0 < label, ∃ completion : Isolation.Completion sign context factor,
      ∃ entries, Isolation.complete? sign context factor = .ok (some completion) ∧
        factorEntries sign context rest = .ok entries ∧
        out = completion.roots.entries.map (fun root => ⟨root, label, positive⟩) ++ entries := by
  by_cases positive : 0 < label
  · cases produced : Isolation.complete? sign context factor with
    | error error => simp [factorEntries, positive, produced] at accepted
    | ok result =>
      cases result with
      | none => simp [factorEntries, positive, produced] at accepted
      | some completion =>
        cases remaining : factorEntries sign context rest with
        | error error => simp [factorEntries, positive, produced, remaining] at accepted
        | ok entries =>
          exact ⟨positive, completion, entries, rfl, rfl, by
            simpa [factorEntries, positive, produced, remaining] using accepted.symm⟩
  · simp [factorEntries, positive] at accepted

/-- Execute zero extraction, the raw Yun recurrence and every actual factor
completion. The extracted zero is restored once with its original label.
This intermediate result retains diagnostics and is not globally ordered. -/
@[expose] def assemble (sign : E → Int) (context : Ctx) (p : DensePoly E) :
    Except SignDet.BuildError (Output sign context) :=
  if p.isZero then .ok .all
  else
    let removed := ZeroFactor.remove p
    match Yun.decomposeRaw removed.1 with
    | .zero => .error .system
    | .factors _ factors =>
      match factorEntries sign context factors.toList with
      | .error error => .error error
      | .ok entries =>
        if positive : 0 < removed.2 then
          .ok (.finite (⟨.point 0, removed.2, positive⟩ :: entries))
        else .ok (.finite entries)

end Hex.RealClosure.Roots

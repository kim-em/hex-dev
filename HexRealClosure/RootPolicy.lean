/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.IsolationPolicy
public import HexRealClosure.CompleteRoots
public import HexRealClosure.ZeroFactor
public import HexRealClosure.Yun

public section

namespace Hex.RealClosure.Roots.Policy

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]
variable [DecidableEq Ctx]

/-- Complete each actual Yun factor and attach its emitted label. An absent
factor domain or a zero label is an internal error, never an empty result. -/
@[expose] def factorEntries (policy : Isolation.Policy) (sign : E → Int) (context : Ctx) :
    List (DensePoly E × Nat) → Except SignDet.BuildError (List (Entry sign context))
  | [] => .ok []
  | (factor, label) :: rest =>
    if positive : 0 < label then
      match policy.complete? sign context factor with
      | .error error => .error error
      | .ok none => .error .system
      | .ok (some completion) =>
        match factorEntries policy sign context rest with
        | .error error => .error error
        | .ok entries => .ok
            (completion.entries.map (fun root => ⟨root, label, positive⟩) ++ entries)
    else .error .system

/-- Successful recursion retains the actual completion of the first factor
and the actual result of completing every remaining factor. -/
theorem factorEntries_cons {policy : Isolation.Policy} {sign : E → Int} {context : Ctx}
    {factor : DensePoly E} {label : Nat} {rest : List (DensePoly E × Nat)}
    {out : List (Entry sign context)}
    (accepted : factorEntries policy sign context ((factor, label) :: rest) = .ok out) :
    ∃ positive : 0 < label, ∃ completion : Isolation.Output sign context,
      ∃ entries, policy.complete? sign context factor = .ok (some completion) ∧
        factorEntries policy sign context rest = .ok entries ∧
        out = completion.entries.map (fun root => ⟨root, label, positive⟩) ++ entries := by
  by_cases positive : 0 < label
  · cases produced : policy.complete? sign context factor with
    | error error => simp [factorEntries, positive, produced] at accepted
    | ok result =>
      cases result with
      | none => simp [factorEntries, positive, produced] at accepted
      | some completion =>
        cases remaining : factorEntries policy sign context rest with
        | error error => simp [factorEntries, positive, produced, remaining] at accepted
        | ok entries =>
          exact ⟨positive, completion, entries, rfl, rfl, by
            simpa [factorEntries, positive, produced, remaining] using accepted.symm⟩
  · simp [factorEntries, positive] at accepted

/-- The standard policy executes the original factor completion exactly. -/
theorem factorEntries_standard (sign : E → Int) (context : Ctx)
    (factors : List (DensePoly E × Nat)) :
    factorEntries .standard sign context factors = Roots.factorEntries sign context factors := by
  induction factors with
  | nil => rfl
  | cons factor factors ih =>
    rcases factor with ⟨p, label⟩
    by_cases positive : 0 < label
    · cases produced : Isolation.complete? sign context p with
      | error error => simp [factorEntries, Roots.factorEntries, positive,
          Isolation.Policy.complete?_standard, produced, Except.map]
      | ok result =>
        cases result with
        | none => simp [factorEntries, Roots.factorEntries, positive,
            Isolation.Policy.complete?_standard, produced, Except.map]
        | some completion =>
          simp [factorEntries, Roots.factorEntries, positive,
            Isolation.Policy.complete?_standard, produced, Except.map, ih]
          rfl
    · simp [factorEntries, Roots.factorEntries, positive]

variable [Div E]

/-- Execute zero extraction, the raw Yun recurrence and every actual factor
completion. The extracted zero is restored once with its original label.
This intermediate result retains diagnostics and is not globally ordered. -/
@[expose] def assemble (policy : Isolation.Policy) (sign : E → Int) (context : Ctx) (p : DensePoly E) :
    Except SignDet.BuildError (Output sign context) :=
  if p.isZero then .ok .all
  else
    let removed := ZeroFactor.remove p
    match Yun.decomposeRaw removed.1 with
    | .zero => .error .system
    | .factors _ factors =>
      match factorEntries policy sign context factors.toList with
      | .error error => .error error
      | .ok entries =>
        if positive : 0 < removed.2 then
          .ok (.finite (⟨.point 0, removed.2, positive⟩ :: entries))
        else .ok (.finite entries)

/-- The standard policy retains the original Yun and zero extraction pipeline. -/
theorem assemble_standard (sign : E → Int) (context : Ctx) (p : DensePoly E) :
    assemble .standard sign context p = Roots.assemble sign context p := by
  simp only [assemble, Roots.assemble, factorEntries_standard]
  rfl

/-- Run the selected finite isolation policy for every actual Yun factor,
then sort all emitted entries with their original multiplicities. -/
@[expose] def roots? (policy : Isolation.Policy) (sign : E → Int) (context : Ctx)
    (p : DensePoly E) : Except SignDet.BuildError (Output sign context) :=
  match assemble policy sign context p with
  | .error error => .error error
  | .ok .all => .ok .all
  | .ok (.finite entries) =>
    match Isolation.Root.sortBy Entry.root entries with
    | .error error => .error error
    | .ok sorted => .ok (.finite sorted)

/-- The default diagnostic API is unchanged, including internal errors. -/
theorem roots?_standard (sign : E → Int) (context : Ctx) (p : DensePoly E) :
    roots? .standard sign context p = Roots.roots? sign context p := by
  simp only [roots?, Roots.roots?, assemble_standard]
  rfl

/-- The ordinary complete root operation. The companion proves that the
diagnostic fallback is unreachable under the coefficient interpretation laws. -/
@[expose] def roots (policy : Isolation.Policy) (sign : E → Int) (context : Ctx) (p : DensePoly E) :
    Output sign context :=
  match policy with
  | .standard => Roots.roots sign context p
  | policy =>
    match roots? policy sign context p with
    | .ok output => output
    | .error error =>
      letI : Inhabited (Output sign context) := ⟨.all⟩
      panic! s!"Roots.Policy.roots: internal error {repr error}"

/-- Standard ordinary roots use the original implementation. -/
theorem roots_standard (sign : E → Int) (context : Ctx) (p : DensePoly E) :
    roots .standard sign context p = Roots.roots sign context p := rfl

/-- The total API returns its actual successful checked construction. -/
theorem roots_of_success {policy : Isolation.Policy} {sign : E → Int} {context : Ctx} {p : DensePoly E}
    {output : Output sign context} (built : roots? policy sign context p = .ok output) :
    roots policy sign context p = output := by
  cases policy with
  | standard =>
    exact Roots.roots_of_success (by rwa [roots?_standard] at built)
  | bounded => simp only [roots, built]
  | whole => simp only [roots, built]

/-- A finite checked output retains the exact assembly and entry sort. -/
theorem roots?_finite {policy : Isolation.Policy} {sign : E → Int} {context : Ctx} {p : DensePoly E}
    {out : List (Entry sign context)} (built : roots? policy sign context p = .ok (.finite out)) :
    ∃ entries, assemble policy sign context p = .ok (.finite entries) ∧
      Isolation.Root.sortBy Entry.root entries = .ok out := by
  cases assembled : assemble policy sign context p with
  | error error => simp [roots?, assembled] at built
  | ok output =>
    cases output with
    | all => simp [roots?, assembled] at built
    | finite entries =>
      cases sorted : Isolation.Root.sortBy Entry.root entries with
      | error error => simp [roots?, assembled, sorted] at built
      | ok result =>
        have same : result = out := by simpa [roots?, assembled, sorted] using built
        exact ⟨entries, rfl, same ▸ sorted⟩

/-- Sorting preserves the separate all-roots case exactly. -/
theorem roots?_all (policy : Isolation.Policy) {sign : E → Int} {context : Ctx} (p : DensePoly E) :
    roots? policy sign context p = .ok .all ↔ assemble policy sign context p = .ok .all := by
  cases assembled : assemble policy sign context p with
  | error error => simp [roots?, assembled]
  | ok output =>
    cases output with
    | all => simp [roots?, assembled]
    | finite entries =>
      cases sorted : Isolation.Root.sortBy Entry.root entries <;> simp [roots?, assembled, sorted]

end Hex.RealClosure.Roots.Policy

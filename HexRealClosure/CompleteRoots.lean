/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootFactors

public section

namespace Hex.RealClosure.Roots

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [Div E]
variable [DecidableEq Ctx]

/-- Complete zero extraction and Yun isolation, then order the original
entries without detaching their multiplicities. Internal failures remain
visible at this diagnostic boundary. -/
@[expose] def roots? (sign : E → Int) (context : Ctx) (p : DensePoly E) :
    Except SignDet.BuildError (Output sign context) :=
  match assemble sign context p with
  | .error error => .error error
  | .ok .all => .ok .all
  | .ok (.finite entries) =>
    match Isolation.Root.sortBy Entry.root entries with
    | .error error => .error error
    | .ok sorted => .ok (.finite sorted)

/-- The ordinary complete root operation. The companion proves that the
diagnostic fallback is unreachable under the coefficient interpretation laws. -/
@[expose] def roots (sign : E → Int) (context : Ctx) (p : DensePoly E) :
    Output sign context :=
  match roots? sign context p with
  | .ok output => output
  | .error error =>
    letI : Inhabited (Output sign context) := ⟨.finite []⟩
    panic! s!"Roots.roots: internal error {repr error}"

/-- The total API returns its actual successful checked construction. -/
theorem roots_of_success {sign : E → Int} {context : Ctx} {p : DensePoly E}
    {output : Output sign context} (built : roots? sign context p = .ok output) :
    roots sign context p = output := by simp only [roots, built]

/-- A finite checked output retains the exact assembly and entry sort. -/
theorem roots?_finite {sign : E → Int} {context : Ctx} {p : DensePoly E}
    {out : List (Entry sign context)} (built : roots? sign context p = .ok (.finite out)) :
    ∃ entries, assemble sign context p = .ok (.finite entries) ∧
      Isolation.Root.sortBy Entry.root entries = .ok out := by
  cases assembled : assemble sign context p with
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
theorem roots?_all {sign : E → Int} {context : Ctx} (p : DensePoly E) :
    roots? sign context p = .ok .all ↔ assemble sign context p = .ok .all := by
  cases assembled : assemble sign context p with
  | error error => simp [roots?, assembled]
  | ok output =>
    cases output with
    | all => simp [roots?, assembled]
    | finite entries =>
      cases sorted : Isolation.Root.sortBy Entry.root entries <;> simp [roots?, assembled, sorted]

end Hex.RealClosure.Roots

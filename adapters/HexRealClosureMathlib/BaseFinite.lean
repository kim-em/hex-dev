/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.StagedEvaluation
public import HexRealClosureMathlib.FiniteRead
public import HexRealClosureMathlib.TransportInventory
import all HexRealClosure.BaseContext

public section

namespace Hex.RealClosure.BaseContext

variable {registry : Registry} {B : Type} [Lean.Grind.Field B] [DecidableEq B]
variable {sign : B → Int} {base : Context registry B sign}

local instance : Field B := HexPolyMathlib.fieldOfGrind

/-- The finite interpretation reads the exact stored base coefficient. -/
noncomputable def Context.partialRead (base : Context registry B sign)
    (interpretation : CoefficientMap B ℝ) (a : Element base) : ℝ :=
  interpretation.map a.stored

/-- Membership remains a guard on that exact native coefficient. -/
def Context.partialDomain (base : Context registry B sign)
    (interpretation : CoefficientMap B ℝ) (a : Element base) : Prop :=
  a.stored ∈ interpretation.domain

/-- Pull a finite base interpretation through the native wrapper directly.
No ordered real-closed ambient or tower model is constructed. -/
theorem Context.partialClosed (base : Context registry B sign)
    (interpretation : CoefficientMap B ℝ) :
    Transport.Closed (base.partialRead interpretation) (base.partialDomain interpretation) := by
  refine ⟨interpretation.domain.zero_mem, ?_, ?_, ?_, interpretation.domain.one_mem,
    ?_, interpretation.map_zero, ?_, ?_, ?_, interpretation.map_one, ?_⟩
  · intro a b ha hb
    exact interpretation.domain.add_mem ha hb
  · intro a b ha hb
    exact interpretation.domain.mul_mem ha hb
  · intro a b ha hb
    exact interpretation.domain.sub_mem ha hb
  · intro n
    exact (n : interpretation.domain).property
  · intro a b ha hb
    exact interpretation.map_add ha hb
  · intro a b ha hb
    exact interpretation.map_mul ha hb
  · intro a b ha hb
    exact interpretation.map_sub ha hb
  · intro n
    change interpretation.map (n : B) = (n : ℝ)
    rw [interpretation.map_mem (n : B) (natCast_mem interpretation.domain n)]
    exact map_natCast interpretation.value n

private theorem sign_cast_zero (s : SignType) : (s : Int) = 0 ↔ s = 0 := by
  cases s <;> decide

/-- Construct one ordinary reader for a finite base inventory directly from
its actual provider history. Reached signs reflect zero, and every inherited
provider coefficient keeps its supplied real value. -/
theorem Context.partial_exists (base : Context registry B sign)
    (following : base.chain.Realization registry) (values : List (Element base)) :
    ∃ interpretation : CoefficientMap B ℝ,
      Transport.Inventory.Agreement (base.partialRead interpretation)
        (base.partialDomain interpretation) Element.sign
        (fun x : ℝ => (SignType.sign x : Int)) values ∧
      ∀ a r, following.RealValue a.stored r →
        base.partialDomain interpretation a ∧ base.partialRead interpretation a = r := by
  let original := following.ordered
  let : LinearOrder B := original.order
  let : IsStrictOrderedRing B := original.ordered
  obtain ⟨interpretation, data, real⟩ :=
    following.exists_interpretation (values.map (fun a => a.stored))
  refine ⟨interpretation, ?_, ?_⟩
  · intro a member
    have obtained := data a.stored (List.mem_map.mpr ⟨a, member, rfl⟩)
    refine ⟨obtained.1, obtained.2, ?_⟩
    have read_zero : (SignType.sign (base.partialRead interpretation a) : Int) = 0 ↔
        base.partialRead interpretation a = 0 := by
      rw [sign_cast_zero, sign_eq_zero_iff]
    have native_zero : sign a.stored = 0 ↔ a = 0 := by
      rw [original.sign, sign_cast_zero, sign_eq_zero_iff, Element.stored_eq_zero]
    exact read_zero.symm.trans (obtained.2 ▸ native_zero)
  · intro a r inherited
    exact real a.stored r inherited

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.Context.partialClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Context.partialClosed

/-- info: 'Hex.RealClosure.BaseContext.Context.partial_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Context.partial_exists

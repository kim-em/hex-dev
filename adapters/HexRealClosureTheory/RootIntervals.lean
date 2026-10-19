/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootOrder
public import HexRealClosureTheory.IsolationRoots
public import HexSignDetTheory.SelectedProducer

public section
namespace Hex.RealClosure.Isolation
open HexPolyTheory.Interpret HexRealRootsTheory

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (ha : ∀ a b, φ (a + b) = φ a + φ b)
variable (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)
variable (hnat : ∀ n : Nat, φ (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (φ a) : Int))

omit [Zero E] [DecidableEq E] [One E] [Add E] [Mul E] [NatCast E]
  [DecidableEq K] [IsRealClosed K] in
include hs hsign in
private theorem endpointsLE_bound (upper lower : Endpoint E) (x y : K)
    (upperBound : match upper.map φ with
      | .posInf => True | .finite value => x < value | .negInf => False)
    (lowerBound : match lower.map φ with
      | .negInf => True | .finite value => value < y | .posInf => False)
    (checked : endpointsLE sign upper lower = true) : x < y := by
  cases upper with
  | negInf => simp [endpointsLE] at checked
  | posInf => simp [endpointsLE] at checked
  | finite u =>
    cases lower with
    | negInf => simp [endpointsLE] at checked
    | posInf => simp [endpointsLE] at checked
    | finite l =>
      change x < φ u at upperBound
      change φ l < y at lowerBound
      have separated : φ u ≤ φ l := by
        by_contra contrary
        have positive : sign (u - l) = 1 := by
          simp [hsign, hs, sign_eq_one_iff.mpr (sub_pos.mpr (lt_of_not_ge contrary))]
        simp [endpointsLE, positive] at checked
      exact lt_trans (lt_of_lt_of_le upperBound separated) lowerBound

include hz h1 ha hs hm hnat hsign in
/-- An interval shortcut orders the same selected roots as the existing
interpretation, without inversion or division preservation premises. -/
theorem Root.intervalOrder_sound {context : Ctx}
    (left right : SignDet.Descriptor E Ctx sign context) {order : Ordering}
    (accepted : Root.intervalOrder? left right = some order) :
    order = Ord.compare (left.root φ hz h1 ha hs hm hnat hsign)
      (right.root φ hz h1 ha hs hm hnat hsign) := by
  have leftInside := (Tarski.mem_rootsIn _ _ _ _).mp
    (left.root_spec φ hz h1 ha hs hm hnat hsign).1
  have rightInside := (Tarski.mem_rootsIn _ _ _ _).mp
    (right.root_spec φ hz h1 ha hs hm hnat hsign).1
  have leftBounds := (Tarski.inInterval_iff _ _ _).mp leftInside.2
  have rightBounds := (Tarski.inInterval_iff _ _ _).mp rightInside.2
  unfold Root.intervalOrder? at accepted
  split at accepted
  · rename_i separated
    cases Option.some.inj accepted
    have less := endpointsLE_bound φ hs hsign left.raw.upper right.raw.lower
      (left.root φ hz h1 ha hs hm hnat hsign)
      (right.root φ hz h1 ha hs hm hnat hsign) leftBounds.2 rightBounds.1 separated
    exact (compare_lt_iff_lt.mpr less).symm
  · split at accepted
    · rename_i separated
      cases Option.some.inj accepted
      have greater := endpointsLE_bound φ hs hsign right.raw.upper left.raw.lower
        (right.root φ hz h1 ha hs hm hnat hsign)
        (left.root φ hz h1 ha hs hm hnat hsign) rightBounds.2 leftBounds.1 separated
      exact (compare_gt_iff_gt.mpr greater).symm
    · cases accepted

end Hex.RealClosure.Isolation

/-- info: 'Hex.RealClosure.Isolation.Root.intervalOrder_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Root.intervalOrder_sound

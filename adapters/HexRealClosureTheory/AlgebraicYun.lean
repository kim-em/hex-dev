/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.Algebraic
public import HexRealClosureTheory.YunInvariant

public section

namespace Hex.RealClosure.Algebraic

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable (hsign : ∀ a, coeffSign a = (SignType.sign (f a) : Int))
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
variable (hd : ∀ a b, f (a / b) = f a / f b)

include hd in
/-- Yun's raw coefficient recurrence over one actual algebraic tower level
interprets exactly as the same recurrence over its ambient field. The
stored coefficients need no field laws as literal equalities. -/
theorem Context.mapYun (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context)) :
    Yun.Decomposition.map
      (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
      (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
      (Yun.decomposeRaw p) =
    Yun.decomposeRaw (DensePoly.Interpret.map
      (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
      (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi) p) := by
  exact Yun.map_decomposeRaw
    (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
    (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_div f hz h1 ha hs hm hnat hsign hn hi hd)
    (Element.denote_inv f hz h1 ha hs hm hnat hsign hn hi hd)
    (Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi) p

include hd in
/-- Yun's actual recurrence over a stored algebraic tower level passes the
full exact replay after coefficient interpretation in the ambient field. -/
theorem Context.checkYun (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context)) :
    Yun.check
      (DensePoly.Interpret.map
        (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
        (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi) p)
      (Yun.Decomposition.map
        (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
        (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
        (Yun.decomposeRaw p)) = true := by
  rw [context.mapYun f hz h1 ha hs hm hnat hsign hn hi hd p]
  exact Yun.decompose_sound _

include hd in
/-- Each ambient root of an emitted factor has that factor's label as its
multiplicity in the interpreted input polynomial. -/
theorem Context.yun_rootMultiplicity
    (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context))
    (unit : Element context)
    (entries : Array (DensePoly (Element context) × Nat))
    (hdecomp : Yun.decomposeRaw p = .factors unit entries)
    (entry : DensePoly (Element context) × Nat) (hmem : entry ∈ entries)
    (x : K)
    (hroot : Polynomial.IsRoot
      (HexPolyTheory.toPolynomial
        (DensePoly.Interpret.map
          (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
          (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
          entry.1)) x) :
    Polynomial.rootMultiplicity x
      (HexPolyTheory.toPolynomial
        (DensePoly.Interpret.map
          (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
          (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi) p)) =
      entry.2 := by
  have hcheck := context.checkYun f hz h1 ha hs hm hnat hsign hn hi hd p
  rw [hdecomp] at hcheck
  simp only [Yun.Decomposition.map] at hcheck
  have hmem' :
      (DensePoly.Interpret.map
        (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
        (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
        entry.1, entry.2) ∈
      entries.map (fun item =>
        (DensePoly.Interpret.map
          (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
          (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
          item.1, item.2)) := by
    exact Array.mem_map.mpr ⟨entry, hmem, rfl⟩
  exact Yun.check_rootMultiplicity _ _ _ _ hmem' hcheck x hroot

include hd in
/-- The emitted tower factors cover exactly the roots of the interpreted
input polynomial in the ambient real closed field. -/
theorem Context.yun_roots_iff
    (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context))
    (unit : Element context)
    (entries : Array (DensePoly (Element context) × Nat))
    (hdecomp : Yun.decomposeRaw p = .factors unit entries)
    (x : K) :
    Polynomial.IsRoot
      (HexPolyTheory.toPolynomial
        (DensePoly.Interpret.map
          (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
          (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi) p)) x ↔
      ∃ entry ∈ entries,
        Polynomial.IsRoot
          (HexPolyTheory.toPolynomial
            (DensePoly.Interpret.map
              (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
              (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
              entry.1)) x := by
  have hcheck := context.checkYun f hz h1 ha hs hm hnat hsign hn hi hd p
  rw [hdecomp] at hcheck
  simp only [Yun.Decomposition.map] at hcheck
  have hroots := Yun.check_roots_iff _ _ _ hcheck x
  constructor
  · intro hroot
    obtain ⟨mapped, hmem, hselected⟩ := hroots.mp hroot
    obtain ⟨entry, hentry, rfl⟩ := Array.mem_map.mp hmem
    exact ⟨entry, hentry, hselected⟩
  · rintro ⟨entry, hentry, hselected⟩
    apply hroots.mpr
    refine ⟨(DensePoly.Interpret.map
      (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
      (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
      entry.1, entry.2), ?_, hselected⟩
    exact Array.mem_map.mpr ⟨entry, hentry, rfl⟩

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Context.mapYun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.mapYun
/-- info: 'Hex.RealClosure.Algebraic.Context.checkYun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.checkYun
/-- info: 'Hex.RealClosure.Algebraic.Context.yun_rootMultiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.yun_rootMultiplicity
/-- info: 'Hex.RealClosure.Algebraic.Context.yun_roots_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.yun_roots_iff

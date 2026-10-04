/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.CoefficientSelected
public import HexRealClosureMathlib.MonicEvaluation

public section

namespace Hex.SignDet.SelectedSigns

attribute [local instance 2000] Field.toGrindField

variable {F K G : Type} [Field F] [DecidableEq F] [LinearOrder F] [IsStrictOrderedRing F]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable [Field G] [DecidableEq G] [LinearOrder G] [IsStrictOrderedRing G] [IsRealClosed G]
variable {Ctx : Type} [DecidableEq Ctx] {context : Ctx}
variable {d : Descriptor F Ctx (fun a : F => (SignType.sign a : Int)) context}
variable {q : DensePoly F}

/-- A recorded zero at the original selected root remains a zero at the
single root selected by the actual substituted descriptor. Its sign is
derived from the accepted query, rather than supplied as an agreement premise. -/
theorem zero_substitute (s : SelectedSigns d [q]) (embedding : F →+* K)
    (ordered : StrictMono embedding) (interpretation : RealClosure.CoefficientMap F G)
    (data : ∀ x ∈ s.coefficients,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      (SignType.sign (interpretation.map x) : Int) = (SignType.sign x : Int))
    (original : (HexPolyMathlib.Interpret.interpret embedding
      (fun a => by rw [← embedding.map_zero]; exact embedding.injective.eq_iff) q).eval
        (d.root embedding (fun a => by rw [← embedding.map_zero]; exact embedding.injective.eq_iff)
          embedding.map_one embedding.map_add (map_sub embedding) embedding.map_mul
          (map_natCast embedding) (fun a => by rw [ordered.sign_comp])) = 0) :
    (HexPolyMathlib.toPolynomial (interpretation.polynomial q)).eval
      ((d.substitute interpretation
        (fun x hx => data x (Finset.mem_union_left _ hx))).root
          (fun a : G => a) (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)) = 0 := by
  classical
  have source := s.values_at_root embedding
    (fun a => by rw [← embedding.map_zero]; exact embedding.injective.eq_iff) embedding.map_one
      embedding.map_add (map_sub embedding) embedding.map_mul (map_natCast embedding)
        (fun a => by rw [ordered.sign_comp])
  simp only [signsAt, List.map_cons, List.map_nil, original, sign_zero] at source
  change s.values.toList = [0] at source
  let target := s.substitute (targetSign := fun a : G => (SignType.sign a : Int)) interpretation data
  have signs := target.values_at_root (fun a : G => a) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have identity (p : DensePoly G) :
      HexPolyMathlib.Interpret.interpret (fun a : G => a) (fun _ => Iff.rfl) p =
        HexPolyMathlib.toPolynomial p := by
    ext i
    rw [HexPolyMathlib.Interpret.coeff_interpret, HexPolyMathlib.coeff_toPolynomial]
  have values : target.values.toList = [0] :=
    (s.substitute_values (targetSign := fun a : G => (SignType.sign a : Int)) interpretation data).trans source
  rw [values] at signs
  simp only [List.map_cons, List.map_nil, signsAt, identity, List.cons.injEq,
    and_true] at signs
  have castZero (a : G) (h : (SignType.sign a : Int) = 0) : a = 0 := by
    have zero : SignType.sign a = 0 := by
      cases hs : SignType.sign a <;> simp [hs] at h ⊢
    exact sign_eq_zero_iff.mp zero
  exact castZero _ signs.symm

variable [Algebra F K]

/-- A checked zero query for the original generator's actual minimal
polynomial supplies the chosen-root premise for algebraic evaluation.
The target root is fixed by the mapped descriptor and the same coefficient
interpretation as its entire query replay. -/
theorem minimal_substitute (s : SelectedSigns d [q])
    (ordered : StrictMono (algebraMap F K)) (interpretation : RealClosure.CoefficientMap F G)
    (data : ∀ x ∈ s.coefficients,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      (SignType.sign (interpretation.map x) : Int) = (SignType.sign x : Int))
    (root : K)
    (selected : root = d.root (algebraMap F K)
      (fun a => by rw [← (algebraMap F K).map_zero]; exact (algebraMap F K).injective.eq_iff)
        (algebraMap F K).map_one (algebraMap F K).map_add (map_sub (algebraMap F K))
        (algebraMap F K).map_mul (map_natCast (algebraMap F K))
        (fun a => by rw [ordered.sign_comp]))
    (original : HexPolyMathlib.toPolynomial q = minpoly F root)
    (minimal : Polynomial interpretation.domain)
    (lift : minimal.map interpretation.domain.subtype = HexPolyMathlib.toPolynomial q) :
    minimal.eval₂ interpretation.value
      ((d.substitute interpretation
        (fun x hx => data x (Finset.mem_union_left _ hx))).root
          (fun a : G => a) (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)) = 0 := by
  classical
  have mapped : HexPolyMathlib.Interpret.interpret (algebraMap F K)
      (fun a => by rw [← (algebraMap F K).map_zero]; exact (algebraMap F K).injective.eq_iff) q =
        (HexPolyMathlib.toPolynomial q).map (algebraMap F K) := by
    ext i
    rw [HexPolyMathlib.Interpret.coeff_interpret, Polynomial.coeff_map,
      HexPolyMathlib.coeff_toPolynomial]
  have zero : (HexPolyMathlib.Interpret.interpret (algebraMap F K)
      (fun a => by rw [← (algebraMap F K).map_zero]; exact (algebraMap F K).injective.eq_iff) q).eval
        (d.root (algebraMap F K)
          (fun a => by rw [← (algebraMap F K).map_zero]; exact (algebraMap F K).injective.eq_iff)
          (algebraMap F K).map_one (algebraMap F K).map_add (map_sub (algebraMap F K))
          (algebraMap F K).map_mul (map_natCast (algebraMap F K))
          (fun a => by rw [ordered.sign_comp])) = 0 := by
    rw [mapped, original, ← selected, Polynomial.eval_map]
    exact minpoly.aeval F root
  have chosen := s.zero_substitute (algebraMap F K) ordered interpretation data zero
  rw [interpretation.polynomial_map q minimal lift, Polynomial.eval_map] at chosen
  exact chosen

/-- info: 'Hex.SignDet.SelectedSigns.minimal_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.SelectedSigns.minimal_substitute

/-- info: 'Hex.SignDet.SelectedSigns.zero_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.SelectedSigns.zero_substitute

end Hex.SignDet.SelectedSigns

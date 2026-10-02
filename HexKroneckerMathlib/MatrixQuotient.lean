/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.MatrixDenote

public section

namespace Hex.Kronecker

theorem difference_bounded {cap k : Nat} {as bs : List Bounds}
    {ps qs : List (MvPolynomial (Fin k) Int)}
    (ha : List.Forall₂ (Bounded cap) as ps) (hb : List.Forall₂ (Bounded cap) bs qs) :
    List.Forall₂ (Bounded cap) (differenceBounds cap as bs) (List.zipWith (·-·) ps qs) := by
  induction ha generalizing bs qs with
  | nil => cases hb <;> exact .nil
  | cons h ht ih =>
      cases hb with
      | nil => exact .nil
      | cons g gt => exact .cons (h.sub g) (ih gt)

theorem scaled_bounded {cap k : Nat} (p : Nat) {bs : List Bounds}
    {ps : List (MvPolynomial (Fin k) Int)} (h : List.Forall₂ (Bounded cap) bs ps) :
    List.Forall₂ (Bounded cap) (bs.map ((Bounds.mk (zeroDegrees k) (min p cap)).mul cap))
      (ps.map (MvPolynomial.C (p:Int)*·)) := by
  apply List.rel_map _ h
  intro b q hq
  simpa only [Int.natAbs_natCast] using (Bounded.int cap k (p:Int)).mul hq

theorem checkRowMod_polynomial {k : Nat} (mode : MulMode) (s : SizeBound) (r p : Nat)
    (v : Fin k → Int) (row : List (MvPolynomial (Fin k) Int))
    (cols : List (List (MvPolynomial (Fin k) Int))) (cs qs : List (MvPolynomial (Fin k) Int))
    (h : let E := MvPolynomial.eval₂Hom (RingHom.id Int) v
      checkRowMod mode s r p (row.map E) (cols.map (List.map E)) (cs.map E) (qs.map E) = true) :
    (cols.map (polyDot row)).length = cs.length ∧
    List.Forall₂ (fun a b => MvPolynomial.eval₂Hom (RingHom.id Int) v a =
      MvPolynomial.eval₂Hom (RingHom.id Int) v b)
      (List.zipWith (·-·) (cols.map (polyDot row)) cs) (qs.map (MvPolynomial.C (p:Int)*·)) := by
  induction cols generalizing cs qs with
  | nil =>
      cases cs <;> cases qs <;> simp only [List.map_nil, List.map_cons, checkRowMod, Bool.false_eq_true] at h
      exact ⟨rfl,.nil⟩
  | cons col cols ih =>
      cases cs <;> cases qs <;> try (simp only [List.map_nil, List.map_cons, checkRowMod, Bool.false_eq_true] at h)
      rename_i c cs q qs
      have h := Bool.and_eq_true_iff.mp h
      have ht := ih cs qs h.2
      refine ⟨congrArg Nat.succ ht.1, List.Forall₂.cons ?_ ht.2⟩
      rw [map_sub, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply, polyDot_eval,
        ← dotValue_eq mode s r _ _ (Bool.and_eq_true_iff.mp h.1).1]
      exact eq_of_beq (Bool.and_eq_true_iff.mp h.1).2

theorem checkRowsMod_polynomial {k : Nat} (mode : MulMode) (s : SizeBound) (r p : Nat)
    (v : Fin k → Int) (cols rows cs qs : List (List (MvPolynomial (Fin k) Int)))
    (h : let E := MvPolynomial.eval₂Hom (RingHom.id Int) v
      checkRowsMod mode s r p (cols.map (List.map E)) (rows.map (List.map E))
        (cs.map (List.map E)) (qs.map (List.map E)) = true) :
    List.Forall₂ (fun a b => a.length = b.length) (polyProduct cols rows) cs ∧
    List.Forall₂ (List.Forall₂ (fun a b => MvPolynomial.eval₂Hom (RingHom.id Int) v a =
      MvPolynomial.eval₂Hom (RingHom.id Int) v b))
      (List.zipWith (List.zipWith (·-·)) (polyProduct cols rows) cs)
      (qs.map (List.map (MvPolynomial.C (p:Int)*·))) := by
  induction rows generalizing cs qs with
  | nil =>
      cases cs <;> cases qs <;> simp only [List.map_nil, List.map_cons, checkRowsMod, Bool.false_eq_true] at h
      exact ⟨.nil,.nil⟩
  | cons row rows ih =>
      cases cs <;> cases qs <;> try (simp only [List.map_nil, List.map_cons, checkRowsMod, Bool.false_eq_true] at h)
      rename_i c cs q qs
      have h := Bool.and_eq_true_iff.mp h
      have hr := checkRowMod_polynomial mode s r p v row cols c q h.1
      have ht := ih cs qs h.2
      exact ⟨.cons hr.1 ht.1, .cons hr.2 ht.2⟩

theorem flatten_zipWith (f : α → β → γ) {as : List (List α)} {bs : List (List β)}
    (h : List.Forall₂ (fun a b => a.length = b.length) as bs) :
    (List.zipWith (List.zipWith f) as bs).flatten = List.zipWith f as.flatten bs.flatten := by
  induction h with
  | nil => rfl
  | cons h ht ih =>
      simp only [List.zipWith_cons_cons, List.flatten_cons, List.zipWith_append h, ih]

end Hex.Kronecker

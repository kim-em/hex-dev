/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexKronecker.Kernel
public import HexKroneckerMathlib.ExprSound
public import HexKroneckerMathlib.KernelBounds

public section

namespace Hex.Kronecker.Kernel

theorem exprEq_polynomial {k : Nat} {lhs rhs : Expr}
    (h : exprEq k lhs rhs = true) (hl : lhs.WellFormed k) (hr : rhs.WellFormed k) :
    lhs.toMvPolynomial hl = rhs.toMvPolynomial hr := by
  let ds := maxDegrees (lhs.degrees k) (rhs.degrees k)
  have hlen : ds.length = k := by simp [ds]
  have hlbox : InBox ds (lhs.toMvPolynomial hl) :=
    (lhs.inBox hl).mono hlen (fun i => by
      simp only [ds, getD_maxDegrees]
      exact Nat.le_max_left _ _)
  have hrbox : InBox ds (rhs.toMvPolynomial hr) :=
    (rhs.inBox hr).mono hlen (fun i => by
      simp only [ds, getD_maxDegrees]
      exact Nat.le_max_right _ _)
  have he := (Int.beq'_eq _ _).mp (Bool.and_eq_true_iff.mp h).2
  apply balanced_injective ds hlen _ _ hlbox hrbox (lhs.height + rhs.height)
    ((lhs.height + rhs.height).log2 + 2)
    ((lhs.norm₁_le hl).trans (Nat.le_add_right _ _))
    ((rhs.norm₁_le hr).trans (Nat.le_add_left _ _)) (width_bound _)
  rw [evalKron_eq_eval₂ _ _ lhs hl, evalKron_eq_eval₂ _ _ rhs hr] at he
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using he

/-- A certificate with no resource-budget premise establishes a universal identity. -/
theorem exprEq_sound {k : Nat} {lhs rhs : Expr} (h : exprEq k lhs rhs = true) :
    ∀ {R : Type u} [CommRing R] (v : Nat → R), lhs.denote v = rhs.denote v := by
  intro R _ v
  obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1
  have hp := exprEq_polynomial h hl hr
  rw [← lhs.denoteFin_eq hl v, ← rhs.denoteFin_eq hr v,
    denote_eq_eval₂ lhs hl, denote_eq_eval₂ rhs hr, hp]

theorem degreesEq_iff (as bs : List Nat) : degreesEq as bs = true ↔ as = bs := by
  rw [degreesEq_eq_impl]
  induction as generalizing bs with
  | nil => cases bs <;> simp [degreesEqImpl]
  | cons a as ih => cases bs <;> simp [degreesEqImpl, ih]

theorem exprEqPlan_sound {k : Nat} {lhs rhs : Expr} {ds : List Nat} {w : Nat}
    (h : exprEqPlan k lhs rhs ds w = true) :
    ∀ {R : Type u} [CommRing R] (v : Nat → R), lhs.denote v = rhs.denote v := by
  simp only [exprEqPlan, Bool.and_eq_true] at h
  have hl := h.1.1.1.1
  have hr := h.1.1.1.2
  have hd := (degreesEq_iff _ _).mp h.1.1.2
  have hb := Nat.le_of_ble_eq_true h.1.2
  have he := (Int.beq'_eq _ _).mp h.2
  subst ds
  change evalKron (2^w) (makeStrides 1 (maxDegrees (lhs.degrees k) (rhs.degrees k))) lhs =
    evalKron (2^w) (makeStrides 1 (maxDegrees (lhs.degrees k) (rhs.degrees k))) rhs at he
  have hlen : (maxDegrees (lhs.degrees k) (rhs.degrees k)).length = k := by simp
  have hp : lhs.toMvPolynomial hl = rhs.toMvPolynomial hr := by
    apply balanced_injective _ hlen _ _
      ((lhs.inBox hl).mono hlen (fun i => by simp only [getD_maxDegrees]; exact Nat.le_max_left _ _))
      ((rhs.inBox hr).mono hlen (fun i => by simp only [getD_maxDegrees]; exact Nat.le_max_right _ _))
      (lhs.height + rhs.height) w
      ((lhs.norm₁_le hl).trans (Nat.le_add_right _ _))
      ((rhs.norm₁_le hr).trans (Nat.le_add_left _ _)) hb
    rw [evalKron_eq_eval₂ _ _ lhs hl, evalKron_eq_eval₂ _ _ rhs hr] at he
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using he
  intro R _ v
  rw [← lhs.denoteFin_eq hl v, ← rhs.denoteFin_eq hr v,
    denote_eq_eval₂ lhs hl, denote_eq_eval₂ rhs hr, hp]

theorem termsEq_polynomial {k : Nat} {lhs rhs : Hex.MvPoly.Kernel.PolyList Int}
    (h : termsEq k lhs rhs = true) : termsPolynomial k lhs = termsPolynomial k rhs := by
  obtain ⟨hw, he⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hw
  let s := plan (add (terms k lhs) (terms k rhs))
  have hbl := terms_bound k lhs hl
  have hbr := terms_bound k rhs hr
  have hs : s.strides.length = k := by simp [s, plan, add, hbl.length, hbr.length]
  have he := (Int.beq'_eq _ _).mp he
  change packTerms (2^s.digitBits) s.strides lhs = packTerms (2^s.digitBits) s.strides rhs at he
  apply pair hbl hbr
  rw [packTerms_eq_eval₂ _ _ hs lhs hl, packTerms_eq_eval₂ _ _ hs rhs hr] at he
  exact he

theorem termsEq_sound {k : Nat} {lhs rhs : Hex.MvPoly.Kernel.PolyList Int}
    (h : termsEq k lhs rhs = true) :
    ∀ {R : Type u} [CommRing R] (v : Fin k → R), denoteTerms R v lhs = denoteTerms R v rhs := by
  intro R _ v
  unfold denoteTerms
  rw [termsEq_polynomial h]

theorem termsEqMod_polynomial {k p : Nat} {lhs rhs q : Hex.MvPoly.Kernel.PolyList Int}
    (h : termsEqMod k p lhs rhs q = true) :
    termsPolynomial k lhs - termsPolynomial k rhs = MvPolynomial.C (p : Int) * termsPolynomial k q := by
  simp only [termsEqMod, Bool.and_eq_true] at h
  have hl := h.1.1.1.1.1.2
  have hr := h.1.1.1.1.2
  have hq := canonical_termShape h.1.2
  have hd := (terms_bound k lhs hl).sub (terms_bound k rhs hr)
  have ht : Exact (mul ⟨zeroDegrees k, p⟩ (terms k q))
      (MvPolynomial.C (p:Int)*termsPolynomial k q) := by
    simpa only [Int.natAbs_natCast] using (Exact.int k (p:Int)).mul (terms_bound k q hq)
  let s := plan (add (add (terms k lhs) (terms k rhs)) (mul ⟨zeroDegrees k, p⟩ (terms k q)))
  have hs : s.strides.length = k := by
    change (makeStrides 1 (maxDegrees _ _)).length = k
    rw [length_makeStrides, length_maxDegrees, hd.length, ht.length, Nat.max_self]
  have he := (Int.beq'_eq _ _).mp h.2
  change packTerms (2^s.digitBits) s.strides lhs - packTerms (2^s.digitBits) s.strides rhs =
    (p:Int)*packTerms (2^s.digitBits) s.strides q at he
  apply pair hd ht
  rw [packTerms_eq_eval₂ _ _ hs lhs hl, packTerms_eq_eval₂ _ _ hs rhs hr,
    packTerms_eq_eval₂ _ _ hs q hq] at he
  simpa only [map_sub, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply] using he

theorem termsEqMod_sound {k p : Nat} {lhs rhs q : Hex.MvPoly.Kernel.PolyList Int}
    (h : termsEqMod k p lhs rhs q = true) :
    ∀ {R : Type u} [CommRing R] [CharP R p] (v : Fin k → R),
      denoteTerms R v lhs = denoteTerms R v rhs := quotient_sound (termsEqMod_polynomial h)

theorem exprEqMod_polynomial {k p : Nat} {lhs rhs : Expr} {q : Hex.MvPoly.Kernel.PolyList Int}
    (h : exprEqMod k p lhs rhs q = true) :
    ∃ (hl : lhs.WellFormed k) (hr : rhs.WellFormed k),
      lhs.toMvPolynomial hl - rhs.toMvPolynomial hr = MvPolynomial.C (p:Int)*termsPolynomial k q := by
  simp only [exprEqMod, Bool.and_eq_true] at h
  have hl := h.1.1.1.1.1.2
  have hr := h.1.1.1.1.2
  have hq := canonical_termShape h.1.2
  refine ⟨hl, hr, ?_⟩
  have hd := (expr_bound lhs hl).sub (expr_bound rhs hr)
  have ht : Exact (mul ⟨zeroDegrees k, p⟩ (terms k q))
      (MvPolynomial.C (p:Int)*termsPolynomial k q) := by
    simpa only [Int.natAbs_natCast] using (Exact.int k (p:Int)).mul (terms_bound k q hq)
  let s := plan (add (add ⟨lhs.degrees k, lhs.height⟩ ⟨rhs.degrees k, rhs.height⟩)
    (mul ⟨zeroDegrees k, p⟩ (terms k q)))
  have hs : s.strides.length = k := by
    change (makeStrides 1 (maxDegrees _ _)).length = k
    rw [length_makeStrides, length_maxDegrees, hd.length, ht.length, Nat.max_self]
  have he := (Int.beq'_eq _ _).mp h.2
  change evalKron (2^s.digitBits) s.strides lhs - evalKron (2^s.digitBits) s.strides rhs =
    (p:Int)*packTerms (2^s.digitBits) s.strides q at he
  apply pair hd ht
  rw [evalKron_eq_eval₂ _ _ lhs hl, evalKron_eq_eval₂ _ _ rhs hr,
    packTerms_eq_eval₂ _ _ hs q hq] at he
  simpa only [map_sub, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply] using he

theorem exprEqMod_sound {k p : Nat} {lhs rhs : Expr} {q : Hex.MvPoly.Kernel.PolyList Int}
    (h : exprEqMod k p lhs rhs q = true) :
    ∀ {R : Type u} [CommRing R] [CharP R p] (v : Nat → R), lhs.denote v = rhs.denote v := by
  intro R _ _ v
  obtain ⟨hl, hr, he⟩ := exprEqMod_polynomial h
  rw [← lhs.denoteFin_eq hl v, ← rhs.denoteFin_eq hr v,
    denote_eq_eval₂ lhs hl, denote_eq_eval₂ rhs hr]
  exact quotient_sound he _

theorem mulTerms_polynomial {mode : MulMode} {k n r m ib sb : Nat}
    {a b c : TermMatrix} (h : mulTerms mode k n r m a b c ib sb = true) :
    polyProduct (columnsWith 0 m (matrixPolynomial k b)) (matrixPolynomial k a) = matrixPolynomial k c := by
  obtain ⟨hw, he⟩ := Bool.and_eq_true_iff.mp h
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2
  have hc := (Bool.and_eq_true_iff.mp hw).2
  let products := product k (boundColumns k m (matrix k b)) (matrix k a)
  let s := plan (common k products.flatten (matrix k c).flatten) ib sb
  have hprod := product_bound (columns_bound k r m b hb) (matrix_bound k n r a ha)
  have hcb := matrix_bound k n m c hc
  have hpf := List.rel_flatten hprod
  have hcf := List.rel_flatten hcb
  have hlen := common_length k _ _ (lengths hpf) (lengths hcf)
  have hs : s.strides.length = k := by simpa only [s, plan, length_makeStrides] using hlen
  change checkRows mode s r (Hex.Matrix.Packed.columns m (packMatrix s b))
    (packMatrix s a) (packMatrix s c) = true at he
  rw [packMatrix_eval s hs a ha, packMatrix_eval s hs b hb, packMatrix_eval s hs c hc,
    ← columnsWith_int] at he
  let v := fun i : Fin k => ((2^s.digitBits : Nat):Int)^s.strides.getD i.val 0
  let E := MvPolynomial.eval₂Hom (RingHom.id Int) v
  have hm : columnsWith (0 : Int) m ((matrixPolynomial k b).map (List.map E)) =
      (columnsWith 0 m (matrixPolynomial k b)).map (List.map E) := by
    simpa only [map_zero] using columnsWith_map E 0 m (matrixPolynomial k b)
  change checkRows mode s r (columnsWith 0 m ((matrixPolynomial k b).map (List.map E)))
    ((matrixPolynomial k a).map (List.map E)) ((matrixPolynomial k c).map (List.map E)) = true at he
  rw [hm] at he
  have he := checkRows_polynomial mode s r v _ _ _ he
  apply flatten_injective he
  exact lists hpf hcf (List.rel_flatten he)

theorem mulTerms_sound {mode : MulMode} {k n r m ib sb : Nat}
    {a b c : TermMatrix} (h : mulTerms mode k n r m a b c ib sb = true) :
    ∀ {R : Type u} [CommRing R] (v : Fin k → R),
      denoteMatrix n r R v a * denoteMatrix r m R v b = denoteMatrix n m R v c := by
  intro R _ v
  have hw := (Bool.and_eq_true_iff.mp h).1
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2
  funext i j
  have he := congrArg (fun rows => (rows.getD i.val []).getD j.val 0) (mulTerms_polynomial h)
  rw [product_entry ha hb, matrixPolynomial_getD] at he
  have he := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) v) he
  simpa only [map_sum, map_mul, denoteEntry, _root_.Matrix.mul_apply, denoteMatrix] using he

theorem mulTermsMod_polynomial {mode : MulMode} {k n r m p ib sb : Nat}
    {a b c q : TermMatrix} (h : mulTermsMod mode k n r m p a b c q ib sb = true) :
    List.Forall₂ (fun a b => a.length = b.length)
      (polyProduct (columnsWith 0 m (matrixPolynomial k b)) (matrixPolynomial k a)) (matrixPolynomial k c) ∧
    List.zipWith (List.zipWith (·-·))
      (polyProduct (columnsWith 0 m (matrixPolynomial k b)) (matrixPolynomial k a)) (matrixPolynomial k c) =
      (matrixPolynomial k q).map (List.map (MvPolynomial.C (p:Int)*·)) := by
  obtain ⟨hv, he⟩ := Bool.and_eq_true_iff.mp h
  have hw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1).2
  have hw₁ := (Bool.and_eq_true_iff.mp hw).1
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw₁).1).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw₁).1).2
  have hc := (Bool.and_eq_true_iff.mp hw₁).2
  have hq := (Bool.and_eq_true_iff.mp hw).2
  let products := product k (boundColumns k m (matrix k b)) (matrix k a)
  let differences := difference products.flatten (matrix k c).flatten
  let scaled := (matrix k q).flatten.map (mul ⟨zeroDegrees k, p⟩)
  let s := plan (common k differences scaled) ib sb
  have hprod := product_bound (columns_bound k r m b hb) (matrix_bound k n r a ha)
  have hcb := matrix_bound k n m c hc
  have hqb := matrix_bound k n m q hq
  have hdb := difference_bound (List.rel_flatten hprod) (List.rel_flatten hcb)
  have hsb := scaled_bound p (List.rel_flatten hqb)
  have hlen := common_length k _ _ (lengths hdb) (lengths hsb)
  have hs : s.strides.length = k := by simpa only [s, plan, length_makeStrides] using hlen
  change checkRowsMod mode s r p (Hex.Matrix.Packed.columns m (packMatrix s b))
    (packMatrix s a) (packMatrix s c) (packMatrix s q) = true at he
  rw [packMatrix_eval s hs a ha, packMatrix_eval s hs b hb, packMatrix_eval s hs c hc,
    packMatrix_eval s hs q hq, ← columnsWith_int] at he
  let v := fun i : Fin k => ((2^s.digitBits : Nat):Int)^s.strides.getD i.val 0
  let E := MvPolynomial.eval₂Hom (RingHom.id Int) v
  have hm : columnsWith (0 : Int) m ((matrixPolynomial k b).map (List.map E)) =
      (columnsWith 0 m (matrixPolynomial k b)).map (List.map E) := by
    simpa only [map_zero] using columnsWith_map E 0 m (matrixPolynomial k b)
  change checkRowsMod mode s r p (columnsWith 0 m ((matrixPolynomial k b).map (List.map E)))
    ((matrixPolynomial k a).map (List.map E)) ((matrixPolynomial k c).map (List.map E))
    ((matrixPolynomial k q).map (List.map E)) = true at he
  rw [hm] at he
  have he := checkRowsMod_polynomial mode s r p v _ _ _ _ he
  refine ⟨he.1, ?_⟩
  apply flatten_injective he.2
  rw [flatten_zipWith _ he.1, ← List.map_flatten]
  apply lists hdb hsb
  have hef := List.rel_flatten he.2
  rw [flatten_zipWith _ he.1, ← List.map_flatten] at hef
  exact hef

theorem mulTermsMod_sound {mode : MulMode} {k n r m p ib sb : Nat}
    {a b c q : TermMatrix} (h : mulTermsMod mode k n r m p a b c q ib sb = true) :
    ∀ {R : Type u} [CommRing R] [CharP R p] (v : Fin k → R),
      denoteMatrix n r R v a * denoteMatrix r m R v b = denoteMatrix n m R v c := by
  intro R _ _ v
  have hv := (Bool.and_eq_true_iff.mp h).1
  have hw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1).2
  have hw₁ := (Bool.and_eq_true_iff.mp hw).1
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw₁).1).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw₁).1).2
  funext i j
  obtain ⟨hl,he⟩ := mulTermsMod_polynomial h
  have he := congrArg (fun rows => (rows.getD i.val []).getD j.val 0) he
  rw [matrixSub_entry hl, matrixScale_entry, product_entry ha hb, matrixPolynomial_getD,
    matrixPolynomial_getD] at he
  have he := quotient_sound he v
  simpa only [map_sum, map_mul, denoteEntry, _root_.Matrix.mul_apply, denoteMatrix] using he

end Hex.Kronecker.Kernel

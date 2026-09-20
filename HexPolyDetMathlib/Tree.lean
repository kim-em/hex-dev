/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyDetMathlib.Packed
public import HexPolyDetMathlib.Scaling
public import HexKroneckerMathlib.Mixed
public import HexKroneckerMathlib.Translate

public section

namespace HexMatrixMathlib.DetPoly.Decode

open Hex.Matrix Hex.Matrix.DetWitness Hex.PolyDet.Packed

variable {R S : Type} [CommRing S] {ops : DetOps R} (D : Decode ops S)

/-- Proof-only arithmetic on the semantic ring, used to instantiate the shared
witness identities. No decision on these values occurs in a certificate. -/
noncomputable def ringOps (S : Type) [CommRing S] : DetOps S where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := Neg.neg
  beq := fun a b => @decide (a = b) (Classical.propDecidable _)
  valid := fun _ => true

noncomputable def identity (S : Type) [CommRing S] : Decode (ringOps S) S where
  eval := id
  zero := rfl
  one := rfl
  valid_zero := rfl
  valid_one := rfl
  valid_add := by intros; rfl
  valid_mul := by intros; rfl
  valid_neg := by intros; rfl
  add := by intros; rfl
  mul := by intros; rfl
  neg := by intros; rfl
  beq := by classical intros; exact decide_eq_true_iff

@[simp] theorem ring_validRow (r : List S) : (ringOps S).validRow r = true := by
  induction r <;> simp_all [DetOps.validRow, ringOps]

@[simp] theorem ring_validRows (r : List (List S)) : (ringOps S).validRows r = true := by
  induction r <;> simp_all [DetOps.validRows]

theorem map_entry (r : List R) (j : Nat) :
    (ringOps S).entry (r.map D.eval) j = D.eval (ops.entry r j) := by
  rw [entry_eq_getD, entry_eq_getD]
  change (r.map D.eval).getD j 0 = _
  rw [← D.zero]
  exact List.getD_map r ops.zero D.eval

theorem ring_signed (swaps : List (Nat × Nat)) (a : S) :
    (ringOps S).signed swaps a = (-1 : S) ^ swaps.length * a :=
  (identity S).eval_signed swaps a rfl

/-- Interpret the same serialized decoder through an injective ring map. -/
noncomputable def map {T : Type} [CommRing T] (f : S →+* T) (hf : Function.Injective f) :
    Decode ops T where
  eval := fun a => f (D.eval a)
  zero := by rw [D.zero, map_zero]
  one := by rw [D.one, map_one]
  valid_zero := D.valid_zero
  valid_one := D.valid_one
  valid_add := D.valid_add
  valid_mul := D.valid_mul
  valid_neg := D.valid_neg
  add a b ha hb := by rw [D.add a b ha hb, map_add]
  mul a b ha hb := by rw [D.mul a b ha hb, map_mul]
  neg a ha := by rw [D.neg a ha, map_neg]
  beq a b ha hb := (D.beq a b ha hb).trans hf.eq_iff.symm


/-- Mixed inputs establish the existing triangular contract after interpreting
only the witness entries. This proof performs no polynomial normalization. -/
theorem mixed_rows {I : Type} (d : R) (swaps : List (Nat × Nat))
    (A : List (List I)) (P : List (List S))
    (product : Nat → List R → List (List I) → List R → Bool)
    (hd : ops.valid d = true)
    (hproduct : ∀ i t c, t.length = i + 1 → ops.validRow t = true →
      product i t (leading (i + 1) A) c = true →
      ∀ j, j < i + 1 → (ringOps S).dot (t.map D.eval) ((ringOps S).column j P) =
        D.eval (ops.entry c j)) :
    ∀ ts i done prev,
      (∀ c ∈ done, ∃ j, j < i ∧ c = (ringOps S).column j P) →
      prev = (match ts with
        | [] => D.eval (ops.signed swaps d)
        | t :: _ => D.eval (ops.entry t i)) →
      rows ops d swaps A product i ts = true →
      (identity S).Triangular (D.eval d) swaps done i (ts.map (List.map D.eval))
        ((ringOps S).columns P i ts.length) prev := by
  intro ts
  induction ts with
  | nil =>
      intro i done prev _ he _
      change D.eval d = (ringOps S).signed swaps prev
      rw [ring_signed, he, D.eval_signed swaps d hd, ← _root_.mul_assoc, ← mul_pow]
      simp
  | cons t ts ih =>
      intro i done prev hdone hprev h
      simp only [Hex.PolyDet.Packed.rows, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at h
      obtain ⟨⟨⟨⟨hlen, ht⟩, hnz⟩, hmul⟩, hrest⟩ := h
      have he := hproduct i t _ hlen ht hmul
      have hl := D.valid_entry t i ht
      have hn : D.eval (ops.entry t i) ≠ 0 := by
        intro hz
        have hb := (D.beq _ _ hl D.valid_zero).mpr (hz.trans D.zero.symm)
        rw [hb] at hnz
        contradiction
      change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
      refine ⟨by simpa using hlen, ring_validRow _, ?_, ?_, ?_, ?_⟩
      · change (ringOps S).entry (t.map D.eval) i ≠ 0
        rwa [D.map_entry]
      · change (ringOps S).entry (t.map D.eval) i = prev
        rw [D.map_entry, hprev]
      · intro c hc
        obtain ⟨j, hj, rfl⟩ := hdone c hc
        change (ringOps S).dot (t.map D.eval) ((ringOps S).column j P) = 0
        simpa only [entry_replicate, ite_eq_right (by omega : j ≠ i), D.zero] using he j (by omega)
      · apply ih (i + 1) ((ringOps S).column i P :: done)
          ((ringOps S).dot (t.map D.eval) ((ringOps S).column i P))
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact ⟨i, by omega, rfl⟩
          · obtain ⟨j, hj, rfl⟩ := hdone c hc
            exact ⟨j, by omega, rfl⟩
        · have he := he i (by omega)
          simp only [entry_replicate] at he
          cases ts <;> exact he
        · exact hrest

omit [CommRing S] in
theorem row_map (f : R → S) (A : List (List R)) (i : Nat) :
    row (A.map (List.map f)) i = (row A i).map f := by
  rw [row_eq_getD, row_eq_getD,
    show ([] : List S) = List.map f [] from rfl, List.getD_map]

omit [CommRing S] in
theorem replace_map (f : R → S) (A : List (List R)) (i : Nat) (r : List R) :
    replace (A.map (List.map f)) i (r.map f) = (replace A i r).map (List.map f) := by
  induction A generalizing i with
  | nil => rfl
  | cons a as ih => cases i <;> simp [replace, ih]

omit [CommRing S] in
theorem permute_map (f : R → S) (s : List (Nat × Nat)) (A : List (List R)) :
    permute s (A.map (List.map f)) = (permute s A).map (List.map f) := by
  induction s generalizing A with
  | nil => rfl
  | cons p s ih =>
    obtain ⟨a,b⟩ := p
    simp only [permute, DetWitness.swap, row_map, replace_map, ih]

omit [CommRing S] in
theorem rowLengths_map (f : R → S) (n : Nat) (A : List (List R)) :
    rowLengths n (A.map (List.map f)) = rowLengths n A := by
  induction A <;> simp_all [rowLengths]

theorem anyNonzero_map (v : List R) (hv : ops.validRow v = true) :
    (ringOps S).anyNonzero (v.map D.eval) = ops.anyNonzero v := by
  induction v with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨ha,has⟩ := Bool.and_eq_true_iff.mp hv
    have he : (ringOps S).beq (D.eval a) (ringOps S).zero = ops.beq a ops.zero := by
      apply Bool.eq_iff_iff.mpr
      simpa only [ringOps, decide_eq_true_eq, D.zero] using (D.beq a ops.zero ha D.valid_zero).symm
    simpa only [List.map_cons, DetOps.anyNonzero, he] using congrArg
      (fun b => !(ops.beq a ops.zero) || b) (ih has)

end HexMatrixMathlib.DetPoly.Decode

namespace HexMatrixMathlib.DetPoly.Tree

open Hex.Matrix Hex.Matrix.DetWitness Hex.PolyDet.Packed
open Hex.Kronecker
open scoped HexMvPolyMathlib
attribute [local instance 2000] Ring.toGrindRing

/-- Natural-number variables give every tree atom its own indeterminate. The
finite Kronecker model validates atom bounds before proving identities here. -/
abbrev Model := MvPolynomial Nat Int

noncomputable def decode (k : Nat) : Decode (Hex.PolyDet.ops (C := Int) k) Model :=
  (Polynomial.decode k).map (MvPolynomial.rename Fin.val).toRingHom
    (MvPolynomial.rename_injective _ Fin.val_injective)

theorem decode_eval (k : Nat) (a : Hex.MvPoly.Kernel.PolyList Int) :
    (decode k).eval a = denoteTerms Model (fun i : Fin k => MvPolynomial.X i.val) a := by
  have he : (MvPolynomial.rename (Fin.val : Fin k → Nat)).toRingHom =
      MvPolynomial.eval₂Hom (Int.castRingHom Model) (fun i => MvPolynomial.X i.val) := by
    ext <;> simp
  unfold decode Decode.map
  change (MvPolynomial.rename Fin.val).toRingHom _ = _
  rw [he]
  rfl


noncomputable def model (A : TreeMatrix) : List (List Model) :=
  A.map (List.map (Expr.denote MvPolynomial.X))

theorem model_entry (A : TreeMatrix) (i j : Nat) :
    (Decode.ringOps Model).entry ((model A).getD i []) j =
      ((A.getD i []).getD j (.int 0)).denote MvPolynomial.X := by
  rw [Decode.entry_eq_getD]
  change ((model A).getD i []).getD j 0 = _
  rw [model, show ([] : List Model) = List.map (Expr.denote MvPolynomial.X) [] from rfl,
    List.getD_map]
  rw [show (0 : Model) = Expr.denote MvPolynomial.X (.int 0) from (Int.cast_zero).symm,
    List.getD_map]

theorem list_entry (k : Nat) (A : TermMatrix) (i j : Nat) :
    denoteEntry (fun i : Fin k => (MvPolynomial.X i.val : Model)) A i j =
      (decode k).eval ((Hex.PolyDet.ops k).entry (A.getD i []) j) := by
  rw [Decode.entry_eq_getD, decode_eval]
  rfl

theorem dot_of_product {mode : MulMode} {k r m ib sb : Nat}
    {t c : List (Hex.MvPoly.Kernel.PolyList Int)} {A : TreeMatrix}
    (ht : t.length ≤ r) (j : Nat) (hj : j < m)
    (h : Kernel.mulTree mode k 1 r m [t] A [c] ib sb = true) :
    (Decode.ringOps Model).dot (t.map (decode k).eval)
      ((Decode.ringOps Model).column j (model A)) =
        (decode k).eval ((Hex.PolyDet.ops k).entry c j) := by
  change (Decode.identity Model).eval _ = _
  rw [(Decode.identity Model).eval_dot _ _ r (by simpa using ht)
    (Decode.ring_validRow _) (Decode.ring_validRow _)]
  have he := congrFun (congrFun (Kernel.mulTree_sound h (R := Model) MvPolynomial.X) (0 : Fin 1)) ⟨j,hj⟩
  simp only [_root_.Matrix.mul_apply, denoteMatrix, denoteTreeMatrix, list_entry,
    Fin.val_zero, List.getD_cons_zero] at he
  simpa only [Decode.identity, id_eq, Decode.map_entry, Decode.column_entry, model_entry] using he


theorem model_leading (r : Nat) (A : TreeMatrix) : model (leading r A) = leading r (model A) := by
  simp [model, leading, List.map_map, List.map_take, Function.comp_def]

theorem prefix_product {mode : MulMode} {k i ib sb : Nat}
    {t c : List (Hex.MvPoly.Kernel.PolyList Int)} {A : TreeMatrix}
    (ht : t.length = i + 1) (j : Nat) (hj : j < i + 1)
    (h : Kernel.mulTree mode k 1 (i + 1) (i + 1) [t] (leading (i + 1) A) [c] ib sb = true) :
    (Decode.ringOps Model).dot (t.map (decode k).eval)
      ((Decode.ringOps Model).column j (model A)) =
        (decode k).eval ((Hex.PolyDet.ops k).entry c j) := by
  have he := dot_of_product (by omega : t.length ≤ i + 1) j hj h
  rw [model_leading] at he
  change (Decode.identity Model).eval _ = _ at he ⊢
  rw [(Decode.identity Model).eval_dot _ _ (i + 1) (by simpa using ht.le)
    (Decode.ring_validRow _) (Decode.ring_validRow _)] at he ⊢
  rw [← he]
  apply Finset.sum_congr rfl
  intro l _
  rw [Decode.column_entry, Decode.column_entry, Decode.leading_entry _ _ l.isLt hj]

theorem rowLengths_all (n : Nat) (A : List (List R)) :
    rowLengths n A = A.all (fun row => row.length == n) := by
  induction A with
  | nil => rfl
  | cons row rows ih =>
    simp only [rowLengths, List.all_cons, ih]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq]


/-- Tree products supply the common determinant identities in a polynomial
domain, preserving the original witness, pivots and row permutation. -/
theorem identities (mode : MulMode) (k n : Nat)
    (A : TreeMatrix) (w : DetWitness (Hex.MvPoly.Kernel.PolyList Int)) (widths : List (Nat × Nat))
    (h : Hex.PolyDet.checkDetPolyPackedTree mode k n A w widths = true) :
    (Decode.identity Model).Identities n (model A) (w.map (decode k).eval) := by
  unfold Hex.PolyDet.checkDetPolyPackedTree at h
  obtain ⟨hA,h⟩ := Bool.and_eq_true_iff.mp h
  have hlen : (model A).length = n := by
    simpa only [model, List.length_map] using
      eq_of_beq (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hA).1).1
  have hrows : rowLengths n (model A) = true := by
    rw [model, Decode.rowLengths_map, rowLengths_all]
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hA).1).2
  cases w with
  | triangular swaps ts d =>
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨hs,hd⟩,ht⟩,hfirst⟩,hcheck⟩ := h
    refine ⟨hlen, hrows, Decode.ring_validRows _, hs, rfl, ?_⟩
    have hm : permute swaps (model A) = model (permute swaps A) :=
      Decode.permute_map _ _ _
    change (Decode.identity Model).Triangular ((decode k).eval d) swaps [] 0
      (ts.map (List.map (decode k).eval))
      ((Decode.ringOps Model).columns (permute swaps (model A)) 0 n) 1
    rw [hm, ← ht]
    apply (decode k).mixed_rows d swaps (permute swaps A) (model (permute swaps A))
      _ hd (fun i t c ht _ hp j hj => prefix_product ht j hj hp)
      ts 0 [] 1 (by simp) _ hcheck
    cases ts with
    | nil =>
      have hn : n = 0 := by simpa using ht.symm
      simp only [hn, BEq.rfl, ↓reduceIte] at hfirst
      have he := ((decode k).beq _ _ hd (decode k).valid_one).mp hfirst
      have hs : swaps = [] := by
        cases swaps with
        | nil => rfl
        | cons s ss => simp [hn, swapsOk] at hs
      simpa only [hs, DetOps.signed, (decode k).one] using he.symm
    | cons t ts =>
      have hn : n ≠ 0 := by simp only [List.length_cons] at ht; omega
      simp [hn, DetWitness.row] at hfirst
      have hv : (Hex.PolyDet.ops k).validRow t = true := by
        simp only [Hex.PolyDet.Packed.rows, Bool.and_eq_true] at hcheck
        exact hcheck.1.1.1.2
      have he := ((decode k).beq _ _ ((decode k).valid_entry t 0 hv)
        (decode k).valid_one).mp hfirst
      simpa only [(decode k).one] using he.symm
  | singular v =>
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨hvlen,hv⟩,hnz⟩,hmul⟩ := h
    refine ⟨hlen, hrows, Decode.ring_validRows _, by simpa using hvlen,
      Decode.ring_validRow _, ?_, ?_⟩
    · rwa [(decode k).anyNonzero_map v hv]
    · intro c hc
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hc
      have hjn : j < n := by simpa only [Decode.columns_length] using hj
      have he := dot_of_product (by omega : v.length ≤ n) j hjn hmul
      have hz : (Hex.PolyDet.ops (C := Int) k).entry (List.replicate n []) j = [] := by
        rw [Decode.entry_eq_getD]
        simp [Hex.PolyDet.ops]
      rw [hz] at he
      change (Decode.ringOps Model).dot _ _ = 0
      rw [← Nat.zero_add j, ← Decode.columns_getD (model A) 0 n j hjn,
        getD_eq_getElem' _ _ _ hj] at he
      exact he.trans (decode k).zero

/-- The certificate determines the determinant without expanding input trees. -/
theorem checkDetPolyPackedTree_sound (mode : MulMode)
    (k n : Nat) (A : TreeMatrix) (w : DetWitness (Hex.MvPoly.Kernel.PolyList Int)) (widths : List (Nat × Nat))
    (h : Hex.PolyDet.checkDetPolyPackedTree mode k n A w widths = true) :
    ((Decode.identity Model).matrix n (model A)).det = (decode k).eval (Polynomial.value w) := by
  have hs := (Decode.identity Model).identities_sound n (model A) (w.map (decode k).eval)
    (identities mode k n A w widths h)
  have hz : (decode k).eval [] = 0 := (decode k).zero
  cases w <;> simpa only [DetWitness.map, Decode.identity, id_eq, Polynomial.value, hz] using hs


variable {F : Type u} [CommRing F]

/-- Entry identification reduces only the retained syntax's denotation. -/
@[expose] def evaluated (n : Nat) (rows : TreeMatrix) (ctx : Lean.RArray F) :
    _root_.Matrix (Fin n) (Fin n) F := denoteTreeMatrix n n ctx.get rows

theorem eval_decode (k : Nat) (ctx : Lean.RArray F) (a : Hex.MvPoly.Kernel.PolyList Int) :
    MvPolynomial.eval₂Hom (Int.castRingHom F) ctx.get ((decode k).eval a) =
      denoteTerms F (fun i : Fin k => ctx.get i.val) a := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.rename Fin.val _) = _
  rw [MvPolynomial.eval₂Hom_rename]
  rfl

theorem evaluated_map (n : Nat) (rows : TreeMatrix) (ctx : Lean.RArray F) :
    ((Decode.identity Model).matrix n (model rows)).map
      (MvPolynomial.eval₂Hom (Int.castRingHom F) ctx.get) = evaluated n rows ctx := by
  ext i j
  simp only [_root_.Matrix.map_apply, Decode.matrix_apply, Decode.identity, id_eq, model_entry,
    Expr.map_denote, MvPolynomial.eval₂Hom_X']
  rfl

/-- Transport from the polynomial domain to any commutative coefficient ring. -/
theorem transport_det (k n : Nat) (rows : TreeMatrix)
    (w : DetWitness (Hex.MvPoly.Kernel.PolyList Int)) (ctx : Lean.RArray F)
    (A : _root_.Matrix (Fin n) (Fin n) F)
    (hcheck : ((Decode.identity Model).matrix n (model rows)).det = (decode k).eval (Polynomial.value w))
    (hA : A = evaluated n rows ctx) :
    A.det = denoteTerms F (fun i : Fin k => ctx.get i.val) (Polynomial.value w) := by
  rw [hA, ← evaluated_map]
  change ((MvPolynomial.eval₂Hom (Int.castRingHom F) ctx.get).mapMatrix _).det = _
  rw [← RingHom.map_det, hcheck, eval_decode]

/-- Compare the target tree directly with the certificate value at its Kronecker point. -/
theorem target_det (k n : Nat) (rows : TreeMatrix)
    (w : DetWitness (Hex.MvPoly.Kernel.PolyList Int)) (ctx : Lean.RArray F)
    (A : _root_.Matrix (Fin n) (Fin n) F) (q : Expr) (e : F)
    (hcheck : ((Decode.identity Model).matrix n (model rows)).det = (decode k).eval (Polynomial.value w))
    (hA : A = evaluated n rows ctx) (he : q.denote ctx.get = e)
    (hq : q.denote ctx.get = denoteTerms F (fun i : Fin k => ctx.get i.val) (Polynomial.value w)) : A.det = e := by
  rw [transport_det k n rows w ctx A hcheck hA,
    ← hq, he]

/-- The generated expression uses the same tree comparison as an explicit target. -/
theorem result_det (k n : Nat) (rows : TreeMatrix)
    (w : DetWitness (Hex.MvPoly.Kernel.PolyList Int)) (ctx : Lean.RArray F)
    (A : _root_.Matrix (Fin n) (Fin n) F) (q : Expr) (e : F)
    (hcheck : ((Decode.identity Model).matrix n (model rows)).det = (decode k).eval (Polynomial.value w))
    (hA : A = evaluated n rows ctx) (he : q.denote ctx.get = e)
    (hq : q.denote ctx.get = denoteTerms F (fun i : Fin k => ctx.get i.val) (Polynomial.value w)) : A.det = e :=
  target_det k n rows w ctx A q e hcheck hA he hq

/-- Rational row scaling uses the same tree certificate and positive-scale cancellation. -/
theorem scaled_det (k n : Nat) (rows : TreeMatrix)
    (w : DetWitness (Hex.MvPoly.Kernel.PolyList Int)) (ctx : Lean.RArray Rat)
    (A : _root_.Matrix (Fin n) (Fin n) Rat) (s : List Nat)
    (hcheck : ((Decode.identity Model).matrix n (model rows)).det = (decode k).eval (Polynomial.value w))
    (hA : evaluated n rows ctx = _root_.Matrix.diagonal (fun i : Fin n => (s.getD i 1 : Rat)) * A)
    (hs : s.length = n) :
    (DetWitness.prodNat s : Rat) * A.det =
      denoteTerms Rat (fun i : Fin k => ctx.get i.val) (Polynomial.value w) := by
  have hdet := transport_det k n rows w ctx _ hcheck hA.symm
  rw [_root_.Matrix.det_mul, _root_.Matrix.det_diagonal] at hdet
  rw [HexMatrixMathlib.prodNat_cast s n hs]
  exact hdet


theorem scaled_target (k : Nat)
    (d : Hex.MvPoly.Kernel.PolyList Int) (ctx : Lean.RArray Rat)
    (D t : Nat) (a e : Rat) (q : Expr)
    (hdet : (D : Rat) * a = denoteTerms Rat (fun i : Fin k => ctx.get i.val) d)
    (ht : 0 < t) (hD : 0 < D) (he : q.denote ctx.get = (t : Rat) * e)
    (hq : (Expr.mul (.int D) q).denote ctx.get =
      denoteTerms Rat (fun i : Fin k => ctx.get i.val) (Hex.MvPoly.Kernel.smul (t : Int) d)) :
    a = e := by
  have h := hq
  have hd : denoteTerms Rat (fun i : Fin k => ctx.get i.val) (Hex.MvPoly.Kernel.smul (t : Int) d) =
      (t : Rat) * denoteTerms Rat (fun i : Fin k => ctx.get i.val) d := by
    unfold denoteTerms termsPolynomial
    rw [HexMvPolyMathlib.Kernel.denote_smul, map_mul, MvPolynomial.eval₂Hom_C]
    simp
  rw [Expr.denote, Expr.denote, he, hd, ← hdet] at h
  apply Scaling.cancel D t a e hD ht
  simpa only [Int.cast_natCast] using h.symm


/-- Identify a displayed value through the same bounded tree comparison. -/
theorem value_eq (k : Nat) (ctx : Lean.RArray F)
    (q : Expr) (d : Hex.MvPoly.Kernel.PolyList Int) (e : F)
    (he : q.denote ctx.get = e) (hq : q.denote ctx.get = denoteTerms F (fun i : Fin k => ctx.get i.val) d) :
    denoteTerms F (fun i : Fin k => ctx.get i.val) d = e :=
  hq.symm.trans he

end HexMatrixMathlib.DetPoly.Tree

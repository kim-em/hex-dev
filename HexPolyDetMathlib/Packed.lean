/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyDet.Packed
public import HexPolyDetMathlib.Residue
public import HexKroneckerMathlib.MatrixDenote
public import HexKroneckerMathlib.MulModSound

public section

namespace HexMatrixMathlib.DetPoly.Decode

open Hex.Matrix Hex.Matrix.DetWitness Hex.PolyDet.Packed


variable {R S : Type} [CommRing S] {ops : DetOps R} (D : Decode ops S)

theorem entry_replicate (i j : Nat) (a : R) :
    ops.entry (List.replicate i ops.zero ++ [a]) j =
      if j = i then a else ops.zero := by
  induction i generalizing j with
  | zero => cases j <;> simp [DetOps.entry]
  | succ i ih =>
      cases j with
      | zero => simp [List.replicate_succ, DetOps.entry]
      | succ j => simpa [List.replicate_succ, DetOps.entry] using ih j

/-- Convert the packed row checks into the same semantic diagonal walk as the
term-list checker. The product soundness premise is supplied by Kronecker. -/
theorem packed_rows (d : R) (swaps : List (Nat × Nat)) (P : List (List R))
    (product : Nat → List R → List (List R) → List R → Bool)
    (hd : ops.valid d = true) (hP : ops.validRows P = true)
    (hproduct : ∀ i t c, t.length = i + 1 → ops.validRow t = true →
      product i t (leading (i + 1) P) c = true →
      ∀ j, j < i + 1 → D.eval (ops.dot t (ops.column j P)) = D.eval (ops.entry c j)) :
    ∀ ts i done prev,
      (∀ c ∈ done, ∃ j, j < i ∧ c = ops.column j P) →
      ops.valid prev = true →
      D.eval prev = (match ts with
        | [] => D.eval (ops.signed swaps d)
        | t :: _ => D.eval (ops.entry t i)) →
      rows ops d swaps P product i ts = true →
      D.Triangular d swaps done i ts (ops.columns P i ts.length) prev := by
  intro ts
  induction ts with
  | nil =>
      intro i done prev _ hp he _
      change D.eval d = D.eval (ops.signed swaps prev)
      rw [D.eval_signed swaps prev hp, he, D.eval_signed swaps d hd]
      have hs : (-1 : S) ^ swaps.length * (-1 : S) ^ swaps.length = 1 := by
        rw [← mul_pow]; simp
      rw [← _root_.mul_assoc, hs, one_mul]
  | cons t ts ih =>
      intro i done prev hdone hp hprev h
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
      refine ⟨hlen, ht, hn, hprev.symm, ?_, ?_⟩
      · intro c hc
        obtain ⟨j, hj, rfl⟩ := hdone c hc
        simpa only [entry_replicate, if_neg (by omega : j ≠ i), D.zero] using he j (by omega)
      · apply ih (i + 1) (ops.column i P :: done) (ops.dot t (ops.column i P))
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact ⟨i, by omega, rfl⟩
          · obtain ⟨j, hj, rfl⟩ := hdone c hc
            exact ⟨j, by omega, rfl⟩
        · exact D.valid_dot t _ ht (D.valid_column P i hP)
        · have he := he i (by omega)
          simp only [entry_replicate, if_pos rfl] at he
          cases ts <;> exact he
        · exact hrest

/-- Either product implementation establishes the common determinant contract. -/
theorem packed_identities (n : Nat) (A : List (List R)) (w : DetWitness R)
    (product : Nat → List R → List (List R) → List R → Bool)
    (singular : List R → Bool)
    (hproduct : ∀ swaps i t c, ops.validRows A = true → swapsOk n swaps = true →
      t.length = i + 1 → ops.validRow t = true →
      product i t (leading (i + 1) (permute swaps A)) c = true →
      ∀ j, j < i + 1 →
        D.eval (ops.dot t (ops.column j (permute swaps A))) = D.eval (ops.entry c j))
    (hsingular : ∀ v, ops.validRows A = true → v.length = n → ops.validRow v = true →
      singular v = true → ∀ j, j < n → D.eval (ops.dot v (ops.column j A)) = 0)
    (h : check ops n A product singular w = true) : D.Identities n A w := by
  cases w with
  | triangular swaps ts d =>
      simp only [check, Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hl, hr⟩, ha⟩, hs⟩, hd⟩, ht⟩, hfirst⟩, hrows⟩ := h
      refine ⟨hl, hr, ha, hs, hd, ?_⟩
      rw [← ht]
      apply D.packed_rows d swaps (permute swaps A) product hd (D.valid_permute swaps A ha)
        (fun i t c hlen hv hp => hproduct swaps i t c ha hs hlen hv hp)
        ts 0 [] ops.one (by simp) D.valid_one _ hrows
      cases ts with
      | nil =>
          have hn : n = 0 := by simpa using ht.symm
          simp only [hn, BEq.rfl, ↓reduceIte] at hfirst
          have he := (D.beq _ _ hd D.valid_one).mp hfirst
          have hs : swaps = [] := by
            cases swaps with
            | nil => rfl
            | cons s ss => simp [hn, swapsOk] at hs
          simpa [hs, DetOps.signed] using he.symm
      | cons t ts =>
          have hn : n ≠ 0 := by simp only [List.length_cons] at ht; omega
          simp [hn, DetWitness.row] at hfirst
          have hv : ops.validRow t = true := by
            simp only [Hex.PolyDet.Packed.rows, Bool.and_eq_true] at hrows
            exact hrows.1.1.1.2
          exact ((D.beq _ _ (D.valid_entry t 0 hv) D.valid_one).mp hfirst).symm
  | singular v =>
      simp only [check, Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨hl, hr⟩, ha⟩, hvlen⟩, hv⟩, hnz⟩, hmul⟩ := h
      refine ⟨hl, hr, ha, hvlen, hv, hnz, ?_⟩
      intro c hc
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
      have hjn : j < n := by simpa only [columns_length] using hj
      have he := hsingular v ha hvlen hv hmul j hjn
      rwa [← Nat.zero_add j, ← columns_getD A 0 n j hjn,
        getD_eq_getElem' _ _ _ hj] at he

end HexMatrixMathlib.DetPoly.Decode

namespace HexMatrixMathlib.DetPoly.Decode

open Hex.Matrix Hex.PolyDet.Packed
open Hex.Kronecker (denoteTerms denoteEntry)

variable {R S : Type} [CommRing S] {ops : DetOps R} (D : Decode ops S)

theorem getD_take (xs : List α) (d : α) {i r : Nat} (hi : i < r) :
    (xs.take r).getD i d = xs.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

theorem leading_entry (r : Nat) (A : List (List R)) {i j : Nat} (hi : i < r) (hj : j < r) :
    ops.entry ((leading r A).getD i []) j = ops.entry (A.getD i []) j := by
  rw [leading, show ([] : List R) = ([] : List R).take r from (List.take_nil).symm, List.getD_map]
  rw [getD_take A [] hi, entry_eq_getD, entry_eq_getD, getD_take _ _ hj, List.take_nil]

/-- Read a lifted matrix through its coefficient interpretation. -/
theorem lifted_entry {k : Nat} (v : Fin k → S)
    (lift : R → Hex.MvPoly.Kernel.PolyList Int)
    (hlift : ∀ a, denoteTerms S v (lift a) = D.eval a)
    (hz : lift ops.zero = []) (A : List (List R)) (i j : Nat) :
    denoteEntry v (A.map (List.map lift)) i j = D.eval (ops.entry (A.getD i []) j) := by
  unfold denoteEntry
  rw [show ([] : List (Hex.MvPoly.Kernel.PolyList Int)) = ([] : List R).map lift from rfl,
    List.getD_map]
  rw [← hz, List.getD_map]
  rw [entry_eq_getD]
  exact hlift _

/-- A finite lifted row product supplies the polynomial dot identity. -/
theorem dot_of_product {k r m : Nat} (v : Fin k → S)
    (lift : R → Hex.MvPoly.Kernel.PolyList Int)
    (hlift : ∀ a, denoteTerms S v (lift a) = D.eval a) (hz : lift ops.zero = [])
    (t : List R) (A : List (List R)) (c : List R)
    (htlen : t.length ≤ r) (ht : ops.validRow t = true) (hA : ops.validRows A = true)
    (h : ∀ j : Fin m,
      (∑ i : Fin r, denoteEntry v [t.map lift] 0 i.val *
        denoteEntry v (A.map (List.map lift)) i.val j.val) =
          denoteEntry v [c.map lift] 0 j.val) (j : Nat) (hj : j < m) :
    D.eval (ops.dot t (ops.column j A)) = D.eval (ops.entry c j) := by
  rw [D.eval_dot t _ r htlen ht (D.valid_column A j hA)]
  have he := h ⟨j, hj⟩
  change (∑ i : Fin r, denoteEntry v ([t].map (List.map lift)) 0 i.val *
    denoteEntry v (A.map (List.map lift)) i.val j) =
    denoteEntry v ([c].map (List.map lift)) 0 j at he
  simpa only [D.lifted_entry v lift hlift hz, List.getD_cons_zero, column_entry] using he

end HexMatrixMathlib.DetPoly.Decode

namespace HexMatrixMathlib.DetPoly.Polynomial

open Hex Hex.Matrix Hex.MvPoly.Kernel
open scoped HexMvPolyMathlib
attribute [local instance 2000] Ring.toGrindRing

private theorem denote_X (k : Nat) (a : PolyList Int) :
    Kronecker.denoteTerms (MvPolynomial (Fin k) Int) MvPolynomial.X a = (decode k).eval a := by
  unfold Kronecker.denoteTerms
  have hc : Int.castRingHom (MvPolynomial (Fin k) Int) = MvPolynomial.C := by ext; simp
  rw [hc]
  exact MvPolynomial.eval₂_eta (Kronecker.termsPolynomial k a)

/-- Packed products establish the shared identities in the integer polynomial domain. -/
theorem packed_identities (budget : Kronecker.Budget) (mode : Kronecker.MulMode)
    (k n : Nat) (A : List (List (PolyList Int))) (w : DetWitness (PolyList Int))
    (h : PolyDet.checkDetPolyPacked budget mode k n A w = true) :
    (decode k).Identities n A w := by
  apply (decode k).packed_identities n A w _ _ _ _ h
  · intro swaps i t c hA _ htlen ht hp j hj
    let P := DetWitness.permute swaps A
    have hP := (decode k).valid_permute swaps A hA
    have hv : (ops k).validRows (PolyDet.Packed.leading (i + 1) P) = true := by
      rw [Decode.validRows_iff]
      intro r hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      rw [Decode.validRow_iff]
      intro a ha
      exact (Decode.validRow_iff _).mp
        ((Decode.validRows_iff P).mp hP s (List.mem_of_mem_take hs)) a (List.mem_of_mem_take ha)
    have he := Kronecker.checkMulTerms_entry hp (R := MvPolynomial (Fin k) Int) MvPolynomial.X (0 : Fin 1)
    have hd := (decode k).dot_of_product (r := i + 1) (m := i + 1) MvPolynomial.X id (denote_X k) rfl t
      (PolyDet.Packed.leading (i + 1) P) c (by omega) ht hv
      (by simpa using he) j hj
    rw [(decode k).eval_dot _ _ (i + 1) (by omega) ht
      ((decode k).valid_column _ j hv)] at hd
    rw [(decode k).eval_dot _ _ (i + 1) (by omega) ht
      ((decode k).valid_column _ j hP)]
    rw [← hd]
    apply Finset.sum_congr rfl
    intro l _
    rw [Decode.column_entry, Decode.column_entry, Decode.leading_entry _ _ l.isLt hj]
  · intro v hA hvlen hv hp j hj
    have he := Kronecker.checkMulTerms_entry hp (R := MvPolynomial (Fin k) Int) MvPolynomial.X (0 : Fin 1)
    have hd := (decode k).dot_of_product (r := n) (m := n) MvPolynomial.X id (denote_X k) rfl v A
      (List.replicate n []) (by omega) hv hA (by simpa using he) j hj
    have hz : (ops (C := Int) k).entry (List.replicate n []) j = [] := by
      rw [Decode.entry_eq_getD]
      simp [ops, PolyDet.ops]
    rw [hz] at hd
    exact hd.trans (decode k).zero

/-- A passing packed certificate determines the same polynomial determinant. -/
theorem checkDetPolyPacked_sound (budget : Kronecker.Budget) (mode : Kronecker.MulMode)
    (k n : Nat) (A : List (List (PolyList Int))) (w : DetWitness (PolyList Int))
    (h : PolyDet.checkDetPolyPacked budget mode k n A w = true) :
    Hex.Matrix.det (matrix k n A) = Hex.MvPoly.Kernel.denote (n := k) (cmp := Mono.grevlex) (value w) := by
  apply (HexMvPolyMathlib.equiv (n := k) (cmp := Mono.grevlex)).injective
  rw [HexMatrixMathlib.det_eq (matrix k n A), RingEquiv.map_det]
  change ((HexMatrixMathlib.matrixEquiv (matrix k n A)).map
    (HexMvPolyMathlib.equiv (n := k) (cmp := Mono.grevlex))).det = _
  rw [← decode_matrix]
  have hs := (decode k).identities_sound n A w (packed_identities budget mode k n A w h)
  cases w <;> simpa [value, decode, HexMvPolyMathlib.Kernel.denote, Hex.MvPoly.Kernel.denote] using hs

end HexMatrixMathlib.DetPoly.Polynomial

namespace HexMatrixMathlib.DetPoly.Residue

open Hex Hex.Matrix Hex.MvPoly.Kernel
open scoped HexMvPolyMathlib HexModArithMathlib.ZMod64
attribute [local instance 2000] Ring.toGrindRing

variable (p : Nat) [Hex.ZMod64.Bounds p]

private theorem denote_lift (k : Nat) (a : PolyList Nat) :
    Kronecker.denoteTerms (MvPolynomial (Fin k) (ZMod p)) MvPolynomial.X
      (PolyDet.Packed.lift a) = (decode p k).eval a := by
  induction a with
  | nil =>
      simp [PolyDet.Packed.lift, Kronecker.denoteTerms, decode]
  | cons a as ih =>
      obtain ⟨e,c⟩ := a
      change Kronecker.denoteTerms _ MvPolynomial.X ((e,(c : Int)) :: PolyDet.Packed.lift as) = _
      unfold Kronecker.denoteTerms at *
      rw [Kronecker.termsPolynomial_cons, map_add, ih]
      change _ + HexMvPolyMathlib.Kernel.denoteMod p as =
        HexMvPolyMathlib.Kernel.denoteMod p ((e,c) :: as)
      rw [HexMvPolyMathlib.Kernel.denoteMod_cons]
      congr 1
      simp [MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq]


/-- Packed products establish the shared identities in the residue polynomial domain. -/
theorem packed_identities (budget : Kronecker.Budget) (mode : Kronecker.MulMode)
    (k n : Nat) (A : List (List (PolyList Nat))) (w : DetWitness (PolyList Nat))
    (qs : List (List (PolyList Int)))
    (h : PolyDet.checkDetPolyPackedMod budget mode p k n A w qs = true) :
    (decode p k).Identities n A w := by
  have h := (Bool.and_eq_true_iff.mp h).2
  apply (decode p k).packed_identities n A w _ _ _ _ h
  · intro swaps i t c hA _ htlen ht hp j hj
    let P := DetWitness.permute swaps A
    have hP := (decode p k).valid_permute swaps A hA
    have hv : (PolyDet.opsMod p k).validRows (PolyDet.Packed.leading (i + 1) P) = true := by
      rw [Decode.validRows_iff]
      intro r hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      rw [Decode.validRow_iff]
      intro a ha
      exact (Decode.validRow_iff _).mp
        ((Decode.validRows_iff P).mp hP s (List.mem_of_mem_take hs)) a (List.mem_of_mem_take ha)
    have he := Kronecker.checkMulTermsMod_entry hp (R := MvPolynomial (Fin k) (ZMod p)) MvPolynomial.X (0 : Fin 1)
    have hd := (decode p k).dot_of_product (r := i + 1) (m := i + 1) MvPolynomial.X PolyDet.Packed.lift (denote_lift p k) rfl t
      (PolyDet.Packed.leading (i + 1) P) c (by omega) ht hv
      (by simpa [PolyDet.Packed.lift] using he) j hj
    rw [(decode p k).eval_dot _ _ (i + 1) (by omega) ht
      ((decode p k).valid_column _ j hv)] at hd
    rw [(decode p k).eval_dot _ _ (i + 1) (by omega) ht
      ((decode p k).valid_column _ j hP)]
    rw [← hd]
    apply Finset.sum_congr rfl
    intro l _
    rw [Decode.column_entry, Decode.column_entry, Decode.leading_entry _ _ l.isLt hj]
  · intro v hA hvlen hv hp j hj
    have he := Kronecker.checkMulTermsMod_entry hp (R := MvPolynomial (Fin k) (ZMod p)) MvPolynomial.X (0 : Fin 1)
    have hd := (decode p k).dot_of_product (r := n) (m := n) MvPolynomial.X PolyDet.Packed.lift (denote_lift p k) rfl v A
      (List.replicate n []) (by omega) hv hA (by simpa [PolyDet.Packed.lift] using he) j hj
    have hz : (PolyDet.opsMod p k).entry (List.replicate n []) j = [] := by
      rw [Decode.entry_eq_getD]
      simp [PolyDet.opsMod]
    rw [hz] at hd
    exact hd.trans (decode p k).zero

/-- Quotient-certified residue products determine the determinant in the residue
polynomial domain; evaluation requires no domain assumption on the target. -/
theorem checkDetPolyPackedMod_sound [Hex.ZMod64.PrimeModulus p]
    (budget : Kronecker.Budget) (mode : Kronecker.MulMode)
    (k n : Nat) (A : List (List (PolyList Nat))) (w : DetWitness (PolyList Nat))
    (qs : List (List (PolyList Int)))
    (h : PolyDet.checkDetPolyPackedMod budget mode p k n A w qs = true) :
    ((decode p k).matrix n A).det = HexMvPolyMathlib.Kernel.denoteMod p
      (n := k) (cmp := Mono.grevlex) (value w) := by
  let : Fact (Nat.Prime p) := ⟨Nat.prime_def.mpr Hex.ZMod64.PrimeModulus.prime⟩
  have hs := (decode p k).identities_sound n A w (packed_identities p budget mode k n A w qs h)
  cases w <;> simpa [value, decode] using hs

end HexMatrixMathlib.DetPoly.Residue

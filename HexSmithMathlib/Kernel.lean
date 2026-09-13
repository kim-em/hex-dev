/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSmith.Cert
public import HexSmith.Kernel
public import HexMatrixMathlib.ListProducts
public import HexHermiteMathlib.Span
public import HexSmith.Structure
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Isomorphisms

public section

/-! Soundness of integer Smith list certificates. -/

namespace HexSmithMathlib

open HexMatrixMathlib Hex.Matrix.Lists

/-- Decode a list witness for use in the reference soundness theorem. -/
@[expose]
def decodeWitness (n m : Nat) (c : Hex.Matrix.SmithWitness) : Hex.Matrix.SmithData n m where
  rank := c.rank
  diag := Vector.ofFn fun i => entry 0 c.diag i
  left := matrixOfLists n n c.left
  leftInv := matrixOfLists n n c.leftInv
  right := matrixOfLists m m c.right
  rightInv := matrixOfLists m m c.rightInv

/-- Decoding preserves every diagonal coefficient. -/
theorem decode_diag (n m : Nat) (c : Hex.Matrix.SmithWitness) (i : Fin c.rank) :
    (decodeWitness n m c).diag[i] = entry 0 c.diag i := by
  change (Vector.ofFn (fun i : Fin c.rank => entry 0 c.diag i))[i.val] = _
  rw [Vector.getElem_ofFn]

private theorem diagonal_eq {n m : Nat} (c : Hex.Matrix.SmithWitness)
    (hlen : c.diag.length = c.rank) :
    (fun (i : Fin n) (j : Fin m) => diagonal c.diag i j) =
      matrixEquiv (Hex.Matrix.diagMatrix (decodeWitness n m c).diag n m) := by
  ext i j
  rw [matrixEquiv_apply, Hex.Matrix.getElem_diagMatrix]
  change diagonal c.diag i j =
    if h : i.val = j.val ∧ i.val < c.rank then
      (decodeWitness n m c).diag[(⟨i.val, h.2⟩ : Fin c.rank)] else 0
  by_cases hij : i.val = j.val
  · by_cases hi : i.val < c.rank
    · rw [dite_eq_left ⟨hij, hi⟩, decode_diag n m c]
      simp [diagonal, hij]
    · have hz : entry 0 c.diag i = 0 := by
        rw [entry_eq_getD, getD_eq_default' _ _ _ (by omega)]
      rw [dite_eq_right (by tauto)]
      unfold diagonal
      rw [show Nat.beq i.val j.val = true from Nat.beq_eq.mpr hij]
      exact hz
  · simp [diagonal, hij]

/-- A passing list certificate establishes the existing reference checker,
without any hypothesis identifying the witness with producer output. -/
theorem reference_check {n m : Nat} (rows : List (List Int))
    (c : Hex.Matrix.SmithWitness) (hc : Hex.Matrix.checkSmithList n m rows c = true) :
    Hex.Matrix.snfCert (matrixOfLists n m rows) (decodeWitness n m c)
      (matrixOfLists n m c.intermediate) = true := by
  simp only [Hex.Matrix.checkSmithList, Bool.and_eq_true, Nat.ble_eq,
    Nat.beq_eq, and_assoc] at hc
  obtain ⟨_, hrn, hrm, hlen, hl, _, hr, _, ht, hp, hd, hT, hD, hL, hR⟩ := hc
  have hleft := matrix_mul_of_product hl hT
  have hdiag : matrixOfLists n m c.intermediate * matrixOfLists m m c.right =
      Hex.Matrix.diagMatrix (decodeWitness n m c).diag n m := by
    apply matrixEquiv.injective
    rw [matrixEquiv_mul, matrixEquiv_matrixOfLists, matrixEquiv_matrixOfLists,
      mul_of_product ht hD, diagonal_eq c hlen]
  have hleftInv := matrix_inverse_of_product hl hL
  have hrightInv := matrix_inverse_of_product hr hR
  simp only [Hex.Matrix.snfCert, Bool.and_eq_true, Hex.Matrix.mulEqCert_iff,
    Hex.Matrix.isSNFShape_iff, and_assoc]
  refine ⟨hleft, ?_, hleftInv, hrightInv, hrn, hrm, ?_, ?_⟩
  · have h := congrArg Hex.Matrix.transpose hdiag
    simpa only [Hex.Matrix.transpose_mul_of_mul_comm, decodeWitness] using h
  · intro i
    change 0 < (Vector.ofFn (fun i : Fin c.rank => entry 0 c.diag i))[i.val]
    rw [Vector.getElem_ofFn]
    exact of_decide_eq_true ((all_iff _ _).mp hp i i.isLt)
  · intro i
    have hi : i.val < c.rank - 1 := i.isLt
    change (Vector.ofFn (fun i : Fin c.rank => entry 0 c.diag i))[i.val]'(by omega) ∣
      (Vector.ofFn (fun i : Fin c.rank => entry 0 c.diag i))[i.val + 1]'(by omega)
    rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
    apply Int.dvd_of_emod_eq_zero
    exact of_decide_eq_true ((all_iff _ _).mp hd i i.isLt)

/-- Soundness inherited from the arbitrary-certificate Smith contract. -/
theorem smith_of_check {n m : Nat} (rows : List (List Int))
    (c : Hex.Matrix.SmithWitness) (hc : Hex.Matrix.checkSmithList n m rows c = true) :
    Hex.Matrix.IsSNF (matrixOfLists n m rows) (decodeWitness n m c) :=
  Hex.Matrix.snfCert_sound (reference_check rows c hc)

namespace Checked

open scoped DirectSum

variable {n m : Nat} {A : Hex.Matrix Int n m} {S : Hex.Matrix.SmithData n m}

/-- Ambient Smith coordinates supplied by the checked right transform. -/
noncomputable def coordinates (h : Hex.Matrix.IsSNF A S) :
    (Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ) := by
  refine LinearEquiv.ofLinearMap
    (Matrix.vecMulLinear (matrixEquiv S.right))
    (Matrix.vecMulLinear (matrixEquiv S.rightInv)) ?_ ?_
  · apply LinearMap.ext
    intro x
    change Matrix.vecMul (Matrix.vecMul x (matrixEquiv S.rightInv))
      (matrixEquiv S.right) = x
    rw [Matrix.vecMul_vecMul, ← matrixEquiv_mul, Hex.Matrix.mul_eq_one_comm h.right_inv]
    change Matrix.vecMul x (matrixEquiv (1 : Hex.Matrix Int m m)) = x
    rw [matrixEquiv_one, Matrix.vecMul_one]
  · apply LinearMap.ext
    intro x
    change Matrix.vecMul (Matrix.vecMul x (matrixEquiv S.right))
      (matrixEquiv S.rightInv) = x
    rw [Matrix.vecMul_vecMul, ← matrixEquiv_mul, h.right_inv]
    change Matrix.vecMul x (matrixEquiv (1 : Hex.Matrix Int m m)) = x
    rw [matrixEquiv_one, Matrix.vecMul_one]

/-- Smith coordinates agree with executable multiplication by the right transform. -/
theorem coordinates_apply (h : Hex.Matrix.IsSNF A S) (v : Vector Int m) :
    coordinates h (vectorEquiv v) = vectorEquiv (Hex.Matrix.vecMul v S.right) := by
  exact (HexHermiteMathlib.vectorEquiv_vecMulLinear S.right v).symm

/-- Membership is divisibility in the leading Smith coordinates and zero in
the free coordinates. Both transforms enter through arbitrary-data solvability. -/
theorem mem_span_iff (h : Hex.Matrix.IsSNF A S) (x : Fin m → ℤ) :
    x ∈ Submodule.span ℤ (Set.range (matrixEquiv A)) ↔
      (∀ i : Fin S.rank, S.diag[i] ∣ coordinates h x (Fin.castLE h.rank_le_m i)) ∧
      (∀ i : Fin (m - S.rank), coordinates h x ⟨S.rank + i, by omega⟩ = 0) := by
  let v : Vector Int m := vectorEquiv.symm x
  have hv : vectorEquiv v = x := vectorEquiv.apply_symm_apply x
  have hm := HexHermiteMathlib.mem_span_iff A v
  change vectorEquiv v ∈ Submodule.span ℤ (Set.range (matrixEquiv A)) ↔ A.memLattice v at hm
  rw [← hv, hm, Hex.Matrix.memLattice,
    Hex.Matrix.solvable_iff_dvd h, coordinates_apply]
  constructor
  · rintro ⟨hd, hz⟩
    refine ⟨hd, fun i => ?_⟩
    simpa only [vectorEquiv_apply] using
      hz ⟨S.rank + i, by omega⟩ (by change S.rank ≤ S.rank + i.val; omega)
  · rintro ⟨hd, hz⟩
    refine ⟨hd, fun j hj => ?_⟩
    let i : Fin (m - S.rank) := ⟨j.val - S.rank, by omega⟩
    have hi : (⟨S.rank + i, by omega⟩ : Fin m) = j := Fin.ext (by simp [i]; omega)
    simpa only [hi, vectorEquiv_apply] using hz i

/-- Cyclic group in one checked diagonal coordinate. -/
abbrev cyclic (S : Hex.Matrix.SmithData n m) (i : Fin S.rank) :=
  ℤ ⧸ Ideal.span ({S.diag[i]} : Set ℤ)

/-- The free-coordinate projection in the checked ambient coordinates. -/
noncomputable def freeProjection (h : Hex.Matrix.IsSNF A S) :
    (Fin m → ℤ) →ₗ[ℤ] (Fin (m - S.rank) → ℤ) :=
  LinearMap.pi fun i => (LinearMap.proj ⟨S.rank + i, by omega⟩).comp
    (coordinates h).toLinearMap

/-- The torsion-coordinate projection as a function on the diagonal indices. -/
noncomputable def torsionFun (h : Hex.Matrix.IsSNF A S) :
    (Fin m → ℤ) →ₗ[ℤ] ((i : Fin S.rank) → cyclic S i) :=
  LinearMap.pi fun i => (Ideal.span ({S.diag[i]} : Set ℤ)).mkQ.comp
    ((LinearMap.proj (Fin.castLE h.rank_le_m i)).comp (coordinates h).toLinearMap)

/-- The presentation map keeps free coordinates and reduces torsion ones. -/
noncomputable def presentation (h : Hex.Matrix.IsSNF A S) :
    (Fin m → ℤ) →ₗ[ℤ]
      (Fin (m - S.rank) → ℤ) × ⨁ i : Fin S.rank, cyclic S i :=
  (freeProjection h).prod
    ((DirectSum.linearEquivFunOnFintype ℤ _ _).symm.toLinearMap.comp (torsionFun h))

/-- The presentation map kills exactly the input row lattice. -/
theorem ker_presentation (h : Hex.Matrix.IsSNF A S) :
    LinearMap.ker (presentation h) = Submodule.span ℤ (Set.range (matrixEquiv A)) := by
  ext x
  rw [LinearMap.mem_ker, mem_span_iff h]
  constructor
  · intro hx
    have hf : freeProjection h x = 0 := by
      simpa [presentation] using congrArg Prod.fst hx
    have ht : torsionFun h x = 0 := by
      have ht := congrArg Prod.snd hx
      have he := congrArg (DirectSum.linearEquivFunOnFintype ℤ (Fin S.rank) (cyclic S)) ht
      simpa [presentation] using he
    refine ⟨fun i => ?_, fun i => congrFun hf i⟩
    have hi := congrFun ht i
    change (Ideal.span ({S.diag[i]} : Set ℤ)).mkQ
      (coordinates h x (Fin.castLE h.rank_le_m i)) = 0 at hi
    rw [← Ideal.mem_span_singleton, ← Submodule.Quotient.mk_eq_zero]
    exact hi
  · rintro ⟨hd, hz⟩
    apply Prod.ext
    · funext i
      exact hz i
    · apply (DirectSum.linearEquivFunOnFintype ℤ (Fin S.rank) (cyclic S)).injective
      funext i
      change (Ideal.span ({S.diag[i]} : Set ℤ)).mkQ
        (coordinates h x (Fin.castLE h.rank_le_m i)) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      exact hd i

/-- Every free and torsion coordinate tuple has a representative. -/
theorem presentation_surjective (h : Hex.Matrix.IsSNF A S) :
    Function.Surjective (presentation h) := by
  classical
  rintro ⟨f, t⟩
  let e := DirectSum.linearEquivFunOnFintype ℤ (Fin S.rank) (cyclic S)
  choose z hz using fun i =>
    Submodule.mkQ_surjective (Ideal.span ({S.diag[i]} : Set ℤ)) (e t i)
  let y : Fin m → ℤ := fun j =>
    if hj : j.val < S.rank then z ⟨j.val, hj⟩
    else f ⟨j.val - S.rank, by omega⟩
  refine ⟨(coordinates h).symm y, ?_⟩
  apply Prod.ext
  · funext i
    change coordinates h ((coordinates h).symm y) ⟨S.rank + i, by omega⟩ = f i
    rw [LinearEquiv.apply_symm_apply]
    simp [y]
  · apply e.injective
    funext i
    change (Ideal.span ({S.diag[i]} : Set ℤ)).mkQ
      (coordinates h ((coordinates h).symm y) (Fin.castLE h.rank_le_m i)) = e t i
    rw [LinearEquiv.apply_symm_apply]
    simpa [y] using hz i

/-- The quotient equivalence of an arbitrary accepted Smith certificate. -/
noncomputable def quotient (h : Hex.Matrix.IsSNF A S) :
    ((Fin m → ℤ) ⧸ Submodule.span ℤ (Set.range (matrixEquiv A))) ≃ₗ[ℤ]
      (Fin (m - S.rank) → ℤ) × ⨁ i : Fin S.rank, cyclic S i :=
  (Submodule.quotEquivOfEq _ _ (ker_presentation h).symm).trans
    ((presentation h).quotKerEquivOfSurjective (presentation_surjective h))

end Checked

open scoped DirectSum

/-- The canonical target type for an integer row-presentation quotient. -/
abbrev SmithQuotient {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ)
    (rank : Nat) (factors : Fin rank → ℤ) :=
  ((Fin m → ℤ) ⧸ Submodule.span ℤ (Set.range A)) ≃ₗ[ℤ]
    (Fin (m - rank) → ℤ) × ⨁ i : Fin rank, ℤ ⧸ Ideal.span ({factors i} : Set ℤ)

/-- A literal Smith decomposition of an integer row presentation. -/
structure SmithResult {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ) where
  /-- The literal rank of the presentation. -/
  rank : Nat
  /-- The rank is bounded by both matrix dimensions. -/
  rank_le : rank ≤ min n m
  /-- The literal canonical invariant-factor function. -/
  factors : Fin rank → ℤ
  /-- Every invariant factor is positive. -/
  positive : ∀ i, 0 < factors i
  /-- Successive invariant factors form a divisibility chain. -/
  chain : ∀ i j : Fin rank, i.val + 1 = j.val → factors i ∣ factors j
  /-- The row-presentation quotient, including its free complement. -/
  equiv : SmithQuotient A rank factors

/-- Construct the literal result from a checked witness and input identification. -/
-- The certificate contract uses theorem-style names for these Type-valued bridges.
@[expose, nolint defsWithUnderscore]
noncomputable def smith_of_checkList {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℤ) (rows : List (List Int))
    (c : Hex.Matrix.SmithWitness) (hA : A = ofLists n m rows)
    (hc : Hex.Matrix.checkSmithList n m rows c = true) : SmithResult A := by
  let h := smith_of_check rows c hc
  have hd (i : Fin (decodeWitness n m c).rank) :
      (decodeWitness n m c).diag[i] = vecOfList c.rank c.diag i := by
    change (Vector.ofFn (fun i : Fin c.rank => entry 0 c.diag i))[i.val] = _
    rw [Vector.getElem_ofFn]
    exact (entry_eq_getD 0 c.diag i.val).trans
      (vecOfList_apply c.rank c.diag ⟨i.val, i.isLt⟩).symm
  refine
    { rank := c.rank
      rank_le := Nat.le_min.mpr ⟨h.rank_le_n, h.rank_le_m⟩
      factors := vecOfList c.rank c.diag
      positive := ?_
      chain := ?_
      equiv := ?_ }
  · intro i
    exact hd i ▸ h.diag_pos i
  · intro i j hij
    have hj : i.val + 1 < (decodeWitness n m c).rank := by
      change i.val + 1 < c.rank
      omega
    have hh := h.chain i.val hj
    change (Vector.ofFn (fun i : Fin c.rank => entry 0 c.diag i))[i.val]'(by omega) ∣
      (Vector.ofFn (fun i : Fin c.rank => entry 0 c.diag i))[i.val + 1]'(by omega) at hh
    rw [Vector.getElem_ofFn, Vector.getElem_ofFn] at hh
    simpa only [vecOfList_apply, entry_eq_getD, hij] using hh
  · subst A
    have e : SmithQuotient (matrixEquiv (matrixOfLists n m rows)) c.rank
        (fun i : Fin (decodeWitness n m c).rank => (decodeWitness n m c).diag[i]) :=
      Checked.quotient h
    have df : (fun i : Fin (decodeWitness n m c).rank => (decodeWitness n m c).diag[i]) =
        vecOfList c.rank c.diag := funext hd
    rw [df] at e
    rw [matrixEquiv_matrixOfLists] at e
    exact e

/-- The checked result retains the literal rank. -/
@[simp] theorem smith_of_checkList_rank {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℤ) (rows : List (List Int))
    (c : Hex.Matrix.SmithWitness) (hA : A = ofLists n m rows)
    (hc : Hex.Matrix.checkSmithList n m rows c = true) :
    (smith_of_checkList A rows c hA hc).rank = c.rank := by
  rfl

/-- The checked result retains the literal factor list. -/
theorem smith_of_checkList_factors {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℤ) (rows : List (List Int))
    (c : Hex.Matrix.SmithWitness) (hA : A = ofLists n m rows)
    (hc : Hex.Matrix.checkSmithList n m rows c = true) :
    HEq (smith_of_checkList A rows c hA hc).factors (vecOfList c.rank c.diag) := by
  rfl

/-- Construct a quotient equivalence with an identified closed target factor function. -/
@[nolint defsWithUnderscore]
noncomputable def smith_equiv_of_checkList {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℤ) (rows : List (List Int))
    (c : Hex.Matrix.SmithWitness) (hA : A = ofLists n m rows)
    (hc : Hex.Matrix.checkSmithList n m rows c = true)
    (d : Fin c.rank → ℤ) (hd : d = vecOfList c.rank c.diag) :
    SmithQuotient A c.rank d := by
  subst d
  exact (smith_of_checkList A rows c hA hc).equiv

end HexSmithMathlib

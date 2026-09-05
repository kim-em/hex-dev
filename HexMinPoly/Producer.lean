/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMinPoly.Cert

public section

/-! Certificate production from row reduction and extended gcd. -/

namespace Hex.Matrix

universe u

variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F] {n : Nat}

private theorem get_ofFn {m : Nat} {α : Type u} (f : Fin m → α) (i : Fin m) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = f i
  rw [Vector.getElem_ofFn]

/-- A candidate right inverse for a Krylov prefix, extracted from the row
transform of the transpose reduction. It is certified at `krylovDeg`. -/
@[expose]
def krylovRightInverseCandidate (A : Matrix F n n) (v : Vector F n) (d : Nat) :
    Matrix F n d :=
  let reduction := rowReduce (Matrix.transpose (krylovMat A v d))
  Matrix.ofFn fun i j =>
    if h : j.val < n then reduction.transform[((⟨j.val, h⟩ : Fin n), i)] else 0

/-- At the computed Krylov degree, the extracted transform block is a right
inverse of the independent Krylov prefix. -/
theorem krylovRightInverseCandidate_sound (A : Matrix F n n) (v : Vector F n) :
    krylovMat A v (krylovDeg A v) *
        krylovRightInverseCandidate A v (krylovDeg A v) =
      Matrix.identity (R := F) (krylovDeg A v) := by
  let d := krylovDeg A v
  let K := krylovMat A v d
  let N := Matrix.transpose K
  let D := rowReduce N
  have hd : d ≤ n := krylovDeg_le A v
  have hRankK : rowReduce_rank K = d := rowReduce_rank_krylovPrefix A v
  have hRankN : rowReduce_rank N = d := by
    change rowReduce_rank (Matrix.transpose K) = d
    rw [rowReduce_rank_transpose, hRankK]
  let T : Matrix F d n := Matrix.takeRows D.transform d hd
  have hTN : T * N = Matrix.identity (R := F) d := by
    have htransform := congrArg
      (fun X : Matrix F n d => Matrix.takeRows X d hd)
      (rowReduce_transform_mul N)
    rw [Matrix.takeRows_mul] at htransform
    change T * N = Matrix.takeRows D.echelon d hd at htransform
    rw [rowReduce_takeRows_echelon_eq_identity N hd hRankN] at htransform
    exact htransform
  have hinv : krylovRightInverseCandidate A v d = Matrix.transpose T := by
    apply Matrix.ext_getElem
    intro i j
    rw [krylovRightInverseCandidate, Matrix.getElem_ofFn, Matrix.getElem_transpose,
      Matrix.getElem_takeRows]
    simp [D, N, K, d, Nat.lt_of_lt_of_le j.isLt hd]
  calc
    K * krylovRightInverseCandidate A v d = K * Matrix.transpose T := by rw [hinv]
    _ = Matrix.transpose N * Matrix.transpose T := by simp [N]
    _ = Matrix.transpose (T * N) := (Matrix.transpose_mul_of_mul_comm T N).symm
    _ = Matrix.transpose (Matrix.identity (R := F) d) := by rw [hTN]
    _ = Matrix.identity (R := F) d := Matrix.transpose_identity

/-- Produce the order certificate for one vector. -/
@[expose]
def orderCert (A : Matrix F n n) (v : Vector F n) : OrderCert F n :=
  let d := krylovDeg A v
  { poly := vecMinPoly A v
    deg := d
    inv := krylovRightInverseCandidate A v d }

/-- Produce the rescaled extended-gcd witness for one LCM step. -/
@[expose]
def lcmStep (running incoming : DensePoly F) : LcmStep F :=
  let raw := DensePoly.xgcd running incoming
  let unit := raw.gcd.leadingCoeff⁻¹
  let common := DensePoly.scale unit raw.gcd
  let left := (DensePoly.divMod running common).1
  let right := (DensePoly.divMod incoming common).1
  { common
    left
    right
    bezoutLeft := DensePoly.scale unit raw.left
    bezoutRight := DensePoly.scale unit raw.right
    result := left * incoming }

/-- The executable extended-gcd producer supplies all four checker identities,
and its result is the normalized least common multiple. -/
theorem lcmStep_sound (running incoming : DensePoly F)
    (hrunningMonic : running.Monic) (hincomingMonic : incoming.Monic) :
    let s := lcmStep running incoming
    running = s.common * s.left ∧
      incoming = s.common * s.right ∧
      s.bezoutLeft * running + s.bezoutRight * incoming = s.common ∧
      s.result = s.left * incoming ∧
      s.result = DensePoly.lcm running incoming ∧ s.result.Monic := by
  let raw := DensePoly.xgcd running incoming
  let unit := raw.gcd.leadingCoeff⁻¹
  let common := DensePoly.scale unit raw.gcd
  have hrunningNe : running ≠ 0 := DensePoly.monic_ne_zero hrunningMonic
  have hincomingNe : incoming ≠ 0 := DensePoly.monic_ne_zero hincomingMonic
  have hgDvd : raw.gcd ∣ running ∧ raw.gcd ∣ incoming := by
    rw [show raw.gcd = DensePoly.gcd running incoming by
      exact DensePoly.xgcd_gcd_eq_gcd running incoming]
    exact DensePoly.gcd_dvd_inputs_field running incoming
  have hgNe : raw.gcd ≠ 0 := by
    rcases hgDvd.1 with ⟨q, hq⟩
    intro hg
    apply hrunningNe
    rw [hq, hg, DensePoly.zero_mul]
  have hgPos : 0 < raw.gcd.size := by
    by_cases h : 0 < raw.gcd.size
    · exact h
    · exact False.elim (hgNe ((DensePoly.size_eq_zero_iff raw.gcd).mp
        (Nat.eq_zero_of_not_pos h)))
  have hgZero : raw.gcd.isZero = false :=
    (DensePoly.isZero_eq_false_iff raw.gcd).2 hgPos
  have hcommon : common = DensePoly.monicize raw.gcd := by
    rw [DensePoly.monicize, ite_eq_right (by simp [hgZero])]
  have hcommonNe : common ≠ 0 := by
    rw [hcommon]
    exact DensePoly.monicize_ne_zero hgNe
  have hcommonMonic : common.Monic := by
    rw [hcommon]
    exact DensePoly.monicize_monic hgNe
  have hcDvdRunning : common ∣ running := by
    rw [hcommon]
    exact DensePoly.monicize_dvd_of_dvd hgNe hgDvd.1
  have hcDvdIncoming : common ∣ incoming := by
    rw [hcommon]
    exact DensePoly.monicize_dvd_of_dvd hgNe hgDvd.2
  rcases hcDvdRunning with ⟨left, hleft⟩
  rcases hcDvdIncoming with ⟨right, hright⟩
  have hleftNe : left ≠ 0 := by
    intro h
    apply hrunningNe
    rw [hleft, h, DensePoly.mul_comm_poly, DensePoly.zero_mul]
  have hrightNe : right ≠ 0 := by
    intro h
    apply hincomingNe
    rw [hright, h, DensePoly.mul_comm_poly, DensePoly.zero_mul]
  have hleftQuot : (DensePoly.divMod running common).1 = left := by
    rw [hleft, DensePoly.mul_comm_poly common left,
      DensePoly.divMod_mul_field left common hcommonNe]
  have hrightQuot : (DensePoly.divMod incoming common).1 = right := by
    rw [hright, DensePoly.mul_comm_poly common right,
      DensePoly.divMod_mul_field right common hcommonNe]
  have hbezout :
      DensePoly.scale unit raw.left * running +
          DensePoly.scale unit raw.right * incoming = common := by
    rw [← DensePoly.scale_mul, ← DensePoly.scale_mul, ← DensePoly.scale_add,
      DensePoly.xgcd_bezout_field running incoming]
  have hleftMonic : left.Monic := by
    have hcommonPos : 0 < common.size := by
      by_cases h : 0 < common.size
      · exact h
      · exact False.elim (hcommonNe ((DensePoly.size_eq_zero_iff common).mp
          (Nat.eq_zero_of_not_pos h)))
    have hleftPos : 0 < left.size := by
      by_cases h : 0 < left.size
      · exact h
      · exact False.elim (hleftNe ((DensePoly.size_eq_zero_iff left).mp
          (Nat.eq_zero_of_not_pos h)))
    have hprod : common.leadingCoeff * left.leadingCoeff ≠ 0 := by
      intro h
      have h' := congrArg (fun x : F => common.leadingCoeff⁻¹ * x) h
      rw [← Lean.Grind.Semiring.mul_assoc,
        Lean.Grind.Field.inv_mul_cancel
          (DensePoly.leadingCoeff_ne_zero_of_pos_size common hcommonPos),
        Lean.Grind.Semiring.one_mul, Lean.Grind.Semiring.mul_zero] at h'
      exact DensePoly.leadingCoeff_ne_zero_of_pos_size left hleftPos h'
    have hlc := DensePoly.leadingCoeff_mul common left hcommonPos hleftPos hprod
    rw [← hleft, hrunningMonic, hcommonMonic, Lean.Grind.Semiring.one_mul] at hlc
    exact hlc.symm
  have hresultMonic : (left * incoming).Monic :=
    DensePoly.mul_monic hleftMonic hincomingMonic
  have hincomingDvd : incoming ∣ left * incoming :=
    ⟨left, DensePoly.mul_comm_poly left incoming⟩
  have hrunningDvd : running ∣ left * incoming := by
    refine ⟨right, ?_⟩
    rw [hleft, hright]
    rw [← DensePoly.mul_assoc_poly, DensePoly.mul_comm_poly left common,
      DensePoly.mul_assoc_poly]
  have hresultDvdLcm : left * incoming ∣ DensePoly.lcm running incoming :=
    DensePoly.commonProduct_dvd running incoming common left right
      (DensePoly.scale unit raw.left) (DensePoly.scale unit raw.right)
      (left * incoming) (DensePoly.lcm running incoming) hincomingNe hleft hright
      hbezout rfl (DensePoly.dvd_lcm_left running incoming)
      (DensePoly.dvd_lcm_right running incoming)
  have hlcmDvdResult : DensePoly.lcm running incoming ∣ left * incoming :=
    DensePoly.lcm_dvd running incoming (left * incoming) hrunningDvd hincomingDvd
  have hresult : left * incoming = DensePoly.lcm running incoming :=
    DensePoly.monic_dvd_antisymm hresultMonic
      (DensePoly.lcm_monic hrunningNe hincomingNe) hresultDvdLcm hlcmDvdResult
  dsimp only [lcmStep]
  change running = common * (DensePoly.divMod running common).1 ∧
    incoming = common * (DensePoly.divMod incoming common).1 ∧
    DensePoly.scale unit raw.left * running +
      DensePoly.scale unit raw.right * incoming = common ∧
    (DensePoly.divMod running common).1 * incoming =
      (DensePoly.divMod running common).1 * incoming ∧
    (DensePoly.divMod running common).1 * incoming = DensePoly.lcm running incoming ∧
    ((DensePoly.divMod running common).1 * incoming).Monic
  rw [hleftQuot, hrightQuot]
  exact ⟨hleft, hright, hbezout, rfl, hresult, hresultMonic⟩

/-- LCM of the first `j` standard-basis order polynomials. -/
@[expose]
def basisOrderLcmPrefix (A : Matrix F n n) (j : Nat) (hj : j ≤ n) : DensePoly F :=
  (List.finRange j).foldl
    (fun running i =>
      DensePoly.lcm running
        (vecMinPoly A (basisVec n ⟨i.val, Nat.lt_of_lt_of_le i.isLt hj⟩))) 1

@[simp, grind =]
theorem basisOrderLcmPrefix_zero (A : Matrix F n n) :
    basisOrderLcmPrefix A 0 (Nat.zero_le n) = 1 := rfl

/-- Extending the prefix by one basis vector performs exactly one `lcm` step. -/
theorem basisOrderLcmPrefix_succ (A : Matrix F n n) (j : Nat) (hj : j + 1 ≤ n) :
    basisOrderLcmPrefix A (j + 1) hj =
      DensePoly.lcm (basisOrderLcmPrefix A j (by omega))
        (vecMinPoly A (basisVec n ⟨j, by omega⟩)) := by
  unfold basisOrderLcmPrefix
  rw [List.finRange_succ_last, List.foldl_append]
  simp only [List.foldl_map, List.foldl_cons, List.foldl_nil]
  congr 2

/-- Every prefix value is monic. -/
theorem basisOrderLcmPrefix_monic (A : Matrix F n n) (j : Nat) (hj : j ≤ n) :
    (basisOrderLcmPrefix A j hj).Monic := by
  induction j with
  | zero =>
      rw [basisOrderLcmPrefix_zero, DensePoly.monic_iff_leadingCoeff_eq_one,
        DensePoly.leadingCoeff_one]
  | succ j ih =>
      rw [basisOrderLcmPrefix_succ]
      exact DensePoly.lcm_monic
        (DensePoly.monic_ne_zero (ih (by omega)))
        (DensePoly.monic_ne_zero (vecMinPoly_monic A (basisVec n ⟨j, by omega⟩)))

/-- The full prefix is the basis-order LCM. -/
theorem basisOrderLcmPrefix_all (A : Matrix F n n) :
    basisOrderLcmPrefix A n (Nat.le_refl n) = basisOrderLcm A := by
  unfold basisOrderLcmPrefix basisOrderLcm DensePoly.lcmList
  rw [List.foldl_map]

/-- The one-pass certificate producer state after the first `j` basis
vectors. The vector lengths make the accumulated witness count explicit. -/
structure MinPolyCert.Prefix (F : Type u) [Zero F] [DecidableEq F]
    (n j : Nat) where
  running : DensePoly F
  order : Vector (OrderCert F n) j
  steps : Vector (LcmStep F) j

/-- Build orders and LCM witnesses in one forward sweep. Each basis-vector
order is computed once and each running LCM is reused by the next step. -/
@[expose]
def MinPolyCert.prefix (A : Matrix F n n) :
    (j : Nat) → j ≤ n → MinPolyCert.Prefix F n j
  | 0, _ => { running := 1, order := #v[], steps := #v[] }
  | j + 1, hj =>
      let previous := MinPolyCert.prefix A j (by omega)
      let order := orderCert A (basisVec n ⟨j, by omega⟩)
      let step := lcmStep previous.running order.poly
      { running := step.result
        order := previous.order.push order
        steps := previous.steps.push step }

private theorem certPrefix_running (A : Matrix F n n) (j : Nat) (hj : j ≤ n) :
    (MinPolyCert.prefix A j hj).running = basisOrderLcmPrefix A j hj := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [MinPolyCert.prefix]
      dsimp only
      have hprevious := ih (by omega)
      have hs := lcmStep_sound
        (basisOrderLcmPrefix A j (by omega))
        (vecMinPoly A (basisVec n ⟨j, by omega⟩))
        (basisOrderLcmPrefix_monic A j (by omega))
        (vecMinPoly_monic A (basisVec n ⟨j, by omega⟩))
      change (lcmStep (MinPolyCert.prefix A j _).running
        (vecMinPoly A (basisVec n ⟨j, by omega⟩))).result = _
      rw [hprevious, hs.2.2.2.2.1, basisOrderLcmPrefix_succ]

private theorem certPrefix_order (A : Matrix F n n) (j : Nat) (hj : j ≤ n)
    (i : Fin j) :
    (MinPolyCert.prefix A j hj).order.get i =
      orderCert A (basisVec n ⟨i.val, Nat.lt_of_lt_of_le i.isLt hj⟩) := by
  induction j with
  | zero => exact Fin.elim0 i
  | succ j ih =>
      rw [MinPolyCert.prefix]
      dsimp only
      by_cases hi : i.val < j
      · change ((MinPolyCert.prefix A j _).order.push _)[i.val] = _
        rw [Vector.getElem_push_lt hi]
        exact ih (by omega) ⟨i.val, hi⟩
      · have hilast : i.val = j := by omega
        have hiFin : i = ⟨j, by omega⟩ := Fin.eq_of_val_eq hilast
        rw [hiFin]
        change ((MinPolyCert.prefix A j _).order.push _)[j] = _
        rw [Vector.getElem_push_eq]

private theorem certPrefix_steps (A : Matrix F n n) (j : Nat) (hj : j ≤ n)
    (i : Fin j) :
    (MinPolyCert.prefix A j hj).steps.get i =
      lcmStep (basisOrderLcmPrefix A i.val (by omega))
        (vecMinPoly A (basisVec n ⟨i.val, by omega⟩)) := by
  induction j with
  | zero => exact Fin.elim0 i
  | succ j ih =>
      rw [MinPolyCert.prefix]
      dsimp only
      by_cases hi : i.val < j
      · change ((MinPolyCert.prefix A j _).steps.push _)[i.val] = _
        rw [Vector.getElem_push_lt hi]
        exact ih (by omega) ⟨i.val, hi⟩
      · have hilast : i.val = j := by omega
        have hiFin : i = ⟨j, by omega⟩ := Fin.eq_of_val_eq hilast
        rw [hiFin]
        change ((MinPolyCert.prefix A j _).steps.push _)[j] = _
        rw [Vector.getElem_push_eq]
        rw [certPrefix_running]
        rfl

/-- Produce a complete basis-wide minimal-polynomial certificate. -/
@[expose]
def minPolyCert (A : Matrix F n n) : MinPolyCert F n :=
  let built := MinPolyCert.prefix A n (Nat.le_refl n)
  { poly := built.running
    order := built.order
    steps := built.steps }

@[simp, grind =]
theorem minPolyCert_order (A : Matrix F n n) (i : Fin n) :
    (minPolyCert A).order.get i = orderCert A (basisVec n i) := by
  unfold minPolyCert
  exact certPrefix_order A n (Nat.le_refl n) i

@[simp, grind =]
theorem minPolyCert_steps (A : Matrix F n n) (i : Fin n) :
    (minPolyCert A).steps.get i =
      lcmStep (basisOrderLcmPrefix A i.val (by omega))
        (vecMinPoly A (basisVec n i)) := by
  unfold minPolyCert
  exact certPrefix_steps A n (Nat.le_refl n) i

/-- The producer's step array agrees with its mathematical prefix fold. -/
theorem minPolyCert_running (A : Matrix F n n) (j : Nat) (hj : j ≤ n) :
    (minPolyCert A).running j hj = basisOrderLcmPrefix A j hj := by
  cases j with
  | zero => rfl
  | succ j =>
      have hs := lcmStep_sound
        (basisOrderLcmPrefix A j (by omega))
        (vecMinPoly A (basisVec n ⟨j, by omega⟩))
        (basisOrderLcmPrefix_monic A j (by omega))
        (vecMinPoly_monic A (basisVec n ⟨j, by omega⟩))
      have hresult := hs.2.2.2.2.1
      rw [MinPolyCert.running]
      simp only [minPolyCert]
      rw [certPrefix_steps]
      change (lcmStep (basisOrderLcmPrefix A j (by omega))
        (vecMinPoly A (basisVec n ⟨j, by omega⟩))).result =
          basisOrderLcmPrefix A (j + 1) hj
      rw [hresult, basisOrderLcmPrefix_succ]

/-- The producer records the executable minimal polynomial as its claim. -/
theorem minPolyCert_poly (A : Matrix F n n) :
    (minPolyCert A).poly = minPoly A := by
  dsimp only [minPolyCert]
  change (MinPolyCert.prefix A n _).running = minPoly A
  unfold minPoly
  rw [certPrefix_running, basisOrderLcmPrefix_all]

/-- Certificates produced from row reduction and extended gcd pass the
kernel-reducible checker. -/
theorem minPolyCert_check (A : Matrix F n n) :
    (minPolyCert A).check A = true := by
  unfold MinPolyCert.check
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro i hi
    have hright : checkRightInverse
        (krylovMat A (basisVec n i) (krylovDeg A (basisVec n i)))
        (krylovRightInverseCandidate A (basisVec n i)
          (krylovDeg A (basisVec n i))) = true :=
      checkRightInverse_complete _ _
        (krylovRightInverseCandidate_sound A (basisVec n i))
    have horder :
        (((vecMinPoly A (basisVec n i)).size = krylovDeg A (basisVec n i) + 1 ∧
          (vecMinPoly A (basisVec n i)).coeff (krylovDeg A (basisVec n i)) = 1) ∧
          evalVec (vecMinPoly A (basisVec n i)) A (basisVec n i) = 0) ∧
          checkRightInverse
            (krylovMat A (basisVec n i) (krylovDeg A (basisVec n i)))
            (krylovRightInverseCandidate A (basisVec n i)
              (krylovDeg A (basisVec n i))) = true :=
      ⟨⟨⟨size_vecMinPoly A (basisVec n i),
        coeff_vecMinPoly_degree A (basisVec n i)⟩,
        evalVec_vecMinPoly A (basisVec n i)⟩, hright⟩
    rw [minPolyCert_order]
    exact horder
  · intro j hj
    have hs := lcmStep_sound
      (basisOrderLcmPrefix A j.val (by omega))
      (vecMinPoly A (basisVec n j))
      (basisOrderLcmPrefix_monic A j.val (by omega))
      (vecMinPoly_monic A (basisVec n j))
    have hrun := minPolyCert_running A j.val (by omega)
    rw [minPolyCert_steps, minPolyCert_order]
    rw [hrun]
    exact ⟨⟨⟨hs.1, hs.2.1⟩, hs.2.2.1⟩, hs.2.2.2.1⟩
  · rw [minPolyCert_poly, minPolyCert_running, basisOrderLcmPrefix_all]
    rfl
  · have hmonic := minPoly_monic A
    have hne : minPoly A ≠ 0 := DensePoly.monic_ne_zero hmonic
    have hpos : 0 < (minPoly A).size := by
      by_cases h : 0 < (minPoly A).size
      · exact h
      · exact False.elim (hne ((DensePoly.size_eq_zero_iff (minPoly A)).mp
          (Nat.eq_zero_of_not_pos h)))
    rw [minPolyCert_poly]
    change (minPoly A).coeff ((minPoly A).size - 1) = 1
    rw [← DensePoly.leadingCoeff_eq_coeff_last (minPoly A) hpos, hmonic]

end Hex.Matrix

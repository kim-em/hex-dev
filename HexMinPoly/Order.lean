/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMinPoly.Krylov
public import HexRowReduce
import HexPoly.Lcm

public section

/-! Order polynomials of vectors from their first Krylov dependency. -/

namespace Hex.Matrix

universe u

variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F] {n : Nat}

private theorem size_eq_succ_of_degree_eq_some (p : DensePoly F) {k : Nat}
    (hdegree : p.degree? = some k) : p.size = k + 1 := by
  have hpos : 0 < p.size := by
    by_cases h : 0 < p.size
    · exact h
    · have hzero : p.size = 0 := Nat.eq_zero_of_not_pos h
      have hnone := (DensePoly.degree?_eq_none_iff p).2 hzero
      rw [hdegree] at hnone
      contradiction
  have hsome := DensePoly.degree?_eq_some_of_pos_size p hpos
  rw [hdegree] at hsome
  injection hsome with hk
  omega

/-- Every Krylov iterate lies in the prefix cut out by a monic annihilator. -/
private theorem krylovVec_mem_of_monic_annihilator (A : Matrix F n n)
    (v : Vector F n) (q : DensePoly F) (k j : Nat) (hqMonic : q.Monic)
    (hqDegree : q.degree? = some k) (hqEval : evalVec q A v = 0) :
    ∃ c : Vector F k, vecMul c (krylovMat A v k) = krylovVec A v j := by
  by_cases hk : k = 0
  · subst k
    have hqSize : q.size = 1 := by
      simpa using size_eq_succ_of_degree_eq_some q hqDegree
    have hq : q = 1 := by
      apply DensePoly.ext_coeff
      intro i
      change q.coeff i = (DensePoly.C (1 : F)).coeff i
      rw [DensePoly.coeff_C]
      by_cases hi : i = 0
      · subst i
        rw [_root_.ite_eq_left rfl]
        have hlc := DensePoly.leadingCoeff_eq_coeff_last q (by omega)
        rw [hqSize] at hlc
        exact hlc.symm.trans hqMonic
      · rw [_root_.ite_eq_right hi]
        exact DensePoly.coeff_eq_zero_of_size_le q (by omega)
    have hv : v = 0 := by
      rw [hq] at hqEval
      change evalVec (DensePoly.C (1 : F)) A v = 0 at hqEval
      rw [evalVec_C] at hqEval
      ext j hj
      have hentry := congrArg (fun w : Vector F n => w[j]) hqEval
      simp only [Vector.getElem_smul, Vector.getElem_zero] at hentry
      change (1 : F) * v[j] = 0 at hentry
      grind
    refine ⟨0, ?_⟩
    rw [Matrix.vecMul_zero, hv, krylovVec_zero]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
    have hqLead : q.leadingCoeff = 1 := hqMonic
    have hcancel : ∀ a : F,
        a - (a / q.leadingCoeff) * q.leadingCoeff = (0 : F) := by
      intro a
      rw [hqLead]
      grind
    let p := DensePoly.monomial j (1 : F)
    let qr := DensePoly.divMod p q
    let rem := qr.2
    have hremDegree : rem.degree?.getD 0 < k := by
      have h := DensePoly.divMod_remainder_degree_lt_of_pos_degree_of_cancel
        p q (by rw [hqDegree]; exact hkPos) hcancel
      simpa [qr, rem, hqDegree] using h
    have hremSize : rem.size ≤ k := by
      by_cases hzero : rem.size = 0
      · omega
      · have hpos : 0 < rem.size := Nat.pos_of_ne_zero hzero
        have hdegree := DensePoly.degree?_eq_some_of_pos_size rem hpos
        have hdegreeVal : rem.degree?.getD 0 = rem.size - 1 := by
          rw [hdegree, Option.getD_some]
        rw [hdegreeVal] at hremDegree
        omega
    refine ⟨rem.coeffVec k, ?_⟩
    rw [← evalVec_eq_vecMul_krylov rem A v k hremSize]
    have hrecon := DensePoly.divMod_reconstruction p q hcancel
    change qr.1 * q + rem = p at hrecon
    have hev := congrArg (fun s : DensePoly F => evalVec s A v) hrecon
    rw [evalVec_add_poly, evalVec_mul, hqEval, evalVec_zero,
      evalVec_monomial] at hev
    ext t ht
    have hentry := congrArg (fun w : Vector F n => w[t]) hev
    simp only [Vector.getElem_add, Vector.getElem_zero, Vector.getElem_smul] at hentry
    change (0 : F) + (evalVec rem A v)[t] =
      (1 : F) * (krylovVec A v j)[t] at hentry
    grind

/-- A monic annihilator bounds the rank of the full Krylov matrix by its
degree.  This is the operational form of cyclic-span closure used by the
prefix argument below. -/
private theorem rank_le_of_monic_annihilator (A : Matrix F n n) (v : Vector F n)
    (q : DensePoly F) (k : Nat) (hqMonic : q.Monic)
    (hqDegree : q.degree? = some k) (hqEval : evalVec q A v = 0) :
    rowReduce_rank (krylovMat A v (n + 1)) ≤ k := by
  apply rowReduce_rank_le_of_rows_span
    (krylovMat A v (n + 1)) (krylovMat A v k)
  intro i
  have hmem := krylovVec_mem_of_monic_annihilator A v q k i.val
    hqMonic hqDegree hqEval
  rcases hmem with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  change vecMul c (krylovMat A v k) = Matrix.getRow (krylovMat A v (n + 1)) i
  rw [getRow_krylovMat]
  exact hc

/-- The rank of the full Krylov matrix, hence the order-polynomial degree. -/
@[expose]
def krylovDeg (A : Matrix F n n) (v : Vector F n) : Nat :=
  rowReduce_rank (krylovMat A v (n + 1))

/-- The order-polynomial degree cannot exceed the ambient dimension. -/
theorem krylovDeg_le (A : Matrix F n n) (v : Vector F n) : krylovDeg A v ≤ n := by
  simpa [krylovDeg, rowReduce_rank] using
    rowReduce_rank_le_m (krylovMat A v (n + 1))

private theorem exists_monic_annihilator_le (A : Matrix F n n) (v : Vector F n) :
    ∃ q : DensePoly F, ∃ k : Nat, k ≤ krylovDeg A v ∧ q.Monic ∧
      q.degree? = some k ∧ evalVec q A v = 0 := by
  let d := krylovDeg A v
  have hd : d ≤ n := krylovDeg_le A v
  let K := krylovMat A v (n + 1)
  have hfactor : ∃ C : Matrix F (n + 1) d, ∃ B : Matrix F d n,
      K = C * B := by
    have hdEq : rowReduce_rank K = d := by rfl
    have hf := rowReduce_rank_factorization K
    rw [hdEq] at hf
    exact hf
  rcases hfactor with ⟨C, B, hK⟩
  let Cpre : Matrix F (d + 1) d := Matrix.takeRows C (d + 1) (by
    change d + 1 ≤ n + 1
    omega)
  let Kpre := krylovMat A v (d + 1)
  have hKpre : Kpre = Cpre * B := by
    apply Matrix.ext_getElem
    intro i j
    let ii : Fin (n + 1) :=
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by omega)⟩
    calc
      Kpre[i][j] = K[ii][j] := by
        change (Matrix.getRow (krylovMat A v (d + 1)) i)[j] =
          (Matrix.getRow (krylovMat A v (n + 1)) ii)[j]
        rw [getRow_krylovMat, getRow_krylovMat]
      _ = (C * B)[ii][j] := congrArg (fun X : Matrix F (n + 1) n => X[ii][j]) hK
      _ = (Cpre * B)[i][j] := by
        rw [Matrix.getElem_mul, Matrix.getElem_mul]
        congr 1
        simp only [Cpre, Matrix.row_takeRows]
        congr 1
  let CT := Matrix.transpose Cpre
  have hCTRank : rowReduce_rank CT ≤ d := by
    exact rowReduce_rank_le_n CT
  have hnullPos : 0 < (d + 1) - rowReduce_rank CT := by omega
  let z : Fin ((d + 1) - rowReduce_rank CT) := ⟨0, hnullPos⟩
  let a : Vector F (d + 1) := (nullspace CT).get z
  have haNe : a ≠ 0 := nullspace_ne_zero CT z
  have haCT : CT * a = 0 := nullspace_sound CT z
  have haC : vecMul a Cpre = 0 := by
    change Matrix.transpose Cpre * a = 0
    exact haCT
  have hcomb : vecMul a Kpre = 0 := by
    calc
      vecMul a Kpre = vecMul a (Cpre * B) := by rw [hKpre]
      _ = vecMul (vecMul a Cpre) B := (Matrix.vecMul_mul a Cpre B).symm
      _ = vecMul (0 : Vector F d) B := by rw [haC]
      _ = 0 := Matrix.vecMul_zero B
  let p := DensePoly.ofList a.toList
  have hpSize : p.size ≤ d + 1 := by
    exact Nat.le_trans (DensePoly.size_ofList_le a.toList) (by simp [Vector.length_toList])
  have hpCoeff : p.coeffVec (d + 1) = a := by
    apply Vector.ext
    intro i hi
    let ii : Fin (d + 1) := ⟨i, hi⟩
    have hiList : i < a.toList.length := by simpa [Vector.length_toList]
    change (p.coeffVec (d + 1)).get ii = a.get ii
    rw [DensePoly.coeffVec_get]
    simp [p, DensePoly.coeff_ofList, List.getD, Vector.getElem_toList]
    rfl
  have hpNe : p ≠ 0 := by
    intro hp
    apply haNe
    rw [← hpCoeff, hp]
    apply Vector.ext
    intro i hi
    let ii : Fin (d + 1) := ⟨i, hi⟩
    change ((0 : DensePoly F).coeffVec (d + 1)).get ii =
      (0 : Vector F (d + 1)).get ii
    rw [DensePoly.coeffVec_get, DensePoly.coeff_zero]
    change (0 : F) = (0 : Vector F (d + 1))[i]
    rw [Vector.getElem_zero]
  have hpEval : evalVec p A v = 0 := by
    rw [evalVec_eq_vecMul_krylov p A v (d + 1) hpSize, hpCoeff, hcomb]
  have hpPos : 0 < p.size := by
    by_cases h : 0 < p.size
    · exact h
    · exact False.elim (hpNe ((DensePoly.size_eq_zero_iff p).mp
        (Nat.eq_zero_of_not_pos h)))
  let k := p.size - 1
  have hk : k ≤ d := by omega
  have hpDegree : p.degree? = some k := by
    exact DensePoly.degree?_eq_some_of_pos_size p hpPos
  let q := DensePoly.monicize p
  refine ⟨q, k, hk, DensePoly.monicize_monic hpNe, ?_, ?_⟩
  · have hqPos : 0 < q.size := by
      simp only [q, DensePoly.size_monicize]
      exact hpPos
    rw [DensePoly.degree?_eq_some_of_pos_size q hqPos]
    simp only [q, DensePoly.size_monicize]
    rfl
  · have hisZero : p.isZero = false := by
      rw [← Bool.not_eq_true]
      intro h
      exact hpNe ((DensePoly.size_eq_zero_iff p).mp
        ((DensePoly.isZero_eq_true_iff p).mp h))
    have hnot : ¬ p.isZero = true := by
      intro h
      rw [h] at hisZero
      cases hisZero
    change evalVec (DensePoly.monicize p) A v = 0
    unfold DensePoly.monicize
    rw [HexPoly.ite_eq_right hnot, evalVec_scale_poly, hpEval]
    ext i hi
    simp only [Vector.getElem_smul, Vector.getElem_zero]
    change p.leadingCoeff⁻¹ * (0 : F) = 0
    grind

omit [DecidableEq F] in
private theorem takeRows_krylovMat (A : Matrix F n n) (v : Vector F n)
    (d r : Nat) (hd : d ≤ r) :
    Matrix.takeRows (krylovMat A v r) d hd = krylovMat A v d := by
  apply Matrix.ext_getElem
  intro i j
  rw [Matrix.getElem_takeRows]
  change (Matrix.getRow (krylovMat A v r)
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt hd⟩)[j] =
    (Matrix.getRow (krylovMat A v d) i)[j]
  rw [getRow_krylovMat, getRow_krylovMat]

/-- Coefficients of the first Krylov dependency, in ascending order.
The prefix and its next vector are sliced from one shared Krylov array. -/
@[expose]
def krylovCoeffs? (A : Matrix F n n) (v : Vector F n) :
    Option (Vector F (krylovDeg A v)) :=
  let rows := krylovRows A v (n + 1)
  let full := Matrix.ofRows rows
  let d := rowReduce_rank full
  have hd : d ≤ n := by
    change krylovDeg A v ≤ n
    exact krylovDeg_le A v
  let answer : Option (Vector F d) :=
    spanCoeffs (n := d)
      (Matrix.takeRows full d (Nat.le_trans hd (by omega)))
      (rows.get ⟨d, by omega⟩)
  answer

/-- Proof-facing characterization of the shared Krylov dependency kernel. -/
theorem krylovCoeffs?_eq_span (A : Matrix F n n) (v : Vector F n) :
    krylovCoeffs? A v =
      spanCoeffs (krylovMat A v (krylovDeg A v))
        (krylovVec A v (krylovDeg A v)) := by
  dsimp only [krylovCoeffs?]
  simp only [krylovDeg]
  change spanCoeffs
      (Matrix.takeRows (krylovMat A v (n + 1))
        (rowReduce_rank (krylovMat A v (n + 1))) _)
      ((krylovRows A v (n + 1)).get
        ⟨rowReduce_rank (krylovMat A v (n + 1)), _⟩) = _
  congr 1
  · exact takeRows_krylovMat A v
      (rowReduce_rank (krylovMat A v (n + 1))) (n + 1)
      (Nat.le_trans (krylovDeg_le A v) (by omega))
  · exact krylovRows_get A v
      (⟨rowReduce_rank (krylovMat A v (n + 1)),
        Nat.lt_succ_of_le (krylovDeg_le A v)⟩ : Fin (n + 1))

/-- The first Krylov dependency always exists. -/
theorem krylovCoeffs_isSome (A : Matrix F n n) (v : Vector F n) :
    (krylovCoeffs? A v).isSome := by
  rcases exists_monic_annihilator_le A v with
    ⟨q, k, hk, hqMonic, hqDegree, hqEval⟩
  have hdk : krylovDeg A v ≤ k := by
    simpa [krylovDeg] using
      rank_le_of_monic_annihilator A v q k hqMonic hqDegree hqEval
  have hkd : k = krylovDeg A v := Nat.le_antisymm hk hdk
  subst k
  rcases krylovVec_mem_of_monic_annihilator A v q (krylovDeg A v)
      (krylovDeg A v) hqMonic hqDegree hqEval with ⟨c, hc⟩
  rw [krylovCoeffs?_eq_span]
  cases hcoeff : spanCoeffs (krylovMat A v (krylovDeg A v))
      (krylovVec A v (krylovDeg A v)) with
  | none =>
      have hnone := (spanCoeffs_eq_none_iff
        (krylovMat A v (krylovDeg A v))
        (krylovVec A v (krylovDeg A v))).1 hcoeff
      exact False.elim (hnone ⟨c, hc⟩)
  | some c => rfl

/-- Assemble `x^d - Σ j, c_j x^j` from ascending dependency coefficients. -/
@[expose]
def dependencyPoly {d : Nat} (c : Vector F d) : DensePoly F :=
  DensePoly.monomial d 1 - DensePoly.ofList c.toList

private theorem dependencyPoly_coeff_top {d : Nat} (c : Vector F d) :
    (dependencyPoly c).coeff d = 1 := by
  rw [dependencyPoly, DensePoly.coeff_sub_ring, DensePoly.coeff_monomial,
    _root_.ite_eq_left rfl, DensePoly.coeff_ofList]
  have hout : ¬ d < c.toList.length := by simp [Vector.length_toList]
  simp [List.getD]
  change (1 : F) - (0 : F) = 1
  grind

private theorem dependencyPoly_size {d : Nat} (c : Vector F d) :
    (dependencyPoly c).size = d + 1 := by
  have hle : (dependencyPoly c).size ≤ d + 1 := by
    apply Nat.le_of_not_gt
    intro hgt
    have hpos : 0 < (dependencyPoly c).size := by omega
    let s := (dependencyPoly c).size - 1
    have hi : d < s := by omega
    have hlast : (dependencyPoly c).coeff s ≠ 0 := by
      exact DensePoly.coeff_last_ne_zero_of_pos_size (dependencyPoly c) hpos
    have hz : (dependencyPoly c).coeff s = 0 := by
      change (DensePoly.monomial d 1 - DensePoly.ofList c.toList).coeff s = 0
      rw [DensePoly.coeff_sub_ring, DensePoly.coeff_monomial,
        _root_.ite_eq_right (by omega), DensePoly.coeff_ofList]
      have hout : ¬ s < c.toList.length := by
        simp [Vector.length_toList]
        omega
      simp [List.getD]
      grind
    exact hlast hz
  have hnot : ¬ (dependencyPoly c).size ≤ d := by
    intro h
    have hz := DensePoly.coeff_eq_zero_of_size_le (dependencyPoly c) h
    rw [dependencyPoly_coeff_top] at hz
    exact Lean.Grind.Field.zero_ne_one hz.symm
  omega

/-- A dependency polynomial is monic. -/
theorem dependencyPoly_monic {d : Nat} (c : Vector F d) :
    (dependencyPoly c).Monic := by
  rw [DensePoly.monic_iff_leadingCoeff_eq_one,
    DensePoly.leadingCoeff_eq_coeff_last _ (by rw [dependencyPoly_size]; omega),
    dependencyPoly_size]
  simpa using dependencyPoly_coeff_top c

/-- A dependency polynomial has degree equal to the dependency length. -/
theorem degree?_dependencyPoly {d : Nat} (c : Vector F d) :
    (dependencyPoly c).degree? = some d := by
  rw [DensePoly.degree?_eq_some_of_pos_size _ (by rw [dependencyPoly_size]; omega),
    dependencyPoly_size]
  congr

private theorem coeffVec_ofList_vector {d : Nat} (c : Vector F d) :
    (DensePoly.ofList c.toList).coeffVec d = c := by
  apply Vector.ext
  intro i hi
  let ii : Fin d := ⟨i, hi⟩
  change ((DensePoly.ofList c.toList).coeffVec d).get ii = c.get ii
  rw [DensePoly.coeffVec_get, DensePoly.coeff_ofList]
  simp [List.getD, Vector.getElem_toList]
  rfl

private theorem evalVec_sub_poly (p q : DensePoly F) (A : Matrix F n n)
    (v : Vector F n) :
    evalVec (p - q) A v = evalVec p A v - evalVec q A v := by
  have hsub : p - q = p + DensePoly.scale (-1 : F) q := by
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_sub_ring, DensePoly.coeff_add_semiring,
      DensePoly.coeff_scale_semiring]
    grind
  rw [hsub, evalVec_add_poly, evalVec_scale_poly]
  ext i hi
  simp only [Vector.getElem_add, Vector.getElem_smul, Vector.getElem_sub]
  change (evalVec p A v)[i] + (-1 : F) * (evalVec q A v)[i] =
    (evalVec p A v)[i] - (evalVec q A v)[i]
  grind

private theorem evalVec_dependencyPoly_of_span {d : Nat} (A : Matrix F n n)
    (v : Vector F n) (c : Vector F d)
    (hc : vecMul c (krylovMat A v d) = krylovVec A v d) :
    evalVec (dependencyPoly c) A v = 0 := by
  let lower := DensePoly.ofList c.toList
  have hlowerSize : lower.size ≤ d := by
    exact Nat.le_trans (DensePoly.size_ofList_le c.toList) (by simp [Vector.length_toList])
  have hlowerEval : evalVec lower A v = krylovVec A v d := by
    rw [evalVec_eq_vecMul_krylov lower A v d hlowerSize,
      coeffVec_ofList_vector, hc]
  rw [dependencyPoly, evalVec_sub_poly, evalVec_monomial,
    hlowerEval]
  ext i hi
  simp only [Vector.getElem_sub, Vector.getElem_smul, Vector.getElem_zero]
  change (1 : F) * (krylovVec A v d)[i] - (krylovVec A v d)[i] = 0
  grind

/-- The order polynomial of `v`.  The `none` branch is unreachable by the
Krylov prefix invariant and is kept only to make the function total. -/
@[expose]
def vecMinPoly (A : Matrix F n n) (v : Vector F n) : DensePoly F :=
  match krylovCoeffs? A v with
  | some c => dependencyPoly c
  | none => 1

/-- The vector order polynomial is monic. -/
theorem vecMinPoly_monic (A : Matrix F n n) (v : Vector F n) :
    (vecMinPoly A v).Monic := by
  cases h : krylovCoeffs? A v with
  | none =>
      have hs := krylovCoeffs_isSome A v
      rw [h] at hs
      contradiction
  | some c =>
      rw [vecMinPoly, h]
      exact dependencyPoly_monic c

/-- The vector order polynomial has the computed Krylov degree. -/
theorem degree?_vecMinPoly (A : Matrix F n n) (v : Vector F n) :
    (vecMinPoly A v).degree? = some (krylovDeg A v) := by
  cases h : krylovCoeffs? A v with
  | none =>
      have hs := krylovCoeffs_isSome A v
      rw [h] at hs
      contradiction
  | some c =>
      rw [vecMinPoly, h]
      exact degree?_dependencyPoly c

/-- The stored coefficient length of the vector order polynomial. -/
theorem size_vecMinPoly (A : Matrix F n n) (v : Vector F n) :
    (vecMinPoly A v).size = krylovDeg A v + 1 :=
  size_eq_succ_of_degree_eq_some _ (degree?_vecMinPoly A v)

/-- The coefficient at the computed Krylov degree is the monic leading
coefficient. -/
theorem coeff_vecMinPoly_degree (A : Matrix F n n) (v : Vector F n) :
    (vecMinPoly A v).coeff (krylovDeg A v) = 1 := by
  have hsize := size_vecMinPoly A v
  have hpos : 0 < (vecMinPoly A v).size := by omega
  calc
    (vecMinPoly A v).coeff (krylovDeg A v) =
        (vecMinPoly A v).coeff ((vecMinPoly A v).size - 1) := by congr; omega
    _ = (vecMinPoly A v).leadingCoeff :=
      (DensePoly.leadingCoeff_eq_coeff_last (vecMinPoly A v) hpos).symm
    _ = 1 := vecMinPoly_monic A v

/-- The vector order polynomial annihilates its vector. -/
theorem evalVec_vecMinPoly (A : Matrix F n n) (v : Vector F n) :
    evalVec (vecMinPoly A v) A v = 0 := by
  cases h : krylovCoeffs? A v with
  | none =>
      have hs := krylovCoeffs_isSome A v
      rw [h] at hs
      contradiction
  | some c =>
      have hc : vecMul c (krylovMat A v (krylovDeg A v)) =
          krylovVec A v (krylovDeg A v) := by
        apply spanCoeffs_sound
        rw [← krylovCoeffs?_eq_span]
        exact h
      rw [vecMinPoly, h]
      exact evalVec_dependencyPoly_of_span A v c hc

/-- The first `krylovDeg` Krylov rows are independent. -/
theorem rowReduce_rank_krylovPrefix (A : Matrix F n n) (v : Vector F n) :
    rowReduce_rank (krylovMat A v (krylovDeg A v)) = krylovDeg A v := by
  let d := krylovDeg A v
  let P := krylovMat A v d
  let K := krylovMat A v (n + 1)
  rcases rowReduce_rank_factorization P with ⟨C, B, hP⟩
  have hspan : ∀ i : Fin (n + 1), ∃ a : Vector F (rowReduce_rank P),
      vecMul a B = Matrix.row K i := by
    intro i
    have hmem := krylovVec_mem_of_monic_annihilator A v (vecMinPoly A v) d i.val
      (vecMinPoly_monic A v) (degree?_vecMinPoly A v) (evalVec_vecMinPoly A v)
    rcases hmem with ⟨c, hc⟩
    refine ⟨vecMul c C, ?_⟩
    calc
      vecMul (vecMul c C) B = vecMul c (C * B) := Matrix.vecMul_mul c C B
      _ = vecMul c P := by rw [← hP]
      _ = krylovVec A v i.val := hc
      _ = Matrix.row K i := by
        change krylovVec A v i.val = Matrix.getRow (krylovMat A v (n + 1)) i
        rw [getRow_krylovMat]
  have hlower : d ≤ rowReduce_rank P := by
    change rowReduce_rank K ≤ rowReduce_rank P
    exact rowReduce_rank_le_of_rows_span K B hspan
  have hupper : rowReduce_rank P ≤ d := rowReduce_rank_le_n P
  exact Nat.le_antisymm hupper hlower

/-- The vector order polynomial divides every annihilator of the vector. -/
theorem vecMinPoly_dvd (A : Matrix F n n) (v : Vector F n) (p : DensePoly F) :
    evalVec p A v = 0 → vecMinPoly A v ∣ p := by
  intro hpEval
  let m := vecMinPoly A v
  let d := krylovDeg A v
  let qr := DensePoly.divMod p m
  have hmMonic : m.Monic := vecMinPoly_monic A v
  have hmDegree : m.degree? = some d := degree?_vecMinPoly A v
  have hmSize : m.size = d + 1 := size_eq_succ_of_degree_eq_some m hmDegree
  have hmEval : evalVec m A v = 0 := evalVec_vecMinPoly A v
  have hcancel : ∀ a : F,
      a - (a / m.leadingCoeff) * m.leadingCoeff = (0 : F) := by
    intro a
    rw [show m.leadingCoeff = 1 from hmMonic]
    grind
  have hrecon : qr.1 * m + qr.2 = p :=
    DensePoly.divMod_reconstruction p m hcancel
  have hremEval : evalVec qr.2 A v = 0 := by
    have hev := congrArg (fun q : DensePoly F => evalVec q A v) hrecon
    rw [evalVec_add_poly, evalVec_mul, hmEval, evalVec_zero, hpEval] at hev
    calc
      evalVec qr.2 A v = 0 + evalVec qr.2 A v := by
        ext i hi
        simp only [Vector.getElem_add, Vector.getElem_zero]
        grind
      _ = 0 := hev
  have hrem : qr.2 = 0 := by
    by_cases hd : d = 0
    · apply DensePoly.divMod_remainder_eq_zero_of_degree_zero_of_cancel p m
      · omega
      · exact hcancel
    · have hdPos : 0 < d := Nat.pos_of_ne_zero hd
      have hremDegree : qr.2.degree?.getD 0 < d := by
        have h := DensePoly.divMod_remainder_degree_lt_of_pos_degree_of_cancel
          p m (by rw [hmDegree]; exact hdPos) hcancel
        simpa [hmDegree] using h
      by_cases hr : qr.2 = 0
      · exact hr
      · have hrPos : 0 < qr.2.size := by
          by_cases hs : 0 < qr.2.size
          · exact hs
          · exact False.elim (hr ((DensePoly.size_eq_zero_iff qr.2).mp
              (Nat.eq_zero_of_not_pos hs)))
        let k := qr.2.size - 1
        have hrDegree : qr.2.degree? = some k :=
          DensePoly.degree?_eq_some_of_pos_size qr.2 hrPos
        have hklt : k < d := by
          have hkval : qr.2.degree?.getD 0 = k := by
            rw [hrDegree, Option.getD_some]
          rw [hkval] at hremDegree
          exact hremDegree
        let rmonic := DensePoly.monicize qr.2
        have hrMonic : rmonic.Monic := DensePoly.monicize_monic hr
        have hrMonicDegree : rmonic.degree? = some k := by
          have hpos : 0 < rmonic.size := by
            simp only [rmonic, DensePoly.size_monicize]
            exact hrPos
          rw [DensePoly.degree?_eq_some_of_pos_size rmonic hpos]
          simp only [rmonic, DensePoly.size_monicize, k]
        have hrMonicEval : evalVec rmonic A v = 0 := by
          have hisZero : qr.2.isZero = false := by
            rw [← Bool.not_eq_true]
            intro h
            exact hr ((DensePoly.size_eq_zero_iff qr.2).mp
              ((DensePoly.isZero_eq_true_iff qr.2).mp h))
          have hnot : ¬ qr.2.isZero = true := by
            intro h
            rw [h] at hisZero
            cases hisZero
          change evalVec (DensePoly.monicize qr.2) A v = 0
          unfold DensePoly.monicize
          rw [HexPoly.ite_eq_right hnot, evalVec_scale_poly, hremEval]
          ext i hi
          simp only [Vector.getElem_smul, Vector.getElem_zero]
          change qr.2.leadingCoeff⁻¹ * (0 : F) = 0
          grind
        have hdk : d ≤ k := by
          simpa [d, krylovDeg] using
            rank_le_of_monic_annihilator A v rmonic k hrMonic
              hrMonicDegree hrMonicEval
        omega
  refine ⟨qr.1, ?_⟩
  rw [← hrecon, hrem, DensePoly.add_zero_poly, DensePoly.mul_comm_poly]

end Hex.Matrix

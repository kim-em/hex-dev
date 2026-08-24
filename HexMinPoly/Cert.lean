/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMinPoly.MinPoly

public section

/-! Division-free certificates for matrix minimal polynomials. -/

namespace Hex.Matrix

universe u

/-- A claimed vector order polynomial and a right inverse witnessing
independence of the preceding Krylov rows. -/
structure OrderCert (F : Type u) [Zero F] [DecidableEq F] (n : Nat) where
  poly : DensePoly F
  deg : Nat
  inv : Matrix F n deg

/-- Ring-identity data certifying one least-common-multiple fold step. -/
structure LcmStep (F : Type u) [Zero F] [DecidableEq F] where
  common : DensePoly F
  left : DensePoly F
  right : DensePoly F
  bezoutLeft : DensePoly F
  bezoutRight : DensePoly F
  result : DensePoly F

/-- A basis-wide certificate.  Its vector indices enforce complete coverage. -/
structure MinPolyCert (F : Type u) [Zero F] [DecidableEq F] (n : Nat) where
  poly : DensePoly F
  order : Vector (OrderCert F n) n
  steps : Vector (LcmStep F) n

variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F] {n : Nat}

/-- Running value before step `j`. -/
@[expose]
def MinPolyCert.running (c : MinPolyCert F n) : (j : Nat) → j ≤ n → DensePoly F
  | 0, _ => 1
  | j + 1, hj => (c.steps.get ⟨j, by omega⟩).result

/-- Check `K * inv = I` one column at a time, using only matrix-vector products. -/
@[expose]
def checkRightInverse {d : Nat} (K : Matrix F d n) (inv : Matrix F n d) : Bool :=
  (List.finRange d).all fun j =>
    decide (K * Matrix.col inv j = basisVec d j)

/-- A successful columnwise check is the corresponding matrix right-inverse
identity. -/
theorem checkRightInverse_sound {d : Nat} (K : Matrix F d n) (inv : Matrix F n d)
    (h : checkRightInverse K inv = true) :
    K * inv = Matrix.identity (R := F) d := by
  unfold checkRightInverse at h
  simp only [List.all_eq_true] at h
  apply Matrix.ext_getElem
  intro i j
  have hj := h j (List.mem_finRange j)
  have hcol : K * Matrix.col inv j = basisVec d j := by
    exact of_decide_eq_true hj
  calc
    (K * inv)[i][j] = (K * Matrix.col inv j)[i] := by
      rw [Matrix.getElem_mul, Matrix.getElem_mulVec]
    _ = (basisVec d j)[i] := by rw [hcol]
    _ = (Matrix.identity (R := F) d)[i][j] := by
      unfold basisVec
      rw [Matrix.getElem_row, Matrix.getElem_identity, Matrix.getElem_identity]
      by_cases hij : i = j <;> simp [hij, eq_comm]

/-- A matrix right-inverse identity makes the division-free column checker
succeed. -/
theorem checkRightInverse_complete {d : Nat} (K : Matrix F d n) (inv : Matrix F n d)
    (h : K * inv = Matrix.identity (R := F) d) :
    checkRightInverse K inv = true := by
  unfold checkRightInverse
  simp only [List.all_eq_true]
  intro j hj
  apply decide_eq_true
  apply Vector.ext
  intro i hi
  let ii : Fin d := ⟨i, hi⟩
  have hentry := congrArg (fun M : Matrix F d d => M[ii][j]) h
  change (K * Matrix.col inv j)[ii] = (basisVec d j)[ii]
  calc
    (K * Matrix.col inv j)[ii] = (K * inv)[ii][j] := by
      rw [Matrix.getElem_mulVec, Matrix.getElem_mul]
    _ = (Matrix.identity (R := F) d)[ii][j] := hentry
    _ = (basisVec d j)[ii] := by
      unfold basisVec
      rw [Matrix.getElem_identity]
      rw [Matrix.getElem_row, Matrix.getElem_identity]
      by_cases hij : ii = j
      · simp [hij]
      · have hji : j ≠ ii := fun h => hij h.symm
        simp [hij, hji]

private theorem eq_zero_of_coeffVec_eq_zero (p : DensePoly F) (d : Nat)
    (hsize : p.size ≤ d) (hcoeff : p.coeffVec d = 0) : p = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_zero]
  by_cases hi : i < d
  · let ii : Fin d := ⟨i, hi⟩
    have hget := congrArg (fun w : Vector F d => w.get ii) hcoeff
    rw [DensePoly.coeffVec_get] at hget
    change p.coeff i = (0 : Vector F d)[i] at hget
    rw [Vector.getElem_zero] at hget
    exact hget
  · exact p.coeff_eq_zero_of_size_le (Nat.le_trans hsize (Nat.le_of_not_gt hi))

/-- A right inverse for the first `d` Krylov rows excludes every nonzero
annihilator whose stored size is at most `d`. -/
theorem eq_zero_of_evalVec_of_rightInverse (p : DensePoly F) (A : Matrix F n n)
    (v : Vector F n) (d : Nat) (inv : Matrix F n d)
    (hsize : p.size ≤ d)
    (hright : krylovMat A v d * inv = Matrix.identity (R := F) d)
    (heval : evalVec p A v = 0) : p = 0 := by
  let coeffs := p.coeffVec d
  let K := krylovMat A v d
  have hcomb : Matrix.vecMul coeffs K = 0 := by
    rw [← evalVec_eq_vecMul_krylov p A v d hsize]
    exact heval
  have hcoeff : coeffs = 0 := by
    calc
      coeffs = Matrix.vecMul coeffs (Matrix.identity (R := F) d) := by
        rw [Matrix.vecMul_identity]
      _ = Matrix.vecMul coeffs (K * inv) := by rw [hright]
      _ = Matrix.vecMul (Matrix.vecMul coeffs K) inv := by
        rw [Matrix.vecMul_mul]
      _ = 0 := by rw [hcomb, Matrix.vecMul_zero]
  exact eq_zero_of_coeffVec_eq_zero p d hsize hcoeff

/-- The kernel-reducible minimal-polynomial certificate checker.  It performs
no row reduction, pivot search, or field division. -/
@[expose]
def MinPolyCert.check (A : Matrix F n n) (c : MinPolyCert F n) : Bool :=
  let ordersOk := (List.finRange n).all fun i =>
    let o := c.order.get i
    decide (o.poly.size = o.deg + 1) &&
      decide (o.poly.coeff o.deg = 1) &&
      decide (evalVec o.poly A (basisVec n i) = 0) &&
      checkRightInverse (krylovMat A (basisVec n i) o.deg) o.inv
  let stepsOk := (List.finRange n).all fun j =>
    let s := c.steps.get j
    let running := c.running j.val (by omega)
    let incoming := (c.order.get j).poly
    decide (running = s.common * s.left) &&
      decide (incoming = s.common * s.right) &&
      decide (s.bezoutLeft * running + s.bezoutRight * incoming = s.common) &&
      decide (s.result = s.left * incoming)
  ordersOk && stepsOk &&
    decide (c.poly = c.running n (Nat.le_refl n)) &&
    decide (c.poly.coeff (c.poly.size - 1) = 1)

/-- The four facts certified for one standard-basis order witness. -/
theorem MinPolyCert.order_sound (A : Matrix F n n) (c : MinPolyCert F n)
    (h : c.check A = true) (i : Fin n) :
    let o := c.order.get i
    o.poly.size = o.deg + 1 ∧
      o.poly.coeff o.deg = 1 ∧
      evalVec o.poly A (basisVec n i) = 0 ∧
      krylovMat A (basisVec n i) o.deg * o.inv = Matrix.identity (R := F) o.deg := by
  unfold MinPolyCert.check at h
  dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hi := h.1.1.1 i (List.mem_finRange i)
  rcases hi with ⟨⟨⟨hsize, hcoeff⟩, heval⟩, hright⟩
  exact ⟨hsize, hcoeff, heval, checkRightInverse_sound _ _ hright⟩

private theorem monic_of_size_coeff (p : DensePoly F) (d : Nat)
    (hsize : p.size = d + 1) (hcoeff : p.coeff d = 1) : p.Monic := by
  rw [DensePoly.monic_iff_leadingCoeff_eq_one,
    DensePoly.leadingCoeff_eq_coeff_last p (by omega), hsize]
  simpa using hcoeff

/-- The final checker clause makes the claimed polynomial genuinely monic,
including ruling out the empty coefficient array. -/
theorem MinPolyCert.poly_monic (A : Matrix F n n) (c : MinPolyCert F n)
    (h : c.check A = true) : c.poly.Monic := by
  unfold MinPolyCert.check at h
  dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hcoeff : c.poly.coeff (c.poly.size - 1) = 1 := h.2
  have hpos : 0 < c.poly.size := by
    by_cases hzero : c.poly.size = 0
    · have hz := c.poly.coeff_eq_zero_of_size_le
          (i := c.poly.size - 1) (by omega)
      rw [hcoeff] at hz
      exact False.elim (Lean.Grind.Field.zero_ne_one hz.symm)
    · omega
  exact monic_of_size_coeff c.poly (c.poly.size - 1) (by omega) hcoeff

private theorem field_cancel_lead (q : DensePoly F) (hq : 0 < q.size) (a : F) :
    a - (a / q.leadingCoeff) * q.leadingCoeff = 0 := by
  have hlc := DensePoly.leadingCoeff_ne_zero_of_pos_size q hq
  rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
    Lean.Grind.Field.inv_mul_cancel hlc, Lean.Grind.Semiring.mul_one]
  grind

private theorem size_le_of_degree_lt (p : DensePoly F) {d : Nat}
    (h : p.degree?.getD 0 < d) : p.size ≤ d := by
  by_cases hp : p.size = 0
  · omega
  have hdeg : p.degree?.getD 0 = p.size - 1 := by
    simp [DensePoly.degree?, hp]
  omega

/-- Each checked order witness divides every polynomial annihilating its
standard-basis vector.  This is the order-level minimality furnished by the
right inverse, independently of how the certificate was produced. -/
theorem MinPolyCert.order_dvd (A : Matrix F n n) (c : MinPolyCert F n)
    (h : c.check A = true) (i : Fin n) (p : DensePoly F)
    (heval : evalVec p A (basisVec n i) = 0) :
    (c.order.get i).poly ∣ p := by
  let o := c.order.get i
  let qr := DensePoly.divMod p o.poly
  have ho := c.order_sound A h i
  rcases ho with ⟨hsize, hcoeff, hoeval, hright⟩
  change o.poly.size = o.deg + 1 at hsize
  change o.poly.coeff o.deg = 1 at hcoeff
  change evalVec o.poly A (basisVec n i) = 0 at hoeval
  change krylovMat A (basisVec n i) o.deg * o.inv =
    Matrix.identity (R := F) o.deg at hright
  have homonic : o.poly.Monic := monic_of_size_coeff o.poly o.deg hsize hcoeff
  have hopos : 0 < o.poly.size := by omega
  have hreconstruct : qr.1 * o.poly + qr.2 = p := by
    exact DensePoly.divMod_reconstruction p o.poly
      (field_cancel_lead o.poly hopos)
  have hremSize : qr.2.size ≤ o.deg := by
    by_cases hd : o.deg = 0
    · have hrem : qr.2 = 0 := by
        apply DensePoly.divMod_remainder_eq_zero_of_degree_zero_of_cancel
        · omega
        · exact field_cancel_lead o.poly hopos
      rw [hrem, DensePoly.size_zero, hd]
      exact Nat.zero_le 0
    · apply size_le_of_degree_lt
      have hodeg : o.poly.degree?.getD 0 = o.deg := by
        rw [DensePoly.degree?_eq_some_of_pos_size o.poly hopos, hsize]
        simp
      rw [← hodeg]
      exact DensePoly.divMod_remainder_degree_lt_of_pos_degree_of_cancel p o.poly
        (by rw [hodeg]; omega)
        (field_cancel_lead o.poly hopos)
  have hremEval : evalVec qr.2 A (basisVec n i) = 0 := by
    have hev := congrArg (fun q : DensePoly F => evalVec q A (basisVec n i)) hreconstruct
    rw [evalVec_add_poly, evalVec_mul, hoeval, evalVec_zero, heval] at hev
    calc
      evalVec qr.2 A (basisVec n i) = 0 + evalVec qr.2 A (basisVec n i) := by
        ext j hj
        simp only [Vector.getElem_add, Vector.getElem_zero]
        grind
      _ = 0 := hev
  have hrem : qr.2 = 0 :=
    eq_zero_of_evalVec_of_rightInverse qr.2 A (basisVec n i) o.deg o.inv
      hremSize hright hremEval
  refine ⟨qr.1, ?_⟩
  rw [← hreconstruct, hrem, DensePoly.add_zero_poly,
    DensePoly.mul_comm_poly]

/-- The four polynomial identities certified for one LCM step. -/
theorem MinPolyCert.step_sound (A : Matrix F n n) (c : MinPolyCert F n)
    (h : c.check A = true) (j : Fin n) :
    let s := c.steps.get j
    let running := c.running j.val (by omega)
    let incoming := (c.order.get j).poly
    running = s.common * s.left ∧
      incoming = s.common * s.right ∧
      s.bezoutLeft * running + s.bezoutRight * incoming = s.common ∧
      s.result = s.left * incoming := by
  unfold MinPolyCert.check at h
  dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hj := h.1.1.2 j (List.mem_finRange j)
  rcases hj with ⟨⟨⟨hrunning, hincoming⟩, hbezout⟩, hresult⟩
  exact ⟨hrunning, hincoming, hbezout, hresult⟩

private theorem poly_mul_right_cancel {a b q : DensePoly F} (hq : q ≠ 0)
    (h : a * q = b * q) : a = b := by
  have hqpos : 0 < q.size := by
    by_cases hpos : 0 < q.size
    · exact hpos
    · exact False.elim (hq ((DensePoly.size_eq_zero_iff q).mp (by omega)))
  have hlc := DensePoly.leadingCoeff_ne_zero_of_pos_size q hqpos
  have hexact (x : F) : (x * q.leadingCoeff) / q.leadingCoeff = x := by
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.mul_inv_cancel hlc, Lean.Grind.Semiring.mul_one]
  have htop (x : F) (hx : x ≠ 0) : x * q.leadingCoeff ≠ 0 := by
    intro hz
    have hz' := congrArg (fun y : F => y * q.leadingCoeff⁻¹) hz
    rw [Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.mul_inv_cancel hlc, Lean.Grind.Semiring.mul_one] at hz'
    exact hx hz'
  have ha := DensePoly.divMod_eq_of_polynomial_mul (a * q) q a hq hexact htop rfl
  have hb := DensePoly.divMod_eq_of_polynomial_mul (b * q) q b hq hexact htop rfl
  have hd := congrArg (fun p : DensePoly F => (DensePoly.divMod p q).1) h
  rw [ha, hb] at hd
  exact hd

private theorem poly_mul_left_comm (a b q : DensePoly F) :
    a * (b * q) = b * (a * q) := by
  rw [← DensePoly.mul_assoc_poly, DensePoly.mul_comm_poly a b,
    DensePoly.mul_assoc_poly]

private theorem checked_step_least (s : LcmStep F) (running incoming p : DensePoly F)
    (hincomingNe : incoming ≠ 0)
    (hrunning : running = s.common * s.left)
    (hincoming : incoming = s.common * s.right)
    (hbezout : s.bezoutLeft * running + s.bezoutRight * incoming = s.common)
    (hresult : s.result = s.left * incoming)
    (hrunDvd : running ∣ p) (hinDvd : incoming ∣ p) : s.result ∣ p := by
  have hcommonNe : s.common ≠ 0 := by
    intro hc
    apply hincomingNe
    rw [hincoming, hc, DensePoly.zero_mul]
  have hunit : s.bezoutLeft * s.left + s.bezoutRight * s.right = 1 := by
    apply poly_mul_right_cancel hcommonNe
    calc
      (s.bezoutLeft * s.left + s.bezoutRight * s.right) * s.common =
          s.bezoutLeft * (s.common * s.left) +
            s.bezoutRight * (s.common * s.right) := by
        rw [DensePoly.mul_add_left_poly]
        congr 1
        · rw [DensePoly.mul_assoc_poly, DensePoly.mul_comm_poly s.left s.common]
        · rw [DensePoly.mul_assoc_poly, DensePoly.mul_comm_poly s.right s.common]
      _ = s.common := by rw [← hrunning, ← hincoming, hbezout]
      _ = 1 * s.common := by
        rw [DensePoly.mul_comm_poly, DensePoly.mul_one_right_poly]
  rcases hrunDvd with ⟨a, ha⟩
  rcases hinDvd with ⟨b, hb⟩
  refine ⟨s.bezoutLeft * b + s.bezoutRight * a, ?_⟩
  rw [hresult]
  calc
    p = 1 * p := by rw [DensePoly.mul_comm_poly, DensePoly.mul_one_right_poly]
    _ = (s.bezoutLeft * s.left + s.bezoutRight * s.right) * p := by rw [hunit]
    _ = (s.bezoutLeft * s.left) * p + (s.bezoutRight * s.right) * p := by
      rw [DensePoly.mul_add_left_poly]
    _ = (s.left * incoming) *
        (s.bezoutLeft * b + s.bezoutRight * a) := by
      rw [DensePoly.mul_add_right_poly]
      congr 1
      · rw [hb]
        simp only [DensePoly.mul_assoc_poly, poly_mul_left_comm]
      · rw [ha, hrunning, hincoming]
        simp only [DensePoly.mul_assoc_poly, poly_mul_left_comm]

private theorem checked_step_common (s : LcmStep F) (running incoming : DensePoly F)
    (hrunning : running = s.common * s.left)
    (hincoming : incoming = s.common * s.right)
    (hresult : s.result = s.left * incoming) :
    running ∣ s.result ∧ incoming ∣ s.result := by
  constructor
  · refine ⟨s.right, ?_⟩
    rw [hresult, hincoming, hrunning]
    simp only [DensePoly.mul_assoc_poly, poly_mul_left_comm]
  · refine ⟨s.left, ?_⟩
    rw [hresult, DensePoly.mul_comm_poly]

private theorem MinPolyCert.final_eq (A : Matrix F n n) (c : MinPolyCert F n)
    (h : c.check A = true) : c.poly = c.running n (Nat.le_refl n) := by
  unfold MinPolyCert.check at h
  dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h.1.2

private theorem MinPolyCert.running_annihilates (A : Matrix F n n)
    (c : MinPolyCert F n) (h : c.check A = true) (j : Nat) (hj : j ≤ n)
    (i : Fin n) (hi : i.val < j) :
    evalVec (c.running j hj) A (basisVec n i) = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
      let jj : Fin n := ⟨j, by omega⟩
      let s := c.steps.get jj
      have hs := c.step_sound A h jj
      change c.running j (by omega) = s.common * s.left ∧
          (c.order.get jj).poly = s.common * s.right ∧
          s.bezoutLeft * c.running j (by omega) +
              s.bezoutRight * (c.order.get jj).poly = s.common ∧
          s.result = s.left * (c.order.get jj).poly at hs
      rcases hs with ⟨hrunning, hincoming, _, hresult⟩
      have hcommon := checked_step_common s (c.running j (by omega))
        (c.order.get jj).poly hrunning hincoming hresult
      change evalVec s.result A (basisVec n i) = 0
      by_cases hij : i.val = j
      · have hfin : i = jj := Fin.ext hij
        rw [hfin]
        have ho := c.order_sound A h jj
        exact evalVec_of_dvd A (basisVec n jj) hcommon.2 ho.2.2.1
      · exact evalVec_of_dvd A (basisVec n i) hcommon.1
          (ih (by omega) (by omega))

private theorem MinPolyCert.running_dvd (A : Matrix F n n)
    (c : MinPolyCert F n) (h : c.check A = true) (p : DensePoly F)
    (heval : ∀ v, evalVec p A v = 0) (j : Nat) (hj : j ≤ n) :
    c.running j hj ∣ p := by
  induction j with
  | zero =>
      change (1 : DensePoly F) ∣ p
      exact ⟨p, by rw [DensePoly.mul_comm_poly, DensePoly.mul_one_right_poly]⟩
  | succ j ih =>
      let jj : Fin n := ⟨j, by omega⟩
      let s := c.steps.get jj
      have hs := c.step_sound A h jj
      change c.running j (by omega) = s.common * s.left ∧
          (c.order.get jj).poly = s.common * s.right ∧
          s.bezoutLeft * c.running j (by omega) +
              s.bezoutRight * (c.order.get jj).poly = s.common ∧
          s.result = s.left * (c.order.get jj).poly at hs
      rcases hs with ⟨hrunning, hincoming, hbezout, hresult⟩
      have ho := c.order_sound A h jj
      have hincomingNe : (c.order.get jj).poly ≠ 0 := by
        intro hz
        have hzsize := congrArg DensePoly.size hz
        rw [DensePoly.size_zero, ho.1] at hzsize
        omega
      change s.result ∣ p
      exact checked_step_least s (c.running j (by omega))
        (c.order.get jj).poly p hincomingNe hrunning hincoming hbezout hresult
        (ih (by omega)) (c.order_dvd A h jj p (heval (basisVec n jj)))

/-- A successful certificate proves monicity, annihilation on every vector,
and divisibility into every annihilator. -/
theorem MinPolyCert.check_sound (A : Matrix F n n) (c : MinPolyCert F n)
    (h : c.check A = true) :
    c.poly.Monic ∧ (∀ v, evalVec c.poly A v = 0) ∧
      ∀ p, (∀ v, evalVec p A v = 0) → c.poly ∣ p := by
  refine ⟨c.poly_monic A h, ?_, ?_⟩
  · rw [evalVec_eq_zero_iff]
    intro i
    rw [c.final_eq A h]
    exact c.running_annihilates A h n (Nat.le_refl n) i i.isLt
  · intro p hp
    rw [c.final_eq A h]
    exact c.running_dvd A h p hp n (Nat.le_refl n)

end Hex.Matrix

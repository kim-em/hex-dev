import HexHensel.Basic

/-!
Executable single-step linear Hensel lifting.

This module implements the linear correction step that lifts a factorization
from congruence modulo `p^k` to congruence modulo `p^(k+1)`, together with the
initial theorem surface describing its computational invariants.
-/
namespace Hex

private theorem list_getD_map_range {α : Type} [Zero α] (size n : Nat) (f : Nat → α) :
    ((List.range size).map f).getD n (Zero.zero : α) =
      if n < size then f n else (Zero.zero : α) := by
  by_cases hn : n < size
  · simp [hn, List.getD]
  · simp [hn, List.getD]

namespace ZPoly

/-- Divide every coefficient by `m` using Lean's truncating integer division. -/
def coeffwiseDiv (f : ZPoly) (m : Nat) : ZPoly :=
  DensePoly.ofCoeffs <|
    (List.range f.size).map (fun i => f.coeff i / Int.ofNat m) |>.toArray

@[simp] theorem coeff_coeffwiseDiv (f : ZPoly) (m i : Nat) :
    (coeffwiseDiv f m).coeff i = f.coeff i / Int.ofNat m := by
  unfold coeffwiseDiv
  rw [DensePoly.coeff_ofCoeffs_list]
  rw [list_getD_map_range]
  by_cases hi : i < f.size
  · simp [hi]
  · have hcoeff : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hi)
    simp [hi, hcoeff]
    rfl

/-- Recover `f - g` from its truncated coefficient-wise division by `m` when
`g ≡ f (mod m)`: the congruence forces `m` to exactly divide each coefficient
of `f - g`, so the truncating `coeffwiseDiv` followed by `DensePoly.scale` of
`m` loses nothing. Consumed by the correction-proof chain in `linearHenselStep`
to justify that the lifted coefficient correction is exact mod `p^k`. -/
private theorem scale_coeffwiseDiv_sub_of_congr
    (f g : ZPoly) (m : Nat) (hfg : ZPoly.congr g f m) :
    DensePoly.scale (Int.ofNat m) (coeffwiseDiv (f - g) m) = f - g := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_scale]
  · rw [coeff_coeffwiseDiv]
    rw [DensePoly.coeff_sub]
    · have hdvd_gf : (m : Int) ∣ g.coeff i - f.coeff i :=
        Int.dvd_of_emod_eq_zero (hfg i)
      have hdvd : (m : Int) ∣ f.coeff i - g.coeff i := by
        rw [← Int.neg_sub]
        exact Int.dvd_neg.mpr hdvd_gf
      rw [Int.mul_comm]
      exact Int.ediv_mul_cancel hdvd
    · rfl
  · exact Int.mul_zero _

end ZPoly

/--
Result of one linear Hensel lift step, packaging the lifted first factor `g`
and the lifted complementary factor `h`. Callers can pattern-match on the
two projections directly, or rewrite via the unfolding simp lemmas
`linearHenselStep_g` / `linearHenselStep_h`.
-/
structure LinearLiftResult where
  /-- The lifted first factor. -/
  g : ZPoly
  /-- The lifted complementary factor. -/
  h : ZPoly

namespace LinearLiftResult

/-- The lifted-and-scaled increment used by one linear Hensel step. -/
def liftScaledIncrement (p k : Nat) [ZMod64.Bounds p] (r : FpPoly p) : ZPoly :=
  DensePoly.scale (Int.ofNat (p ^ k)) (FpPoly.liftToZ r)

@[simp] theorem coeff_liftScaledIncrement
    (p k : Nat) [ZMod64.Bounds p] (r : FpPoly p) (i : Nat) :
    (liftScaledIncrement p k r).coeff i =
      Int.ofNat (p ^ k) * Int.ofNat (r.coeff i).toNat := by
  unfold liftScaledIncrement
  rw [DensePoly.coeff_scale]
  · rw [FpPoly.coeff_liftToZ]
  · exact Int.mul_zero _

/-- A scaled lift is coefficientwise zero modulo the scaling modulus. -/
theorem congr_liftScaledIncrement_zero
    (p k : Nat) [ZMod64.Bounds p] (r : FpPoly p) :
    ZPoly.congr (liftScaledIncrement p k r) 0 (p ^ k) := by
  intro i
  rw [coeff_liftScaledIncrement]
  rw [DensePoly.coeff_zero]
  simp

end LinearLiftResult

namespace ZPoly

/-- One linear Hensel correction step from modulus `p^k` to `p^(k+1)`. -/
def linearHenselStep
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p) : LinearLiftResult :=
  let e := coeffwiseDiv (f - g * h) (p ^ k)
  let gMod := modP p g
  let hMod := modP p h
  let eMod := modP p e
  let qr := DensePoly.divMod (t * eMod) gMod
  let q := qr.1
  let r := qr.2
  let g' := g + LinearLiftResult.liftScaledIncrement p k r
  let hCorrection := s * eMod + q * hMod
  let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
  { g := reduceModPow g' p (k + 1)
    h := reduceModPow h' p (k + 1) }

/-- The `g` projection of a linear Hensel step, exposed without unfolding the result record. -/
@[simp] theorem linearHenselStep_g
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p) :
    (linearHenselStep p k f g h s t).g =
      let e := coeffwiseDiv (f - g * h) (p ^ k)
      let gMod := modP p g
      let eMod := modP p e
      let qr := DensePoly.divMod (t * eMod) gMod
      reduceModPow (g + LinearLiftResult.liftScaledIncrement p k qr.2) p (k + 1) := by
  simp [linearHenselStep]

/-- The `h` projection of a linear Hensel step, exposed without unfolding the result record. -/
@[simp] theorem linearHenselStep_h
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p) :
    (linearHenselStep p k f g h s t).h =
      let e := coeffwiseDiv (f - g * h) (p ^ k)
      let gMod := modP p g
      let hMod := modP p h
      let eMod := modP p e
      let qr := DensePoly.divMod (t * eMod) gMod
      let hCorrection := s * eMod + qr.1 * hMod
      reduceModPow (h + LinearLiftResult.liftScaledIncrement p k hCorrection) p (k + 1) := by
  simp [linearHenselStep]

private theorem congr_mul_reduceModPow_pair
    (p k : Nat) [ZMod64.Bounds p] (g h : ZPoly) :
    ZPoly.congr
      (ZPoly.reduceModPow g p k * ZPoly.reduceModPow h p k)
      (g * h)
      (p ^ k) := by
  apply ZPoly.congr_mul
  · exact ZPoly.congr_reduceModPow g p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))
  · exact ZPoly.congr_reduceModPow h p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))

/-- The algebraic rearrangement
`r * hMod + gMod * (s * eMod + q * hMod) = eMod`,
given the Euclidean division `q * gMod + r = t * eMod` and the Bezout identity
`s * gMod + t * hMod = 1` over `FpPoly p`. This identity is what makes one
linear Hensel correction step exact mod `p`: it is the rearrangement called
on by the correction-proof chain to discharge the mod-`p` residue between the
naive correction `q * hMod` and the actual lifted increment. -/
private theorem linearHenselStep_correction_identity
    (p : Nat) [ZMod64.Bounds p]
    (gMod hMod eMod s t q r : FpPoly p)
    (hdiv : q * gMod + r = t * eMod)
    (hbez : s * gMod + t * hMod = 1) :
    r * hMod + gMod * (s * eMod + q * hMod) = eMod := by
  calc
    r * hMod + gMod * (s * eMod + q * hMod)
        = r * hMod + (gMod * (s * eMod) + gMod * (q * hMod)) := by
          rw [FpPoly.left_distrib]
    _ = (s * gMod) * eMod + (q * gMod + r) * hMod := by
          grind [FpPoly.add_assoc, FpPoly.add_comm, FpPoly.mul_assoc, FpPoly.mul_comm,
            FpPoly.right_distrib]
    _ = (s * gMod) * eMod + (t * eMod) * hMod := by
          rw [hdiv]
    _ = (s * gMod) * eMod + (t * hMod) * eMod := by
          grind [FpPoly.mul_assoc, FpPoly.mul_comm]
    _ = (s * gMod + t * hMod) * eMod := by
          rw [FpPoly.right_distrib]
    _ = 1 * eMod := by
          rw [hbez]
    _ = eMod := by
          rw [FpPoly.one_mul]

/-- Reducing the integer `1` polynomial modulo `p` yields the `FpPoly p`
identity. Bottom-of-recursion case for the `modP p` algebra rewrites consumed
by the linear Hensel step's correctness chain. -/
@[simp] theorem modP_one (p : Nat) [ZMod64.Bounds p] :
    ZPoly.modP p (1 : ZPoly) = (1 : FpPoly p) := by
  have hcong : ZPoly.congr (FpPoly.liftToZ (1 : FpPoly p)) (1 : ZPoly) p := by
    intro i
    rw [FpPoly.coeff_liftToZ]
    change
      (Int.ofNat (DensePoly.coeff (DensePoly.C (1 : ZMod64 p)) i).toNat -
          DensePoly.coeff (DensePoly.C (1 : Int)) i) % (p : Int) = 0
    rw [DensePoly.coeff_C, DensePoly.coeff_C]
    cases i with
    | zero =>
        cases p with
        | zero =>
            cases Nat.not_lt_zero _ (ZMod64.Bounds.pPos (p := 0))
        | succ p' =>
            cases p' with
            | zero =>
                change (Int.ofNat (1 % 1) - 1) % (1 : Int) = 0
                simp
            | succ p'' =>
                have hlt : 1 < Nat.succ (Nat.succ p'') := by omega
                change
                  (Int.ofNat (1 % Nat.succ (Nat.succ p'')) - 1) %
                    (Nat.succ (Nat.succ p'') : Int) = 0
                simp [Nat.mod_eq_of_lt hlt]
    | succ i =>
        change (Int.ofNat 0 - (0 : Int)) % (p : Int) = 0
        simp
  exact Eq.trans (ZPoly.modP_eq_of_congr p _ _ (ZPoly.congr_symm _ _ _ hcong))
    (FpPoly.modP_liftToZ (p := p) (1 : FpPoly p))

/-- A `modP p` equality converts to a `ZPoly.congr` against the lift: if
`modP p z = u` then the lifted-back-to-`ZPoly` representative `FpPoly.liftToZ u`
agrees with `z` coefficientwise modulo `p`. Used by the correction-proof chain
when an `FpPoly`-side computation has produced the canonical residue and the
caller needs to feed it back into the integer-side congruence. -/
theorem congr_liftToZ_of_modP_eq
    (p : Nat) [ZMod64.Bounds p] (u : FpPoly p) (z : ZPoly)
    (h : ZPoly.modP p z = u) :
    ZPoly.congr (FpPoly.liftToZ u) z p := by
  simpa [← h] using FpPoly.congr_liftToZ_modP (p := p) z

private theorem zmod_add_lift_congr
    (p : Nat) [ZMod64.Bounds p] (a b : ZMod64 p) :
    (Int.ofNat (a + b).toNat - (Int.ofNat a.toNat + Int.ofNat b.toNat)) %
      (p : Int) = 0 := by
  change (Int.ofNat (ZMod64.add a b).toNat -
      (Int.ofNat a.toNat + Int.ofNat b.toNat)) % (p : Int) = 0
  rw [ZMod64.toNat_add]
  have hp : 0 < p := ZMod64.Bounds.pPos (p := p)
  have hmod :
      Int.ofNat ((a.toNat + b.toNat) % p) =
        (Int.ofNat (a.toNat + b.toNat)) % (p : Int) := by
    exact Int.natCast_emod _ _
  rw [hmod]
  have hdiv :
      (p : Int) ∣
        (Int.ofNat (a.toNat + b.toNat) % (p : Int) -
          Int.ofNat (a.toNat + b.toNat)) :=
    Int.dvd_sub_self_of_emod_eq rfl
  rw [show Int.ofNat (a.toNat + b.toNat) =
      Int.ofNat a.toNat + Int.ofNat b.toNat by
        simp [Int.ofNat_eq_natCast]]
  exact Int.emod_eq_zero_of_dvd hdiv

private theorem zmod_add_zero_zero (p : Nat) [ZMod64.Bounds p] :
    (Zero.zero : ZMod64 p) + (Zero.zero : ZMod64 p) = (Zero.zero : ZMod64 p) := by
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  have hto :
      ((Zero.zero : ZMod64 p) + (Zero.zero : ZMod64 p)).toNat = 0 := by
    change (ZMod64.add (ZMod64.zero : ZMod64 p) ZMod64.zero).toNat = 0
    rw [ZMod64.toNat_add]
    have hzero : (ZMod64.zero : ZMod64 p).toNat = 0 := ZMod64.toNat_zero
    rw [hzero]
    simp
  simpa [ZMod64.toNat_eq_val, ZMod64.toNat_zero] using hto

/-- `FpPoly.liftToZ` is additive modulo `p`: the integer lift of a sum is
coefficientwise congruent to the sum of the integer lifts. Together with
`liftToZ_mul_congr` this is the bridge used by `modP_add` /
`modP_lift_mul_left` / `modP_lift_mul_right` to push `modP p` through the
`+`/`·` structure of the linear Hensel correction. -/
theorem liftToZ_add_congr
    (p : Nat) [ZMod64.Bounds p] (f g : FpPoly p) :
    ZPoly.congr (FpPoly.liftToZ (f + g)) (FpPoly.liftToZ f + FpPoly.liftToZ g) p := by
  intro i
  rw [FpPoly.coeff_liftToZ]
  rw [DensePoly.coeff_add f g i (zmod_add_zero_zero p)]
  rw [DensePoly.coeff_add (FpPoly.liftToZ f) (FpPoly.liftToZ g) i (by rfl)]
  rw [FpPoly.coeff_liftToZ, FpPoly.coeff_liftToZ]
  exact zmod_add_lift_congr p (f.coeff i) (g.coeff i)

private theorem zmod_mul_lift_congr
    (p : Nat) [ZMod64.Bounds p] (a b : ZMod64 p) :
    (Int.ofNat (a * b).toNat - (Int.ofNat a.toNat * Int.ofNat b.toNat)) %
      (p : Int) = 0 := by
  change (Int.ofNat (ZMod64.mul a b).toNat -
      (Int.ofNat a.toNat * Int.ofNat b.toNat)) % (p : Int) = 0
  rw [ZMod64.toNat_mul]
  have hmod :
      Int.ofNat ((a.toNat * b.toNat) % p) =
        (Int.ofNat (a.toNat * b.toNat)) % (p : Int) := by
    exact Int.natCast_emod _ _
  rw [hmod]
  have hdiv :
      (p : Int) ∣
        (Int.ofNat (a.toNat * b.toNat) % (p : Int) -
          Int.ofNat (a.toNat * b.toNat)) :=
    Int.dvd_sub_self_of_emod_eq rfl
  rw [show Int.ofNat (a.toNat * b.toNat) =
      Int.ofNat a.toNat * Int.ofNat b.toNat by
        simp [Int.ofNat_eq_natCast]]
  exact Int.emod_eq_zero_of_dvd hdiv

/-- Per-term coefficient congruence at the lifted product diagonal: the `i`th
diagonal contribution to the `n`th coefficient of `f * g` over `FpPoly p`,
lifted to `Int`, agrees mod `p` with the corresponding `DensePoly.mulCoeffStep`
contribution over `FpPoly.liftToZ f · FpPoly.liftToZ g`. Gates the diagonal
fold underlying `liftToZ_mul_congr`. -/
private theorem liftToZ_mulCoeffTerm_congr
    (p : Nat) [ZMod64.Bounds p] (f g : FpPoly p) (n i : Nat) :
    (Int.ofNat (FpPoly.mulCoeffTerm f g n i).toNat -
        DensePoly.mulCoeffStep (FpPoly.liftToZ f) (FpPoly.liftToZ g) n i 0 (n - i)) %
      (p : Int) = 0 := by
  unfold FpPoly.mulCoeffTerm DensePoly.mulCoeffStep
  by_cases hni : n < i
  · have hneq : i + (n - i) ≠ n := by omega
    rw [if_pos hni, if_neg hneq]
    change (Int.ofNat (ZMod64.zero : ZMod64 p).toNat - 0) % (p : Int) = 0
    rw [ZMod64.toNat_zero]
    simp
  · have hle : i ≤ n := Nat.le_of_not_gt hni
    have heq : i + (n - i) = n := Nat.add_sub_of_le hle
    simp [hni, heq, FpPoly.coeff_liftToZ]
    exact zmod_mul_lift_congr p (f.coeff i) (g.coeff (n - i))

private def intDiagonalMulCoeffTerm
    (p q : ZPoly) (n i : Nat) : Int :=
  if n < i then 0 else p.coeff i * q.coeff (n - i)

private def intBoundedDiagonalMulCoeffTerm
    (p q : ZPoly) (n i m : Nat) : Int :=
  if n < i then 0 else if n - i < m then p.coeff i * q.coeff (n - i) else 0

private theorem fold_mulCoeffStep_eq_bounded_diagonal_int
    (p q : ZPoly) (n i m : Nat) (acc : Int) :
    (List.range m).foldl (DensePoly.mulCoeffStep p q n i) acc =
      acc + intBoundedDiagonalMulCoeffTerm p q n i m := by
  induction m generalizing acc with
  | zero =>
      simp [intBoundedDiagonalMulCoeffTerm]
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold DensePoly.mulCoeffStep intBoundedDiagonalMulCoeffTerm
      by_cases hlt : n < i
      · have hne : i + m ≠ n := by omega
        simp [hlt, hne]
      · by_cases hm : n - i < m
        · have hne : i + m ≠ n := by omega
          simp [hlt, hm, hne]
          omega
        · by_cases heq : i + m = n
          · have hsub : n - i = m := by omega
            simp [hlt, heq, hsub]
          · have hm' : ¬ n - i < m + 1 := by omega
            simp [hlt, hm, hm', heq]

private theorem fold_mulCoeffStep_eq_diagonal_int
    (p q : ZPoly) (n i : Nat) (acc : Int) :
    (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) acc =
      acc + intDiagonalMulCoeffTerm p q n i := by
  rw [fold_mulCoeffStep_eq_bounded_diagonal_int]
  unfold intBoundedDiagonalMulCoeffTerm intDiagonalMulCoeffTerm
  by_cases hlt : n < i
  · simp [hlt]
  · by_cases hbound : n - i < q.size
    · simp [hlt, hbound]
    · have hcoeff : q.coeff (n - i) = 0 :=
        DensePoly.coeff_eq_zero_of_size_le q (Nat.le_of_not_gt hbound)
      simp [hlt, hbound, hcoeff]

private theorem fold_mulCoeff_outer_eq_diagonal_int
    (p q : ZPoly) (n : Nat) (xs : List Nat) (acc : Int) :
    xs.foldl
        (fun coeff i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) coeff)
        acc =
      xs.foldl (fun coeff i => coeff + intDiagonalMulCoeffTerm p q n i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [fold_mulCoeffStep_eq_diagonal_int]
      exact ih (acc + intDiagonalMulCoeffTerm p q n i)

/-- Reifies the executable nested-fold `DensePoly.mulCoeffSum p q n` into the
flat diagonal-sum `Σ_{i < p.size} intDiagonalMulCoeffTerm p q n i` over `Int`.
This bridge identity is what lets `liftToZ_mul_congr` reason about the lifted
product coefficient as an additive `Int` sum, where the per-term congruence
from `liftToZ_mulCoeffTerm_diagonal_congr` propagates cleanly. -/
private theorem mulCoeffSum_eq_diagonal_int (p q : ZPoly) (n : Nat) :
    DensePoly.mulCoeffSum p q n =
      (List.range p.size).foldl (fun acc i => acc + intDiagonalMulCoeffTerm p q n i) 0 := by
  unfold DensePoly.mulCoeffSum
  exact fold_mulCoeff_outer_eq_diagonal_int p q n (List.range p.size) 0

private theorem intDiagonalMulCoeffTerm_eq_zero_of_size_le
    (p q : ZPoly) (n i : Nat) (hi : p.size ≤ i) :
    intDiagonalMulCoeffTerm p q n i = 0 := by
  unfold intDiagonalMulCoeffTerm
  by_cases hn : n < i
  · simp [hn]
  · have hcoeff : p.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le p hi
    simp [hn, hcoeff]

private theorem fold_diagonal_extend_int (p q : ZPoly) (n d : Nat) :
    (List.range (p.size + d)).foldl (fun acc i => acc + intDiagonalMulCoeffTerm p q n i) 0 =
      (List.range p.size).foldl (fun acc i => acc + intDiagonalMulCoeffTerm p q n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : intDiagonalMulCoeffTerm p q n (p.size + d) = 0 :=
        intDiagonalMulCoeffTerm_eq_zero_of_size_le p q n (p.size + d) (by omega)
      simp [hterm]

private theorem diagonalSum_eq_bound_int
    (p q : ZPoly) (n m : Nat) (hm : p.size ≤ m) :
    (List.range p.size).foldl (fun acc i => acc + intDiagonalMulCoeffTerm p q n i) 0 =
      (List.range m).foldl (fun acc i => acc + intDiagonalMulCoeffTerm p q n i) 0 := by
  have hm' : p.size + (m - p.size) = m := by omega
  rw [← hm']
  exact (fold_diagonal_extend_int p q n (m - p.size)).symm

private theorem liftToZ_size_le
    (p : Nat) [ZMod64.Bounds p] (f : FpPoly p) :
    (FpPoly.liftToZ f).size ≤ f.size := by
  by_cases hle : (FpPoly.liftToZ f).size ≤ f.size
  · exact hle
  · exfalso
    have hlt : f.size < (FpPoly.liftToZ f).size := Nat.lt_of_not_ge hle
    have hpos : 0 < (FpPoly.liftToZ f).size := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    have hlast :=
      DensePoly.coeff_last_ne_zero_of_pos_size (FpPoly.liftToZ f) hpos
    have hidx : f.size ≤ (FpPoly.liftToZ f).size - 1 := by omega
    have hf : f.coeff ((FpPoly.liftToZ f).size - 1) = 0 :=
      DensePoly.coeff_eq_zero_of_size_le f hidx
    rw [FpPoly.coeff_liftToZ, hf] at hlast
    exact hlast (by
      change Int.ofNat (ZMod64.zero : ZMod64 p).toNat = (0 : Int)
      rw [ZMod64.toNat_zero]
      rfl)

private theorem liftToZ_mulCoeffTerm_diagonal_congr
    (p : Nat) [ZMod64.Bounds p] (f g : FpPoly p) (n i : Nat) :
    (Int.ofNat (FpPoly.mulCoeffTerm f g n i).toNat -
        intDiagonalMulCoeffTerm (FpPoly.liftToZ f) (FpPoly.liftToZ g) n i) %
      (p : Int) = 0 := by
  unfold intDiagonalMulCoeffTerm
  by_cases hni : n < i
  · simp [hni, FpPoly.mulCoeffTerm]
    change (Int.ofNat (ZMod64.zero : ZMod64 p).toNat - 0) % (p : Int) = 0
    rw [ZMod64.toNat_zero]
    simp
  · have hle : i ≤ n := Nat.le_of_not_gt hni
    have heq : i + (n - i) = n := Nat.add_sub_of_le hle
    simpa [hni, DensePoly.mulCoeffStep, heq] using liftToZ_mulCoeffTerm_congr p f g n i

private theorem zmod_add_lift_congr_of_terms
    (p : Nat) [ZMod64.Bounds p] (a b : ZMod64 p) (x y : Int)
    (ha : (Int.ofNat a.toNat - x) % (p : Int) = 0)
    (hb : (Int.ofNat b.toNat - y) % (p : Int) = 0) :
    (Int.ofNat (a + b).toNat - (x + y)) % (p : Int) = 0 := by
  have hadd := zmod_add_lift_congr p a b
  have hxy : ((Int.ofNat a.toNat + Int.ofNat b.toNat) - (x + y)) % (p : Int) = 0 := by
    have hsum :
        (p : Int) ∣
          (Int.ofNat a.toNat + Int.ofNat b.toNat) - (x + y) := by
      have hda : (p : Int) ∣ Int.ofNat a.toNat - x := Int.dvd_of_emod_eq_zero ha
      have hdb : (p : Int) ∣ Int.ofNat b.toNat - y := Int.dvd_of_emod_eq_zero hb
      rcases hda with ⟨ka, hka⟩
      rcases hdb with ⟨kb, hkb⟩
      refine ⟨ka + kb, ?_⟩
      calc
        Int.ofNat a.toNat + Int.ofNat b.toNat - (x + y)
            = (Int.ofNat a.toNat - x) + (Int.ofNat b.toNat - y) := by omega
        _ = (p : Int) * ka + (p : Int) * kb := by rw [hka, hkb]
        _ = (p : Int) * (ka + kb) := by grind
    exact Int.emod_eq_zero_of_dvd hsum
  have htotal :
      (p : Int) ∣
        (Int.ofNat (a + b).toNat - (x + y)) := by
    have h1 : (p : Int) ∣
        Int.ofNat (a + b).toNat - (Int.ofNat a.toNat + Int.ofNat b.toNat) :=
      Int.dvd_of_emod_eq_zero hadd
    have h2 : (p : Int) ∣
        (Int.ofNat a.toNat + Int.ofNat b.toNat) - (x + y) :=
      Int.dvd_of_emod_eq_zero hxy
    rcases h1 with ⟨k1, hk1⟩
    rcases h2 with ⟨k2, hk2⟩
    refine ⟨k1 + k2, ?_⟩
    calc
      Int.ofNat (a + b).toNat - (x + y)
          =
            (Int.ofNat (a + b).toNat - (Int.ofNat a.toNat + Int.ofNat b.toNat)) +
              ((Int.ofNat a.toNat + Int.ofNat b.toNat) - (x + y)) := by omega
      _ = (p : Int) * k1 + (p : Int) * k2 := by rw [hk1, hk2]
      _ = (p : Int) * (k1 + k2) := by grind
  exact Int.emod_eq_zero_of_dvd htotal

/-- Inductive lift transport carrying the per-term diagonal congruence
(`liftToZ_mulCoeffTerm_diagonal_congr`) across the diagonal fold. The
hypothesis `hacc` says the seed `acc` lifted to `Int` agrees mod `p` with the
integer-side seed `accZ`; the conclusion says that property is preserved after
adding the next diagonal contribution on both sides. Driver of the inductive
step in `liftToZ_mul_congr`. -/
private theorem fold_liftToZ_mulCoeffTerm_congr
    (p : Nat) [ZMod64.Bounds p] (f g : FpPoly p) (n : Nat) (xs : List Nat)
    (acc : ZMod64 p) (accZ : Int)
    (hacc : (Int.ofNat acc.toNat - accZ) % (p : Int) = 0) :
    (Int.ofNat
        (xs.foldl (fun coeff i => coeff + FpPoly.mulCoeffTerm f g n i) acc).toNat -
        xs.foldl
          (fun coeff i =>
            coeff + intDiagonalMulCoeffTerm (FpPoly.liftToZ f) (FpPoly.liftToZ g) n i)
          accZ) %
      (p : Int) = 0 := by
  induction xs generalizing acc accZ with
  | nil =>
      simpa using hacc
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      exact zmod_add_lift_congr_of_terms p acc (FpPoly.mulCoeffTerm f g n i) accZ
        (intDiagonalMulCoeffTerm (FpPoly.liftToZ f) (FpPoly.liftToZ g) n i)
        hacc (liftToZ_mulCoeffTerm_diagonal_congr p f g n i)

/-- `FpPoly.liftToZ` is multiplicative modulo `p`: the integer lift of a
product is coefficientwise congruent to the product of the integer lifts.
Multiplicative companion of `liftToZ_add_congr`; together they bridge the
`FpPoly`-side ring operations into `ZPoly.congr` form, which the `modP` push
lemmas (`modP_add`, `modP_lift_mul_left`, `modP_lift_mul_right`) consume to
expose the linear Hensel correction's mod-`p` structure. -/
theorem liftToZ_mul_congr
    (p : Nat) [ZMod64.Bounds p] (f g : FpPoly p) :
    ZPoly.congr (FpPoly.liftToZ (f * g)) (FpPoly.liftToZ f * FpPoly.liftToZ g) p := by
  intro n
  rw [FpPoly.coeff_liftToZ, FpPoly.coeff_mul, DensePoly.coeff_mul]
  rw [mulCoeffSum_eq_diagonal_int]
  rw [diagonalSum_eq_bound_int (FpPoly.liftToZ f) (FpPoly.liftToZ g) n f.size
    (liftToZ_size_le p f)]
  exact fold_liftToZ_mulCoeffTerm_congr p f g n (List.range f.size) 0 0 (by
    change (Int.ofNat (ZMod64.zero : ZMod64 p).toNat - 0) % (p : Int) = 0
    rw [ZMod64.toNat_zero]
    simp)

/-- `ZPoly.modP p` distributes over addition: the canonical mod-`p` residue
of a sum is the sum of residues. Standard ring-homomorphism rewrite for
`modP p` used by the linear Hensel step proof to split `modP p (g·h + ...)`
into manageable pieces. -/
@[simp] theorem modP_add
    (p : Nat) [ZMod64.Bounds p] (f g : ZPoly) :
    ZPoly.modP p (f + g) = ZPoly.modP p f + ZPoly.modP p g := by
  have hliftAdd :
      ZPoly.congr
        (FpPoly.liftToZ (ZPoly.modP p f + ZPoly.modP p g))
        (FpPoly.liftToZ (ZPoly.modP p f) + FpPoly.liftToZ (ZPoly.modP p g)) p :=
    liftToZ_add_congr p (ZPoly.modP p f) (ZPoly.modP p g)
  have hpieces :
      ZPoly.congr
        (FpPoly.liftToZ (ZPoly.modP p f) + FpPoly.liftToZ (ZPoly.modP p g))
        (f + g) p :=
    ZPoly.congr_add _ _ _ _ p
      (FpPoly.congr_liftToZ_modP (p := p) f)
      (FpPoly.congr_liftToZ_modP (p := p) g)
  have hsum :
      ZPoly.congr
        (FpPoly.liftToZ (ZPoly.modP p f + ZPoly.modP p g))
        (f + g) p :=
    ZPoly.congr_trans _ _ _ p hliftAdd hpieces
  exact Eq.trans
    (ZPoly.modP_eq_of_congr p (f + g)
      (FpPoly.liftToZ (ZPoly.modP p f + ZPoly.modP p g))
      (ZPoly.congr_symm _ _ _ hsum))
    (FpPoly.modP_liftToZ (p := p) (ZPoly.modP p f + ZPoly.modP p g))

/-- `ZPoly.modP p` distributes over multiplication: the canonical mod-`p`
residue of a product is the product of residues. Multiplicative companion
of `modP_add`; the Mathlib-free Gauss-transfer chain consumes this to
expose `modP p (f * g)` in its factored form. -/
@[simp] theorem modP_mul
    (p : Nat) [ZMod64.Bounds p] (f g : ZPoly) :
    ZPoly.modP p (f * g) = ZPoly.modP p f * ZPoly.modP p g := by
  have hliftMul :
      ZPoly.congr
        (FpPoly.liftToZ (ZPoly.modP p f * ZPoly.modP p g))
        (FpPoly.liftToZ (ZPoly.modP p f) * FpPoly.liftToZ (ZPoly.modP p g)) p :=
    liftToZ_mul_congr p (ZPoly.modP p f) (ZPoly.modP p g)
  have hpieces :
      ZPoly.congr
        (FpPoly.liftToZ (ZPoly.modP p f) * FpPoly.liftToZ (ZPoly.modP p g))
        (f * g) p :=
    ZPoly.congr_mul _ _ _ _ p
      (FpPoly.congr_liftToZ_modP (p := p) f)
      (FpPoly.congr_liftToZ_modP (p := p) g)
  have hprod :
      ZPoly.congr
        (FpPoly.liftToZ (ZPoly.modP p f * ZPoly.modP p g))
        (f * g) p :=
    ZPoly.congr_trans _ _ _ p hliftMul hpieces
  exact Eq.trans
    (ZPoly.modP_eq_of_congr p (f * g)
      (FpPoly.liftToZ (ZPoly.modP p f * ZPoly.modP p g))
      (ZPoly.congr_symm _ _ _ hprod))
    (FpPoly.modP_liftToZ (p := p) (ZPoly.modP p f * ZPoly.modP p g))

/-- `modP p` reduces a `liftToZ`-on-the-left product to the `FpPoly`-side
factor times the `modP` of the integer side: `modP p (liftToZ r · h) =
r · modP p h`. Companion of `modP_lift_mul_right`; consumed by the linear
Hensel step's correctness chain to push `modP p` past the
`s * eMod`-shaped half of the correction product. -/
theorem modP_lift_mul_left
    (p : Nat) [ZMod64.Bounds p] (r : FpPoly p) (h : ZPoly) :
    ZPoly.modP p (FpPoly.liftToZ r * h) = r * ZPoly.modP p h := by
  let hMod := ZPoly.modP p h
  have hmulLift :
      ZPoly.congr (FpPoly.liftToZ (r * hMod)) (FpPoly.liftToZ r * FpPoly.liftToZ hMod) p :=
    liftToZ_mul_congr p r hMod
  have hright :
      ZPoly.congr (FpPoly.liftToZ r * FpPoly.liftToZ hMod) (FpPoly.liftToZ r * h) p :=
    ZPoly.congr_mul _ _ _ _ p
      (ZPoly.congr_refl (FpPoly.liftToZ r) p)
      (FpPoly.congr_liftToZ_modP (p := p) h)
  have hprod :
      ZPoly.congr (FpPoly.liftToZ (r * hMod)) (FpPoly.liftToZ r * h) p :=
    ZPoly.congr_trans _ _ _ p hmulLift hright
  exact Eq.trans
    (ZPoly.modP_eq_of_congr p (FpPoly.liftToZ r * h) (FpPoly.liftToZ (r * hMod))
      (ZPoly.congr_symm _ _ _ hprod))
    (FpPoly.modP_liftToZ (p := p) (r * hMod))

/-- `modP p` reduces a `liftToZ`-on-the-right product to the `modP` of the
integer side times the `FpPoly`-side factor: `modP p (g · liftToZ hCorrection)
= modP p g · hCorrection`. Companion of `modP_lift_mul_left`; consumed by the
linear Hensel step's correctness chain to push `modP p` past the
`q * hMod`-shaped half of the correction product. -/
theorem modP_lift_mul_right
    (p : Nat) [ZMod64.Bounds p] (g : ZPoly) (hCorrection : FpPoly p) :
    ZPoly.modP p (g * FpPoly.liftToZ hCorrection) =
      ZPoly.modP p g * hCorrection := by
  let gMod := ZPoly.modP p g
  have hmulLift :
      ZPoly.congr (FpPoly.liftToZ (gMod * hCorrection))
        (FpPoly.liftToZ gMod * FpPoly.liftToZ hCorrection) p :=
    liftToZ_mul_congr p gMod hCorrection
  have hleft :
      ZPoly.congr (FpPoly.liftToZ gMod * FpPoly.liftToZ hCorrection)
        (g * FpPoly.liftToZ hCorrection) p :=
    ZPoly.congr_mul _ _ _ _ p
      (FpPoly.congr_liftToZ_modP (p := p) g)
      (ZPoly.congr_refl (FpPoly.liftToZ hCorrection) p)
  have hprod :
      ZPoly.congr (FpPoly.liftToZ (gMod * hCorrection))
        (g * FpPoly.liftToZ hCorrection) p :=
    ZPoly.congr_trans _ _ _ p hmulLift hleft
  exact Eq.trans
    (ZPoly.modP_eq_of_congr p (g * FpPoly.liftToZ hCorrection)
      (FpPoly.liftToZ (gMod * hCorrection)) (ZPoly.congr_symm _ _ _ hprod))
    (FpPoly.modP_liftToZ (p := p) (gMod * hCorrection))

/-- Combined `modP_add` + `modP_lift_mul_left` + `modP_lift_mul_right` rewrite
in the exact `liftToZ r · h + g · liftToZ hCorrection` shape produced by the
linear Hensel correction step. Single-rewrite entry point consumed by the
linear-Hensel correctness chain in place of three separate `modP` pushes. -/
theorem modP_add_lift_mul
    (p : Nat) [ZMod64.Bounds p] (g h : ZPoly) (r hCorrection : FpPoly p) :
    ZPoly.modP p (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection) =
      r * ZPoly.modP p h + ZPoly.modP p g * hCorrection := by
  rw [modP_add, modP_lift_mul_left, modP_lift_mul_right]

private theorem scale_congr_of_congr_mod_base
    (p k : Nat) (first e : ZPoly)
    (_hk : 1 ≤ k)
    (hfirst : ZPoly.congr first e p) :
    ZPoly.congr
      (DensePoly.scale (Int.ofNat (p ^ k)) first)
      (DensePoly.scale (Int.ofNat (p ^ k)) e)
      (p ^ (k + 1)) := by
  intro i
  rw [DensePoly.coeff_scale _ _ _ (Int.mul_zero (Int.ofNat (p ^ k))),
    DensePoly.coeff_scale _ _ _ (Int.mul_zero (Int.ofNat (p ^ k)))]
  have hbase : (p : Int) ∣ first.coeff i - e.coeff i :=
    Int.dvd_of_emod_eq_zero (hfirst i)
  rcases hbase with ⟨w, hw⟩
  apply Int.emod_eq_zero_of_dvd
  refine ⟨w, ?_⟩
  rw [← Int.mul_sub, hw]
  rw [← Int.mul_assoc]
  have hpow : p ^ (k + 1) = p ^ k * p := by
    rw [Nat.pow_succ]
  rw [hpow]
  change (Int.ofNat (p ^ k) * Int.ofNat p) * w = Int.ofNat (p ^ k * p) * w
  rfl

private theorem liftScaledCoeff_product_dvd_next
    (p k : Nat) [ZMod64.Bounds p]
    (r hCorrection : FpPoly p) (_hk : 1 ≤ k) (i j : Nat) :
    ((p ^ (k + 1) : Nat) : Int) ∣
      (LinearLiftResult.liftScaledIncrement p k r).coeff i *
        (LinearLiftResult.liftScaledIncrement p k hCorrection).coeff j := by
  rcases Nat.exists_eq_add_of_le _hk with ⟨k0, rfl⟩
  rw [LinearLiftResult.coeff_liftScaledIncrement,
    LinearLiftResult.coeff_liftScaledIncrement]
  refine ⟨Int.ofNat (p ^ k0 * (r.coeff i).toNat * (hCorrection.coeff j).toNat), ?_⟩
  have hpow_exp : (1 + k0) + (1 + k0) = (1 + k0 + 1) + k0 := by
    omega
  have hpow : p ^ (1 + k0) * p ^ (1 + k0) = p ^ (1 + k0 + 1) * p ^ k0 := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    rw [hpow_exp]
  calc
    Int.ofNat (p ^ (1 + k0)) * Int.ofNat (r.coeff i).toNat *
        (Int.ofNat (p ^ (1 + k0)) * Int.ofNat (hCorrection.coeff j).toNat)
        =
          Int.ofNat (p ^ (1 + k0) * p ^ (1 + k0)) *
            (Int.ofNat (r.coeff i).toNat * Int.ofNat (hCorrection.coeff j).toNat) := by
          grind
    _ =
          Int.ofNat (p ^ (1 + k0 + 1) * p ^ k0) *
            (Int.ofNat (r.coeff i).toNat * Int.ofNat (hCorrection.coeff j).toNat) := by
          rw [hpow]
    _ =
          Int.ofNat (p ^ (1 + k0 + 1)) *
            Int.ofNat (p ^ k0 * (r.coeff i).toNat * (hCorrection.coeff j).toNat) := by
          grind

private theorem mulCoeffStep_liftScaled_dvd_next
    (p k : Nat) [ZMod64.Bounds p]
    (r hCorrection : FpPoly p) (_hk : 1 ≤ k)
    (n i : Nat) (acc : Int) (j : Nat)
    (hacc : ((p ^ (k + 1) : Nat) : Int) ∣ acc) :
    ((p ^ (k + 1) : Nat) : Int) ∣
      DensePoly.mulCoeffStep
        (LinearLiftResult.liftScaledIncrement p k r)
        (LinearLiftResult.liftScaledIncrement p k hCorrection)
        n i acc j := by
  by_cases hij : i + j = n
  · rcases hacc with ⟨a, ha⟩
    rcases liftScaledCoeff_product_dvd_next p k r hCorrection _hk i j with ⟨c, hc⟩
    refine ⟨a + c, ?_⟩
    calc
      DensePoly.mulCoeffStep
          (LinearLiftResult.liftScaledIncrement p k r)
          (LinearLiftResult.liftScaledIncrement p k hCorrection)
          n i acc j
          = acc +
              (LinearLiftResult.liftScaledIncrement p k r).coeff i *
                (LinearLiftResult.liftScaledIncrement p k hCorrection).coeff j := by
            simp [DensePoly.mulCoeffStep, hij]
      _ = ((p ^ (k + 1) : Nat) : Int) * a +
            ((p ^ (k + 1) : Nat) : Int) * c := by rw [ha, hc]
      _ = ((p ^ (k + 1) : Nat) : Int) * (a + c) := by grind
  · simpa [DensePoly.mulCoeffStep, hij] using hacc

private theorem foldl_mulCoeffStep_liftScaled_dvd_next
    (p k : Nat) [ZMod64.Bounds p]
    (r hCorrection : FpPoly p) (_hk : 1 ≤ k)
    (n i : Nat) (xs : List Nat) (acc : Int)
    (hacc : ((p ^ (k + 1) : Nat) : Int) ∣ acc) :
    ((p ^ (k + 1) : Nat) : Int) ∣
      xs.foldl
        (DensePoly.mulCoeffStep
          (LinearLiftResult.liftScaledIncrement p k r)
          (LinearLiftResult.liftScaledIncrement p k hCorrection)
          n i)
        acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons j xs ih =>
      simpa using
        ih (DensePoly.mulCoeffStep
          (LinearLiftResult.liftScaledIncrement p k r)
          (LinearLiftResult.liftScaledIncrement p k hCorrection)
          n i acc j)
          (mulCoeffStep_liftScaled_dvd_next p k r hCorrection _hk n i acc j hacc)

private theorem foldl_mulCoeffSum_liftScaled_dvd_next
    (p k : Nat) [ZMod64.Bounds p]
    (r hCorrection : FpPoly p) (_hk : 1 ≤ k)
    (n : Nat) (xs : List Nat) (acc : Int)
    (hacc : ((p ^ (k + 1) : Nat) : Int) ∣ acc) :
    ((p ^ (k + 1) : Nat) : Int) ∣
      xs.foldl
        (fun acc i =>
          (List.range (LinearLiftResult.liftScaledIncrement p k hCorrection).size).foldl
            (DensePoly.mulCoeffStep
              (LinearLiftResult.liftScaledIncrement p k r)
              (LinearLiftResult.liftScaledIncrement p k hCorrection)
              n i)
            acc)
        acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons i xs ih =>
      have hinner :
          ((p ^ (k + 1) : Nat) : Int) ∣
            (List.range (LinearLiftResult.liftScaledIncrement p k hCorrection).size).foldl
              (DensePoly.mulCoeffStep
                (LinearLiftResult.liftScaledIncrement p k r)
                (LinearLiftResult.liftScaledIncrement p k hCorrection)
                n i)
              acc :=
        foldl_mulCoeffStep_liftScaled_dvd_next p k r hCorrection _hk n i
          (List.range (LinearLiftResult.liftScaledIncrement p k hCorrection).size) acc hacc
      simpa using ih
        ((List.range (LinearLiftResult.liftScaledIncrement p k hCorrection).size).foldl
          (DensePoly.mulCoeffStep
            (LinearLiftResult.liftScaledIncrement p k r)
            (LinearLiftResult.liftScaledIncrement p k hCorrection)
            n i)
          acc) hinner

private theorem linearHenselStep_product_expansion_cross_congr
    (p k : Nat) [ZMod64.Bounds p]
    (r hCorrection : FpPoly p)
    (_hk : 1 ≤ k) :
    ZPoly.congr
      (LinearLiftResult.liftScaledIncrement p k r *
        LinearLiftResult.liftScaledIncrement p k hCorrection)
      0
      (p ^ (k + 1)) := by
  intro i
  rw [DensePoly.coeff_mul, DensePoly.coeff_zero]
  apply Int.emod_eq_zero_of_dvd
  unfold DensePoly.mulCoeffSum
  simpa using
    foldl_mulCoeffSum_liftScaled_dvd_next p k r hCorrection _hk i
      (List.range (LinearLiftResult.liftScaledIncrement p k r).size) 0 ⟨0, by simp⟩

private theorem mulCoeffStep_scale_left_int
    (c : Int) (f g : ZPoly) (n i : Nat) (acc : Int) (j : Nat) :
    DensePoly.mulCoeffStep (DensePoly.scale c f) g n i (c * acc) j =
      c * DensePoly.mulCoeffStep f g n i acc j := by
  unfold DensePoly.mulCoeffStep
  by_cases hij : i + j = n
  · rw [if_pos hij, if_pos hij]
    rw [DensePoly.coeff_scale _ _ _ (Int.mul_zero c)]
    grind
  · rw [if_neg hij, if_neg hij]

private theorem foldl_mulCoeffStep_scale_left_int
    (c : Int) (f g : ZPoly) (n i : Nat) (xs : List Nat) (acc : Int) :
    xs.foldl (DensePoly.mulCoeffStep (DensePoly.scale c f) g n i) (c * acc) =
      c * xs.foldl (DensePoly.mulCoeffStep f g n i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons j xs ih =>
      simp only [List.foldl_cons]
      rw [mulCoeffStep_scale_left_int]
      exact ih (DensePoly.mulCoeffStep f g n i acc j)

private theorem foldl_mulCoeffSum_scale_left_int
    (c : Int) (f g : ZPoly) (n : Nat) (xs : List Nat) (acc : Int) :
    xs.foldl
        (fun acc i => (List.range g.size).foldl
          (DensePoly.mulCoeffStep (DensePoly.scale c f) g n i) acc)
        (c * acc) =
      c *
        xs.foldl
          (fun acc i => (List.range g.size).foldl
            (DensePoly.mulCoeffStep f g n i) acc)
          acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [foldl_mulCoeffStep_scale_left_int]
      exact ih
        ((List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc)

private theorem dense_size_scale_int_of_ne_zero
    (c : Int) (hc : c ≠ 0) (f : ZPoly) :
    (DensePoly.scale c f).size = f.size := by
  apply Nat.le_antisymm
  · by_cases hle : (DensePoly.scale c f).size ≤ f.size
    · exact hle
    · exfalso
      have hlt : f.size < (DensePoly.scale c f).size := Nat.lt_of_not_ge hle
      let i := (DensePoly.scale c f).size - 1
      have hpos : 0 < (DensePoly.scale c f).size := by omega
      have hf_le : f.size ≤ i := by omega
      have hcoeff_zero : f.coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le f hf_le
      have hscale_ne :
          (DensePoly.scale c f).coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size (DensePoly.scale c f) hpos
      rw [DensePoly.coeff_scale _ _ _ (Int.mul_zero c), hcoeff_zero] at hscale_ne
      exact hscale_ne (Int.mul_zero c)
  · by_cases hle : f.size ≤ (DensePoly.scale c f).size
    · exact hle
    · exfalso
      have hlt : (DensePoly.scale c f).size < f.size := Nat.lt_of_not_ge hle
      let i := f.size - 1
      have hfpos : 0 < f.size := by omega
      have hscale_le : (DensePoly.scale c f).size ≤ i := by omega
      have hscale_zero : (DensePoly.scale c f).coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le (DensePoly.scale c f) hscale_le
      have hf_ne : f.coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size f hfpos
      rw [DensePoly.coeff_scale _ _ _ (Int.mul_zero c)] at hscale_zero
      exact (Int.mul_ne_zero hc hf_ne) hscale_zero

private theorem dense_scale_mul_left_int
    (c : Int) (hc : c ≠ 0) (f g : ZPoly) :
    DensePoly.scale c f * g = DensePoly.scale c (f * g) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_mul, DensePoly.coeff_scale _ _ _ (Int.mul_zero c),
    DensePoly.coeff_mul]
  unfold DensePoly.mulCoeffSum
  rw [dense_size_scale_int_of_ne_zero c hc f]
  simpa [Zero.zero] using
    (foldl_mulCoeffSum_scale_left_int c f g n (List.range f.size) 0)

private theorem dense_scale_mul_right_int
    (c : Int) (hc : c ≠ 0) (f g : ZPoly) :
    f * DensePoly.scale c g = DensePoly.scale c (f * g) := by
  rw [DensePoly.mul_comm_poly f (DensePoly.scale c g)]
  rw [dense_scale_mul_left_int c hc]
  rw [DensePoly.mul_comm_poly g f]

private theorem dense_scale_add_int
    (c : Int) (f g : ZPoly) :
    DensePoly.scale c (f + g) = DensePoly.scale c f + DensePoly.scale c g := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale _ _ _ (Int.mul_zero c)]
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_scale _ _ _ (Int.mul_zero c)]
  rw [DensePoly.coeff_scale _ _ _ (Int.mul_zero c)]
  grind

private theorem add_cross_congr
    (m : Nat) (base a b cross : ZPoly)
    (hcross : ZPoly.congr cross 0 m) :
    ZPoly.congr (base + a + (b + cross)) (base + (a + b)) m := by
  intro i
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_add_semiring]
  have hx := hcross i
  rw [DensePoly.coeff_zero] at hx
  have hdiff :
      (base.coeff i + a.coeff i + (b.coeff i + cross.coeff i) -
          (base.coeff i + (a.coeff i + b.coeff i))) =
        cross.coeff i := by
    omega
  rw [hdiff]
  simpa using hx

private theorem linearHenselStep_product_expansion_identity_congr_core
    (p k : Nat) [ZMod64.Bounds p]
    (g h : ZPoly) (r hCorrection : FpPoly p)
    (_hk : 1 ≤ k) :
    ZPoly.congr
      ((g + LinearLiftResult.liftScaledIncrement p k r) *
        (h + LinearLiftResult.liftScaledIncrement p k hCorrection))
      (g * h +
        DensePoly.scale (Int.ofNat (p ^ k))
          (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection))
      (p ^ (k + 1)) := by
  have hscale_ne : Int.ofNat (p ^ k) ≠ 0 := by
    exact Int.ofNat_ne_zero.mpr
      (Nat.ne_of_gt (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)) : 0 < p ^ k))
  unfold LinearLiftResult.liftScaledIncrement
  rw [DensePoly.mul_add_right_poly]
  rw [DensePoly.mul_add_left_poly g
    (DensePoly.scale (Int.ofNat (p ^ k)) (FpPoly.liftToZ r))
    (DensePoly.scale (Int.ofNat (p ^ k)) (FpPoly.liftToZ hCorrection))]
  rw [DensePoly.mul_add_left_poly g
    (DensePoly.scale (Int.ofNat (p ^ k)) (FpPoly.liftToZ r))
    h]
  rw [dense_scale_mul_left_int (Int.ofNat (p ^ k)) hscale_ne (FpPoly.liftToZ r) h]
  rw [dense_scale_mul_right_int (Int.ofNat (p ^ k)) hscale_ne g
    (FpPoly.liftToZ hCorrection)]
  rw [dense_scale_add_int (Int.ofNat (p ^ k)) (FpPoly.liftToZ r * h)
    (g * FpPoly.liftToZ hCorrection)]
  let cross :=
    DensePoly.scale (Int.ofNat (p ^ k)) (FpPoly.liftToZ r) *
      DensePoly.scale (Int.ofNat (p ^ k)) (FpPoly.liftToZ hCorrection)
  have hcross :
      ZPoly.congr cross 0 (p ^ (k + 1)) := by
    simpa [cross, LinearLiftResult.liftScaledIncrement] using
      linearHenselStep_product_expansion_cross_congr p k r hCorrection _hk
  simpa [cross] using
    add_cross_congr (p ^ (k + 1)) (g * h)
      (DensePoly.scale (Int.ofNat (p ^ k)) (FpPoly.liftToZ r * h))
      (DensePoly.scale (Int.ofNat (p ^ k)) (g * FpPoly.liftToZ hCorrection))
      cross hcross

private theorem linearHenselStep_product_expansion_identity_congr
    (p k : Nat) [ZMod64.Bounds p]
    (g h : ZPoly) (r hCorrection : FpPoly p)
    (_hk : 1 ≤ k) :
    let g' := g + LinearLiftResult.liftScaledIncrement p k r
    let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
    ZPoly.congr
      (g' * h')
      (g * h +
        DensePoly.scale (Int.ofNat (p ^ k))
          (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection))
      (p ^ (k + 1)) := by
  intro g' h'
  simpa [g', h'] using
    linearHenselStep_product_expansion_identity_congr_core p k g h r hCorrection _hk

private theorem linearHenselStep_recombine_error_congr
    (p k : Nat) (f g h : ZPoly) :
    ZPoly.congr (g * h + (f - g * h)) f (p ^ (k + 1)) := by
  intro i
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_sub_ring]
  have hzero :
      (g * h).coeff i + (f.coeff i - (g * h).coeff i) - f.coeff i = 0 := by
    omega
  rw [hzero]
  simp

private theorem linearHenselStep_first_order_congr
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (r hCorrection : FpPoly p)
    (hcorr :
      r * ZPoly.modP p h + ZPoly.modP p g * hCorrection =
        ZPoly.modP p (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))) :
    ZPoly.congr
      (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection)
      (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))
      p := by
  have hmod :
      ZPoly.modP p
        (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection) =
        r * ZPoly.modP p h + ZPoly.modP p g * hCorrection :=
    modP_add_lift_mul p g h r hCorrection
  have hlift :
      ZPoly.congr
        (FpPoly.liftToZ (r * ZPoly.modP p h + ZPoly.modP p g * hCorrection))
        (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection)
        p :=
    congr_liftToZ_of_modP_eq p
      (r * ZPoly.modP p h + ZPoly.modP p g * hCorrection)
      (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection)
      hmod
  have he :
      ZPoly.congr
        (FpPoly.liftToZ (ZPoly.modP p (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))))
        (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))
        p :=
    FpPoly.congr_liftToZ_modP
      (p := p) (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))
  have hcorr' :
      ZPoly.congr
        (FpPoly.liftToZ (r * ZPoly.modP p h + ZPoly.modP p g * hCorrection))
        (FpPoly.liftToZ (ZPoly.modP p (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))))
        p := by
    rw [hcorr]
    exact ZPoly.congr_refl _ p
  exact ZPoly.congr_trans _ _ _ p
    (ZPoly.congr_symm _ _ _ hlift)
    (ZPoly.congr_trans _ _ _ p hcorr' he)

private theorem linearHenselStep_scaled_first_order_congr
    (p k : Nat) [ZMod64.Bounds p]
    (f g h first e : ZPoly)
    (_hk : 1 ≤ k)
    (hbase : DensePoly.scale (Int.ofNat (p ^ k)) e = f - g * h)
    (hfirst : ZPoly.congr first e p) :
    ZPoly.congr
      (DensePoly.scale (Int.ofNat (p ^ k)) first)
      (f - g * h)
      (p ^ (k + 1)) := by
  rw [← hbase]
  exact scale_congr_of_congr_mod_base p k first e _hk hfirst

private theorem linearHenselStep_product_expansion_congr
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (r hCorrection : FpPoly p)
    (_hk : 1 ≤ k)
    (_hprod : ZPoly.congr (g * h) f (p ^ k))
    (hfirst :
      ZPoly.congr
        (DensePoly.scale (Int.ofNat (p ^ k))
          (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection))
        (f - g * h)
        (p ^ (k + 1))) :
    let g' := g + LinearLiftResult.liftScaledIncrement p k r
    let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
    ZPoly.congr (g' * h') f (p ^ (k + 1)) := by
  intro g' h'
  have hexpand :
      ZPoly.congr
        (g' * h')
        (g * h +
          DensePoly.scale (Int.ofNat (p ^ k))
            (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection))
        (p ^ (k + 1)) := by
    simpa [g', h', LinearLiftResult.liftScaledIncrement] using
      linearHenselStep_product_expansion_identity_congr p k g h r hCorrection _hk
  have hsum :
      ZPoly.congr
        (g * h +
          DensePoly.scale (Int.ofNat (p ^ k))
            (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection))
        (g * h + (f - g * h))
        (p ^ (k + 1)) :=
    ZPoly.congr_add _ _ _ _ _
      (ZPoly.congr_refl (g * h) (p ^ (k + 1))) hfirst
  exact ZPoly.congr_trans _ _ _ _ hexpand
    (ZPoly.congr_trans _ _ _ _
      hsum (linearHenselStep_recombine_error_congr p k f g h))

private theorem linearHenselStep_raw_factor_congr_from_correction
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (r hCorrection _e : FpPoly p)
    (hk : 1 ≤ k)
    (hprod : ZPoly.congr (g * h) f (p ^ k))
    (hcorr :
      r * ZPoly.modP p h + ZPoly.modP p g * hCorrection =
        ZPoly.modP p (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))) :
    let g' := g + LinearLiftResult.liftScaledIncrement p k r
    let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
    ZPoly.congr (g' * h') f (p ^ (k + 1)) := by
  intro g' h'
  let eZ := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
  let first := FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection
  have hbase : DensePoly.scale (Int.ofNat (p ^ k)) eZ = f - g * h := by
    simpa [eZ] using ZPoly.scale_coeffwiseDiv_sub_of_congr f (g * h) (p ^ k) hprod
  have hfirst : ZPoly.congr first eZ p := by
    simpa [first, eZ] using
      linearHenselStep_first_order_congr p k f g h r hCorrection hcorr
  have hscaled :
      ZPoly.congr
        (DensePoly.scale (Int.ofNat (p ^ k)) first)
        (f - g * h)
        (p ^ (k + 1)) :=
    linearHenselStep_scaled_first_order_congr p k f g h first eZ hk hbase hfirst
  simpa [g', h', first] using
    linearHenselStep_product_expansion_congr p k f g h r hCorrection hk hprod hscaled

private theorem linearHenselStep_raw_factor_congr
    (p k : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hk : 1 ≤ k)
    (hprod : ZPoly.congr (g * h) f (p ^ k))
    (hbez :
      ZPoly.congr
        (FpPoly.liftToZ (s * ZPoly.modP p g + t * ZPoly.modP p h))
        1 p)
    (_hmonic : DensePoly.Monic g) :
    let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
    let gMod := ZPoly.modP p g
    let hMod := ZPoly.modP p h
    let eMod := ZPoly.modP p e
    let qr := DensePoly.divMod (t * eMod) gMod
    let q := qr.1
    let r := qr.2
    let g' := g + LinearLiftResult.liftScaledIncrement p k r
    let hCorrection := s * eMod + q * hMod
    let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
    ZPoly.congr (g' * h') f (p ^ (k + 1)) := by
  intro e gMod hMod eMod qr q r g' hCorrection h'
  have hdiv : q * gMod + r = t * eMod := by
    simpa [qr, q, r] using DensePoly.divMod_spec (t * eMod) gMod
  have hbezFp : s * gMod + t * hMod = 1 := by
    have hmod := ZPoly.modP_eq_of_congr p _ _ hbez
    rw [FpPoly.modP_liftToZ, modP_one] at hmod
    exact hmod
  have hcorr :
      r * hMod + gMod * hCorrection = eMod := by
    simpa [hCorrection] using
      linearHenselStep_correction_identity p gMod hMod eMod s t q r hdiv hbezFp
  exact
    linearHenselStep_raw_factor_congr_from_correction
      p k f g h r hCorrection eMod hk hprod hcorr

private theorem linearHenselStep_reduced_factor_congr
    (p k : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hk : 1 ≤ k)
    (hprod : ZPoly.congr (g * h) f (p ^ k))
    (hbez :
      ZPoly.congr
        (FpPoly.liftToZ (s * ZPoly.modP p g + t * ZPoly.modP p h))
        1 p)
    (hmonic : DensePoly.Monic g) :
    let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
    let gMod := ZPoly.modP p g
    let hMod := ZPoly.modP p h
    let eMod := ZPoly.modP p e
    let qr := DensePoly.divMod (t * eMod) gMod
    let q := qr.1
    let r := qr.2
    let g' := g + LinearLiftResult.liftScaledIncrement p k r
    let hCorrection := s * eMod + q * hMod
    let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
    ZPoly.congr
      (ZPoly.reduceModPow g' p (k + 1) * ZPoly.reduceModPow h' p (k + 1))
      f
      (p ^ (k + 1)) := by
  intro e gMod hMod eMod qr q r g' hCorrection h'
  exact ZPoly.congr_trans
    (ZPoly.reduceModPow g' p (k + 1) * ZPoly.reduceModPow h' p (k + 1))
    (g' * h')
    f
    (p ^ (k + 1))
    (congr_mul_reduceModPow_pair p (k + 1) g' h')
    (by
      simpa [e, gMod, hMod, eMod, qr, q, r, g', hCorrection, h'] using
        linearHenselStep_raw_factor_congr p k f g h s t hk hprod hbez hmonic)

private def henselLiftLoop
    (p : Nat) [ZMod64.Bounds p]
    (steps current : Nat)
    (f : ZPoly) (s t : FpPoly p)
    (acc : LinearLiftResult) : LinearLiftResult :=
  match steps with
  | 0 => acc
  | steps + 1 =>
      let next := linearHenselStep p current f acc.g acc.h s t
      henselLiftLoop p steps (current + 1) f s t next

/-- The proof state carried by the linear Hensel loop at precision `p^current`. -/
def LinearLiftLoopInvariant
    (p current : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (s t : FpPoly p) (acc : LinearLiftResult) : Prop :=
  ZPoly.congr (acc.g * acc.h) f (p ^ current) ∧
    ZPoly.congr
      (FpPoly.liftToZ (s * ZPoly.modP p acc.g + t * ZPoly.modP p acc.h))
      1 p ∧
    DensePoly.Monic acc.g

namespace LinearLiftLoopInvariant

/-- The product-congruence component of a linear-lift loop invariant. -/
theorem product_congr
    {p current : Nat} [ZMod64.Bounds p]
    {f : ZPoly} {s t : FpPoly p} {acc : LinearLiftResult}
    (hinv : LinearLiftLoopInvariant p current f s t acc) :
    ZPoly.congr (acc.g * acc.h) f (p ^ current) :=
  hinv.1

/-- The Bezout-congruence component of a linear-lift loop invariant. -/
theorem bezout_congr
    {p current : Nat} [ZMod64.Bounds p]
    {f : ZPoly} {s t : FpPoly p} {acc : LinearLiftResult}
    (hinv : LinearLiftLoopInvariant p current f s t acc) :
    ZPoly.congr
      (FpPoly.liftToZ (s * ZPoly.modP p acc.g + t * ZPoly.modP p acc.h))
      1 p :=
  hinv.2.1

/-- The monicity component of a linear-lift loop invariant. -/
theorem monic_g
    {p current : Nat} [ZMod64.Bounds p]
    {f : ZPoly} {s t : FpPoly p} {acc : LinearLiftResult}
    (hinv : LinearLiftLoopInvariant p current f s t acc) :
    DensePoly.Monic acc.g :=
  hinv.2.2

end LinearLiftLoopInvariant

/-- The per-step degree hypothesis needed to preserve monicity of the `g` factor. -/
def LinearLiftStepDegreeInvariant
    (p current : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (_s t : FpPoly p) (acc : LinearLiftResult) : Prop :=
  let e := ZPoly.coeffwiseDiv (f - acc.g * acc.h) (p ^ current)
  let gMod := ZPoly.modP p acc.g
  let eMod := ZPoly.modP p e
  let qr := DensePoly.divMod (t * eMod) gMod
  (LinearLiftResult.liftScaledIncrement p current qr.2).degree?.getD 0 <
    acc.g.degree?.getD 0

/--
Lift a factorization modulo `p` to a factorization modulo `p^k` by iterating the
linear Hensel step.
-/
def henselLift
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p) : LinearLiftResult :=
  match k with
  | 0 =>
      { g := reduceModPow g p 0
        h := reduceModPow h p 0 }
  | k' + 1 =>
      let start :=
        { g := reduceModPow g p 1
          h := reduceModPow h p 1 }
      henselLiftLoop p k' 1 f s t start

/-- The lifted factors still multiply to `f` modulo the next power of `p`. -/
theorem linearHenselStep_spec
    (p k : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hk : 1 ≤ k)
    (hprod : ZPoly.congr (g * h) f (p ^ k))
    (hbez :
      ZPoly.congr
        (FpPoly.liftToZ (s * ZPoly.modP p g + t * ZPoly.modP p h))
        1 p)
    (hmonic : DensePoly.Monic g) :
    let r := linearHenselStep p k f g h s t
    ZPoly.congr (r.g * r.h) f (p ^ (k + 1)) := by
  unfold linearHenselStep
  simpa using
    linearHenselStep_reduced_factor_congr p k f g h s t hk hprod hbez hmonic

private theorem coeff_last_eq_leadingCoeff (f : ZPoly) (hpos : 0 < f.size) :
    f.coeff (f.size - 1) = f.leadingCoeff := by
  cases f with
  | mk coeffs normalized =>
      have hcoeffs : 0 < coeffs.size := by simpa [DensePoly.size] using hpos
      have hidx : coeffs.size - 1 < coeffs.size := Nat.sub_one_lt (Nat.ne_of_gt hcoeffs)
      change coeffs.getD (coeffs.size - 1) 0 = coeffs.back?.getD 0
      rw [Array.back?_eq_getElem?]
      rw [Array.getElem?_eq_getElem hidx]
      exact (Array.getElem_eq_getD 0).symm

private theorem monic_size_pos (f : ZPoly) (hmonic : DensePoly.Monic f) :
    0 < f.size := by
  by_cases hpos : 0 < f.size
  · exact hpos
  · have hsize : f.size = 0 := Nat.eq_zero_of_not_pos hpos
    have hlead : f.leadingCoeff = 0 := by
      cases f with
      | mk coeffs normalized =>
          simp [DensePoly.leadingCoeff, DensePoly.size] at hsize ⊢
          simp [hsize]
    have hlead_one : f.leadingCoeff = 1 := by
      simpa [DensePoly.Monic] using hmonic
    rw [hlead] at hlead_one
    exact False.elim (Int.zero_ne_one hlead_one)

private theorem degree?_eq_some_of_coeff_eq_one_and_high_coeff_zero
    (f : ZPoly) (n : Nat)
    (hone : f.coeff n = 1)
    (hhigh : ∀ i, n < i → f.coeff i = 0) :
    f.degree? = some n := by
  have hn_lt_size : n < f.size := by
    by_cases hn : n < f.size
    · exact hn
    · have hcoeff := DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hn)
      rw [hone] at hcoeff
      exact False.elim (Int.one_ne_zero hcoeff)
  have hsize_le : f.size ≤ n + 1 := by
    by_cases hle : f.size ≤ n + 1
    · exact hle
    · have hlast_zero : f.coeff (f.size - 1) = 0 := by
        apply hhigh
        omega
      have hlast_ne : f.coeff (f.size - 1) ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size f (by omega)
      exact False.elim (hlast_ne hlast_zero)
  have hsize : f.size = n + 1 := by omega
  unfold DensePoly.degree?
  simp [hsize]

private theorem monic_of_coeff_eq_one_and_high_coeff_zero
    (f : ZPoly) (n : Nat)
    (hone : f.coeff n = 1)
    (hhigh : ∀ i, n < i → f.coeff i = 0) :
    DensePoly.Monic f := by
  have hdeg := degree?_eq_some_of_coeff_eq_one_and_high_coeff_zero f n hone hhigh
  have hsize : f.size = n + 1 := by
    unfold DensePoly.degree? at hdeg
    by_cases hzero : f.size = 0
    · simp [hzero] at hdeg
    · simp [hzero] at hdeg
      omega
  unfold DensePoly.Monic
  have hlast := coeff_last_eq_leadingCoeff f (by omega)
  rw [hsize] at hlast
  have hidx : n + 1 - 1 = n := by omega
  rw [hidx] at hlast
  rw [← hlast]
  exact hone

private theorem degree?_eq_some_size_sub_one_of_monic
    (f : ZPoly) (hmonic : DensePoly.Monic f) :
    f.degree? = some (f.size - 1) := by
  unfold DensePoly.degree?
  have hpos := monic_size_pos f hmonic
  simp [Nat.ne_of_gt hpos]

private theorem degree?_getD_eq_size_sub_one_of_monic
    (f : ZPoly) (hmonic : DensePoly.Monic f) :
    f.degree?.getD 0 = f.size - 1 := by
  rw [degree?_eq_some_size_sub_one_of_monic f hmonic]
  rfl

private theorem coeff_last_eq_one_of_monic
    (f : ZPoly) (hmonic : DensePoly.Monic f) :
    f.coeff (f.size - 1) = 1 := by
  rw [coeff_last_eq_leadingCoeff f (monic_size_pos f hmonic)]
  simpa [DensePoly.Monic] using hmonic

private theorem size_le_of_degree?_getD_lt
    (f : ZPoly) {n : Nat}
    (hdeg : f.degree?.getD 0 < n) :
    f.size ≤ n := by
  unfold DensePoly.degree? at hdeg
  by_cases hzero : f.size = 0
  · omega
  · simp [hzero] at hdeg
    omega

private theorem add_low_degree_degree?_eq
    (g a : ZPoly)
    (hmonic : DensePoly.Monic g)
    (hdeg : a.degree?.getD 0 < g.degree?.getD 0) :
    (g + a).degree? = g.degree? := by
  let n := g.size - 1
  have hgpos := monic_size_pos g hmonic
  have hgdeg : g.degree?.getD 0 = n := by
    simpa [n] using degree?_getD_eq_size_sub_one_of_monic g hmonic
  have hasize : a.size ≤ n := by
    apply size_le_of_degree?_getD_lt a
    simpa [hgdeg] using hdeg
  have hone : (g + a).coeff n = 1 := by
    rw [DensePoly.coeff_add g a n (by rfl)]
    have ha : a.coeff n = 0 := DensePoly.coeff_eq_zero_of_size_le a hasize
    have hg : g.coeff n = 1 := by
      simpa [n] using coeff_last_eq_one_of_monic g hmonic
    rw [hg, ha]
    omega
  have hhigh : ∀ i, n < i → (g + a).coeff i = 0 := by
    intro i hi
    rw [DensePoly.coeff_add g a i (by rfl)]
    have hgzero : g.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le g (by omega)
    have hazero : a.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le a (by omega)
    rw [hgzero, hazero]
    rfl
  calc
    (g + a).degree? = some n :=
      degree?_eq_some_of_coeff_eq_one_and_high_coeff_zero (g + a) n hone hhigh
    _ = g.degree? := by
      rw [degree?_eq_some_size_sub_one_of_monic g hmonic]

private theorem add_low_degree_monic
    (g a : ZPoly)
    (hmonic : DensePoly.Monic g)
    (hdeg : a.degree?.getD 0 < g.degree?.getD 0) :
    DensePoly.Monic (g + a) := by
  let n := g.size - 1
  have hgdeg : g.degree?.getD 0 = n := by
    simpa [n] using degree?_getD_eq_size_sub_one_of_monic g hmonic
  have hasize : a.size ≤ n := by
    apply size_le_of_degree?_getD_lt a
    simpa [hgdeg] using hdeg
  have hone : (g + a).coeff n = 1 := by
    rw [DensePoly.coeff_add g a n (by rfl)]
    have ha : a.coeff n = 0 := DensePoly.coeff_eq_zero_of_size_le a hasize
    have hg : g.coeff n = 1 := by
      simpa [n] using coeff_last_eq_one_of_monic g hmonic
    rw [hg, ha]
    omega
  have hhigh : ∀ i, n < i → (g + a).coeff i = 0 := by
    intro i hi
    rw [DensePoly.coeff_add g a i (by rfl)]
    have hgzero : g.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le g (by omega)
    have hazero : a.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le a (by omega)
    rw [hgzero, hazero]
    rfl
  exact monic_of_coeff_eq_one_and_high_coeff_zero (g + a) n hone hhigh

private theorem one_lt_pow_succ_of_one_lt (p k : Nat) (hp : 1 < p) :
    1 < p ^ (k + 1) := by
  induction k with
  | zero =>
      simpa using hp
  | succ k ih =>
      rw [Nat.add_succ, Nat.pow_succ]
      exact Nat.lt_of_lt_of_le ih
        (Nat.le_mul_of_pos_right (p ^ (k + 1)) (Nat.zero_lt_of_lt hp))

private theorem reduceModPow_degree?_eq_of_monic
    (p k : Nat) (f : ZPoly)
    (hp : 1 < p)
    (hmonic : DensePoly.Monic f) :
    (ZPoly.reduceModPow f p (k + 1)).degree? = f.degree? := by
  let n := f.size - 1
  have hmodpos : 0 < p ^ (k + 1) := Nat.pow_pos (by omega)
  have hmodgt : 1 < p ^ (k + 1) := one_lt_pow_succ_of_one_lt p k hp
  have hone : (ZPoly.reduceModPow f p (k + 1)).coeff n = 1 := by
    rw [ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hmodpos]
    have hf : f.coeff n = 1 := by
      simpa [n] using coeff_last_eq_one_of_monic f hmonic
    rw [hf]
    exact Int.emod_eq_of_lt (by decide) (by
      change Int.ofNat 1 < Int.ofNat (p ^ (k + 1))
      exact Int.ofNat_lt.mpr hmodgt)
  have hhigh : ∀ i, n < i → (ZPoly.reduceModPow f p (k + 1)).coeff i = 0 := by
    intro i hi
    apply ZPoly.coeff_reduceModPow_eq_zero_of_emod
    have hfzero : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f (by omega)
    rw [hfzero]
    simp
  calc
    (ZPoly.reduceModPow f p (k + 1)).degree? =
        some n :=
      degree?_eq_some_of_coeff_eq_one_and_high_coeff_zero
        (ZPoly.reduceModPow f p (k + 1)) n hone hhigh
    _ = f.degree? := by
      rw [degree?_eq_some_size_sub_one_of_monic f hmonic]

theorem reduceModPow_monic_of_monic
    (p k : Nat) (f : ZPoly)
    (hp : 1 < p)
    (hmonic : DensePoly.Monic f) :
    DensePoly.Monic (ZPoly.reduceModPow f p (k + 1)) := by
  let n := f.size - 1
  have hmodpos : 0 < p ^ (k + 1) := Nat.pow_pos (by omega)
  have hmodgt : 1 < p ^ (k + 1) := one_lt_pow_succ_of_one_lt p k hp
  have hone : (ZPoly.reduceModPow f p (k + 1)).coeff n = 1 := by
    rw [ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hmodpos]
    have hf : f.coeff n = 1 := by
      simpa [n] using coeff_last_eq_one_of_monic f hmonic
    rw [hf]
    exact Int.emod_eq_of_lt (by decide) (by
      change Int.ofNat 1 < Int.ofNat (p ^ (k + 1))
      exact Int.ofNat_lt.mpr hmodgt)
  have hhigh : ∀ i, n < i → (ZPoly.reduceModPow f p (k + 1)).coeff i = 0 := by
    intro i hi
    apply ZPoly.coeff_reduceModPow_eq_zero_of_emod
    have hfzero : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f (by omega)
    rw [hfzero]
    simp
  exact monic_of_coeff_eq_one_and_high_coeff_zero
    (ZPoly.reduceModPow f p (k + 1)) n hone hhigh

/-- The linear step preserves monicity of the lifted `g` factor. -/
theorem linearHenselStep_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hp : 1 < p)
    (hmonic : DensePoly.Monic g)
    (hgCorrectionDegree :
      let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
      let gMod := ZPoly.modP p g
      let eMod := ZPoly.modP p e
      let qr := DensePoly.divMod (t * eMod) gMod
      (LinearLiftResult.liftScaledIncrement p k qr.2).degree?.getD 0 < g.degree?.getD 0) :
    DensePoly.Monic (linearHenselStep p k f g h s t).g := by
  unfold linearHenselStep
  let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
  let gMod := ZPoly.modP p g
  let eMod := ZPoly.modP p e
  let qr := DensePoly.divMod (t * eMod) gMod
  let g' := g + LinearLiftResult.liftScaledIncrement p k qr.2
  have hgRaw : DensePoly.Monic g' := by
    exact add_low_degree_monic g (LinearLiftResult.liftScaledIncrement p k qr.2)
      hmonic (by simpa [e, gMod, eMod, qr] using hgCorrectionDegree)
  simpa [e, gMod, eMod, qr, g'] using reduceModPow_monic_of_monic p k g' hp hgRaw

/-- The linear step preserves the degree of the monic `g` factor. -/
theorem linearHenselStep_g_degree?_eq
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hp : 1 < p)
    (hmonic : DensePoly.Monic g)
    (hgCorrectionDegree :
      let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
      let gMod := ZPoly.modP p g
      let eMod := ZPoly.modP p e
      let qr := DensePoly.divMod (t * eMod) gMod
      (LinearLiftResult.liftScaledIncrement p k qr.2).degree?.getD 0 < g.degree?.getD 0) :
    (linearHenselStep p k f g h s t).g.degree? = g.degree? := by
  unfold linearHenselStep
  let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
  let gMod := ZPoly.modP p g
  let eMod := ZPoly.modP p e
  let qr := DensePoly.divMod (t * eMod) gMod
  let g' := g + LinearLiftResult.liftScaledIncrement p k qr.2
  have hgRawMonic : DensePoly.Monic g' := by
    exact add_low_degree_monic g (LinearLiftResult.liftScaledIncrement p k qr.2)
      hmonic (by simpa [e, gMod, eMod, qr] using hgCorrectionDegree)
  have hgRawDegree : g'.degree? = g.degree? := by
    exact add_low_degree_degree?_eq g (LinearLiftResult.liftScaledIncrement p k qr.2)
      hmonic (by simpa [e, gMod, eMod, qr] using hgCorrectionDegree)
  calc
    (ZPoly.reduceModPow g' p (k + 1)).degree? = g'.degree? :=
      reduceModPow_degree?_eq_of_monic p k g' hp hgRawMonic
    _ = g.degree? := hgRawDegree

/-- The linear step keeps the degree of `h` unchanged under the expected invariant. -/
theorem linearHenselStep_h_degree?_eq
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (_hp : 1 < p)
    (_hprod : ZPoly.congr (g * h) f (p ^ k))
    (hhRawDegree :
      let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
      let gMod := ZPoly.modP p g
      let hMod := ZPoly.modP p h
      let eMod := ZPoly.modP p e
      let qr := DensePoly.divMod (t * eMod) gMod
      let hCorrection := s * eMod + qr.1 * hMod
      let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
      h'.degree? = h.degree?)
    (hhReducedDegree :
      let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
      let gMod := ZPoly.modP p g
      let hMod := ZPoly.modP p h
      let eMod := ZPoly.modP p e
      let qr := DensePoly.divMod (t * eMod) gMod
      let hCorrection := s * eMod + qr.1 * hMod
      let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
      (ZPoly.reduceModPow h' p (k + 1)).degree? = h'.degree?) :
    (linearHenselStep p k f g h s t).h.degree? = h.degree? := by
  unfold linearHenselStep
  let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
  let gMod := ZPoly.modP p g
  let hMod := ZPoly.modP p h
  let eMod := ZPoly.modP p e
  let qr := DensePoly.divMod (t * eMod) gMod
  let hCorrection := s * eMod + qr.1 * hMod
  let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
  calc
    (ZPoly.reduceModPow h' p (k + 1)).degree? = h'.degree? := by
      simpa [e, gMod, hMod, eMod, qr, hCorrection, h'] using hhReducedDegree
    _ = h.degree? := by
      simpa [e, gMod, hMod, eMod, qr, hCorrection, h'] using hhRawDegree

private theorem henselLiftLoop_invariant
    (p steps current : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f : ZPoly) (s t : FpPoly p) (acc : LinearLiftResult)
    (hp : 1 < p)
    (hcurrent : 1 ≤ current)
    (hinv : LinearLiftLoopInvariant p current f s t acc)
    (hstepDegree :
      ∀ (n : Nat) (state : LinearLiftResult),
        current ≤ n →
        LinearLiftLoopInvariant p n f s t state →
        LinearLiftStepDegreeInvariant p n f s t state)
    (hstepBezout :
      ∀ (n : Nat) (state : LinearLiftResult),
        current ≤ n →
        LinearLiftLoopInvariant p n f s t state →
        let next := linearHenselStep p n f state.g state.h s t
        ZPoly.congr
          (FpPoly.liftToZ (s * ZPoly.modP p next.g + t * ZPoly.modP p next.h))
          1 p) :
    LinearLiftLoopInvariant p (current + steps) f s t
      (henselLiftLoop p steps current f s t acc) := by
  induction steps generalizing current acc with
  | zero =>
      simpa [henselLiftLoop] using hinv
  | succ steps ih =>
      let next := linearHenselStep p current f acc.g acc.h s t
      have hnext :
          LinearLiftLoopInvariant p (current + 1) f s t next := by
        rcases hinv with ⟨hprod, hbez, hmonic⟩
        refine ⟨?_, ?_, ?_⟩
        · simpa [next] using
            linearHenselStep_spec p current f acc.g acc.h s t hcurrent hprod hbez hmonic
        · simpa [next] using hstepBezout current acc (by omega) ⟨hprod, hbez, hmonic⟩
        · exact
            linearHenselStep_monic p current f acc.g acc.h s t hp hmonic
              (by
                simpa [LinearLiftStepDegreeInvariant] using
                  hstepDegree current acc (by omega) ⟨hprod, hbez, hmonic⟩)
      have htail :
          LinearLiftLoopInvariant p ((current + 1) + steps) f s t
            (henselLiftLoop p steps (current + 1) f s t next) := by
        apply ih (current := current + 1) (acc := next)
        · omega
        · exact hnext
        · intro n state hn hstate
          exact hstepDegree n state (by omega) hstate
        · intro n state hn hstate
          exact hstepBezout n state (by omega) hstate
      simpa [henselLiftLoop, next, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- The iterative linear wrapper lifts the factorization to congruence modulo `p^k`. -/
theorem henselLift_spec
    (p k : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hstart :
      LinearLiftLoopInvariant p 1 f s t
        { g := ZPoly.reduceModPow g p 1
          h := ZPoly.reduceModPow h p 1 })
    (hstepDegree :
      ∀ (n : Nat) (state : LinearLiftResult),
        1 ≤ n →
        LinearLiftLoopInvariant p n f s t state →
        LinearLiftStepDegreeInvariant p n f s t state)
    (hstepBezout :
      ∀ (n : Nat) (state : LinearLiftResult),
        1 ≤ n →
        LinearLiftLoopInvariant p n f s t state →
        let next := linearHenselStep p n f state.g state.h s t
        ZPoly.congr
          (FpPoly.liftToZ (s * ZPoly.modP p next.g + t * ZPoly.modP p next.h))
          1 p) :
    let r := henselLift p k f g h s t
    ZPoly.congr (r.g * r.h) f (p ^ k) := by
  cases k with
  | zero =>
      omega
  | succ k' =>
      let start : LinearLiftResult :=
        { g := ZPoly.reduceModPow g p 1
          h := ZPoly.reduceModPow h p 1 }
      have hloop :
          LinearLiftLoopInvariant p (1 + k') f s t
            (henselLiftLoop p k' 1 f s t start) := by
        simpa [start] using
          henselLiftLoop_invariant p k' 1 f s t start hp (by omega) (by simpa [start] using hstart)
            hstepDegree hstepBezout
      simpa [henselLift, start, Nat.add_comm] using hloop.1

/-- The iterative linear wrapper preserves monicity of the lifted `g` factor. -/
theorem henselLift_monic
    (p k : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hstart :
      LinearLiftLoopInvariant p 1 f s t
        { g := ZPoly.reduceModPow g p 1
          h := ZPoly.reduceModPow h p 1 })
    (hstepDegree :
      ∀ (n : Nat) (state : LinearLiftResult),
        1 ≤ n →
        LinearLiftLoopInvariant p n f s t state →
        LinearLiftStepDegreeInvariant p n f s t state)
    (hstepBezout :
      ∀ (n : Nat) (state : LinearLiftResult),
        1 ≤ n →
        LinearLiftLoopInvariant p n f s t state →
        let next := linearHenselStep p n f state.g state.h s t
        ZPoly.congr
          (FpPoly.liftToZ (s * ZPoly.modP p next.g + t * ZPoly.modP p next.h))
          1 p) :
    DensePoly.Monic (henselLift p k f g h s t).g := by
  cases k with
  | zero =>
      omega
  | succ k' =>
      let start : LinearLiftResult :=
        { g := ZPoly.reduceModPow g p 1
          h := ZPoly.reduceModPow h p 1 }
      have hloop :
          LinearLiftLoopInvariant p (1 + k') f s t
            (henselLiftLoop p k' 1 f s t start) := by
        simpa [start] using
          henselLiftLoop_invariant p k' 1 f s t start hp (by omega) (by simpa [start] using hstart)
            hstepDegree hstepBezout
      simpa [henselLift, start] using hloop.2.2

end ZPoly
end Hex

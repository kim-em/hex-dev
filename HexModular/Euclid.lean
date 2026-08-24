/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith

public section

/-!
Truncated extended-Euclidean rows for rational reconstruction.
-/
namespace Hex

namespace Modular

/-- One row of the extended Euclidean remainder sequence on `(m, a)`. The
omitted coefficient of `m` is never inspected by reconstruction consumers. -/
structure Row where
  /-- The current Euclidean remainder. -/
  r : Int
  /-- The coefficient of the second input `a`. -/
  t : Int
  deriving DecidableEq

/-- Continue the nonnegative Euclidean recurrence until the current remainder
is at most `P`, or until the zero remainder is reached. -/
private def euclidUntil.go (P : Int) (oldR r : Nat) (oldT t : Int) : Row :=
  if (r : Int) ≤ P then
    { r := Int.ofNat r, t }
  else if _hr : r = 0 then
    { r := 0, t }
  else
    let q := oldR / r
    euclidUntil.go P r (oldR % r) t (oldT - Int.ofNat q * t)
termination_by r
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _hr)

private theorem cramer_fst (oldR r p q oldT t : Int) :
    oldR * (p * t - r * q) + r * (oldR * q - p * oldT) =
      p * (oldR * t - r * oldT) := by
  simp only [Int.mul_sub]
  have hcancel : oldR * (r * q) = r * (oldR * q) := by ac_rfl
  have hleft : oldR * (p * t) = p * (oldR * t) := by ac_rfl
  have hright : r * (p * oldT) = p * (r * oldT) := by ac_rfl
  rw [hcancel, hleft, hright]
  omega

private theorem cramer_snd (oldR r p q oldT t : Int) :
    oldT * (p * t - r * q) + t * (oldR * q - p * oldT) =
      q * (oldR * t - r * oldT) := by
  simp only [Int.mul_sub]
  have hcancel : oldT * (p * t) = t * (p * oldT) := by ac_rfl
  have hleft : oldT * (r * q) = q * (r * oldT) := by ac_rfl
  have hright : t * (oldR * q) = q * (oldR * t) := by ac_rfl
  rw [hcancel, hleft, hright]
  omega

private theorem lattice_rep {modulus oldR r : Nat} {a oldT t p q : Int}
    (hmodulus : 0 < modulus)
    (hold : (modulus : Int) ∣ oldT * a - Int.ofNat oldR)
    (hcurrent : (modulus : Int) ∣ t * a - Int.ofNat r)
    (htarget : (modulus : Int) ∣ q * a - p)
    (hdet : Int.ofNat oldR * t - Int.ofNat r * oldT = (modulus : Int) ∨
      Int.ofNat oldR * t - Int.ofNat r * oldT = -(modulus : Int)) :
    ∃ alpha beta : Int,
      p = alpha * Int.ofNat oldR + beta * Int.ofNat r ∧
        q = alpha * oldT + beta * t := by
  have halphaDvd : (modulus : Int) ∣ p * t - Int.ofNat r * q := by
    have hsum := Int.dvd_add
      (Int.dvd_mul_of_dvd_right (b := -t) htarget)
      (Int.dvd_mul_of_dvd_right (b := q) hcurrent)
    rw [show
      -t * (q * a - p) + q * (t * a - Int.ofNat r) =
        p * t - Int.ofNat r * q by
      simp only [Int.mul_sub, Int.neg_mul]
      have h₁ : t * (q * a) = q * (t * a) := by ac_rfl
      have h₂ : t * p = p * t := by ac_rfl
      have h₃ : q * Int.ofNat r = Int.ofNat r * q := by ac_rfl
      rw [h₁, h₂, h₃]
      omega] at hsum
    exact hsum
  have hbetaDvd : (modulus : Int) ∣ Int.ofNat oldR * q - p * oldT := by
    have hdifference := Int.dvd_sub
      (Int.dvd_mul_of_dvd_right (b := oldT) htarget)
      (Int.dvd_mul_of_dvd_right (b := q) hold)
    rw [show
      oldT * (q * a - p) - q * (oldT * a - Int.ofNat oldR) =
        Int.ofNat oldR * q - p * oldT by
      simp only [Int.mul_sub]
      have h₁ : oldT * (q * a) = q * (oldT * a) := by ac_rfl
      have h₂ : oldT * p = p * oldT := by ac_rfl
      have h₃ : q * Int.ofNat oldR = Int.ofNat oldR * q := by ac_rfl
      rw [h₁, h₂, h₃]
      omega] at hdifference
    exact hdifference
  let determinant := Int.ofNat oldR * t - Int.ofNat r * oldT
  have hdetNe : determinant ≠ 0 := hdet.elim
    (fun h => by dsimp only [determinant]; rw [h]; omega)
    (fun h => by dsimp only [determinant]; rw [h]; omega)
  have halphaDet : determinant ∣ p * t - Int.ofNat r * q := hdet.elim
    (fun h => by simpa only [determinant, h] using halphaDvd)
    (fun h => by simpa only [determinant, h, Int.neg_dvd] using halphaDvd)
  have hbetaDet : determinant ∣ Int.ofNat oldR * q - p * oldT := hdet.elim
    (fun h => by simpa only [determinant, h] using hbetaDvd)
    (fun h => by simpa only [determinant, h, Int.neg_dvd] using hbetaDvd)
  rcases halphaDet with ⟨alpha, halpha⟩
  rcases hbetaDet with ⟨beta, hbeta⟩
  refine ⟨alpha, beta, ?_, ?_⟩
  · apply Int.eq_of_mul_eq_mul_left hdetNe
    have hcramer := cramer_fst (Int.ofNat oldR) (Int.ofNat r) p q oldT t
    rw [halpha, hbeta] at hcramer
    calc
      determinant * p = p * determinant := by ac_rfl
      _ = Int.ofNat oldR * (determinant * alpha) +
          Int.ofNat r * (determinant * beta) := by
        simpa only [determinant] using hcramer.symm
      _ = determinant *
          (alpha * Int.ofNat oldR + beta * Int.ofNat r) := by
        rw [Int.mul_add]
        ac_rfl
  · apply Int.eq_of_mul_eq_mul_left hdetNe
    have hcramer := cramer_snd (Int.ofNat oldR) (Int.ofNat r) p q oldT t
    rw [halpha, hbeta] at hcramer
    calc
      determinant * q = q * determinant := by ac_rfl
      _ = oldT * (determinant * alpha) + t * (determinant * beta) := by
        simpa only [determinant] using hcramer.symm
      _ = determinant * (alpha * oldT + beta * t) := by
        rw [Int.mul_add]
        ac_rfl

private theorem no_small_vector {oldR r : Nat} {oldT t p q : Int}
    (hr : r < oldR)
    (hsign : oldT ≤ 0 ∧ 0 < t ∨ t < 0 ∧ 0 ≤ oldT)
    (hp : p.natAbs < oldR) (hq : 0 < q) (hqsmall : q < (t.natAbs : Int))
    (hrep : ∃ alpha beta : Int,
      p = alpha * Int.ofNat oldR + beta * Int.ofNat r ∧
        q = alpha * oldT + beta * t) : False := by
  rcases hrep with ⟨alpha, beta, hpRep, hqRep⟩
  have holdR : (0 : Int) < Int.ofNat oldR :=
    Int.ofNat_lt.mpr (Nat.zero_lt_of_lt hr)
  have hrNonneg : (0 : Int) ≤ Int.ofNat r := Int.natCast_nonneg _
  have hpAbs : (p.natAbs : Int) < Int.ofNat oldR := Int.ofNat_lt.mpr hp
  have hpUpper : p < Int.ofNat oldR := Int.lt_of_le_of_lt Int.le_natAbs hpAbs
  have hpLower : -Int.ofNat oldR < p := by
    have hneg : -p ≤ (p.natAbs : Int) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -p))
    omega
  rcases hsign with hsign | hsign
  · have htAbs : (t.natAbs : Int) = t := by
      rw [Int.ofNat_natAbs_of_nonneg (Int.le_of_lt hsign.2)]
    rw [htAbs] at hqsmall
    by_cases hbeta : beta ≤ 0
    · have hbetaT : beta * t ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg hbeta (Int.le_of_lt hsign.2)
      have halphaNeg : alpha < 0 := by
        apply Int.lt_of_not_ge
        intro halpha
        have halphaT : alpha * oldT ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos halpha hsign.1
        omega
      have halphaR : alpha * Int.ofNat oldR ≤ -Int.ofNat oldR := by
        calc
          alpha * Int.ofNat oldR ≤ (-1 : Int) * Int.ofNat oldR :=
            Int.mul_le_mul_of_nonneg_right (show alpha ≤ -1 by omega)
              (Int.le_of_lt holdR)
          _ = -Int.ofNat oldR := by simp
      have hbetaR : beta * Int.ofNat r ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg hbeta hrNonneg
      omega
    · have hbetaPos : 0 < beta := Int.lt_of_not_ge hbeta
      have hbetaT : t ≤ beta * t := by
        calc
          t = (1 : Int) * t := by simp
          _ ≤ beta * t := Int.mul_le_mul_of_nonneg_right
            (show (1 : Int) ≤ beta by omega) (Int.le_of_lt hsign.2)
      have halphaPos : 0 < alpha := by
        apply Int.lt_of_not_ge
        intro halpha
        have halphaT : 0 ≤ alpha * oldT :=
          Int.mul_nonneg_of_nonpos_of_nonpos halpha hsign.1
        omega
      have halphaR : Int.ofNat oldR ≤ alpha * Int.ofNat oldR := by
        calc
          Int.ofNat oldR = (1 : Int) * Int.ofNat oldR := by simp
          _ ≤ alpha * Int.ofNat oldR := Int.mul_le_mul_of_nonneg_right
            (show (1 : Int) ≤ alpha by omega) (Int.le_of_lt holdR)
      have hbetaR : 0 ≤ beta * Int.ofNat r :=
        Int.mul_nonneg (Int.le_of_lt hbetaPos) hrNonneg
      omega
  · have htAbs : (t.natAbs : Int) = -t := by
      rw [Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hsign.1)]
    rw [htAbs] at hqsmall
    by_cases hbeta : 0 ≤ beta
    · have hbetaT : beta * t ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos hbeta (Int.le_of_lt hsign.1)
      have halphaPos : 0 < alpha := by
        apply Int.lt_of_not_ge
        intro halpha
        have halphaT : alpha * oldT ≤ 0 :=
          Int.mul_nonpos_of_nonpos_of_nonneg halpha hsign.2
        omega
      have halphaR : Int.ofNat oldR ≤ alpha * Int.ofNat oldR := by
        calc
          Int.ofNat oldR = (1 : Int) * Int.ofNat oldR := by simp
          _ ≤ alpha * Int.ofNat oldR := Int.mul_le_mul_of_nonneg_right
            (show (1 : Int) ≤ alpha by omega) (Int.le_of_lt holdR)
      have hbetaR : 0 ≤ beta * Int.ofNat r :=
        Int.mul_nonneg hbeta hrNonneg
      omega
    · have hbetaNeg : beta < 0 := Int.lt_of_not_ge hbeta
      have hbetaT : -t ≤ beta * t := by
        have := Int.mul_le_mul_of_nonpos_right (show beta ≤ -1 by omega)
          (Int.le_of_lt hsign.1)
        simpa only [Int.neg_mul, Int.one_mul] using this
      have halphaNeg : alpha < 0 := by
        apply Int.lt_of_not_ge
        intro halpha
        have halphaT : 0 ≤ alpha * oldT :=
          Int.mul_nonneg halpha hsign.2
        omega
      have halphaR : alpha * Int.ofNat oldR ≤ -Int.ofNat oldR := by
        calc
          alpha * Int.ofNat oldR ≤ (-1 : Int) * Int.ofNat oldR :=
            Int.mul_le_mul_of_nonneg_right (show alpha ≤ -1 by omega)
              (Int.le_of_lt holdR)
          _ = -Int.ofNat oldR := by simp
      have hbetaR : beta * Int.ofNat r ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg (Int.le_of_lt hbetaNeg) hrNonneg
      omega

private theorem euclidUntil.go_spec (modulus : Nat) (a P : Int)
    (oldR r : Nat) (oldT t : Int) :
    0 < modulus → 0 ≤ P → r < oldR → P < Int.ofNat oldR →
    (modulus : Int) ∣ oldT * a - Int.ofNat oldR →
    (modulus : Int) ∣ t * a - Int.ofNat r →
    (Int.ofNat oldR * t - Int.ofNat r * oldT = (modulus : Int) ∨
      Int.ofNat oldR * t - Int.ofNat r * oldT = -(modulus : Int)) →
    (oldT ≤ 0 ∧ 0 < t ∨ t < 0 ∧ 0 ≤ oldT) →
    let row := euclidUntil.go P oldR r oldT t
    0 ≤ row.r ∧ (row.r : Int) ≤ P ∧ row.t ≠ 0 ∧
      (modulus : Int) ∣ row.t * a - row.r ∧
      ∀ p q : Int, p.natAbs ≤ P → 0 < q →
        (modulus : Int) ∣ q * a - p →
        (row.t.natAbs : Int) ≤ q := by
  fun_induction euclidUntil.go P oldR r oldT t with
  | case1 oldR r oldT t hstop =>
      intro hmodulus hP hr hcut hold hcurrent hdet hsign
      dsimp only
      have htNe : t ≠ 0 := by
        rcases hsign with hsign | hsign <;> omega
      refine ⟨Int.natCast_nonneg _, hstop, htNe, hcurrent, ?_⟩
      intro p q hp hq htarget
      apply Int.le_of_not_gt
      intro hqsmall
      have hpLt : p.natAbs < oldR := by
        apply Int.ofNat_lt.mp
        exact Int.lt_of_le_of_lt hp hcut
      exact no_small_vector hr hsign hpLt hq hqsmall
        (lattice_rep hmodulus hold hcurrent htarget hdet)
  | case2 oldR oldT t hstop =>
      intro _hmodulus hP
      omega
  | case3 oldR r oldT t hstop hrNe quotient ih =>
      intro hmodulus hP hr hcut hold hcurrent hdet hsign
      have hrPos : 0 < r := Nat.pos_of_ne_zero hrNe
      have hquotientPos : 0 < quotient := by
        dsimp only [quotient]
        exact Nat.div_pos (Nat.le_of_lt hr) hrPos
      have hdivmodNat := Nat.mod_add_div oldR r
      have hdivmod : Int.ofNat (oldR % r) +
          Int.ofNat r * Int.ofNat quotient = Int.ofNat oldR := by
        dsimp only [quotient]
        exact congrArg Int.ofNat hdivmodNat
      have hnext : (modulus : Int) ∣
          (oldT - Int.ofNat quotient * t) * a - Int.ofNat (oldR % r) := by
        have hdifference := Int.dvd_sub hold
          (Int.dvd_mul_of_dvd_right (b := Int.ofNat quotient) hcurrent)
        rw [show
          (oldT * a - Int.ofNat oldR) -
              Int.ofNat quotient * (t * a - Int.ofNat r) =
            (oldT - Int.ofNat quotient * t) * a - Int.ofNat (oldR % r) by
          simp only [Int.mul_sub, Int.sub_mul]
          have hmul : Int.ofNat quotient * (t * a) =
              (Int.ofNat quotient * t) * a := by ac_rfl
          have hcomm : Int.ofNat quotient * Int.ofNat r =
              Int.ofNat r * Int.ofNat quotient := by ac_rfl
          rw [hmul, hcomm]
          omega] at hdifference
        exact hdifference
      have hdetNext :
          Int.ofNat r * (oldT - Int.ofNat quotient * t) -
                Int.ofNat (oldR % r) * t = (modulus : Int) ∨
            Int.ofNat r * (oldT - Int.ofNat quotient * t) -
                Int.ofNat (oldR % r) * t = -(modulus : Int) := by
        have hnegDet :
            Int.ofNat r * (oldT - Int.ofNat quotient * t) -
                Int.ofNat (oldR % r) * t =
              -(Int.ofNat oldR * t - Int.ofNat r * oldT) := by
          simp only [Int.mul_sub]
          have hmul : Int.ofNat r * (Int.ofNat quotient * t) =
              (Int.ofNat r * Int.ofNat quotient) * t := by ac_rfl
          rw [hmul]
          have hsum :
              Int.ofNat r * Int.ofNat quotient * t +
                  Int.ofNat (oldR % r) * t = Int.ofNat oldR * t := by
            rw [← Int.add_mul]
            rw [Int.add_comm]
            rw [hdivmod]
          omega
        rcases hdet with hdet | hdet
        · exact Or.inr (by rw [hnegDet, hdet])
        · exact Or.inl (by rw [hnegDet, hdet]; simp)
      have hsignNext :
          t ≤ 0 ∧ 0 < oldT - Int.ofNat quotient * t ∨
            oldT - Int.ofNat quotient * t < 0 ∧ 0 ≤ t := by
        have hquotientInt : (0 : Int) < Int.ofNat quotient :=
          Int.ofNat_lt.mpr hquotientPos
        rcases hsign with hsign | hsign
        · have hproduct : 0 < Int.ofNat quotient * t :=
            Int.mul_pos hquotientInt hsign.2
          exact Or.inr ⟨by omega, Int.le_of_lt hsign.2⟩
        · have hproduct : Int.ofNat quotient * t < 0 :=
            Int.mul_neg_of_pos_of_neg hquotientInt hsign.1
          exact Or.inl ⟨Int.le_of_lt hsign.1, by omega⟩
      have hcutNext : P < Int.ofNat r := by
        exact Int.lt_of_not_ge hstop
      exact ih hmodulus hP (Nat.mod_lt oldR hrPos) hcutNext
        hcurrent hnext hdetNext hsignNext

/-- Return the first row of the extended Euclidean remainder sequence on
`(m, a)` whose remainder is at most `P`. The modulus is interpreted up to
sign, and `a` is reduced before entering the recurrence. -/
def euclidUntil (m a P : Int) : Row :=
  let modulus := m.natAbs
  if _hm : modulus = 0 then
    { r := 0, t := 0 }
  else
    let residue := (a % (Int.ofNat modulus)).natAbs
    euclidUntil.go P modulus residue 0 1

/-- The truncated Euclidean row is a nonzero modular-lattice vector whose
second coordinate is no larger than that of any bounded lattice vector. -/
theorem euclidUntil_spec {modulus : Nat} {a P : Int}
    (hmodulus : 0 < modulus) (hP : 0 ≤ P) (hcut : P < (modulus : Int)) :
    let row := euclidUntil (Int.ofNat modulus) a P
    0 ≤ row.r ∧ row.r ≤ P ∧ row.t ≠ 0 ∧
      (modulus : Int) ∣ row.t * a - row.r ∧
      ∀ p q : Int, p.natAbs ≤ P → 0 < q →
        (modulus : Int) ∣ q * a - p →
        (row.t.natAbs : Int) ≤ q := by
  unfold euclidUntil
  simp only [Int.natAbs_ofNat']
  split
  · omega
  · have hresidueNonneg : (0 : Int) ≤ a % Int.ofNat modulus :=
      Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hmodulus))
    have hresidueEq :
        Int.ofNat ((a % Int.ofNat modulus).natAbs) = a % Int.ofNat modulus :=
      Int.ofNat_natAbs_of_nonneg hresidueNonneg
    apply euclidUntil.go_spec modulus a P
    · exact hmodulus
    · exact hP
    · apply Int.ofNat_lt.mp
      change Int.ofNat ((a % Int.ofNat modulus).natAbs) < Int.ofNat modulus
      rw [hresidueEq]
      exact Int.emod_lt_of_pos _ (Int.ofNat_lt.mpr hmodulus)
    · exact hcut
    · simp
    · simp only [Int.one_mul]
      rw [hresidueEq]
      simpa only [Int.ofNat_eq_natCast] using
        (Int.dvd_self_sub_emod (x := a) (m := Int.ofNat modulus))
    · exact Or.inl (by simp)
    · exact Or.inl ⟨by omega, by omega⟩

#guard euclidUntil 1 0 1 == { r := 0, t := 1 }
#guard euclidUntil 101 51 2 == { r := 1, t := 2 }

end Modular

end Hex

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModular.Crt
public import HexModular.Euclid

public section

/-!
Bounded, vector, and maximal-quotient rational reconstruction.
-/
namespace Hex

namespace Modular

/-- Check that `x` represents `a` modulo `m` and satisfies the requested
numerator and denominator bounds. This is split from the Euclidean search so
certificate replay need not unfold that search. -/
@[expose]
def ratReconCheck (a : Int) (m : Nat) (P Q : Int) (x : Rat) : Bool :=
  decide (0 < m) &&
    decide ((Int.ofNat x.den * a - x.num) % (m : Int) = 0) &&
    decide ((x.num.natAbs : Int) ≤ P) &&
    decide ((0 : Int) < x.den) &&
    decide ((x.den : Int) ≤ Q)

/-- Reconstruct `a mod m` as a rational with numerator absolute value at most
`P` and positive denominator at most `Q`. The truncated Euclidean candidate is
normalized and all output conditions are checked before it is returned. -/
def ratRecon? (a : Int) (m : Nat) (P Q : Int) : Option Rat :=
  if m = 0 then
    none
  else
    let row := euclidUntil (Int.ofNat m) a P
    if row.t = 0 then
      none
    else
      let candidate := Rat.divInt row.r row.t
      if ratReconCheck a m P Q candidate then some candidate else none

/-- Symmetric rational reconstruction with
`P = Q = ⌊√((m-1)/2)⌋`, which guarantees `2 P Q < m`. -/
def ratReconWide? (a : Int) (m : Nat) : Option Rat :=
  let bound := Nat.sqrt ((m - 1) / 2)
  ratRecon? a m (Int.ofNat bound) (Int.ofNat bound)

/-- Every rational returned by bounded reconstruction satisfies the requested
modular congruence. -/
theorem ratRecon?_congr {a : Int} {m : Nat} {P Q : Int} {x : Rat}
    (h : ratRecon? a m P Q = some x) :
    (Int.ofNat x.den * a - x.num) % (m : Int) = 0 := by
  unfold ratRecon? at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  next candidate hcheck =>
    cases h
    simp only [ratReconCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨⟨⟨_, hcongr⟩, _⟩, _⟩, _⟩
    exact hcongr

/-- Every rational returned by bounded reconstruction satisfies the requested
numerator and denominator bounds. -/
theorem ratRecon?_bounds {a : Int} {m : Nat} {P Q : Int} {x : Rat}
    (h : ratRecon? a m P Q = some x) :
    (x.num.natAbs : Int) ≤ P ∧ 0 < x.den ∧ (x.den : Int) ≤ Q := by
  unfold ratRecon? at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  next candidate hcheck =>
    cases h
    simp only [ratReconCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨⟨⟨_, _⟩, hnum⟩, hdenpos⟩, hdenBound⟩
    exact ⟨hnum, by simpa using hdenpos, hdenBound⟩

/-- The reduced denominator of a successful reconstruction is coprime to the
modulus. -/
theorem ratRecon?_den_coprime {a : Int} {m : Nat} {P Q : Int} {x : Rat}
    (h : ratRecon? a m P Q = some x) :
    Nat.gcd x.den m = 1 := by
  apply Nat.gcd_eq_one_iff.mpr
  intro divisor hden hmodulus
  have hcongr := ratRecon?_congr h
  have hmodulusDvd : (m : Int) ∣ Int.ofNat x.den * a - x.num :=
    Int.dvd_of_emod_eq_zero hcongr
  have hdivisorDvd : (divisor : Int) ∣ Int.ofNat x.den * a - x.num :=
    Int.dvd_trans (Int.ofNat_dvd.mpr hmodulus) hmodulusDvd
  have hdenDvd : (divisor : Int) ∣ Int.ofNat x.den * a :=
    Int.dvd_mul_of_dvd_left (Int.ofNat_dvd.mpr hden)
  have hnumDvd : (divisor : Int) ∣ x.num := by
    have := Int.dvd_sub hdenDvd hdivisorDvd
    rw [show Int.ofNat x.den * a - (Int.ofNat x.den * a - x.num) =
      x.num by omega] at this
    exact this
  exact Nat.gcd_eq_one_iff.mp x.reduced divisor
    (Int.ofNat_dvd_left.mp hnumDvd) hden

/-- Rational reconstruction is unique whenever twice the product of the two
bounds is strictly smaller than the modulus. -/
theorem ratRecon_unique {a P Q : Int} {m : Nat} {y₁ y₂ : Rat}
    (hm : 2 * P * Q < (m : Int))
    (h₁ : (Int.ofNat y₁.den * a - y₁.num) % (m : Int) = 0)
    (h₂ : (Int.ofNat y₂.den * a - y₂.num) % (m : Int) = 0)
    (b₁ : (y₁.num.natAbs : Int) ≤ P ∧ (y₁.den : Int) ≤ Q)
    (b₂ : (y₂.num.natAbs : Int) ≤ P ∧ (y₂.den : Int) ≤ Q) :
    y₁ = y₂ := by
  have hmodulus : (0 : Int) < (m : Int) := by
    have hden₁ : (0 : Int) < y₁.den := by exact_mod_cast y₁.den_pos
    have hP : 0 ≤ P := Int.le_trans (Int.natCast_nonneg _) b₁.1
    have hQ : 0 < Q := Int.lt_of_lt_of_le hden₁ b₁.2
    have hprod : 0 ≤ 2 * P * Q :=
      Int.mul_nonneg (Int.mul_nonneg (by omega) hP) (Int.le_of_lt hQ)
    omega
  have hm₁ : (m : Int) ∣ Int.ofNat y₁.den * a - y₁.num :=
    Int.dvd_of_emod_eq_zero h₁
  have hm₂ : (m : Int) ∣ Int.ofNat y₂.den * a - y₂.num :=
    Int.dvd_of_emod_eq_zero h₂
  let cross := y₁.num * Int.ofNat y₂.den -
    y₂.num * Int.ofNat y₁.den
  have hcrossDvd : (m : Int) ∣ cross := by
    have hdifference := Int.dvd_sub
      (Int.dvd_mul_of_dvd_right (b := Int.ofNat y₂.den) hm₁)
      (Int.dvd_mul_of_dvd_right (b := Int.ofNat y₁.den) hm₂)
    have hcancel : Int.ofNat y₂.den * (Int.ofNat y₁.den * a) =
        Int.ofNat y₁.den * (Int.ofNat y₂.den * a) := by
      ac_rfl
    rw [show
      Int.ofNat y₂.den * (Int.ofNat y₁.den * a - y₁.num) -
          Int.ofNat y₁.den * (Int.ofNat y₂.den * a - y₂.num) =
        -cross by
      simp only [Int.mul_sub]
      rw [hcancel]
      dsimp only [cross]
      have hmul₁ : Int.ofNat y₂.den * y₁.num =
          y₁.num * Int.ofNat y₂.den := by ac_rfl
      have hmul₂ : Int.ofNat y₁.den * y₂.num =
          y₂.num * Int.ofNat y₁.den := by ac_rfl
      rw [hmul₁, hmul₂]
      omega] at hdifference
    exact Int.dvd_neg.mp hdifference
  have hP : 0 ≤ P := Int.le_trans (Int.natCast_nonneg _) b₁.1
  have hden₁ : (0 : Int) ≤ y₁.den := Int.natCast_nonneg _
  have hden₂ : (0 : Int) ≤ y₂.den := Int.natCast_nonneg _
  have hterm₁ : (y₁.num.natAbs : Int) * Int.ofNat y₂.den ≤ P * Q := by
    exact Int.le_trans
      (Int.mul_le_mul_of_nonneg_right b₁.1 hden₂)
      (Int.mul_le_mul_of_nonneg_left b₂.2 hP)
  have hterm₂ : (y₂.num.natAbs : Int) * Int.ofNat y₁.den ≤ P * Q := by
    exact Int.le_trans
      (Int.mul_le_mul_of_nonneg_right b₂.1 hden₁)
      (Int.mul_le_mul_of_nonneg_left b₁.2 hP)
  have hcrossBound : (cross.natAbs : Int) < (m : Int) := by
    have htriangle := Int.natAbs_sub_le
      (y₁.num * Int.ofNat y₂.den) (y₂.num * Int.ofNat y₁.den)
    have htriangleInt : (cross.natAbs : Int) ≤
        (y₁.num.natAbs : Int) * Int.ofNat y₂.den +
          (y₂.num.natAbs : Int) * Int.ofNat y₁.den := by
      apply Int.ofNat_le.mpr
      simpa only [cross, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_ofNat',
        Int.natCast_add, Int.natCast_mul] using htriangle
    have hm' : 2 * (P * Q) < (m : Int) := by
      simpa only [Int.mul_assoc] using hm
    omega
  have hcrossZero : cross = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hcrossDvd
    simpa only [Int.natAbs_natCast] using Int.ofNat_lt.mp hcrossBound
  apply Rat.eq_iff_mul_eq_mul.mpr
  dsimp only [cross] at hcrossZero
  exact Int.sub_eq_zero.mp hcrossZero

/-- Under the uniqueness bound, bounded reconstruction finds every rational
that satisfies the congruence and bounds. -/
theorem ratRecon?_complete {a P Q : Int} {m : Nat} {y : Rat}
    (hm : 2 * P * Q < (m : Int))
    (hy : (Int.ofNat y.den * a - y.num) % (m : Int) = 0)
    (hb : (y.num.natAbs : Int) ≤ P ∧ (y.den : Int) ≤ Q) :
    ratRecon? a m P Q = some y := by
  have hdenPos : (0 : Int) < y.den := by exact_mod_cast y.den_pos
  have hP : 0 ≤ P := Int.le_trans (Int.natCast_nonneg _) hb.1
  have hQ : 0 < Q := Int.lt_of_lt_of_le hdenPos hb.2
  have htwoP : 0 ≤ 2 * P := Int.mul_nonneg (by omega) hP
  have hprodNonneg : 0 ≤ 2 * P * Q :=
    Int.mul_nonneg htwoP (Int.le_of_lt hQ)
  have hmodulusInt : (0 : Int) < (m : Int) := Int.lt_of_le_of_lt hprodNonneg hm
  have hmodulus : 0 < m := Int.ofNat_lt.mp hmodulusInt
  have hPLeProduct : P ≤ 2 * P * Q := by
    have hPLeTwoP : P ≤ 2 * P := by omega
    have hTwoPLe : 2 * P ≤ 2 * P * Q := by
      calc
        2 * P = (2 * P) * 1 := by simp
        _ ≤ (2 * P) * Q := Int.mul_le_mul_of_nonneg_left (by omega) htwoP
    exact Int.le_trans hPLeTwoP hTwoPLe
  have hcut : P < (m : Int) := by omega
  let row := euclidUntil (Int.ofNat m) a P
  have hspec := euclidUntil_spec (a := a) (P := P) hmodulus hP hcut
  dsimp only at hspec
  have htargetDvd : (m : Int) ∣ Int.ofNat y.den * a - y.num :=
    Int.dvd_of_emod_eq_zero hy
  have htBound : (row.t.natAbs : Int) ≤ Int.ofNat y.den := by
    exact hspec.2.2.2.2 y.num (Int.ofNat y.den) hb.1 hdenPos htargetDvd
  let cross := row.r * Int.ofNat y.den - y.num * row.t
  have hcrossDvd : (m : Int) ∣ cross := by
    have hdifference := Int.dvd_sub
      (Int.dvd_mul_of_dvd_right (b := row.t) htargetDvd)
      (Int.dvd_mul_of_dvd_right (b := Int.ofNat y.den) hspec.2.2.2.1)
    rw [show
      row.t * (Int.ofNat y.den * a - y.num) -
          Int.ofNat y.den * (row.t * a - row.r) = cross by
      simp only [Int.mul_sub]
      have h₁ : row.t * (Int.ofNat y.den * a) =
          Int.ofNat y.den * (row.t * a) := by ac_rfl
      have h₂ : row.t * y.num = y.num * row.t := by ac_rfl
      have h₃ : Int.ofNat y.den * row.r = row.r * Int.ofNat y.den := by ac_rfl
      rw [h₁, h₂, h₃]
      dsimp only [cross]
      omega] at hdifference
    exact hdifference
  have hrowAbs : (row.r.natAbs : Int) ≤ P := by
    rw [Int.ofNat_natAbs_of_nonneg hspec.1]
    exact hspec.2.1
  have hterm₁ : (row.r.natAbs : Int) * Int.ofNat y.den ≤
      P * Int.ofNat y.den :=
    Int.mul_le_mul_of_nonneg_right hrowAbs (Int.natCast_nonneg _)
  have hterm₂ : (y.num.natAbs : Int) * (row.t.natAbs : Int) ≤
      P * Int.ofNat y.den := by
    exact Int.le_trans
      (Int.mul_le_mul_of_nonneg_right hb.1 (Int.natCast_nonneg _))
      (Int.mul_le_mul_of_nonneg_left htBound hP)
  have hdenProduct : 2 * P * Int.ofNat y.den ≤ 2 * P * Q :=
    Int.mul_le_mul_of_nonneg_left hb.2 htwoP
  have hcrossBound : (cross.natAbs : Int) < (m : Int) := by
    have htriangle := Int.natAbs_sub_le
      (row.r * Int.ofNat y.den) (y.num * row.t)
    have htriangleInt : (cross.natAbs : Int) ≤
        (row.r.natAbs : Int) * Int.ofNat y.den +
          (y.num.natAbs : Int) * (row.t.natAbs : Int) := by
      apply Int.ofNat_le.mpr
      simpa only [cross, Int.natAbs_mul, Int.natAbs_ofNat',
        Int.natCast_add, Int.natCast_mul] using htriangle
    have hm' : 2 * (P * Int.ofNat y.den) < (m : Int) := by
      have : 2 * P * Int.ofNat y.den < (m : Int) :=
        Int.lt_of_le_of_lt hdenProduct hm
      simpa only [Int.mul_assoc] using this
    omega
  have hcrossZero : cross = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hcrossDvd
    simpa only [Int.natAbs_natCast] using Int.ofNat_lt.mp hcrossBound
  have hcandidate : Rat.divInt row.r row.t = y := by
    rw [← Rat.num_divInt_den y]
    apply (Rat.divInt_eq_divInt_iff hspec.2.2.1 (by omega)).mpr
    dsimp only [cross] at hcrossZero
    exact Int.sub_eq_zero.mp hcrossZero
  have hcheck : ratReconCheck a m P Q y = true := by
    simp only [ratReconCheck, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨hmodulus, hy⟩, hb.1⟩, hdenPos⟩, hb.2⟩
  unfold ratRecon?
  rw [ite_eq_right (Nat.ne_of_gt hmodulus)]
  change (if row.t = 0 then none else
      let candidate := Rat.divInt row.r row.t
      if ratReconCheck a m P Q candidate then some candidate else none) = some y
  rw [ite_eq_right hspec.2.2.1]
  dsimp only
  rw [hcandidate, ite_eq_left hcheck]

/-- Check a vector reconstruction with common denominator. -/
private def ratReconVecCheck (a y : Vector Int k) (m : Nat) (P Q d : Int) : Bool :=
  decide (0 < m) && decide (0 < d) && decide (d ≤ Q) &&
    (Vector.zipWith
      (fun ai yi =>
        decide ((d * ai - yi) % (m : Int) = 0) &&
          decide ((yi.natAbs : Int) ≤ P))
      a y).toArray.all (fun ok => ok)

private theorem ratReconVecCheck_spec {a y : Vector Int k} {m : Nat} {P Q d : Int}
    (h : ratReconVecCheck a y m P Q d = true) :
    0 < d ∧ d ≤ Q ∧
      ∀ i : Fin k,
        (d * a[i] - y[i]) % (m : Int) = 0 ∧ (y[i].natAbs : Int) ≤ P := by
  simp only [ratReconVecCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hmodulus, hden⟩, hdenBound⟩, hall⟩
  refine ⟨hden, hdenBound, ?_⟩
  intro i
  have hi : i.val < (Vector.zipWith
      (fun ai yi =>
        decide ((d * ai - yi) % (m : Int) = 0) &&
          decide ((yi.natAbs : Int) ≤ P)) a y).toArray.size := by
    simp
  have halli := Array.all_eq_true.mp hall i.val hi
  simp only [Vector.getElem_toArray, Vector.getElem_zipWith,
    Bool.and_eq_true, decide_eq_true_eq] at halli
  exact halli

/-- Process the remaining coordinates of a common-denominator reconstruction.
The index increases until it reaches the statically known vector length. -/
private def ratReconVec.go (a : Vector Int k) (m : Nat) (P Q : Int)
    (i : Nat) (hi : i ≤ k) (nums : Vector Int k) (d : Nat) :
    Option (Vector Int k × Nat) :=
  if hik : i = k then
    some (nums, d)
  else
    have hlt : i < k := by omega
    let residue := a[i]
    let fast := symMod (Int.ofNat d * residue) m
    if (fast.natAbs : Int) ≤ P then
      ratReconVec.go a m P Q (i + 1) (by omega) (nums.set i fast) d
    else do
      let entry ← ratRecon? residue m P Q
      let newD := Nat.lcm d entry.den
      let oldScale := Int.ofNat (newD / d)
      let entryScale := Int.ofNat (newD / entry.den)
      let nums :=
        (nums.map fun value => value * oldScale).set i (entry.num * entryScale)
      ratReconVec.go a m P Q (i + 1) (by omega) nums newD
termination_by k - i
decreasing_by all_goals exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self i)

/-- Reconstruct `k` residues as rationals with a common denominator. The first
entry seeds the denominator. Later entries first try one symmetric
multiplication at that denominator, falling back to their own Euclidean run
only when necessary. Denominators are combined with `lcm`, and the final
numerator vector and denominator are reduced by their common gcd. -/
def ratReconVec? (a : Vector Int k) (m : Nat) (P Q : Int) :
    Option (Vector Int k × Int) :=
  if hk : k = 0 then
    let y := Vector.replicate k (0 : Int)
    if ratReconVecCheck a y m P Q 1 then
      some (y, 1)
    else
      none
  else
    do
      have hkpos : 0 < k := by omega
      let first ← ratRecon? a[0] m P Q
      let nums := (Vector.replicate k (0 : Int)).set 0 first.num
      let (nums, d) ← ratReconVec.go a m P Q 1 (by omega) nums first.den
      let common := nums.foldl (fun g value => Nat.gcd g value.natAbs) d
      let reducedNums := nums.map fun value => value / Int.ofNat common
      let reducedDen := d / common
      let denInt := Int.ofNat reducedDen
      if ratReconVecCheck a reducedNums m P Q denInt then
        some (reducedNums, denInt)
      else
        none

/-- A successful common-denominator vector reconstruction has a positive
bounded denominator, and every coordinate satisfies its congruence and
numerator bound. -/
theorem ratReconVec?_spec {a : Vector Int k} {m : Nat} {P Q d : Int}
    {y : Vector Int k}
    (h : ratReconVec? a m P Q = some (y, d)) :
    0 < d ∧ d ≤ Q ∧
      ∀ i : Fin k,
        (d * a[i] - y[i]) % (m : Int) = 0 ∧ (y[i].natAbs : Int) ≤ P := by
  unfold ratReconVec? at h
  split at h
  · dsimp only at h
    split at h <;> try contradiction
    next hcheck =>
      cases h
      exact ratReconVecCheck_spec hcheck
  · cases hfirst : ratRecon? a[0] m P Q with
    | none => simp [hfirst] at h
    | some first =>
      cases hgo : ratReconVec.go a m P Q 1 (by omega)
          ((Vector.replicate k (0 : Int)).set 0 first.num) first.den with
      | none => simp [hfirst, hgo] at h
      | some result =>
        rcases result with ⟨nums, den⟩
        simp only [Option.bind_eq_bind, hfirst, Option.bind_some, hgo] at h
        split at h <;> try contradiction
        next hcheck =>
          cases h
          exact ratReconVecCheck_spec hcheck

/-- Track the row immediately preceding the largest quotient in an extended
Euclidean run. -/
private def maxQuotRow.go (oldR r : Nat) (oldT t : Int)
    (bestQuot : Nat) (best : Option Row) : Option Row :=
  if _hr : r = 0 then
    best
  else
    let quotient := oldR / r
    let (bestQuot, best) :=
      if bestQuot < quotient then
        (quotient, some { r := Int.ofNat r, t })
      else
        (bestQuot, best)
    maxQuotRow.go r (oldR % r) t (oldT - Int.ofNat quotient * t)
      bestQuot best
termination_by r
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _hr)

/-- Produce the maximal-quotient rational-reconstruction candidate. This is a
heuristic: only the modular congruence is checked and promised. -/
def ratReconMaxQuot? (a : Int) (m : Nat) : Option Rat :=
  if _hm : m = 0 then
    none
  else
    let residue := (a % (m : Int)).natAbs
    if residue = 0 then
      some 0
    else
      match maxQuotRow.go m residue 0 1 0 none with
      | none => none
      | some row =>
          if row.t = 0 then
            none
          else
            let candidate := Rat.divInt row.r row.t
            if (Int.ofNat candidate.den * a - candidate.num) % (m : Int) = 0 then
              some candidate
            else
              none

/-- A maximal-quotient candidate always satisfies the modular congruence; no
claim is made that it is the intended rational. -/
theorem ratReconMaxQuot?_congr {a : Int} {m : Nat} {x : Rat}
    (h : ratReconMaxQuot? a m = some x) :
    (Int.ofNat x.den * a - x.num) % (m : Int) = 0 := by
  unfold ratReconMaxQuot? at h
  split at h <;> try contradiction
  dsimp only at h
  split at h
  · cases h
    have hr : a % (m : Int) = 0 := Int.natAbs_eq_zero.mp (by assumption)
    simp [hr]
  · split at h <;> try contradiction
    split at h <;> try contradiction
    try dsimp only at h
    split at h <;> try contradiction
    next candidate hcheck =>
      cases h
      exact hcheck

end Modular

end Hex

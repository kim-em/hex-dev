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

/-- Every common divisor of a denominator `d` and the modulus divides every
numerator of a congruent pair, so a pair reduced as a whole has a denominator
whose divisors are all coprime to the modulus. -/
private theorem gcd_eq_one_of_reduced {a y : Vector Int k} {m : Nat} {d t : Int}
    (hy : ∀ i : Fin k, (d * a[i] - y[i]) % (m : Int) = 0)
    (hred : ∀ g : Int, (∀ i : Fin k, g ∣ y[i]) → g ∣ d → g ∣ 1)
    (ht : t ∣ d) : Int.gcd t m = 1 := by
  apply Int.gcd_eq_one_iff.mpr
  intro c hct hcm
  have hcd : c ∣ d := Int.dvd_trans hct ht
  apply hred c _ hcd
  intro i
  have hdiff : c ∣ d * a[i] - y[i] :=
    Int.dvd_trans hcm (Int.dvd_of_emod_eq_zero (hy i))
  have hprod : c ∣ d * a[i] := Int.dvd_mul_of_dvd_left hcd
  have := Int.dvd_sub hprod hdiff
  rw [show d * a[i] - (d * a[i] - y[i]) = y[i] by omega] at this
  exact this

/-- Cancel a factor coprime to the modulus from a divisibility. -/
private theorem dvd_of_dvd_mul_of_gcd_one {m t x : Int} (h : m ∣ t * x)
    (hcop : Int.gcd t m = 1) : m ∣ x := by
  apply Int.natAbs_dvd_natAbs.mp
  have h' : m.natAbs ∣ t.natAbs * x.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h
    rwa [Int.natAbs_mul] at this
  have hcop' : Nat.Coprime m.natAbs t.natAbs := by
    rw [Int.gcd_eq_natAbs_gcd_natAbs] at hcop
    exact Nat.Coprime.symm hcop
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop' h'

/-- The reduced form of `n / d` for `0 < d`: both `n` and `d` are the reduced
numerator and denominator times one positive integer. -/
private theorem divInt_scale {n d : Int} (hd : 0 < d) :
    ∃ t : Int, 0 < t ∧ d = (Rat.divInt n d).den * t ∧ n = (Rat.divInt n d).num * t := by
  generalize hq : Rat.divInt n d = q
  have hdenPos : (0 : Int) < q.den := by exact_mod_cast q.den_pos
  have hcross : n * q.den = q.num * d := by
    have h := Rat.num_divInt_den q
    exact (Rat.divInt_eq_divInt_iff (Int.ne_of_gt hd) (Int.ne_of_gt hdenPos)).mp
      (hq.trans h.symm)
  have hdenDvd : q.den ∣ d.natAbs := by
    have h1 : (q.den : Int) ∣ q.num * d := ⟨n, by rw [← hcross]; ac_rfl⟩
    have h2 : q.den ∣ q.num.natAbs * d.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h1
      rwa [Int.natAbs_mul, Int.natAbs_natCast] at this
    exact Nat.Coprime.dvd_of_dvd_mul_left q.reduced.symm h2
  obtain ⟨s, hs⟩ := hdenDvd
  refine ⟨s, ?_, ?_, ?_⟩
  · have : 0 < d.natAbs := Int.natAbs_pos.mpr (Int.ne_of_gt hd)
    rw [hs] at this
    exact_mod_cast Nat.pos_of_mul_pos_left this
  · have : d = (d.natAbs : Int) := (Int.natAbs_of_nonneg (Int.le_of_lt hd)).symm
    rw [this, hs]
    push_cast
    rfl
  · have hd' : d = (q.den : Int) * s := by
      have : d = (d.natAbs : Int) := (Int.natAbs_of_nonneg (Int.le_of_lt hd)).symm
      rw [this, hs]
      push_cast
      rfl
    rw [hd'] at hcross
    have : n * q.den = (q.num * s) * q.den := by rw [hcross]; ac_rfl
    exact Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hdenPos) this

/-- A coordinate of a reduced, congruent, bounded pair, as a reduced rational,
satisfies the scalar congruence and bounds. -/
private theorem target_rat {a y : Vector Int k} {m : Nat} {P Q d : Int}
    (hd : 0 < d) (hdQ : d ≤ Q)
    (hy : ∀ i : Fin k, (d * a[i] - y[i]) % (m : Int) = 0 ∧ (y[i].natAbs : Int) ≤ P)
    (hred : ∀ g : Int, (∀ i : Fin k, g ∣ y[i]) → g ∣ d → g ∣ 1) (i : Fin k) :
    (Int.ofNat (Rat.divInt y[i] d).den * a[i] - (Rat.divInt y[i] d).num) % (m : Int) = 0 ∧
      ((Rat.divInt y[i] d).num.natAbs : Int) ≤ P ∧ ((Rat.divInt y[i] d).den : Int) ≤ Q := by
  obtain ⟨t, ht, hdt, hnt⟩ := divInt_scale (n := y[i]) hd
  have hcong := (hy i).1
  have hbound := (hy i).2
  generalize hq : Rat.divInt y[i] d = q at hdt hnt ⊢
  have hcop : Int.gcd t m = 1 :=
    gcd_eq_one_of_reduced (fun j => (hy j).1) hred ⟨q.den, by rw [hdt]; ac_rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · apply Int.emod_eq_zero_of_dvd
    apply dvd_of_dvd_mul_of_gcd_one _ hcop
    have h1 : (m : Int) ∣ d * a[i] - y[i] := Int.dvd_of_emod_eq_zero hcong
    rw [hdt, hnt] at h1
    rw [show t * (Int.ofNat q.den * a[i] - q.num) = (q.den : Int) * t * a[i] - q.num * t by
      rw [Int.mul_sub]; ac_rfl]
    exact h1
  · have h1 : y[i].natAbs = q.num.natAbs * t.natAbs := by rw [hnt, Int.natAbs_mul]
    have h2 : 0 < t.natAbs := Int.natAbs_pos.mpr (Int.ne_of_gt ht)
    have h3 : q.num.natAbs ≤ y[i].natAbs := by
      rw [h1]; exact Nat.le_mul_of_pos_right _ h2
    exact Int.le_trans (Int.ofNat_le.mpr h3) hbound
  · have h1 : (q.den : Int) ≤ d := by
      rw [hdt]
      have : (q.den : Int) * 1 ≤ (q.den : Int) * t :=
        Int.mul_le_mul_of_nonneg_left ht (Int.natCast_nonneg _)
      simpa using this
    exact Int.le_trans h1 hdQ

/-- A coordinate of a reduced, congruent, bounded pair is found by the scalar
reconstruction. -/
private theorem ratRecon?_coord {a y : Vector Int k} {m : Nat} {P Q d : Int}
    (hm : 2 * P * Q < (m : Int)) (hd : 0 < d) (hdQ : d ≤ Q)
    (hy : ∀ i : Fin k, (d * a[i] - y[i]) % (m : Int) = 0 ∧ (y[i].natAbs : Int) ≤ P)
    (hred : ∀ g : Int, (∀ i : Fin k, g ∣ y[i]) → g ∣ d → g ∣ 1) (i : Fin k) :
    ratRecon? a[i] m P Q = some (Rat.divInt y[i] d) := by
  obtain ⟨hcong, hnum, hden⟩ := target_rat hd hdQ hy hred i
  exact ratRecon?_complete hm hcong ⟨hnum, hden⟩

/-- The fast branch of the loop, when it accepts, agrees with the target. -/
private theorem fast_eq {a y : Vector Int k} {m : Nat} {P Q d : Int} {dcur : Nat}
    (hm : 2 * P * Q < (m : Int)) (hd : 0 < d) (hdQ : d ≤ Q)
    (hy : ∀ i : Fin k, (d * a[i] - y[i]) % (m : Int) = 0 ∧ (y[i].natAbs : Int) ≤ P)
    (hred : ∀ g : Int, (∀ i : Fin k, g ∣ y[i]) → g ∣ d → g ∣ 1)
    (hcur : 0 < dcur) (hdvd : (dcur : Int) ∣ d) (i : Fin k)
    (hfast : ((symMod ((dcur : Int) * a[i]) m).natAbs : Int) ≤ P) :
    symMod ((dcur : Int) * a[i]) m * d = y[i] * (dcur : Int) := by
  have hP : 0 ≤ P := Int.le_trans (Int.natCast_nonneg _) hfast
  have hQ : 0 < Q := Int.lt_of_lt_of_le hd hdQ
  have hprod : 0 ≤ 2 * P * Q :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) hP) (Int.le_of_lt hQ)
  have hm0 : 0 < m := Int.ofNat_lt.mp (Int.lt_of_le_of_lt hprod hm)
  have hfcong := symMod_emod (a := (dcur : Int) * a[i]) hm0
  generalize hf : symMod ((dcur : Int) * a[i]) m = f at hfast hfcong ⊢
  have hdcurPos : (0 : Int) < (dcur : Int) := by omega
  obtain ⟨t₁, ht₁, hdt₁, hft₁⟩ := divInt_scale (n := f) hdcurPos
  have hcross : Rat.divInt f (dcur : Int) = Rat.divInt y[i] d := by
    apply ratRecon_unique (a := a[i]) hm
    · generalize hq₁ : Rat.divInt f (dcur : Int) = q₁ at hdt₁ hft₁ ⊢
      have ht₁dvd : t₁ ∣ d := Int.dvd_trans ⟨q₁.den, by rw [hdt₁]; ac_rfl⟩ hdvd
      have hcop₁ := gcd_eq_one_of_reduced (fun j => (hy j).1) hred ht₁dvd
      apply Int.emod_eq_zero_of_dvd
      apply dvd_of_dvd_mul_of_gcd_one _ hcop₁
      have h1 : (m : Int) ∣ (dcur : Int) * a[i] - f := by
        apply Int.dvd_of_emod_eq_zero
        rw [Int.sub_emod, hfcong, Int.sub_self, Int.zero_emod]
      rw [hdt₁, hft₁] at h1
      rw [show t₁ * (Int.ofNat q₁.den * a[i] - q₁.num) =
          (q₁.den : Int) * t₁ * a[i] - q₁.num * t₁ by rw [Int.mul_sub]; ac_rfl]
      exact h1
    · exact (target_rat hd hdQ hy hred i).1
    · generalize hq₁ : Rat.divInt f (dcur : Int) = q₁ at hdt₁ hft₁ ⊢
      refine ⟨?_, ?_⟩
      · have h1 : f.natAbs = q₁.num.natAbs * t₁.natAbs := by rw [hft₁, Int.natAbs_mul]
        have h2 : 0 < t₁.natAbs := Int.natAbs_pos.mpr (Int.ne_of_gt ht₁)
        have h3 : q₁.num.natAbs ≤ f.natAbs := by
          rw [h1]; exact Nat.le_mul_of_pos_right _ h2
        exact Int.le_trans (Int.ofNat_le.mpr h3) hfast
      · have h1 : (q₁.den : Int) ≤ (dcur : Int) := by
          rw [hdt₁]
          have : (q₁.den : Int) * 1 ≤ (q₁.den : Int) * t₁ :=
            Int.mul_le_mul_of_nonneg_left ht₁ (Int.natCast_nonneg _)
          simpa using this
        exact Int.le_trans h1 (Int.le_trans (Int.le_of_dvd hd hdvd) hdQ)
    · exact ⟨(target_rat hd hdQ hy hred i).2.1, (target_rat hd hdQ hy hred i).2.2⟩
  exact (Rat.divInt_eq_divInt_iff (Int.ne_of_gt hdcurPos) (Int.ne_of_gt hd)).mp hcross

/-- The loop keeps a denominator dividing the target's and numerators
proportional to the target's, and never fails on a reduced, congruent,
bounded target. -/
private theorem ratReconVec.go_complete {a y : Vector Int k} {m : Nat} {P Q d : Int}
    (hm : 2 * P * Q < (m : Int)) (hd : 0 < d) (hdQ : d ≤ Q)
    (hy : ∀ i : Fin k, (d * a[i] - y[i]) % (m : Int) = 0 ∧ (y[i].natAbs : Int) ≤ P)
    (hred : ∀ g : Int, (∀ i : Fin k, g ∣ y[i]) → g ∣ d → g ∣ 1) :
    ∀ (i : Nat) (hi : i ≤ k) (nums : Vector Int k) (dcur : Nat),
      0 < dcur → (dcur : Int) ∣ d →
      (∀ j : Fin k, j.val < i → nums[j] * d = y[j] * (dcur : Int)) →
      ∃ nums' : Vector Int k, ∃ dcur' : Nat,
        ratReconVec.go a m P Q i hi nums dcur = some (nums', dcur') ∧
        0 < dcur' ∧ (dcur' : Int) ∣ d ∧
        ∀ j : Fin k, nums'[j] * d = y[j] * (dcur' : Int) := by
  suffices key : ∀ n : Nat, ∀ (i : Nat) (hi : i ≤ k) (nums : Vector Int k) (dcur : Nat),
      k - i = n → 0 < dcur → (dcur : Int) ∣ d →
      (∀ j : Fin k, j.val < i → nums[j] * d = y[j] * (dcur : Int)) →
      ∃ nums' : Vector Int k, ∃ dcur' : Nat,
        ratReconVec.go a m P Q i hi nums dcur = some (nums', dcur') ∧
        0 < dcur' ∧ (dcur' : Int) ∣ d ∧
        ∀ j : Fin k, nums'[j] * d = y[j] * (dcur' : Int) from
    fun i hi nums dcur => key (k - i) i hi nums dcur rfl
  intro n
  induction n with
  | zero =>
    intro i hi nums dcur hn hcur hdvd hinv
    have hik : i = k := by omega
    refine ⟨nums, dcur, ?_, hcur, hdvd, ?_⟩
    · unfold ratReconVec.go
      rw [dite_eq_left hik]
    · intro j
      exact hinv j (hik ▸ j.isLt)
  | succ n ih =>
    intro i hi nums dcur hn hcur hdvd hinv
    have hik : i ≠ k := by omega
    have hlt : i < k := by omega
    unfold ratReconVec.go
    rw [dite_eq_right hik]
    dsimp only
    simp only [Int.ofNat_eq_natCast]
    by_cases hfast : ((symMod ((dcur : Int) * a[i]) m).natAbs : Int) ≤ P
    · rw [ite_eq_left hfast]
      apply ih (i + 1) (by omega) _ dcur (by omega) hcur hdvd
      intro j hj
      rw [Fin.getElem_fin, Vector.getElem_set]
      split
      · next hji =>
        have := fast_eq hm hd hdQ hy hred hcur hdvd ⟨i, hlt⟩ hfast
        simpa [← hji] using this
      · next hji =>
        exact hinv j (by omega)
    · rw [ite_eq_right hfast]
      have hcoord := ratRecon?_coord hm hd hdQ hy hred ⟨i, hlt⟩
      simp only [Fin.getElem_fin] at hcoord
      rw [hcoord]
      simp only [Option.bind_eq_bind, Option.bind_some]
      obtain ⟨t, ht, hdt, hnt⟩ := divInt_scale (n := y[i]) hd
      generalize hq : Rat.divInt y[i] d = q at hdt hnt ⊢
      have hdenPos : 0 < q.den := q.den_pos
      obtain ⟨s, hs⟩ := Nat.dvd_lcm_left dcur q.den
      obtain ⟨s', hs'⟩ := Nat.dvd_lcm_right dcur q.den
      have hlcmPos : 0 < Nat.lcm dcur q.den := Nat.lcm_pos hcur hdenPos
      have hlcmDvd : ((Nat.lcm dcur q.den : Nat) : Int) ∣ d := by
        have h1 : dcur ∣ d.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
        have h2 : q.den ∣ d.natAbs := Int.natAbs_dvd_natAbs.mpr ⟨t, hdt⟩
        have h3 := Nat.lcm_dvd h1 h2
        have h4 : ((Nat.lcm dcur q.den : Nat) : Int) ∣ (d.natAbs : Int) := Int.ofNat_dvd.mpr h3
        rwa [Int.natAbs_of_nonneg (Int.le_of_lt hd)] at h4
      apply ih (i + 1) (by omega) _ (Nat.lcm dcur q.den) (by omega) hlcmPos hlcmDvd
      intro j hj
      simp only [Fin.getElem_fin]
      rw [Vector.getElem_set]
      split
      · next hji =>
        subst hji
        rw [hs', Nat.mul_div_cancel_left _ hdenPos, hnt, hdt]
        push_cast
        ac_rfl
      · next hji =>
        rw [Vector.getElem_map, hs, Nat.mul_div_cancel_left _ hcur]
        have := hinv j (by omega)
        simp only [Fin.getElem_fin] at this
        push_cast
        calc nums[j.val] * (s : Int) * d = nums[j.val] * d * s := by ac_rfl
          _ = y[j.val] * (dcur : Int) * s := by rw [this]
          _ = y[j.val] * ((dcur : Int) * s) := by ac_rfl

/-- The gcd fold divides its seed and every entry. -/
private theorem foldl_gcd_dvd (nums : Vector Int k) (d : Nat) :
    (nums.foldl (fun g value => Nat.gcd g value.natAbs) d) ∣ d ∧
      ∀ j : Fin k, (nums.foldl (fun g value => Nat.gcd g value.natAbs) d) ∣ nums[j].natAbs := by
  have key : ∀ (l : List Int) (init : Nat),
      (l.foldl (fun g value => Nat.gcd g value.natAbs) init) ∣ init ∧
        ∀ v ∈ l, (l.foldl (fun g value => Nat.gcd g value.natAbs) init) ∣ v.natAbs := by
    intro l
    induction l with
    | nil => intro init; exact ⟨Nat.dvd_refl _, fun v hv => nomatch hv⟩
    | cons x xs ih =>
      intro init
      simp only [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih (Nat.gcd init x.natAbs)
      refine ⟨Nat.dvd_trans h1 (Nat.gcd_dvd_left _ _), ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact Nat.dvd_trans h1 (Nat.gcd_dvd_right _ _)
      · exact h2 v hv'
  rw [← Vector.foldl_toList]
  obtain ⟨h1, h2⟩ := key nums.toList d
  exact ⟨h1, fun j => h2 _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem j.isLt))⟩

/-- The converse of `ratReconVecCheck_spec`. -/
private theorem ratReconVecCheck_of {a y : Vector Int k} {m : Nat} {P Q d : Int}
    (hm : 0 < m) (hd : 0 < d) (hdQ : d ≤ Q)
    (hy : ∀ i : Fin k, (d * a[i] - y[i]) % (m : Int) = 0 ∧ (y[i].natAbs : Int) ≤ P) :
    ratReconVecCheck a y m P Q d = true := by
  simp only [ratReconVecCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hm, hd⟩, hdQ⟩, ?_⟩
  apply Array.all_eq_true.mpr
  intro i hi
  simp only [Vector.getElem_toArray, Vector.getElem_zipWith,
    Bool.and_eq_true, decide_eq_true_eq]
  have hik : i < k := by simpa using hi
  exact hy ⟨i, hik⟩

/-- Under the uniqueness bound, common-denominator reconstruction finds every
pair that is reduced as a whole, positive and bounded in its denominator,
and congruent and bounded in every coordinate. Reducedness is not
decoration: at `m = 18`, `a = (10)`, the pair `(2, 2)` satisfies every other
hypothesis, but its reduced rational `1` does not satisfy the congruence and
the reconstruction returns `none`. -/
theorem ratReconVec?_complete {a y : Vector Int k} {m : Nat} {P Q d : Int}
    (hm : 2 * P * Q < (m : Int)) (hP : 0 ≤ P) (hd : 0 < d) (hdQ : d ≤ Q)
    (hy : ∀ i : Fin k, (d * a[i] - y[i]) % (m : Int) = 0 ∧ (y[i].natAbs : Int) ≤ P)
    (hred : ∀ g : Int, (∀ i : Fin k, g ∣ y[i]) → g ∣ d → g ∣ 1) :
    ratReconVec? a m P Q = some (y, d) := by
  have hQ : 0 < Q := Int.lt_of_lt_of_le hd hdQ
  have hprod : 0 ≤ 2 * P * Q :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) hP) (Int.le_of_lt hQ)
  have hm0 : 0 < m := Int.ofNat_lt.mp (Int.lt_of_le_of_lt hprod hm)
  unfold ratReconVec?
  split
  · next hk =>
    subst hk
    dsimp only
    have hd1 : d = 1 :=
      Int.eq_one_of_dvd_one (Int.le_of_lt hd) (hred d (fun i => i.elim0) (Int.dvd_refl d))
    subst hd1
    have hy0 : y = Vector.replicate 0 0 := Vector.ext (fun i hi => absurd hi (Nat.not_lt_zero _))
    rw [ite_eq_left (ratReconVecCheck_of hm0 hd hdQ (fun i => i.elim0)), hy0]
  · next hk =>
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hcoord := ratRecon?_coord hm hd hdQ hy hred ⟨0, hkpos⟩
    simp only [Fin.getElem_fin] at hcoord
    obtain ⟨t, ht, hdt, hnt⟩ := divInt_scale (n := y[0]) hd
    generalize hq : Rat.divInt y[0] d = q at hdt hnt hcoord
    have hinv : ∀ j : Fin k, j.val < 1 →
        ((Vector.replicate k (0 : Int)).set 0 q.num)[j] * d = y[j] * (q.den : Int) := by
      intro j hj
      have hj0 : j = ⟨0, hkpos⟩ := Fin.ext (Nat.lt_one_iff.mp hj)
      subst hj0
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
      rw [hnt, hdt]
      ac_rfl
    obtain ⟨nums', dcur', hgo, hpos', hdvd', hinv'⟩ :=
      ratReconVec.go_complete hm hd hdQ hy hred 1 hkpos _ q.den q.den_pos ⟨t, hdt⟩ hinv
    obtain ⟨s, hs⟩ := hdvd'
    have hdcurPos : (0 : Int) < dcur' := by omega
    have hys : ∀ j : Fin k, y[j] = nums'[j] * s := by
      intro j
      have h1 := hinv' j
      rw [hs] at h1
      have h2 : y[j] * (dcur' : Int) = (nums'[j] * s) * (dcur' : Int) := by
        rw [← h1]; ac_rfl
      exact Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hdcurPos) h2
    have hs1 : s = 1 := by
      have hsdvd : s ∣ 1 :=
        hred s (fun j => ⟨nums'[j], by rw [hys j]; ac_rfl⟩) ⟨dcur', by rw [hs]; ac_rfl⟩
      have habs : s.natAbs = 1 := Nat.eq_one_of_dvd_one (Int.natAbs_dvd_natAbs.mpr hsdvd)
      rcases Int.natAbs_eq s with h | h <;> rw [habs] at h
      · exact h
      · rw [h] at hs
        omega
    subst hs1
    have hnums : nums' = y := Vector.ext (fun j hj => by
      have := hys ⟨j, hj⟩
      rw [Fin.getElem_fin] at this
      simpa using this.symm)
    subst hnums
    have hd' : d = (dcur' : Int) := by rw [hs]; simp
    subst hd'
    have hcommon : nums'.foldl (fun g value => Nat.gcd g value.natAbs) dcur' = 1 := by
      obtain ⟨h1, h2⟩ := foldl_gcd_dvd nums' dcur'
      apply Nat.eq_one_of_dvd_one
      apply Int.ofNat_dvd.mp
      apply hred
      · intro j
        exact Int.natAbs_dvd_natAbs.mp (by simpa using h2 j)
      · exact Int.ofNat_dvd.mpr h1
    simp only [Option.bind_eq_bind, hcoord, Option.bind_some, hgo, hcommon, Nat.div_one,
      Int.ofNat_eq_natCast, Int.ofNat_one, Int.ediv_one, Vector.map_id']
    rw [ite_eq_left (ratReconVecCheck_of hm0 hd hdQ hy)]

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

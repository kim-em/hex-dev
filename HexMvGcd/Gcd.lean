/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexMvGcd.Gauss
public import HexMvGcd.Brown
public import HexMvGcd.ZPoly

@[expose] public section
set_option backward.proofsInPublic true

/-!
Public multivariate gcd, content, and primitive-part API.

This milestone exposes the deterministic checked PRS route. Later fast
producers may propose certificates, but every public result remains gated by
the same checker and falls back here.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}

private theorem restore_checks [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R]
    {f h : MvPoly n R cmp} {reduced : StructuralReduction n R cmp}
    {cert restored : GcdCert n R cmp}
    (hr : restoreStructural? f h reduced cert = some restored) :
    checkGcd f h restored = true := by
  unfold restoreStructural? at hr
  dsimp only at hr
  split at hr
  · next hc =>
      cases hr
      exact hc
  · contradiction

private theorem gcdCertWith_checksCore [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (cfg : GcdConfig) (f h : MvPoly n R cmp) :
    checkGcd f h (gcdCertWith cfg f h).cert = true := by
  unfold gcdCertWith
  split
  · split
    · assumption
    · exact prsCert_checks f h
  · split
    · exact prsCert_checks f h
    · dsimp only
      split
      · split
        · split
          · apply restore_checks
            assumption
          · split
            · apply restore_checks
              assumption
            · exact prsCert_checks f h
        · split
          · apply restore_checks
            assumption
          · exact prsCert_checks f h
      · split
        · apply restore_checks
          assumption
        · exact prsCert_checks f h

/-- Canonical checked gcd certificate. -/
def gcdCert [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : GcdCert n R cmp :=
  (gcdCertWith GcdConfig.default f h).cert

/-- Every public certificate has passed executable replay. -/
theorem gcdCert_checks [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : checkGcd f h (gcdCert f h) = true := by
  exact gcdCertWith_checksCore GcdConfig.default f h

theorem gcdCertWith_checks [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (cfg : GcdConfig) (f h : MvPoly n R cmp) :
    checkGcd f h (gcdCertWith cfg f h).cert = true := by
  exact gcdCertWith_checksCore cfg f h

/-- Certified coefficient content in a named main variable. -/
def contentInCert {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p : MvPoly (n + 1) R cmp) :
    ContentCert n R cmp' :=
  let coeffs := (toUnivariate i cmp' p).toArray.toList
  contentCertWith (fun f h => gcdCert f h) coeffs

/-- Content in a named main variable. -/
def contentIn {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p : MvPoly (n + 1) R cmp) :
    MvPoly n R cmp' :=
  (contentInCert i cmp' p).value

/-- Primitive part in a named main variable. -/
def primPartIn {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p : MvPoly (n + 1) R cmp) :
    MvPoly (n + 1) R cmp :=
  quotient p (constIn i cmp' (contentIn i cmp' p))

theorem contentInCert_checks
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p : MvPoly (n + 1) R cmp) :
    checkContent (toUnivariate i cmp' p).toArray.toList
      (contentInCert i cmp' p) = true := by
  unfold contentInCert
  apply contentCertWith_checks
  intro f h
  exact gcdCert_checks f h

theorem contentIn_dvd_coeff
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p : MvPoly (n + 1) R cmp) (k : Nat) :
    contentIn i cmp' p ∣ (toUnivariate i cmp' p).coeff k := by
  let view := toUnivariate i cmp' p
  let cert := contentInCert i cmp' p
  have hs := checkContent_sound (contentInCert_checks i cmp' p)
  change cert.value ∣ view.coeff k
  by_cases hk : k < view.toList.length
  · have hmem : view.toList[k] ∈ view.toList := List.getElem_mem _
    have hd := hs.1 view.toList[k] hmem
    have hcoeff : view.toList[k] = view.coeff k := by
      have hget := DensePoly.toList_getD_eq_coeff view k
      exact (List.getElem_eq_getD (h := hk) 0).trans hget
    exact hcoeff ▸ hd
  · have hsize : view.size ≤ k := by
      rw [DensePoly.length_toList] at hk
      omega
    rw [DensePoly.coeff_eq_zero_of_size_le view hsize]
    refine ⟨0, ?_⟩
    exact (MvPoly.zero_mul cert.value).symm

/-- Universal property of named-variable content. -/
theorem dvd_contentIn
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p : MvPoly (n + 1) R cmp)
    (d : MvPoly n R cmp')
    (hd : ∀ k, d ∣ (toUnivariate i cmp' p).coeff k) :
    d ∣ contentIn i cmp' p := by
  let view := toUnivariate i cmp' p
  let cert := contentInCert i cmp' p
  have hs := checkContent_sound (contentInCert_checks i cmp' p)
  change d ∣ cert.value
  apply hs.2 d
  intro q hq
  change q ∈ view.toList at hq
  rw [DensePoly.toList_eq_coeff_range] at hq
  rcases List.mem_map.mp hq with ⟨k, _, rfl⟩
  exact hd k

@[simp] theorem contentIn_zero
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] :
    contentIn (R := R) (cmp := cmp) i cmp' 0 = 0 := by
  have hd : ∀ k, (0 : MvPoly n R cmp') ∣
      (toUnivariate i cmp' (0 : MvPoly (n + 1) R cmp)).coeff k := by
    intro k
    have hcoeff :
        (toUnivariate i cmp' (0 : MvPoly (n + 1) R cmp)).coeff k = 0 := by
      apply ext
      intro m
      rw [toUnivariate_coeff, coeff_zero, coeff_zero]
    refine ⟨0, ?_⟩
    exact hcoeff.trans (MvPoly.zero_mul 0).symm
  rcases dvd_contentIn i cmp' 0 0 hd with ⟨q, hq⟩
  exact hq.trans (MvPoly.mul_zero q)

/-- Named-variable content is the normalized final gcd of its recursive
coefficient fold. -/
theorem contentIn_normalized
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p : MvPoly (n + 1) R cmp) :
    polyNormalize (contentIn i cmp' p) = contentIn i cmp' p := by
  unfold contentIn contentInCert
  apply contentCertWith_normalized
  intro f h
  exact gcdCert_checks f h

/-- Named-variable content times primitive part reconstructs the input. -/
theorem contentIn_mul_primPartIn
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p : MvPoly (n + 1) R cmp) :
    constIn i cmp' (contentIn i cmp' p) * primPartIn i cmp' p = p := by
  have hd : constIn i cmp' (contentIn i cmp' p) ∣ p :=
    constIn_dvd i (contentIn i cmp' p) p (contentIn_dvd_coeff i cmp' p)
  by_cases hp : p = 0
  · subst p
    rw [contentIn_zero, constIn_zero, MvPoly.zero_mul]
  · have hc :
        constIn (cmp := cmp) i cmp' (contentIn i cmp' p) ≠
          (0 : MvPoly (n + 1) R cmp) := by
      intro hc
      rcases hd with ⟨q, hq⟩
      rw [hc, MvPoly.mul_zero] at hq
      exact hp hq
    rw [MvPoly.mul_comm]
    exact quotient_mul_of_dvd hc hd

@[simp] theorem primPartIn_zero
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] :
    primPartIn (R := R) (cmp := cmp) i cmp' 0 = 0 := by
  unfold primPartIn quotient
  rw [contentIn_zero, constIn_zero]
  simp [divExact?]

theorem primPartIn_content
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] {p : MvPoly (n + 1) R cmp} (hp : p ≠ 0) :
    contentIn i cmp' (primPartIn i cmp' p) = 1 := by
  let c := contentIn i cmp' p
  let q := primPartIn i cmp' p
  let d := contentIn i cmp' q
  have hrec : constIn (cmp := cmp) i cmp' c * q = p :=
    contentIn_mul_primPartIn i cmp' p
  have hc : c ≠ 0 := by
    intro hzero
    apply hp
    rw [← hrec, hzero, constIn_zero, MvPoly.zero_mul]
  have hcoeff : ∀ k,
      (toUnivariate i cmp' p).coeff k =
        c * (toUnivariate i cmp' q).coeff k := by
    intro k
    rw [← hrec]
    exact coeff_constIn_mul i c q k
  have hcd : c * d ∣ c := by
    apply dvd_contentIn i cmp' p (c * d)
    intro k
    have hd := contentIn_dvd_coeff i cmp' q k
    change d ∣ (toUnivariate i cmp' q).coeff k at hd
    rcases (GcdDomainLaws.dvd_iff d
      ((toUnivariate i cmp' q).coeff k)).mp hd with ⟨a, ha⟩
    apply (GcdDomainLaws.dvd_iff (c * d)
      ((toUnivariate i cmp' p).coeff k)).mpr
    refine ⟨a, ?_⟩
    rw [hcoeff, ha, MvPoly.mul_assoc]
  rcases (GcdDomainLaws.dvd_iff (c * d) c).mp hcd with ⟨u, hu⟩
  have hunit : d * u = 1 := by
    have hzero : c * (1 - d * u) = 0 := by
      calc
        c * (1 - d * u) = c - (c * d) * u := by grind
        _ = 0 := by rw [← hu]; grind
    rcases GcdDomainLaws.no_zero_div c (1 - d * u) hzero with
      hzero | hrest
    · exact False.elim (hc hzero)
    · grind
  have hisUnit : polyIsUnit d = true :=
    (polyIsUnit_iff d).mpr ⟨u, hunit⟩
  have hnorm : polyNormalize d = d := contentIn_normalized i cmp' q
  calc
    contentIn i cmp' (primPartIn i cmp' p) = d := rfl
    _ = polyNormalize d := hnorm.symm
    _ = 1 := polyNormalize_unit d hisUnit

theorem contentIn_mul
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p q : MvPoly (n + 1) R cmp) :
    contentIn i cmp' (p * q) = contentIn i cmp' p * contentIn i cmp' q := by
  sorry

theorem primPartIn_mul
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p q : MvPoly (n + 1) R cmp) :
    primPartIn i cmp' (p * q) = primPartIn i cmp' p * primPartIn i cmp' q := by
  sorry

/-- Canonically normalized gcd. -/
def gcd [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : MvPoly n R cmp :=
  (gcdCert f h).gcd

/-- The exact left and right cofactors accompanying the canonical gcd. -/
def cofactors [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : MvPoly n R cmp × MvPoly n R cmp :=
  let cert := gcdCert f h
  (cert.cofL, cert.cofR)

def gcdWith [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [GcdProducer R]
    (cfg : GcdConfig) (f h : MvPoly n R cmp) : MvPoly n R cmp × Rand :=
  let run := gcdCertWith cfg f h
  (run.cert.gcd, run.rand)

def isCoprime [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : Bool :=
  polyIsUnit (gcd f h)

def gcdList [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [GcdProducer R]
    (ps : List (MvPoly n R cmp)) : MvPoly n R cmp :=
  ps.foldl gcd 0

def lcm [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : MvPoly n R cmp :=
  let cert := gcdCert f h
  polyNormalize (cert.gcd * cert.cofL * cert.cofR)

/-! Install the executable operations before stating contracts that use the
polynomial `GcdOps.isUnit` spelling.  The lawful instance is assembled from
those contracts below. -/

instance instGcdOpsMvPoly [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [GcdProducer R] :
    GcdOps (MvPoly n R cmp) where
  gcd := gcd
  exactDiv := quotient
  isUnit := polyIsUnit
  normUnit := polyNormUnit

private theorem checkedResult [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) :
    CheckedGcdResult f h (gcd f h) (cofactors f h).1 (cofactors f h).2 := by
  simpa [gcd, cofactors] using
    (checkGcd_sound (gcdCert_checks f h))

/-- The canonical gcd divides its left input. -/
theorem gcd_dvd_left [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : gcd f h ∣ f := by
  rcases checkedResult f h with ⟨hf, _, _, _⟩
  refine ⟨(cofactors f h).1, ?_⟩
  exact hf.trans (MvPoly.mul_comm (gcd f h) (cofactors f h).1)

/-- The canonical gcd divides its right input. -/
theorem gcd_dvd_right [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : gcd f h ∣ h := by
  rcases checkedResult f h with ⟨_, hh, _, _⟩
  refine ⟨(cofactors f h).2, ?_⟩
  exact hh.trans (MvPoly.mul_comm (gcd f h) (cofactors f h).2)

/-- Every common divisor divides the canonical gcd. -/
theorem dvd_gcd [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h d : MvPoly n R cmp) (hf : d ∣ f) (hh : d ∣ h) : d ∣ gcd f h := by
  exact (checkedResult f h).greatest d hf hh

theorem gcd_normalized [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : polyNormalize (gcd f h) = gcd f h := by
  exact (checkedResult f h).2.2.1

@[simp] theorem gcd_zero_zero [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] :
    gcd (0 : MvPoly n R cmp) 0 = 0 := by
  have hzero : (0 : MvPoly n R cmp) ∣ 0 := by
    refine ⟨0, ?_⟩
    exact (MvPoly.mul_zero 0).symm
  rcases dvd_gcd 0 0 0 hzero hzero with ⟨q, hq⟩
  exact hq.trans (MvPoly.mul_zero q)

@[simp] theorem gcd_zero_right [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f : MvPoly n R cmp) : gcd f 0 = polyNormalize f := by
  let g := gcd f 0
  let a := (cofactors f 0).1
  let b := (cofactors f 0).2
  change g = polyNormalize f
  have hfa : f = g * a := (checkedResult f 0).1
  have hzero : (0 : MvPoly n R cmp) = g * b := (checkedResult f 0).2.1
  by_cases hg : g = 0
  · have hf : f = 0 := by
      calc
        f = g * a := hfa
        _ = 0 := by rw [hg, MvPoly.zero_mul]
    rw [hg, hf, polyNormalize_zero]
  · have hb : b = 0 := by
      rcases GcdDomainLaws.no_zero_div g b hzero.symm with hgz | hbz
      · exact False.elim (hg hgz)
      · exact hbz
    have haunit : polyIsUnit a = true := by
      apply (polyIsUnit_iff a).mpr
      apply (checkedResult f 0).2.2.2 a
      · refine ⟨1, ?_⟩
        exact (MvPoly.one_mul a).symm
      · refine ⟨0, ?_⟩
        exact hb.trans (MvPoly.zero_mul a).symm
    symm
    calc
      polyNormalize f = polyNormalize (g * a) :=
        congrArg polyNormalize hfa
      _ = polyNormalize g * polyNormalize a := polyNormalize_mul g a
      _ = g * 1 := by rw [gcd_normalized, polyNormalize_unit a haunit]
      _ = g := MvPoly.mul_one g

@[simp] theorem gcd_zero_left [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f : MvPoly n R cmp) : gcd 0 f = polyNormalize f := by
  let g := gcd 0 f
  let a := (cofactors 0 f).1
  let b := (cofactors 0 f).2
  change g = polyNormalize f
  have hzero : (0 : MvPoly n R cmp) = g * a := (checkedResult 0 f).1
  have hfb : f = g * b := (checkedResult 0 f).2.1
  by_cases hg : g = 0
  · have hf : f = 0 := by
      calc
        f = g * b := hfb
        _ = 0 := by rw [hg, MvPoly.zero_mul]
    rw [hg, hf, polyNormalize_zero]
  · have ha : a = 0 := by
      rcases GcdDomainLaws.no_zero_div g a hzero.symm with hgz | haz
      · exact False.elim (hg hgz)
      · exact haz
    have hbunit : polyIsUnit b = true := by
      apply (polyIsUnit_iff b).mpr
      apply (checkedResult 0 f).2.2.2 b
      · refine ⟨0, ?_⟩
        exact ha.trans (MvPoly.zero_mul b).symm
      · refine ⟨1, ?_⟩
        exact (MvPoly.one_mul b).symm
    symm
    calc
      polyNormalize f = polyNormalize (g * b) :=
        congrArg polyNormalize hfb
      _ = polyNormalize g * polyNormalize b := polyNormalize_mul g b
      _ = g * 1 := by rw [gcd_normalized, polyNormalize_unit b hbunit]
      _ = g := MvPoly.mul_one g

theorem gcd_eq_one_of_left_unit [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) (hf : polyIsUnit f = true) : gcd f h = 1 := by
  rcases (polyIsUnit_iff f).mp hf with ⟨u, hu⟩
  rcases gcd_dvd_left f h with ⟨q, hq⟩
  have hunit : polyIsUnit (gcd f h) = true := by
    apply (polyIsUnit_iff (gcd f h)).mpr
    refine ⟨q * u, ?_⟩
    calc
      gcd f h * (q * u) = (q * gcd f h) * u := by
        rw [← MvPoly.mul_assoc, MvPoly.mul_comm (gcd f h) q]
      _ = f * u := by rw [← hq]
      _ = 1 := hu
  calc
    gcd f h = polyNormalize (gcd f h) := (gcd_normalized f h).symm
    _ = 1 := polyNormalize_unit _ hunit

theorem gcd_eq_one_of_right_unit [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) (hh : polyIsUnit h = true) : gcd f h = 1 := by
  rcases (polyIsUnit_iff h).mp hh with ⟨u, hu⟩
  rcases gcd_dvd_right f h with ⟨q, hq⟩
  have hunit : polyIsUnit (gcd f h) = true := by
    apply (polyIsUnit_iff (gcd f h)).mpr
    refine ⟨q * u, ?_⟩
    calc
      gcd f h * (q * u) = (q * gcd f h) * u := by
        rw [← MvPoly.mul_assoc, MvPoly.mul_comm (gcd f h) q]
      _ = h * u := by rw [← hq]
      _ = 1 := hu
  calc
    gcd f h = polyNormalize (gcd f h) := (gcd_normalized f h).symm
    _ = 1 := polyNormalize_unit _ hunit

theorem gcd_mul_cofactor_left [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) :
    gcd f h * (cofactors f h).1 = f := by
  exact (checkedResult f h).1.symm

theorem gcd_mul_cofactor_right [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) :
    gcd f h * (cofactors f h).2 = h := by
  exact (checkedResult f h).2.1.symm

theorem cofactors_spec [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) :
    f = gcd f h * (cofactors f h).1 ∧
      h = gcd f h * (cofactors f h).2 := by
  exact ⟨(checkedResult f h).1, (checkedResult f h).2.1⟩

theorem cofactors_coprime [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) :
    ∀ d, d ∣ (cofactors f h).1 → d ∣ (cofactors f h).2 →
      GcdOps.isUnit d = true := by
  intro d hdL hdR
  apply (polyIsUnit_iff d).mpr
  exact (checkedResult f h).2.2.2 d hdL hdR

theorem isCoprime_iff [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) :
    isCoprime f h = true ↔
      ∀ d, d ∣ f → d ∣ h → GcdOps.isUnit d = true := by
  unfold isCoprime
  rw [polyIsUnit_iff]
  constructor
  · rintro ⟨u, hu⟩ d hdf hdh
    rcases dvd_gcd f h d hdf hdh with ⟨q, hq⟩
    apply (polyIsUnit_iff d).mpr
    refine ⟨q * u, ?_⟩
    calc
      d * (q * u) = (d * q) * u := (mul_assoc d q u).symm
      _ = (q * d) * u := congrArg (fun p => p * u)
        (Lean.Grind.CommSemiring.mul_comm d q)
      _ = gcd f h * u := by rw [← hq]
      _ = 1 := hu
  · intro hcop
    exact (polyIsUnit_iff (gcd f h)).mp
      (hcop (gcd f h) (gcd_dvd_left f h) (gcd_dvd_right f h))

@[simp] theorem gcdList_nil [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] :
    gcdList ([] : List (MvPoly n R cmp)) = 0 := rfl

theorem gcdList_dvd [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    {p : MvPoly n R cmp} {ps : List (MvPoly n R cmp)} (hp : p ∈ ps) :
    gcdList ps ∣ p := by
  have dvdRefl (q : MvPoly n R cmp) : q ∣ q := by
    refine ⟨1, ?_⟩
    exact (MvPoly.one_mul q).symm
  have dvdTrans {a b c : MvPoly n R cmp}
      (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
    rcases hab with ⟨q, hq⟩
    rcases hbc with ⟨r, hr⟩
    refine ⟨r * q, ?_⟩
    calc
      c = r * b := hr
      _ = r * (q * a) := congrArg (fun x => r * x) hq
      _ = (r * q) * a := (MvPoly.mul_assoc r q a).symm
  have foldDvdAcc (xs : List (MvPoly n R cmp)) (acc : MvPoly n R cmp) :
      xs.foldl gcd acc ∣ acc := by
    induction xs generalizing acc with
    | nil => exact dvdRefl acc
    | cons a xs ih =>
        exact dvdTrans (ih (acc := gcd acc a)) (gcd_dvd_left acc a)
  have foldDvdMem (xs : List (MvPoly n R cmp)) (acc q : MvPoly n R cmp)
      (hq : q ∈ xs) : xs.foldl gcd acc ∣ q := by
    induction xs generalizing acc with
    | nil => simp at hq
    | cons a xs ih =>
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp hq with hqa | hq
        · subst q
          exact dvdTrans (foldDvdAcc xs (gcd acc a))
            (gcd_dvd_right acc a)
        · exact ih (acc := gcd acc a) hq
  exact foldDvdMem ps 0 p hp

theorem dvd_gcdList [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    {d : MvPoly n R cmp} {ps : List (MvPoly n R cmp)}
    (hd : ∀ p ∈ ps, d ∣ p) : d ∣ gcdList ps := by
  have foldGreatest (xs : List (MvPoly n R cmp)) (acc : MvPoly n R cmp)
      (hacc : d ∣ acc) (hxs : ∀ p ∈ xs, d ∣ p) :
      d ∣ xs.foldl gcd acc := by
    induction xs generalizing acc with
    | nil => exact hacc
    | cons a xs ih =>
        apply ih (acc := gcd acc a)
        · exact dvd_gcd acc a d hacc (hxs a (by simp))
        · intro p hp
          exact hxs p (by simp [hp])
  unfold gcdList
  apply foldGreatest ps 0
  · refine ⟨0, ?_⟩
    exact (MvPoly.zero_mul d).symm
  · exact hd

@[simp] theorem lcm_zero_left [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f : MvPoly n R cmp) : lcm 0 f = 0 := by
  change polyNormalize
    (gcd 0 f * (cofactors 0 f).1 * (cofactors 0 f).2) = 0
  rw [← (checkedResult 0 f).1]
  rw [MvPoly.zero_mul, polyNormalize_zero]

@[simp] theorem lcm_zero_right [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f : MvPoly n R cmp) : lcm f 0 = 0 := by
  change polyNormalize
    (gcd f 0 * (cofactors f 0).1 * (cofactors f 0).2) = 0
  have hswap :
      gcd f 0 * (cofactors f 0).1 * (cofactors f 0).2 =
        (gcd f 0 * (cofactors f 0).2) * (cofactors f 0).1 := by
    calc
      gcd f 0 * (cofactors f 0).1 * (cofactors f 0).2 =
          gcd f 0 * ((cofactors f 0).1 * (cofactors f 0).2) :=
        MvPoly.mul_assoc _ _ _
      _ = gcd f 0 * ((cofactors f 0).2 * (cofactors f 0).1) :=
        congrArg (fun p => gcd f 0 * p)
          (MvPoly.mul_comm (cofactors f 0).1 (cofactors f 0).2)
      _ = (gcd f 0 * (cofactors f 0).2) * (cofactors f 0).1 :=
        (MvPoly.mul_assoc _ _ _).symm
  rw [hswap, ← (checkedResult f 0).2.1]
  rw [MvPoly.zero_mul, polyNormalize_zero]

theorem dvd_lcm_left [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : f ∣ lcm f h := by
  change f ∣ polyNormalize
    (gcd f h * (cofactors f h).1 * (cofactors f h).2)
  let raw := gcd f h * (cofactors f h).1 * (cofactors f h).2
  refine ⟨(cofactors f h).2 * polyNormUnit raw, ?_⟩
  change raw * polyNormUnit raw =
    ((cofactors f h).2 * polyNormUnit raw) * f
  calc
    raw * polyNormUnit raw =
        (gcd f h * (cofactors f h).1) *
          ((cofactors f h).2 * polyNormUnit raw) :=
      MvPoly.mul_assoc _ _ _
    _ = ((cofactors f h).2 * polyNormUnit raw) *
          (gcd f h * (cofactors f h).1) := MvPoly.mul_comm _ _
    _ = ((cofactors f h).2 * polyNormUnit raw) * f :=
      congrArg (fun p => ((cofactors f h).2 * polyNormUnit raw) * p)
        (checkedResult f h).1.symm

theorem dvd_lcm_right [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : h ∣ lcm f h := by
  change h ∣ polyNormalize
    (gcd f h * (cofactors f h).1 * (cofactors f h).2)
  let raw := gcd f h * (cofactors f h).1 * (cofactors f h).2
  refine ⟨(cofactors f h).1 * polyNormUnit raw, ?_⟩
  change raw * polyNormUnit raw =
    ((cofactors f h).1 * polyNormUnit raw) * h
  calc
    raw * polyNormUnit raw =
        (gcd f h * (cofactors f h).2 * (cofactors f h).1) *
          polyNormUnit raw := by
      congr 2
      calc
        gcd f h * (cofactors f h).1 * (cofactors f h).2 =
            gcd f h * ((cofactors f h).1 * (cofactors f h).2) :=
          MvPoly.mul_assoc _ _ _
        _ = gcd f h * ((cofactors f h).2 * (cofactors f h).1) :=
          congrArg (fun p => gcd f h * p)
            (MvPoly.mul_comm (cofactors f h).1 (cofactors f h).2)
        _ = gcd f h * (cofactors f h).2 * (cofactors f h).1 :=
          (MvPoly.mul_assoc _ _ _).symm
    _ = (gcd f h * (cofactors f h).2) *
          ((cofactors f h).1 * polyNormUnit raw) :=
      MvPoly.mul_assoc _ _ _
    _ = ((cofactors f h).1 * polyNormUnit raw) *
          (gcd f h * (cofactors f h).2) := MvPoly.mul_comm _ _
    _ = ((cofactors f h).1 * polyNormUnit raw) * h :=
      congrArg (fun p => ((cofactors f h).1 * polyNormUnit raw) * p)
        (checkedResult f h).2.1.symm

theorem lcm_dvd [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h m : MvPoly n R cmp) (hf : f ∣ m) (hh : h ∣ m) :
    lcm f h ∣ m := by
  let g := gcd f h
  let a := (cofactors f h).1
  let b := (cofactors f h).2
  let raw := g * a * b
  change polyNormalize raw ∣ m
  have hfa : f = g * a := (checkedResult f h).1
  have hhb : h = g * b := (checkedResult f h).2.1
  by_cases hg : g = 0
  · have hfzero : f = 0 := by
      calc
        f = g * a := hfa
        _ = 0 := by rw [hg, MvPoly.zero_mul]
    rcases hf with ⟨q, hqm⟩
    have hm : m = 0 := by
      calc
        m = q * f := hqm
        _ = 0 := by rw [hfzero, MvPoly.mul_zero]
    refine ⟨0, ?_⟩
    calc
      m = 0 := hm
      _ = 0 * polyNormalize raw := (MvPoly.zero_mul _).symm
  · rcases hf with ⟨x, hxm⟩
    rcases hh with ⟨y, hym⟩
    have hcancel : x * a = y * b := by
      have heq : g * (x * a) = g * (y * b) := by
        calc
          g * (x * a) = (g * x) * a := (MvPoly.mul_assoc g x a).symm
          _ = (x * g) * a :=
            congrArg (fun p => p * a) (MvPoly.mul_comm g x)
          _ = x * (g * a) := MvPoly.mul_assoc x g a
          _ = m := (hxm.trans (congrArg (fun p => x * p) hfa)).symm
          _ = y * (g * b) := hym.trans (congrArg (fun p => y * p) hhb)
          _ = (y * g) * b := (MvPoly.mul_assoc y g b).symm
          _ = (g * y) * b :=
            congrArg (fun p => p * b) (MvPoly.mul_comm y g)
          _ = g * (y * b) := MvPoly.mul_assoc g y b
      have hzero : g * (x * a - y * b) = 0 := by grind
      rcases GcdDomainLaws.no_zero_div g (x * a - y * b) hzero with
        hgz | hrest
      · exact False.elim (hg hgz)
      · grind
    have hcop : CoprimeCofactors a b := by
      exact (checkedResult f h).2.2.2
    have hbxa : b ∣ x * a := ⟨y, hcancel⟩
    have hbxb : b ∣ x * b := ⟨x, rfl⟩
    have hbx : b ∣ x :=
      CoprimeCancelLaws.cancel_coprime x a b b hcop hbxa hbxb
    rcases hbx with ⟨z, hx⟩
    have hraw : raw ∣ m := by
      refine ⟨z, ?_⟩
      calc
        m = x * f := hxm
        _ = (z * b) * (g * a) := by rw [hx, hfa]
        _ = z * (b * (g * a)) := MvPoly.mul_assoc _ _ _
        _ = z * ((g * a) * b) :=
          congrArg (fun p => z * p) (MvPoly.mul_comm b (g * a))
        _ = z * raw := rfl
    rcases hraw with ⟨z, hzm⟩
    rcases (polyIsUnit_iff (polyNormUnit raw)).mp
        (polyNormUnit_isUnit raw) with ⟨v, hv⟩
    refine ⟨z * v, ?_⟩
    change m = (z * v) * (raw * polyNormUnit raw)
    calc
      m = z * raw := hzm
      _ = (z * v) * (raw * polyNormUnit raw) := by grind

theorem lcm_normalized [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : polyNormalize (lcm f h) = lcm f h := by
  exact polyNormalize_idem _

private theorem reorder_mul
    {cmp' : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp] [IsMonomialOrder cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (p q : MvPoly n R cmp) :
    reorder cmp' (p * q) = reorder cmp' p * reorder cmp' q := by
  apply ext
  intro m
  rw [coeff_reorder, coeff_mul, coeff_mul]
  apply List.foldl_add_congr (Mono.splits m)
  intro ab _
  rw [coeff_reorder, coeff_reorder]

private theorem reorder_reorder
    {cmp' : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp] [IsMonomialOrder cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (p : MvPoly n R cmp) : reorder cmp (reorder cmp' p) = p := by
  apply ext
  intro m
  rw [coeff_reorder, coeff_reorder]

private theorem reorder_dvd
    {cmp' : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp] [IsMonomialOrder cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    {p q : MvPoly n R cmp} (hpq : p ∣ q) :
    reorder cmp' p ∣ reorder cmp' q := by
  rcases hpq with ⟨a, ha⟩
  refine ⟨reorder cmp' a, ?_⟩
  calc
    reorder cmp' q = reorder cmp' (a * p) := congrArg (reorder cmp') ha
    _ = reorder cmp' a * reorder cmp' p := reorder_mul a p

private theorem eq_normalize_of_dvd [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R]
    (a b : MvPoly n R cmp) (ha : polyNormalize a = a)
    (hab : a ∣ b) (hba : b ∣ a) : a = polyNormalize b := by
  rcases hab with ⟨q, hbq⟩
  by_cases hazero : a = 0
  · have hbzero : b = 0 := by
      calc
        b = q * a := hbq
        _ = 0 := by rw [hazero, MvPoly.mul_zero]
    rw [hazero, hbzero, polyNormalize_zero]
  · rcases hba with ⟨r, har⟩
    have hqr : q * r = 1 := by
      have hzero : (q * r - 1) * a = 0 := by
        rw [har, hbq]
        grind
      rcases GcdDomainLaws.no_zero_div (q * r - 1) a hzero with
        hrest | haz
      · grind
      · exact False.elim (hazero haz)
    have hqunit : polyIsUnit q = true :=
      (polyIsUnit_iff q).mpr ⟨r, hqr⟩
    symm
    calc
      polyNormalize b = polyNormalize (q * a) :=
        congrArg polyNormalize hbq
      _ = polyNormalize q * polyNormalize a := polyNormalize_mul q a
      _ = 1 * a := by rw [polyNormalize_unit q hqunit, ha]
      _ = a := MvPoly.one_mul a

theorem gcd_reorder
    {cmp' : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp] [IsMonomialOrder cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) :
    ∃ u v : R, u * v = 1 ∧
      gcd (reorder cmp' f) (reorder cmp' h) =
        reorder cmp' (gcd f h) * C u := by
  let g := gcd f h
  let g' := gcd (reorder cmp' f) (reorder cmp' h)
  let r := reorder cmp' g
  have hrdvd : r ∣ g' := by
    apply dvd_gcd
    · exact reorder_dvd (gcd_dvd_left f h)
    · exact reorder_dvd (gcd_dvd_right f h)
  have hg'dvd : g' ∣ r := by
    have hleft : reorder cmp g' ∣ f := by
      have := reorder_dvd (cmp := cmp') (cmp' := cmp)
        (gcd_dvd_left (reorder cmp' f) (reorder cmp' h))
      simpa [reorder_reorder] using this
    have hright : reorder cmp g' ∣ h := by
      have := reorder_dvd (cmp := cmp') (cmp' := cmp)
        (gcd_dvd_right (reorder cmp' f) (reorder cmp' h))
      simpa [reorder_reorder] using this
    have hback : reorder cmp g' ∣ g := dvd_gcd f h _ hleft hright
    have := reorder_dvd (cmp := cmp) (cmp' := cmp') hback
    simpa [reorder_reorder] using this
  have hcanon : g' = polyNormalize r :=
    eq_normalize_of_dvd g' r (gcd_normalized _ _) hg'dvd hrdvd
  cases hlead : r.leadingTerm with
  | none =>
      refine ⟨1, 1, Lean.Grind.Semiring.mul_one 1, ?_⟩
      change g' = r * C 1
      rw [hcanon]
      unfold polyNormalize polyNormUnit
      rw [hlead]
      rfl
  | some term =>
      rcases term with ⟨m, c⟩
      rcases LawfulGcdOps.normUnit_unit c with ⟨v, hv⟩
      refine ⟨GcdOps.normUnit c, v, hv, ?_⟩
      change g' = r * C (GcdOps.normUnit c)
      rw [hcanon]
      unfold polyNormalize polyNormUnit
      rw [hlead]

/-- Convert an arity-one integer polynomial to the actual `ZPoly` kernel. -/
def toZPoly {cmp : Mono 1 → Mono 1 → Ordering}
    [IsMonomialOrder cmp] (f : MvPoly 1 Int cmp) : ZPoly :=
  let i : Fin 1 := ⟨0, by omega⟩
  let q := toUnivariate i Mono.lex f
  DensePoly.ofList <| (List.range q.size).map fun k => coeff Mono.zero (q.coeff k)

/-- Convert an integer univariate kernel value back to arity one. -/
def ofZPoly {cmp : Mono 1 → Mono 1 → Ordering}
    [IsMonomialOrder cmp] (f : ZPoly) : MvPoly 1 Int cmp :=
  let i : Fin 1 := ⟨0, by omega⟩
  ofUnivariate (cmp := cmp) i Mono.lex <|
    DensePoly.ofList <| (List.range f.size).map fun k => C (f.coeff k)

instance instLawfulGcdOpsMvPoly [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] :
    LawfulGcdOps (MvPoly n R cmp) := by
  refine {
    dvd_iff := ?_
    one_ne_zero := ?_
    no_zero_div := ?_
    gcd_dvd_left := gcd_dvd_left
    gcd_dvd_right := gcd_dvd_right
    dvd_gcd := dvd_gcd
    gcd_normalized := gcd_normalized
    exactDiv_cancel := ?_
    isUnit_iff := polyIsUnit_iff
    normUnit_unit := ?_
    normalize_mul := polyNormalize_mul
    normalize_idem := polyNormalize_idem
    normalize_unit := polyNormalize_unit }
  · intro a b
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.trans (MvPoly.mul_comm q a)⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.trans (MvPoly.mul_comm a q)⟩
  · intro hone
    have hcoeff := congrArg (coeff (Mono.zero : Mono n)) hone
    rw [coeff_one, coeff_zero, Hex.ite_eq_left rfl] at hcoeff
    exact LawfulGcdOps.one_ne_zero hcoeff
  · intro a b hab
    exact GcdDomainLaws.no_zero_div a b hab
  · intro a b hb
    change quotient (a * b) b = a
    unfold quotient
    have hdiv : divExact? (a * b) b = some a :=
      (divExact?_eq hb).mpr rfl
    simp [hdiv]
  · intro a
    exact (polyIsUnit_iff (polyNormUnit a)).mp
      (polyNormUnit_isUnit a)

end Hex.MvPoly

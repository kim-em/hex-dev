/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexMvGcd.Gauss
public import HexMvGcd.Brown
public import HexPolyZGcd

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
  sorry

theorem gcdCertWith_checks [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (cfg : GcdConfig) (f h : MvPoly n R cmp) :
    checkGcd f h (gcdCertWith cfg f h).cert = true := by
  sorry

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
  sorry

theorem contentIn_mul_primPartIn
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p : MvPoly (n + 1) R cmp) :
    constIn i cmp' (contentIn i cmp' p) * primPartIn i cmp' p = p := by
  sorry

theorem contentIn_dvd_coeff
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p : MvPoly (n + 1) R cmp) (k : Nat) :
    contentIn i cmp' p ∣ (toUnivariate i cmp' p).coeff k := by
  sorry

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
  sorry

@[simp] theorem contentIn_zero
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] :
    contentIn (R := R) (cmp := cmp) i cmp' 0 = 0 := by
  sorry

@[simp] theorem primPartIn_zero
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] :
    primPartIn (R := R) (cmp := cmp) i cmp' 0 = 0 := by
  sorry

theorem primPartIn_content
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] {p : MvPoly (n + 1) R cmp} (hp : p ≠ 0) :
    contentIn i cmp' (primPartIn i cmp' p) = 1 := by
  sorry

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

theorem gcd_dvd_left [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : gcd f h ∣ f := by
  rcases checkedResult f h with ⟨hf, _, _, _⟩
  refine ⟨(cofactors f h).1, ?_⟩
  exact hf.trans (MvPoly.mul_comm (gcd f h) (cofactors f h).1)

theorem gcd_dvd_right [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : gcd f h ∣ h := by
  rcases checkedResult f h with ⟨_, hh, _, _⟩
  refine ⟨(cofactors f h).2, ?_⟩
  exact hh.trans (MvPoly.mul_comm (gcd f h) (cofactors f h).2)

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
  sorry

@[simp] theorem gcd_zero_left [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f : MvPoly n R cmp) : gcd 0 f = polyNormalize f := by
  sorry

theorem gcd_eq_one_of_left_unit [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) (hf : polyIsUnit f = true) : gcd f h = 1 := by
  sorry

theorem gcd_eq_one_of_right_unit [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) (hh : polyIsUnit h = true) : gcd f h = 1 := by
  sorry

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
  sorry

theorem lcm_normalized [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : polyNormalize (lcm f h) = lcm f h := by
  exact polyNormalize_idem _

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
  sorry

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
  constructor <;> intros <;> sorry

end Hex.MvPoly

namespace Hex

/-! The actual `HexPolyZGcd` kernel supplies the required `DensePoly Int`
coefficient instance. -/

instance instGcdOpsZPoly : GcdOps ZPoly where
  gcd := ZPoly.gcd
  exactDiv f g := (ZPoly.divExact? f g).getD 0
  isUnit f := decide (f.size = 1 ∧ (f.coeff 0 = 1 ∨ f.coeff 0 = -1))
  normUnit f := if f = 0 ∨ 0 < f.leadingCoeff then 1 else -1

instance instLawfulGcdOpsZPoly : LawfulGcdOps ZPoly := by
  constructor <;> intros <;> sorry

end Hex

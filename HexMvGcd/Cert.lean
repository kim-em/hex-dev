/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Modulus
public import HexMvGcd.CertData
public import HexMvGcd.Gauss
public import HexPolyFp

@[expose] public section
set_option backward.proofsInPublic true

/-!
Checked recursive certificates for multivariate gcd and content.

The three datatypes are mutually inductive because positive-arity coprimality
certificates contain checked coefficient-content folds, whose steps are gcd
certificates one arity lower.  Every cycle therefore decreases the arity.
-/

namespace Hex.MvPoly

universe u v

/-- Coefficientwise map for dense polynomials, allowing leading coefficients
to vanish. -/
def denseMapCoeffs {S : Type u} {T : Type v}
    [Zero S] [DecidableEq S] [Zero T] [DecidableEq T] [BEq T] [LawfulBEq T]
    (f : S → T) (p : DensePoly S) : DensePoly T :=
  DensePoly.ofCoeffs <| Array.ofFn (n := p.size) fun k => f (p.coeff k)

@[simp] theorem coeff_denseMapCoeffs {S : Type u} {T : Type v}
    [Zero S] [DecidableEq S] [Zero T] [DecidableEq T] [BEq T] [LawfulBEq T]
    (f : S → T) (hzero : f 0 = 0) (p : DensePoly S) (k : Nat) :
    (denseMapCoeffs f p).coeff k = f (p.coeff k) := by
  rw [denseMapCoeffs, DensePoly.coeff_ofCoeffs,
    Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases hk : k < p.size
  · rw [dite_eq_left hk, Option.getD_some]
  · rw [dite_eq_right hk, Option.getD_none,
      DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hk)]
    exact hzero.symm

theorem denseMapCoeffs_mul {S : Type u} {T : Type v}
    [Lean.Grind.CommRing S] [DecidableEq S]
    [Lean.Grind.CommRing T] [DecidableEq T] [BEq T] [LawfulBEq T]
    (f : S → T) (hzero : f 0 = 0)
    (hadd : ∀ a b, f (a + b) = f a + f b)
    (hmul : ∀ a b, f (a * b) = f a * f b)
    (p q : DensePoly S) :
    denseMapCoeffs f (p * q) = denseMapCoeffs f p * denseMapCoeffs f q := by
  apply DensePoly.ext_coeff
  intro k
  rw [coeff_denseMapCoeffs f hzero, DensePoly.coeff_mul,
    DensePoly.mulCoeffSum_eq_diagonal,
    DensePoly.diagonalSum_eq_degree_bound]
  rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum_eq_diagonal,
    DensePoly.diagonalSum_eq_degree_bound]
  have hfold : ∀ (xs : List Nat) (acc : S),
      f (xs.foldl
          (fun z i => z + DensePoly.diagonalMulCoeffTerm p q k i) acc) =
        xs.foldl
          (fun z i => z + DensePoly.diagonalMulCoeffTerm
            (denseMapCoeffs f p) (denseMapCoeffs f q) k i) (f acc) := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons i is ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih, hadd]
        congr 1
        unfold DensePoly.diagonalMulCoeffTerm
        by_cases hki : k < i
        · simp [hki, hzero]
        · simp only [hki, ite_false, hmul,
            coeff_denseMapCoeffs f hzero]
  simpa [hzero] using hfold (List.range (k + 1)) 0

@[simp] theorem denseMapCoeffs_zero {S : Type u} {T : Type v}
    [Lean.Grind.CommRing S] [DecidableEq S]
    [Lean.Grind.CommRing T] [DecidableEq T] [BEq T] [LawfulBEq T]
    (f : S → T) (hzero : f 0 = 0) :
    denseMapCoeffs f (0 : DensePoly S) = 0 := by
  apply DensePoly.ext_coeff
  intro k
  rw [coeff_denseMapCoeffs f hzero, DensePoly.coeff_zero,
    DensePoly.coeff_zero, hzero]

theorem denseMapCoeffs_add {S : Type u} {T : Type v}
    [Lean.Grind.CommRing S] [DecidableEq S]
    [Lean.Grind.CommRing T] [DecidableEq T] [BEq T] [LawfulBEq T]
    (f : S → T) (hzero : f 0 = 0)
    (hadd : ∀ a b, f (a + b) = f a + f b)
    (p q : DensePoly S) :
    denseMapCoeffs f (p + q) = denseMapCoeffs f p + denseMapCoeffs f q := by
  apply DensePoly.ext_coeff
  intro k
  rw [coeff_denseMapCoeffs f hzero, DensePoly.coeff_add_semiring,
    hadd, DensePoly.coeff_add_semiring, coeff_denseMapCoeffs f hzero,
    coeff_denseMapCoeffs f hzero]

/-- Recursive evaluation through univariate views.  This form is used by the
modular certificate checker because its ring laws follow directly from the
corresponding view and dense-evaluation laws. -/
def evalAt {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S] :
    (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
      [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] →
      (Fin n → S) → MvPoly n S cmp → S
  | 0, _, _, _, _, p => coeff Mono.zero p
  | n + 1, _, _, _, x, p =>
      DensePoly.eval
        (denseMapCoeffs
          (evalAt n Mono.lex (fun j => x j.succ))
          (toUnivariate 0 Mono.lex p))
        (x 0)

@[simp] theorem evalAt_zero {n : Nat} {S : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    (x : Fin n → S) : evalAt n cmp x 0 = 0 := by
  induction n with
  | zero => exact coeff_zero Mono.zero
  | succ n ih =>
      simp only [evalAt, toUnivariate_zero,
        denseMapCoeffs_zero _ (ih (fun j => x j.succ)), DensePoly.eval_zero]

theorem evalAt_add {n : Nat} {S : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    (x : Fin n → S) (p q : MvPoly n S cmp) :
    evalAt n cmp x (p + q) = evalAt n cmp x p + evalAt n cmp x q := by
  induction n with
  | zero =>
      simp only [evalAt, coeff_add]
  | succ n ih =>
      simp only [evalAt, toUnivariate_add,
        denseMapCoeffs_add _ (evalAt_zero (fun j => x j.succ))
          (ih (fun j => x j.succ)),
        DensePoly.eval_add_semiring]

theorem evalAt_mul {n : Nat} {S : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    (x : Fin n → S) (p q : MvPoly n S cmp) :
    evalAt n cmp x (p * q) = evalAt n cmp x p * evalAt n cmp x q := by
  induction n with
  | zero =>
      simp only [evalAt, coeff_mul, Mono.splits]
      grind
  | succ n ih =>
      simp only [evalAt, toUnivariate_mul,
        denseMapCoeffs_mul _ (evalAt_zero (fun j => x j.succ))
          (evalAt_add (fun j => x j.succ)) (ih (fun j => x j.succ)),
        DensePoly.eval_mul_commring]

/-- Coefficientwise image followed by evaluation of all remaining variables,
leaving one dense univariate polynomial over the bundled prime field. -/
def imageAt {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (P : ZMod64.Prime)
    (φ : @CoeffHom R P.m _ _ _ _ P.bounds)
    (a : Fin n → @ZMod64 P.m P.bounds)
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (f : MvPoly (n + 1) R cmp) :
    @FpPoly P.m P.bounds :=
  letI : ZMod64.Bounds P.m := P.bounds
  letI : ZMod64.PrimeModulus P.m := ZMod64.primeModulusOfPrime P.prime
  let q := toUnivariate i cmp' f
  denseMapCoeffs
    (fun c => evalAt n cmp' a (MvPoly.mapCoeffs φ.toField c)) q

@[simp] theorem imageAt_zero {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (P : ZMod64.Prime)
    (φ : @CoeffHom R P.m _ _ _ _ P.bounds)
    (a : Fin n → @ZMod64 P.m P.bounds)
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] :
    imageAt P φ a i cmp' (0 : MvPoly (n + 1) R cmp) = 0 := by
  letI : ZMod64.Bounds P.m := P.bounds
  letI : ZMod64.PrimeModulus P.m := ZMod64.primeModulusOfPrime P.prime
  unfold imageAt
  rw [toUnivariate_zero]
  apply denseMapCoeffs_zero
  rw [mapCoeffs_zero φ.map_zero, evalAt_zero]

theorem imageAt_add {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (P : ZMod64.Prime)
    (φ : @CoeffHom R P.m _ _ _ _ P.bounds)
    (a : Fin n → @ZMod64 P.m P.bounds)
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (f h : MvPoly (n + 1) R cmp) :
    imageAt P φ a i cmp' (f + h) =
      imageAt P φ a i cmp' f + imageAt P φ a i cmp' h := by
  letI : ZMod64.Bounds P.m := P.bounds
  letI : ZMod64.PrimeModulus P.m := ZMod64.primeModulusOfPrime P.prime
  unfold imageAt
  rw [toUnivariate_add]
  apply denseMapCoeffs_add
  · rw [mapCoeffs_zero φ.map_zero, evalAt_zero]
  · intro x y
    rw [mapCoeffs_add φ.map_zero φ.map_add, evalAt_add]

theorem imageAt_mul {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (P : ZMod64.Prime)
    (φ : @CoeffHom R P.m _ _ _ _ P.bounds)
    (a : Fin n → @ZMod64 P.m P.bounds)
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (f h : MvPoly (n + 1) R cmp) :
    imageAt P φ a i cmp' (f * h) =
      imageAt P φ a i cmp' f * imageAt P φ a i cmp' h := by
  letI : ZMod64.Bounds P.m := P.bounds
  letI : ZMod64.PrimeModulus P.m := ZMod64.primeModulusOfPrime P.prime
  unfold imageAt
  rw [toUnivariate_mul]
  apply denseMapCoeffs_mul
  · rw [mapCoeffs_zero φ.map_zero, evalAt_zero]
  · intro x y
    rw [mapCoeffs_add φ.map_zero φ.map_add, evalAt_add]
  · intro x y
    rw [mapCoeffs_mul φ.map_zero φ.map_add φ.map_mul, evalAt_mul]

theorem imageAt_size_le {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (P : ZMod64.Prime)
    (φ : @CoeffHom R P.m _ _ _ _ P.bounds)
    (a : Fin n → @ZMod64 P.m P.bounds)
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (f : MvPoly (n + 1) R cmp) :
    (imageAt P φ a i cmp' f).size ≤ (toUnivariate i cmp' f).size := by
  letI : ZMod64.Bounds P.m := P.bounds
  letI : ZMod64.PrimeModulus P.m := ZMod64.primeModulusOfPrime P.prime
  unfold imageAt denseMapCoeffs
  exact Nat.le_trans (DensePoly.size_ofCoeffs_le _) (by simp)

/-- Coefficientwise cast from the integer model used by `ratLift`. -/
def intModelToRat {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Int cmp) : MvPoly n Rat cmp :=
  mapCoeffs (fun z : Int => (z : Rat)) p

/-- The canonical identification of the proof-only integer fraction field
with Lean's rational numbers. -/
private instance : Hex.Fraction.NonzeroOne Int := ⟨by decide⟩

private def fractionIntToRat : Hex.Fraction Int → Rat :=
  Quotient.lift (fun r : Hex.Fraction.Rep Int => Rat.divInt r.num r.den) (by
    intro a b hab
    exact (Rat.divInt_eq_divInt_iff a.den_ne b.den_ne).mpr hab)

private theorem fractionIntToRat_injective :
    Function.Injective fractionIntToRat := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      apply Quotient.sound
      exact (Rat.divInt_eq_divInt_iff a.den_ne b.den_ne).mp h

private theorem fractionIntToRat_ofRep (r : Hex.Fraction.Rep Int) :
    fractionIntToRat (Hex.Fraction.ofRep r) = Rat.divInt r.num r.den := by
  rfl

private theorem fractionIntToRat_zero : fractionIntToRat 0 = 0 := by
  change Rat.divInt 0 1 = 0
  exact Rat.zero_divInt 1

private theorem fractionIntToRat_one : fractionIntToRat 1 = 1 := by
  change Rat.divInt 1 1 = 1
  exact Rat.divInt_self' (by decide)

private theorem fractionIntToRat_ofCoeff (z : Int) :
    fractionIntToRat (Hex.Fraction.ofCoeff z) = (z : Rat) := by
  change Rat.divInt z 1 = (z : Rat)
  calc
    Rat.divInt z 1 = mkRat z 1 := Rat.divInt_ofNat z 1
    _ = (z : Rat) := by simpa using Rat.mkRat_self (z : Rat)

private theorem fractionIntToRat_add (x y : Hex.Fraction Int) :
    fractionIntToRat (x + y) = fractionIntToRat x + fractionIntToRat y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ a b =>
    change fractionIntToRat
        (Hex.Fraction.ofRep a + Hex.Fraction.ofRep b) =
      fractionIntToRat (Hex.Fraction.ofRep a) +
        fractionIntToRat (Hex.Fraction.ofRep b)
    rw [show Hex.Fraction.ofRep a + Hex.Fraction.ofRep b =
      Hex.Fraction.ofRep (Hex.Fraction.Rep.add a b) from rfl]
    rw [fractionIntToRat_ofRep, fractionIntToRat_ofRep,
      fractionIntToRat_ofRep]
    simp only [Hex.Fraction.Rep.add]
    change Rat.divInt (a.num * b.den + b.num * a.den) (a.den * b.den) =
      Rat.divInt a.num a.den + Rat.divInt b.num b.den
    exact (Rat.divInt_add_divInt a.num b.num a.den_ne b.den_ne).symm

private theorem fractionIntToRat_mul (x y : Hex.Fraction Int) :
    fractionIntToRat (x * y) = fractionIntToRat x * fractionIntToRat y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ a b =>
    change fractionIntToRat
        (Hex.Fraction.ofRep a * Hex.Fraction.ofRep b) =
      fractionIntToRat (Hex.Fraction.ofRep a) *
        fractionIntToRat (Hex.Fraction.ofRep b)
    rw [Hex.Fraction.mul_ofRep, fractionIntToRat_ofRep,
      fractionIntToRat_ofRep, fractionIntToRat_ofRep]
    simp only [Hex.Fraction.Rep.mul]
    change Rat.divInt (a.num * b.num) (a.den * b.den) =
      Rat.divInt a.num a.den * Rat.divInt b.num b.den
    exact (Rat.divInt_mul_divInt a.num b.num).symm

private def ratToFraction (q : Rat) : Hex.Fraction Int :=
  Hex.Fraction.ofRep
    ⟨q.num, (q.den : Int), by simpa using q.den_nz⟩

private theorem fractionIntToRat_ratToFraction (q : Rat) :
    fractionIntToRat (ratToFraction q) = q := by
  change Rat.divInt q.num (q.den : Int) = q
  exact Rat.num_divInt_den q

private theorem ratToFraction_fractionIntToRat (x : Hex.Fraction Int) :
    ratToFraction (fractionIntToRat x) = x := by
  apply fractionIntToRat_injective
  rw [fractionIntToRat_ratToFraction]

private theorem ratToFraction_zero : ratToFraction 0 = 0 := by
  apply fractionIntToRat_injective
  rw [fractionIntToRat_ratToFraction, fractionIntToRat_zero]

private theorem ratToFraction_one : ratToFraction 1 = 1 := by
  apply fractionIntToRat_injective
  rw [fractionIntToRat_ratToFraction, fractionIntToRat_one]

private theorem ratToFraction_add (x y : Rat) :
    ratToFraction (x + y) = ratToFraction x + ratToFraction y := by
  apply fractionIntToRat_injective
  rw [fractionIntToRat_ratToFraction, fractionIntToRat_add,
    fractionIntToRat_ratToFraction, fractionIntToRat_ratToFraction]

private theorem ratToFraction_mul (x y : Rat) :
    ratToFraction (x * y) = ratToFraction x * ratToFraction y := by
  apply fractionIntToRat_injective
  rw [fractionIntToRat_ratToFraction, fractionIntToRat_mul,
    fractionIntToRat_ratToFraction, fractionIntToRat_ratToFraction]

private theorem ratToFraction_intCast (z : Int) :
    ratToFraction (z : Rat) = Hex.Fraction.ofCoeff z := by
  apply fractionIntToRat_injective
  rw [fractionIntToRat_ratToFraction, fractionIntToRat_ofCoeff]

private def fractionPolyToRat {n : Nat}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n (Hex.Fraction Int) cmp) : MvPoly n Rat cmp :=
  mapCoeffs fractionIntToRat p

private def ratPolyToFraction {n : Nat}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Rat cmp) : MvPoly n (Hex.Fraction Int) cmp :=
  mapCoeffs ratToFraction p

private theorem fractionPolyToRat_one {n : Nat}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    fractionPolyToRat (1 : MvPoly n (Hex.Fraction Int) cmp) = 1 :=
  mapCoeffs_one fractionIntToRat_zero fractionIntToRat_one

private theorem fractionPolyToRat_mul {n : Nat}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p q : MvPoly n (Hex.Fraction Int) cmp) :
    fractionPolyToRat (p * q) =
      fractionPolyToRat p * fractionPolyToRat q :=
  mapCoeffs_mul fractionIntToRat_zero fractionIntToRat_add
    fractionIntToRat_mul p q

private theorem ratPolyToFraction_mul {n : Nat}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p q : MvPoly n Rat cmp) :
    ratPolyToFraction (p * q) =
      ratPolyToFraction p * ratPolyToFraction q :=
  mapCoeffs_mul ratToFraction_zero ratToFraction_add
    ratToFraction_mul p q

private theorem fractionPolyToRat_ratPolyToFraction {n : Nat}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Rat cmp) :
    fractionPolyToRat (ratPolyToFraction p) = p := by
  apply ext
  intro m
  rw [fractionPolyToRat, ratPolyToFraction,
    coeff_mapCoeffs fractionIntToRat_zero,
    coeff_mapCoeffs ratToFraction_zero,
    fractionIntToRat_ratToFraction]

private theorem fractionPolyToRat_fractionMap {n : Nat}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Int cmp) :
    fractionPolyToRat (fractionMap p) = intModelToRat p := by
  apply ext
  intro m
  rw [fractionPolyToRat, fractionMap, intModelToRat,
    coeff_mapCoeffs fractionIntToRat_zero,
    coeff_mapCoeffs Hex.Fraction.ofCoeff_zero,
    coeff_mapCoeffs (show ((0 : Int) : Rat) = 0 from rfl),
    fractionIntToRat_ofCoeff]

private theorem ratPolyToFraction_intModelToRat {n : Nat}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Int cmp) :
    ratPolyToFraction (intModelToRat p) = fractionMap p := by
  apply ext
  intro m
  rw [ratPolyToFraction, intModelToRat, fractionMap,
    coeff_mapCoeffs ratToFraction_zero,
    coeff_mapCoeffs (show ((0 : Int) : Rat) = 0 from rfl),
    coeff_mapCoeffs Hex.Fraction.ofCoeff_zero,
    ratToFraction_intCast]

/-- The three replay operations at one arity.  Packaging them by arity avoids
Lean's well-founded mutual-recursion compiler: recursive certificate calls
always move to the already-built lower-arity package, while content folds are
ordinary structural recursion on their two lists. -/
structure Cert.CheckOpsAt (R : Type u) [Lean.Grind.CommRing R]
    (E : Cert.Leaves.{v}) (n : Nat) : Type (max (u + 1) (v + 1)) where
  coprime : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    MvPoly n R cmp → MvPoly n R cmp → Cert.Coprime R E n cmp → Bool
  gcd : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    MvPoly n R cmp → MvPoly n R cmp → Cert.Gcd R E n cmp → Bool
  content : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    List (MvPoly n R cmp) → Cert.Content R E n cmp → Bool

@[reducible] def checkGcdUsing {n : Nat} {R : Type u} {E : Cert.Leaves.{v}}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (coprime : MvPoly n R cmp → MvPoly n R cmp →
      Cert.Coprime R E n cmp → Bool)
    (f h : MvPoly n R cmp) (cert : Cert.Gcd R E n cmp) : Bool :=
  (cert.gcd * cert.cofL == f) &&
    (cert.gcd * cert.cofR == h) &&
    (polyNormalize cert.gcd == cert.gcd) &&
    coprime cert.cofL cert.cofR cert.coprime

/-! `checkContentSteps` exposes the accumulator used by content replay.  The
public checker fixes that accumulator to zero; keeping the general recursion
named lets producer proofs state the natural induction invariant. -/

@[reducible] def checkContentSteps {n : Nat} {R : Type u} {E : Cert.Leaves.{v}}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (gcd : MvPoly n R cmp → MvPoly n R cmp → Cert.Gcd R E n cmp → Bool)
    (value acc : MvPoly n R cmp) :
    List (MvPoly n R cmp) → List (Cert.Gcd R E n cmp) → Bool
  | [], [] => acc == value
  | q :: qs, step :: steps =>
      gcd acc q step && checkContentSteps gcd value step.gcd qs steps
  | _, _ => false

@[reducible] def checkContentUsing {n : Nat} {R : Type u} {E : Cert.Leaves.{v}}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (gcd : MvPoly n R cmp → MvPoly n R cmp → Cert.Gcd R E n cmp → Bool)
    (coeffs : List (MvPoly n R cmp)) (cert : Cert.Content R E n cmp) : Bool :=
  checkContentSteps gcd cert.value 0 coeffs cert.steps

@[reducible] def Cert.baseCheck {S : Type u} {E : Cert.Leaves.{v}}
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    [Dvd S] [GcdOps S]
    {cmp : Mono 0 → Mono 0 → Ordering}
    [IsMonomialOrder cmp]
    (checkLeaf : MvPoly 0 S cmp → MvPoly 0 S cmp → E 0 cmp → Bool)
    (f h : MvPoly 0 S cmp) (cert : Cert.Coprime S E 0 cmp) : Bool :=
  match cert with
  | .unit => polyIsUnit f || polyIsUnit h
  | .base u v => u * coeff Mono.zero f + v * coeff Mono.zero h == 1
  | .bezout u v => u * f + v * h == 1
  | .leaf data => checkLeaf f h data

@[reducible] def Cert.succCheck {n : Nat} {S : Type u} {E : Cert.Leaves.{v}}
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    [Dvd S] [GcdOps S]
    (lower : Cert.CheckOpsAt S E n)
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    (checkLeaf : MvPoly (n + 1) S cmp → MvPoly (n + 1) S cmp → E (n + 1) cmp → Bool)
    (f h : MvPoly (n + 1) S cmp)
    (cert : Cert.Coprime S E (n + 1) cmp) : Bool := by
  cases cert with
  | unit => exact polyIsUnit f || polyIsUnit h
  | bezout u v => exact u * f + v * h == 1
  | leaf data => exact checkLeaf f h data
  | split i cmp' P φ a α β left right rest =>
      letI : ZMod64.Bounds P.m := P.bounds
      letI : ZMod64.PrimeModulus P.m :=
        ZMod64.primeModulusOfPrime P.prime
      let fImage := imageAt P φ a i cmp' f
      let hImage := imageAt P φ a i cmp' h
      let fView := toUnivariate i cmp' f
      let hView := toUnivariate i cmp' h
      exact decide (fImage.degree? = fView.degree?) &&
        decide (hImage.degree? = hView.degree?) &&
        (α * fImage + β * hImage == 1) &&
        lower.content cmp' fView.toArray.toList left &&
        lower.content cmp' hView.toArray.toList right &&
        lower.coprime cmp' left.value right.value rest
  | splitBezout i cmp' u v r left right rest =>
      let fView := toUnivariate i cmp' f
      let hView := toUnivariate i cmp' h
      exact decide (r ≠ 0) &&
        (u * f + v * h == constIn i cmp' r) &&
        lower.content cmp' fView.toArray.toList left &&
        lower.content cmp' hView.toArray.toList right &&
        lower.coprime cmp' left.value right.value rest

/-- Generic replay parameterized by a leaf checker. Soundness requires a
separate contract for that callback; the public checkers fix it to `checkRatLeaf`. -/
@[reducible] def Cert.checkOps {S : Type u} {E : Cert.Leaves.{v}}
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    [Dvd S] [GcdOps S]
    (checkLeaf : (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
      [IsMonomialOrder cmp] → MvPoly n S cmp → MvPoly n S cmp → E n cmp → Bool) :
    (n : Nat) → Cert.CheckOpsAt S E n
  | 0 =>
      { coprime := fun cmp _ => Cert.baseCheck (cmp := cmp) (checkLeaf 0 cmp)
        gcd := fun cmp _ => checkGcdUsing (Cert.baseCheck (cmp := cmp) (checkLeaf 0 cmp))
        content := fun cmp _ => checkContentUsing
          (checkGcdUsing (Cert.baseCheck (cmp := cmp) (checkLeaf 0 cmp))) }
  | n + 1 =>
      let lower := Cert.checkOps checkLeaf n
      { coprime := fun cmp _ => Cert.succCheck lower (cmp := cmp) (checkLeaf (n + 1) cmp)
        gcd := fun cmp _ => checkGcdUsing (Cert.succCheck lower (cmp := cmp) (checkLeaf (n + 1) cmp))
        content := fun cmp _ => checkContentUsing
          (checkGcdUsing (Cert.succCheck lower (cmp := cmp) (checkLeaf (n + 1) cmp))) }

/-- Replay rational scaling and primitive integer-model coprimality. -/
@[reducible] def checkRatLift {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    (f h : MvPoly n Rat cmp) (lift : RatLiftCert n cmp) : Bool :=
  decide (lift.scaleL ≠ 0) && decide (lift.scaleR ≠ 0) &&
    (f == C lift.scaleL * intModelToRat lift.left) &&
    (h == C lift.scaleR * intModelToRat lift.right) &&
    decide (scalarContent lift.left = 1) &&
    decide (scalarContent lift.right = 1) &&
    (Cert.checkOps (S := Int) (E := Cert.NoLeaves)
      (fun _ _ _ _ _ impossible => nomatch impossible) n).coprime
        cmp lift.left lift.right lift.cert

/-- Replay a rational leaf entirely with canonical `Int` and `Rat` operations. -/
@[reducible] def checkRatLeaf {n : Nat} {R : Type u} [Lean.Grind.CommRing R]
    [DecidableEq R] [BEq R] [LawfulBEq R]
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (f h : MvPoly n R cmp) (leaf : RatLeaf R n cmp) : Bool :=
  checkRatLift (mapCoeffs leaf.model.toRat f) (mapCoeffs leaf.model.toRat h) leaf.data

/-- Replay package for certificates with canonical rational leaves. -/
abbrev CheckOpsAt (R : Type u) [Lean.Grind.CommRing R] (n : Nat) :=
  Cert.CheckOpsAt R (RatLeaf R) n

@[reducible] def baseCheckCoprime {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R]
    {cmp : Mono 0 → Mono 0 → Ordering} [IsMonomialOrder cmp]
    (f h : MvPoly 0 R cmp) (cert : CoprimeCert 0 R cmp) : Bool :=
  Cert.baseCheck checkRatLeaf f h cert

@[reducible] def succCheckCoprime {n : Nat} {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] (lower : CheckOpsAt R n)
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering} [IsMonomialOrder cmp]
    (f h : MvPoly (n + 1) R cmp) (cert : CoprimeCert (n + 1) R cmp) : Bool :=
  Cert.succCheck lower checkRatLeaf f h cert

@[reducible] def checkOps {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] : (n : Nat) → CheckOpsAt R n
  | 0 =>
      { coprime := fun cmp _ => baseCheckCoprime (cmp := cmp)
        gcd := fun cmp _ => checkGcdUsing (baseCheckCoprime (cmp := cmp))
        content := fun cmp _ => checkContentUsing
          (checkGcdUsing (baseCheckCoprime (cmp := cmp))) }
  | n + 1 =>
      let lower := checkOps n
      { coprime := fun cmp _ => succCheckCoprime lower (cmp := cmp)
        gcd := fun cmp _ => checkGcdUsing (succCheckCoprime lower (cmp := cmp))
        content := fun cmp _ => checkContentUsing
          (checkGcdUsing (succCheckCoprime lower (cmp := cmp))) }

/-- The public replay package is the generic core at rational leaves. -/
theorem checkOps_eq {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] (n : Nat) :
    checkOps (R := R) n = Cert.checkOps (fun _ _ => checkRatLeaf) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [checkOps, Cert.checkOps, ih]

@[reducible] private def checkNoLeaf (n : Nat)
    (cmp : Mono n → Mono n → Ordering) [IsMonomialOrder cmp]
    (_ _ : MvPoly n Int cmp) (data : Cert.NoLeaves n cmp) : Bool :=
  nomatch data

/-- Replay recursive coprimality evidence. -/
@[reducible] def checkCoprime {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (f h : MvPoly n R cmp) (cert : CoprimeCert n R cmp) : Bool :=
  (checkOps (R := R) n).coprime cmp f h cert

/-- Replay a gcd candidate and its coprimality evidence. -/
@[reducible] def checkGcd {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (f h : MvPoly n R cmp) (cert : GcdCert n R cmp) : Bool :=
  (checkOps (R := R) n).gcd cmp f h cert

/-- Replay a coefficient gcd fold, starting from zero and requiring exactly
one checked gcd step per coefficient. -/
@[reducible] def checkContent {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (coeffs : List (MvPoly n R cmp)) (cert : ContentCert n R cmp) : Bool :=
  (checkOps (R := R) n).content cmp coeffs cert

/-- The semantic property witnessed by a coprimality certificate. -/
def CoprimeCofactors {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (f h : MvPoly n R cmp) : Prop :=
  ∀ d, d ∣ f → d ∣ h → ∃ u, d * u = 1

private theorem coprime_of_unit_left {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    {f h : MvPoly n R cmp} (hf : polyIsUnit f = true) :
    CoprimeCofactors f h := by
  intro d hdf _
  rcases hdf with ⟨q, hq⟩
  rcases (polyIsUnit_iff f).mp hf with ⟨v, hv⟩
  refine ⟨q * v, ?_⟩
  calc
    d * (q * v) = (q * d) * v := by grind
    _ = f * v := by rw [← hq]
    _ = 1 := hv

private theorem coprime_of_unit_right {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    {f h : MvPoly n R cmp} (hh : polyIsUnit h = true) :
    CoprimeCofactors f h := by
  intro d _ hdh
  rcases hdh with ⟨q, hq⟩
  rcases (polyIsUnit_iff h).mp hh with ⟨v, hv⟩
  refine ⟨q * v, ?_⟩
  calc
    d * (q * v) = (q * d) * v := by grind
    _ = h * v := by rw [← hq]
    _ = 1 := hv

private theorem coprime_of_bezout {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R]
    {f h u v : MvPoly n R cmp} (hbez : u * f + v * h = 1) :
    CoprimeCofactors f h := by
  intro d hdf hdh
  rcases hdf with ⟨a, ha⟩
  rcases hdh with ⟨b, hb⟩
  refine ⟨u * a + v * b, ?_⟩
  calc
    d * (u * a + v * b) = u * (a * d) + v * (b * d) := by grind
    _ = u * f + v * h := by rw [← ha, ← hb]
    _ = 1 := hbez

private theorem zero_arity_eq_C {R : Type u}
    {cmp : Mono 0 → Mono 0 → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (f : MvPoly 0 R cmp) : f = C (coeff Mono.zero f) := by
  apply eq_C_of_vars_eq_nil
  cases hvars : f.vars with
  | nil => rfl
  | cons i is => exact Fin.elim0 i

private theorem coprime_of_base {R : Type u}
    {cmp : Mono 0 → Mono 0 → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    {f h : MvPoly 0 R cmp} {u v : R}
    (hbez : u * coeff Mono.zero f + v * coeff Mono.zero h = 1) :
    CoprimeCofactors f h := by
  apply coprime_of_bezout
    (u := C u) (v := C v)
  rw [zero_arity_eq_C f, zero_arity_eq_C h]
  apply ext
  intro m
  have hm : m = Mono.zero := by
    apply Vector.ext
    intro i hi
    exact Fin.elim0 ⟨i, hi⟩
  subst m
  simp only [coeff_add, coeff_one, ite_true, coeff_C_mul, coeff_C]
  exact hbez

/-- Direct semantic payload of a checked gcd certificate. -/
def CheckedGcdResult {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (f h g cofL cofR : MvPoly n R cmp) : Prop :=
  f = g * cofL ∧ h = g * cofR ∧ polyNormalize g = g ∧
    CoprimeCofactors cofL cofR

/-- A checked result plus greatest-common-divisor maximality. -/
def IsGcdCertResult {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (f h g cofL cofR : MvPoly n R cmp) : Prop :=
  CheckedGcdResult f h g cofL cofR ∧
    ∀ d, d ∣ f → d ∣ h → d ∣ g

/-- Soundness package matching the mutually recursive certificate replay
operations at one arity. -/
structure Cert.SoundOpsAt (R : Type u) [Lean.Grind.CommRing R]
    [DecidableEq R] [BEq R] [LawfulBEq R] [Dvd R] [GcdOps R]
    (E : Cert.Leaves.{v}) (n : Nat) (ops : Cert.CheckOpsAt R E n) :
    Prop where
  coprime : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    ∀ {f h : MvPoly n R cmp} {cert : Cert.Coprime R E n cmp},
      ops.coprime cmp f h cert = true → CoprimeCofactors f h
  gcd : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    ∀ {f h : MvPoly n R cmp} {cert : Cert.Gcd R E n cmp},
      ops.gcd cmp f h cert = true →
        IsGcdCertResult f h cert.gcd cert.cofL cert.cofR
  content : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    ∀ {coeffs : List (MvPoly n R cmp)} {cert : Cert.Content R E n cmp},
      ops.content cmp coeffs cert = true →
        (∀ q ∈ coeffs, cert.value ∣ q) ∧
          ∀ d, (∀ q ∈ coeffs, d ∣ q) → d ∣ cert.value

private theorem checkedGcd_greatest {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    [CoprimeCancelLaws (MvPoly n R cmp)]
    {f h g cofL cofR : MvPoly n R cmp}
    (hc : CheckedGcdResult f h g cofL cofR) :
    ∀ d, d ∣ f → d ∣ h → d ∣ g := by
  intro d hdf hdh
  rcases hc with ⟨hf, hh, _, hcop⟩
  rw [hf] at hdf
  rw [hh] at hdh
  exact CoprimeCancelLaws.cancel_coprime g cofL cofR d hcop hdf hdh

private theorem checkGcdUsing_sound {n : Nat} {R : Type u}
    {E : Cert.Leaves.{v}} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    (check : MvPoly n R cmp → MvPoly n R cmp →
      Cert.Coprime R E n cmp → Bool)
    (sound : ∀ {f h cert}, check f h cert = true → CoprimeCofactors f h)
    {f h : MvPoly n R cmp} {cert : Cert.Gcd R E n cmp}
    (hc : checkGcdUsing check f h cert = true) :
    IsGcdCertResult f h cert.gcd cert.cofL cert.cofR := by
  simp only [checkGcdUsing, Bool.and_eq_true, beq_iff_eq] at hc
  let payload : CheckedGcdResult f h cert.gcd cert.cofL cert.cofR :=
    ⟨hc.1.1.1.symm, hc.1.1.2.symm, hc.1.2, sound hc.2⟩
  exact ⟨payload, checkedGcd_greatest payload⟩

private theorem checkContentSteps_sound {n : Nat} {R : Type u}
    {E : Cert.Leaves.{v}} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    (check : MvPoly n R cmp → MvPoly n R cmp →
      Cert.Gcd R E n cmp → Bool)
    (sound : ∀ {f h cert}, check f h cert = true →
      IsGcdCertResult f h cert.gcd cert.cofL cert.cofR)
    (value acc : MvPoly n R cmp) (coeffs : List (MvPoly n R cmp))
    (steps : List (Cert.Gcd R E n cmp))
    (hc : checkContentSteps check value acc coeffs steps = true) :
    (value ∣ acc ∧ ∀ q ∈ coeffs, value ∣ q) ∧
      ∀ d, d ∣ acc → (∀ q ∈ coeffs, d ∣ q) → d ∣ value := by
  induction coeffs generalizing acc steps with
  | nil =>
      cases steps with
      | nil =>
          simp only [checkContentSteps, beq_iff_eq] at hc
          subst value
          refine ⟨⟨?_, by simp⟩, ?_⟩
          · exact ⟨1, (MvPoly.one_mul acc).symm⟩
          · intro d hd _
            exact hd
      | cons step steps => simp [checkContentSteps] at hc
  | cons q qs ih =>
      cases steps with
      | nil => simp [checkContentSteps] at hc
      | cons step steps =>
          simp only [checkContentSteps, Bool.and_eq_true] at hc
          have hstep := sound hc.1
          have htail := ih step.gcd steps hc.2
          have hstepAcc : step.gcd ∣ acc :=
            ⟨step.cofL, hstep.1.1.trans (MvPoly.mul_comm _ _)⟩
          have hstepQ : step.gcd ∣ q :=
            ⟨step.cofR, hstep.1.2.1.trans (MvPoly.mul_comm _ _)⟩
          refine ⟨⟨Hex.dvdTrans htail.1.1 hstepAcc, ?_⟩, ?_⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact Hex.dvdTrans htail.1.1 hstepQ
            · exact htail.1.2 x hx
          · intro d hdacc hdcoeff
            apply htail.2 d
            · exact hstep.2 d hdacc (hdcoeff q (List.mem_cons_self ..))
            · intro x hx
              exact hdcoeff x (List.mem_cons_of_mem q hx)

private theorem checkContentUsing_sound {n : Nat} {R : Type u}
    {E : Cert.Leaves.{v}} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    (check : MvPoly n R cmp → MvPoly n R cmp →
      Cert.Gcd R E n cmp → Bool)
    (sound : ∀ {f h cert}, check f h cert = true →
      IsGcdCertResult f h cert.gcd cert.cofL cert.cofR)
    {coeffs : List (MvPoly n R cmp)} {cert : Cert.Content R E n cmp}
    (hc : checkContentUsing check coeffs cert = true) :
    (∀ q ∈ coeffs, cert.value ∣ q) ∧
      ∀ d, (∀ q ∈ coeffs, d ∣ q) → d ∣ cert.value := by
  have hs := checkContentSteps_sound check sound cert.value 0 coeffs cert.steps hc
  refine ⟨hs.1.2, ?_⟩
  intro d hd
  apply hs.2 d
  · apply (GcdDomainLaws.dvd_iff d 0).mpr
    exact ⟨0, (MvPoly.mul_zero d).symm⟩
  · exact hd

private theorem eq_constIn_of_mul_eq_constIn {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    {cmp' : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R]
    [IsMonomialOrder cmp] [IsMonomialOrder cmp']
    (i : Fin (n + 1)) {d q : MvPoly (n + 1) R cmp}
    {r : MvPoly n R cmp'} (hr : r ≠ 0)
    (hprod : q * d = constIn i cmp' r) :
    ∃ c : MvPoly n R cmp', d = constIn i cmp' c := by
  let dv := toUnivariate i cmp' d
  let qv := toUnivariate i cmp' q
  have hview : qv * dv = DensePoly.C r := by
    calc
      qv * dv = toUnivariate i cmp' (q * d) :=
        (toUnivariate_mul i q d).symm
      _ = DensePoly.C r := by rw [hprod, toUnivariate_constIn]
  have hCr : DensePoly.C r ≠ (0 : DensePoly (MvPoly n R cmp')) := by
    intro hzero
    have hsize := congrArg DensePoly.size hzero
    rw [DensePoly.size_C_of_ne_zero hr, DensePoly.size_zero] at hsize
    omega
  have hmul : qv * dv ≠ 0 := by rw [hview]; exact hCr
  have hqv : qv ≠ 0 := by
    intro hzero
    apply hmul
    rw [hzero, DensePoly.zero_mul]
  have hdv : dv ≠ 0 := by
    intro hzero
    apply hmul
    rw [DensePoly.mul_comm_poly qv, hzero, DensePoly.zero_mul]
  have hqpos : 0 < qv.size := Nat.pos_of_ne_zero fun hzero =>
    hqv ((DensePoly.size_eq_zero_iff qv).mp hzero)
  have hdpos : 0 < dv.size := Nat.pos_of_ne_zero fun hzero =>
    hdv ((DensePoly.size_eq_zero_iff dv).mp hzero)
  have htop : qv.leadingCoeff * dv.leadingCoeff ≠ 0 := by
    intro hzero
    rcases GcdDomainLaws.no_zero_div qv.leadingCoeff dv.leadingCoeff hzero with
      hq | hd
    · exact DensePoly.leadingCoeff_ne_zero_of_pos_size qv hqpos hq
    · exact DensePoly.leadingCoeff_ne_zero_of_pos_size dv hdpos hd
  have hsize := DensePoly.size_mul_of_top_ne qv dv hqpos hdpos htop
  have hdle : dv.size ≤ 1 := by
    rw [hview, DensePoly.size_C_of_ne_zero hr] at hsize
    omega
  let c := dv.coeff 0
  have hdense : dv = DensePoly.C c := by
    apply DensePoly.ext_coeff
    intro k
    rw [DensePoly.coeff_C]
    by_cases hk : k = 0
    · rw [ite_eq_left hk, hk]
    · rw [ite_eq_right hk]
      exact DensePoly.coeff_eq_zero_of_size_le dv (by omega)
  refine ⟨c, ?_⟩
  calc
    d = ofUnivariate (cmp := cmp) i cmp' dv :=
      (ofUnivariate_toUnivariate i d).symm
    _ = ofUnivariate (cmp := cmp) i cmp' (DensePoly.C c) := by rw [hdense]
    _ = constIn i cmp' c := rfl

private theorem coeff_dvd_of_constIn_dvd {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    {cmp' : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R]
    [IsMonomialOrder cmp] [IsMonomialOrder cmp']
    (i : Fin (n + 1)) {c : MvPoly n R cmp'}
    {d f : MvPoly (n + 1) R cmp}
    (hd : d = constIn i cmp' c) (hdf : d ∣ f) (k : Nat) :
    c ∣ (toUnivariate i cmp' f).coeff k := by
  rcases hdf with ⟨q, hq⟩
  refine ⟨(toUnivariate i cmp' q).coeff k, ?_⟩
  calc
    (toUnivariate i cmp' f).coeff k =
        (toUnivariate i cmp' (q * d)).coeff k := by rw [hq]
    _ = (toUnivariate i cmp' (constIn i cmp' c * q)).coeff k := by
      rw [hd, MvPoly.mul_comm q]
    _ = c * (toUnivariate i cmp' q).coeff k := coeff_constIn_mul i c q k
    _ = (toUnivariate i cmp' q).coeff k * c := MvPoly.mul_comm _ _

private theorem constIn_of_image_unit {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    {cmp' : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R]
    [IsMonomialOrder cmp] [IsMonomialOrder cmp']
    (P : ZMod64.Prime)
    (φ : @CoeffHom R P.m _ _ _ _ P.bounds)
    (a : Fin n → @ZMod64 P.m P.bounds) (i : Fin (n + 1))
    {d q f : MvPoly (n + 1) R cmp}
    (hf : f = q * d)
    (hdegree : (imageAt P φ a i cmp' f).degree? =
      (toUnivariate i cmp' f).degree?)
    (himage : imageAt P φ a i cmp' f ≠ 0)
    (hunit : ∃ w, imageAt P φ a i cmp' d * w = 1) :
    ∃ c : MvPoly n R cmp', d = constIn i cmp' c := by
  letI : ZMod64.Bounds P.m := P.bounds
  letI : ZMod64.PrimeModulus P.m := ZMod64.primeModulusOfPrime P.prime
  let dImage := imageAt P φ a i cmp' d
  let qImage := imageAt P φ a i cmp' q
  let fImage := imageAt P φ a i cmp' f
  let dView := toUnivariate i cmp' d
  let qView := toUnivariate i cmp' q
  let fView := toUnivariate i cmp' f
  have hImageProd : fImage = qImage * dImage := by
    dsimp only [fImage, qImage, dImage]
    rw [hf, imageAt_mul]
  have hViewProd : fView = qView * dView := by
    dsimp only [fView, qView, dView]
    rw [hf, toUnivariate_mul]
  rcases hunit with ⟨w, hdw⟩
  have hdUnit : GcdOps.isUnit dImage = true :=
    (LawfulGcdOps.isUnit_iff dImage).mpr ⟨w, hdw⟩
  have hdImageSize : dImage.size = 1 := by
    change decide (dImage.size = 1) = true at hdUnit
    exact of_decide_eq_true hdUnit
  have hdImage : dImage ≠ 0 := by
    intro hz
    simp [hz] at hdImageSize
  have hqImage : qImage ≠ 0 := by
    intro hz
    apply himage
    change fImage = 0
    rw [hImageProd, hz]
    exact DensePoly.zero_mul dImage
  have hqImagePos : 0 < qImage.size :=
    FpPoly.size_pos_of_ne_zero hqImage
  have hqViewPos : 0 < qView.size := by
    have hle := imageAt_size_le P φ a i cmp' q
    change qImage.size ≤ qView.size at hle
    omega
  have hdViewPos : 0 < dView.size := by
    have hle := imageAt_size_le P φ a i cmp' d
    change dImage.size ≤ dView.size at hle
    omega
  have htop : qView.leadingCoeff * dView.leadingCoeff ≠ 0 := by
    intro hz
    rcases GcdDomainLaws.no_zero_div qView.leadingCoeff dView.leadingCoeff hz with
      hq | hd
    · exact DensePoly.leadingCoeff_ne_zero_of_pos_size qView hqViewPos hq
    · exact DensePoly.leadingCoeff_ne_zero_of_pos_size dView hdViewPos hd
  have hViewSize :=
    DensePoly.size_mul_of_top_ne qView dView hqViewPos hdViewPos htop
  have hImageSize :=
    FpPoly.size_mul_eq_add_sub_one qImage dImage hqImage hdImage
  have hfImagePos : 0 < fImage.size := FpPoly.size_pos_of_ne_zero himage
  have hfViewPos : 0 < fView.size := by
    rw [hViewProd, hViewSize]
    omega
  have hsameSize : fImage.size = fView.size := by
    change fImage.degree? = fView.degree? at hdegree
    rw [DensePoly.degree?_eq_some_of_pos_size fImage hfImagePos,
      DensePoly.degree?_eq_some_of_pos_size fView hfViewPos] at hdegree
    simp only [Option.some.injEq] at hdegree
    omega
  have hqSizeLe := imageAt_size_le P φ a i cmp' q
  change qImage.size ≤ qView.size at hqSizeLe
  have hdViewSize : dView.size = 1 := by
    rw [hImageProd, hImageSize, hdImageSize] at hsameSize
    rw [hViewProd, hViewSize] at hsameSize
    omega
  let c := dView.coeff 0
  have hdense : dView = DensePoly.C c := by
    apply DensePoly.ext_coeff
    intro k
    rw [DensePoly.coeff_C]
    by_cases hk : k = 0
    · rw [ite_eq_left hk, hk]
    · rw [ite_eq_right hk]
      exact DensePoly.coeff_eq_zero_of_size_le dView (by omega)
  refine ⟨c, ?_⟩
  calc
    d = ofUnivariate (cmp := cmp) i cmp' dView :=
      (ofUnivariate_toUnivariate i d).symm
    _ = ofUnivariate (cmp := cmp) i cmp' (DensePoly.C c) := by rw [hdense]
    _ = constIn i cmp' c := rfl

private theorem unit_of_constIn_common {n : Nat} {R : Type u}
    {E : Cert.Leaves.{v}}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    {cmp' : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R]
    [IsMonomialOrder cmp] [IsMonomialOrder cmp']
    (i : Fin (n + 1)) {d f h : MvPoly (n + 1) R cmp}
    {c : MvPoly n R cmp'} {left right : Cert.Content R E n cmp'}
    (hd : d = constIn i cmp' c) (hdf : d ∣ f) (hdh : d ∣ h)
    (hleft :
      (∀ q ∈ (toUnivariate i cmp' f).toArray.toList, left.value ∣ q) ∧
        ∀ e, (∀ q ∈ (toUnivariate i cmp' f).toArray.toList, e ∣ q) →
          e ∣ left.value)
    (hright :
      (∀ q ∈ (toUnivariate i cmp' h).toArray.toList, right.value ∣ q) ∧
        ∀ e, (∀ q ∈ (toUnivariate i cmp' h).toArray.toList, e ∣ q) →
          e ∣ right.value)
    (hrest : CoprimeCofactors left.value right.value) :
    ∃ w, d * w = 1 := by
  have hcLeft : c ∣ left.value := by
    apply hleft.2 c
    intro x hx
    rw [List.mem_iff_getElem] at hx
    rcases hx with ⟨k, hk, hx⟩
    have hk' : k < (toUnivariate i cmp' f).toArray.size := by simpa using hk
    rw [← hx, Array.getElem_toList,
      Array.getElem_eq_getD (0 : MvPoly n R cmp')]
    change c ∣ (toUnivariate i cmp' f).coeff k
    exact coeff_dvd_of_constIn_dvd i hd hdf k
  have hcRight : c ∣ right.value := by
    apply hright.2 c
    intro x hx
    rw [List.mem_iff_getElem] at hx
    rcases hx with ⟨k, hk, hx⟩
    have hk' : k < (toUnivariate i cmp' h).toArray.size := by simpa using hk
    rw [← hx, Array.getElem_toList,
      Array.getElem_eq_getD (0 : MvPoly n R cmp')]
    change c ∣ (toUnivariate i cmp' h).coeff k
    exact coeff_dvd_of_constIn_dvd i hd hdh k
  rcases hrest c hcLeft hcRight with ⟨w, hw⟩
  refine ⟨constIn i cmp' w, ?_⟩
  rw [hd, ← constIn_mul, hw, constIn_one]

private theorem coprime_of_split {n : Nat} {R : Type u}
    {E : Cert.Leaves.{v}}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    {cmp' : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R]
    [IsMonomialOrder cmp] [IsMonomialOrder cmp']
    (P : ZMod64.Prime)
    (φ : @CoeffHom R P.m _ _ _ _ P.bounds)
    (a : Fin n → @ZMod64 P.m P.bounds) (i : Fin (n + 1))
    {f h : MvPoly (n + 1) R cmp} {α β : @FpPoly P.m P.bounds}
    {left right : Cert.Content R E n cmp'}
    (hfDegree : (imageAt P φ a i cmp' f).degree? =
      (toUnivariate i cmp' f).degree?)
    (hhDegree : (imageAt P φ a i cmp' h).degree? =
      (toUnivariate i cmp' h).degree?)
    (hbez : α * imageAt P φ a i cmp' f +
      β * imageAt P φ a i cmp' h = 1)
    (hleft :
      (∀ q ∈ (toUnivariate i cmp' f).toArray.toList, left.value ∣ q) ∧
        ∀ d, (∀ q ∈ (toUnivariate i cmp' f).toArray.toList, d ∣ q) →
          d ∣ left.value)
    (hright :
      (∀ q ∈ (toUnivariate i cmp' h).toArray.toList, right.value ∣ q) ∧
        ∀ d, (∀ q ∈ (toUnivariate i cmp' h).toArray.toList, d ∣ q) →
          d ∣ right.value)
    (hrest : CoprimeCofactors left.value right.value) :
    CoprimeCofactors f h := by
  letI : ZMod64.Bounds P.m := P.bounds
  letI : ZMod64.PrimeModulus P.m := ZMod64.primeModulusOfPrime P.prime
  intro d hdf hdh
  rcases hdf with ⟨qf, hqf⟩
  rcases hdh with ⟨qh, hqh⟩
  let dImage := imageAt P φ a i cmp' d
  let qfImage := imageAt P φ a i cmp' qf
  let qhImage := imageAt P φ a i cmp' qh
  let fImage := imageAt P φ a i cmp' f
  let hImage := imageAt P φ a i cmp' h
  have hfImage : fImage = qfImage * dImage := by
    dsimp only [fImage, qfImage, dImage]
    rw [hqf, imageAt_mul]
  have hhImage : hImage = qhImage * dImage := by
    dsimp only [hImage, qhImage, dImage]
    rw [hqh, imageAt_mul]
  have rotate (x y z : @FpPoly P.m P.bounds) : x * (y * z) = y * (z * x) := by
    calc
      x * (y * z) = (x * y) * z := (DensePoly.mul_assoc_poly x y z).symm
      _ = (y * x) * z := congrArg (fun t => t * z) (DensePoly.mul_comm_poly x y)
      _ = y * (x * z) := DensePoly.mul_assoc_poly y x z
      _ = y * (z * x) := congrArg (fun t => y * t) (DensePoly.mul_comm_poly x z)
  have hdUnit : ∃ w, dImage * w = 1 := by
    refine ⟨α * qfImage + β * qhImage, ?_⟩
    calc
      dImage * (α * qfImage + β * qhImage) =
          dImage * (α * qfImage) + dImage * (β * qhImage) :=
        DensePoly.mul_add_right_poly _ _ _
      _ = α * (qfImage * dImage) + β * (qhImage * dImage) := by
        rw [rotate dImage α qfImage, rotate dImage β qhImage]
      _ = α * fImage + β * hImage := by rw [hfImage, hhImage]
      _ = 1 := hbez
  have hone : (1 : @FpPoly P.m P.bounds) ≠ 0 := LawfulGcdOps.one_ne_zero
  by_cases hfZero : fImage = 0
  · have hhNonzero : hImage ≠ 0 := by
      intro hhZero
      apply hone
      calc
        1 = α * fImage + β * hImage := hbez.symm
        _ = 0 := by
          rw [hfZero, hhZero, FpPoly.mul_zero, FpPoly.mul_zero]
          exact DensePoly.zero_add_semiring 0
    have hdEq := constIn_of_image_unit P φ a i hqh hhDegree hhNonzero hdUnit
    rcases hdEq with ⟨c, hd⟩
    exact unit_of_constIn_common i hd ⟨qf, hqf⟩ ⟨qh, hqh⟩
      hleft hright hrest
  · have hdEq := constIn_of_image_unit P φ a i hqf hfDegree hfZero hdUnit
    rcases hdEq with ⟨c, hd⟩
    exact unit_of_constIn_common i hd ⟨qf, hqf⟩ ⟨qh, hqh⟩
      hleft hright hrest

private theorem coprime_of_splitBezout {n : Nat} {R : Type u}
    {E : Cert.Leaves.{v}}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    {cmp' : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R]
    [IsMonomialOrder cmp] [IsMonomialOrder cmp']
    (i : Fin (n + 1)) {f h u v : MvPoly (n + 1) R cmp} {r : MvPoly n R cmp'}
    {left right : Cert.Content R E n cmp'}
    (hr : r ≠ 0) (hbez : u * f + v * h = constIn (cmp := cmp) i cmp' r)
    (hleft :
      (∀ q ∈ (toUnivariate i cmp' f).toArray.toList, left.value ∣ q) ∧
        ∀ d, (∀ q ∈ (toUnivariate i cmp' f).toArray.toList, d ∣ q) →
          d ∣ left.value)
    (hright :
      (∀ q ∈ (toUnivariate i cmp' h).toArray.toList, right.value ∣ q) ∧
        ∀ d, (∀ q ∈ (toUnivariate i cmp' h).toArray.toList, d ∣ q) →
          d ∣ right.value)
    (hrest : CoprimeCofactors left.value right.value) :
    CoprimeCofactors f h := by
  intro d hdf hdh
  rcases hdf with ⟨qf, hqf⟩
  rcases hdh with ⟨qh, hqh⟩
  have hdConst : d ∣ constIn (cmp := cmp) i cmp' r := by
    refine ⟨u * qf + v * qh, ?_⟩
    calc
      constIn (cmp := cmp) i cmp' r = u * f + v * h := hbez.symm
      _ = u * (qf * d) + v * (qh * d) := by rw [hqf, hqh]
      _ = (u * qf + v * qh) * d := by grind
  rcases hdConst with ⟨q, hq⟩
  have hdEq : ∃ c : MvPoly n R cmp', d = constIn i cmp' c :=
    eq_constIn_of_mul_eq_constIn i hr hq.symm
  rcases hdEq with ⟨c, hd⟩
  exact unit_of_constIn_common i hd ⟨qf, hqf⟩ ⟨qh, hqh⟩
    hleft hright hrest

private theorem baseCheck_sound {R : Type u} {E : Cert.Leaves.{v}}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R]
    {cmp : Mono 0 → Mono 0 → Ordering} [IsMonomialOrder cmp]
    (checkLeaf : MvPoly 0 R cmp → MvPoly 0 R cmp → E 0 cmp → Bool)
    (leafSound : ∀ {f h data}, checkLeaf f h data = true →
      CoprimeCofactors f h)
    {f h : MvPoly 0 R cmp} {cert : Cert.Coprime R E 0 cmp}
    (hc : Cert.baseCheck checkLeaf f h cert = true) :
    CoprimeCofactors f h := by
  cases cert with
  | unit =>
      simp only [Cert.baseCheck, Bool.or_eq_true] at hc
      rcases hc with hf | hh
      · exact coprime_of_unit_left hf
      · exact coprime_of_unit_right hh
  | base u v =>
      simp only [Cert.baseCheck, beq_iff_eq] at hc
      exact coprime_of_base hc
  | bezout u v =>
      simp only [Cert.baseCheck, beq_iff_eq] at hc
      exact coprime_of_bezout hc
  | leaf data =>
      exact leafSound hc

private theorem succCheck_sound {n : Nat} {R : Type u} {E : Cert.Leaves.{v}}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R]
    (lower : Cert.CheckOpsAt R E n)
    (lowerSound : Cert.SoundOpsAt R E n lower)
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    (checkLeaf : MvPoly (n + 1) R cmp → MvPoly (n + 1) R cmp →
      E (n + 1) cmp → Bool)
    (leafSound : ∀ {f h data}, checkLeaf f h data = true →
      CoprimeCofactors f h)
    {f h : MvPoly (n + 1) R cmp}
    {cert : Cert.Coprime R E (n + 1) cmp}
    (hc : Cert.succCheck lower checkLeaf f h cert = true) :
    CoprimeCofactors f h := by
  cases cert with
  | unit =>
      simp only [Cert.succCheck, Bool.or_eq_true] at hc
      rcases hc with hf | hh
      · exact coprime_of_unit_left hf
      · exact coprime_of_unit_right hh
  | bezout u v =>
      simp only [Cert.succCheck, beq_iff_eq] at hc
      exact coprime_of_bezout hc
  | leaf data =>
      exact leafSound hc
  | split i cmp' P φ a α β left right rest =>
      letI : ZMod64.Bounds P.m := P.bounds
      letI : ZMod64.PrimeModulus P.m := ZMod64.primeModulusOfPrime P.prime
      change
        (decide ((imageAt P φ a i cmp' f).degree? =
              (toUnivariate i cmp' f).degree?) &&
          decide ((imageAt P φ a i cmp' h).degree? =
              (toUnivariate i cmp' h).degree?) &&
          (α * imageAt P φ a i cmp' f + β * imageAt P φ a i cmp' h == 1) &&
          lower.content cmp' (toUnivariate i cmp' f).toArray.toList left &&
          lower.content cmp' (toUnivariate i cmp' h).toArray.toList right &&
          lower.coprime cmp' left.value right.value rest) = true at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      rcases hc with ⟨⟨⟨⟨⟨hfDegree, hhDegree⟩, hbez⟩, hleft⟩,
        hright⟩, hrest⟩
      exact coprime_of_split P φ a i hfDegree hhDegree hbez
        (lowerSound.content cmp' hleft) (lowerSound.content cmp' hright)
        (lowerSound.coprime cmp' hrest)
  | splitBezout i cmp' u v r left right rest =>
      change
        (decide (r ≠ 0) &&
          (u * f + v * h == constIn i cmp' r) &&
          lower.content cmp' (toUnivariate i cmp' f).toArray.toList left &&
          lower.content cmp' (toUnivariate i cmp' h).toArray.toList right &&
          lower.coprime cmp' left.value right.value rest) = true at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      rcases hc with ⟨⟨⟨⟨hr, hbez⟩, hleft⟩, hright⟩, hrest⟩
      exact coprime_of_splitBezout i hr hbez
        (lowerSound.content cmp' hleft) (lowerSound.content cmp' hright)
        (lowerSound.coprime cmp' hrest)

private theorem certCheckOps_sound {R : Type u} {E : Cert.Leaves.{v}}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R]
    (checkLeaf : (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
      [IsMonomialOrder cmp] → MvPoly n R cmp → MvPoly n R cmp →
        E n cmp → Bool)
    (leafSound : (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
      [IsMonomialOrder cmp] →
      ∀ {f h : MvPoly n R cmp} {data : E n cmp},
        checkLeaf n cmp f h data = true → CoprimeCofactors f h) :
    (n : Nat) → Cert.SoundOpsAt R E n (Cert.checkOps checkLeaf n) := by
  intro n
  induction n with
  | zero =>
      refine { coprime := ?_, gcd := ?_, content := ?_ }
      · intro cmp _ f h cert hc
        exact baseCheck_sound (checkLeaf 0 cmp) (leafSound 0 cmp) hc
      · intro cmp _ f h cert hc
        exact checkGcdUsing_sound (Cert.baseCheck (checkLeaf 0 cmp))
          (fun hc => baseCheck_sound (checkLeaf 0 cmp) (leafSound 0 cmp) hc) hc
      · intro cmp _ coeffs cert hc
        exact checkContentUsing_sound
          (checkGcdUsing (Cert.baseCheck (checkLeaf 0 cmp)))
          (fun hc => checkGcdUsing_sound (Cert.baseCheck (checkLeaf 0 cmp))
            (fun hc => baseCheck_sound (checkLeaf 0 cmp) (leafSound 0 cmp) hc) hc)
          hc
  | succ n ih =>
      let lower := Cert.checkOps checkLeaf n
      have lowerSound : Cert.SoundOpsAt R E n lower := ih
      refine { coprime := ?_, gcd := ?_, content := ?_ }
      · intro cmp _ f h cert hc
        exact succCheck_sound lower lowerSound (checkLeaf (n + 1) cmp)
          (leafSound (n + 1) cmp) hc
      · intro cmp _ f h cert hc
        exact checkGcdUsing_sound
          (Cert.succCheck lower (checkLeaf (n + 1) cmp))
          (fun hc => succCheck_sound lower lowerSound (checkLeaf (n + 1) cmp)
            (leafSound (n + 1) cmp) hc) hc
      · intro cmp _ coeffs cert hc
        exact checkContentUsing_sound
          (checkGcdUsing (Cert.succCheck lower (checkLeaf (n + 1) cmp)))
          (fun hc => checkGcdUsing_sound
            (Cert.succCheck lower (checkLeaf (n + 1) cmp))
            (fun hc => succCheck_sound lower lowerSound (checkLeaf (n + 1) cmp)
              (leafSound (n + 1) cmp) hc) hc)
          hc

private theorem checkNoLeaves_sound {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    {f h : MvPoly n Int cmp} {cert : Cert.Coprime Int Cert.NoLeaves n cmp}
    (hc : (Cert.checkOps checkNoLeaf n).coprime cmp f h cert = true) :
    CoprimeCofactors f h := by
  have hs := certCheckOps_sound checkNoLeaf
    (fun _ _ _ _ _ data _ => nomatch data) n
  exact hs.coprime cmp hc

private theorem coprime_intModelToRat {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    {f h : MvPoly n Int cmp} (hc : CoprimeCofactors f h) :
    CoprimeCofactors (intModelToRat f) (intModelToRat h) := by
  have hfrac : CoprimeOverFraction f h :=
    coprimeOverFraction_of_coprime hc
  intro d hdf hdh
  have hdf' : ratPolyToFraction d ∣ fractionMap f := by
    rcases hdf with ⟨q, hq⟩
    refine ⟨ratPolyToFraction q, ?_⟩
    calc
      fractionMap f = ratPolyToFraction (intModelToRat f) :=
        (ratPolyToFraction_intModelToRat f).symm
      _ = ratPolyToFraction (q * d) := by rw [hq]
      _ = ratPolyToFraction q * ratPolyToFraction d :=
        ratPolyToFraction_mul q d
  have hdh' : ratPolyToFraction d ∣ fractionMap h := by
    rcases hdh with ⟨q, hq⟩
    refine ⟨ratPolyToFraction q, ?_⟩
    calc
      fractionMap h = ratPolyToFraction (intModelToRat h) :=
        (ratPolyToFraction_intModelToRat h).symm
      _ = ratPolyToFraction (q * d) := by rw [hq]
      _ = ratPolyToFraction q * ratPolyToFraction d :=
        ratPolyToFraction_mul q d
  rcases hfrac (ratPolyToFraction d) hdf' hdh' with ⟨u, hu⟩
  refine ⟨fractionPolyToRat u, ?_⟩
  calc
    d * fractionPolyToRat u =
        fractionPolyToRat (ratPolyToFraction d) * fractionPolyToRat u := by
      rw [fractionPolyToRat_ratPolyToFraction]
    _ = fractionPolyToRat (ratPolyToFraction d * u) :=
      (fractionPolyToRat_mul _ _).symm
    _ = fractionPolyToRat 1 := by rw [hu]
    _ = 1 := fractionPolyToRat_one

private theorem rat_C_mul_C {n : Nat}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (a b : Rat) :
    (C a : MvPoly n Rat cmp) * C b = C (a * b) := by
  change monomial Mono.zero a * monomial Mono.zero b = monomial Mono.zero (a * b)
  rw [monomial_mul_monomial, Mono.zero_mul]

private theorem dvd_of_rat_scale_dvd {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    {s : Rat} (hs : s ≠ 0) {p f d : MvPoly n Rat cmp}
    (hf : f = C s * p) (hdf : d ∣ f) : d ∣ p := by
  rcases hdf with ⟨q, hq⟩
  refine ⟨C s⁻¹ * q, ?_⟩
  calc
    p = 1 * p := (MvPoly.one_mul p).symm
    _ = C (s⁻¹ * s) * p := by
      rw [Rat.inv_mul_cancel s hs]
      change C 1 * p = C 1 * p
      rfl
    _ = (C s⁻¹ * C s) * p := by rw [rat_C_mul_C]
    _ = C s⁻¹ * (C s * p) := MvPoly.mul_assoc _ _ _
    _ = C s⁻¹ * f := by rw [← hf]
    _ = C s⁻¹ * (q * d) := by rw [hq]
    _ = (C s⁻¹ * q) * d := (MvPoly.mul_assoc _ _ _).symm

/-- Rational-lift replay proves coprimality of the rational inputs. -/
theorem checkRatLift_sound {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    {f h : MvPoly n Rat cmp} {lift : RatLiftCert n cmp}
    (hc : checkRatLift f h lift = true) : CoprimeCofactors f h := by
  change
    (decide (lift.scaleL ≠ 0) && decide (lift.scaleR ≠ 0) &&
      (f == C lift.scaleL * intModelToRat lift.left) &&
      (h == C lift.scaleR * intModelToRat lift.right) &&
      decide (scalarContent lift.left = 1) &&
      decide (scalarContent lift.right = 1) &&
      (Cert.checkOps (S := Int) (E := Cert.NoLeaves)
        (fun _ _ _ _ _ impossible => nomatch impossible) n).coprime
          cmp lift.left lift.right lift.cert) = true at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨⟨hscaleL, hscaleR⟩, hf⟩, hh⟩, _⟩, _⟩, hcert⟩
  have hInt : CoprimeCofactors lift.left lift.right :=
    checkNoLeaves_sound hcert
  have hRat := coprime_intModelToRat hInt
  intro d hdf hdh
  apply hRat d
  · exact dvd_of_rat_scale_dvd hscaleL hf hdf
  · exact dvd_of_rat_scale_dvd hscaleR hh hdh

private theorem RatModel.from_zero {R : Type u} [Lean.Grind.CommRing R]
    (model : RatModel R) : model.fromRat 0 = 0 := by
  have h := model.left_inv (0 : R)
  rw [model.map_zero] at h
  exact h

private theorem RatModel.from_one {R : Type u} [Lean.Grind.CommRing R]
    (model : RatModel R) : model.fromRat 1 = 1 := by
  have h := model.left_inv (1 : R)
  rw [model.map_one] at h
  exact h

private theorem RatModel.from_add {R : Type u} [Lean.Grind.CommRing R]
    (model : RatModel R) (x y : Rat) :
    model.fromRat (x + y) = model.fromRat x + model.fromRat y := by
  apply model.injective
  rw [model.right_inv, model.map_add, model.right_inv, model.right_inv]

private theorem RatModel.from_mul {R : Type u} [Lean.Grind.CommRing R]
    (model : RatModel R) (x y : Rat) :
    model.fromRat (x * y) = model.fromRat x * model.fromRat y := by
  apply model.injective
  rw [model.right_inv, model.map_mul, model.right_inv, model.right_inv]

private theorem RatModel.poly_left_inv {n : Nat} {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (model : RatModel R) (p : MvPoly n R cmp) :
    mapCoeffs model.fromRat (mapCoeffs model.toRat p) = p := by
  apply ext
  intro m
  rw [coeff_mapCoeffs model.from_zero,
    coeff_mapCoeffs model.map_zero, model.left_inv]

private theorem checkRatLeaf_sound {n : Nat} {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R]
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    {f h : MvPoly n R cmp} {leaf : RatLeaf R n cmp}
    (hc : checkRatLeaf f h leaf = true) : CoprimeCofactors f h := by
  have hRat : CoprimeCofactors
      (mapCoeffs leaf.model.toRat f) (mapCoeffs leaf.model.toRat h) :=
    checkRatLift_sound hc
  intro d hdf hdh
  have hdfRat : mapCoeffs leaf.model.toRat d ∣
      mapCoeffs leaf.model.toRat f := by
    rcases hdf with ⟨q, hq⟩
    refine ⟨mapCoeffs leaf.model.toRat q, ?_⟩
    calc
      mapCoeffs leaf.model.toRat f = mapCoeffs leaf.model.toRat (q * d) := by
        rw [hq]
      _ = mapCoeffs leaf.model.toRat q *
          mapCoeffs leaf.model.toRat d :=
        mapCoeffs_mul leaf.model.map_zero leaf.model.map_add
          leaf.model.map_mul q d
  have hdhRat : mapCoeffs leaf.model.toRat d ∣
      mapCoeffs leaf.model.toRat h := by
    rcases hdh with ⟨q, hq⟩
    refine ⟨mapCoeffs leaf.model.toRat q, ?_⟩
    calc
      mapCoeffs leaf.model.toRat h = mapCoeffs leaf.model.toRat (q * d) := by
        rw [hq]
      _ = mapCoeffs leaf.model.toRat q *
          mapCoeffs leaf.model.toRat d :=
        mapCoeffs_mul leaf.model.map_zero leaf.model.map_add
          leaf.model.map_mul q d
  rcases hRat (mapCoeffs leaf.model.toRat d) hdfRat hdhRat with ⟨u, hu⟩
  refine ⟨mapCoeffs leaf.model.fromRat u, ?_⟩
  have hback := congrArg (mapCoeffs leaf.model.fromRat) hu
  rw [mapCoeffs_mul leaf.model.from_zero leaf.model.from_add
      leaf.model.from_mul,
    mapCoeffs_one leaf.model.from_zero leaf.model.from_one,
    leaf.model.poly_left_inv] at hback
  exact hback

private theorem ratLeaves_sound {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] :
    (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
      [IsMonomialOrder cmp] →
      ∀ {f h : MvPoly n R cmp} {leaf : RatLeaf R n cmp},
        checkRatLeaf f h leaf = true → CoprimeCofactors f h := by
  intro _ _ _ _ _ _ hc
  exact checkRatLeaf_sound hc

/-- Simultaneous checker soundness: recursive coprimality replay. -/
theorem checkCoprime_sound {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    {f h : MvPoly n R cmp} {cert : CoprimeCert n R cmp}
    (hc : checkCoprime f h cert = true) : CoprimeCofactors f h := by
  have hs := certCheckOps_sound
    (fun n cmp _ => checkRatLeaf (n := n) (cmp := cmp))
    (ratLeaves_sound (R := R)) n
  apply hs.coprime cmp
  rw [← checkOps_eq (R := R) n]
  exact hc

/-- Simultaneous checker soundness: a content fold is both a common divisor
and greatest among common divisors. -/
theorem checkContent_sound {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    {coeffs : List (MvPoly n R cmp)} {cert : ContentCert n R cmp}
    (hc : checkContent coeffs cert = true) :
    (∀ q ∈ coeffs, cert.value ∣ q) ∧
      ∀ d, (∀ q ∈ coeffs, d ∣ q) → d ∣ cert.value := by
  have hs := certCheckOps_sound
    (fun n cmp _ => checkRatLeaf (n := n) (cmp := cmp))
    (ratLeaves_sound (R := R)) n
  apply hs.content cmp
  rw [← checkOps_eq (R := R) n]
  exact hc

/-- Simultaneous checker soundness: exact cofactors, normalization, and
coprimality. -/
theorem checkGcd_sound {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    {f h : MvPoly n R cmp} {cert : GcdCert n R cmp}
    (hc : checkGcd f h cert = true) :
    CheckedGcdResult f h cert.gcd cert.cofL cert.cofR := by
  cases n with
  | zero =>
      simp only [checkGcd, checkGcdUsing, Bool.and_eq_true,
        beq_iff_eq] at hc
      exact ⟨hc.1.1.1.symm, hc.1.1.2.symm, hc.1.2,
        checkCoprime_sound hc.2⟩
  | succ n =>
      simp only [checkGcd, checkGcdUsing, Bool.and_eq_true,
        beq_iff_eq] at hc
      exact ⟨hc.1.1.1.symm, hc.1.1.2.symm, hc.1.2,
        checkCoprime_sound hc.2⟩

/-- Separate gcd-domain cancellation turns checked coprime cofactors into
maximality. -/
theorem CheckedGcdResult.greatest {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    [CoprimeCancelLaws (MvPoly n R cmp)]
    {f h g cofL cofR : MvPoly n R cmp}
    (hc : CheckedGcdResult f h g cofL cofR) :
    ∀ d, d ∣ f → d ∣ h → d ∣ g := by
  intro d hdf hdh
  rcases hc with ⟨hf, hh, _, hcop⟩
  rw [hf] at hdf
  rw [hh] at hdh
  exact CoprimeCancelLaws.cancel_coprime g cofL cofR d hcop hdf hdh

/-- Full semantic payload of an accepted certificate. -/
theorem checkGcd_greatest {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    [CoprimeCancelLaws (MvPoly n R cmp)]
    {f h : MvPoly n R cmp} {cert : GcdCert n R cmp}
    (hc : checkGcd f h cert = true) :
    IsGcdCertResult f h cert.gcd cert.cofL cert.cofR := by
  exact ⟨checkGcd_sound hc, (checkGcd_sound hc).greatest⟩

end Hex.MvPoly

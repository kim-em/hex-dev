/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvHensel.Modulus
public import HexPolyFp
public import HexPolyZ
public import HexModArith.Modulus

@[expose] public section

/-!
The univariate correction equation used at the bottom of multivariate Hensel
lifting.

The working modulus is an arbitrary-precision prime power, so `solveUni` does
not pretend that it is a `ZMod64` modulus.  Only `witnessOf?` works at the
word-sized residue prime: it computes the partial-fraction tuple there with
`DensePoly.xgcd`, then lifts the tuple one power of the prime at a time.
-/

namespace Hex.MvHensel

open Hex

/- These direct-array arithmetic wrappers keep the executable producer out of
the noncomputable reference definitions used to state polynomial laws. -/
def zAdd (f g : ZPoly) : ZPoly := DensePoly.addImpl f g
def zSub (f g : ZPoly) : ZPoly := DensePoly.subImpl f g
def zMul (f g : ZPoly) : ZPoly := DensePoly.mulImpl f g

/-- Coefficientwise reduction into the bounded residue field. -/
def toFp (p : Nat) [ZMod64.Bounds p] (f : ZPoly) : FpPoly p :=
  DensePoly.ofCoeffs (f.toArray.map fun c => ZMod64.intCast p c)

/-- Lift residue coefficients to their standard nonnegative representatives. -/
def fromFp {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : ZPoly :=
  DensePoly.ofCoeffs (f.toArray.map fun c => (c.toNat : Int))

/-- Where a multivariate lift takes place.  The coordinate fields are already
needed by the witness-producing API even though the univariate layer only
inspects `prime` and `exponent`. -/
structure Setup (n : Nat) where
  /-- The variable retained in the univariate image. -/
  main : Fin (n + 1)
  /-- Values assigned to the remaining variables. -/
  point : Fin n → Int
  /-- The bounded residue prime used to initialise the lift. -/
  prime : ZMod64.Prime
  /-- The requested prime-power exponent. -/
  exponent : Nat

namespace Setup

/-- The arbitrary-precision working modulus `p ^ l`. -/
def modulus (s : Setup n) : Nat := s.prime.m ^ s.exponent

end Setup

/-! # Integer-polynomial modular arithmetic -/

/-- Coefficientwise symmetric reduction of an integer polynomial. -/
def reduceUni (q : Nat) (f : ZPoly) : ZPoly :=
  DensePoly.ofCoeffs (f.toArray.map fun c => Modular.symMod c q)

/-- Coefficientwise congruence of integer polynomials modulo `q`. -/
def UniCongr (q : Nat) (f g : ZPoly) : Prop :=
  ∀ k : Nat, (f.coeff k - g.coeff k) % (q : Int) = 0

/-- Every stored coefficient lies in the symmetric interval `(-q/2,q/2]`. -/
def UniSymCanonical (q : Nat) (f : ZPoly) : Prop :=
  ∀ k : Nat, -(q : Int) < 2 * f.coeff k ∧ 2 * f.coeff k ≤ (q : Int)

/-- Ordered product of a list of integer polynomials. -/
def uniProduct (fs : List ZPoly) : ZPoly :=
  fs.foldl zMul 1

/-- Products omitting each list entry, built with one prefix and one suffix
pass.  The order of the retained entries is preserved. -/
def complementProducts {α : Type} (mul : α → α → α) (one : α)
    (xs : List α) : List α :=
  let prefixes := xs.scanl mul one
  let suffixes :=
    (xs.reverse.scanl (fun suffix x => mul x suffix) one).reverse.drop 1
  List.zipWith mul prefixes suffixes

/-- The product of every image other than the one at position `j`. -/
def productExcept (images : List ZPoly) (j : Nat) : ZPoly :=
  (complementProducts zMul 1 images).getD j 1

/-- Complementary products `b_j = ∏_{m ≠ j} F_m`, in image order. -/
def complements (images : List ZPoly) : List ZPoly :=
  complementProducts zMul 1 images

/-- The partial-fraction linear combination `Σ_j σ_j b_j`. -/
def uniCombination (coeffs bases : List ZPoly) : ZPoly :=
  (coeffs.zip bases).foldl
    (fun acc pair => zAdd acc (zMul pair.1 pair.2)) 0

/-- Whether every coefficient of `f` is divisible by `q`. -/
def coeffsDivisible (q : Nat) (f : ZPoly) : Bool :=
  f.toArray.all fun c => c % (q : Int) = 0

/-- Exact coefficientwise division, used only after a divisibility check. -/
def divCoeffs? (q : Nat) (f : ZPoly) : Option ZPoly :=
  if q = 0 then none
  else if coeffsDivisible q f then
    some (DensePoly.ofCoeffs (f.toArray.map fun c => c / (q : Int)))
  else none

/-- Invert an integer modulo `q`, returning the symmetric representative. -/
def invMod? (a : Int) (q : Nat) : Option Int :=
  if q ≤ 1 then none
  else
    let eg := Hex.pureIntExtGcd a (q : Int)
    if eg.1 = 1 then some (Modular.symMod eg.2.1 q) else none

/-- GMP-backed runtime implementation of `invMod?`. -/
def invModImpl? (a : Int) (q : Nat) : Option Int :=
  if q ≤ 1 then none
  else
    let eg := HexArith.Int.extGcd a (q : Int)
    if eg.1 = 1 then some (Modular.symMod eg.2.1 q) else none

/-- The runtime extended-gcd attachment computes the reference inverse. -/
theorem invMod_eq_impl : invMod? = invModImpl? := by
  funext a q
  simp only [invMod?, invModImpl?, HexArith.Int.extGcd]
  rfl

@[csimp] theorem invMod_csimp : @invMod? = @invModImpl? := invMod_eq_impl

/-- Fuelled long remainder in `(Z/qZ)[x]`.  The divisor is required to have a
unit leading coefficient; failure of that executable precondition returns
`none`. -/
def remUnitAux (q : Nat) (g : ZPoly) (invLead : Int) :
    Nat → ZPoly → ZPoly
  | 0, r => reduceUni q r
  | fuel + 1, r =>
      let r := reduceUni q r
      if r.size < g.size then
        r
      else
        let k := r.size - g.size
        let c := Modular.symMod (r.leadingCoeff * invLead) q
        let cancel := DensePoly.scaleImpl c (DensePoly.shiftImpl k g)
        remUnitAux q g invLead fuel (zSub r cancel)

/-- Remainder modulo a polynomial whose leading coefficient is a unit modulo
`q`. -/
def remUnit? (q : Nat) (f g : ZPoly) : Option ZPoly :=
  let g := reduceUni q g
  if g.size = 0 then none
  else
    match invMod? g.leadingCoeff q with
    | none => none
    | some invLead => some (remUnitAux q g invLead (f.size + 1) f)

/-- Pairwise worker for `solveUni`.  Equal list lengths are part of the checked
lift input; the total fallback truncates at the shorter list. -/
def solveUniGo (q : Nat) (c : ZPoly) :
    List ZPoly → List ZPoly → List ZPoly
  | F :: Fs, sigma :: sigmas =>
      (remUnit? q (zMul sigma c) F).getD 0 :: solveUniGo q c Fs sigmas
  | _, _ => []

/-- Given a partial-fraction witness, return the symmetric-canonical,
degree-bounded solution of the univariate correction equation. -/
def solveUni (q : Nat) (images witness : List ZPoly) (c : ZPoly) :
    List ZPoly :=
  solveUniGo q c images witness

/-! # Producing and lifting the partial-fraction tuple -/

/-- Compute the inverse of the complementary product modulo image `j` over
the residue prime. -/
def baseWitnessAt? (p : Nat) [ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] (images bases : List ZPoly)
    (j : Nat) : Option ZPoly :=
  let F := images.getD j 0
  let Fp := toFp p F
  if F.size < 2 || Fp.size != F.size then
    none
  else
    let bp := toFp p (bases.getD j 1)
    let raw := DensePoly.xgcd bp Fp
    if raw.gcd.size != 1 || raw.gcd.leadingCoeff = 0 then
      none
    else
      let scale := raw.gcd.leadingCoeff⁻¹
      let sigma := DensePoly.scaleImpl scale raw.left % Fp
      some (fromFp sigma)

/-- Compute the partial-fraction tuple modulo the residue prime. -/
def baseWitness? (prime : ZMod64.Prime)
    (images bases : List ZPoly) : Option (List ZPoly) :=
  letI : ZMod64.Bounds prime.m := prime.bounds
  letI : ZMod64.PrimeModulus prime.m :=
    ZMod64.primeModulusOfPrime prime.prime
  if images.isEmpty then none
  else do
    let tuple ← (List.range images.length).mapM
      (baseWitnessAt? prime.m images bases)
    let identity := uniCombination tuple bases
    if coeffsDivisible prime.m (zSub identity 1) then
      some tuple
    else none

/-- Solve one correction equation modulo the residue prime using the base
partial-fraction tuple. -/
def solveBase? (prime : ZMod64.Prime) (images base : List ZPoly)
    (c : ZPoly) : Option (List ZPoly) :=
  letI : ZMod64.Bounds prime.m := prime.bounds
  letI : ZMod64.PrimeModulus prime.m :=
    ZMod64.primeModulusOfPrime prime.prime
  if images.length != base.length then none
  else
    (List.range images.length).mapM fun j =>
      let Fp := toFp prime.m (images.getD j 0)
      if Fp.size = 0 then none
      else
        let sigma := toFp prime.m (base.getD j 0)
        let ep := toFp prime.m c
        some (fromFp ((DensePoly.mulImpl sigma ep) % Fp))

/-- Add the scaled correction tuple without reducing by the image factors.
This preservation is essential: such a reduction would generally destroy the
lifted partial-fraction identity. -/
def addScaled (scale : Nat) : List ZPoly → List ZPoly → List ZPoly
  | sigma :: sigmas, tau :: taus =>
      zAdd sigma (DensePoly.scaleImpl (scale : Int) tau) ::
        addScaled scale sigmas taus
  | [], [] => []
  | _, _ => []

/-- The changing part of a partial-fraction witness lift. -/
structure WitnessState where
  /-- The prime power at which `tuple` is currently valid. -/
  modulus : Nat
  /-- The current lifted partial-fraction tuple. -/
  tuple : List ZPoly

/-- Lift an already valid mod-`p` tuple through `steps` further powers. -/
def liftWitness (prime : ZMod64.Prime)
    (images bases base : List ZPoly) :
    Nat → WitnessState → Option WitnessState
  | 0, state => some state
  | steps + 1, state => do
      let residual := zSub (1 : ZPoly)
        (uniCombination state.tuple bases)
      let error ← divCoeffs? state.modulus residual
      let correction ← solveBase? prime images base error
      let next := addScaled state.modulus state.tuple correction
      let nextModulus := state.modulus * prime.m
      if coeffsDivisible nextModulus
          (zSub (uniCombination next bases) 1) then
        liftWitness prime images bases base steps
          { modulus := nextModulus, tuple := next }
      else none

/-- Produce the partial-fraction tuple modulo `p ^ l`, or `none` if an image
loses degree modulo `p`, the images are not pairwise coprime there, or the
requested exponent is zero. -/
def witnessOf? (s : Setup n) (images : List ZPoly) : Option (List ZPoly) := do
  if s.exponent = 0 then none else pure ()
  let bases := complements images
  let base ← baseWitness? s.prime images bases
  let lifted ← liftWitness s.prime images bases base (s.exponent - 1)
    { modulus := s.prime.m, tuple := base }
  if coeffsDivisible lifted.modulus
      (zSub (uniCombination lifted.tuple bases) 1) then
    some lifted.tuple
  else none

/-! # The checked mathematical contract -/

/-- The direct hypotheses on the univariate data extracted from V1, V5 and
V6 of a valid multivariate lift input. -/
structure UniValid (q : Nat) (images witness : List ZPoly) : Prop where
  /-- A working prime power is nontrivial. -/
  modulus : 1 < q
  /-- There is one witness component per image. -/
  lengths : witness.length = images.length
  /-- Constant images have already been removed as content. -/
  positiveDegree : ∀ j, j < images.length → 0 < (images.getD j 0).degree?.getD 0
  /-- Every image has unit leading coefficient modulo the prime power. -/
  unitLeading : ∀ j, j < images.length →
    Int.gcd (images.getD j 0).leadingCoeff (q : Int) = 1
  /-- The supplied tuple is a partial-fraction identity. -/
  identity : UniCongr q (uniCombination witness (complements images)) 1
  /-- Witness components use their degree-bounded representatives. -/
  witnessDegree : ∀ j, j < images.length →
    (witness.getD j 0).degree?.getD 0 <
      (images.getD j 0).degree?.getD 0

/-- `solveUni` reconstructs every right-hand side below the product degree. -/
theorem solveUni_spec {q : Nat} {images witness : List ZPoly} {c : ZPoly}
    (h : UniValid q images witness)
    (hc : (reduceUni q c).degree?.getD 0 <
      (uniProduct images).degree?.getD 0) :
    UniCongr q
      (uniCombination (solveUni q images witness c) (complements images)) c := by
  sorry

/-- Each component returned by `solveUni` has degree below its image. -/
theorem solveUni_degree {q : Nat} {images witness : List ZPoly} {c : ZPoly}
    (h : UniValid q images witness) (j : Nat) (hj : j < images.length) :
    ((solveUni q images witness c).getD j 0).degree?.getD 0 <
      (images.getD j 0).degree?.getD 0 := by
  sorry

/-- `solveUni` chooses the symmetric representative of each residue class. -/
theorem solveUni_symCanonical {q : Nat} {images witness : List ZPoly}
    {c : ZPoly} (h : UniValid q images witness) (j : Nat)
    (hj : j < images.length) :
    UniSymCanonical q ((solveUni q images witness c).getD j 0) := by
  sorry

/-- Degree-bounded solutions are unique coefficientwise modulo `q`. -/
theorem solveUni_unique {q : Nat} {images witness tau : List ZPoly}
    {c : ZPoly} (h : UniValid q images witness)
    (hlen : tau.length = images.length)
    (hdegree : ∀ j, j < images.length →
      (tau.getD j 0).degree?.getD 0 <
        (images.getD j 0).degree?.getD 0)
    (hsum : UniCongr q (uniCombination tau (complements images)) c) :
    ∀ j, j < images.length →
      UniCongr q (tau.getD j 0)
        ((solveUni q images witness c).getD j 0) := by
  sorry

/-- Two symmetric-canonical representatives of the same coefficientwise
residue class are equal. -/
theorem UniSymCanonical.eq_of_congr {q : Nat} {f g : ZPoly}
    (hf : UniSymCanonical q f) (hg : UniSymCanonical q g)
    (hfg : UniCongr q f g) : f = g := by
  apply DensePoly.ext_coeff
  intro k
  have hf' := hf k
  have hg' := hg k
  have hq : 0 < q := by omega
  have hdvd : (q : Int) ∣ f.coeff k - g.coeff k :=
    Int.dvd_of_emod_eq_zero (hfg k)
  have hlt : (f.coeff k - g.coeff k).natAbs < q := by
    by_cases hnonneg : 0 ≤ f.coeff k - g.coeff k
    · rw [← Int.ofNat_lt, Int.natAbs_of_nonneg hnonneg]
      omega
    · have hnonpos : f.coeff k - g.coeff k ≤ 0 := by omega
      rw [← Int.ofNat_lt, Int.ofNat_natAbs_of_nonpos hnonpos]
      omega
  have hzero : f.coeff k - g.coeff k = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    simpa using hlt
  omega

/-- A symmetric-canonical degree-bounded solution is the exact tuple
component selected by `solveUni`, not merely a congruent representative. -/
theorem solveUni_eq {q : Nat} {images witness tau : List ZPoly}
    {c : ZPoly} (h : UniValid q images witness)
    (hlen : tau.length = images.length)
    (hdegree : ∀ j, j < images.length →
      (tau.getD j 0).degree?.getD 0 <
        (images.getD j 0).degree?.getD 0)
    (hsum : UniCongr q (uniCombination tau (complements images)) c)
    (hcanonical : ∀ j, j < images.length →
      UniSymCanonical q (tau.getD j 0)) :
    ∀ j, j < images.length →
      tau.getD j 0 = (solveUni q images witness c).getD j 0 := by
  intro j hj
  apply UniSymCanonical.eq_of_congr (hcanonical j hj)
    (solveUni_symCanonical h j hj)
  exact solveUni_unique h hlen hdegree hsum j hj

end Hex.MvHensel

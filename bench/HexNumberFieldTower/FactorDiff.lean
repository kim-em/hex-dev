/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.FactorRaw

public section

/-!
# Exact differential checks for tower factorization experiments

The reference namespaces below freeze the computational norm and factorization
definitions from `af7b4d49f661a23debf82960bfff3c78435ff135`. Keep them independent
of the candidate's norm, recovery dispatch, and checker. This untimed local
driver compares complete coordinate arrays and certificate acceptance; it is
not a lean-bench registration or a source of performance measurements.
-/
namespace Hex.NumberTower

namespace ReferenceNorm

open Arithmetic

/-- Interpret flattened current-tower coordinates as a polynomial in the top
generator, with coefficients that are constant polynomials in `X` over the
lower tower. -/
@[expose]
def liftCoefficient (level : Level) (lower : List Level)
    (a : Array Rat) : DensePoly (DensePoly (Coeff lower)) :=
  let lowerDim := levelsDim lower
  DensePoly.ofCoeffs <| ((List.range level.degree).map fun j =>
    DensePoly.C (Coeff.ofData lower (block a j lowerDim))).toArray

/-- The newest level's monic defining polynomial in the elimination variable,
with coefficients regarded as constant polynomials in `X`. -/
@[expose]
def definingOuter (level : Level) (lower : List Level) :
    DensePoly (DensePoly (Coeff lower)) :=
  DensePoly.ofCoeffs <| (((List.range level.degree).map fun i =>
    DensePoly.C (Coeff.ofData lower (level.defining.getD i #[]))).toArray).push
      (DensePoly.C 1)

/-- Substitute `X - cY` into a polynomial over the current tower, presenting
the result as a polynomial in `Y` over `lower[X]`. -/
@[expose]
def shiftedOuter (level : Level) (lower : List Level)
    (f : Array (Array Rat)) (c : Int) :
    DensePoly (DensePoly (Coeff lower)) :=
  let x : DensePoly (Coeff lower) := DensePoly.monomial 1 1
  let negShift : Coeff lower := Coeff.ofData lower #[(-(c : Rat))]
  let xSubCY : DensePoly (DensePoly (Coeff lower)) :=
    DensePoly.ofCoeffs #[x, DensePoly.C negShift]
  f.foldr (fun coefficient value =>
    liftCoefficient level lower coefficient + xSubCY * value) 0

/-- One Trager norm step. Input coefficients are flattened over
`level :: lower`; output coefficients are flattened over `lower`. -/
@[expose]
def oneLevel (level : Level) (lower : List Level)
    (f : Array (Array Rat)) (c : Int) : Array (Array Rat) :=
  (DensePoly.resultant (definingOuter level lower)
    (shiftedOuter level lower f c)).toArray.map Coeff.data

/-- Eliminate every tower generator without shifting. This absolute norm is
used to obtain root candidates for splitting; recursive Trager factorization
continues to use `oneLevel` independently at each level. -/
@[expose]
def iterated : (levels : List Level) → Array (Array Rat) → Array (Array Rat)
  | [], f => f
  | level :: lower, f => iterated lower (oneLevel level lower f 0)

/-- Formal derivative over a runtime-indexed lower tower. -/
@[expose]
def derivative (lower : List Level) (f : DensePoly (Coeff lower)) :
    DensePoly (Coeff lower) :=
  DensePoly.ofCoeffs <| ((List.range (f.size - 1)).map fun i =>
    Coeff.ofData lower <| (f.coeff (i + 1)).data.map fun q =>
      ((i + 1 : Nat) : Rat) * q).toArray

/-- Monic normalization over the runtime-indexed lower tower. -/
@[expose]
def monic (f : DensePoly (Coeff lower)) : DensePoly (Coeff lower) :=
  if f.isZero then 0 else DensePoly.scale f.leadingCoeff⁻¹ f

/-- Executable squarefreeness test over a checked lower tower. The rational
base uses the certified modular trial before exact gcd fallback. -/
@[expose]
def isSquarefree (lower : List Level) (f : Array (Array Rat)) : Bool :=
  match lower with
  -- This is Factor.toRatPoly, spelled out to avoid the downstream import.
  -- The base case of the companion's isSquarefree_iff pins them definitionally.
  | [] => ZPoly.ratSquarefree (DensePoly.ofCoeffs (f.map fun a => a.getD 0 0))
  | _ :: _ =>
    let p : DensePoly (Coeff lower) :=
      DensePoly.ofCoeffs (f.map (Coeff.ofData lower))
    !p.isZero && (DensePoly.gcd p (derivative lower p)).size ≤ 1

/-- Number of deterministic Trager shifts required for a top degree `d` and
component degree `m`. -/
@[expose]
def tragerShiftCount (d m : Nat) : Nat :=
  Nat.choose (d * m) 2 + 1

/-- Deterministic signed enumeration `0, 1, -1, 2, -2, ...`. -/
@[expose]
def signedShift (i : Nat) : Int :=
  AlgebraicPoly.Common.signedShift i

/-- Search successive signed shifts without materializing the remaining range. -/
@[expose]
def findSquarefreeShiftAux (level : Level) (lower : List Level)
    (f : Array (Array Rat)) (i : Nat) : Nat →
    Option (Int × Array (Array Rat))
  | 0 => none
  | fuel + 1 =>
    let c := signedShift i
    let norm := oneLevel level lower f c
    if isSquarefree lower norm then
      some (c, norm)
    else
      findSquarefreeShiftAux level lower f (i + 1) fuel

/-- Search exactly the finite Trager collision bound and return the first
shift whose one-level norm is squarefree over the lower tower. -/
@[expose]
def findSquarefreeShift (level : Level) (lower : List Level)
    (f : Array (Array Rat)) : Option (Int × Array (Array Rat)) :=
  findSquarefreeShiftAux level lower f 0
    (tragerShiftCount level.degree (f.size - 1))


end ReferenceNorm
end Hex.NumberTower
namespace Hex.NumberTower

namespace ReferenceFactor

open Arithmetic

/-- Convert raw flattened coefficient arrays to a runtime-indexed tower
polynomial. -/
@[expose]
def rawPoly (levels : List Level) (f : Array (Array Rat)) :
    DensePoly (Coeff levels) :=
  DensePoly.ofCoeffs (f.map (Coeff.ofData levels))

/-- Extract flattened coefficient arrays from a runtime-indexed tower
polynomial. -/
@[expose]
def polyCoords {levels : List Level} (f : DensePoly (Coeff levels)) :
    Array (Array Rat) :=
  f.toArray.map Coeff.data

/-- Fuel-bounded Yun loop. Here `w` is the product of the factors whose
multiplicity is still at least the current index, while `repeated` contains
their remaining copies. Dividing `w` by their gcd emits the squarefree
component of exactly that multiplicity. -/
@[expose]
def yunAux (levels : List Level)
    (w repeated : DensePoly (Coeff levels)) (multiplicity fuel : Nat)
    (out : Array (Array (Array Rat) × Nat)) :
    Array (Array (Array Rat) × Nat) :=
  match fuel with
  | 0 => out
  | fuel + 1 =>
      if w = 1 then
        out
      else
        let shared := ReferenceNorm.monic (DensePoly.gcd w repeated)
        let component := ReferenceNorm.monic (w / shared)
        let out := if 0 < component.natDegree then
          out.push (polyCoords component, multiplicity)
        else
          out
        let nextRepeated := ReferenceNorm.monic (repeated / shared)
        yunAux levels shared nextRepeated (multiplicity + 1) fuel out

/-- Yun squarefree decomposition over raw tower coordinates. Zero and
constants have no positive-degree components. -/
@[expose]
def yunRaw (levels : List Level) (f : Array (Array Rat)) :
    Array (Array (Array Rat) × Nat) :=
  let p := rawPoly levels f
  if p.natDegree = 0 then
    #[]
  else
    let normalized := ReferenceNorm.monic p
    let repeated := ReferenceNorm.monic
      (DensePoly.gcd normalized (ReferenceNorm.derivative levels normalized))
    let distinct := ReferenceNorm.monic (normalized / repeated)
    yunAux levels distinct repeated 1 (p.size + 1) #[]

/-- Polynomial power used by reconstruction checks, computed by repeated
squaring so high multiplicities do not induce a linear multiplication chain. -/
@[expose]
def polyPow {levels : List Level} (f : DensePoly (Coeff levels)) (n : Nat) :
    DensePoly (Coeff levels) :=
  if n = 0 then
    1
  else
    let half := polyPow f (n / 2)
    let square := half * half
    if n % 2 = 0 then square else square * f
termination_by n
decreasing_by omega

/-- Reconstruct a monic polynomial from raw Yun components. -/
@[expose]
def yunProduct (levels : List Level)
    (components : Array (Array (Array Rat) × Nat)) :
    Array (Array Rat) :=
  polyCoords <| components.foldl
    (fun product component =>
      product * polyPow (rawPoly levels component.1) component.2)
    1

/-- Check that the emitted multiplicities are in strictly increasing order. -/
@[expose]
def yunMultiplicitiesIncrease
    (components : Array (Array (Array Rat) × Nat)) : Bool :=
  decide <| components.toList.Pairwise fun a b => a.2 < b.2

/-- Check that distinct Yun components are pairwise coprime. -/
@[expose]
def yunPairwiseCoprime (levels : List Level)
    (components : Array (Array (Array Rat) × Nat)) : Bool :=
  decide <| components.toList.Pairwise fun a b =>
    (DensePoly.gcd (rawPoly levels a.1) (rawPoly levels b.1)).size ≤ 1

/-- Self-check a Yun decomposition: multiplicities are positive and strictly
increasing, the monic squarefree components are pairwise coprime, and their
powered product reconstructs the monic input. Polynomials of degree zero have
the unique empty decomposition. -/
@[expose]
def checkYun (levels : List Level) (f : Array (Array Rat))
    (components : Array (Array (Array Rat) × Nat)) : Bool :=
  let p := rawPoly levels f
  if p.natDegree = 0 then
    components.isEmpty
  else
    yunMultiplicitiesIncrease components &&
      components.all (fun component =>
        0 < component.2 &&
          let factor := rawPoly levels component.1
          0 < factor.natDegree && factor.leadingCoeff = 1) &&
      yunPairwiseCoprime levels components &&
      components.all (fun component =>
        ReferenceNorm.isSquarefree levels component.1) &&
      yunProduct levels components = polyCoords (ReferenceNorm.monic p)

/-- Recover the rational polynomial stored by base-tower raw coordinates. -/
@[expose]
def toRatPoly (f : Array (Array Rat)) : DensePoly Rat :=
  DensePoly.ofCoeffs (f.map fun coefficient => coefficient.getD 0 0)

/-- Convert a rational polynomial back to raw base-tower coordinates. -/
@[expose]
def ofRatPoly (f : DensePoly Rat) : Array (Array Rat) :=
  f.toArray.map fun coefficient => #[coefficient]

/-- Complete factorization of a monic squarefree rational polynomial. The
Berlekamp–Zassenhaus entries are expanded by multiplicity before their monic
normalizations are checked against the input.  The recursive caller admits
only squarefree inputs, so the companion proves that this expansion contains
one copy of each irreducible factor; expanding here also makes reconstruction
independent of that semantic fact. -/
@[expose]
def factorRat? (input : DensePoly Rat) :
    Option (Array (Array (Array Rat))) :=
  let p := if input.isZero then 0 else
    DensePoly.scale input.leadingCoeff⁻¹ input
  if p.isZero then
    some #[]
  else if ZPoly.ratSquarefree p then
    let integer := ZPoly.ratPolyPrimitivePart p
    let factorization := ZPoly.factorize integer
    let factors := (factorization.factors.flatMap fun entry =>
      Array.replicate entry.2 entry.1).map fun factor =>
        let q := ZPoly.toRatPoly factor
        let q := DensePoly.scale q.leadingCoeff⁻¹ q
        ofRatPoly q
    let product := factors.foldl
      (fun product factor => product * toRatPoly factor)
      1
    if product = p then some factors else none
  else
    none

/-- The newest generator as a runtime-indexed element. A linear level already
lies in the lower field, so its generator is the negative constant term of its
monic relation. -/
@[expose]
def topGenerator (level : Level) (lower : List Level) :
    Coeff (level :: lower) :=
  if level.degree = 1 then
    -Coeff.ofData (level :: lower) (level.defining.getD 0 #[])
  else
    Coeff.ofData (level :: lower)
      ((Array.replicate (levelsDim lower) 0).push 1)

/-- Substitute `X - c*alpha` in a current-level polynomial. -/
@[expose]
def shiftTop (level : Level) (lower : List Level)
    (f : Array (Array Rat)) (c : Int) : Array (Array Rat) :=
  let levels := level :: lower
  let delta := Coeff.ofData levels #[(c : Rat)] * topGenerator level lower
  let substitution : DensePoly (Coeff levels) :=
    DensePoly.ofCoeffs #[-delta, 1]
  polyCoords (DensePoly.compose (rawPoly levels f) substitution)

/-- Embed a lower-tail polynomial into the current level. Mixed-radix order
places lower coordinates in the first top-generator block. -/
@[expose]
def embedLower (level : Level) (lower : List Level)
    (f : Array (Array Rat)) : Array (Array Rat) :=
  let levels := level :: lower
  polyCoords <| DensePoly.ofCoeffs <| f.map fun coefficient =>
    Coeff.ofData levels coefficient

/-- Start recovery division with the monic shifted component when it has
smaller degree than the lifted norm factor. The remaining Euclidean chain
uses exactly the reference gcd's remaining fuel and remainder representative. -/
@[expose]
def recoveryGcd (p q : DensePoly (Coeff levels)) : DensePoly (Coeff levels) :=
  if p.isZero = false ∧ p.size < q.size ∧ p.leadingCoeff = 1 then
    DensePoly.gcdAux p (DensePoly.modArray q p id) (p.size + q.size - 1)
  else
    DensePoly.gcd p q

/-- Recover current-level factors from irreducible lower factors of a
squarefree Trager norm, then undo the selected generator shift. -/
@[expose]
def recover (level : Level) (lower : List Level)
    (shift : Int) (component : Array (Array Rat))
    (lowerFactors : Array (Array (Array Rat))) :
    Array (Array (Array Rat)) :=
  let levels := level :: lower
  let shifted := rawPoly levels (shiftTop level lower component shift)
  lowerFactors.foldl (fun out lowerFactor =>
    let lifted := rawPoly levels (embedLower level lower lowerFactor)
    let common := ReferenceNorm.monic (recoveryGcd shifted lifted)
    if 0 < common.natDegree then
      let unshifted := shiftTop level lower (polyCoords common) (-shift)
      out.push (polyCoords (ReferenceNorm.monic (rawPoly levels unshifted)))
    else
      out) #[]

/-- Recursive Trager factorization of one monic squarefree component. The
recursion is structural in the tower height; every proper level performs one
bounded one-level norm search and recurses only on the lower tail. -/
@[expose]
def factorSquarefree? : (levels : List Level) → Array (Array Rat) →
    Option (Array (Array (Array Rat)))
  | [], f => factorRat? (toRatPoly f)
  | level :: lower, f => do
      if ReferenceNorm.isSquarefree (level :: lower) f then
        let (shift, norm) ← ReferenceNorm.findSquarefreeShift level lower f
        let lowerFactors ← factorSquarefree? lower norm
        let factors := recover level lower shift f lowerFactors
        let p := ReferenceNorm.monic (rawPoly (level :: lower) f)
        let product := factors.foldl
          (fun product factor => product * rawPoly (level :: lower) factor)
          1
        if factors.all (fun factor =>
            0 < (rawPoly (level :: lower) factor).natDegree) &&
            product = p then
          some factors
        else
          none
      else
        none

/-- Runtime factorization payload before re-indexing coefficients by a public
`NumberTower`. -/
structure RawFactorization where
  /-- The leading scalar's raw coordinates. -/
  scalar : Array Rat
  /-- Raw monic factors, canonically sorted, each with its multiplicity. -/
  factors : Array (Array (Array Rat) × Nat)

/-- Lexicographic order on rational lists. -/
@[expose]
def ratListLess : List Rat → List Rat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a < b then true else if b < a then false else ratListLess as bs

/-- Flatten polynomial coefficient coordinates for canonical sorting.  Each
coefficient carries its length, so the key remains injective even for malformed
raw inputs whose coordinate blocks do not have the tower width. -/
@[expose]
def flattenPoly (f : Array (Array Rat)) : List Rat :=
  f.toList.flatMap fun coefficient =>
    (coefficient.size : Rat) :: coefficient.toList

/-- Canonical lexicographic factor order. -/
@[expose]
def factorLess (a b : Array (Array Rat)) : Bool :=
  ratListLess (flattenPoly a) (flattenPoly b)

/-- Insert one factor into a canonically ordered factor list. Equal coordinate
keys are combined by adding multiplicities. -/
@[expose]
def insertFactor (factor : Array (Array Rat) × Nat) :
    List (Array (Array Rat) × Nat) → List (Array (Array Rat) × Nat)
  | [] => [factor]
  | head :: tail =>
      if factorLess factor.1 head.1 then
        factor :: head :: tail
      else if factorLess head.1 factor.1 then
        head :: insertFactor factor tail
      else
        (head.1, head.2 + factor.2) :: tail

/-- Sort factors canonically and combine duplicate coordinate keys. -/
@[expose]
def canonicalFactors
    (factors : Array (Array (Array Rat) × Nat)) :
    Array (Array (Array Rat) × Nat) :=
  (factors.toList.foldl (fun out factor => insertFactor factor out) []).toArray

/-- Check that every pair of factors is in strict canonical order. Strictness
ensures each irreducible occurs once, with its multiplicity stored in the
paired natural number. -/
@[expose]
def factorsSorted (factors : Array (Array (Array Rat) × Nat)) : Bool :=
  decide <| factors.toList.Pairwise fun a b =>
    factorLess a.1 b.1 = true

/-- Multiply a scalar and powered raw factor list. -/
@[expose]
def factorProduct (levels : List Level) (scalar : Array Rat)
    (factors : Array (Array (Array Rat) × Nat)) : Array (Array Rat) :=
  polyCoords <| factors.foldl
    (fun product factor =>
      product * polyPow (rawPoly levels factor.1) factor.2)
    (DensePoly.C (Coeff.ofData levels scalar))

/-- Executable recursive irreducibility checker for a monic squarefree raw
tower polynomial. The rational base delegates to the integer-polynomial checker
shared by rational factorization; proper towers accept exactly a singleton
Trager reconstruction. -/
@[expose]
def isIrreducible (levels : List Level) (f : Array (Array Rat)) : Bool :=
  let p := rawPoly levels f
  0 < p.natDegree && p.leadingCoeff = 1 &&
    ReferenceNorm.isSquarefree levels f &&
    match levels with
    | [] => ZPoly.isIrreducible (ZPoly.ratPolyPrimitivePart (toRatPoly f))
    | _ :: _ =>
        match factorSquarefree? levels f with
        | some factors => factors = #[polyCoords p]
        | none => false

/-- Append all irreducible factors of one Yun component, carrying the Yun
multiplicity into the accumulated factor list. -/
@[expose]
def appendComponent? (levels : List Level)
    (out : Array (Array (Array Rat) × Nat))
    (component : Array (Array Rat) × Nat) :
    Option (Array (Array (Array Rat) × Nat)) := do
  let irreducibles ← factorSquarefree? levels component.1
  pure <| irreducibles.foldl
    (fun out factor => out.push (factor, component.2)) out

/-- Full executable raw factorization certificate check. At proper tower
levels, “irreducible” means a piece the recursive Trager checker cannot split;
the Mathlib companion supplies the semantic irreducibility theorem. Cheap
reconstruction and canonical-order checks precede recursive replay. -/
@[expose]
def check (levels : List Level) (f : Array (Array Rat)) (scalar : Array Rat)
    (factors : Array (Array (Array Rat) × Nat)) : Bool :=
  factors.all (fun factor =>
      polyCoords (rawPoly levels factor.1) = factor.1) &&
    factorProduct levels scalar factors = f && factorsSorted factors &&
      factors.all (fun factor =>
        0 < factor.2 && isIrreducible levels factor.1)

/-- Produce a canonical factorization candidate with checked Yun
multiplicities and recursive Trager recovery. The public dependent constructor
performs the one full executable certificate replay. -/
@[expose]
def factorRaw? (levels : List Level) (f : Array (Array Rat)) :
    Option RawFactorization := do
  let p := rawPoly levels f
  let scalar := p.leadingCoeff.data
  let components := yunRaw levels f
  if checkYun levels f components then
    let factors ← components.foldlM (appendComponent? levels) #[]
    let factors := canonicalFactors factors
    some ⟨scalar, factors⟩
  else
    none


end ReferenceFactor
end Hex.NumberTower

open Hex Hex.NumberTower Hex.NumberTower.Arithmetic

private def level (degree : Nat) (defining : Array (Array Rat)) : Level :=
  ⟨degree, defining, AlgebraicNumber.zero.toRoot⟩

private def compareFactor (levels : List Level) (f : Array (Array Rat)) : IO Unit := do
  let actual := Factor.factorRaw? levels f
  let expected := ReferenceFactor.factorRaw? levels f
  match actual, expected with
  | some a, some b =>
    unless a.scalar == b.scalar && a.factors == b.factors do
      throw (IO.userError s!"canonical factor mismatch: {repr f}")
    let check := Factor.check levels f a.scalar a.factors
    unless check == ReferenceFactor.check levels f b.scalar b.factors do
      throw (IO.userError "checker mismatch")
    unless check do throw (IO.userError s!"checker rejected: {repr f}")
    if !a.factors.isEmpty then
      let bad := a.factors.modify 0 fun (p, n) => (p, n + 1)
      if Factor.check levels f a.scalar bad || ReferenceFactor.check levels f b.scalar bad then
        throw (IO.userError "corrupted multiplicity accepted")
  | _, _ => throw (IO.userError s!"factorization missing: {repr f}")

def main : IO Unit := do
  let sqrtTwo := level 2 #[#[-2], #[0]]
  let sqrtThree := level 2 #[#[-3, 0], #[0, 0]]
  let mut factors := 0
  for levels in [[], [sqrtTwo], [sqrtThree, sqrtTwo]] do
    let x : DensePoly (Coeff levels) := DensePoly.monomial 1 1
    let a := Coeff.ofData levels #[1/2, 1/3, 1/4, 1/5]
    let first := x - DensePoly.C a
    let second := x + 1
    for p in #[0, 1, DensePoly.C a, first, first * second,
        Factor.polyPow first 2 * second,
        DensePoly.scale (Coeff.ofData levels #[2/3]) (first * second),
        x * x - x - 1] do
      compareFactor levels (Factor.polyCoords p)
      factors := factors + 1
  for n in #[2, 3, 4, 6, 8, 12, 24] do
    let f := (Array.range (n + 1)).map fun i =>
      if i == n then #[1, 0] else if i == 0 || i == 1 then #[-1, 0] else #[0, 0]
    compareFactor [sqrtTwo] f
    factors := factors + 1
  let mut norms := 0
  for (top, lower) in [(sqrtTwo, []), (level 2 #[#[1], #[1]], []),
      (sqrtThree, [sqrtTwo]), (level 2 #[#[1, 1], #[1, -1]], [sqrtTwo]),
      (level 3 #[#[-2], #[0], #[0]], [])] do
    for n in Array.range 6 do
      for seed in Array.range 5 do
        let f := (Array.range n).map fun i =>
          (Array.range (top.degree * levelsDim lower)).map fun j =>
            ((Int.ofNat ((i * 3 + j * 2 + seed) % 7) - 3 : Int) : Rat) / (j + 1 : Nat)
        for shift in #[0, 1, -1, 2, -2] do
          let expected := ReferenceNorm.oneLevel top lower f shift
          let actual := Norm.oneLevel top lower f shift
          unless actual == expected do
            throw (IO.userError s!"norm mismatch: {top.degree}, {n}, {seed}, {shift}: {repr actual} != {repr expected}")
          norms := norms + 1
  IO.println s!"Exact canonical factorizations/checks: {factors}; exact norm arrays: {norms}; corrupted multiplicities rejected."

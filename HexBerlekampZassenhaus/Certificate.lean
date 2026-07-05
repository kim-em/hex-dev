/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.Basic
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL.Basic
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL.Basic
-- Needed so `decide`/`rfl` over `DensePoly`/`Array` equality reduces in the
-- kernel: the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq

public import HexBerlekampZassenhaus.Records
public meta import HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects the irreducibility-certificate structures, their checkers, and `certifyIrreducible?`.
-/
namespace Hex

/--
Reassemble normalization-prefix and square-free factors around the supplied
core factors, expanding each core factor `q` to its multiplicity in
`d.repeatedPart` so the recorded `Factorization` carries the right exponents
for higher-multiplicity inputs. Falls back to the un-expanded
`polynomialNormalizationPrefixFactors` shape when the expansion does not
fully consume `repeatedPart` (e.g. when the BZ pipeline emitted the raw
square-free core as a single core factor).
-/
@[expose]
private def reassemblePolynomialFactors
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) : Array ZPoly :=
  let (expanded, residual) := expandRepeatedPartFactorArray d.repeatedPart coreFactors
  if residual = 1 then
    xPowerFactorArray d.xPower ++ expanded ++ coreFactors
  else
    polynomialNormalizationPrefixFactors d ++ coreFactors

@[expose]
private def factorizationOfFactors (f : ZPoly) (factors : Array ZPoly) : Factorization :=
  { scalar := signedContentScalar f
    factors := collectFactorMultiplicities factors }

private def normalizedConstantFactors (d : FactorNormalizationData) : Array ZPoly :=
  let coreFactor :=
    if d.squareFreeCore = 1 then
      #[]
    else
      #[d.squareFreeCore]
  normalizationPrefixFactors d ++ coreFactor

/--
Per-prime modular irreducibility evidence for integer irreducibility
certificates.

The factor array records the modular factors observed at this prime. The degree
list and Rabin certificates are zipped with those concrete factors so the
checker can validate certificate metadata and the executable Rabin witness
against the polynomial it is meant to certify.
-/
structure PrimeFactorData where
  p : Nat
  [bounds : ZMod64.Bounds p]
  factorDegrees : Array Nat
  factorPolys : Array (FpPoly p)
  factorCerts : Array Berlekamp.IrreducibilityCertificate

/--
Evidence that a candidate integer factor degree is impossible for one recorded
prime block.

If an integer factor has degree `targetDegree`, then reducing modulo any good
prime gives a product of modular irreducible factors whose degrees sum to
`targetDegree`. The checker validates an obstruction by confirming that the
referenced prime block has no subset of recorded factor degrees with this sum.
-/
structure DegreeObstruction where
  targetDegree : Nat
  primeIndex : Nat

/--
Checker-first certificate data for irreducibility over `Z[x]`.

Each entry groups all modular degree and irreducibility-certificate data for a
single prime so the checker can validate the prime and degree metadata before
the later proof layer interprets the degree obstruction mathematically.
-/
structure ZPolyIrreducibilityCertificate where
  perPrime : Array PrimeFactorData
  degreeObstructions : Array DegreeObstruction

namespace PrimeFactorData

/-- Sum the recorded modular factor degrees for one prime. -/
def degreeSum (d : PrimeFactorData) : Nat :=
  d.factorDegrees.toList.foldl (fun acc n => acc + n) 0

/-- Ordered product of the recorded modular factors for one prime. -/
@[expose]
def factorProduct (d : PrimeFactorData) : @FpPoly d.p d.bounds :=
  letI := d.bounds
  d.factorPolys.foldl (· * ·) 1

/-- Does the recorded degree multiset contain `n`? -/
def containsDegree (d : PrimeFactorData) (n : Nat) : Bool :=
  d.factorDegrees.toList.any fun degree => degree == n

@[expose]
def hasSubsetDegreeAux : List Nat → Nat → Bool
  | [], target => target == 0
  | degree :: degrees, target =>
      hasSubsetDegreeAux degrees target ||
        (degree ≤ target && hasSubsetDegreeAux degrees (target - degree))

/--
Does some subset of this prime block's modular factor degrees sum to `target`?
-/
@[expose]
def hasSubsetDegree (d : PrimeFactorData) (target : Nat) : Bool :=
  hasSubsetDegreeAux d.factorDegrees.toList target

/--
Check one nested finite-field irreducibility certificate against its degree slot
and the concrete modular factor occupying that slot.
-/
@[expose]
def checkCertAtFactor
    (d : PrimeFactorData) (degree : Nat) (factor : @FpPoly d.p d.bounds)
    (cert : Berlekamp.IrreducibilityCertificate) : Bool :=
  letI := d.bounds
  decide (cert.p = d.p) &&
    decide (cert.n = degree) &&
    d.containsDegree cert.n &&
    factor.degree? == some degree &&
    if hmonic : factor.leadingCoeff = 1 then
      Berlekamp.checkIrreducibilityCertificate factor (by exact hmonic) cert
    else
      false

/--
Check that nested certificates match the enclosing prime, degree array, and
concrete modular factor array.
-/
@[expose]
def checkFactorCerts (d : PrimeFactorData) : Bool :=
  d.factorDegrees.size == d.factorCerts.size &&
    d.factorDegrees.size == d.factorPolys.size &&
    (d.factorDegrees.toList.zip (d.factorPolys.toList.zip d.factorCerts.toList)).all fun pair =>
      checkCertAtFactor d pair.1 pair.2.1 pair.2.2

/-- Check one prime block against the integer polynomial being certified. -/
@[expose]
def checkForPolynomial (f : ZPoly) (d : PrimeFactorData) : Bool :=
  letI := d.bounds
  isGoodPrime f d.p &&
    d.factorDegrees.all (fun degree => 0 < degree) &&
    d.degreeSum == (ZPoly.modP d.p f).degree?.getD 0 &&
    d.factorProduct == ZPoly.modP d.p f &&
    d.checkFactorCerts

end PrimeFactorData

namespace ZPolyIrreducibilityCertificate

/-- Nontrivial integer factor degrees that must be ruled out for `f`. -/
@[expose]
def candidateFactorDegrees (f : ZPoly) : List Nat :=
  (List.range ((f.degree?.getD 0) / 2)).map fun i => i + 1

/-- Look up a per-prime block by the index stored in an obstruction. -/
@[expose]
def primeDataAt? (cert : ZPolyIrreducibilityCertificate) (idx : Nat) :
    Option PrimeFactorData :=
  match cert.perPrime.toList.drop idx with
  | [] => none
  | primeData :: _ => some primeData

end ZPolyIrreducibilityCertificate

namespace DegreeObstruction

/--
Check one degree obstruction against the certificate's per-prime degree data.

The target must be one of the nontrivial candidate degrees for `f`, and the
referenced prime block must have no subset of modular factor degrees summing to
that target.
-/
@[expose]
def checkForCertificate
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (obs : DegreeObstruction) : Bool :=
  decide (obs.targetDegree ∈ ZPolyIrreducibilityCertificate.candidateFactorDegrees f) &&
    match cert.primeDataAt? obs.primeIndex with
    | none => false
    | some primeData => !primeData.hasSubsetDegree obs.targetDegree

end DegreeObstruction

namespace ZPolyIrreducibilityCertificate

/-- Does the obstruction array contain a valid obstruction for `targetDegree`? -/
@[expose]
def hasObstructionFor (f : ZPoly)
    (cert : ZPolyIrreducibilityCertificate) (targetDegree : Nat) : Bool :=
  cert.degreeObstructions.toList.any fun obs =>
    obs.targetDegree == targetDegree && obs.checkForCertificate f cert

/-- Check that every candidate nontrivial factor degree is ruled out. -/
def checkDegreeObstructions (f : ZPoly)
    (cert : ZPolyIrreducibilityCertificate) : Bool :=
  (cert.degreeObstructions.all fun obs => obs.checkForCertificate f cert) &&
    (candidateFactorDegrees f).all fun targetDegree =>
      cert.hasObstructionFor f targetDegree

end ZPolyIrreducibilityCertificate

/--
Executable surface checker for integer-polynomial irreducibility certificates.

This validates all computational alignment data available at this layer: every
prime block must use an admissible prime for `f`, its recorded modular factors
must multiply back to the modular image, each nested finite-field certificate
must match the enclosing prime and its concrete factor, and every nontrivial
integer factor degree must be excluded by explicit per-prime degree data.
-/
def checkIrreducibleCert
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate) : Bool :=
  cert.perPrime.all (fun primeData => primeData.checkForPolynomial f) &&
    cert.checkDegreeObstructions f

namespace PrimeFactorData

/--
Kernel-reducible counterpart of `checkCertAtFactor`.

Identical metadata alignment checks, but the nested Rabin certificate is
replayed through `Berlekamp.checkIrreducibilityCertificateLinearIncremental`,
whose pow-chain validation costs `O(n · p)` kernel multiplications per factor
instead of the `O(Σ p^k)` recomputation against the committed
`FpPoly.frobeniusXPowMod`. The incremental comparison is preferred over
`Berlekamp.checkIrreducibilityCertificateLinear` because certificate replay
targets degrees where `p^n` overwhelms any kernel budget while `n · p` stays
cheap.
-/
def checkCertAtFactorLinear
    (d : PrimeFactorData) (degree : Nat) (factor : @FpPoly d.p d.bounds)
    (cert : Berlekamp.IrreducibilityCertificate) : Bool :=
  letI := d.bounds
  decide (cert.p = d.p) &&
    decide (cert.n = degree) &&
    d.containsDegree cert.n &&
    factor.degree? == some degree &&
    if hmonic : factor.leadingCoeff = 1 then
      Berlekamp.checkIrreducibilityCertificateLinearIncremental factor (by exact hmonic) cert
    else
      false

/-- Kernel-reducible counterpart of `checkFactorCerts`, replaying each nested
certificate through `checkCertAtFactorLinear`. -/
def checkFactorCertsLinear (d : PrimeFactorData) : Bool :=
  d.factorDegrees.size == d.factorCerts.size &&
    d.factorDegrees.size == d.factorPolys.size &&
    (d.factorDegrees.toList.zip (d.factorPolys.toList.zip d.factorCerts.toList)).all fun pair =>
      checkCertAtFactorLinear d pair.1 pair.2.1 pair.2.2

/-- Kernel-reducible counterpart of `checkForPolynomial`, replaying the nested
certificates through `checkFactorCertsLinear`. -/
def checkForPolynomialLinear (f : ZPoly) (d : PrimeFactorData) : Bool :=
  letI := d.bounds
  isGoodPrime f d.p &&
    d.factorDegrees.all (fun degree => 0 < degree) &&
    d.degreeSum == (ZPoly.modP d.p f).degree?.getD 0 &&
    d.factorProduct == ZPoly.modP d.p f &&
    d.checkFactorCertsLinear

/--
`checkCertAtFactorLinear` implies `checkCertAtFactor` once the block's prime
is genuinely prime: the two differ only in the nested pow-chain replay, which
`Berlekamp.checkIrreducibilityCertificate_of_linearIncremental` bridges.
-/
theorem checkCertAtFactor_of_linear
    (d : PrimeFactorData) (degree : Nat) (factor : @FpPoly d.p d.bounds)
    (cert : Berlekamp.IrreducibilityCertificate)
    (hp : Hex.Nat.Prime d.p)
    (hcheck : d.checkCertAtFactorLinear degree factor cert = true) :
    d.checkCertAtFactor degree factor cert = true := by
  letI := d.bounds
  letI : ZMod64.PrimeModulus d.p := ZMod64.primeModulusOfPrime hp
  unfold checkCertAtFactorLinear at hcheck
  unfold checkCertAtFactor
  simp only [Bool.and_eq_true] at hcheck ⊢
  rcases hcheck with ⟨hmeta, htail⟩
  refine ⟨hmeta, ?_⟩
  by_cases hmonic : factor.leadingCoeff = 1
  · rw [dif_pos hmonic] at htail ⊢
    exact Berlekamp.checkIrreducibilityCertificate_of_linearIncremental
      factor _ cert htail
  · rw [dif_neg hmonic] at htail
    simp at htail

/-- `checkFactorCertsLinear` implies `checkFactorCerts` once the block's prime
is genuinely prime. -/
theorem checkFactorCerts_of_linear
    (d : PrimeFactorData) (hp : Hex.Nat.Prime d.p)
    (hcheck : d.checkFactorCertsLinear = true) :
    d.checkFactorCerts = true := by
  unfold checkFactorCertsLinear at hcheck
  unfold checkFactorCerts
  simp only [Bool.and_eq_true] at hcheck ⊢
  rcases hcheck with ⟨hsizes, hall⟩
  refine ⟨hsizes, ?_⟩
  rw [List.all_eq_true] at hall ⊢
  intro pair hmem
  exact checkCertAtFactor_of_linear d pair.1 pair.2.1 pair.2.2 hp (hall pair hmem)

/-- `checkForPolynomialLinear` implies `checkForPolynomial` once the block's
prime is genuinely prime. -/
theorem checkForPolynomial_of_linear
    (f : ZPoly) (d : PrimeFactorData) (hp : Hex.Nat.Prime d.p)
    (hcheck : d.checkForPolynomialLinear f = true) :
    d.checkForPolynomial f = true := by
  unfold checkForPolynomialLinear at hcheck
  unfold checkForPolynomial
  simp only [Bool.and_eq_true] at hcheck ⊢
  rcases hcheck with ⟨hmeta, hcerts⟩
  exact ⟨hmeta, checkFactorCerts_of_linear d hp hcerts⟩

end PrimeFactorData

/--
Kernel-reducible counterpart of `checkIrreducibleCert`: the same surface
checks, with every nested Rabin certificate replayed through the incremental
pow-chain checker so `decide` can reduce a literal certificate without
re-running the committed `FpPoly.frobeniusXPowMod` in the kernel.

Consumers discharge this checker on literal certificate data and cross to the
committed checker (hence to `checkIrreducibleCert`'s soundness theorem) via
`checkIrreducibleCert_of_linear`.
-/
def checkIrreducibleCertLinear
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate) : Bool :=
  cert.perPrime.all (fun primeData => primeData.checkForPolynomialLinear f) &&
    cert.checkDegreeObstructions f

/--
The kernel-reducible integer checker implies the committed one, given that
every recorded block prime is genuinely prime. Primality feeds the pow-chain
recurrence `X^(p^(k+1)) ≡ (X^(p^k))^p (mod f)` that identifies the incremental
replay with the committed Frobenius routine.
-/
theorem checkIrreducibleCert_of_linear
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hprime : ∀ primeData ∈ cert.perPrime.toList, Hex.Nat.Prime primeData.p)
    (hcheck : checkIrreducibleCertLinear f cert = true) :
    checkIrreducibleCert f cert = true := by
  unfold checkIrreducibleCertLinear at hcheck
  unfold checkIrreducibleCert
  simp only [Bool.and_eq_true] at hcheck ⊢
  rcases hcheck with ⟨hblocks, hobs⟩
  refine ⟨?_, hobs⟩
  rw [Array.all_eq_true] at hblocks ⊢
  intro i hi
  have hmem : cert.perPrime[i] ∈ cert.perPrime.toList := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simpa using hi, by simp⟩
  exact PrimeFactorData.checkForPolynomial_of_linear f cert.perPrime[i]
    (hprime cert.perPrime[i] hmem) (hblocks i hi)

/--
Rabin certificates for every modular factor at a prime block, aligned with the
factor array. Fails (returns `none`) if any modular factor is non-monic or is
not certified irreducible by `Berlekamp.buildIrreducibilityCertificate?`.
-/
private def buildFactorCerts? {p : Nat} [ZMod64.Bounds p]
    (factors : Array (FpPoly p)) :
    Option (Array Berlekamp.IrreducibilityCertificate) :=
  factors.foldl
    (fun acc g =>
      match acc with
      | none => none
      | some arr =>
        if hmonic : DensePoly.leadingCoeff g = 1 then
          match Berlekamp.buildIrreducibilityCertificate? g hmonic with
          | some cert => some (arr.push cert)
          | none => none
        else
          none)
    (some #[])

/--
Build one prime block for `f` at the small-prime candidate `c`: its recorded
modular factors, their degrees, and one nested Rabin certificate per factor.

The block is returned only when the prime is admissible, every modular factor
is Rabin-certified, and the assembled block self-verifies against `f` through
`PrimeFactorData.checkForPolynomial` (so a block that survives here is exactly
one the kernel checker will accept). This requires the modular image of `f` to
be monic at `c.p`, i.e. `leadingCoeff f ≡ 1 (mod c.p)`; otherwise the recorded
monic factors cannot multiply back to `ZPoly.modP c.p f` and the block is
rejected.
-/
private def buildPrimeFactorData? (f : ZPoly) (c : SmallPrimeCandidate) :
    Option PrimeFactorData :=
  letI := c.bounds
  if isGoodPrime f c.p then
    let factors := berlekampFactorsModP f c
    match buildFactorCerts? factors with
    | none => none
    | some certs =>
      let data : PrimeFactorData :=
        { p := c.p
          factorDegrees := factors.map fun g => g.degree?.getD 0
          factorPolys := factors
          factorCerts := certs }
      if data.checkForPolynomial f then some data else none
  else
    none

/--
Choose, for each nontrivial candidate integer factor degree of `f`, a prime
block whose recorded modular factor degrees have no subset summing to that
degree — the multi-prime degree obstruction that rules out a genuine integer
factor of that degree.

Returns `none` if some candidate degree cannot be obstructed by any of the
supplied blocks. That happens both when `f` really does have an integer factor
of that degree, and — a genuine limitation of this per-prime degree-sum
language — when a degree is un-obstructable because every prime's factorization
admits a subset summing to it. The latter rules out the balanced half-degree
cases (e.g. Swinnerton-Dyer `√2+√3+√5` and `Φ₁₅`, whose `deg/2` obstruction is
never available): the checker cannot certify those irreducibles, so the
generator declines them. It succeeds whenever each target degree has some
admissible obstructing prime — in particular whenever `f` has an inert prime,
whose single block obstructs every proper degree at once.
-/
private def buildDegreeObstructions (f : ZPoly) (blocks : Array PrimeFactorData) :
    Option (Array DegreeObstruction) :=
  (ZPolyIrreducibilityCertificate.candidateFactorDegrees f).foldl
    (fun acc d =>
      match acc with
      | none => none
      | some obs =>
        match (List.range blocks.size).find? fun i =>
          match blocks[i]? with
          | some blk => !blk.hasSubsetDegree d
          | none => false with
        | some i => some (obs.push { targetDegree := d, primeIndex := i })
        | none => none)
    (some #[])

end Hex

import HexBerlekamp.Basic

/-!
Executable irreducibility tests for `hex-berlekamp`.

This module exposes two executable decision procedures over `FpPoly p`:
Berlekamp's rank criterion, phrased via the fixed-space matrix `Q_f - I`, and
Rabin's test, phrased via Frobenius remainders and gcd checks at the maximal
proper divisors of `deg f`.
-/
namespace Hex

namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/-- `X^(p^k) - X` reduced modulo `f`. -/
def frobeniusDiffMod (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat) :
    FpPoly p :=
  FpPoly.frobeniusXPowMod f hmonic k - FpPoly.modByMonic f FpPoly.X hmonic

/--
Positive divisors of `n` below `n`, listed in ascending order.

These are the candidates from which Rabin's test extracts the maximal proper
divisors.
-/
def properDivisors (n : Nat) : List Nat :=
  ((List.range (n - 1)).map Nat.succ).filter fun d => n % d = 0

/--
The maximal proper divisors of `n`, i.e. those proper divisors not strictly
below any other proper divisor of `n`.
-/
def maximalProperDivisors (n : Nat) : List Nat :=
  let ds := properDivisors n
  ds.filter fun d => !(ds.any fun e => d < e && e % d = 0)

/-- `true` exactly when `g` is a nonzero constant polynomial. -/
def isUnitPolynomial (g : FpPoly p) : Bool :=
  match g.degree? with
  | some 0 => true
  | _ => false

/--
Berlekamp's executable rank criterion: a nonconstant monic `f` passes when
`rank(Q_f - I) = deg(f) - 1`.
-/
def berlekampRankTest (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)] : Bool :=
  let n := basisSize f
  decide (0 < n ∧ Matrix.rref_rank (fixedSpaceMatrix f hmonic) = n - 1)

/--
The divisibility leg of Rabin's criterion: `f` divides `X^(p^n) - X`, with
`n = deg(f)`, exactly when the reduced remainder vanishes.
-/
def rabinDividesTest (f : FpPoly p) (hmonic : DensePoly.Monic f) : Bool :=
  let n := basisSize f
  (frobeniusDiffMod f hmonic n).isZero

/--
The gcd leg of Rabin's criterion at a single maximal proper divisor `d` of
`deg(f)`.
-/
def rabinCoprimeTest (f : FpPoly p) (hmonic : DensePoly.Monic f) (d : Nat) : Bool :=
  isUnitPolynomial (DensePoly.gcd f (frobeniusDiffMod f hmonic d))

/--
Record the per-divisor Rabin gcd checks so downstream factorization code can
see which maximal proper divisor rejected a candidate polynomial.
-/
def rabinWitnesses (f : FpPoly p) (hmonic : DensePoly.Monic f) : List (Nat × Bool) :=
  let n := basisSize f
  (maximalProperDivisors n).map fun d => (d, rabinCoprimeTest f hmonic d)

/-- Bezout evidence that one Rabin gcd leg is coprime. -/
structure RabinBezoutWitness (p : Nat) [ZMod64.Bounds p] where
  left : FpPoly p
  right : FpPoly p

/--
Self-describing certificate data for Rabin irreducibility checking.

The `bezout` array is indexed in the same order as `maximalProperDivisors n`.
Each witness proves coprimality of `f` and
`X^(p^d) - X mod f` by the executable identity
`left * f + right * (X^(p^d) - X) = 1`.
-/
structure IrreducibilityCertificate where
  p : Nat
  [bounds : ZMod64.Bounds p]
  n : Nat
  powChain : Array (FpPoly p)
  bezout : Array (RabinBezoutWitness p)

namespace IrreducibilityCertificate

variable (cert : IrreducibilityCertificate)

/-- Read the certified `X^(p^k) mod f` witness, if present. -/
def powWitness? (k : Nat) : Option (@FpPoly cert.p cert.bounds) :=
  cert.powChain[k]?

/-- Read the Bezout witness for the `i`-th maximal proper divisor, if present. -/
def bezoutWitness? (i : Nat) : Option (@RabinBezoutWitness cert.p cert.bounds) :=
  cert.bezout[i]?

end IrreducibilityCertificate

/--
Same-prime view of a self-contained certificate after its stored `p` has been
matched against the ambient field.
-/
structure SamePrimeIrreducibilityCertificate (p : Nat) [ZMod64.Bounds p] where
  n : Nat
  powChain : Array (FpPoly p)
  bezout : Array (RabinBezoutWitness p)

def IrreducibilityCertificate.toAmbient?
    (cert : IrreducibilityCertificate) (p : Nat) [ZMod64.Bounds p] :
    Option (SamePrimeIrreducibilityCertificate p) := by
  match cert with
  | { p := certP, bounds := certBounds, n := n, powChain := powChain, bezout := bezout } =>
      if h : certP = p then
        subst h
        letI := certBounds
        exact some { n := n, powChain := powChain, bezout := bezout }
      else
        exact none

/-- The Rabin difference polynomial represented by a certificate pow-chain entry. -/
def certifiedFrobeniusDiffMod (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (powWitness : FpPoly p) : FpPoly p :=
  powWitness - FpPoly.modByMonic f FpPoly.X hmonic

/-- Check that a certificate's pow chain matches the committed Frobenius routine. -/
def checkPowChain (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate p) : Bool :=
  cert.powChain.size == cert.n + 1 &&
    (List.range (cert.n + 1)).all fun k =>
      cert.powChain[k]? == some (FpPoly.frobeniusXPowMod f hmonic k)

/--
Kernel-reducible pow-chain check for small closed polynomials. It checks the
same mathematical witnesses as `checkPowChain`, but compares against the
structural Frobenius evaluator so `decide` can reduce concrete certificates.
-/
def checkPowChainLinear (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate p) : Bool :=
  cert.powChain.size == cert.n + 1 &&
    (List.range (cert.n + 1)).all fun k =>
      cert.powChain[k]? == some (FpPoly.frobeniusXPowModLinear f hmonic k)

/-- Check one Bezout witness for a Rabin maximal-proper-divisor leg. -/
def checkRabinBezoutWitness (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate p) (i d : Nat) : Bool :=
  match cert.powChain[d]?, cert.bezout[i]? with
  | some powWitness, some witness =>
      let diff := certifiedFrobeniusDiffMod f hmonic powWitness
      witness.left * f + witness.right * diff == 1
  | _, _ => false

/-- Check all Bezout witnesses against `maximalProperDivisors cert.n`. -/
def checkRabinBezoutWitnesses (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate p) : Bool :=
  let divisors := maximalProperDivisors cert.n
  cert.bezout.size == divisors.length &&
    (divisors.zipIdx).all fun pair =>
      checkRabinBezoutWitness f hmonic cert pair.2 pair.1

/--
Executable checker for a Rabin irreducibility certificate.

It validates the self-described `p` and `n`, recomputes every pow-chain
entry, checks the divisibility leg `X^(p^n) = X mod f`, and verifies each
Bezout identity for the maximal proper divisors of `n`.
-/
def checkIrreducibilityCertificate (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate) : Bool :=
  match cert.toAmbient? p with
  | none => false
  | some samePrimeCert =>
      decide (0 < samePrimeCert.n) &&
        decide (samePrimeCert.n = basisSize f) &&
        checkPowChain f hmonic samePrimeCert &&
        (samePrimeCert.powChain[samePrimeCert.n]? == some (FpPoly.modByMonic f FpPoly.X hmonic)) &&
        checkRabinBezoutWitnesses f hmonic samePrimeCert

/--
Kernel-reducible Rabin certificate checker. This is intended for small
record-literal polynomials where the theorem input
`rabinTest f hmonic = true` should be discharged by `decide`.
-/
def checkIrreducibilityCertificateLinear (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate) : Bool :=
  match cert.toAmbient? p with
  | none => false
  | some samePrimeCert =>
      decide (0 < samePrimeCert.n) &&
        decide (samePrimeCert.n = basisSize f) &&
        checkPowChainLinear f hmonic samePrimeCert &&
        (samePrimeCert.powChain[samePrimeCert.n]? == some (FpPoly.modByMonic f FpPoly.X hmonic)) &&
        checkRabinBezoutWitnesses f hmonic samePrimeCert

/--
Rabin's executable irreducibility test: `f` must be nonconstant, divide
`X^(p^n) - X`, and be coprime to `X^(p^d) - X` for every maximal proper
divisor `d` of `n = deg(f)`.
-/
def rabinTest (f : FpPoly p) (hmonic : DensePoly.Monic f) : Bool :=
  let n := basisSize f
  decide (0 < n) &&
    rabinDividesTest f hmonic &&
    (rabinWitnesses f hmonic).all Prod.snd

theorem berlekampRankTest_spec (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)] :
    berlekampRankTest f hmonic = true ↔
      0 < basisSize f ∧
      Matrix.rref_rank (fixedSpaceMatrix f hmonic) = basisSize f - 1 := by
  simp [berlekampRankTest]

theorem rabinDividesTest_spec (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    rabinDividesTest f hmonic =
      (frobeniusDiffMod f hmonic (basisSize f)).isZero := by
  rfl

private theorem zmod64_one_ne_zero_of_prime
    (hp : Hex.Nat.Prime p) :
    (1 : ZMod64 p) ≠ 0 := by
  intro hone
  have hnat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat hone
  change (ZMod64.one : ZMod64 p).toNat = (ZMod64.zero : ZMod64 p).toNat at hnat
  have hp_gt : 1 < p := by
    have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
    omega
  rw [ZMod64.toNat_one, ZMod64.toNat_zero, Nat.mod_eq_of_lt hp_gt] at hnat
  omega

private theorem fp_one_ne_zero [ZMod64.PrimeModulus p] :
    (1 : FpPoly p) ≠ 0 := by
  intro hone
  have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) hone
  change (DensePoly.C (1 : ZMod64 p)).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
  rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
  simp only [if_true] at hcoeff
  exact zmod64_one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) hcoeff

private theorem eq_zero_of_size_eq_zero (f : FpPoly p) (hsize : f.size = 0) :
    f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_zero]
  exact DensePoly.coeff_eq_zero_of_size_le f (by omega)

private theorem isUnitPolynomial_of_dvd_one
    [ZMod64.PrimeModulus p] {g : FpPoly p}
    (hdiv : g ∣ (1 : FpPoly p)) :
    isUnitPolynomial g = true := by
  by_cases hsize : g.size = 0
  · rcases hdiv with ⟨r, hr⟩
    have hg : g = 0 := eq_zero_of_size_eq_zero g hsize
    have hone_zero : (1 : FpPoly p) = 0 := by
      rw [hg] at hr
      simpa using hr
    exact False.elim (fp_one_ne_zero hone_zero)
  · have hnot_pos_degree : ¬ 0 < g.degree?.getD 0 := by
      intro hpos
      have hmod_zero :
          (1 : FpPoly p) % g = 0 :=
        DensePoly.mod_eq_zero_of_dvd (1 : FpPoly p) g hdiv
      have hone_degree : (1 : FpPoly p).degree?.getD 0 = 0 := by
        change (DensePoly.C (1 : ZMod64 p)).degree?.getD 0 = 0
        exact DensePoly.degree?_C_getD (1 : ZMod64 p)
      have hmod_one :
          (1 : FpPoly p) % g = 1 :=
        DensePoly.mod_eq_self_of_degree_lt (1 : FpPoly p) g (by
          rw [hone_degree]
          exact hpos)
      have hone_zero : (1 : FpPoly p) = 0 := by
        rw [hmod_one] at hmod_zero
        exact hmod_zero
      exact fp_one_ne_zero hone_zero
    unfold isUnitPolynomial
    have hdegree_getD : g.degree?.getD 0 = 0 := Nat.eq_zero_of_not_pos hnot_pos_degree
    have hdegree : g.degree? = some 0 := by
      simp [DensePoly.degree?, hsize] at hdegree_getD ⊢
      omega
    rw [hdegree]

private theorem isUnitPolynomial_gcd_of_bezout
    [ZMod64.PrimeModulus p] {f diff left right : FpPoly p}
    (hbezout : left * f + right * diff = 1) :
    isUnitPolynomial (DensePoly.gcd f diff) = true := by
  let g := DensePoly.gcd f diff
  change isUnitPolynomial g = true
  apply isUnitPolynomial_of_dvd_one
  have hgcd_left : g ∣ f := by
    dsimp [g]
    exact DensePoly.gcd_dvd_left f diff
  have hgcd_right : g ∣ diff := by
    dsimp [g]
    exact DensePoly.gcd_dvd_right f diff
  rcases hgcd_left with ⟨a, ha⟩
  rcases hgcd_right with ⟨b, hb⟩
  refine ⟨left * a + right * b, ?_⟩
  have hleft : left * (g * a) = g * (left * a) := by
    calc
      left * (g * a) = (left * g) * a := by
        rw [FpPoly.mul_assoc]
      _ = (g * left) * a := by
        rw [FpPoly.mul_comm left g]
      _ = g * (left * a) := by
        rw [FpPoly.mul_assoc]
  have hright : right * (g * b) = g * (right * b) := by
    calc
      right * (g * b) = (right * g) * b := by
        rw [FpPoly.mul_assoc]
      _ = (g * right) * b := by
        rw [FpPoly.mul_comm right g]
      _ = g * (right * b) := by
        rw [FpPoly.mul_assoc]
  calc
    (1 : FpPoly p) = left * f + right * diff := hbezout.symm
    _ = left * (g * a) + right * (g * b) := by
          rw [ha, hb]
    _ = g * (left * a) + g * (right * b) := by
          rw [hleft, hright]
    _ = g * (left * a + right * b) := by
          exact (FpPoly.left_distrib g (left * a) (right * b)).symm

private theorem checkRabinBezoutWitness_rabinCoprimeTest
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate p) (i d : Nat)
    (hcheck : checkRabinBezoutWitness f hmonic cert i d = true)
    (hpow : cert.powChain[d]? = some (FpPoly.frobeniusXPowMod f hmonic d)) :
    rabinCoprimeTest f hmonic d = true := by
  unfold checkRabinBezoutWitness at hcheck
  rw [hpow] at hcheck
  cases hbezoutOpt : cert.bezout[i]? with
  | none =>
      simp [hbezoutOpt] at hcheck
  | some witness =>
      simp [hbezoutOpt] at hcheck
      unfold rabinCoprimeTest frobeniusDiffMod
      exact isUnitPolynomial_gcd_of_bezout hcheck

private theorem List.all_map_pair_snd {α : Type u} (xs : List α) (p : α → Bool) :
    (xs.map fun x => (x, p x)).all Prod.snd = xs.all p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [ih]

private theorem mem_properDivisors_le {n d : Nat} (hmem : d ∈ properDivisors n) :
    d ≤ n := by
  unfold properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range] at hmem
  rcases hmem with ⟨⟨k, hk, rfl⟩, _⟩
  omega

private theorem mem_maximalProperDivisors_le {n d : Nat}
    (hmem : d ∈ maximalProperDivisors n) :
    d ≤ n := by
  unfold maximalProperDivisors at hmem
  simp only [List.mem_filter] at hmem
  exact mem_properDivisors_le hmem.1

private theorem checkRabinBezoutWitnesses_rabinWitnesses_all
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate p)
    (hcheck : checkRabinBezoutWitnesses f hmonic cert = true)
    (hpow : ∀ k, k ≤ cert.n →
      cert.powChain[k]? = some (FpPoly.frobeniusXPowMod f hmonic k))
    (hn : cert.n = basisSize f) :
    (rabinWitnesses f hmonic).all Prod.snd = true := by
  unfold checkRabinBezoutWitnesses at hcheck
  simp only [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_hsize, hall⟩
  unfold rabinWitnesses
  rw [← hn]
  let ds := maximalProperDivisors cert.n
  change (ds.map fun d => (d, rabinCoprimeTest f hmonic d)).all Prod.snd = true
  rw [List.all_map_pair_snd]
  change ds.all (fun d => rabinCoprimeTest f hmonic d) = true
  have hds :
      ∀ (xs : List Nat) start,
        (∀ d, d ∈ xs → d ∈ maximalProperDivisors cert.n) →
        (xs.zipIdx start).all
            (fun pair => checkRabinBezoutWitness f hmonic cert pair.2 pair.1) = true →
        xs.all (fun d => rabinCoprimeTest f hmonic d) = true := by
    clear hall
    intro xs
    induction xs with
    | nil =>
        intro start _hmem _hall
        rfl
    | cons d ds ih =>
        intro start hmem hall
        simp only [List.zipIdx_cons, List.all_cons, Bool.and_eq_true] at hall ⊢
        rcases hall with ⟨hd, htail⟩
        constructor
        · apply checkRabinBezoutWitness_rabinCoprimeTest f hmonic cert start d hd
          apply hpow
          apply mem_maximalProperDivisors_le
          exact hmem d (by simp)
        · exact ih (start + 1) (fun e he => hmem e (by simp [he])) htail
  exact hds ds 0 (fun d hmem => hmem) hall

theorem checkPowChain_spec
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate p) :
    checkPowChain f hmonic cert = true →
      ∀ k, k ≤ cert.n →
        cert.powChain[k]? = some (FpPoly.frobeniusXPowMod f hmonic k) := by
  intro hcheck k hk
  unfold checkPowChain at hcheck
  simp only [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_hsize, hall⟩
  have hmem : k ∈ List.range (cert.n + 1) := by
    simpa [List.mem_range] using Nat.lt_succ_of_le hk
  have hbeq :
      (cert.powChain[k]? == some (FpPoly.frobeniusXPowMod f hmonic k)) = true :=
    List.all_eq_true.mp hall k hmem
  simpa using hbeq

theorem checkPowChainLinear_spec
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate p) :
    checkPowChainLinear f hmonic cert = true →
      ∀ k, k ≤ cert.n →
        cert.powChain[k]? = some (FpPoly.frobeniusXPowMod f hmonic k) := by
  intro hcheck k hk
  unfold checkPowChainLinear at hcheck
  simp only [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_hsize, hall⟩
  have hmem : k ∈ List.range (cert.n + 1) := by
    simpa [List.mem_range] using Nat.lt_succ_of_le hk
  have hbeq :
      (cert.powChain[k]? == some (FpPoly.frobeniusXPowModLinear f hmonic k)) = true :=
    List.all_eq_true.mp hall k hmem
  have hlinear :
      cert.powChain[k]? = some (FpPoly.frobeniusXPowModLinear f hmonic k) := by
    simpa using hbeq
  rw [hlinear, FpPoly.frobeniusXPowModLinear_eq_frobeniusXPowMod]

/--
Shared closing step for the three `checkIrreducibilityCertificate*_rabinTest`
theorems: assemble `rabinTest f hmonic = true` from a verified pow chain, a
matching divisibility witness, and the Bezout-witness check.
-/
private theorem rabinTest_of_powChain_spec
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate p)
    (hnpos : 0 < cert.n) (hn : cert.n = basisSize f)
    (hpow : ∀ k, k ≤ cert.n →
      cert.powChain[k]? = some (FpPoly.frobeniusXPowMod f hmonic k))
    (hdividesWitness :
      cert.powChain[cert.n]? = some (FpPoly.modByMonic f FpPoly.X hmonic))
    (hwitnesses : checkRabinBezoutWitnesses f hmonic cert = true) :
    rabinTest f hmonic = true := by
  simp only [rabinTest, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [hn] using hnpos
  · unfold rabinDividesTest frobeniusDiffMod
    have hpowN := hpow cert.n (Nat.le_refl _)
    rw [hpowN] at hdividesWitness
    simp at hdividesWitness
    rw [← hn, ← hdividesWitness]
    change (FpPoly.frobeniusXPowMod f hmonic cert.n -
        FpPoly.frobeniusXPowMod f hmonic cert.n).isZero = true
    rw [FpPoly.sub_self]
    rfl
  · exact checkRabinBezoutWitnesses_rabinWitnesses_all
      f hmonic cert hwitnesses hpow hn

theorem checkIrreducibilityCertificate_rabinTest
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate) :
    checkIrreducibilityCertificate f hmonic cert = true →
      rabinTest f hmonic = true := by
  intro hcheck
  unfold checkIrreducibilityCertificate at hcheck
  cases hambient : cert.toAmbient? p with
  | none =>
      simp [hambient] at hcheck
  | some samePrimeCert =>
      have hparts :
          (((0 < samePrimeCert.n ∧ samePrimeCert.n = basisSize f) ∧
              checkPowChain f hmonic samePrimeCert = true) ∧
              samePrimeCert.powChain[samePrimeCert.n]? =
                some (FpPoly.modByMonic f FpPoly.X hmonic)) ∧
            checkRabinBezoutWitnesses f hmonic samePrimeCert = true := by
        simpa [checkIrreducibilityCertificate, hambient, Bool.and_eq_true] using hcheck
      rcases hparts with ⟨⟨⟨⟨hnpos, hn⟩, hpowCheck⟩, hdividesWitness⟩, hwitnesses⟩
      exact rabinTest_of_powChain_spec f hmonic samePrimeCert hnpos hn
        (checkPowChain_spec f hmonic samePrimeCert hpowCheck)
        hdividesWitness hwitnesses

theorem checkIrreducibilityCertificateLinear_rabinTest
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate) :
    checkIrreducibilityCertificateLinear f hmonic cert = true →
      rabinTest f hmonic = true := by
  intro hcheck
  unfold checkIrreducibilityCertificateLinear at hcheck
  cases hambient : cert.toAmbient? p with
  | none =>
      simp [hambient] at hcheck
  | some samePrimeCert =>
      have hparts :
          (((0 < samePrimeCert.n ∧ samePrimeCert.n = basisSize f) ∧
              checkPowChainLinear f hmonic samePrimeCert = true) ∧
              samePrimeCert.powChain[samePrimeCert.n]? =
                some (FpPoly.modByMonic f FpPoly.X hmonic)) ∧
            checkRabinBezoutWitnesses f hmonic samePrimeCert = true := by
        simpa [checkIrreducibilityCertificateLinear, hambient, Bool.and_eq_true] using hcheck
      rcases hparts with ⟨⟨⟨⟨hnpos, hn⟩, hpowCheck⟩, hdividesWitness⟩, hwitnesses⟩
      exact rabinTest_of_powChain_spec f hmonic samePrimeCert hnpos hn
        (checkPowChainLinear_spec f hmonic samePrimeCert hpowCheck)
        hdividesWitness hwitnesses

/-! ### Incremental pow-chain check

`checkPowChainLinear` re-evaluates each `cert.powChain[k]` from scratch via
`FpPoly.frobeniusXPowModLinear`, which expands to `p^k` modular
multiplications.  For `(p, n) = (5, 6)` or `(7, 6)` that is far beyond
practical kernel-reduction budgets.  The incremental version below uses the
chain identity
`X^(p^(k+1)) mod f = (X^(p^k) mod f)^p mod f`
(`FpPoly.frobeniusXPowMod_succ`) so that each step costs only `p`
multiplications, dropping the total work from `Σ p^k` to `n · p`. -/

/--
The single-step recurrence: `powChain[k+1]` must equal
`(powChain[k])^p mod f`.
-/
def checkPowChainLinearIncrementalStep
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate p) (k : Nat) : Bool :=
  match cert.powChain[k]?, cert.powChain[k+1]? with
  | some prev, some next => next == FpPoly.powModMonicLinear prev f hmonic p
  | _, _ => false

/--
Kernel-reducible incremental pow-chain check.  Validates that
`powChain[0] = X mod f` and that each successor is the previous entry's
`p`-th power modulo `f`.  Total work is `O(n · p)` instead of `O(Σ p^k)`.
-/
def checkPowChainLinearIncremental (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate p) : Bool :=
  cert.powChain.size == cert.n + 1 &&
    (cert.powChain[0]? == some (FpPoly.modByMonic f FpPoly.X hmonic)) &&
    (List.range cert.n).all fun k =>
      checkPowChainLinearIncrementalStep f hmonic cert k

/--
Incremental Rabin certificate checker, suitable for `(p, n)` regimes where
`p^n` is too large for `checkIrreducibilityCertificateLinear` but `n · p`
remains in budget (e.g. `(5, 6)` or `(7, 6)`).
-/
def checkIrreducibilityCertificateLinearIncremental
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate) : Bool :=
  match cert.toAmbient? p with
  | none => false
  | some samePrimeCert =>
      decide (0 < samePrimeCert.n) &&
        decide (samePrimeCert.n = basisSize f) &&
        checkPowChainLinearIncremental f hmonic samePrimeCert &&
        (samePrimeCert.powChain[samePrimeCert.n]? == some (FpPoly.modByMonic f FpPoly.X hmonic)) &&
        checkRabinBezoutWitnesses f hmonic samePrimeCert

theorem checkPowChainLinearIncremental_spec
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate p) :
    checkPowChainLinearIncremental f hmonic cert = true →
      ∀ k, k ≤ cert.n →
        cert.powChain[k]? = some (FpPoly.frobeniusXPowMod f hmonic k) := by
  intro hcheck
  unfold checkPowChainLinearIncremental at hcheck
  simp only [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨⟨_hsize, hzero⟩, hsteps⟩
  have hzero' : cert.powChain[0]? = some (FpPoly.modByMonic f FpPoly.X hmonic) := by
    simpa using hzero
  intro k hk
  induction k with
  | zero =>
      rw [hzero', FpPoly.frobeniusXPowMod_zero]
  | succ j ih =>
      have hj_le : j ≤ cert.n := Nat.le_of_succ_le hk
      have hj : j < cert.n := Nat.lt_of_succ_le hk
      have hih : cert.powChain[j]? = some (FpPoly.frobeniusXPowMod f hmonic j) :=
        ih hj_le
      have hmem : j ∈ List.range cert.n := List.mem_range.mpr hj
      have hstep : checkPowChainLinearIncrementalStep f hmonic cert j = true :=
        List.all_eq_true.mp hsteps j hmem
      unfold checkPowChainLinearIncrementalStep at hstep
      rw [hih] at hstep
      cases hnext : cert.powChain[j+1]? with
      | none =>
          rw [hnext] at hstep
          simp at hstep
      | some next =>
          rw [hnext] at hstep
          have heq :
              next = FpPoly.powModMonicLinear
                (FpPoly.frobeniusXPowMod f hmonic j) f hmonic p := by
            simpa using hstep
          rw [heq, FpPoly.powModMonicLinear_eq_powModMonic,
              ← FpPoly.frobeniusXPowMod_succ]

theorem checkIrreducibilityCertificateLinearIncremental_rabinTest
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate) :
    checkIrreducibilityCertificateLinearIncremental f hmonic cert = true →
      rabinTest f hmonic = true := by
  intro hcheck
  unfold checkIrreducibilityCertificateLinearIncremental at hcheck
  cases hambient : cert.toAmbient? p with
  | none =>
      simp [hambient] at hcheck
  | some samePrimeCert =>
      have hparts :
          (((0 < samePrimeCert.n ∧ samePrimeCert.n = basisSize f) ∧
              checkPowChainLinearIncremental f hmonic samePrimeCert = true) ∧
              samePrimeCert.powChain[samePrimeCert.n]? =
                some (FpPoly.modByMonic f FpPoly.X hmonic)) ∧
            checkRabinBezoutWitnesses f hmonic samePrimeCert = true := by
        simpa [checkIrreducibilityCertificateLinearIncremental, hambient,
          Bool.and_eq_true] using hcheck
      rcases hparts with ⟨⟨⟨⟨hnpos, hn⟩, hpowCheck⟩, hdividesWitness⟩, hwitnesses⟩
      exact rabinTest_of_powChain_spec f hmonic samePrimeCert hnpos hn
        (checkPowChainLinearIncremental_spec f hmonic samePrimeCert hpowCheck)
        hdividesWitness hwitnesses

end Berlekamp

end Hex

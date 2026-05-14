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

/--
Match a certificate's stored prime against the ambient `p`. Returns the
same-prime view on success, or `none` if the certificate is for a different
prime.
-/
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

/-- `berlekampRankTest` succeeds exactly when the fixed-space matrix has rank
`deg(f) - 1`, the Berlekamp rank criterion. -/
theorem berlekampRankTest_spec (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)] :
    berlekampRankTest f hmonic = true ↔
      0 < basisSize f ∧
      Matrix.rref_rank (fixedSpaceMatrix f hmonic) = basisSize f - 1 := by
  simp [berlekampRankTest]

/-- `rabinDividesTest` reduces to checking that `frobeniusDiffMod f _ n`
vanishes, where `n = deg(f)`. -/
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

/-- If `checkPowChain` accepts, every entry `cert.powChain[k]` (for `k ≤ cert.n`)
agrees with the committed Frobenius routine `FpPoly.frobeniusXPowMod`. -/
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

/-- Linear-kernel companion to `checkPowChain_spec`: if `checkPowChainLinear`
accepts, every entry agrees with `FpPoly.frobeniusXPowMod`, after rewriting
the structural Frobenius evaluator through
`FpPoly.frobeniusXPowModLinear_eq_frobeniusXPowMod`. -/
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

/-- If `checkIrreducibilityCertificate` accepts a self-describing certificate,
the corresponding `rabinTest` succeeds. Downstream irreducibility soundness
(`FpPoly.Irreducible`) is then chained via
`HexBerlekamp.RabinSoundness.rabinTest_imp_irreducible`. -/
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

/-- Kernel-reducible counterpart of `checkIrreducibilityCertificate_rabinTest`,
suited to `decide`-discharged certificates over small concrete polynomials. -/
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
Quotient-witness checker for `FpPoly 2` pow chains.  Entry `k` of
`quotients` certifies
`powChain[k] * powChain[k] = powChain[k+1] + quotients[k] * f`, with both
chain entries already reduced modulo `f`.
-/
def checkPowChainLinearIncrementalQuotientWitnessStep
    (f : FpPoly 2) (cert : SamePrimeIrreducibilityCertificate 2)
    (quotients : Array (FpPoly 2)) (k : Nat) : Bool :=
  match cert.powChain[k]?, cert.powChain[k + 1]?, quotients[k]? with
  | some prev, some curr, some quot =>
      decide (prev.degree?.getD 0 < f.degree?.getD 0) &&
        (decide (curr.degree?.getD 0 < f.degree?.getD 0) &&
          ((prev * prev).coeffs == (curr + quot * f).coeffs))
  | _, _, _ => false

theorem checkPowChainLinearIncrementalQuotientWitnessStep_of_entries
    (f prev curr quot : FpPoly 2)
    (cert : SamePrimeIrreducibilityCertificate 2)
    (quotients : Array (FpPoly 2)) (k : Nat)
    (hprev : cert.powChain[k]? = some prev)
    (hcurr : cert.powChain[k + 1]? = some curr)
    (hquot : quotients[k]? = some quot)
    (hprevRed : prev.degree?.getD 0 < f.degree?.getD 0)
    (hcurrRed : curr.degree?.getD 0 < f.degree?.getD 0)
    (hmulCoeffs : (prev * prev).coeffs = (curr + quot * f).coeffs) :
    checkPowChainLinearIncrementalQuotientWitnessStep f cert quotients k = true := by
  unfold checkPowChainLinearIncrementalQuotientWitnessStep
  rw [hprev, hcurr, hquot]
  simp [hprevRed, hcurrRed, hmulCoeffs]

theorem checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_bools
    (f prev curr quot : FpPoly 2)
    (cert : SamePrimeIrreducibilityCertificate 2)
    (quotients : Array (FpPoly 2)) (k : Nat)
    (hprev : cert.powChain[k]? = some prev)
    (hcurr : cert.powChain[k + 1]? = some curr)
    (hquot : quotients[k]? = some quot)
    (hprevRed : decide (prev.degree?.getD 0 < f.degree?.getD 0) = true)
    (hcurrRed : decide (curr.degree?.getD 0 < f.degree?.getD 0) = true)
    (hmulCoeffs : ((prev * prev).coeffs == (curr + quot * f).coeffs) = true) :
    checkPowChainLinearIncrementalQuotientWitnessStep f cert quotients k = true := by
  apply checkPowChainLinearIncrementalQuotientWitnessStep_of_entries
      (prev := prev) (curr := curr) (quot := quot)
  · exact hprev
  · exact hcurr
  · exact hquot
  · exact of_decide_eq_true hprevRed
  · exact of_decide_eq_true hcurrRed
  · exact eq_of_beq hmulCoeffs

theorem degree?_getD_lt_of_size_le
    {R : Type u} [Zero R] [DecidableEq R] (g : DensePoly R) {n : Nat}
    (hnpos : 0 < n) (hsize : g.size ≤ n) :
    g.degree?.getD 0 < n := by
  unfold DensePoly.degree?
  by_cases hzero : g.size = 0
  · simp [hzero, hnpos]
  · simp [hzero]
    omega

theorem checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (f prev curr quot : FpPoly 2)
    (cert : SamePrimeIrreducibilityCertificate 2)
    (quotients : Array (FpPoly 2)) (k : Nat)
    (hprev : cert.powChain[k]? = some prev)
    (hcurr : cert.powChain[k + 1]? = some curr)
    (hquot : quotients[k]? = some quot)
    (hfpos : 0 < f.degree?.getD 0)
    (hprevSize : prev.size ≤ f.degree?.getD 0)
    (hcurrSize : curr.size ≤ f.degree?.getD 0)
    (hmulCoeffs : (prev * prev).coeffs = (curr + quot * f).coeffs) :
    checkPowChainLinearIncrementalQuotientWitnessStep f cert quotients k = true := by
  apply checkPowChainLinearIncrementalQuotientWitnessStep_of_entries
      (prev := prev) (curr := curr) (quot := quot)
  · exact hprev
  · exact hcurr
  · exact hquot
  · exact degree?_getD_lt_of_size_le prev hfpos hprevSize
  · exact degree?_getD_lt_of_size_le curr hfpos hcurrSize
  · exact hmulCoeffs

def gf2BitCoeff (bits : UInt64) (i : Nat) : ZMod64 2 :=
  if (((bits >>> i.toUInt64) &&& 1) = 0) then
    0
  else
    1

def gf2WordPoly (bits : UInt64) (width : Nat) : FpPoly 2 :=
  FpPoly.ofCoeffs (((List.range width).map fun i => gf2BitCoeff bits i).toArray)

theorem gf2WordPoly_size_le (bits : UInt64) (width : Nat) :
    (gf2WordPoly bits width).size ≤ width := by
  unfold gf2WordPoly FpPoly.ofCoeffs
  exact Nat.le_trans (DensePoly.size_ofCoeffs_le _) (by simp)

theorem gf2WordPoly_degree?_getD_lt
    (bits : UInt64) {width bound : Nat} (hwidth_pos : 0 < bound)
    (hwidth : width ≤ bound) :
    (gf2WordPoly bits width).degree?.getD 0 < bound :=
  degree?_getD_lt_of_size_le (gf2WordPoly bits width) hwidth_pos
    (Nat.le_trans (gf2WordPoly_size_le bits width) hwidth)

theorem gf2WordPoly_coeff (bits : UInt64) (width i : Nat) :
    (gf2WordPoly bits width).coeff i =
      if i < width then gf2BitCoeff bits i else 0 := by
  unfold gf2WordPoly FpPoly.ofCoeffs gf2BitCoeff
  rw [DensePoly.coeff_ofCoeffs]
  by_cases hi : i < width
  · simp [Array.getD, hi]
  · simp [Array.getD, hi]
    rfl

def coeffsEqUpTo (bound : Nat) (a b : FpPoly 2) : Bool :=
  (List.range bound).all fun i => a.coeff i == b.coeff i

def quotientStepCoeffCheck
    (bound : Nat) (prev curr quot f : FpPoly 2) : Bool :=
  coeffsEqUpTo bound (prev * prev) (curr + quot * f)

theorem coeff_eq_of_coeffsEqUpTo
    {bound : Nat} {a b : FpPoly 2}
    (h : coeffsEqUpTo bound a b = true) :
    ∀ i, i < bound → a.coeff i = b.coeff i := by
  intro i hi
  unfold coeffsEqUpTo at h
  have hmem : i ∈ List.range bound := List.mem_range.mpr hi
  have hbool := List.all_eq_true.mp h i hmem
  exact eq_of_beq hbool

theorem coeffs_eq_of_size_le_of_coeff_eq
    {bound : Nat} {a b : FpPoly 2}
    (ha : a.size ≤ bound) (hb : b.size ≤ bound)
    (hcoeff : ∀ i, i < bound → a.coeff i = b.coeff i) :
    a.coeffs = b.coeffs := by
  have hpoly : a = b := by
    apply DensePoly.ext_coeff
    intro i
    by_cases hi : i < bound
    · exact hcoeff i hi
    · rw [DensePoly.coeff_eq_zero_of_size_le a (by omega : a.size ≤ i),
        DensePoly.coeff_eq_zero_of_size_le b (by omega : b.size ≤ i)]
  exact congrArg DensePoly.coeffs hpoly

theorem coeffs_eq_of_size_le_of_coeffsEqUpTo
    {bound : Nat} {a b : FpPoly 2}
    (ha : a.size ≤ bound) (hb : b.size ≤ bound)
    (h : coeffsEqUpTo bound a b = true) :
    a.coeffs = b.coeffs :=
  coeffs_eq_of_size_le_of_coeff_eq ha hb (coeff_eq_of_coeffsEqUpTo h)

theorem quotientStep_coeffs_eq_of_check
    {bound : Nat} {prev curr quot f : FpPoly 2}
    (hleft : (prev * prev).size ≤ bound)
    (hright : (curr + quot * f).size ≤ bound)
    (hcheck : quotientStepCoeffCheck bound prev curr quot f = true) :
    (prev * prev).coeffs = (curr + quot * f).coeffs := by
  unfold quotientStepCoeffCheck at hcheck
  exact coeffs_eq_of_size_le_of_coeffsEqUpTo hleft hright hcheck

def gf2WordQuotientStepCoeffCheck
    (bound width : Nat) (prevBits currBits quotBits fBits : UInt64) : Bool :=
  quotientStepCoeffCheck bound
    (gf2WordPoly prevBits width)
    (gf2WordPoly currBits width)
    (gf2WordPoly quotBits width)
    (gf2WordPoly fBits width)

theorem gf2WordQuotientStep_coeffs_eq_of_check
    {bound width : Nat} {prevBits currBits quotBits fBits : UInt64}
    (hleft :
      (gf2WordPoly prevBits width * gf2WordPoly prevBits width).size ≤ bound)
    (hright :
      (gf2WordPoly currBits width +
        gf2WordPoly quotBits width * gf2WordPoly fBits width).size ≤ bound)
    (hcheck :
      gf2WordQuotientStepCoeffCheck bound width prevBits currBits quotBits fBits =
        true) :
    (gf2WordPoly prevBits width * gf2WordPoly prevBits width).coeffs =
      (gf2WordPoly currBits width +
        gf2WordPoly quotBits width * gf2WordPoly fBits width).coeffs := by
  apply quotientStep_coeffs_eq_of_check (bound := bound)
  · exact hleft
  · exact hright
  · exact hcheck

private theorem densePoly_eq_of_coeffs_eq
    {R : Type u} [Zero R] [DecidableEq R] {a b : DensePoly R}
    (h : a.coeffs = b.coeffs) : a = b := by
  cases a with
  | mk acoeffs anorm =>
      cases b with
      | mk bcoeffs bnorm =>
          simp only at h
          subst h
          rfl

theorem checkPowChainLinearIncrementalQuotientWitnesses_first_of_coeffs
    (f first : FpPoly 2) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate 2)
    (hfirst : cert.powChain[0]? = some first)
    (hcoeffs : first.coeffs = (FpPoly.modByMonic f FpPoly.X hmonic).coeffs) :
    cert.powChain[0]? == some (FpPoly.modByMonic f FpPoly.X hmonic) := by
  have hpoly : first = FpPoly.modByMonic f FpPoly.X hmonic :=
    densePoly_eq_of_coeffs_eq hcoeffs
  rw [hfirst, hpoly]
  simp

theorem checkPowChainLinearIncrementalQuotientWitnesses_first_of_coeffs_beq
    (f first : FpPoly 2) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate 2)
    (hfirst : cert.powChain[0]? = some first)
    (hcoeffs : (first.coeffs == (FpPoly.modByMonic f FpPoly.X hmonic).coeffs) = true) :
    cert.powChain[0]? == some (FpPoly.modByMonic f FpPoly.X hmonic) :=
  checkPowChainLinearIncrementalQuotientWitnesses_first_of_coeffs
    f first hmonic cert hfirst (eq_of_beq hcoeffs)

private theorem checkPowChainLinearIncrementalQuotientWitnessStep_zero_pilot :
    let zero : FpPoly 2 := 0
    let cert : SamePrimeIrreducibilityCertificate 2 :=
      { n := 1, powChain := #[zero, zero], bezout := #[] }
    checkPowChainLinearIncrementalQuotientWitnessStep FpPoly.X cert #[zero] 0 = true := by
  apply checkPowChainLinearIncrementalQuotientWitnessStep_of_entries
    (prev := (0 : FpPoly 2)) (curr := (0 : FpPoly 2)) (quot := (0 : FpPoly 2))
  · rfl
  · rfl
  · rfl
  · decide
  · decide
  · rfl

private theorem checkPowChainLinearIncrementalQuotientWitnessStep_zero_bool_pilot :
    let zero : FpPoly 2 := 0
    let cert : SamePrimeIrreducibilityCertificate 2 :=
      { n := 1, powChain := #[zero, zero], bezout := #[] }
    checkPowChainLinearIncrementalQuotientWitnessStep FpPoly.X cert #[zero] 0 = true := by
  apply checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_bools
    (prev := (0 : FpPoly 2)) (curr := (0 : FpPoly 2)) (quot := (0 : FpPoly 2))
  · rfl
  · rfl
  · rfl
  · decide
  · decide
  · rfl

def checkPowChainLinearIncrementalQuotientWitnesses
    (f : FpPoly 2) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate 2) (quotients : Array (FpPoly 2)) :
    Bool :=
  cert.powChain.size == cert.n + 1 &&
    quotients.size == cert.n &&
    (cert.powChain[0]? == some (FpPoly.modByMonic f FpPoly.X hmonic)) &&
    (List.range cert.n).all fun k =>
      checkPowChainLinearIncrementalQuotientWitnessStep f cert quotients k

theorem checkPowChainLinearIncrementalQuotientWitnesses_of_steps
    (f : FpPoly 2) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate 2) (quotients : Array (FpPoly 2))
    (hpowSize : cert.powChain.size == cert.n + 1)
    (hquotSize : quotients.size == cert.n)
    (hfirst : cert.powChain[0]? == some (FpPoly.modByMonic f FpPoly.X hmonic))
    (hsteps : ∀ k, k < cert.n →
      checkPowChainLinearIncrementalQuotientWitnessStep f cert quotients k = true) :
    checkPowChainLinearIncrementalQuotientWitnesses f hmonic cert quotients = true := by
  unfold checkPowChainLinearIncrementalQuotientWitnesses
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨hpowSize, hquotSize⟩, hfirst⟩, ?_⟩
  rw [List.all_eq_true]
  intro k hk
  exact hsteps k (List.mem_range.mp hk)

private def primeTwo : Hex.Nat.Prime 2 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · simp at hm
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem powModMonicLinear_two_eq_of_quotientWitness
    (f prev curr quot : FpPoly 2) (hmonic : DensePoly.Monic f)
    (hprevRed : prev.degree?.getD 0 < f.degree?.getD 0)
    (hcurrRed : curr.degree?.getD 0 < f.degree?.getD 0)
    (hmul : prev * prev = curr + quot * f) :
    FpPoly.powModMonicLinear prev f hmonic 2 = curr := by
  letI : ZMod64.PrimeModulus 2 := ZMod64.primeModulusOfPrime primeTwo
  letI : DensePoly.DivModLaws (ZMod64 2) := ZMod64.instDivModLawsZMod64Fp 2
  have hprevMod : prev % f = prev :=
    DensePoly.mod_eq_self_of_degree_lt prev f hprevRed
  have hcurrMod : curr % f = curr :=
    DensePoly.mod_eq_self_of_degree_lt curr f hcurrRed
  have hquotMod : (quot * f) % f = 0 :=
    DensePoly.mod_eq_zero_of_dvd (quot * f) f ⟨quot, (FpPoly.mul_comm f quot).symm⟩
  have hsquareMod : (prev * prev) % f = curr := by
    rw [hmul]
    rw [DensePoly.DivModLaws.mod_add_mod curr (quot * f) f]
    rw [hcurrMod, hquotMod]
    rw [FpPoly.add_zero]
    exact hcurrMod
  unfold FpPoly.powModMonicLinear
  change FpPoly.modByMonic f (FpPoly.modByMonic f (1 * prev) hmonic * prev) hmonic =
    curr
  simp only [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod, FpPoly.one_mul, hprevMod]
  exact hsquareMod

theorem checkPowChainLinearIncremental_of_quotientWitnesses
    (f : FpPoly 2) (hmonic : DensePoly.Monic f)
    (cert : SamePrimeIrreducibilityCertificate 2) (quotients : Array (FpPoly 2)) :
    checkPowChainLinearIncrementalQuotientWitnesses f hmonic cert quotients = true →
      checkPowChainLinearIncremental f hmonic cert = true := by
  intro h
  unfold checkPowChainLinearIncrementalQuotientWitnesses at h
  unfold checkPowChainLinearIncremental
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨hsize, _hquotSize⟩, hfirst⟩, hsteps⟩ := h
  refine ⟨⟨hsize, hfirst⟩, ?_⟩
  rw [List.all_eq_true]
  intro k hk
  have hstep := List.all_eq_true.mp hsteps k hk
  unfold checkPowChainLinearIncrementalStep
  unfold checkPowChainLinearIncrementalQuotientWitnessStep at hstep
  cases hprev : cert.powChain[k]? with
  | none =>
      rw [hprev] at hstep
      exact False.elim (Bool.noConfusion hstep)
  | some prev =>
      cases hcurr : cert.powChain[k + 1]? with
      | none =>
          rw [hprev, hcurr] at hstep
          exact False.elim (Bool.noConfusion hstep)
      | some curr =>
          cases hquot : quotients[k]? with
          | none =>
              rw [hprev, hcurr, hquot] at hstep
              exact False.elim (Bool.noConfusion hstep)
          | some quot =>
              rw [hprev, hcurr, hquot] at hstep
              have hparts :
                  decide (prev.degree?.getD 0 < f.degree?.getD 0) = true ∧
                    (decide (curr.degree?.getD 0 < f.degree?.getD 0) &&
                      ((prev * prev).coeffs == (curr + quot * f).coeffs)) = true := by
                simpa only [Bool.and_eq_true] using hstep
              have hprevRedBool := hparts.1
              have hrest := hparts.2
              have hrestParts :
                  decide (curr.degree?.getD 0 < f.degree?.getD 0) = true ∧
                    ((prev * prev).coeffs == (curr + quot * f).coeffs) = true := by
                simpa only [Bool.and_eq_true] using hrest
              have hcurrRedBool := hrestParts.1
              have hmulCoeffsBool := hrestParts.2
              have hprevRed : prev.degree?.getD 0 < f.degree?.getD 0 :=
                of_decide_eq_true hprevRedBool
              have hcurrRed : curr.degree?.getD 0 < f.degree?.getD 0 :=
                of_decide_eq_true hcurrRedBool
              have hmulCoeffs : (prev * prev).coeffs = (curr + quot * f).coeffs :=
                eq_of_beq hmulCoeffsBool
              have hmul : prev * prev = curr + quot * f := by
                exact densePoly_eq_of_coeffs_eq hmulCoeffs
              have hpow := powModMonicLinear_two_eq_of_quotientWitness
                f prev curr quot hmonic hprevRed hcurrRed hmul
              simp [hpow]

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

/-- Incremental companion to `checkPowChain_spec`: if
`checkPowChainLinearIncremental` accepts, every entry agrees with
`FpPoly.frobeniusXPowMod`. The proof inducts on `k`, using the chain
identity `X^(p^(k+1)) ≡ (X^(p^k))^p (mod f)`. -/
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

/-- Incremental counterpart of `checkIrreducibilityCertificate_rabinTest`,
suited to `(p, n)` regimes where the per-step `O(n · p)` cost fits the
`decide` kernel budget but the bulk `O(Σ p^k)` of the non-incremental
checker does not. -/
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

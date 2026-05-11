import HexGF2.Euclid

/-!
Executable Rabin-style irreducibility certificate checker for packed `GF(2)`
polynomials.

This module mirrors the structure of `HexBerlekamp/Irreducibility.lean` but
operates over the packed `GF2Poly` representation. The certificate stores a
precomputed Frobenius pow chain `X^(2^k) mod f` for `k = 0..n` together with
Bezout witnesses for each maximal proper divisor of `n = deg f`, and the
checker validates the chain by per-step squaring and the legs by Bezout
identities. The soundness target here is the parallel `rabinTest` Bool
predicate; the further bridge `rabinTest = true → GF2Poly.Irreducible f`
(Rabin's theorem for char-2 polynomials) is its own follow-up issue.
-/
namespace Hex
namespace GF2Poly

/-- Decidable equality on packed `GF(2)` polynomials, derived from the
underlying `Array UInt64` representation. The `wf` field is a `Prop`, so
its proofs are irrelevant for the structural comparison. -/
instance instDecidableEq : DecidableEq GF2Poly := fun p q =>
  match decEq p.words q.words with
  | isTrue hw =>
      match Nat.decEq p.degree q.degree with
      | isTrue hd =>
          isTrue (by
            cases p
            cases q
            simp_all)
      | isFalse hd =>
          isFalse (fun h => hd (by cases h; rfl))
  | isFalse hw =>
      isFalse (fun h => hw (by cases h; rfl))

instance instBEq : BEq GF2Poly where
  beq p q := decide (p = q)

instance instLawfulBEq : LawfulBEq GF2Poly where
  eq_of_beq := by
    intro a b h
    exact of_decide_eq_true h
  rfl := by
    intro a
    exact decide_eq_true rfl

/-- Square a polynomial modulo `f`. -/
def sqMod (f g : GF2Poly) : GF2Poly :=
  (g * g) % f

/-- Iterated squaring `k` times starting from `X mod f`, computing
`X^(2^k) mod f` over the packed `GF(2)` representation. -/
def xpow2kMod (f : GF2Poly) : Nat → GF2Poly
  | 0 => monomial 1 % f
  | k + 1 => sqMod f (xpow2kMod f k)

@[simp] theorem xpow2kMod_zero (f : GF2Poly) :
    xpow2kMod f 0 = monomial 1 % f := rfl

@[simp] theorem xpow2kMod_succ (f : GF2Poly) (k : Nat) :
    xpow2kMod f (k + 1) = sqMod f (xpow2kMod f k) := rfl

/-- The polynomial `X^(2^k) - X` reduced modulo `f`. Since the packed
representation is over characteristic two, subtraction collapses to addition. -/
def frobeniusDiffMod (f : GF2Poly) (k : Nat) : GF2Poly :=
  xpow2kMod f k + monomial 1 % f

/-- Positive divisors of `n` strictly below `n`, listed in ascending order. -/
def properDivisors (n : Nat) : List Nat :=
  ((List.range (n - 1)).map Nat.succ).filter fun d => n % d = 0

/-- The maximal proper divisors of `n`: those proper divisors not strictly
below any other proper divisor of `n`. -/
def maximalProperDivisors (n : Nat) : List Nat :=
  let ds := properDivisors n
  ds.filter fun d => !(ds.any fun e => d < e && e % d = 0)

/-- `true` exactly when `g` is a nonzero constant polynomial. -/
def isUnitPolynomial (g : GF2Poly) : Bool :=
  match g.degree? with
  | some 0 => true
  | _ => false

/-- The divisibility leg of Rabin's criterion: `f` divides `X^(2^n) - X`,
with `n = deg(f)`, exactly when the reduced remainder vanishes. -/
def rabinDividesTest (f : GF2Poly) : Bool :=
  (frobeniusDiffMod f f.degree).isZero

/-- The gcd leg of Rabin's criterion at a single maximal proper divisor `d`. -/
def rabinCoprimeTest (f : GF2Poly) (d : Nat) : Bool :=
  isUnitPolynomial (gcd f (frobeniusDiffMod f d))

/-- Per-divisor Rabin gcd outcomes for downstream factorization use. -/
def rabinWitnesses (f : GF2Poly) : List (Nat × Bool) :=
  (maximalProperDivisors f.degree).map fun d => (d, rabinCoprimeTest f d)

@[simp] theorem rabinWitnesses_all (f : GF2Poly) :
    (rabinWitnesses f).all Prod.snd =
      (maximalProperDivisors f.degree).all fun d => rabinCoprimeTest f d := by
  unfold rabinWitnesses
  induction maximalProperDivisors f.degree with
  | nil => rfl
  | cons d ds ih => simp [ih]

/-- Rabin's executable irreducibility test: `f` must be nonconstant, divide
`X^(2^n) - X`, and be coprime to `X^(2^d) - X` for every maximal proper
divisor `d` of `n = deg(f)`. -/
def rabinTest (f : GF2Poly) : Bool :=
  decide (0 < f.degree) &&
    rabinDividesTest f &&
    (rabinWitnesses f).all Prod.snd

/-- Bezout evidence that one Rabin gcd leg is coprime. -/
structure RabinBezoutWitness where
  left : GF2Poly
  right : GF2Poly

/-- Self-describing certificate data for Rabin irreducibility checking.

The `bezout` array is indexed in the same order as `maximalProperDivisors n`.
Each witness proves coprimality of `f` and `X^(2^d) - X mod f` by the
executable identity `left * f + right * (X^(2^d) - X mod f) = 1`. -/
structure IrreducibilityCertificate where
  n : Nat
  powChain : Array GF2Poly
  bezout : Array RabinBezoutWitness

namespace IrreducibilityCertificate

variable (cert : IrreducibilityCertificate)

/-- Read the certified `X^(2^k) mod f` witness, if present. -/
def powWitness? (k : Nat) : Option GF2Poly :=
  cert.powChain[k]?

@[simp] theorem powWitness?_eq_getElem? (k : Nat) :
    cert.powWitness? k = cert.powChain[k]? := rfl

/-- Read the Bezout witness for the `i`-th maximal proper divisor, if present. -/
def bezoutWitness? (i : Nat) : Option RabinBezoutWitness :=
  cert.bezout[i]?

@[simp] theorem bezoutWitness?_eq_getElem? (i : Nat) :
    cert.bezoutWitness? i = cert.bezout[i]? := rfl

end IrreducibilityCertificate

/-- The Rabin difference polynomial represented by a certificate pow-chain
entry. Equivalently `powWitness + (X mod f)` since char 2 collapses
subtraction to addition. -/
def certifiedFrobeniusDiffMod (f powWitness : GF2Poly) : GF2Poly :=
  powWitness + monomial 1 % f

/-- Check that a certificate's pow chain matches the executable iteration
`xpow2kMod`. The first entry must equal `X mod f`, and each subsequent entry
must equal the squaring step `sqMod f` of the previous. -/
def checkPowChain (f : GF2Poly) (cert : IrreducibilityCertificate) : Bool :=
  cert.powChain.size == cert.n + 1 &&
    (List.range (cert.n + 1)).all fun k =>
      cert.powChain[k]? == some (xpow2kMod f k)

/-- Check one Bezout witness for a Rabin maximal-proper-divisor leg. -/
def checkRabinBezoutWitness (f : GF2Poly) (cert : IrreducibilityCertificate)
    (i d : Nat) : Bool :=
  match cert.powChain[d]?, cert.bezout[i]? with
  | some powWitness, some witness =>
      let diff := certifiedFrobeniusDiffMod f powWitness
      witness.left * f + witness.right * diff == 1
  | _, _ => false

/-- Check all Bezout witnesses against `maximalProperDivisors cert.n`. -/
def checkRabinBezoutWitnesses (f : GF2Poly)
    (cert : IrreducibilityCertificate) : Bool :=
  let divisors := maximalProperDivisors cert.n
  cert.bezout.size == divisors.length &&
    (divisors.zipIdx).all fun pair =>
      checkRabinBezoutWitness f cert pair.2 pair.1

/-- Executable checker for a Rabin irreducibility certificate.

It validates the self-described `n`, recomputes every pow-chain entry,
checks the divisibility leg `X^(2^n) ≡ X mod f`, and verifies each Bezout
identity for the maximal proper divisors of `n`. -/
def checkIrreducibilityCertificate (f : GF2Poly)
    (cert : IrreducibilityCertificate) : Bool :=
  decide (0 < cert.n) &&
    decide (cert.n = f.degree) &&
    checkPowChain f cert &&
    (cert.powChain[cert.n]? == some (monomial 1 % f)) &&
    checkRabinBezoutWitnesses f cert

/-- Linear-time pow-chain check: each entry must be the squaring step of the
previous, with the first entry equal to `X mod f`.

This is logically equivalent to `checkPowChain` but uses only `O(n)`
squarings during kernel reduction, where `checkPowChain` recomputes
`xpow2kMod f k` from scratch for each `k` and is `O(n^2)`. The linear
form is intended for kernel-reducible `decide` checks on certificates
whose modulus has degree comparable to a few machine words. -/
def checkPowChainLinear (f : GF2Poly) (cert : IrreducibilityCertificate) : Bool :=
  cert.powChain.size == cert.n + 1 &&
    (cert.powChain[0]? == some (monomial 1 % f)) &&
    (List.range cert.n).all fun k =>
      match cert.powChain[k]?, cert.powChain[k + 1]? with
      | some prev, some curr => curr == sqMod f prev
      | _, _ => false

/-- Linear-time variant of `checkIrreducibilityCertificate`. The only
difference is that it uses `checkPowChainLinear` for the pow-chain leg. -/
def checkIrreducibilityCertificateLinear (f : GF2Poly)
    (cert : IrreducibilityCertificate) : Bool :=
  decide (0 < cert.n) &&
    decide (cert.n = f.degree) &&
    checkPowChainLinear f cert &&
    (cert.powChain[cert.n]? == some (monomial 1 % f)) &&
    checkRabinBezoutWitnesses f cert

theorem rabinDividesTest_spec (f : GF2Poly) :
    rabinDividesTest f = (frobeniusDiffMod f f.degree).isZero := rfl

/-! ## Soundness of the certificate checker against `rabinTest`

The proofs mirror `HexBerlekamp.checkIrreducibilityCertificate_rabinTest`.
The terminal target here is the Bool predicate `rabinTest`; the further
bridge `rabinTest = true → GF2Poly.Irreducible f` (Rabin's theorem) is its
own follow-up issue. -/

private theorem one_ne_zero_gf2poly : (1 : GF2Poly) ≠ 0 := by
  intro h
  have hwords := congrArg toWords h
  have hbad : toWords (1 : GF2Poly) ≠ toWords (0 : GF2Poly) := by decide
  exact hbad hwords

private theorem one_degree_eq_zero : (1 : GF2Poly).degree = 0 := by
  decide

private theorem one_degree?_eq_some_zero : (1 : GF2Poly).degree? = some 0 := by
  decide

private theorem isUnitPolynomial_of_dvd_one {g : GF2Poly}
    (hdiv : g ∣ (1 : GF2Poly)) :
    isUnitPolynomial g = true := by
  have hg_ne : g ≠ 0 := by
    rcases hdiv with ⟨r, hr⟩
    intro hg
    rw [hg, zero_mul] at hr
    exact one_ne_zero_gf2poly hr
  have hgle := degree_le_of_dvd_nonzero hg_ne one_ne_zero_gf2poly hdiv
  rw [one_degree_eq_zero] at hgle
  have hgdeg : g.degree = 0 := Nat.eq_zero_of_le_zero hgle
  have hgzeroFalse : g.isZero = false := by
    cases hzero : g.isZero
    · rfl
    · exact False.elim (hg_ne (eq_zero_of_isZero hzero))
  obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hgzeroFalse
  have hd0 : d = 0 := by simpa [degree, hd] using hgdeg
  unfold isUnitPolynomial
  rw [hd, hd0]

private theorem dvd_add' {d a b : GF2Poly} :
    d ∣ a → d ∣ b → d ∣ a + b := by
  intro hda hdb
  rcases hda with ⟨ra, hra⟩
  rcases hdb with ⟨rb, hrb⟩
  refine ⟨ra + rb, ?_⟩
  rw [hra, hrb, ← right_distrib]

private theorem dvd_mul_left' {d a : GF2Poly} (c : GF2Poly) :
    d ∣ a → d ∣ c * a := by
  intro hda
  rcases hda with ⟨r, hr⟩
  refine ⟨c * r, ?_⟩
  calc
    c * a = c * (d * r) := by rw [hr]
    _ = (c * d) * r := by rw [mul_assoc]
    _ = (d * c) * r := by rw [mul_comm c d]
    _ = d * (c * r) := by rw [mul_assoc]

private theorem isUnitPolynomial_gcd_of_bezout
    {f diff left right : GF2Poly}
    (hbezout : left * f + right * diff = 1) :
    isUnitPolynomial (gcd f diff) = true := by
  apply isUnitPolynomial_of_dvd_one
  have hgcd_left : gcd f diff ∣ f := gcd_dvd_left f diff
  have hgcd_right : gcd f diff ∣ diff := gcd_dvd_right f diff
  have hbezDvd : gcd f diff ∣ left * f + right * diff :=
    dvd_add' (dvd_mul_left' left hgcd_left) (dvd_mul_left' right hgcd_right)
  rw [hbezout] at hbezDvd
  exact hbezDvd

private theorem List.all_eq_true_of_mem {α : Type u} {xs : List α} {p : α → Bool}
    (hall : xs.all p = true) {x : α} (hx : x ∈ xs) : p x = true := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      rcases hall with ⟨hy, hys⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hy
      · exact ih hys hx

private theorem List.all_map_pair_snd {α : Type u} (xs : List α) (p : α → Bool) :
    (xs.map fun x => (x, p x)).all Prod.snd = xs.all p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

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

theorem checkPowChain_spec
    (f : GF2Poly) (cert : IrreducibilityCertificate) :
    checkPowChain f cert = true →
      ∀ k, k ≤ cert.n →
        cert.powChain[k]? = some (xpow2kMod f k) := by
  intro hcheck k hk
  unfold checkPowChain at hcheck
  simp only [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_hsize, hall⟩
  have hmem : k ∈ List.range (cert.n + 1) := by
    simpa [List.mem_range] using Nat.lt_succ_of_le hk
  have hbeq :
      (cert.powChain[k]? == some (xpow2kMod f k)) = true :=
    List.all_eq_true_of_mem hall hmem
  exact eq_of_beq hbeq

private theorem checkRabinBezoutWitness_rabinCoprimeTest
    (f : GF2Poly) (cert : IrreducibilityCertificate) (i d : Nat)
    (hcheck : checkRabinBezoutWitness f cert i d = true)
    (hpow : cert.powChain[d]? = some (xpow2kMod f d)) :
    rabinCoprimeTest f d = true := by
  unfold checkRabinBezoutWitness at hcheck
  rw [hpow] at hcheck
  cases hbezoutOpt : cert.bezout[i]? with
  | none =>
      simp [hbezoutOpt] at hcheck
  | some witness =>
      simp [hbezoutOpt] at hcheck
      -- After `simp`, `==` is reduced to `=`.
      unfold rabinCoprimeTest frobeniusDiffMod
      exact isUnitPolynomial_gcd_of_bezout hcheck

private theorem checkRabinBezoutWitnesses_rabinWitnesses_all
    (f : GF2Poly) (cert : IrreducibilityCertificate)
    (hcheck : checkRabinBezoutWitnesses f cert = true)
    (hpow : ∀ k, k ≤ cert.n →
      cert.powChain[k]? = some (xpow2kMod f k))
    (hn : cert.n = f.degree) :
    (rabinWitnesses f).all Prod.snd = true := by
  unfold checkRabinBezoutWitnesses at hcheck
  simp only [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_hsize, hall⟩
  unfold rabinWitnesses
  rw [← hn]
  let ds := maximalProperDivisors cert.n
  change (ds.map fun d => (d, rabinCoprimeTest f d)).all Prod.snd = true
  rw [List.all_map_pair_snd]
  change ds.all (fun d => rabinCoprimeTest f d) = true
  have hds :
      ∀ (xs : List Nat) start,
        (∀ d, d ∈ xs → d ∈ maximalProperDivisors cert.n) →
        (xs.zipIdx start).all
            (fun pair => checkRabinBezoutWitness f cert pair.2 pair.1) = true →
        xs.all (fun d => rabinCoprimeTest f d) = true := by
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
        · apply checkRabinBezoutWitness_rabinCoprimeTest f cert start d hd
          apply hpow
          apply mem_maximalProperDivisors_le
          exact hmem d (by simp)
        · exact ih (start + 1) (fun e he => hmem e (by simp [he])) htail
  exact hds ds 0 (fun d hmem => hmem) hall

/-- The executable certificate checker is sound against the parallel
`rabinTest` Bool predicate.

The further bridge `rabinTest = true → GF2Poly.Irreducible f` (Rabin's
theorem for polynomials over GF(2)) is the subject of a follow-up issue. -/
theorem checkIrreducibilityCertificate_rabinTest
    (f : GF2Poly) (cert : IrreducibilityCertificate) :
    checkIrreducibilityCertificate f cert = true → rabinTest f = true := by
  intro hcheck
  unfold checkIrreducibilityCertificate at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨hnpos, hn⟩, hpowCheck⟩, hdividesBeq⟩, hwitnesses⟩ := hcheck
  have hdividesWitness :
      cert.powChain[cert.n]? = some (monomial 1 % f) := eq_of_beq hdividesBeq
  have hpow := checkPowChain_spec f cert hpowCheck
  simp only [rabinTest, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [hn] using hnpos
  · -- rabinDividesTest f = true
    unfold rabinDividesTest frobeniusDiffMod
    have hpowN :
        cert.powChain[cert.n]? = some (xpow2kMod f cert.n) :=
      hpow cert.n (Nat.le_refl _)
    rw [hpowN] at hdividesWitness
    have hxpow_eq : xpow2kMod f cert.n = monomial 1 % f := by
      have hsome := hdividesWitness
      exact Option.some.inj hsome
    rw [← hn]
    rw [hxpow_eq]
    -- Goal: (monomial 1 % f + monomial 1 % f).isZero = true
    have hself : monomial 1 % f + monomial 1 % f = 0 := by simp
    rw [hself]
    exact (isZero_of_eq_zero rfl)
  · exact checkRabinBezoutWitnesses_rabinWitnesses_all
      f cert hwitnesses hpow hn

theorem checkPowChainLinear_spec
    (f : GF2Poly) (cert : IrreducibilityCertificate) :
    checkPowChainLinear f cert = true →
      ∀ k, k ≤ cert.n →
        cert.powChain[k]? = some (xpow2kMod f k) := by
  intro hcheck
  unfold checkPowChainLinear at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨⟨_hsize, h0beq⟩, hsteps⟩ := hcheck
  have h0 : cert.powChain[0]? = some (monomial 1 % f) := eq_of_beq h0beq
  intro k
  induction k with
  | zero =>
      intro _hk
      simpa [xpow2kMod_zero] using h0
  | succ m ih =>
      intro hk
      have hm := ih (Nat.le_of_succ_le hk)
      have hmem : m ∈ List.range cert.n := by
        simpa [List.mem_range] using hk
      have hstep_all :
          (match cert.powChain[m]?, cert.powChain[m + 1]? with
            | some prev, some curr => curr == sqMod f prev
            | _, _ => false) = true :=
        List.all_eq_true_of_mem hsteps hmem
      rw [hm] at hstep_all
      cases hopt : cert.powChain[m + 1]? with
      | none =>
          rw [hopt] at hstep_all
          exact False.elim (Bool.noConfusion hstep_all)
      | some curr =>
          rw [hopt] at hstep_all
          have hcurr : curr = sqMod f (xpow2kMod f m) := by
            simpa using eq_of_beq hstep_all
          simp [hcurr, xpow2kMod_succ]

theorem checkIrreducibilityCertificateLinear_rabinTest
    (f : GF2Poly) (cert : IrreducibilityCertificate) :
    checkIrreducibilityCertificateLinear f cert = true → rabinTest f = true := by
  intro hcheck
  unfold checkIrreducibilityCertificateLinear at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨hnpos, hn⟩, hpowCheck⟩, hdividesBeq⟩, hwitnesses⟩ := hcheck
  have hdividesWitness :
      cert.powChain[cert.n]? = some (monomial 1 % f) := eq_of_beq hdividesBeq
  have hpow := checkPowChainLinear_spec f cert hpowCheck
  simp only [rabinTest, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [hn] using hnpos
  · unfold rabinDividesTest frobeniusDiffMod
    have hpowN :
        cert.powChain[cert.n]? = some (xpow2kMod f cert.n) :=
      hpow cert.n (Nat.le_refl _)
    rw [hpowN] at hdividesWitness
    have hxpow_eq : xpow2kMod f cert.n = monomial 1 % f := by
      have hsome := hdividesWitness
      exact Option.some.inj hsome
    rw [← hn]
    rw [hxpow_eq]
    have hself : monomial 1 % f + monomial 1 % f = 0 := by simp
    rw [hself]
    exact (isZero_of_eq_zero rfl)
  · exact checkRabinBezoutWitnesses_rabinWitnesses_all
      f cert hwitnesses hpow hn

end GF2Poly
end Hex

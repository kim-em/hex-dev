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

/-- Read the Bezout witness for the `i`-th maximal proper divisor, if present. -/
def bezoutWitness? (i : Nat) : Option RabinBezoutWitness :=
  cert.bezout[i]?

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

theorem rabinDividesTest_spec (f : GF2Poly) :
    rabinDividesTest f = (frobeniusDiffMod f f.degree).isZero := rfl

end GF2Poly
end Hex

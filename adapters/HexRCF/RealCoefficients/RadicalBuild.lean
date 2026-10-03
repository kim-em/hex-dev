/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.RadicalCheck
public import HexPoly.Euclid
public import HexPoly.Lcm

public section

/-! Propose a radical certificate using the existing dense-polynomial gcd. -/

namespace Hex.RCF.RealCoefficients.RadicalCert

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [Div E] [NatCast E] [DecidableEq Ctx]

private def candidate (context : Ctx) (core quotient : DensePoly E)
    (exponent : Nat) : RadicalCert E Ctx :=
  { context, core, quotient, exponent
    cofactor := (DensePoly.divMod
      (DensePoly.natPow core (exponent + 1)) quotient).1 }

private def search (context : Ctx) (product core quotient : DensePoly E) :
    List Nat → Option (RadicalCert E Ctx)
  | [] => none
  | exponent :: rest =>
      let cert := candidate context core quotient exponent
      if cert.check context product then some cert
      else search context product core quotient rest

omit [NatCast E] in
private theorem search_checked (context : Ctx) (product core quotient : DensePoly E)
    (steps : List Nat) (cert : RadicalCert E Ctx)
    (h : search context product core quotient steps = some cert) :
    cert.check context product = true := by
  induction steps with
  | nil => simp [search] at h
  | cons exponent rest ih =>
      let proposed := candidate context core quotient exponent
      by_cases hc : proposed.check context product = true
      · have heq : proposed = cert := by
          simpa [search, proposed, hc] using h
        subst cert
        exact hc
      · have hf : proposed.check context product = false := by
          cases hvalue : proposed.check context product <;> simp_all
        have hrest : search context product core quotient rest = some cert := by
          simpa [search, proposed, hf] using h
        exact ih hrest

omit [NatCast E] in
private theorem search_core (context : Ctx) (product core quotient : DensePoly E)
    (steps : List Nat) (cert : RadicalCert E Ctx)
    (produced : search context product core quotient steps = some cert) : cert.core = core := by
  induction steps with
  | nil => simp [search] at produced
  | cons exponent rest ih =>
    by_cases accepted : (candidate context core quotient exponent).check context product = true
    · have same : candidate context core quotient exponent = cert := by
        simpa only [search, accepted, ite_eq_left, Option.some.injEq] using produced
      rw [← same]; rfl
    · have rejected : (candidate context core quotient exponent).check context product = false := by
        cases result : (candidate context core quotient exponent).check context product <;> simp_all
      apply ih
      simpa only [search, rejected, Bool.false_eq_true, ↓reduceIte] using produced

omit [NatCast E] in
private theorem search_success (context : Ctx) (product core quotient : DensePoly E)
    (steps : List Nat) (exponent : Nat) (member : exponent ∈ steps)
    (accepted : (candidate context core quotient exponent).check context product = true) :
    ∃ cert, search context product core quotient steps = some cert := by
  induction steps with
  | nil => simp at member
  | cons first rest ih =>
    by_cases checked : (candidate context core quotient first).check context product = true
    · exact ⟨candidate context core quotient first, by simp only [search, checked, ite_eq_left]⟩
    · have rejected : (candidate context core quotient first).check context product = false := by
        cases result : (candidate context core quotient first).check context product <;> simp_all
      have present : exponent ∈ rest := by
        rcases List.mem_cons.mp member with same | remaining
        · subst exponent; exact False.elim (checked accepted)
        · exact remaining
      obtain ⟨cert, produced⟩ := ih present
      exact ⟨cert, by simpa only [search, rejected, Bool.false_eq_true, ↓reduceIte] using produced⟩

/-- Quotient by the derivative gcd proposes a reduced core. A bounded search
then supplies the second radical identity. Only candidates accepted by the
literal checker are returned; failure makes no claim about the root set. -/
def build (context : Ctx) (product : DensePoly E) : Option (RadicalCert E Ctx) :=
  if product.isZero then none
  else
    let gcd := DensePoly.gcd product product.derivativeImpl
    let core := (DensePoly.divMod product gcd).1
    let quotient := (DensePoly.divMod product core).1
    search context product core quotient (List.range (product.natDegree + 1))

/-- Normalize only the proposed carrier core. The original product and both
divisibility identities remain bound to the certificate checker. Signed Sturm
chains are constructed separately and retain their positive-scaling convention. -/
def buildMonic [Inv E] (context : Ctx) (product : DensePoly E) :
    Option (RadicalCert E Ctx) :=
  if product.isZero then none
  else
    let gcd := DensePoly.gcd product product.derivativeImpl
    let core := DensePoly.monicize (DensePoly.divMod product gcd).1
    let quotient := (DensePoly.divMod product core).1
    search context product core quotient (List.range (product.natDegree + 1))

/-- Monic proposals undergo the same literal checks as the existing producer. -/
theorem buildMonic_checked [Inv E] (context : Ctx) (product : DensePoly E)
    (cert : RadicalCert E Ctx) (produced : buildMonic context product = some cert) :
    cert.check context product = true := by
  unfold buildMonic at produced
  split at produced
  · contradiction
  · exact search_checked context product _ _ _ cert produced

/-- Successful normalization retains precisely the monic derivative-gcd quotient. -/
theorem buildMonic_core [Inv E] (context : Ctx) (product : DensePoly E)
    (cert : RadicalCert E Ctx) (produced : buildMonic context product = some cert) :
    cert.core = DensePoly.monicize
      (DensePoly.divMod product (DensePoly.gcd product product.derivativeImpl)).1 := by
  unfold buildMonic at produced
  split at produced
  · contradiction
  · exact search_core context product _ _ _ cert produced

/-- With lawful field operations, every accepted normalized core is monic. -/
theorem buildMonic_monic {K : Type u} [Lean.Grind.Field K] [DecidableEq K] [NatCast K]
    (context : Ctx) (product : DensePoly K) (cert : RadicalCert K Ctx)
    (produced : buildMonic context product = some cert) : cert.core.Monic := by
  rw [buildMonic_core context product cert produced]
  apply DensePoly.monicize_monic
  intro zero
  have nonzero := core_ne_zero context product cert
    (buildMonic_checked context product cert produced)
  rw [buildMonic_core context product cert produced, zero, DensePoly.monicize_zero] at nonzero
  exact nonzero rfl

/-- A successful producer result is accepted by the exact replay checker. -/
theorem build_checked (context : Ctx) (product : DensePoly E)
    (cert : RadicalCert E Ctx) (h : build context product = some cert) :
    cert.check context product = true := by
  unfold build at h
  split at h
  · contradiction
  · exact search_checked context product _ _ _ cert h

/-- Every successful search retains the exact derivative-gcd quotient proposed
by the builder, independently of which checked exponent was found first. -/
theorem build_core (context : Ctx) (product : DensePoly E) (cert : RadicalCert E Ctx)
    (produced : build context product = some cert) :
    cert.core = (DensePoly.divMod product (DensePoly.gcd product product.derivativeImpl)).1 := by
  unfold build at produced
  split at produced
  · contradiction
  · exact search_core context product _ _ _ cert produced

/-- A successful builder started with a nonzero polynomial. -/
theorem build_nonzero (context : Ctx) (product : DensePoly E) (cert : RadicalCert E Ctx)
    (produced : build context product = some cert) : product ≠ 0 := by
  intro zero
  subst product
  simp only [build, show (0 : DensePoly E).isZero = true from rfl, ite_eq_left] at produced
  contradiction

/-- The two actual quotient identities at the maximum allowed exponent ensure
that the existing bounded search produces a certificate. This is an assembly
law; mathematical progress must establish the hypotheses under interpretation. -/
theorem build_fromIdentities (context : Ctx) (product : DensePoly E) (nonzero : product ≠ 0)
    (identities :
      let core := (DensePoly.divMod product (DensePoly.gcd product product.derivativeImpl)).1
      let quotient := (DensePoly.divMod product core).1
      let cofactor := (DensePoly.divMod (DensePoly.natPow core (product.natDegree + 1)) quotient).1
      (product - core * quotient).isZero = true ∧
        (DensePoly.natPow core (product.natDegree + 1) - quotient * cofactor).isZero = true)
    (coreNe : (DensePoly.divMod product (DensePoly.gcd product product.derivativeImpl)).1 ≠ 0) :
    ∃ cert, build context product = some cert := by
  let core := (DensePoly.divMod product (DensePoly.gcd product product.derivativeImpl)).1
  let quotient := (DensePoly.divMod product core).1
  have accepted : (candidate context core quotient product.natDegree).check context product = true := by
    have notZero : core.isZero = false := by
      cases result : core.isZero with
      | false => rfl
      | true => exact False.elim (coreNe ((DensePoly.size_eq_zero_iff core).mp
          ((DensePoly.isZero_eq_true_iff core).mp result)))
    have first : (product - core * quotient).isZero = true := identities.1
    have second : (DensePoly.natPow core (product.natDegree + 1) -
        quotient * (DensePoly.divMod (DensePoly.natPow core (product.natDegree + 1)) quotient).1).isZero = true :=
      identities.2
    simp only [candidate, check, first, second, notZero, Bool.not_false,
      Bool.and_true, Nat.le_refl, decide_true]
  have notZero : product.isZero = false := by
    cases result : product.isZero with
    | false => rfl
    | true => exact False.elim (nonzero ((DensePoly.size_eq_zero_iff product).mp
        ((DensePoly.isZero_eq_true_iff product).mp result)))
  unfold build
  simp only [notZero, Bool.false_eq_true, ↓reduceIte]
  exact search_success context product core quotient (List.range (product.natDegree + 1))
    product.natDegree (List.mem_range.mpr (Nat.lt_succ_self _)) accepted

end Hex.RCF.RealCoefficients.RadicalCert

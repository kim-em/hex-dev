/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsTheory.TarskiDomain
public import HexRealRootsTheory.TarskiMod
public import HexRealRoots.TarskiTests

public section

namespace HexRealRootsTheory.TarskiTests

open Hex DensePoly HexPolyTheory.Interpret HexRealRootsTheory.Tarski
open HexPoly.InterpretTests

private theorem value_neg (a : Rep) : value (-a) = -value a := by
  change value (pack (-(raw a).1) (-(raw a).2)) = -value a
  rw [value_pack]
  exact (neg_add (raw a).1 (raw a).2).symm

/-- The generic production/replay proof applies to a noninjective coefficient
representation with no ring, order or field instance. -/
theorem noncanonical_chains (p g : Poly) (hp : p ≠ 0) :
    SignedRemainderChain.check Hex.TarskiTests.Noncanonical.sign p g
      (SignedRemainderChain.build Hex.TarskiTests.Noncanonical.sign SignedRemainderChain.normalizeId p g) = true := by
  apply build_checks value value_eq_zero value_add value_sub value_mul value_one value_neg
    Hex.TarskiTests.Noncanonical.sign
    (fun a => by simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_eq_one_iff_pos, Rat.num_pos])
    (fun a => by simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_neg_iff, Rat.num_neg])
    SignedRemainderChain.normalizeId _ p g hp
  intro r _
  simp only [SignedRemainderChain.normalizeId, value_one, Polynomial.C_1, one_mul]
  exact ⟨zero_lt_one, True.intro⟩

/-- Full certificate acceptance also preserves literal context and endpoint
bindings over the noncanonical coefficient representation. -/
theorem noncanonical_certificates (context : Nat) (p g : Poly) (a b : Endpoint Rep)
    (cert : TarskiCertificate Rep Rep Nat)
    (hcert : TarskiCertificate.certify Hex.TarskiTests.Noncanonical.sign Hex.TarskiTests.Noncanonical.endpointSigns
      SignedRemainderChain.normalizeId context p g a b = some cert) :
    TarskiCertificate.check Hex.TarskiTests.Noncanonical.sign Hex.TarskiTests.Noncanonical.endpointSigns
      context p g a b cert.value cert = true := by
  refine TarskiCertificate.certify_checks _ _ _ noncanonical_chains ?_ context p g a b cert hcert
  intro q e
  apply Endpoint.signAt_bounds
  · intro c
    have h := Int.sign_trichotomy (value c).num
    rcases h with h | h | h <;> change -1 ≤ (value c).num.sign ∧ (value c).num.sign ≤ 1 <;> omega
  · intro q x
    have h := Int.sign_trichotomy (value (q.eval x)).num
    rcases h with h | h | h <;>
      change -1 ≤ (value (q.eval x)).num.sign ∧ (value (q.eval x)).num.sign ≤ 1 <;> omega

-- Public remainder invariance also covers a repeated head and infinite bounds.
example (q : Polynomial Rat) :
    rootSum (Polynomial.X ^ 2) (q % Polynomial.X ^ 2) .negInf .posInf =
      rootSum (Polynomial.X ^ 2) q .negInf .posInf :=
  rootSum_mod _ _ _ _

example (q : Polynomial Rat) (a b : Endpoint Rat) :
    rootSum 0 (q % 0) a b = rootSum 0 q a b := rootSum_mod _ _ _ _

/-- info: 'HexRealRootsTheory.Tarski.rootSum_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootSum_mod

/-- info: 'HexRealRootsTheory.Tarski.integer_certify_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integer_certify_checks
/-- info: 'HexRealRootsTheory.TarskiTests.noncanonical_chains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_chains
/-- info: 'HexRealRootsTheory.TarskiTests.noncanonical_certificates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_certificates

/-- info: 'HexRealRootsTheory.Tarski.check_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_squarefree
/-- info: 'HexRealRootsTheory.Tarski.integer_query_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integer_query_isSome

/-- info: 'HexRealRootsTheory.Tarski.integer_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integer_domain
/-- info: 'HexRealRootsTheory.Tarski.integer_check_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integer_check_domain

end HexRealRootsTheory.TarskiTests

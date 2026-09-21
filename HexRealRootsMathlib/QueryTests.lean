/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsMathlib.QueryInteger
public import HexRealRoots.QueryTests

public section

namespace HexRealRootsMathlib.QueryTests

open Hex DensePoly HexPolyMathlib.Interpret HexRealRootsMathlib.Query
open HexPoly.InterpretTests

private theorem value_neg (a : Rep) : value (-a) = -value a := by
  change value (pack (-(raw a).1) (-(raw a).2)) = -value a
  rw [value_pack]
  exact (neg_add (raw a).1 (raw a).2).symm

/-- The generic production/replay proof applies to a noninjective coefficient
representation with no ring, order or field instance. -/
theorem noncanonical_chains (p g : Poly) (hp : p ≠ 0) :
    QueryChain.check Hex.QueryTests.Noncanonical.sign p g
      (QueryChain.build Hex.QueryTests.Noncanonical.sign QueryChain.normalizeId p g) = true := by
  apply build_checks value value_eq_zero value_add value_sub value_mul value_one value_neg
    Hex.QueryTests.Noncanonical.sign
    (fun a => by simp only [Hex.QueryTests.Noncanonical.sign, Int.sign_eq_one_iff_pos, Rat.num_pos])
    (fun a => by simp only [Hex.QueryTests.Noncanonical.sign, Int.sign_neg_iff, Rat.num_neg])
    QueryChain.normalizeId _ p g hp
  intro r _
  simp only [QueryChain.normalizeId, value_one, Polynomial.C_1, one_mul]
  exact ⟨zero_lt_one, True.intro⟩

/-- Full certificate acceptance also preserves literal context and endpoint
bindings over the noncanonical coefficient representation. -/
theorem noncanonical_certificates (context : Nat) (p g : Poly) (a b : Endpoint Rep)
    (cert : QueryReplay Rep Rep Nat)
    (hcert : QueryReplay.certify Hex.QueryTests.Noncanonical.sign Hex.QueryTests.Noncanonical.adapter
      QueryChain.normalizeId context p g a b = some cert) :
    QueryReplay.check Hex.QueryTests.Noncanonical.sign Hex.QueryTests.Noncanonical.adapter
      context p g a b cert.value cert = true := by
  refine QueryReplay.certify_checks _ _ _ noncanonical_chains ?_ context p g a b cert hcert
  intro q e
  apply Endpoint.signAt_bounds
  · intro c
    have h := Int.sign_trichotomy (value c).num
    rcases h with h | h | h <;> change -1 ≤ (value c).num.sign ∧ (value c).num.sign ≤ 1 <;> omega
  · intro q x
    have h := Int.sign_trichotomy (value (q.eval x)).num
    rcases h with h | h | h <;>
      change -1 ≤ (value (q.eval x)).num.sign ∧ (value (q.eval x)).num.sign ≤ 1 <;> omega

/-- info: 'HexRealRootsMathlib.Query.integer_certify_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integer_certify_checks
/-- info: 'HexRealRootsMathlib.QueryTests.noncanonical_chains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_chains
/-- info: 'HexRealRootsMathlib.QueryTests.noncanonical_certificates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_certificates

/-- info: 'HexRealRootsMathlib.Query.check_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_squarefree
/-- info: 'HexRealRootsMathlib.Query.integer_query_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integer_query_isSome

end HexRealRootsMathlib.QueryTests


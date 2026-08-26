/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntTable10Exact

/-!
# Exact-supremum acceptance for PNT+ BKLNW Table 10

The existing row conformance files exercise bounded planning, mutation
rejection, chronological replay, and `ProofFrontend`.  This final guard checks
that their source-authenticated numerical conclusion crosses the generic
ordinary-kernel supremum bridge and reaches the exact theorem shape retained
by PNT+.
-/

namespace Hex.IntervalMathlib.PntTable10ExactConformance

open Hex.Interval.Experiment
open PntTable10Exact

/-- Representative exact-source adapter.  In the localized PNT+ rewrite,
`a1`, `a2`, and `epsilon` are its unchanged `Inputs.default` coefficients and
the final three hypotheses are its existing coefficient lemmas. -/
theorem table_10_row25_exact (B : Nat → Real)
    (member : ((25 : Real), B 1, B 2, B 3, B 4, B 5) ∈
      PntTable10Shard.sourceTable)
    (k : Nat) (column : k ∈ Finset.Icc 1 5)
    (a1 a2 epsilon : Real)
    (ha1 : a1 ≤ PntTable10Shard.certificate.a1.value)
    (ha2 : a2 ≤ PntTable10Shard.certificate.a2.value)
    (hepsilon : epsilon ≤ PntTable10Shard.certificate.epsilon.value) :
    exactBound k a1 a2 epsilon 25 26 ≤
      B k * PntTable10Shard.margin.value := by
  apply Shard.row25OfMem B member k column a1 a2 epsilon
    (by norm_num [PntTable10Shard.certificate, PntTable10Shard.Decimal.value,
      PntTable10Shard.decimal])
    (by norm_num [PntTable10Shard.certificate, PntTable10Shard.Decimal.value,
      PntTable10Shard.decimal])
    (by norm_num [PntTable10Shard.certificate, PntTable10Shard.Decimal.value,
      PntTable10Shard.decimal])
    ha1 ha2 hepsilon

/--
info: 'Hex.IntervalMathlib.PntTable10ExactConformance.table_10_row25_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms table_10_row25_exact

/--
info: 'Hex.Interval.Experiment.PntTable10Exact.exactBound_eq_sourceSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exactBound_eq_sourceSum

end Hex.IntervalMathlib.PntTable10ExactConformance

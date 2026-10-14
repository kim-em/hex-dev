/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPTheory.Compact

/-! Replay allocations count all terminal nodes, not only chain depth.
This Pocklington root has 30 children: its 31 nodes plus the ECPP base wrapper
fit the 32-node replay ceiling. Adding even one ECPP row exceeds that ceiling,
despite shallow row and terminal depths.
-/

namespace Hex.ECPP.NodeBudget

@[expose] public def terminal : Hex.Nat.PrimeCert :=
  .pock 63220109280835215576290412583087324986549373981 [
    (2, 0, .small 2),
    (3, 0, .small 3),
    (2, 0, .small 5),
    (2, 0, .small 7),
    (2, 0, .small 11),
    (2, 0, .small 13),
    (2, 0, .small 17),
    (2, 0, .small 19),
    (5, 0, .small 23),
    (2, 0, .small 29),
    (2, 0, .small 31),
    (2, 0, .small 37),
    (2, 0, .small 41),
    (3, 0, .small 43),
    (2, 0, .small 47),
    (2, 0, .small 53),
    (2, 0, .small 59),
    (2, 0, .small 61),
    (2, 0, .small 67),
    (2, 0, .small 71),
    (2, 0, .small 73),
    (2, 0, .small 79),
    (2, 0, .small 83),
    (2, 0, .small 89),
    (2, 0, .small 97),
    (2, 0, .small 101),
    (2, 0, .small 103),
    (2, 0, .small 107),
    (2, 0, .small 109),
    (2, 0, .small 113)]

example : _root_.Nat.Prime 63220109280835215576290412583087324986549373981 := by
  ecpp using (Hex.ECPP.Cert.base terminal)

example : _root_.Nat.Prime 63220109280835215576290412583087324986549373981 := by
  ecpp using (ecpp_cert% "63220109280835215576290412583087324986549373981" using terminal)

@[expose] public def overLimit : Hex.ECPP.Cert :=
  -- This row is deliberately invalid: node exhaustion precedes checker work.
  .step 63220109280835215576290412583087324986549373983 1 1 0 1 1 [] (.base terminal)

/-- error: ecpp: certificate exceeds 32 total nodes -/
#guard_msgs in
example : _root_.Nat.Prime 63220109280835215576290412583087324986549373983 := by
  ecpp using overLimit

-- A small shared representation denotes exponentially many terminal nodes.
-- The raw public validation route must exhaust its allocation before reifying
-- that tree. No arithmetic property of the untrusted proposal is assumed.
/-- error: ecpp: certificate exceeds 32 total nodes -/
#guard_msgs in
run_meta do
  let mut leaf := Hex.Nat.PrimeCert.small 2
  for _ in [:60] do
    leaf := .pock 3 [(2, 0, leaf), (2, 0, leaf)]
  Hex.ECPP.validateCert (.base leaf)

-- The expression route must charge substituted occurrences as well. This
-- proposal uses only constructors and lets, with 60 successive shared nodes.
/-- error: ecpp: certificate syntax exceeds 131072 nodes -/
#guard_msgs in
set_option maxHeartbeats 1000000 in
run_meta do
  let small := Hex.PrimalityTactic.reifyPrimeCert (.small 2)
  let template := Hex.PrimalityTactic.reifyPrimeCert
    (.pock 3 [(2, 0, .small 2), (2, 0, .small 2)])
  let body := template.replace fun e => if e == small then some (Lean.mkBVar 0) else none
  let mut data := small
  for _ in [:60] do
    data := Lean.mkLet `child (Lean.mkConst ``Hex.Nat.PrimeCert) data body
  discard <| Hex.ECPP.readCert (Lean.mkApp (Lean.mkConst ``Hex.ECPP.Cert.base) data)

end Hex.ECPP.NodeBudget

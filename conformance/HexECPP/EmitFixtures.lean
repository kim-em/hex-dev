/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPP.Import
import HexECPP.Fixture17
import HexECPP.Fixture65
import HexECPP.Fixture256
import HexECPP.Fixture512
import Lean.Data.Json

/-! Frozen ECPP cases for the independent PARI/Python oracle. -/

open Hex.ECPP Lean

private def pointJson : Point → Json
  | .infinity => Json.null
  | .affine x y => toJson #[x, y]

private def resultJson : Option (Point × List Nat) → Json
  | none => Json.null
  | some (P, rest) => Json.mkObj [
      ("point", pointJson P), ("rest", toJson rest)]

private def emit (j : Json) : IO Unit := IO.println j.compress

private def emitOperation (n a b : Nat) (P Q : Point) (ws : List Nat) : IO Unit :=
  emit <| Json.mkObj [
    ("kind", toJson "add"), ("n", toJson n), ("a", toJson a), ("b", toJson b),
    ("p", pointJson P), ("q", pointJson Q), ("witnesses", toJson ws),
    ("result", resultJson (add? n a P Q ws))]

private def emitSubject (n : Nat) (accepted : Bool) : IO Unit :=
  emit <| Json.mkObj [
    ("kind", toJson "subject"), ("n", toJson n),
    ("accepted", toJson accepted)]

private def emitScalar (n a b q : Nat) (Q : Point)
    (ws : List Nat) : IO Unit :=
  emit <| Json.mkObj [
    ("kind", toJson "scalar"), ("n", toJson n),
    ("a", toJson a), ("b", toJson b), ("q", toJson q),
    ("point", pointJson Q), ("witnesses", toJson ws),
    ("result", resultJson (replay n a b q Q ws))]

private def emitStep (cert : Cert) : IO Unit :=
  match cert with
  | .step n a b x y d ws child =>
      emit <| Json.mkObj [
        ("kind", toJson "step"), ("n", toJson n), ("a", toJson a), ("b", toJson b),
        ("x", toJson x), ("y", toJson y),
        ("d", toJson d), ("q", toJson child.subject),
        ("witnesses", toJson ws), ("accepted", toJson (check cert))]
  | _ => pure ()

/-- Exhaust every point pair and scalar up to twice the field size on three
small nonsingular curves. The Python oracle uses separate field arithmetic. -/
private def emitSmallCurves : IO Unit := do
  for n in [5, 7, 11] do
    for params in [(0, 3), (1, 0)] do
      let (a, b) := params
      let points : List Point := .infinity ::
        ((List.range n).flatMap fun x =>
          (List.range n).filterMap fun y =>
            if onCurve n a b x y then some (.affine x y) else none)
      for P in points do
        for Q in points do
          match proposeAdd n a P Q with
          | .ok (_, some u) => emitOperation n a b P Q [u]
          | .ok (_, none) => emitOperation n a b P Q []
          | .error _ => pure ()
      for Q in points do
        for q in List.range (2 * n + 1) do
          match proposeScalar defaultImportBudget n a q Q with
          | .ok (_, ws) => emitScalar n a b q Q ws
          | .error _ => pure ()

def main (_ : List String) : IO UInt32 := do
  emitSmallCurves
  let P : Point := .affine 1 2
  emitOperation 7 0 3 .infinity P []
  emitOperation 7 0 3 P .infinity []
  emitOperation 7 0 3 P (.affine 1 5) []
  emitOperation 7 0 3 P P []
  emitOperation 7 0 3 P P [2]
  emitOperation 7 0 3 P P [3]
  emitOperation 7 0 3 P P [2, 4]
  emitOperation 7 0 3 P (.affine 6 3) [3]
  emitOperation 7 0 3 P (.affine 1 3) []
  emitStep Fixture17.cert
  emitStep Fixture65.cert
  emitSubject Fixture17.cert.subject (check Fixture17.cert)
  emitSubject Fixture65.cert.subject (check Fixture65.cert)
  emitSubject Fixture256.cert.subject (check Fixture256.cert)
  emitSubject Fixture512.cert.subject (check Fixture512.cert)
  emitSubject 35 false
  emitSubject 49 false
  return 0

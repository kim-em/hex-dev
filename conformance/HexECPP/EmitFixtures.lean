/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPP.Search
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

private def emitChain : Cert → IO Unit
  | .base c => emitSubject c.subject (Hex.Nat.checkPrime c)
  | c@(.step _ _ _ _ _ _ _ child) => do
      emitStep c
      emitChain child

private def emitTwists : IO Unit := do
  for (n, d, j, g) in [(13, 3, (0 : Int), 2), (17, 4, (1728 : Int), 3)] do
    for (a, b) in CM.curves n ⟨d, j⟩ g do
      for x in List.range n do
        for y in List.range n do
          if onCurve n a b x y then
            for q in List.range (2 * n + 1) do
              if let .ok (_, ws) := proposeScalar defaultImportBudget n a q (.affine x y) then
                emitScalar n a b q (.affine x y) ws
  for (n, d, j, g) in [(13, 3, (0 : Int), 2), (17, 4, (1728 : Int), 3),
      (11, 7, (-3375 : Int), 2)] do
    for (a, b) in CM.curves n ⟨d, j⟩ g do
      let order := 1 + ((List.range n).map fun x =>
        ((List.range n).filter (onCurve n a b x)).length).sum
      emit <| Json.mkObj [("kind", toJson "curve"), ("n", toJson n),
        ("a", toJson a), ("b", toJson b), ("j", toJson (residue n j)),
        ("order", toJson order)]

private def emitCM : IO Unit := do
  for n in [5, 7, 9, 13, 17, 25, 35, 49, 101, 113] do
    for a in List.range n do
      emit <| Json.mkObj [
        ("kind", toJson "root"), ("n", toJson n), ("a", toJson a),
        ("symbol", toJson (CM.symbol a n)), ("root", toJson (CM.sqrt? n 2 a))]
  for (n, d, r) in [(13, 3, 6), (13, 3, 1), (17, 4, 4), (11, 7, 2),
      (47, 11, 6), (35, 3, 15), (49, 3, 20)] do
    emit <| Json.mkObj [("kind", toJson "norm"), ("n", toJson n),
      ("d", toJson d), ("root", toJson r), ("result", toJson (CM.norm? n d r))]
  for n in [177080666831933235355717939809840315427,
      69199437377629051939477864552334532767081794053034238723740032946332041487367] do
    if let .ok c := (produce n 0).result then emitChain c
    else throw <| IO.userError "native fixture unexpectedly exhausted"

def main (_ : List String) : IO UInt32 := do
  emitSmallCurves
  emitCM
  emitTwists
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

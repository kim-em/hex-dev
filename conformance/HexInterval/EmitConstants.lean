/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval
import Hex.Conformance.Emit

/-!
# Exact named-constant fixtures

Emit original source/order/precision inputs, independently checkable rational
center/radius, dyadic endpoints, and the actual compiled checker result. The
Python Fraction oracle recomputes the series from the original inputs and
also checks containment against a second Machin identity for π.
-/

open Hex.Interval.Constants

private def pair (q : Rat) : String := s!"[{q.num},{q.den}]"

private def sourceName : Source → String
  | .piMachinV1 => "pi-machin-v1"
  | .expOneTaylorV1 => "exp-one-taylor-v1"

def main : IO Unit := do
  for source in [Source.piMachinV1, .expOneTaylorV1] do
    for bits in [0, 1, 8, 32, 128, 256, 1000] do
      let limits := limitsFor bits
      let certificate ← match enclose limits source bits with
        | .ok value => pure value
        | .error error => throw (IO.userError s!"provider failed: {repr error}")
      let accepted := match check limits source bits certificate with
        | .ok _ => true
        | .error _ => false
      if !accepted then throw (IO.userError "generated certificate failed replay")
      Hex.Conformance.Emit.emitLine <|
        "{\"kind\":\"interval-constant-v1\",\"lib\":\"HexInterval\",\"case\":\"" ++
        sourceName source ++ s!"/{bits}" ++ "\",\"source\":\"" ++ sourceName source ++
        "\",\"bits\":" ++ toString bits ++ ",\"order\":" ++ toString certificate.order ++
        ",\"center\":" ++ pair certificate.approximation.center ++
        ",\"radius\":" ++ pair certificate.approximation.radius ++
        ",\"lower\":" ++ pair certificate.lower.toRat ++
        ",\"upper\":" ++ pair certificate.upper.toRat ++
        ",\"accepted\":true}"

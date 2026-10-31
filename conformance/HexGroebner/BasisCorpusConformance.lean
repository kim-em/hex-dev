/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Producer.Pipeline
import HexGroebner.F4Fixtures

open Hex.Groebner

private def checked : Bool := Id.run do
  for field in Fixtures.fields do
    for order in [TermOrder.lex,.grlex,.grevlex] do
      for c in F4Fixtures.cases field do
        let .success value _ _ := Producer.basisWith ⟨field,c.variables,order⟩ {} c.generators | return false
        if !checkBasis value.context value.generators value.polynomials value.certificate then return false
  return true

#guard checked

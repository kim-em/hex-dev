/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexGroebner.F4Fixtures

namespace Hex.Groebner.EmitF4

private def array (values : Array String) : String :=
  "[" ++ String.intercalate "," values.toList ++ "]"

private def term (term : RawTerm) : String :=
  "[" ++ array (term.exponents.map toString) ++ "," ++ toString term.coefficient.toNat ++ "]"

private def polynomial (p : RawPolynomial) : String := array (p.map term)

private def orderName : TermOrder → String
  | .lex => "lex"
  | .grlex => "grlex"
  | .grevlex => "grevlex"

private def emit : IO Unit := do
  for field in Fixtures.fields do
    for order in [TermOrder.lex, .grlex, .grevlex] do
      for c in F4Fixtures.cases field do
        let context : Context := ⟨field, c.variables, order⟩
        let (candidate, stats) ← match computeWith context {} c.generators with
          | .candidate candidate stats => pure (candidate, stats)
          | .invalid e _ => throw (IO.userError s!"{c.name}: {reprStr e}")
          | .exhausted r _ => throw (IO.userError s!"{c.name}: exhausted {reprStr r}")
          | .representation e _ => throw (IO.userError s!"{c.name}: representation {reprStr e}")
        let value := "{" ++ s!"\"p\":{field.modulus.toNat},\"variables\":{c.variables}," ++
          "\"order\":\"" ++ orderName order ++ "\",\"generators\":" ++
          array (c.generators.map polynomial) ++ ",\"basis\":" ++
          array (candidate.polynomials.map polynomial) ++
          s!",\"rounds\":{stats.rounds},\"pairs\":{stats.pairs},\"work\":{stats.work}" ++ "}"
        Hex.Conformance.Emit.emitResult "HexGroebner" s!"p{field.modulus.toNat}/{orderName order}/{c.name}" "f4" value

end Hex.Groebner.EmitF4

def main : IO Unit := Hex.Groebner.EmitF4.emit

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexGroebner.F4Fixtures

/-! Oracle profile: Singular reduced bases, `if_available` by default and
`required` for manual validation with `--require-oracles` or
`HEX_REQUIRE_ORACLES=1`. SymPy F5B provides an additional always-run oracle.
The core profile in F4Conformance has no external oracle. -/

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
          | .internal e _ => throw (IO.userError s!"{c.name}: internal {reprStr e}")
          | .invalid e _ => throw (IO.userError s!"{c.name}: {reprStr e}")
          | .exhausted r _ => throw (IO.userError s!"{c.name}: exhausted {reprStr r}")
          | .representation e _ => throw (IO.userError s!"{c.name}: representation {reprStr e}")
        let (serial, serialStats) ← match computeWith context { batchSize := 1 } c.generators with
          | .candidate candidate stats => pure (candidate, stats)
          | .internal e _ => throw (IO.userError s!"{c.name}: internal {reprStr e}")
          | .invalid e _ => throw (IO.userError s!"{c.name}: {reprStr e}")
          | .exhausted r _ => throw (IO.userError s!"{c.name}: serial exhausted {reprStr r}")
          | .representation e _ => throw (IO.userError s!"{c.name}: serial representation {reprStr e}")
        if candidate.polynomials != serial.polynomials then
          throw (IO.userError s!"{c.name}: batch-size-dependent reduced basis")
        let value := "{" ++ s!"\"p\":{field.modulus.toNat},\"variables\":{c.variables}," ++
          "\"order\":\"" ++ orderName order ++ "\",\"generators\":" ++
          array (c.generators.map polynomial) ++ ",\"basis\":" ++
          array (candidate.polynomials.map polynomial) ++
          s!",\"rounds\":{stats.rounds},\"pairs\":{stats.pairs},\"work\":{stats.work}," ++
          s!"\"productPairs\":{stats.productPairs},\"chainPairs\":{stats.chainPairs}," ++
          s!"\"serialChainPairs\":{serialStats.chainPairs},\"serialWork\":{serialStats.work}," ++
          s!"\"serialRounds\":{serialStats.rounds}" ++ "}"
        Hex.Conformance.Emit.emitResult "HexGroebner" s!"p{field.modulus.toNat}/{orderName order}/{c.name}" "f4" value

end Hex.Groebner.EmitF4

def main : IO Unit := Hex.Groebner.EmitF4.emit

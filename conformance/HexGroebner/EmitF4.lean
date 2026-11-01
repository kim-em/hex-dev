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

private def canonical (p : Nat) (raw : RawPolynomial) : Certificate.Polynomial :=
  raw.foldl (fun f term => if term.coefficient == 0 then f else
    Hex.MvPoly.Kernel.addMod p f [(term.exponents.toList,term.coefficient.toNat)]) []

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
        let original := c.generators.map (canonical field.modulus.toNat)
        let checked ← match basisWith context {} original with
          | .success value _ => pure value
          | _ => throw (IO.userError s!"{c.name}: checked F4 computation failed")
        if checked.value.polynomials != candidate.polynomials.map (canonical field.modulus.toNat) then
          throw (IO.userError s!"{c.name}: checked/candidate reduced basis mismatch")
        let (serial, serialStats) ← match computeWith context { batchSize := 1 } c.generators with
          | .candidate candidate stats => pure (candidate, stats)
          | .internal e _ => throw (IO.userError s!"{c.name}: internal {reprStr e}")
          | .invalid e _ => throw (IO.userError s!"{c.name}: {reprStr e}")
          | .exhausted r _ => throw (IO.userError s!"{c.name}: serial exhausted {reprStr r}")
          | .representation e _ => throw (IO.userError s!"{c.name}: serial representation {reprStr e}")
        if candidate.polynomials != serial.polynomials then
          throw (IO.userError s!"{c.name}: batch-size-dependent reduced basis")
        let (scalar, scalarStats) ← match computeWith context { nativeRows := false } c.generators with
          | .candidate candidate stats => pure (candidate, stats)
          | .internal e _ => throw (IO.userError s!"{c.name}: scalar internal {reprStr e}")
          | .invalid e _ => throw (IO.userError s!"{c.name}: {reprStr e}")
          | .exhausted r _ => throw (IO.userError s!"{c.name}: scalar exhausted {reprStr r}")
          | .representation e _ => throw (IO.userError s!"{c.name}: scalar representation {reprStr e}")
        if candidate.polynomials != scalar.polynomials || stats != scalarStats then
          throw (IO.userError s!"{c.name}: native/scalar candidate or counter mismatch")
        let (reference, referenceStats) ← match computeWith context { gebauerMoller := false } c.generators with
          | .candidate candidate stats => pure (candidate, stats)
          | .internal e _ => throw (IO.userError s!"{c.name}: reference internal {reprStr e}")
          | .invalid e _ => throw (IO.userError s!"{c.name}: reference {reprStr e}")
          | .exhausted r _ => throw (IO.userError s!"{c.name}: reference exhausted {reprStr r}")
          | .representation e _ => throw (IO.userError s!"{c.name}: reference representation {reprStr e}")
        if candidate.polynomials != reference.polynomials then
          throw (IO.userError s!"{c.name}: Gebauer–Möller/reference candidate mismatch")
        let (portableMonomials, monomialStats) ← match computeWith context { nativeMonomials := false } c.generators with
          | .candidate candidate statistics => pure (candidate, statistics)
          | _ => throw (IO.userError s!"{c.name}: portable monomial computation failed")
        if candidate.polynomials != portableMonomials.polynomials || stats != monomialStats then
          throw (IO.userError s!"{c.name}: packed/portable monomial or counter mismatch")
        let separate ← match computeWith context { batchInterreduce := false } c.generators with
          | .candidate candidate _ => pure candidate
          | _ => throw (IO.userError s!"{c.name}: separate tail reduction failed")
        if candidate.polynomials != separate.polynomials then
          throw (IO.userError s!"{c.name}: shared/separate tail reduction mismatch")
        let value := "{" ++ s!"\"p\":{field.modulus.toNat},\"variables\":{c.variables}," ++
          "\"order\":\"" ++ orderName order ++ "\",\"generators\":" ++
          array (c.generators.map polynomial) ++ ",\"basis\":" ++
          array (candidate.polynomials.map polynomial) ++
          s!",\"rounds\":{stats.rounds},\"pairs\":{stats.pairs},\"work\":{stats.work}," ++
          s!"\"batchSize\":{candidate.batchSize},\"largestBatch\":{stats.largestBatch}," ++
          s!"\"peakMatrixRows\":{stats.peakMatrixRows},\"peakMatrixEntries\":{stats.peakMatrixEntries}," ++
          s!"\"productPairs\":{stats.productPairs},\"chainPairs\":{stats.chainPairs},\"gmPairs\":{stats.gmPairs}," ++
          s!"\"serialChainPairs\":{serialStats.chainPairs},\"serialWork\":{serialStats.work}," ++
          s!"\"serialRounds\":{serialStats.rounds},\"referenceWork\":{referenceStats.work}," ++
          s!"\"referenceMatrixEntries\":{referenceStats.matrixEntries},\"matrixEntries\":{stats.matrixEntries}" ++ "}"
        Hex.Conformance.Emit.emitResult "HexGroebner" s!"p{field.modulus.toNat}/{orderName order}/{c.name}" "f4" value

end Hex.Groebner.EmitF4

def main : IO Unit := Hex.Groebner.EmitF4.emit

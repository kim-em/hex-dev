/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Division
import Hex.Conformance.Emit
import HexGroebner.F4Fixtures
import Lean.Data.Json

open Hex.Groebner Lean

namespace Hex.Groebner.EmitDivision

private def canonical (p : Nat) (raw : RawPolynomial) : Certificate.Polynomial :=
  raw.foldl (fun f t => if t.coefficient == 0 then f else
    Hex.MvPoly.Kernel.addMod p f [(t.exponents.toList,t.coefficient.toNat)]) []

private def dividend (p n seed : Nat) : Certificate.Polynomial :=
  (List.range 8).foldl (fun f i =>
    let exponents := (List.range n).map fun j =>
      ((seed+1)*1103515245 + (i+3)*12345 + (j+1)*69069 + i*j*17) % 4
    let coefficient := ((seed+1)*69069 + (i+1)*12345) % p
    if coefficient == 0 then f else Hex.MvPoly.Kernel.addMod p f [(exponents,coefficient)]) []

private def orderName : TermOrder → String
  | .lex => "lex"
  | .grlex => "grlex"
  | .grevlex => "grevlex"

private def emit : IO Unit := do
  for field in Fixtures.fields do
    for order in [TermOrder.lex, .grlex, .grevlex] do
      for (c,seed) in (F4Fixtures.cases field).zipIdx do
        let context : Context := ⟨field,c.variables,order⟩
        let basis ← match computeWith context {} c.generators with
          | .candidate value _ => pure (value.polynomials.map (canonical field.modulus.toNat))
          | _ => throw (IO.userError s!"{c.name}: F4 candidate failed")
        for (name,divisors) in [("generators",c.generators.map (canonical field.modulus.toNat)),("basis",basis)] do
          let f := dividend field.modulus.toNat c.variables seed
          let (result,usage) ← match divideWith context {} divisors f with
            | .success result usage => pure (result.value,usage)
            | _ => throw (IO.userError s!"{c.name}/{name}: checked division failed")
          let value := Json.mkObj [
            ("p",toJson field.modulus.toNat),("variables",toJson c.variables),
            ("order",toJson (orderName order)),("generators",toJson divisors),
            ("dividend",toJson f),("quotients",toJson result.quotients),
            ("remainder",toJson result.remainder),("work",toJson usage.work)]
          Hex.Conformance.Emit.emitResult "HexGroebner"
            s!"p{field.modulus.toNat}/{orderName order}/{c.name}/{name}" "division" value.compress

end Hex.Groebner.EmitDivision

def main : IO Unit := Hex.Groebner.EmitDivision.emit

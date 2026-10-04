/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexRealClosure.TrivialChecks
public import Hex.Conformance.Emit
public import Lean.Data.Json

public section

open Hex Hex.RealClosure Hex.RealClosure.Trivial Lean

private def rat (q : Rat) : Json := toJson #[q.num, (q.den : Int)]

private def real (a : RealAlgebraicNumber) : Json :=
  let s := a.toAlgebraic.rep.1.square
  Json.mkObj [("poly", toJson a.toAlgebraic.p.toArray), ("re", rat s.re.toRat),
    ("im", rat s.im.toRat), ("prec", toJson s.prec)]

private def emit {registry : BaseContext.Registry} {parent : Tower.Context registry}
    (source : Map parent) (generators : Array RealAlgebraicNumber) (name : String) (p : DensePoly parent.Value) : IO Unit := do
  let roots := parent.roots p
  let native ← p.toArray.mapM fun a => do
    let some text := String.fromUTF8? (parent.codec.encode a).writeBytes
      | throw (IO.userError "native coefficient JSON is not UTF-8")
    IO.ofExcept (Json.parse text)
  let value := Json.mkObj [("schema", toJson (2 : Nat)),
    ("generators", Json.arr (generators.map real)),
    ("nativeCoefficients", Json.arr native),
    ("coefficients", Json.arr (p.toArray.map fun a => real (source.value a))),
    ("roots", match roots with
      | .all => Json.null
      | .finite entries => Json.arr ((entries.map fun original =>
          let e := source.entry original
          Json.mkObj [("root", real e.root), ("multiplicity", toJson e.multiplicity),
            ("kind", toJson (match original.root with
              | .point _ => "point"
              | .selected _ _ _ => "selected"))]).toArray))]

  Hex.Conformance.Emit.emitResult "HexRealClosure" name "trivialRoots" value.compress

def main : IO Unit := Trivial.Checks.runWith emit

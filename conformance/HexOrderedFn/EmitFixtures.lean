/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexOrderedFn.Infinitesimal
import Lean.Data.Json

open Hex Hex.OrderedFn Lean
open scoped Hex.OrderedFn.Infinitesimal

namespace Hex.OrderedFn.Emit

private def fraction {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (encode : K → Json) (f : RationalFn K) : Json :=
  Json.mkObj [("num", .arr (f.num.coeffs.map encode)), ("den", .arr (f.den.coeffs.map encode))]

private def rational (q : Rat) : Json := .arr #[toJson q.num, toJson q.den]

private def emit (depth : Nat) (name operation : String) (fields : List (String × Json)) : IO Unit := do
  (← IO.getStdout).putStrLn (Json.mkObj ([("kind", toJson "ordered-fn"),
    ("lib", toJson "HexOrderedFn"), ("case", toJson name), ("depth", toJson depth),
    ("operation", toJson operation)] ++ fields)).compress

private def values {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (depth : Nat) (encode : K → Json) (baseSign : K → Int)
    (xs : Array (RationalFn K)) : IO Unit := do
  for hi : i in [:xs.size] do
    have hv : i < xs.size := by get_elem_tactic
    let f := xs[i]
    emit depth s!"level{depth}/sign/{i}" "sign"
      [("input", fraction encode f), ("value", toJson (Infinitesimal.sign baseSign f))]
    let g := xs[(i + 1) % xs.size]'(Nat.mod_lt _ (by omega))
    let result := match Infinitesimal.compare baseSign f g with
      | .lt => -1 | .eq => 0 | .gt => (1 : Int)
    emit depth s!"level{depth}/compare/{i}" "compare"
      [("left", fraction encode f), ("right", fraction encode g),
        ("difference", fraction encode (f - g)), ("value", toJson result)]

def run : IO Unit := do
  let e : RationalFn Rat := RationalFn.X
  -- de Moura–Passmore §4; see provenance.md alongside the generated fixtures.
  for (name, left, right) in #[
      ("paper/reciprocal", 1/e, (10^27 : RationalFn Rat)),
      ("paper/comparison-rational", 2 + 2*3 + 3^2 - 2*e - 2*3*e + e^2,
        (2 + 2*3 + 3^2 : RationalFn Rat))] do
    let result := match Infinitesimal.compare orderSign left right with
      | .lt => -1 | .eq => 0 | .gt => (1 : Int)
    emit 1 name "compare"
      [("left", fraction rational left), ("right", fraction rational right),
        ("difference", fraction rational (left - right)), ("value", toJson result)]
  values 1 rational orderSign #[0, e, -e, 1/e, 1/(e-1), (e^2-1)/(e-1),
    (1-e)/(e-1), e-e, e^8, e^8/(e^2-1), 2^128 * e^2 - e^3, e^2 / (e^3-e)]
  for i in [0, 1, 3, 8] do
    for a in [-3, -1, 1, 3] do
      let p : DensePoly Rat := DensePoly.monomial i a * (DensePoly.ofCoeffs #[-1, 1])
      let q : DensePoly Rat := DensePoly.ofCoeffs #[0, -2, 1]
      if hq : q ≠ 0 then
        let f := RationalFn.normalize p q hq
        emit 1 s!"normalize/{i}/{a}" "normalize"
          [("num", .arr (p.coeffs.map rational)), ("den", .arr (q.coeffs.map rational)),
            ("value", fraction rational f), ("sign", toJson (Infinitesimal.sign orderSign f))]
      else throw (IO.userError "fixture denominator vanished")
  let x : DensePoly Rat := DensePoly.monomial 1 1
  for (name, p, q) in #[
      ("normalize/nonmonic", x + 2, 1 - 2*x),
      ("normalize/negative-factor", (x-1)*(x+2), (x-1)*(x+3))] do
    if hq : q ≠ 0 then
      let f := RationalFn.normalize p q hq
      emit 1 name "normalize"
        [("num", .arr (p.coeffs.map rational)), ("den", .arr (q.coeffs.map rational)),
          ("value", fraction rational f), ("sign", toJson (Infinitesimal.sign orderSign f))]
    else throw (IO.userError "fixture denominator vanished")
  let d : RationalFn (RationalFn Rat) := RationalFn.X
  let c := RationalFn.C (K := RationalFn Rat)
  values 2 (fraction rational) (Infinitesimal.sign orderSign)
    #[0, d, c e, d-c e, d-c (e^8), c e+d, d/(c e-d), c e/d, 1/(d-c e),
      (d^2-c (e^2))/(d-c e), (c e-d)/(d-c e), d-d]
  let g : RationalFn (RationalFn (RationalFn Rat)) := RationalFn.X
  let c₂ := RationalFn.C (K := RationalFn (RationalFn Rat))
  values 3 (fraction (fraction rational)) (Infinitesimal.sign (Infinitesimal.sign orderSign))
    #[g, g-c₂ d, g-c₂ (d^3), c₂ (c e)-g, g / c₂ d, g-g]

end Hex.OrderedFn.Emit

def main : IO Unit := Hex.OrderedFn.Emit.run

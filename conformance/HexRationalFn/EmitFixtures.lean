/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRationalFn
import HexRationalFn.Domains
import Lean.Data.Json

open scoped HexRationalFn.Conformance

namespace HexRationalFn.Emit
open Hex Lean
attribute [local instance] Lean.Grind.Ring.intCast Lean.Grind.Semiring.natCast

private def inputs : Array (List Int × List Int) :=
  let h := (DensePoly.ofList [1, 1] : DensePoly Int) ^ (16 : Nat)
  #[
  ([], []), ([1], []), ([], [-3, 1]), ([2], [-2]), ([1], [2]), ([1, 2], [3, 2]), ([1], [0, 1]),
  ([-1, 0, 1], [-1, 1]), ([1, 2, 1], [0, 1, 1]),
  ([1, 0, 1], [0, 1]), ([1], [1, 1]), ([1], [0, -1, 0, 1]),
  ([0, 1], [1]), ([1, -2, 1], [-1, 1]),
  ([1, 0, 0, 0, 0, 0, 1], [-1, 0, 1]), ([1, 3, 3, 1], [1, 2, 1]),
  ((h * DensePoly.ofList [1, 0, 1]).toArray.toList,
    (h * DensePoly.ofList [0, 1]).toArray.toList)]

private def poly {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (encode : K → Json) (p : DensePoly K) : Json := .arr (p.toArray.map encode)

private def pair {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (encode : K → Json) (p q : DensePoly K) : Json :=
  Json.mkObj [("num", poly encode p), ("den", poly encode q)]

private def fraction {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (encode : K → Json) (f : RationalFn K) : Json := pair encode f.num f.den

private def optional {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (encode : K → Json) : Option (RationalFn K) → Json
  | none => .null
  | some f => fraction encode f

private def emitDomain {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (domain : String) (characteristic : Nat) (encode : K → Json) : IO Unit := do
  let out ← IO.getStdout
  let emit := fun (op : String) (operands : Array Json) (expected : Json) (extra : List (String × Json)) =>
    out.putStrLn (Json.mkObj ([("schema_version", toJson (1 : Nat)), ("domain", toJson domain),
      ("characteristic", toJson characteristic), ("operation", toJson op),
      ("operands", .arr operands), ("expected", expected)] ++ extra)).compress
  let mut values : Array (RationalFn K) := #[]
  for (ps, qs) in inputs do
    let p := DensePoly.ofList (ps.map Int.cast : List K)
    let q := DensePoly.ofList (qs.map Int.cast : List K)
    emit "normalize" #[pair encode p q] (optional encode (RationalFn.ofFraction? p q)) []
    if hq : q ≠ 0 then
      let f := RationalFn.normalize p q hq
      values := values.push f
      let c := RationalFn.certifyWith RationalFn.defaultPlan p q hq
      let mutations := #[c, { c with num := c.num + 1 }, { c with den := c.den + 1 },
        { c with s := c.s + 1 }, { c with t := c.t + 1 },
        { c with num := -c.num, den := -c.den, s := -c.s, t := -c.t },
        { c with s := c.s + c.den, t := c.t - c.num }]
      for cert in mutations do
        let cj := Json.mkObj [("num", poly encode cert.num), ("den", poly encode cert.den),
          ("s", poly encode cert.s), ("t", poly encode cert.t)]
        emit "check" #[pair encode p q] (toJson (RationalFn.check p q cert)) [("certificate", cj)]
  for hi : i in [:values.size] do
    have hv : i < values.size := by get_elem_tactic
    let f := values[i]
    let g := values[(i + 1) % values.size]'(Nat.mod_lt _ (by omega))
    let fs := #[fraction encode f]
    let both := #[fraction encode f, fraction encode g]
    for (op, value) in [("add", f + g), ("sub", f - g), ("mul", f * g), ("div", f / g)] do
      emit op both (fraction encode value) []
    emit "equal" both (toJson (f == g)) []
    emit "equal" #[fraction encode f, fraction encode f] (toJson true) []
    emit "div?" both (optional encode (RationalFn.div? f g)) []
    emit "neg" fs (fraction encode (-f)) []
    emit "inv" fs (fraction encode f⁻¹) []
    emit "inv?" fs (optional encode (RationalFn.inv? f)) []
    for n in [0, 1, 3] do
      emit "pow" fs (fraction encode (f ^ n)) [("exponent", toJson n)]
    emit "derivative" fs (fraction encode (RationalFn.derivative f)) []
    let (q, r) := RationalFn.split f
    emit "split" fs (Json.mkObj [("polynomial", poly encode q), ("proper", fraction encode r)]) []
    emit "toPoly?" fs (match RationalFn.toPoly? f with | none => .null | some p => poly encode p) []
    for n in [0, 1, 2] do
      let a : K := Nat.cast n
      emit "eval" fs (match RationalFn.eval? f a with | none => .null | some v => encode v)
        [("point", encode a)]

end HexRationalFn.Emit

def main : IO Unit := do
  HexRationalFn.Emit.emitDomain "QQ" 0 (fun a : Rat => Lean.Json.arr #[Lean.toJson a.num, Lean.toJson a.den])
  HexRationalFn.Emit.emitDomain "GF" 2 (fun a : Hex.ZMod64 2 => Lean.toJson a.toNat)
  HexRationalFn.Emit.emitDomain "GF" 7 (fun a : Hex.ZMod64 7 => Lean.toJson a.toNat)

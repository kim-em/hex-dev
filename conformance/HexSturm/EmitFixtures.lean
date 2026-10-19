/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSturm
import HexRealRoots.TarskiTests
import Hex.Conformance.Emit
import Lean.Data.Json

/-! Direct rational and noncanonical frontend fixtures. The pinned FLINT oracle
reads the original polynomials and endpoints; it does not replay Lean chains.
Producer replay controls accompany numerical results without claiming external
certificate soundness. -/
namespace Hex.Sturm.Emit
open Hex DensePoly Lean
open scoped Hex

private def x {E : Type} [Zero E] [One E] [DecidableEq E] : DensePoly E :=
  ofCoeffs #[0, 1]

private def rat (q : Rat) : Json := toJson #[q.num, (q.den : Int)]
private def poly (p : DensePoly Rat) : Json := .arr (p.toArray.map rat)
private def endpoint : Endpoint Rat → Json
  | .negInf => toJson "-inf"
  | .posInf => toJson "+inf"
  | .finite q => rat q

private def results {E : Type} [Zero E] [DecidableEq E] [One E] [Add E]
    [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [Div E] (sign : E → Int)
    (p : DensePoly E) (qs : List (DensePoly E)) (a b : Endpoint E) : Json :=
  let prepared := prepare sign p a b
  let retargeted := (prepare sign p .negInf .posInf).bind (fun d => d.withEndpoints? a b)
  let certificates := qs.map (certify sign (10575 : Nat) p · a b)
  Json.mkObj [
    ("query", toJson (qs.map (query sign p · a b))),
    ("reduced_query", toJson (qs.map (queryReduced sign p · a b))),
    ("root_count", toJson (rootCount sign p a b)),
    ("prepared", toJson prepared.isSome),
    ("prepared_query", toJson (prepared.map fun d => qs.map (queryPrepared d))),
    ("prepared_reduced_query", toJson (prepared.map fun d => qs.map (queryReducedPrepared d))),
    ("prepared_count", toJson (prepared.map countPrepared)),
    ("certificate_values", toJson (certificates.map (fun c => c.map TarskiCertificate.value))),
    ("producer_replay", toJson (certificates.zip qs |>.map fun (c, f) =>
      match c with
      | none => false
      | some cert => check sign 10575 p f a b cert.value cert)),
    ("wrong_value_replay", toJson (certificates.zip qs |>.map fun (c, f) =>
      match c with
      | none => false
      | some cert => check sign 10575 p f a b (cert.value + 1) cert)),
    ("prepared_certificate_values", toJson (prepared.map fun d => qs.map fun f =>
      (certifyPrepared (10575 : Nat) d f).value)),
    ("prepared_replay", toJson (prepared.map fun d => qs.map fun f =>
      let cert := certifyPrepared (10575 : Nat) d f
      check sign 10575 p f a b cert.value cert)),
    ("prepared_wrong_value_replay", toJson (prepared.map fun d => qs.map fun f =>
      let cert := certifyPrepared (10575 : Nat) d f
      check sign 10575 p f a b (cert.value + 1) cert)),
    ("count_certificate_value", toJson (prepared.map fun d =>
      (certifyCountPrepared (10575 : Nat) d).value)),
    ("count_certificate_replay", toJson (prepared.map fun d =>
      check sign 10575 p 1 a b (countPrepared d) (certifyCountPrepared (10575 : Nat) d))),
    ("count_certificate_wrong_replay", toJson (prepared.map fun d =>
      let cert := certifyCountPrepared (10575 : Nat) d
      check sign 10575 p 1 a b (cert.value + 1) cert)),
    ("retargeted", toJson retargeted.isSome),
    ("retargeted_query", toJson (retargeted.map fun d => qs.map (queryPrepared d))),
    ("retargeted_count", toJson (retargeted.map countPrepared))]

private def queries (p : DensePoly Rat) : List (DensePoly Rat) :=
  [1, 0, -1, x, x - 1, p, natPow x 8, scale (1 / 10 : Rat) x]

private def integerResults (p : DensePoly Rat) (qs : List (DensePoly Rat))
    (a b : Endpoint Rat) : Option (Int × List (Option Int)) := do
  let _ ← rootCount orderSign p a b
  match a, b with
  | .finite lower, .finite upper =>
    if lower.den != 1 || upper.den != 1 then none
    else if h : Dyadic.ofInt lower.num < Dyadic.ofInt upper.num then
      let interval := ⟨Dyadic.ofInt lower.num, Dyadic.ofInt upper.num, h⟩
      let head := (ZPoly.clearDenominators p).2
      some (ZPoly.sturmCount head interval,
        qs.map fun f => ZPoly.tarskiQuery head (ZPoly.clearDenominators f).2 interval)
    else none
  | _, _ => none

private def emit (name : String) (p : DensePoly Rat) (a b : Endpoint Rat) : IO Unit := do
  let qs := queries p
  let data := Json.mkObj [("schema", toJson (1 : Nat)), ("seed", toJson (10575 : Nat)),
    ("head", poly p), ("queries", toJson (qs.map poly)),
    ("lower", endpoint a), ("upper", endpoint b),
    ("storage", toJson "rational"), ("integer", toJson (integerResults p qs a b)),
    ("result", results orderSign p qs a b)]
  Hex.Conformance.Emit.emitResult "HexSturm" name "queries" data.compress

private def intervals : List (Endpoint Rat × Endpoint Rat) :=
  [(.negInf, .posInf), (.finite (-2), .finite 2), (.negInf, .finite 0),
   (.finite 0, .posInf), (.finite (-1), .finite 2), (.finite 2, .finite (-2)),
   (.finite 0, .finite 0), (.posInf, .negInf), (.negInf, .negInf),
   (.posInf, .posInf), (.finite (-2), .finite 1), (.posInf, .finite 2)]

private def core : List (String × DensePoly Rat) :=
  [("two-roots", x * x - 1), ("negative-head", 1 - x * x),
   ("non-monic", scale (2 / 3 : Rat) (x * x - 2)),
   ("cubic", x * x * x - x), ("zero-head", 0), ("constant", C 5),
   ("negative-constant", C (-5)), ("four-x", scale 4 x), ("repeated-head", (x - 1) * (x - 1)),
   ("root-free", x * x + 1), ("rational-root", x - C (1 / 3 : Rat))]

private def raw (a : HexPoly.InterpretTests.Rep) : Json :=
  let ab := HexPoly.InterpretTests.raw a
  toJson [rat ab.1, rat ab.2]

private def noncanonical (i : Nat) (a b : Endpoint Rat) : IO Unit := do
  let p := Hex.TarskiTests.Noncanonical.head
  let qs := [1, 0, -1, x, x - 1, p, natPow x 8,
    scale (HexPoly.InterpretTests.pack 0 (1 / 10 : Rat)) x]
  let stored : Endpoint Rat → Endpoint HexPoly.InterpretTests.Rep
    | .negInf => .negInf | .posInf => .posInf
    | .finite q => .finite (HexPoly.InterpretTests.pack (q / 2) (q / 2))
  let data := Json.mkObj [("schema", toJson (1 : Nat)), ("seed", toJson (10575 : Nat)),
    ("head", poly (DensePoly.ofCoeffs (p.toArray.map HexPoly.InterpretTests.value))),
    ("queries", toJson (qs.map fun q => poly (DensePoly.ofCoeffs (q.toArray.map HexPoly.InterpretTests.value)))),
    ("raw_head", toJson (p.toArray.toList.map raw)),
    ("raw_queries", toJson (qs.map fun q => q.toArray.toList.map raw)),
    ("raw_lower", match stored a with
      | .finite v => raw v | .negInf => toJson "-inf" | .posInf => toJson "+inf"),
    ("raw_upper", match stored b with
      | .finite v => raw v | .negInf => toJson "-inf" | .posInf => toJson "+inf"),
    ("lower", endpoint a), ("upper", endpoint b),
    ("storage", toJson "noncanonical"),
    ("integer", toJson (integerResults
      (DensePoly.ofCoeffs (p.toArray.map HexPoly.InterpretTests.value))
      (qs.map fun q => DensePoly.ofCoeffs (q.toArray.map HexPoly.InterpretTests.value)) a b)),
    ("result", results Hex.TarskiTests.Noncanonical.sign p qs (stored a) (stored b))]
  Hex.Conformance.Emit.emitResult "HexSturm" s!"noncanonical/{i}" "queries" data.compress

/-- Fixed core intervals and reproducible POSIX-LCG rational cubic inputs. -/
def run : IO Unit := do
  for (name, p) in core do
    for ((a, b), i) in intervals.zipIdx do
      emit s!"{name}/{i}" p a b
  let mut seed := 10575
  for i in [:24] do
    let mut coefficients : Array Rat := #[]
    for _ in [:4] do
      seed := (1103515245 * seed + 12345) % 2147483648
      coefficients := coefficients.push (mkRat (((seed % 11 : Nat) : Int) - 5) (seed % 5 + 1))
    emit s!"seed-10575/{i}/0" (ofCoeffs coefficients) .negInf .posInf
    emit s!"seed-10575/{i}/1" (ofCoeffs coefficients) (.finite (-2)) (.finite 2)
  for ((a, b), i) in intervals.zipIdx do
    noncanonical i a b

end Hex.Sturm.Emit

def main : IO Unit := Hex.Sturm.Emit.run

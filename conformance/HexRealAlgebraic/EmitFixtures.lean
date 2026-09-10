/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexRealAlgebraic.Checks
import HexNumberField.ComplexChecks
import Lean.Data.Json

/-! Self-contained JSONL results with exact polynomial-and-disc operand identities. -/

namespace Hex.RealAlgebraicEmit

open Lean
open RealAlgebraicNumber (ofRat ofAlgebraic? sqrt?)

private def rat (q : Rat) : Json := toJson #[q.num, (q.den : Int)]

private def algebraic (a : AlgebraicNumber) : Json :=
  let s := a.rep.1.square
  Json.mkObj [("poly", toJson a.p.toArray), ("re", rat s.re.toRat),
    ("im", rat s.im.toRat), ("prec", toJson s.prec)]

private def real (a : RealAlgebraicNumber) : Json := algebraic a.toAlgebraic

private def optional (a : Option RealAlgebraicNumber) : Json :=
  a.map real |>.getD Json.null

private def emit (case operation : String) (fields : List (String × Json)) : IO Unit :=
  Hex.Conformance.Emit.emitResult "HexRealAlgebraic" case operation
    (Json.mkObj (("schema", toJson (1 : Nat)) :: fields)).compress

private def ordering : Ordering → Int
  | .lt => -1
  | .eq => 0
  | .gt => 1

private def emitOrder (case : String) (a b : RealAlgebraicNumber) : IO Unit :=
  emit case "order" [("a", real a), ("b", real b),
    ("compare", toJson (ordering (compare a b))),
    ("reverse", toJson (ordering (compare b a))),
    ("eq", toJson (a == b)), ("lt", toJson (decide (a < b))),
    ("le", toJson (decide (a ≤ b))), ("gt", toJson (decide (b < a))),
    ("ge", toJson (decide (b ≤ a))), ("min", real (min a b)), ("max", real (max a b))]

private def emitScalar (case : String) (a : RealAlgebraicNumber) : IO Unit :=
  emit case "scalar" [("a", real a), ("sign", toJson a.sign), ("abs", real a.abs),
    ("floor", toJson a.floor), ("ceil", toJson a.ceil),
    ("rational", (a.toRat?.map rat).getD Json.null), ("sqrt", optional a.sqrt?),
    ("sqrtSquare", optional (a * a).sqrt?), ("conj", real a.conj)]

private def emitArithmetic (case : String) (a b : RealAlgebraicNumber) : IO Unit :=
  emit case "arithmetic" [("a", real a), ("b", real b),
    ("add", real (a + b)), ("sub", real (a - b)), ("mul", real (a * b)),
    ("div", real (a / b)), ("neg", real (-a)), ("inv", real a⁻¹),
    ("natPow", real (a ^ (3 : Nat))), ("intPow", real (a ^ (-2 : Int))),
    ("nsmul", real ((3 : Nat) • a)), ("zsmul", real ((-3 : Int) • a)),
    ("qsmul", real ((2 / 3 : Rat) • a))]

private def emitApprox (case : String) (a : RealAlgebraicNumber) (prec : Int) : IO Unit :=
  emit case "approx" [("a", real a), ("prec", toJson prec),
    ("center", rat (a.approx prec).toRat),
    ("radius", rat (a.approxBall prec).radius.toRat)]

private def counted (r : RealRootCount) : Json :=
  Json.mkObj [("root", real r.root), ("multiplicity", toJson r.multiplicity)]

private def emitIntegerRoots (case : String) (p : ZPoly) : IO Unit :=
  emit case "integerRoots" [("poly", toJson p.toArray),
    ("roots", Json.arr (p.realAlgebraicRoots.map real))]

private def emitRoots (case : String) (coefficients : Array RealAlgebraicNumber) : IO Unit :=
  let roots := (RealAlgebraicPoly.ofArray coefficients).roots
  emit case "algebraicRoots" [("coefficients", Json.arr (coefficients.map real)),
    ("roots", match roots with
      | .all => Json.null
      | .finite entries => Json.arr (entries.map counted))]

private def emitComplex : IO Unit := do
  let i := AlgebraicNumber.I
  for (case, a, b, n) in #[
      ("complex-zero", 0, 0, 0), ("complex-rational", 4, 5, 2),
      ("complex-cut", -8, 0, 3), ("complex-upper", i, 1 + i, 3), ("complex-fourth", -1, 0, 4),
      ("complex-lower", -i, i, 2), ("complex-same-side", i, 2 * i, 2),
      ("complex-above-cut", -1 + i / 16, -1, 2),
      ("complex-below-cut", -1 - i / 16, -1, 2)] do
    emit case "complex" [("a", algebraic a), ("b", algebraic b),
      ("conj", algebraic a.conj), ("re", real a.re), ("im", real a.im),
      ("sqrt", algebraic a.sqrt), ("n", toJson n), ("nthRoot", algebraic (a.nthRoot n)),
      ("lt", toJson (decide (a < b))), ("le", toJson (decide (a ≤ b)))]

/-- Emit every deterministic fixture after running the compiled core checks. -/
def run (localProfile : Bool := false) : IO Unit := do
  RealAlgebraicChecks.run true
  ComplexAlgebraicChecks.run
  emitComplex
  let some s := ofAlgebraic? (ZPoly.rootNear #p[-2, 0, 1] (3 / 2))
    | throw (IO.userError "sqrt(2) construction failed")
  let some t := ofAlgebraic? (ZPoly.rootNear #p[-8, 0, 1] 3)
    | throw (IO.userError "sqrt(8) construction failed")
  let q := ofRat (-3 / 2)
  for (case, a, b) in #[
      ("zero", 0, 0), ("rational", q, 0), ("sqrt-signs", -s, s),
      ("sqrt-lower", s, ofRat (7071 / 5000)),
      ("sqrt-upper", s, ofRat (14143 / 10000)),
      ("negative-lower", -s, ofRat (7071 / 5000)),
      ("negative-upper", -s, ofRat (14143 / 10000)),
      ("equal-sqrt", s, t / 2), ("equal-square", s * s, 2),
      ("equal-cancel", (s + 1) - s, 1), ("cross-factor", s, s + ofRat (1 / 4096))] do
    emitOrder case a b
  for (case, a) in #[("zero", 0), ("rational", q), ("sqrt", s), ("negative-sqrt", -s),
      ("negative-one", -1), ("rational-square", ofRat (9 / 4)),
      ("sqrt-above-two", s + 1),
      ("negative-integer", -2), ("positive-integer", 3)] do
    emitScalar case a
  emitArithmetic "zero" 0 0
  emitArithmetic "rational" q 0
  emitArithmetic "sqrt" s s
  for (case, a) in #[("zero", 0), ("rational", q), ("sqrt", s), ("negative-sqrt", -s)] do
    for prec in #[(-8 : Int), 0, 16] do
      emitApprox (case ++ "/" ++ toString prec) a prec
  let mignotte : ZPoly := #p[-2, 1024, -131072, 0, 0, 0, 0, 0, 1]
  emitIntegerRoots "mignotte" mignotte
  let near := mignotte.realAlgebraicRoots
  match near[1]?, near[2]? with
  | some a, some b =>
    emitOrder "mignotte-close" a b
    emitOrder "mignotte-left-rational" a (ofRat (1 / 256))
    emitOrder "mignotte-right-rational" (ofRat (1 / 256)) b
  | _, _ => throw (IO.userError "missing Mignotte roots")
  emitIntegerRoots "degree-eight" (#p[-2, 0, 1] * #p[-3, 0, 1] * #p[-5, 0, 1] * #p[-7, 0, 1])
  emitIntegerRoots "zero" #p[]
  emitIntegerRoots "constant" #p[7]
  emitIntegerRoots "nonreal" #p[1, 0, 1]
  emitRoots "irrational-coefficient" #[-s, 0, 1]
  emitRoots "repeated" #[1, -2, 1]
  emitRoots "zero" #[]
  emitRoots "constant" #[1]
  emitRoots "nonreal" #[1, 0, 1]
  for (a, i) in (ZPoly.algebraicRoots #p[1, 0, 1]).zipIdx do
    emit ("conjugate/" ++ toString i) "reject"
      [("a", algebraic a), ("accepted", toJson (ofAlgebraic? a).isSome)]
  emit "nonreal-coefficient" "rejectPolynomial"
    [("coefficients", Json.arr #[algebraic AlgebraicNumber.I]),
      ("accepted", toJson (RealAlgebraicPoly.ofAlgebraic?
        (AlgebraicPoly.ofArray #[AlgebraicNumber.I])).isSome)]
  for (case, a) in #[("zero", 0), ("rational", q), ("sqrt", s), ("negative-sqrt", -s)] do
    let b := a.toAlgebraic
    let re := AlgebraicNumber.Display.decimalValue b.rep.1.square.re.toRat
      (AlgebraicNumber.Display.digitsFor (mahlerPrec b.p))
    emit case "repr" [("a", real a), ("text", toJson (reprStr a)),
      ("roundtrip", optional (ofAlgebraic? (b.p.rootNear re)))]
  if localProfile then
    emitIntegerRoots "local-degree-twelve"
      (#p[-2, 0, 1] * #p[-3, 0, 1] * #p[-5, 0, 1] * #p[-7, 0, 1] * #p[-11, 0, 1] * #p[-13, 0, 1])
    let mut seed : Nat := 10141
    for i in [:8] do
      seed := (1664525 * seed + 1013904223) % 4294967296
      let r := ofRat (((seed % 17 : Nat) : Rat) - 8)
      emitOrder ("local-random-route/" ++ toString i) ((s + r) - r) s

/-- Emit actual Lean round-trip checks using each value's generated representation. -/
unsafe def reprChecks : IO Unit := do
  let some s := ofAlgebraic? (ZPoly.rootNear #p[-2, 0, 1] (3 / 2))
    | throw (IO.userError "sqrt(2) construction failed")
  IO.println "/-\nCopyright (c) 2026 Lean FRO, LLC. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Kim Morrison\n-/\n\nimport HexRealAlgebraic\n\n/-! Reproducible Repr round-trip fixtures; generated by hexrealalgebraic_emit_fixtures --repr. -/\n\nopen Hex\nopen Hex.RealAlgebraicNumber (ofRat ofAlgebraic?)\n"
  for ((expr, a), i) in #[("ofRat 0", 0), ("ofRat (-3 / 2)", ofRat (-3 / 2)),
      ("(ofAlgebraic? (ZPoly.rootNear #p[-2, 0, 1] (3 / 2))).getD 0", s),
      ("-((ofAlgebraic? (ZPoly.rootNear #p[-2, 0, 1] (3 / 2))).getD 0)", -s)].zipIdx do
    if i > 0 then IO.println ""
    IO.println ("#guard (" ++ reprStr a ++ ") == (" ++ expr ++ ")")
    IO.println ("#guard (" ++ reprStr (some a) ++ ") == some (" ++ expr ++ ")")

  for (expr, a) in #[("AlgebraicNumber.I.conj", AlgebraicNumber.I.conj),
      ("ZPoly.rootNear #p[-2, 0, 0, 1] (-1) (-1)",
        ZPoly.rootNear #p[-2, 0, 0, 1] (-1) (-1))] do
    IO.println ("\n#guard (" ++ reprStr a ++ ") == (" ++ expr ++ ")")
    let c := a.toQAdjoin
    IO.println ("#guard (" ++ reprStr c ++ ").toAlgebraicNumber == (" ++ expr ++ ")")
    let raw := PolyQuot.reduce a.p a.x (#p[0, 1] : DensePoly Rat)
    let repText := "⟨⟨" ++ Display.square a.rep.1.square ++ ", " ++
      Display.certificate a.rep.1.witness ++ "⟩, by decide⟩"
    IO.println ("#guard (if h : ZPoly.isIrreducible (" ++ reprStr a.p ++
      ") = true then letI : ZPoly.CheckedIrreducible (" ++ reprStr a.p ++
      ") := ⟨h, by decide⟩; (" ++ reprStr raw ++
      ").toAlgebraicNumber (" ++ repText ++ ") rfl == (" ++ expr ++ ") else false)")


end Hex.RealAlgebraicEmit

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [] => Hex.RealAlgebraicEmit.run
  | ["--local"] => Hex.RealAlgebraicEmit.run true
  | ["--repr"] => Hex.RealAlgebraicEmit.reprChecks
  | _ => throw (IO.userError "usage: hexrealalgebraic_emit_fixtures [--local|--repr]")

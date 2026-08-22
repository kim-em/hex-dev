/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexTruncatedSeries

/-!
JSONL fixtures for the SymPy truncated-series oracle.

The stream deliberately includes the precision-zero and precision-one surface
for both integer and rational coefficients, then the nonunit, branch-selection,
composition, reversion, and zero-extension cases called out by the SPEC.
-/

namespace HexTruncatedSeries.Emit

open Hex Hex.TSeries
open Hex.Conformance.Emit
open scoped Hex

private def lib : String := "HexTruncatedSeries"

private def coeffList (a : TSeries R n) : List R :=
  a.coeffs.toArray.toList

private def asRat (xs : List Int) : List Rat :=
  xs.map Rat.ofInt

private def emitInt (case : String) (a : TSeries Int n) : IO Unit :=
  emitSeriesFixture lib case "ZZ" n (asRat (coeffList a))

private def emitRat (case : String) (a : TSeries Rat n) : IO Unit :=
  emitSeriesFixture lib case "QQ" n (coeffList a)

private def resultInt (case op : String) (a : TSeries Int n) : IO Unit :=
  emitResult lib case op (seriesValue (asRat (coeffList a)))

private def resultRat (case op : String) (a : TSeries Rat n) : IO Unit :=
  emitResult lib case op (seriesValue (coeffList a))

private def resultOptInt (case op : String) (a : Option (TSeries Int n)) : IO Unit :=
  emitResult lib case op (optionSeriesValue (a.map fun x => asRat (coeffList x)))

private def resultOptRat (case op : String) (a : Option (TSeries Rat n)) : IO Unit :=
  emitResult lib case op (optionSeriesValue (a.map coeffList))

private def intInput (n : Nat) : TSeries Int n :=
  ofFn fun i => if i = 0 then 1 else if i = 1 then 1 else Int.ofNat (i + 1)

private def ratInput (n : Nat) : TSeries Rat n :=
  ofFn fun i => if i = 0 then 1 else if i = 1 then 1 else (i + 1 : Rat)

private def xInt (n : Nat) : TSeries Int n := X
private def xRat (n : Nat) : TSeries Rat n := X

private def xPlusSqInt (n : Nat) : TSeries Int n :=
  ofFn fun i => if i = 1 ∨ i = 2 then 1 else 0

private def xPlusSqRat (n : Nat) : TSeries Rat n :=
  ofFn fun i => if i = 1 ∨ i = 2 then 1 else 0

private instance intPrecisionTwoInverses : NatInverses Int (2 - 1) :=
  { invNat := fun _ => 1
    invNat_eq := by
      intro k hk hle
      have hk1 : k = 1 := by omega
      subst k
      decide }

private def emitIntSurface (n : Nat) [NatInverses Int n] : IO Unit := do
  let a := intInput n
  let stem := s!"int/{n}"
  emitInt (stem ++ "/input") a
  resultInt (stem ++ "/input") "neg" (-a)
  resultInt (stem ++ "/input") "add/self" (a + a)
  resultInt (stem ++ "/input") "mul/self" (a * a)
  resultInt (stem ++ "/input") "pow/3" (a ^ 3)
  resultInt (stem ++ "/input") "mulUpTo/1" (mulUpTo 1 a a)
  resultInt (stem ++ "/input") "truncate/self" (a.truncate n (Nat.le_refl n))
  resultInt (stem ++ "/input") "extend/plus1" (a.extend (n + 1) (by omega))
  resultInt (stem ++ "/input") "mulXPow/1" (a.mulXPow 1)
  resultOptInt (stem ++ "/input") "divXPow?/1" (divXPow? a 1)
  emitResult lib (stem ++ "/input") "valuation?"
    (match valuation? a with | none => "null" | some k => toString k)
  resultInt (stem ++ "/input") "deriv" a.deriv
  resultInt (stem ++ "/input") "integrate" (integrate a)
  resultInt (stem ++ "/input") "invOfUnit/1" (invOfUnit a 1)
  resultOptInt (stem ++ "/input") "inv?" (inv? a)
  resultOptInt (stem ++ "/input") "sqrt?/1" (sqrt? a 1)

  let inner := xInt n
  emitInt (stem ++ "/comp/outer") a
  emitInt (stem ++ "/comp/inner") inner
  resultInt (stem ++ "/comp") "comp" (comp a inner)
  resultInt (stem ++ "/comp") "compHorner" (compHorner a inner)
  resultOptInt (stem ++ "/comp") "comp?" (comp? a inner)

  let revInput := xPlusSqInt n
  emitInt (stem ++ "/rev") revInput
  resultInt (stem ++ "/rev") "revOfUnit/1" (revOfUnit revInput 1)
  resultOptInt (stem ++ "/rev") "rev?" (rev? revInput)

private def emitRatSurface (n : Nat) : IO Unit := do
  let a := ratInput n
  let stem := s!"rat/{n}"
  emitRat (stem ++ "/input") a
  resultRat (stem ++ "/input") "neg" (-a)
  resultRat (stem ++ "/input") "add/self" (a + a)
  resultRat (stem ++ "/input") "mul/self" (a * a)
  resultRat (stem ++ "/input") "pow/3" (a ^ 3)
  resultRat (stem ++ "/input") "mulUpTo/1" (mulUpTo 1 a a)
  resultRat (stem ++ "/input") "truncate/self" (a.truncate n (Nat.le_refl n))
  resultRat (stem ++ "/input") "extend/plus1" (a.extend (n + 1) (by omega))
  resultRat (stem ++ "/input") "mulXPow/1" (a.mulXPow 1)
  resultOptRat (stem ++ "/input") "divXPow?/1" (divXPow? a 1)
  emitResult lib (stem ++ "/input") "valuation?"
    (match valuation? a with | none => "null" | some k => toString k)
  resultRat (stem ++ "/input") "deriv" a.deriv
  resultRat (stem ++ "/input") "integrate" (integrate a)
  resultRat (stem ++ "/input") "invOfUnit/1" (invOfUnit a 1)
  resultOptRat (stem ++ "/input") "inv?" (inv? a)
  resultRat (stem ++ "/input") "sqrtOfRoot/1" (sqrtOfRoot a 1 (1 / 2))
  resultOptRat (stem ++ "/input") "sqrt?/1" (sqrt? a 1)

  let inner := xRat n
  emitRat (stem ++ "/comp/outer") a
  emitRat (stem ++ "/comp/inner") inner
  resultRat (stem ++ "/comp") "comp" (comp a inner)
  resultRat (stem ++ "/comp") "compHorner" (compHorner a inner)
  resultOptRat (stem ++ "/comp") "comp?" (comp? a inner)

  let revInput := xPlusSqRat n
  emitRat (stem ++ "/rev") revInput
  resultRat (stem ++ "/rev") "revOfUnit/1" (revOfUnit revInput 1)
  resultOptRat (stem ++ "/rev") "rev?" (rev? revInput)
  resultRat (stem ++ "/rev") "revLagrange" (revLagrange revInput 1)

private def emitLowExpLog : IO Unit := do
  emitInt "int/0/exp" (0 : TSeries Int 0)
  resultInt "int/0/exp" "exp" (exp (0 : TSeries Int 0))
  emitInt "int/0/log" (1 : TSeries Int 0)
  resultInt "int/0/log" "log" (log (1 : TSeries Int 0))
  emitInt "int/1/exp" (0 : TSeries Int 1)
  resultInt "int/1/exp" "exp" (exp (0 : TSeries Int 1))
  emitInt "int/1/log" (1 : TSeries Int 1)
  resultInt "int/1/log" "log" (log (1 : TSeries Int 1))
  let x2 := xInt 2
  emitInt "int/2/exp" x2
  resultInt "int/2/exp" "exp" (exp x2)
  let onePlusX2 := (1 : TSeries Int 2) + x2
  emitInt "int/2/log" onePlusX2
  resultInt "int/2/log" "log" (log onePlusX2)
  for n in [0, 1] do
    let x := xRat n
    emitRat s!"rat/{n}/exp" x
    resultRat s!"rat/{n}/exp" "exp" (exp x)
    let onePlusX := (1 : TSeries Rat n) + x
    emitRat s!"rat/{n}/log" onePlusX
    resultRat s!"rat/{n}/log" "log" (log onePlusX)

private def emitFailures : IO Unit := do
  for n in [0, 1, 4] do
    let a : TSeries Int n := ofFn fun i => if i = 0 then 2 else if i = 1 then 1 else 0
    emitInt s!"int/nonunit-inv/{n}" a
    resultOptInt s!"int/nonunit-inv/{n}" "inv?" (inv? a)

  for n in [0, 1, 2, 3, 4, 5, 6] do
    let b := xPlusSqInt n
    emitInt s!"int/rev-catalan/{n}" b
    resultOptInt s!"int/rev-catalan/{n}" "rev?" (rev? b)
    let twoX : TSeries Int n :=
      ofFn fun i => if i = 1 then 2 else if i = 2 then 1 else 0
    emitInt s!"int/rev-nonunit/{n}" twoX
    resultOptInt s!"int/rev-nonunit/{n}" "rev?" (rev? twoX)

  let badConst : TSeries Int 1 := C 1
  emitInt "int/rev-constant/1" badConst
  resultOptInt "int/rev-constant/1" "rev?" (rev? badConst)

  for n in [0, 1, 2, 3, 4] do
    let a : TSeries Int n := ofFn fun i => if i = 0 then 4 else if i = 1 then 1 else 0
    emitInt s!"int/sqrt-unit-boundary/{n}" a
    resultOptInt s!"int/sqrt-unit-boundary/{n}" "sqrt?/2" (sqrt? a 2)

  let q : TSeries Rat 5 := ofFn fun i => if i = 0 ∨ i = 1 then 1 else 0
  emitRat "rat/sqrt/positive" q
  resultRat "rat/sqrt/positive" "sqrtOfRoot/1" (sqrtOfRoot q 1 (1 / 2))
  emitRat "rat/sqrt/negative" q
  resultRat "rat/sqrt/negative" "sqrtOfRoot/-1" (sqrtOfRoot q (-1) (-1 / 2))
  emitRat "rat/sqrt/wrong-root" q
  resultOptRat "rat/sqrt/wrong-root" "sqrt?/2" (sqrt? q 2)

  for n in [1, 2, 3, 4, 5, 6] do
    let nonzeroInner : TSeries Rat n := C 1 + X
    emitRat s!"rat/comp/nonzero/{n}/outer" (ratInput n)
    emitRat s!"rat/comp/nonzero/{n}/inner" nonzeroInner
    resultOptRat s!"rat/comp/nonzero/{n}" "comp?"
      (comp? (ratInput n) nonzeroInner)

  let oversized : TSeries Int 3 := 0
  emitInt "int/divXPow/oversized" oversized
  resultOptInt "int/divXPow/oversized" "divXPow?/5" (divXPow? oversized 5)
  let badDiv : TSeries Int 4 := ofFn fun i => if i = 0 then 1 else 0
  emitInt "int/divXPow/nonzero-low" badDiv
  resultOptInt "int/divXPow/nonzero-low" "divXPow?/2" (divXPow? badDiv 2)

private def emitLarge : IO Unit := do
  let outer : TSeries Rat 12 := ofFn fun _ => 1
  let inner : TSeries Rat 12 := ofFn fun i => if i = 1 ∨ i = 2 then 1 else 0
  emitRat "rat/comp/geometric/outer" outer
  emitRat "rat/comp/geometric/inner" inner
  resultRat "rat/comp/geometric" "comp" (comp outer inner)
  resultRat "rat/comp/geometric" "compHorner" (compHorner outer inner)

  let b : TSeries Rat 8 := xPlusSqRat 8
  emitRat "rat/rev/routes" b
  resultRat "rat/rev/routes" "revOfUnit/1" (revOfUnit b 1)
  resultRat "rat/rev/routes" "revLagrange" (revLagrange b 1)

  for n in List.range 16 |>.drop 1 do
    let x := xRat (n + 1)
    emitRat s!"rat/exp/{n + 1}" x
    resultRat s!"rat/exp/{n + 1}" "exp" (exp x)
    let onePlusX := (1 : TSeries Rat (n + 1)) + x
    emitRat s!"rat/log/{n + 1}" onePlusX
    resultRat s!"rat/log/{n + 1}" "log" (log onePlusX)

  let x2 : TSeries Int 2 := X
  emitInt "int/extend/mul-before" x2
  resultInt "int/extend/mul-before" "mulThenExtend/3"
    ((x2 * x2).extend 3 (by omega))
  resultInt "int/extend/mul-before" "extendThenMul/3"
    (x2.extend 3 (by omega) * x2.extend 3 (by omega))

private def emitAll : IO Unit := do
  emitIntSurface 0
  emitIntSurface 1
  emitRatSurface 0
  emitRatSurface 1
  emitLowExpLog
  emitFailures
  emitLarge

end HexTruncatedSeries.Emit

def main : IO Unit :=
  HexTruncatedSeries.Emit.emitAll

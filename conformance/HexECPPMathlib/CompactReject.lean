/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPPMathlib.Compact

public section

example : Nat.Prime 17 := by
  ecpp using (ecpp_cert% "17" using (.small 17))

theorem computedSubject : Nat.Prime (2 ^ 4 + 1) := by
  ecpp using (ecpp_cert% "17" using (.small 17))

example : True := by
  fail_if_success
    have : Nat.Prime 19 := by
      ecpp using (ecpp_cert% "17" using (.small 17))
  fail_if_success
    have : Nat.Prime 35 := by
      ecpp using (ecpp_cert% "35" using (.small 35))
  fail_if_success
    have : Nat.Prime 17 := by
      ecpp using (ecpp_cert% "17" using (.small 19))
  fail_if_success
    have : Nat.Prime 17 := by
      ecpp using (ecpp_cert% "[]" using (.small 17))
  fail_if_success
    have : Nat.Prime 17 := by
      ecpp using (ecpp_cert% "17; quit" using (.small 17))
  fail_if_success
    have : Nat.Prime 17 := by
      ecpp using (ecpp_cert% "[[35,10,2,0,[15,16,15]]]" using (.small 13))
  trivial

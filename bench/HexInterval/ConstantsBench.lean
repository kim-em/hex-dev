/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval
import LeanBench

/-!
# Named-constant producer and checker acceptance measurements

These four fixed 1000-bit registrations are compiled acceptance/hash anchors.
They make no asymptotic or whole-library Phase-4 claim. Generation and replay
are timed separately; replay inputs are prepared before the timed region.
Both paths hash precision, order, the rational witness and both cuts; each
registration fixes the source identity.
The independent Fraction oracle checks the same source/order/precision inputs.
-/

namespace Hex.Interval.ConstantsBench

open Constants

initialize bitsRef : IO.Ref Nat ← IO.mkRef 1000

private def certificate (source : Source) (bits : Nat) : IO Certificate :=
  match enclose (limitsFor bits) source bits with
  | .ok c => pure c
  | .error e => throw (IO.userError s!"constant generation failed: {repr e}")

initialize piRef : IO.Ref (Option Certificate) ← IO.mkRef (some (← certificate .piMachinV1 1000))
initialize eRef : IO.Ref (Option Certificate) ← IO.mkRef (some (← certificate .expOneTaylorV1 1000))

private def report (c : Certificate) : List Int :=
  [c.bits, c.order, c.approximation.center.num, c.approximation.center.den,
    c.approximation.radius.num, c.approximation.radius.den,
    c.lower.toRat.num, c.lower.toRat.den, c.upper.toRat.num, c.upper.toRat.den]

@[noinline] def piGenerate (_ : Unit) : IO (List Int) := do
  pure (report (← certificate .piMachinV1 (← bitsRef.get)))

@[noinline] def eGenerate (_ : Unit) : IO (List Int) := do
  pure (report (← certificate .expOneTaylorV1 (← bitsRef.get)))

private def replay (source : Source) (c : Certificate) : IO (List Int) := do
  match check (limitsFor c.bits) source c.bits c with
  | .error e => throw (IO.userError s!"constant replay failed: {repr e}")
  | .ok _ => pure (report c)

@[noinline] def piCheck (_ : Unit) : IO (List Int) := do
  match ← piRef.get with
  | some c => replay .piMachinV1 c
  | none => throw (IO.userError "missing pi input")

@[noinline] def eCheck (_ : Unit) : IO (List Int) := do
  match ← eRef.get with
  | some c => replay .expOneTaylorV1 c
  | none => throw (IO.userError "missing e input")

setup_fixed_benchmark piGenerate where { repeats := 5, expectedHash := some 358707094099571319 }
setup_fixed_benchmark eGenerate where { repeats := 5, expectedHash := some 1127381572105118723 }
setup_fixed_benchmark piCheck where { repeats := 5, expectedHash := some 358707094099571319 }
setup_fixed_benchmark eCheck where { repeats := 5, expectedHash := some 1127381572105118723 }

end Hex.Interval.ConstantsBench

def main (args : List String) : IO UInt32 := do
  if args == ["hashes"] then
    for run in [Hex.Interval.ConstantsBench.piGenerate, Hex.Interval.ConstantsBench.eGenerate,
        Hex.Interval.ConstantsBench.piCheck, Hex.Interval.ConstantsBench.eCheck] do
      IO.println (hash (← run ()))
    pure 0
  else LeanBench.Cli.dispatch args

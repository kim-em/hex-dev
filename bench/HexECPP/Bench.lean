/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPP.Fixture65
import HexECPP.Fixture256
import HexECPP.Fixture512
import HexECPP.ImportConformance
import HexECPP.PariFixtures
import LeanBench

/-!
Mathlib-free compiled ECPP measurements. Conversion, checking, and raw
certificate size have separate registrations; kernel replay is measured in
fresh bridge proof modules.
-/

open Hex.ECPP

private instance : Inhabited Cert := ⟨.base (.small 2)⟩

initialize cert65Ref : IO.Ref Cert ← IO.mkRef Fixture65.cert
initialize cert256Ref : IO.Ref Cert ← IO.mkRef Fixture256.cert
initialize cert512Ref : IO.Ref Cert ← IO.mkRef Fixture512.cert
initialize pari65Ref : IO.Ref String ← IO.mkRef ImportConformance.pari65
initialize pari256Ref : IO.Ref String ← IO.mkRef PariFixtures.pari256
initialize pari512Ref : IO.Ref String ← IO.mkRef PariFixtures.pari512

def runCheck65 (_ : Unit) : IO Nat := do
  return if checkAt 18446744073709551629 (← cert65Ref.get) then 1 else 0

def runCheck256 (_ : Unit) : IO Nat := do
  return if check (← cert256Ref.get) then 1 else 0

def runCheck512 (_ : Unit) : IO Nat := do
  return if check (← cert512Ref.get) then 1 else 0

def runConvert65 (_ : Unit) : IO Nat := do
  return match convertText ImportConformance.budget (← pari65Ref.get)
      Fixture65.child with
  | .ok c => if check c then 1 else 0
  | .error _ => 0

def runConvert256 (_ : Unit) : IO Nat := do
  return match convertText defaultImportBudget (← pari256Ref.get)
      PariFixtures.leaf256 with
  | .ok c => if check c then 1 else 0
  | .error _ => 0

def runConvert512 (_ : Unit) : IO Nat := do
  return match convertText defaultImportBudget (← pari512Ref.get)
      PariFixtures.leaf512 with
  | .ok c => if check c then 1 else 0
  | .error _ => 0

def runParse512 (_ : Unit) : IO Nat := do
  return match parsePari defaultImportBudget (← pari512Ref.get) with
  | .ok c => c.rows.length
  | .error _ => 0

private partial def certSize : Cert → Nat
  | .base _ => 1
  | .step _ _ _ _ _ _ ws child => 1 + ws.length + certSize child

def runSize65 (_ : Unit) : IO Nat := return certSize (← cert65Ref.get)
def runSize256 (_ : Unit) : IO Nat := return certSize (← cert256Ref.get)
def runSize512 (_ : Unit) : IO Nat := return certSize (← cert512Ref.get)

setup_fixed_benchmark runCheck65 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runCheck256 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runCheck512 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runConvert65 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runConvert256 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runConvert512 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runParse512 where {
  repeats := 3
  expectedHash := some (hash (17 : Nat))
}
setup_fixed_benchmark runSize65 where { repeats := 3 }
setup_fixed_benchmark runSize256 where { repeats := 3 }
setup_fixed_benchmark runSize512 where { repeats := 3 }

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Driver.Sampled

def main (args : List String) : IO UInt32 := Hex.Groebner.Driver.Sampled.run args

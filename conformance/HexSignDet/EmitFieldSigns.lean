/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.CommonField

def main : IO Unit :=
  IO.println (Hex.SignDet.CommonField.scalarFixtures false).compress

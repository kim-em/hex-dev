/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.CommonField
import Hex.Conformance.Emit

open Hex

def main (args : List String) : IO Unit := do
  unless args.isEmpty || args == ["--legacy"] do
    throw (IO.userError "usage: hexsigndet_emit_common_fields [--legacy]")
  for (name, inputs) in [
      ("independent-quadratics", #[ZPoly.rootNear #p[-2, 0, 1] 1.4,
        ZPoly.rootNear #p[-3, 0, 1] 1.7]),
      ("reversed-quadratics", #[ZPoly.rootNear #p[-3, 0, 1] 1.7,
        ZPoly.rootNear #p[-2, 0, 1] 1.4]),
      ("independent-cubics", #[ZPoly.rootNear #p[-2, 0, 0, 1] 1.3,
        ZPoly.rootNear #p[-4, 0, 0, 1] 1.6])] do
    Hex.Conformance.Emit.emitResult "HexSignDet" ("common/" ++ name) "common-field"
      ((if args.isEmpty then Hex.SignDet.CommonField.fixture
        else Hex.SignDet.CommonField.fixtureLegacy) inputs).compress

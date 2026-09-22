/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Table
public import HexSignDet.Produce

public section

namespace Hex.SignDet

/-- Construct a sparse table from an accepted complete-support replay.
Internal construction diagnostics remain explicit until general producer
completeness is proved; this is not the total `determinePrepared` API. -/
def buildTablePrepared {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
    [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
    (context : Ctx) (domain : Sturm.PreparedDomain E) (qs : List (DensePoly E))
    (reduced : Bool := true) : Except BuildError (SignTable qs.length) :=
  match buildPrepared context domain qs reduced with
  | .error err => .error err
  | .ok t => .ok (t.val.table t.property)

end Hex.SignDet

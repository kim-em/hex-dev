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
Internal construction diagnostics are explicit for arbitrary coefficient
operations. The companion proves success for lawful interpretations. -/
def buildTablePrepared {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
    [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
    (context : Ctx) (domain : Sturm.PreparedDomain E) (qs : List (DensePoly E))
    (reduced : Bool := true) : Except BuildError (SignTable qs.length) :=
  match buildPrepared context domain qs reduced with
  | .error err => .error err
  | .ok t => .ok (t.val.table t.property)

/-- A successful prepared replay yields its exact checked sparse table. -/
theorem buildTablePrepared_ofReplay {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
    [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
    (context : Ctx) (domain : Sturm.PreparedDomain E) (qs : List (DensePoly E))
    (reduced : Bool)
    (t : {t : Replay E Ctx //
      t.check domain.sign context domain.head domain.lower domain.upper qs = true})
    (h : buildPrepared context domain qs reduced = .ok t) :
    buildTablePrepared context domain qs reduced = .ok (t.val.table t.property) := by
  simp only [buildTablePrepared, h]

/-- Total sign determination over a prepared domain, using the same checked
BKR producer. An internal error emits a diagnostic and returns an empty table;
the companion proves that branch unreachable with lawful coefficients,
using the shared proved root-sum theorem. -/
@[expose] def determinePrepared {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
    [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
    (context : Ctx) (domain : Sturm.PreparedDomain E) (qs : List (DensePoly E))
    (reduced : Bool := true) : SignTable qs.length :=
  match buildTablePrepared context domain qs reduced with
  | .ok table => table
  | .error err =>
    letI : Inhabited (SignTable qs.length) := ⟨SignTable.empty qs.length⟩
    panic! s!"determinePrepared: internal error {repr err}"

/-- The total API returns exactly the successful checked producer's table. -/
theorem determinePrepared_ofBuild {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
    [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
    (context : Ctx) (domain : Sturm.PreparedDomain E) (qs : List (DensePoly E))
    (reduced : Bool) (table : SignTable qs.length)
    (h : buildTablePrepared context domain qs reduced = .ok table) :
    determinePrepared context domain qs reduced = table := by
  simp only [determinePrepared, h]

/-- Sign determination returns `none` exactly when preparation rejects the
root domain. A valid domain uses the total prepared operation, retaining the
supplied query order and exact counts, including omitted conditions. -/
@[expose] def determine {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
    [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
    (sign : E → Int) (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (reduced : Bool := true) : Option (SignTable qs.length) :=
  match Sturm.prepare sign p a b with
  | none => none
  | some domain => some (determinePrepared context domain qs reduced)

end Hex.SignDet

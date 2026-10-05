/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean
public import HexSignDet.Codec.Json
public meta import HexSignDet.Codec.Json

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay
open Lean Hex.SignDet

mutual
/-- Quote untrusted integer-only JSON data as constructors. Acceptance still
requires checking the resulting expression and its literal subject bindings. -/
def jsonExpr : Codec.Json → Expr
  | .null => mkConst ``Codec.Json.Value.null
  | .bool value => mkApp (mkConst ``Codec.Json.Value.bool) (toExpr value)
  | .number value => mkApp (mkConst ``Codec.Json.Value.number) (toExpr value)
  | .string value => mkApp (mkConst ``Codec.Json.Value.string) (toExpr value)
  | .array values => mkApp (mkConst ``Codec.Json.Value.array) (valuesExpr values)
  | .object fields => mkApp (mkConst ``Codec.Json.Value.object) (fieldsExpr fields)
def valuesExpr : Codec.Json.Values → Expr
  | .nil => mkConst ``Codec.Json.Values.nil
  | .cons value rest => mkApp2 (mkConst ``Codec.Json.Values.cons) (jsonExpr value) (valuesExpr rest)
def fieldsExpr : Codec.Json.Fields → Expr
  | .nil => mkConst ``Codec.Json.Fields.nil
  | .cons key value rest => mkAppN (mkConst ``Codec.Json.Fields.cons)
      #[toExpr key, jsonExpr value, fieldsExpr rest]
end

/-- Change one literal JSON field only when its previous value is exactly the
expected input. Used to make certificate mutations independent of decoding. -/
def replace (j : Codec.Json) (path : List Nat) (expected value : Codec.Json) :
    Option Codec.Json := do
  match path with
  | [] => if j = expected then some value else none
  | i :: rest =>
    let values ← j.getArr?.toOption
    let old ← values[i]?
    let changed ← replace old rest expected value
    return Codec.Json.arr (values.set! i changed)

end Hex.RealClosure.Algebraic.KernelReplay

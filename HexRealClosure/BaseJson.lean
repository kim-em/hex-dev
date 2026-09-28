/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ContextData
public import HexRealClosure.BaseCodec
public import HexSignDet.Codec.Laws

public section

namespace Hex.RealClosure.BaseContext
open Tower Lean SignDet

mutual
/-- Structured base payloads preserve every recursive fraction level. -/
@[expose] def Syntax.literal : Syntax → Literal
  | .rational q => .array (.cons (.number 0 0)
      (.cons (.number q.num 0) (.cons (.number q.den 0) .nil)))
  | .fraction p q => .array (.cons (.number 1 0)
      (.cons (.array (Syntax.literals p)) (.cons (.array (Syntax.literals q)) .nil)))
@[expose] def Syntax.literals : List Syntax → Literals
  | [] => .nil
  | x :: xs => .cons x.literal (Syntax.literals xs)
end

mutual
/-- Canonical rationals and exact field counts are checked before the existing
base reader checks level shapes and nonzero fraction denominators. -/
@[expose] def Syntax.ofLiteral : Literal → Option Syntax
  | .array (.cons (.number 0 0) (.cons (.number n 0) (.cons (.number d 0) .nil))) =>
    let q := mkRat n d.toNat
    if 0 < d ∧ q.num = n ∧ (q.den : Int) = d then some (.rational q) else none
  | .array (.cons (.number 1 0) (.cons (.array p) (.cons (.array q) .nil))) => do
    return .fraction (← Syntax.ofLiterals p) (← Syntax.ofLiterals q)
  | _ => none
@[expose] def Syntax.ofLiterals : Literals → Option (List Syntax)
  | .nil => some []
  | .cons x xs => do return (← Syntax.ofLiteral x) :: (← Syntax.ofLiterals xs)
end

mutual
theorem Syntax.ofLiteral_literal (x : Syntax) : Syntax.ofLiteral x.literal = some x := by
  cases x with
  | rational q =>
    simp [Syntax.literal, Syntax.ofLiteral, Rat.mkRat_self, Nat.pos_of_ne_zero q.den_nz]
  | fraction p q =>
    simp [Syntax.literal, Syntax.ofLiteral, Syntax.ofLiterals_literals p,
      Syntax.ofLiterals_literals q]

theorem Syntax.ofLiterals_literals (xs : List Syntax) :
    Syntax.ofLiterals (Syntax.literals xs) = some xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [Syntax.literals, Syntax.ofLiterals,
      Syntax.ofLiteral_literal x, Syntax.ofLiterals_literals xs]
end

private def require {A : Type} (message : String) : Option A → Except String A
  | none => .error message
  | some a => .ok a

/-- Exact structured coefficient codec for one nominal staged base. Its
registry and native search progress remain attached to the supplied context. -/
def Element.codec {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign) : ValueCodec (Element context) where
  encode a := (context.write a.stored).literal.toJson
  decode j := do
    let literal ← require "unsupported base payload shape" (Literal.ofJson j)
    let raw ← require "invalid base payload" (Syntax.ofLiteral literal)
    let stored ← require "base coefficient rejected" (context.read raw)
    return ⟨stored⟩

theorem Element.codec_lawful {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign) : (Element.codec context).Lawful := by
  intro a
  rcases a with ⟨stored⟩
  simp [Element.codec, Literal.ofJson_toJson, Syntax.ofLiteral_literal,
    Context.read_write, require, bind, Except.bind, pure, Except.pure]

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.Element.codec_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Element.codec_lawful

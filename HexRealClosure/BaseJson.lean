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
open Tower SignDet

mutual
/-- Structured base payloads preserve every recursive fraction level. -/
@[expose] def Syntax.literal : Syntax → Literal
  | .rational q => .array (.cons (.number 0)
      (.cons (.number q.num) (.cons (.number q.den) .nil)))
  | .fraction p q => .array (.cons (.number 1)
      (.cons (.array (Syntax.literalsLoop p [])) (.cons (.array (Syntax.literalsLoop q [])) .nil)))
@[expose] def Syntax.literalsLoop : List Syntax → List Literal → Literals
  | [], acc => Literals.ofList acc.reverse
  | x :: xs, acc => Syntax.literalsLoop xs (x.literal :: acc)
end

@[expose] def Syntax.literals (xs : List Syntax) : Literals := Syntax.literalsLoop xs []

private theorem Syntax.literalsLoop_eq (xs : List Syntax) (acc : List Literal) :
    Syntax.literalsLoop xs acc = Literals.ofList (acc.reverse ++ xs.map Syntax.literal) := by
  induction xs generalizing acc with
  | nil => simp [Syntax.literalsLoop]
  | cons x xs ih => simp [Syntax.literalsLoop, ih, List.reverse_cons, List.append_assoc]

private theorem Syntax.literals_nil : Syntax.literals [] = .nil := rfl

private theorem Syntax.literals_cons (x : Syntax) (xs : List Syntax) :
    Syntax.literals (x :: xs) = .cons x.literal (Syntax.literals xs) := by
  simp [Syntax.literals, Syntax.literalsLoop_eq, Literals.ofList, Codec.Json.Values.ofList]

mutual
/-- Canonical rationals and exact field counts are checked before the existing
base reader checks level shapes and nonzero fraction denominators. -/
@[expose] def Syntax.ofLiteral : Literal → Option Syntax
  | .array (.cons (.number 0) (.cons (.number n) (.cons (.number d) .nil))) =>
    let q := mkRat n d.toNat
    if 0 < d ∧ q.num = n ∧ (q.den : Int) = d then some (.rational q) else none
  | .array (.cons (.number 1) (.cons (.array p) (.cons (.array q) .nil))) => do
    return .fraction (← Syntax.ofLiteralsLoop p []) (← Syntax.ofLiteralsLoop q [])
  | _ => none
@[expose] def Syntax.ofLiteralsLoop : Literals → List Syntax → Option (List Syntax)
  | .nil, acc => some acc.reverse
  | .cons x xs, acc => do
    let value ← Syntax.ofLiteral x
    Syntax.ofLiteralsLoop xs (value :: acc)
end

@[expose] def Syntax.ofLiterals (xs : Literals) : Option (List Syntax) :=
  Syntax.ofLiteralsLoop xs []

mutual
theorem Syntax.ofLiteral_literal (x : Syntax) : Syntax.ofLiteral x.literal = some x := by
  cases x with
  | rational q =>
    simp [Syntax.literal, Syntax.ofLiteral, Rat.mkRat_self, Nat.pos_of_ne_zero q.den_nz]
  | fraction p q =>
    change (do
      let numerator ← Syntax.ofLiteralsLoop (Syntax.literals p) []
      let denominator ← Syntax.ofLiteralsLoop (Syntax.literals q) []
      pure (Syntax.fraction numerator denominator)) = some (Syntax.fraction p q)
    simp [Syntax.ofLiteralsLoop_literals p [], Syntax.ofLiteralsLoop_literals q []]

theorem Syntax.ofLiteralsLoop_literals (xs : List Syntax) (acc : List Syntax) :
    Syntax.ofLiteralsLoop (Syntax.literals xs) acc = some (acc.reverse ++ xs) := by
  cases xs with
  | nil => simp [Syntax.literals_nil, Syntax.ofLiteralsLoop]
  | cons x xs => simp [Syntax.literals_cons, Syntax.ofLiteralsLoop,
      Syntax.ofLiteral_literal x, Syntax.ofLiteralsLoop_literals xs (x :: acc),
      List.reverse_cons, List.append_assoc]
end

theorem Syntax.ofLiterals_literals (xs : List Syntax) :
    Syntax.ofLiterals (Syntax.literals xs) = some xs := by
  simpa [Syntax.ofLiterals] using Syntax.ofLiteralsLoop_literals xs []

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

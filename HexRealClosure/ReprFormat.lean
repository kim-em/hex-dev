/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootBytes
public import Init.Data.String.Lemmas
import all HexSignDet.Codec.Bytes

public section

namespace Hex.RealClosure.Tower.ReprFormat
open SignDet
open SignDet.Codec (Json)

/-- A quoted argument for the checked reader expression. The argument is itself
printed JSON text, so control characters in stored names are already escaped. -/
@[expose] def quote (text : String) : String :=
  String.ofList (Codec.Token.writeTokens (Json.Value.string text).tokensLoop)

theorem quote_utf8 (text : String) : (quote text).toUTF8 = (Json.Value.string text).writeBytes := by
  unfold quote Json.Value.writeBytes Codec.Token.writeBytes
  rfl

@[expose] def header (reader : String) : String :=
  "(Hex.RealClosure.Tower.Catalog." ++ reader ++ " catalog "

@[expose] def suffix : String := " limits)"

/-- Reconstructible Lean code uses the caller's validated catalog and lexical
policy. The checked expression returns `Except`, retaining reader failures. -/
@[expose] def write (reader text : String) : String := header reader ++ quote text ++ suffix

/-- Read only the canonical checked expression, with exact function and argument
names. This is a finite format reader, not an evaluator for arbitrary Lean code. -/
@[expose] def argument (reader input : String) : Except String String := do
  let chars := input.toList
  let first := (header reader).toList
  if ¬ first <+: chars then throw "wrong reconstruction expression"
  let rest := chars.drop first.length
  let last := suffix.toList
  if ¬ last <:+ rest then throw "missing reconstruction policy"
  return String.ofList (rest.take (rest.length - last.length))

theorem argument_write (reader text : String) : argument reader (write reader text) = .ok (quote text) := by
  simp [argument, write, String.toList_append, List.IsPrefix, List.IsSuffix,
    pure, Except.pure]

/-- Bound the source expression before extracting its quoted JSON argument.
The argument is decoded by the shared UTF-8/JSON parser with the same policy. -/
@[expose] def read (reader input : String) (limits : Codec.Limits := {}) : Except String String := do
  if input.toUTF8.size > limits.bytes then throw "reconstruction expression byte limit exceeded"
  let literal ← argument reader input
  let value ← Codec.parse limits literal.toUTF8
  value.getStr?

/-- The canonical expression reader recovers the actual argument. Both
premises are lexical bounds; no parse or mathematical success is assumed. -/
theorem read_write (reader text : String) (limits : Codec.Limits)
    (sourceBound : (write reader text).toUTF8.size ≤ limits.bytes)
    (literalBound : Codec.checkBytes limits (quote text).toUTF8 = .ok ()) :
    read reader (write reader text) limits = .ok text := by
  unfold read
  rw [ite_eq_right (Nat.not_lt.mpr sourceBound), argument_write]
  simp only [bind, Except.bind]
  rw [quote_utf8] at literalBound ⊢
  rw [Codec.parse_write _ limits literalBound]
  rfl

end Hex.RealClosure.Tower.ReprFormat

/-- info: 'Hex.RealClosure.Tower.ReprFormat.argument_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReprFormat.argument_write
/-- info: 'Hex.RealClosure.Tower.ReprFormat.read_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReprFormat.read_write

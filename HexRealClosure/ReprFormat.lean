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

/-- A generated packet contains at most one nesting delimiter or decimal digit
per UTF-8 byte. The printer uses its own packet size rather than the untrusted
reader's default policy. -/
@[expose] def packetLimits (text : String) : Codec.Limits :=
  let size := text.toUTF8.size
  { bytes := size, depth := size + 1, digits := size + 1 }

/-- Direct-value reconstruction code. The named reader determines whether the
caller supplies `catalog` or the original indexed `parent`. -/
@[expose] def write (reader binding text : String) : String :=
  "(Hex.RealClosure.Tower." ++ reader ++ " " ++ binding ++ " " ++ quote text ++ ")"

end Hex.RealClosure.Tower.ReprFormat

/-- info: 'Hex.RealClosure.Tower.ReprFormat.quote_utf8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReprFormat.quote_utf8

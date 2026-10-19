/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootBytes
public import Init.Data.String.Lemmas
import all HexSignDet.Codec.Bytes
import all HexRealClosure.TowerBytes

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

/-- Parse a trusted printer-produced packet without applying an arbitrary
untrusted-input cap. Context and value validation still use the existing
structured checked reader. External input should use the bounded byte APIs. -/
@[expose] def readPacket (text : String) : Except String Serialized :=
  match Json.readBytes text.toUTF8 with
  | none => .error "invalid printed packet JSON or UTF-8"
  | some value => Serialized.codec.decode value

/-- Every generated packet parses successfully, with no acceptance premise. -/
theorem readPacket_write (raw : Serialized) : readPacket raw.writeText = .ok raw := by
  unfold readPacket
  rw [Serialized.writeText_utf8, Serialized.parse_write]
  exact Serialized.codec_lawful raw

/-- Direct-value reconstruction code. The named reader determines whether the
caller supplies `catalog` or the original indexed `parent`. -/
@[expose] def write (reader binding text : String) : String :=
  "(Hex.RealClosure.Tower." ++ reader ++ " " ++ binding ++ " " ++ quote text ++ ")"

end Hex.RealClosure.Tower.ReprFormat

/-- info: 'Hex.RealClosure.Tower.ReprFormat.quote_utf8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReprFormat.quote_utf8

/-- info: 'Hex.RealClosure.Tower.ReprFormat.readPacket_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReprFormat.readPacket_write

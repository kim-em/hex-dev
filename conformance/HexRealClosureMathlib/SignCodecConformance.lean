/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.PackingConformance
public meta import HexRealClosureMathlib.PackingConformance
public meta import HexRealClosureMathlib.CoefficientSignsConformance
public import HexRealClosureMathlib.SignCodec
public meta import HexRealClosureMathlib.SignCodec
public import HexSignDet.Codec.Bytes
public meta import HexSignDet.Codec.Bytes
import all HexRealClosure.Algebraic
import all HexRealClosure.AlgebraicCodec
import all HexRealClosureMathlib.SignCodec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json

public section

namespace Hex.RealClosure.Algebraic.SignCodecConformance
open SignDet
open CoefficientSignsConformance PackingConformance

@[expose] def reader := Element.signCodec ValueCodec.rat literalFacts
@[expose] def literalJson := (Element.codec ValueCodec.rat).encode literal

/- Exact literal restoration needs no producer, including canonical zero.
Changing the sign, removing the fact or supplying a semantically equal but
structurally different representative rejects. -/
set_option maxRecDepth 32768 in
theorem literal_reader :
    reader.decode literalJson = .ok literal ∧
    reader.decode (.arr #[]) = .ok 0 ∧
    reader.decode (.arr #[Codec.poly ValueCodec.rat stored, .number (-1)]) =
      .error "stored sign fact missing or mismatched" ∧
    (Element.signCodec ValueCodec.rat ([] : List (SignFact context))).decode literalJson =
      .error "stored sign fact missing or mismatched" ∧
    reader.decode ((Element.codec ValueCodec.rat).encode small) =
      .error "stored sign fact missing or mismatched" := by
  decide +kernel

/- A JSON byte roundtrip still passes through the strict literal reader. -/
#guard reader.decodeBytes literalJson.writeBytes == .ok literal
#guard (Element.signCodec ValueCodec.rat ([] : List (SignFact context))).decodeBytes
  literalJson.writeBytes == .error "stored sign fact missing or mismatched"
-- The shared printer ends each token with a space; removing just that space is valid.
#guard reader.decodeBytes (literalJson.writeBytes.extract 0 (literalJson.writeBytes.size - 1)) == .ok literal
#guard (reader.decodeBytes (literalJson.writeBytes.extract 0 (literalJson.writeBytes.size - 2))).toOption.isNone

/-- info: 'Hex.RealClosure.Algebraic.Element.signCodec_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Element.signCodec_sound

end Hex.RealClosure.Algebraic.SignCodecConformance

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SourceIdentityPacket
import HexSignDet.Codec.Bytes
open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests Hex.RCF.SourceIdentityCases
open Hex.RCF.SelectedRootTests.SourceIdentityPackets

/-! Build-only input production, separate from the frozen source quotation.
The emitted bytes propose evidence; the importing kernel audits check replay.
This Mathlib-importing generator is not a runtime benchmark. -/

private def stored (packet : Codec.Json × Int × Codec.Json) : Codec.Json :=
  .arr #[packet.1,Codec.Json.of packet.2.1,packet.2.2]

#eval (show IO Unit from do
  let some equation := ScalarPacket.build Data.native Data.base.codec
      (embed (ZPoly.toRatPoly SquareTwo.polynomial))
    | throw (IO.userError "source equation production rejected")
  let some enclosure := ScalarPacket.build Data.native Data.base.codec
      (embed (SourceIdentity.margin SquareTwo.square))
    | throw (IO.userError "source enclosure production rejected")
  let some negative := ScalarPacket.build Data.native Data.base.codec
      (embed (SourceIdentity.margin negativeSquare))
    | throw (IO.userError "negative enclosure production rejected")
  let proposed := Codec.Json.arr #[equation,enclosure,negative]
  let frozen := Codec.Json.arr #[stored packet0,stored packet1,stored packet2]
  unless proposed.writeBytes == frozen.writeBytes do
    throw (IO.userError "source-identity proposals differ from the frozen packets")
  if let some path ← IO.getEnv "HEX_RCF_SOURCE_IDENTITY_OUTPUT" then
    IO.FS.writeBinFile path proposed.writeBytes
  IO.println s!"source-identity proposals match frozen packets ({proposed.writeBytes.size} bytes); replay is checked separately")

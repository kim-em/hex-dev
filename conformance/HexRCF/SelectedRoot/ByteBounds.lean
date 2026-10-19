/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SelectedRoot.ByteData
public import Batteries.Data.Except

public section

open Hex.SignDet
namespace Hex.RCF.SelectedRootTests.ByteBounds

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem bounded : Codec.checkBytes {} Hex.RCF.SelectedRootTests.ByteData.literal = .ok () := by
  unfold Codec.checkBytes
  simp only [Codec.forIn_data, ← Array.forIn_toList]
  decide +kernel

end Hex.RCF.SelectedRootTests.ByteBounds

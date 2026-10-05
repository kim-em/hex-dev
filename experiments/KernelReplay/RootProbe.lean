/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import KernelReplay.Root
import all KernelReplay.Root
import all HexRealClosure.Algebraic
import all HexRealClosure.RootReplay
import all HexRealClosure.SignCodec
import all HexRealClosure.SignRequests
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Value
import all HexSignDet.Dag
import all HexSignDet.Descriptor
import all HexRealRoots.TarskiShared
import all HexPoly.Euclid.DivGcd
import all Init.Data.Array.Basic

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#root_replay_probe

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import KernelReplay.FactOperations
import all HexRealClosure.Algebraic
import all HexRealClosure.FactOperations
import all HexPoly.Euclid.DivGcd
import all Init.Data.Array.Basic
import all HexSignDet.Descriptor
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Value
import all HexRealRoots.TarskiShared

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#fact_operations_probe

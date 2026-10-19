/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Codec.Json
public import HexRCF.CellReplay.MutationData0
/-! Shared constructor data from `conformance-fixtures/HexRCF/cell-replay-mutations.json`.
The descriptor reader checks this supplied replay independently of its producer. -/
public section

namespace Hex.RCF.RealCoefficients.CellReplayTests.Mutations
open Hex.SignDet
@[expose] def j247 : Codec.Json := .array (.cons (j244) (.cons (j151) (.cons (j51) (.cons (j1) (.cons (j246) .nil)))))
@[expose] def j248 : Codec.Json := .array (.cons (j2) (.cons (j242) (.cons (j26) (.cons (j6) (.cons (j7) (.cons (j247) (.cons (j247) (.cons (j9) (.cons (j46) (.cons (.number (1)) (.cons (.number (0)) (.cons (.number (1)) .nil))))))))))))
@[expose] def j249 : Codec.Json := .array (.cons (j248) .nil)
@[expose] def j250 : Codec.Json := .array (.cons (j2) (.cons (j242) (.cons (j6) (.cons (j7) (.cons (j1) (.cons (.number (1)) (.cons (j149) (.cons (j249) (.cons (j155) (.cons (j148) (.cons (j88) .nil)))))))))))
@[expose] def j251 : Codec.Json := .array (.cons (j250) (.cons (j1) .nil))
@[expose] def j252 : Codec.Json := .array (.cons (j251) .nil)
@[expose] def j253 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) (.cons (j252) .nil)))
@[expose] def j254 : Codec.Json := .array (.cons (j4) (.cons (j144) (.cons (j146) (.cons (j243) (.cons (j253) (.cons (j226) .nil))))))
@[expose] def otherRoot : Codec.Json := j254
@[expose] def j255 : Codec.Json := .array (.cons (.number (0)) (.cons (j1) (.cons (j1) (.cons (.number (1)) (.cons (j1) .nil)))))
@[expose] def j256 : Codec.Json := .array (.cons (j2) (.cons (j11) (.cons (j6) (.cons (j7) (.cons (j160) (.cons (.number (1)) (.cons (j215) (.cons (j154) (.cons (j155) (.cons (j219) (.cons (j255) .nil)))))))))))
@[expose] def j257 : Codec.Json := .array (.cons (j256) (.cons (j222) .nil))
@[expose] def j258 : Codec.Json := .array (.cons (j185) (.cons (j201) (.cons (j212) (.cons (j257) .nil))))
@[expose] def j259 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (3)) (.cons (j258) .nil)))
@[expose] def j260 : Codec.Json := .array (.cons (.number (1)) (.cons (j147) (.cons (j160) (.cons (j161) (.cons (j259) .nil)))))
@[expose] def j261 : Codec.Json := .array (.cons (j4) (.cons (j144) (.cons (j146) (.cons (j147) (.cons (j159) (.cons (j260) .nil))))))
@[expose] def missingBasis : Codec.Json := j261
end Hex.RCF.RealCoefficients.CellReplayTests.Mutations

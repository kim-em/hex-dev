/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Codec.Json
public import HexRCF.EnumeratedSource.PositiveData0
/-! Shared constructor data from `conformance-fixtures/HexRCF/enumerated-source.json`.
The descriptor reader checks this supplied replay independently of its producer. -/
public section

namespace Hex.RCF.RealCoefficients.EnumeratedSource.Positive
open Hex.SignDet
@[expose] def j235 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (-1)) (.cons (.number (-1)) (.cons (.number (1)) .nil))))
@[expose] def j236 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (1)) (.cons (.number (-1)) (.cons (.number (-1)) .nil))))
@[expose] def j237 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (-1)) (.cons (.number (1)) (.cons (.number (-1)) .nil))))
@[expose] def j238 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (1)) (.cons (.number (1)) (.cons (.number (1)) .nil))))
@[expose] def j239 : Codec.Json := .array (.cons (j235) (.cons (j236) (.cons (j237) (.cons (j238) .nil))))
@[expose] def j240 : Codec.Json := .array (.cons (j229) (.cons (j232) (.cons (j233) (.cons (j234) (.cons (j239) (.cons (.number (4)) .nil))))))
@[expose] def j241 : Codec.Json := .array (.cons (j5) (.cons (j161) (.cons (j24) .nil)))
@[expose] def j242 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (370688)) (.cons (.number (131057)) .nil)))
@[expose] def j243 : Codec.Json := .array (.cons (j4) (.cons (j185) (.cons (j242) .nil)))
@[expose] def j244 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (131057)) (.cons (.number (92672)) .nil)))
@[expose] def j245 : Codec.Json := .array (.cons (j244) (.cons (j4) .nil))
@[expose] def j246 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (261919)) (.cons (.number (8588099584)) .nil)))
@[expose] def j247 : Codec.Json := .array (.cons (j4) (.cons (j245) (.cons (j246) .nil)))
@[expose] def j248 : Codec.Json := .array (.cons (j247) .nil)
@[expose] def j249 : Codec.Json := .array (.cons (j4) (.cons (j161) .nil))
@[expose] def j250 : Codec.Json := .array (.cons (j249) .nil)
@[expose] def j251 : Codec.Json := .array (.cons (j241) (.cons (j27) (.cons (j243) (.cons (j248) (.cons (j250) .nil)))))
@[expose] def j252 : Codec.Json := .array (.cons (j1) (.cons (j5) (.cons (j163) (.cons (j6) (.cons (j7) (.cons (j33) (.cons (j251) (.cons (j34) (.cons (j35) (.cons (.number (2)) (.cons (.number (0)) (.cons (.number (2)) .nil))))))))))))
@[expose] def j253 : Codec.Json := .array (.cons (j36) (.cons (j179) (.cons (j45) (.cons (j252) .nil))))
@[expose] def j254 : Codec.Json := .array (.cons (.number (2)) (.cons (j161) (.cons (j49) .nil)))
@[expose] def j255 : Codec.Json := .array (.cons (j254) .nil)
@[expose] def j256 : Codec.Json := .array (.cons (j255) (.cons (j161) .nil))
@[expose] def j257 : Codec.Json := .array (.cons (j256) .nil)
@[expose] def j258 : Codec.Json := .array (.cons (j4) (.cons (j24) (.cons (j244) .nil)))
@[expose] def j259 : Codec.Json := .array (.cons (.number (2)) (.cons (j163) (.cons (j258) .nil)))
@[expose] def j260 : Codec.Json := .array (.cons (j50) (.cons (j259) .nil))
@[expose] def j261 : Codec.Json := .array (.cons (j260) (.cons (j163) .nil))
@[expose] def j262 : Codec.Json := .array (.cons (j261) .nil)
@[expose] def j263 : Codec.Json := .array (.cons (j48) (.cons (j257) (.cons (j53) (.cons (j262) .nil))))
@[expose] def j264 : Codec.Json := .array (.cons (.number (2)) (.cons (j161) (.cons (j208) .nil)))
@[expose] def j265 : Codec.Json := .array (.cons (j60) (.cons (j98) (.cons (j264) .nil)))
@[expose] def j266 : Codec.Json := .array (.cons (j265) .nil)
@[expose] def j267 : Codec.Json := .array (.cons (j1) (.cons (j5) (.cons (j6) (.cons (j7) (.cons (j228) (.cons (.number (4)) (.cons (j240) (.cons (j253) (.cons (j263) (.cons (j266) (.cons (j66) .nil)))))))))))
@[expose] def j268 : Codec.Json := .array (.cons (j267) (.cons (j150) .nil))
@[expose] def j269 : Codec.Json := .array (.cons (j68) (.cons (j88) (.cons (j213) (.cons (j227) (.cons (j268) .nil)))))
@[expose] def j270 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (4)) (.cons (j269) .nil)))
@[expose] def marginGraph : Codec.Json := j270
@[expose] def j271 : Codec.Json := .array (.cons (j5) (.cons (.number (0)) (.cons (j153) .nil)))
@[expose] def j272 : Codec.Json := .array (.cons (j156) (.cons (.number (1)) (.cons (j270) .nil)))
@[expose] def j273 : Codec.Json := .array (.cons (j10) (.cons (j105) (.cons (j271) (.cons (j272) .nil))))
@[expose] def packet : Codec.Json := j273
end Hex.RCF.RealCoefficients.EnumeratedSource.Positive

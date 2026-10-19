/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Codec.Json
public import HexRCF.EnumeratedSource.NegativeData0
/-! Shared constructor data from `conformance-fixtures/HexRCF/enumerated-source.json`.
The descriptor reader checks this supplied replay independently of its producer. -/
public section

namespace Hex.RCF.RealCoefficients.EnumeratedSource.Negative
open Hex.SignDet
@[expose] def j235 : Codec.Json := .array (.cons (.number (2)) (.cons (.number (0)) (.cons (.number (0)) (.cons (.number (-2)) .nil))))
@[expose] def j236 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (-1)) (.cons (.number (-1)) (.cons (.number (1)) .nil))))
@[expose] def j237 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (1)) (.cons (.number (-1)) (.cons (.number (-1)) .nil))))
@[expose] def j238 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (-1)) (.cons (.number (1)) (.cons (.number (-1)) .nil))))
@[expose] def j239 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (1)) (.cons (.number (1)) (.cons (.number (1)) .nil))))
@[expose] def j240 : Codec.Json := .array (.cons (j236) (.cons (j237) (.cons (j238) (.cons (j239) .nil))))
@[expose] def j241 : Codec.Json := .array (.cons (j230) (.cons (j233) (.cons (j234) (.cons (j235) (.cons (j240) (.cons (.number (4)) .nil))))))
@[expose] def j242 : Codec.Json := .array (.cons (j5) (.cons (j161) (.cons (j24) .nil)))
@[expose] def j243 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (370688)) (.cons (.number (131057)) .nil)))
@[expose] def j244 : Codec.Json := .array (.cons (j4) (.cons (j166) (.cons (j243) .nil)))
@[expose] def j245 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (131057)) (.cons (.number (92672)) .nil)))
@[expose] def j246 : Codec.Json := .array (.cons (j245) (.cons (j20) .nil))
@[expose] def j247 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (261919)) (.cons (.number (8588099584)) .nil)))
@[expose] def j248 : Codec.Json := .array (.cons (j4) (.cons (j246) (.cons (j247) .nil)))
@[expose] def j249 : Codec.Json := .array (.cons (j248) .nil)
@[expose] def j250 : Codec.Json := .array (.cons (j4) (.cons (j161) .nil))
@[expose] def j251 : Codec.Json := .array (.cons (j250) .nil)
@[expose] def j252 : Codec.Json := .array (.cons (j242) (.cons (j27) (.cons (j244) (.cons (j249) (.cons (j251) .nil)))))
@[expose] def j253 : Codec.Json := .array (.cons (j1) (.cons (j5) (.cons (j163) (.cons (j6) (.cons (j7) (.cons (j33) (.cons (j252) (.cons (j35) (.cons (j34) (.cons (.number (0)) (.cons (.number (2)) (.cons (.number (-2)) .nil))))))))))))
@[expose] def j254 : Codec.Json := .array (.cons (j36) (.cons (j180) (.cons (j46) (.cons (j253) .nil))))
@[expose] def j255 : Codec.Json := .array (.cons (.number (2)) (.cons (j161) (.cons (j50) .nil)))
@[expose] def j256 : Codec.Json := .array (.cons (j255) .nil)
@[expose] def j257 : Codec.Json := .array (.cons (j256) (.cons (j161) .nil))
@[expose] def j258 : Codec.Json := .array (.cons (j257) .nil)
@[expose] def j259 : Codec.Json := .array (.cons (j4) (.cons (j164) (.cons (j245) .nil)))
@[expose] def j260 : Codec.Json := .array (.cons (.number (2)) (.cons (j163) (.cons (j259) .nil)))
@[expose] def j261 : Codec.Json := .array (.cons (j51) (.cons (j260) .nil))
@[expose] def j262 : Codec.Json := .array (.cons (j261) (.cons (j163) .nil))
@[expose] def j263 : Codec.Json := .array (.cons (j262) .nil)
@[expose] def j264 : Codec.Json := .array (.cons (j49) (.cons (j258) (.cons (j54) (.cons (j263) .nil))))
@[expose] def j265 : Codec.Json := .array (.cons (.number (2)) (.cons (j161) (.cons (j209) .nil)))
@[expose] def j266 : Codec.Json := .array (.cons (j61) (.cons (j98) (.cons (j265) .nil)))
@[expose] def j267 : Codec.Json := .array (.cons (j266) .nil)
@[expose] def j268 : Codec.Json := .array (.cons (.number (-1)) (.cons (.number (-1)) .nil))
@[expose] def j269 : Codec.Json := .array (.cons (j268) (.cons (j9) .nil))
@[expose] def j270 : Codec.Json := .array (.cons (.number (2)) (.cons (j64) (.cons (j64) (.cons (.number (-2)) (.cons (j269) .nil)))))
@[expose] def j271 : Codec.Json := .array (.cons (j1) (.cons (j5) (.cons (j6) (.cons (j7) (.cons (j229) (.cons (.number (4)) (.cons (j241) (.cons (j254) (.cons (j264) (.cons (j267) (.cons (j270) .nil)))))))))))
@[expose] def j272 : Codec.Json := .array (.cons (j271) (.cons (j150) .nil))
@[expose] def j273 : Codec.Json := .array (.cons (j69) (.cons (j89) (.cons (j214) (.cons (j228) (.cons (j272) .nil)))))
@[expose] def j274 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (4)) (.cons (j273) .nil)))
@[expose] def marginGraph : Codec.Json := j274
@[expose] def j275 : Codec.Json := .array (.cons (j5) (.cons (.number (0)) (.cons (j153) .nil)))
@[expose] def j276 : Codec.Json := .array (.cons (j156) (.cons (.number (1)) (.cons (j274) .nil)))
@[expose] def j277 : Codec.Json := .array (.cons (j10) (.cons (j105) (.cons (j275) (.cons (j276) .nil))))
@[expose] def packet : Codec.Json := j277
end Hex.RCF.RealCoefficients.EnumeratedSource.Negative

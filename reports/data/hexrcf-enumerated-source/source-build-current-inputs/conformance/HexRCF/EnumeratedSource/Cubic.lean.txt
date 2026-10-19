/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Codec.Json
public import HexRCF.EnumeratedSource.CubicData0
/-! Shared constructor data from `conformance-fixtures/HexRCF/enumerated-source.json`.
The descriptor reader checks this supplied replay independently of its producer. -/
public section

namespace Hex.RCF.RealCoefficients.EnumeratedSource.Cubic
open Hex.SignDet
@[expose] def j235 : Codec.Json := .array (.cons (j5) (.cons (j232) (.cons (j234) (.cons (j202) .nil))))
@[expose] def j236 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (-19317815121)) (.cons (.number (10224230144)) .nil)))
@[expose] def j237 : Codec.Json := .array (.cons (j236) (.cons (j11) .nil))
@[expose] def j238 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (1595863148103357)) (.cons (.number (670055146717184)) .nil)))
@[expose] def j239 : Codec.Json := .array (.cons (j4) (.cons (j237) (.cons (j238) .nil)))
@[expose] def j240 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (-1340110293434368)) (.cons (.number (531954382701119)) .nil)))
@[expose] def j241 : Codec.Json := .array (.cons (j240) (.cons (j18) .nil))
@[expose] def j242 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (1346921726276322561523562446848)) (.cons (.number (282975465274928573198483852161)) .nil)))
@[expose] def j243 : Codec.Json := .array (.cons (j4) (.cons (j241) (.cons (j242) .nil)))
@[expose] def j244 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (-451144542095674201519953963846426420385261889)) (.cons (.number (358250457724023371626526318932137133553811456)) .nil)))
@[expose] def j245 : Codec.Json := .array (.cons (j244) (.cons (j4) .nil))
@[expose] def j246 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (860908980737602065149122892520026022839822591)) (.cons (.number (453549534178797199769117499790381448220762277801366206283776)) .nil)))
@[expose] def j247 : Codec.Json := .array (.cons (j4) (.cons (j245) (.cons (j246) .nil)))
@[expose] def j248 : Codec.Json := .array (.cons (j243) (.cons (j247) .nil))
@[expose] def j249 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (-848507517748138632283156122497)) (.cons (.number (673460863138161280761781223424)) .nil)))
@[expose] def j250 : Codec.Json := .array (.cons (j249) (.cons (j4) .nil))
@[expose] def j251 : Codec.Json := .array (.cons (j4) (.cons (j250) .nil))
@[expose] def j252 : Codec.Json := .array (.cons (j251) .nil)
@[expose] def j253 : Codec.Json := .array (.cons (j235) (.cons (j204) (.cons (j239) (.cons (j248) (.cons (j252) .nil)))))
@[expose] def j254 : Codec.Json := .array (.cons (j1) (.cons (j5) (.cons (j229) (.cons (j6) (.cons (j7) (.cons (j33) (.cons (j253) (.cons (j224) (.cons (j225) (.cons (.number (2)) (.cons (.number (1)) (.cons (.number (1)) .nil))))))))))))
@[expose] def j255 : Codec.Json := .array (.cons (j35) (.cons (j226) (.cons (j254) .nil)))
@[expose] def j256 : Codec.Json := .array (.cons (.number (0)) (.cons (j195) (.cons (j61) .nil)))
@[expose] def j257 : Codec.Json := .array (.cons (j256) .nil)
@[expose] def j258 : Codec.Json := .array (.cons (j257) (.cons (j195) .nil))
@[expose] def j259 : Codec.Json := .array (.cons (j258) .nil)
@[expose] def j260 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (-645)) (.cons (.number (128)) .nil)))
@[expose] def j261 : Codec.Json := .array (.cons (j260) (.cons (j4) .nil))
@[expose] def j262 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (39938399)) (.cons (.number (4194304)) .nil)))
@[expose] def j263 : Codec.Json := .array (.cons (j4) (.cons (j261) (.cons (j262) .nil)))
@[expose] def j264 : Codec.Json := .array (.cons (.number (0)) (.cons (j229) (.cons (j263) .nil)))
@[expose] def j265 : Codec.Json := .array (.cons (j256) (.cons (j264) .nil))
@[expose] def j266 : Codec.Json := .array (.cons (j265) (.cons (j229) .nil))
@[expose] def j267 : Codec.Json := .array (.cons (j266) .nil)
@[expose] def j268 : Codec.Json := .array (.cons (j60) (.cons (j259) (.cons (j267) .nil)))
@[expose] def j269 : Codec.Json := .array (.cons (j257) .nil)
@[expose] def j270 : Codec.Json := .array (.cons (j1) (.cons (j5) (.cons (j6) (.cons (j7) (.cons (j196) (.cons (.number (3)) (.cons (j21) (.cons (j255) (.cons (j268) (.cons (j269) (.cons (j75) .nil)))))))))))
@[expose] def j271 : Codec.Json := .array (.cons (j270) (.cons (j0) .nil))
@[expose] def j272 : Codec.Json := .array (.cons (j95) (.cons (j195) .nil))
@[expose] def j273 : Codec.Json := .array (.cons (.number (1)) (.cons (j195) (.cons (j61) .nil)))
@[expose] def j274 : Codec.Json := .array (.cons (j106) (.cons (j273) .nil))
@[expose] def j275 : Codec.Json := .array (.cons (j274) .nil)
@[expose] def j276 : Codec.Json := .array (.cons (j1) (.cons (j5) (.cons (j6) (.cons (j7) (.cons (j272) (.cons (.number (1)) (.cons (j115) (.cons (j116) (.cons (j117) (.cons (j275) (.cons (j75) .nil)))))))))))
@[expose] def j277 : Codec.Json := .array (.cons (j276) (.cons (j176) .nil))
@[expose] def j278 : Codec.Json := .array (.cons (j12) (.cons (j78) (.cons (j95) (.cons (j195) .nil))))
@[expose] def j279 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (1)) (.cons (.number (1)) (.cons (.number (1)) .nil))))
@[expose] def j280 : Codec.Json := .array (.cons (j279) .nil)
@[expose] def j281 : Codec.Json := .array (.cons (j180) (.cons (j280) (.cons (j14) (.cons (j14) (.cons (j74) (.cons (.number (1)) .nil))))))
@[expose] def j282 : Codec.Json := .array (.cons (.number (3)) (.cons (j195) (.cons (j61) .nil)))
@[expose] def j283 : Codec.Json := .array (.cons (j71) (.cons (j130) (.cons (j131) (.cons (j282) .nil))))
@[expose] def j284 : Codec.Json := .array (.cons (j283) .nil)
@[expose] def j285 : Codec.Json := .array (.cons (j1) (.cons (j5) (.cons (j6) (.cons (j7) (.cons (j278) (.cons (.number (1)) (.cons (j281) (.cons (j116) (.cons (j117) (.cons (j284) (.cons (j75) .nil)))))))))))
@[expose] def j286 : Codec.Json := .array (.cons (j285) (.cons (j189) .nil))
@[expose] def j287 : Codec.Json := .array (.cons (j77) (.cons (j94) (.cons (j146) (.cons (j110) (.cons (j271) (.cons (j277) (.cons (j286) .nil)))))))
@[expose] def j288 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (6)) (.cons (j287) .nil)))
@[expose] def marginGraph : Codec.Json := j288
@[expose] def j289 : Codec.Json := .array (.cons (j5) (.cons (.number (0)) (.cons (j192) .nil)))
@[expose] def j290 : Codec.Json := .array (.cons (j195) (.cons (.number (1)) (.cons (j288) .nil)))
@[expose] def j291 : Codec.Json := .array (.cons (j10) (.cons (j139) (.cons (j289) (.cons (j290) .nil))))
@[expose] def packet : Codec.Json := j291
end Hex.RCF.RealCoefficients.EnumeratedSource.Cubic

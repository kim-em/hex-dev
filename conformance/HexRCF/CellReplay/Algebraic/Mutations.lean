/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Codec.Json
public import HexRCF.CellReplay.Algebraic.MutationData0
/-! Shared constructor data from `conformance-fixtures/HexRCF/cell-algebraic-mutations.json`.
The descriptor reader checks this supplied replay independently of its producer. -/
public section

namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Mutations
open Hex.SignDet
@[expose] def j220 : Codec.Json := .array (.cons (j37) (.cons (j49) (.cons (j1) (.cons (j43) (.cons (j0) (.cons (j0) .nil))))))
@[expose] def j221 : Codec.Json := .array (.cons (j49) (.cons (j61) .nil))
@[expose] def j222 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) .nil))
@[expose] def j223 : Codec.Json := .array (.cons (j41) (.cons (j49) .nil))
@[expose] def j224 : Codec.Json := .array (.cons (j223) .nil)
@[expose] def j225 : Codec.Json := .array (.cons (j221) (.cons (j222) (.cons (j87) (.cons (j0) (.cons (j224) .nil)))))
@[expose] def j226 : Codec.Json := .array (.cons (j37) (.cons (j49) (.cons (j61) (.cons (j1) (.cons (j43) (.cons (j225) (.cons (j225) (.cons (j45) (.cons (j82) (.cons (.number (1)) (.cons (.number (0)) (.cons (.number (1)) .nil))))))))))))
@[expose] def j227 : Codec.Json := .array (.cons (j226) .nil)
@[expose] def j228 : Codec.Json := .array (.cons (j37) (.cons (j49) (.cons (j1) (.cons (j43) (.cons (j0) (.cons (.number (1)) (.cons (j12) (.cons (j227) (.cons (j194) (.cons (j9) (.cons (j30) .nil)))))))))))
@[expose] def j229 : Codec.Json := .array (.cons (j228) (.cons (j0) .nil))
@[expose] def j230 : Codec.Json := .array (.cons (j229) .nil)
@[expose] def j231 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) (.cons (j230) .nil)))
@[expose] def j232 : Codec.Json := .array (.cons (j42) (.cons (j42) (.cons (j0) .nil)))
@[expose] def j233 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (1)) (.cons (.number (0)) .nil)))
@[expose] def j234 : Codec.Json := .array (.cons (j42) .nil)
@[expose] def j235 : Codec.Json := .array (.cons (j53) (.cons (j55) (.cons (j3) (.cons (j24) (.cons (j59) (.cons (.number (2)) .nil))))))
@[expose] def j236 : Codec.Json := .array (.cons (j226) (.cons (j226) (.cons (j226) .nil)))
@[expose] def j237 : Codec.Json := .array (.cons (j2) .nil)
@[expose] def j238 : Codec.Json := .array (.cons (j237) (.cons (.number (-1)) .nil))
@[expose] def j239 : Codec.Json := .array (.cons (j238) (.cons (j41) .nil))
@[expose] def j240 : Codec.Json := .array (.cons (j130) (.cons (j38) .nil))
@[expose] def j241 : Codec.Json := .array (.cons (j240) (.cons (.number (1)) .nil))
@[expose] def j242 : Codec.Json := .array (.cons (j41) (.cons (j239) (.cons (j241) .nil)))
@[expose] def j243 : Codec.Json := .array (.cons (.number (0)) (.cons (j61) (.cons (j242) .nil)))
@[expose] def j244 : Codec.Json := .array (.cons (j243) .nil)
@[expose] def j245 : Codec.Json := .array (.cons (j244) .nil)
@[expose] def j246 : Codec.Json := .array (.cons (j37) (.cons (j49) (.cons (j1) (.cons (j43) (.cons (j234) (.cons (.number (3)) (.cons (j235) (.cons (j236) (.cons (j119) (.cons (j245) (.cons (j30) .nil)))))))))))
@[expose] def j247 : Codec.Json := .array (.cons (j246) (.cons (j0) .nil))
@[expose] def j248 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (1)) (.cons (.number (0)) .nil)))
@[expose] def j249 : Codec.Json := .array (.cons (j53) (.cons (j55) (.cons (j248) (.cons (j203) (.cons (j59) (.cons (.number (2)) .nil))))))
@[expose] def j250 : Codec.Json := .array (.cons (j50) (.cons (j10) (.cons (j87) (.cons (j0) (.cons (j0) .nil)))))
@[expose] def j251 : Codec.Json := .array (.cons (j37) (.cons (j49) (.cons (j0) (.cons (j1) (.cons (j43) (.cons (j225) (.cons (j250) (.cons (j54) (.cons (j10) (.cons (.number (0)) (.cons (.number (0)) (.cons (.number (0)) .nil))))))))))))
@[expose] def j252 : Codec.Json := .array (.cons (j226) (.cons (j251) (.cons (j251) .nil)))
@[expose] def j253 : Codec.Json := .array (.cons (.number (0)) (.cons (j0) (.cons (j87) .nil)))
@[expose] def j254 : Codec.Json := .array (.cons (j253) .nil)
@[expose] def j255 : Codec.Json := .array (.cons (j254) (.cons (j0) .nil))
@[expose] def j256 : Codec.Json := .array (.cons (j255) .nil)
@[expose] def j257 : Codec.Json := .array (.cons (j253) (.cons (j253) .nil))
@[expose] def j258 : Codec.Json := .array (.cons (j257) (.cons (j0) .nil))
@[expose] def j259 : Codec.Json := .array (.cons (j258) .nil)
@[expose] def j260 : Codec.Json := .array (.cons (j86) (.cons (j256) (.cons (j259) .nil)))
@[expose] def j261 : Codec.Json := .array (.cons (j254) .nil)
@[expose] def j262 : Codec.Json := .array (.cons (j37) (.cons (j49) (.cons (j1) (.cons (j43) (.cons (j9) (.cons (.number (3)) (.cons (j249) (.cons (j252) (.cons (j260) (.cons (j261) (.cons (j30) .nil)))))))))))
@[expose] def j263 : Codec.Json := .array (.cons (j262) (.cons (j0) .nil))
@[expose] def j264 : Codec.Json := .array (.cons (j42) (.cons (j0) .nil))
@[expose] def j265 : Codec.Json := .array (.cons (j222) .nil)
@[expose] def j266 : Codec.Json := .array (.cons (j190) (.cons (j265) (.cons (j10) (.cons (j10) (.cons (j11) (.cons (.number (1)) .nil))))))
@[expose] def j267 : Codec.Json := .array (.cons (.number (1)) (.cons (j0) (.cons (j87) .nil)))
@[expose] def j268 : Codec.Json := .array (.cons (j243) (.cons (j267) .nil))
@[expose] def j269 : Codec.Json := .array (.cons (j268) .nil)
@[expose] def j270 : Codec.Json := .array (.cons (j37) (.cons (j49) (.cons (j1) (.cons (j43) (.cons (j264) (.cons (.number (1)) (.cons (j266) (.cons (j227) (.cons (j194) (.cons (j269) (.cons (j30) .nil)))))))))))
@[expose] def j271 : Codec.Json := .array (.cons (j101) .nil)
@[expose] def j272 : Codec.Json := .array (.cons (j270) (.cons (j271) .nil))
@[expose] def j273 : Codec.Json := .array (.cons (j202) .nil)
@[expose] def j274 : Codec.Json := .array (.cons (j233) .nil)
@[expose] def j275 : Codec.Json := .array (.cons (j273) (.cons (j274) (.cons (j10) (.cons (j10) (.cons (j11) (.cons (.number (1)) .nil))))))
@[expose] def j276 : Codec.Json := .array (.cons (.number (1)) (.cons (j61) (.cons (j242) .nil)))
@[expose] def j277 : Codec.Json := .array (.cons (.number (2)) (.cons (j0) (.cons (j87) .nil)))
@[expose] def j278 : Codec.Json := .array (.cons (j243) (.cons (j276) (.cons (j277) .nil)))
@[expose] def j279 : Codec.Json := .array (.cons (j278) .nil)
@[expose] def j280 : Codec.Json := .array (.cons (j37) (.cons (j49) (.cons (j1) (.cons (j43) (.cons (j232) (.cons (.number (1)) (.cons (j275) (.cons (j227) (.cons (j194) (.cons (j279) (.cons (j30) .nil)))))))))))
@[expose] def j281 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (2)) .nil))
@[expose] def j282 : Codec.Json := .array (.cons (j281) .nil)
@[expose] def j283 : Codec.Json := .array (.cons (j280) (.cons (j282) .nil))
@[expose] def j284 : Codec.Json := .array (.cons (j247) (.cons (j263) (.cons (j272) (.cons (j283) .nil))))
@[expose] def j285 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (3)) (.cons (j284) .nil)))
@[expose] def j286 : Codec.Json := .array (.cons (.number (1)) (.cons (j220) (.cons (j232) (.cons (j233) (.cons (j285) .nil)))))
@[expose] def j287 : Codec.Json := .array (.cons (j0) (.cons (Codec.Json.Value.null) (.cons (j219) (.cons (j220) (.cons (j231) (.cons (j286) .nil))))))
@[expose] def wrongPoint : Codec.Json := j287
@[expose] def j288 : Codec.Json := .array (.cons (j238) (.cons (j219) (.cons (j219) (.cons (j220) (.cons (j231) (.cons (j286) .nil))))))
@[expose] def presentLeft : Codec.Json := j288
@[expose] def j289 : Codec.Json := .array (.cons (j238) (.cons (Codec.Json.Value.null) (.cons (Codec.Json.Value.null) (.cons (j220) (.cons (j231) (.cons (j286) .nil))))))
@[expose] def absentRight : Codec.Json := j289
@[expose] def j290 : Codec.Json := .array (.cons (j37) (.cons (j62) (.cons (j1) (.cons (j43) (.cons (j0) (.cons (j0) .nil))))))
@[expose] def j291 : Codec.Json := .array (.cons (j62) (.cons (j61) .nil))
@[expose] def j292 : Codec.Json := .array (.cons (j291) (.cons (j222) (.cons (j87) (.cons (j0) (.cons (j69) .nil)))))
@[expose] def j293 : Codec.Json := .array (.cons (j37) (.cons (j62) (.cons (j61) (.cons (j1) (.cons (j43) (.cons (j292) (.cons (j292) (.cons (j45) (.cons (j82) (.cons (.number (1)) (.cons (.number (0)) (.cons (.number (1)) .nil))))))))))))
@[expose] def j294 : Codec.Json := .array (.cons (j293) .nil)
@[expose] def j295 : Codec.Json := .array (.cons (j37) (.cons (j62) (.cons (j1) (.cons (j43) (.cons (j0) (.cons (.number (1)) (.cons (j12) (.cons (j294) (.cons (j194) (.cons (j9) (.cons (j30) .nil)))))))))))
@[expose] def j296 : Codec.Json := .array (.cons (j295) (.cons (j0) .nil))
@[expose] def j297 : Codec.Json := .array (.cons (j296) .nil)
@[expose] def j298 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) (.cons (j297) .nil)))
@[expose] def j299 : Codec.Json := .array (.cons (j238) (.cons (Codec.Json.Value.null) (.cons (j219) (.cons (j290) (.cons (j298) (.cons (j286) .nil))))))
@[expose] def otherRoot : Codec.Json := j299
@[expose] def j300 : Codec.Json := .array (.cons (j0) (.cons (.number (0)) (.cons (j0) .nil)))
@[expose] def j301 : Codec.Json := .array (.cons (j300) (.cons (j49) (.cons (j1) (.cons (j43) (.cons (j0) (.cons (j0) .nil))))))
@[expose] def j302 : Codec.Json := .array (.cons (j238) (.cons (Codec.Json.Value.null) (.cons (j219) (.cons (j301) (.cons (j231) (.cons (j286) .nil))))))
@[expose] def staleContext : Codec.Json := j302
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Mutations

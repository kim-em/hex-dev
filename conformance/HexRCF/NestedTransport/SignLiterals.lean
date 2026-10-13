/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Codec.Json
public import HexRCF.NestedTransport.SignData
/-! Shared constructor data from `conformance-fixtures/HexRCF/nested-transport-signs.json`.
The descriptor reader checks this supplied replay independently of its producer. -/
public section

namespace Hex.RCF.RealCoefficients.NestedTransportTests.SignLiterals
open Hex.SignDet
@[expose] def j265 : Codec.Json := .array (.cons (j264) (.cons (.number (1)) .nil))
@[expose] def j266 : Codec.Json := .array (.cons (j7) (.cons (j262) (.cons (j265) .nil)))
@[expose] def j267 : Codec.Json := .array (.cons (j266) .nil)
@[expose] def j268 : Codec.Json := .array (.cons (j7) (.cons (j253) .nil))
@[expose] def j269 : Codec.Json := .array (.cons (j268) .nil)
@[expose] def j270 : Codec.Json := .array (.cons (j254) (.cons (j31) (.cons (j258) (.cons (j267) (.cons (j269) .nil)))))
@[expose] def j271 : Codec.Json := .array (.cons (j52) (.cons (j55) (.cons (j249) (.cons (j56) (.cons (j57) (.cons (j77) (.cons (j270) (.cons (j38) (.cons (j39) (.cons (.number (1)) (.cons (.number (0)) (.cons (.number (1)) .nil))))))))))))
@[expose] def j272 : Codec.Json := .array (.cons (j78) (.cons (j245) (.cons (j271) .nil)))
@[expose] def j273 : Codec.Json := .array (.cons (.number (0)) (.cons (j17) (.cons (j94) .nil)))
@[expose] def j274 : Codec.Json := .array (.cons (j273) .nil)
@[expose] def j275 : Codec.Json := .array (.cons (j274) (.cons (j17) .nil))
@[expose] def j276 : Codec.Json := .array (.cons (j275) .nil)
@[expose] def j277 : Codec.Json := .array (.cons (j7) (.cons (j70) (.cons (j231) .nil)))
@[expose] def j278 : Codec.Json := .array (.cons (.number (0)) (.cons (j249) (.cons (j277) .nil)))
@[expose] def j279 : Codec.Json := .array (.cons (j273) (.cons (j278) .nil))
@[expose] def j280 : Codec.Json := .array (.cons (j279) (.cons (j249) .nil))
@[expose] def j281 : Codec.Json := .array (.cons (j280) .nil)
@[expose] def j282 : Codec.Json := .array (.cons (j93) (.cons (j276) (.cons (j281) .nil)))
@[expose] def j283 : Codec.Json := .array (.cons (j274) .nil)
@[expose] def j284 : Codec.Json := .array (.cons (j52) (.cons (j55) (.cons (j56) (.cons (j57) (.cons (j223) (.cons (.number (3)) (.cons (j109) (.cons (j272) (.cons (j282) (.cons (j283) (.cons (j45) .nil)))))))))))
@[expose] def j285 : Codec.Json := .array (.cons (j284) (.cons (j0) .nil))
@[expose] def j286 : Codec.Json := .array (.cons (j13) (.cons (j17) .nil))
@[expose] def j287 : Codec.Json := .array (.cons (j117) .nil)
@[expose] def j288 : Codec.Json := .array (.cons (j133) (.cons (j287) (.cons (j26) (.cons (j26) (.cons (j27) (.cons (.number (1)) .nil))))))
@[expose] def j289 : Codec.Json := .array (.cons (.number (1)) (.cons (j17) (.cons (j94) .nil)))
@[expose] def j290 : Codec.Json := .array (.cons (j210) (.cons (j289) .nil))
@[expose] def j291 : Codec.Json := .array (.cons (j290) .nil)
@[expose] def j292 : Codec.Json := .array (.cons (j52) (.cons (j55) (.cons (j56) (.cons (j57) (.cons (j286) (.cons (.number (1)) (.cons (j288) (.cons (j136) (.cons (j137) (.cons (j291) (.cons (j45) .nil)))))))))))
@[expose] def j293 : Codec.Json := .array (.cons (.number (4)) (.cons (.number (5)) .nil))
@[expose] def j294 : Codec.Json := .array (.cons (j293) .nil)
@[expose] def j295 : Codec.Json := .array (.cons (j292) (.cons (j294) .nil))
@[expose] def j296 : Codec.Json := .array (.cons (j9) (.cons (j13) (.cons (j17) .nil)))
@[expose] def j297 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (0)) (.cons (.number (0)) .nil)))
@[expose] def j298 : Codec.Json := .array (.cons (j297) .nil)
@[expose] def j299 : Codec.Json := .array (.cons (j38) .nil)
@[expose] def j300 : Codec.Json := .array (.cons (j298) (.cons (j299) (.cons (j26) (.cons (j26) (.cons (j27) (.cons (.number (1)) .nil))))))
@[expose] def j301 : Codec.Json := .array (.cons (.number (1)) (.cons (j13) (.cons (j94) .nil)))
@[expose] def j302 : Codec.Json := .array (.cons (.number (2)) (.cons (j17) (.cons (j94) .nil)))
@[expose] def j303 : Codec.Json := .array (.cons (j186) (.cons (j301) (.cons (j302) .nil)))
@[expose] def j304 : Codec.Json := .array (.cons (j303) .nil)
@[expose] def j305 : Codec.Json := .array (.cons (j52) (.cons (j55) (.cons (j56) (.cons (j57) (.cons (j296) (.cons (.number (1)) (.cons (j300) (.cons (j136) (.cons (j137) (.cons (j304) (.cons (j45) .nil)))))))))))
@[expose] def j306 : Codec.Json := .array (.cons (.number (3)) (.cons (.number (6)) .nil))
@[expose] def j307 : Codec.Json := .array (.cons (j306) .nil)
@[expose] def j308 : Codec.Json := .array (.cons (j305) (.cons (j307) .nil))
@[expose] def j309 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (0)) (.cons (.number (0)) (.cons (.number (0)) (.cons (.number (0)) .nil)))))
@[expose] def j310 : Codec.Json := .array (.cons (j309) .nil)
@[expose] def j311 : Codec.Json := .array (.cons (j59) .nil)
@[expose] def j312 : Codec.Json := .array (.cons (j310) (.cons (j311) (.cons (j26) (.cons (j26) (.cons (j27) (.cons (.number (1)) .nil))))))
@[expose] def j313 : Codec.Json := .array (.cons (.number (2)) (.cons (j9) (.cons (j94) .nil)))
@[expose] def j314 : Codec.Json := .array (.cons (.number (3)) (.cons (j13) (.cons (j94) .nil)))
@[expose] def j315 : Codec.Json := .array (.cons (.number (4)) (.cons (j17) (.cons (j94) .nil)))
@[expose] def j316 : Codec.Json := .array (.cons (j95) (.cons (j138) (.cons (j313) (.cons (j314) (.cons (j315) .nil)))))
@[expose] def j317 : Codec.Json := .array (.cons (j316) .nil)
@[expose] def j318 : Codec.Json := .array (.cons (j52) (.cons (j55) (.cons (j56) (.cons (j57) (.cons (j18) (.cons (.number (1)) (.cons (j312) (.cons (j136) (.cons (j137) (.cons (j317) (.cons (j45) .nil)))))))))))
@[expose] def j319 : Codec.Json := .array (.cons (.number (2)) (.cons (.number (7)) .nil))
@[expose] def j320 : Codec.Json := .array (.cons (j319) .nil)
@[expose] def j321 : Codec.Json := .array (.cons (j318) (.cons (j320) .nil))
@[expose] def j322 : Codec.Json := .array (.cons (j107) (.cons (j130) (.cons (j144) (.cons (j197) (.cons (j222) (.cons (j285) (.cons (j295) (.cons (j308) (.cons (j321) .nil)))))))))
@[expose] def j323 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (8)) (.cons (j322) .nil)))
@[expose] def j324 : Codec.Json := .array (.cons (.number (1)) (.cons (j58) (.cons (j18) (.cons (j59) (.cons (j323) .nil)))))
@[expose] def evidence : Codec.Json := j324
end Hex.RCF.RealCoefficients.NestedTransportTests.SignLiterals

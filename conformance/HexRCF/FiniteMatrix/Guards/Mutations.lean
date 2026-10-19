/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Codec.Json
public import HexRCF.FiniteMatrix.Guards.MutationData0
/-! Shared constructor data from `conformance-fixtures/HexRCF/guarded-matrix-mutations.json`.
The descriptor reader checks this supplied replay independently of its producer. -/
public section

namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Mutations
open Hex.SignDet
@[expose] def j250 : Codec.Json := .array (.cons (j249) .nil)
@[expose] def j251 : Codec.Json := .array (.cons (j58) (.cons (j245) (.cons (j250) .nil)))
@[expose] def j252 : Codec.Json := .array (.cons (j243) .nil)
@[expose] def j253 : Codec.Json := .array (.cons (.number (8)) (.cons (j8) (.cons (j9) (.cons (j13) (.cons (j192) (.cons (.number (3)) (.cons (j79) (.cons (j241) (.cons (j251) (.cons (j252) (.cons (j73) .nil)))))))))))
@[expose] def j254 : Codec.Json := .array (.cons (j253) (.cons (j4) .nil))
@[expose] def j255 : Codec.Json := .array (.cons (j21) (.cons (j25) .nil))
@[expose] def j256 : Codec.Json := .array (.cons (.number (-1)) (.cons (.number (-1)) .nil))
@[expose] def j257 : Codec.Json := .array (.cons (j256) .nil)
@[expose] def j258 : Codec.Json := .array (.cons (j103) (.cons (j257) (.cons (j30) (.cons (j30) (.cons (j72) (.cons (.number (1)) .nil))))))
@[expose] def j259 : Codec.Json := .array (.cons (.number (1)) (.cons (j25) (.cons (j59) .nil)))
@[expose] def j260 : Codec.Json := .array (.cons (j179) (.cons (j259) .nil))
@[expose] def j261 : Codec.Json := .array (.cons (j260) .nil)
@[expose] def j262 : Codec.Json := .array (.cons (.number (8)) (.cons (j8) (.cons (j9) (.cons (j13) (.cons (j255) (.cons (.number (1)) (.cons (j258) (.cons (j107) (.cons (j108) (.cons (j261) (.cons (j73) .nil)))))))))))
@[expose] def j263 : Codec.Json := .array (.cons (.number (4)) (.cons (.number (5)) .nil))
@[expose] def j264 : Codec.Json := .array (.cons (j263) .nil)
@[expose] def j265 : Codec.Json := .array (.cons (j262) (.cons (j264) .nil))
@[expose] def j266 : Codec.Json := .array (.cons (j8) (.cons (j21) (.cons (j25) .nil)))
@[expose] def j267 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (0)) (.cons (.number (0)) .nil)))
@[expose] def j268 : Codec.Json := .array (.cons (j267) .nil)
@[expose] def j269 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (-1)) (.cons (.number (-1)) .nil)))
@[expose] def j270 : Codec.Json := .array (.cons (j269) .nil)
@[expose] def j271 : Codec.Json := .array (.cons (j268) (.cons (j270) (.cons (j30) (.cons (j30) (.cons (j72) (.cons (.number (1)) .nil))))))
@[expose] def j272 : Codec.Json := .array (.cons (.number (1)) (.cons (j21) (.cons (j59) .nil)))
@[expose] def j273 : Codec.Json := .array (.cons (.number (2)) (.cons (j25) (.cons (j59) .nil)))
@[expose] def j274 : Codec.Json := .array (.cons (j130) (.cons (j272) (.cons (j273) .nil)))
@[expose] def j275 : Codec.Json := .array (.cons (j274) .nil)
@[expose] def j276 : Codec.Json := .array (.cons (.number (8)) (.cons (j8) (.cons (j9) (.cons (j13) (.cons (j266) (.cons (.number (1)) (.cons (j271) (.cons (j107) (.cons (j108) (.cons (j275) (.cons (j73) .nil)))))))))))
@[expose] def j277 : Codec.Json := .array (.cons (.number (3)) (.cons (.number (6)) .nil))
@[expose] def j278 : Codec.Json := .array (.cons (j277) .nil)
@[expose] def j279 : Codec.Json := .array (.cons (j276) (.cons (j278) .nil))
@[expose] def j280 : Codec.Json := .array (.cons (j20) (.cons (j17) (.cons (j8) (.cons (j21) (.cons (j25) .nil)))))
@[expose] def j281 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (0)) (.cons (.number (0)) (.cons (.number (0)) (.cons (.number (0)) .nil)))))
@[expose] def j282 : Codec.Json := .array (.cons (j281) .nil)
@[expose] def j283 : Codec.Json := .array (.cons (j27) .nil)
@[expose] def j284 : Codec.Json := .array (.cons (j282) (.cons (j283) (.cons (j30) (.cons (j30) (.cons (j72) (.cons (.number (1)) .nil))))))
@[expose] def j285 : Codec.Json := .array (.cons (.number (2)) (.cons (j4) (.cons (j129) .nil)))
@[expose] def j286 : Codec.Json := .array (.cons (.number (3)) (.cons (j21) (.cons (j59) .nil)))
@[expose] def j287 : Codec.Json := .array (.cons (.number (4)) (.cons (j25) (.cons (j59) .nil)))
@[expose] def j288 : Codec.Json := .array (.cons (j69) (.cons (j109) (.cons (j285) (.cons (j286) (.cons (j287) .nil)))))
@[expose] def j289 : Codec.Json := .array (.cons (j288) .nil)
@[expose] def j290 : Codec.Json := .array (.cons (.number (8)) (.cons (j8) (.cons (j9) (.cons (j13) (.cons (j280) (.cons (.number (1)) (.cons (j284) (.cons (j107) (.cons (j108) (.cons (j289) (.cons (j73) .nil)))))))))))
@[expose] def j291 : Codec.Json := .array (.cons (.number (2)) (.cons (.number (7)) .nil))
@[expose] def j292 : Codec.Json := .array (.cons (j291) .nil)
@[expose] def j293 : Codec.Json := .array (.cons (j290) (.cons (j292) .nil))
@[expose] def j294 : Codec.Json := .array (.cons (j75) (.cons (j100) (.cons (j114) (.cons (j134) (.cons (j191) (.cons (j254) (.cons (j265) (.cons (j279) (.cons (j293) .nil)))))))))
@[expose] def j295 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (8)) (.cons (j294) .nil)))
@[expose] def j296 : Codec.Json := .array (.cons (.number (1)) (.cons (j14) (.cons (j26) (.cons (j27) (.cons (j295) .nil)))))
@[expose] def order : Codec.Json := j296
@[expose] def j297 : Codec.Json := .array (.cons (.number (9)) (.cons (j8) (.cons (j9) (.cons (j13) (.cons (j4) (.cons (j4) .nil))))))
@[expose] def j298 : Codec.Json := .array (.cons (.number (1)) (.cons (j297) (.cons (j280) (.cons (j27) (.cons (j295) .nil)))))
@[expose] def context : Codec.Json := j298
@[expose] def j299 : Codec.Json := .array (.cons (j227) .nil)
@[expose] def j300 : Codec.Json := .array (.cons (j290) (.cons (j299) .nil))
@[expose] def j301 : Codec.Json := .array (.cons (j75) (.cons (j100) (.cons (j114) (.cons (j134) (.cons (j191) (.cons (j254) (.cons (j265) (.cons (j279) (.cons (j300) .nil)))))))))
@[expose] def j302 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (8)) (.cons (j301) .nil)))
@[expose] def j303 : Codec.Json := .array (.cons (.number (1)) (.cons (j14) (.cons (j280) (.cons (j27) (.cons (j302) .nil)))))
@[expose] def cycle : Codec.Json := j303
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Mutations

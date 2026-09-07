/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFq.Entry

public section

namespace Hex.GFq

/-- Instance-selected field for C(271, 1). -/
instance committedEntry_271_1 : CommittedEntry 271 1 where
  entry := Hex.Conway.supportedEntry_271_1

/-- Instance-selected field for C(271, 2). -/
instance committedEntry_271_2 : CommittedEntry 271 2 where
  entry := Hex.Conway.supportedEntry_271_2

/-- Instance-selected field for C(271, 3). -/
instance committedEntry_271_3 : CommittedEntry 271 3 where
  entry := Hex.Conway.supportedEntry_271_3

/-- Instance-selected field for C(271, 4). -/
instance committedEntry_271_4 : CommittedEntry 271 4 where
  entry := Hex.Conway.supportedEntry_271_4

/-- Instance-selected field for C(277, 1). -/
instance committedEntry_277_1 : CommittedEntry 277 1 where
  entry := Hex.Conway.supportedEntry_277_1

/-- Instance-selected field for C(277, 2). -/
instance committedEntry_277_2 : CommittedEntry 277 2 where
  entry := Hex.Conway.supportedEntry_277_2

/-- Instance-selected field for C(277, 3). -/
instance committedEntry_277_3 : CommittedEntry 277 3 where
  entry := Hex.Conway.supportedEntry_277_3

/-- Instance-selected field for C(277, 4). -/
instance committedEntry_277_4 : CommittedEntry 277 4 where
  entry := Hex.Conway.supportedEntry_277_4

/-- Instance-selected field for C(281, 1). -/
instance committedEntry_281_1 : CommittedEntry 281 1 where
  entry := Hex.Conway.supportedEntry_281_1

/-- Instance-selected field for C(281, 2). -/
instance committedEntry_281_2 : CommittedEntry 281 2 where
  entry := Hex.Conway.supportedEntry_281_2

/-- Instance-selected field for C(281, 3). -/
instance committedEntry_281_3 : CommittedEntry 281 3 where
  entry := Hex.Conway.supportedEntry_281_3

/-- Instance-selected field for C(281, 4). -/
instance committedEntry_281_4 : CommittedEntry 281 4 where
  entry := Hex.Conway.supportedEntry_281_4

/-- Instance-selected field for C(283, 1). -/
instance committedEntry_283_1 : CommittedEntry 283 1 where
  entry := Hex.Conway.supportedEntry_283_1

/-- Instance-selected field for C(283, 2). -/
instance committedEntry_283_2 : CommittedEntry 283 2 where
  entry := Hex.Conway.supportedEntry_283_2

/-- Instance-selected field for C(283, 3). -/
instance committedEntry_283_3 : CommittedEntry 283 3 where
  entry := Hex.Conway.supportedEntry_283_3

/-- Instance-selected field for C(283, 4). -/
instance committedEntry_283_4 : CommittedEntry 283 4 where
  entry := Hex.Conway.supportedEntry_283_4

/-- Instance-selected field for C(293, 1). -/
instance committedEntry_293_1 : CommittedEntry 293 1 where
  entry := Hex.Conway.supportedEntry_293_1

/-- Instance-selected field for C(293, 2). -/
instance committedEntry_293_2 : CommittedEntry 293 2 where
  entry := Hex.Conway.supportedEntry_293_2

/-- Instance-selected field for C(293, 3). -/
instance committedEntry_293_3 : CommittedEntry 293 3 where
  entry := Hex.Conway.supportedEntry_293_3

/-- Instance-selected field for C(293, 4). -/
instance committedEntry_293_4 : CommittedEntry 293 4 where
  entry := Hex.Conway.supportedEntry_293_4

/-- Instance-selected field for C(307, 1). -/
instance committedEntry_307_1 : CommittedEntry 307 1 where
  entry := Hex.Conway.supportedEntry_307_1

/-- Instance-selected field for C(307, 2). -/
instance committedEntry_307_2 : CommittedEntry 307 2 where
  entry := Hex.Conway.supportedEntry_307_2

/-- Instance-selected field for C(307, 3). -/
instance committedEntry_307_3 : CommittedEntry 307 3 where
  entry := Hex.Conway.supportedEntry_307_3

/-- Instance-selected field for C(311, 1). -/
instance committedEntry_311_1 : CommittedEntry 311 1 where
  entry := Hex.Conway.supportedEntry_311_1

/-- Instance-selected field for C(311, 2). -/
instance committedEntry_311_2 : CommittedEntry 311 2 where
  entry := Hex.Conway.supportedEntry_311_2

/-- Instance-selected field for C(311, 3). -/
instance committedEntry_311_3 : CommittedEntry 311 3 where
  entry := Hex.Conway.supportedEntry_311_3

/-- Instance-selected field for C(313, 1). -/
instance committedEntry_313_1 : CommittedEntry 313 1 where
  entry := Hex.Conway.supportedEntry_313_1

/-- Instance-selected field for C(313, 2). -/
instance committedEntry_313_2 : CommittedEntry 313 2 where
  entry := Hex.Conway.supportedEntry_313_2

/-- Instance-selected field for C(313, 3). -/
instance committedEntry_313_3 : CommittedEntry 313 3 where
  entry := Hex.Conway.supportedEntry_313_3

/-- Instance-selected field for C(317, 1). -/
instance committedEntry_317_1 : CommittedEntry 317 1 where
  entry := Hex.Conway.supportedEntry_317_1

/-- Instance-selected field for C(317, 2). -/
instance committedEntry_317_2 : CommittedEntry 317 2 where
  entry := Hex.Conway.supportedEntry_317_2

/-- Instance-selected field for C(317, 3). -/
instance committedEntry_317_3 : CommittedEntry 317 3 where
  entry := Hex.Conway.supportedEntry_317_3

/-- Instance-selected field for C(331, 1). -/
instance committedEntry_331_1 : CommittedEntry 331 1 where
  entry := Hex.Conway.supportedEntry_331_1

/-- Instance-selected field for C(331, 2). -/
instance committedEntry_331_2 : CommittedEntry 331 2 where
  entry := Hex.Conway.supportedEntry_331_2

/-- Instance-selected field for C(331, 3). -/
instance committedEntry_331_3 : CommittedEntry 331 3 where
  entry := Hex.Conway.supportedEntry_331_3

/-- Instance-selected field for C(337, 1). -/
instance committedEntry_337_1 : CommittedEntry 337 1 where
  entry := Hex.Conway.supportedEntry_337_1

/-- Instance-selected field for C(337, 2). -/
instance committedEntry_337_2 : CommittedEntry 337 2 where
  entry := Hex.Conway.supportedEntry_337_2

/-- Instance-selected field for C(337, 3). -/
instance committedEntry_337_3 : CommittedEntry 337 3 where
  entry := Hex.Conway.supportedEntry_337_3

/-- Instance-selected field for C(347, 1). -/
instance committedEntry_347_1 : CommittedEntry 347 1 where
  entry := Hex.Conway.supportedEntry_347_1

/-- Instance-selected field for C(347, 2). -/
instance committedEntry_347_2 : CommittedEntry 347 2 where
  entry := Hex.Conway.supportedEntry_347_2

/-- Instance-selected field for C(347, 3). -/
instance committedEntry_347_3 : CommittedEntry 347 3 where
  entry := Hex.Conway.supportedEntry_347_3

/-- Instance-selected field for C(349, 1). -/
instance committedEntry_349_1 : CommittedEntry 349 1 where
  entry := Hex.Conway.supportedEntry_349_1

/-- Instance-selected field for C(349, 2). -/
instance committedEntry_349_2 : CommittedEntry 349 2 where
  entry := Hex.Conway.supportedEntry_349_2

/-- Instance-selected field for C(349, 3). -/
instance committedEntry_349_3 : CommittedEntry 349 3 where
  entry := Hex.Conway.supportedEntry_349_3

/-- Instance-selected field for C(353, 1). -/
instance committedEntry_353_1 : CommittedEntry 353 1 where
  entry := Hex.Conway.supportedEntry_353_1

/-- Instance-selected field for C(353, 2). -/
instance committedEntry_353_2 : CommittedEntry 353 2 where
  entry := Hex.Conway.supportedEntry_353_2

/-- Instance-selected field for C(353, 3). -/
instance committedEntry_353_3 : CommittedEntry 353 3 where
  entry := Hex.Conway.supportedEntry_353_3

/-- Instance-selected field for C(359, 1). -/
instance committedEntry_359_1 : CommittedEntry 359 1 where
  entry := Hex.Conway.supportedEntry_359_1

/-- Instance-selected field for C(359, 2). -/
instance committedEntry_359_2 : CommittedEntry 359 2 where
  entry := Hex.Conway.supportedEntry_359_2

/-- Instance-selected field for C(359, 3). -/
instance committedEntry_359_3 : CommittedEntry 359 3 where
  entry := Hex.Conway.supportedEntry_359_3

/-- Instance-selected field for C(367, 1). -/
instance committedEntry_367_1 : CommittedEntry 367 1 where
  entry := Hex.Conway.supportedEntry_367_1

/-- Instance-selected field for C(367, 2). -/
instance committedEntry_367_2 : CommittedEntry 367 2 where
  entry := Hex.Conway.supportedEntry_367_2

/-- Instance-selected field for C(367, 3). -/
instance committedEntry_367_3 : CommittedEntry 367 3 where
  entry := Hex.Conway.supportedEntry_367_3

/-- Instance-selected field for C(373, 1). -/
instance committedEntry_373_1 : CommittedEntry 373 1 where
  entry := Hex.Conway.supportedEntry_373_1

/-- Instance-selected field for C(373, 2). -/
instance committedEntry_373_2 : CommittedEntry 373 2 where
  entry := Hex.Conway.supportedEntry_373_2

/-- Instance-selected field for C(373, 3). -/
instance committedEntry_373_3 : CommittedEntry 373 3 where
  entry := Hex.Conway.supportedEntry_373_3

/-- Instance-selected field for C(379, 1). -/
instance committedEntry_379_1 : CommittedEntry 379 1 where
  entry := Hex.Conway.supportedEntry_379_1

/-- Instance-selected field for C(379, 2). -/
instance committedEntry_379_2 : CommittedEntry 379 2 where
  entry := Hex.Conway.supportedEntry_379_2

/-- Instance-selected field for C(379, 3). -/
instance committedEntry_379_3 : CommittedEntry 379 3 where
  entry := Hex.Conway.supportedEntry_379_3

/-- Instance-selected field for C(383, 1). -/
instance committedEntry_383_1 : CommittedEntry 383 1 where
  entry := Hex.Conway.supportedEntry_383_1

/-- Instance-selected field for C(383, 2). -/
instance committedEntry_383_2 : CommittedEntry 383 2 where
  entry := Hex.Conway.supportedEntry_383_2

/-- Instance-selected field for C(383, 3). -/
instance committedEntry_383_3 : CommittedEntry 383 3 where
  entry := Hex.Conway.supportedEntry_383_3

/-- Instance-selected field for C(389, 1). -/
instance committedEntry_389_1 : CommittedEntry 389 1 where
  entry := Hex.Conway.supportedEntry_389_1

/-- Instance-selected field for C(389, 2). -/
instance committedEntry_389_2 : CommittedEntry 389 2 where
  entry := Hex.Conway.supportedEntry_389_2

/-- Instance-selected field for C(389, 3). -/
instance committedEntry_389_3 : CommittedEntry 389 3 where
  entry := Hex.Conway.supportedEntry_389_3

/-- Instance-selected field for C(397, 1). -/
instance committedEntry_397_1 : CommittedEntry 397 1 where
  entry := Hex.Conway.supportedEntry_397_1

/-- Instance-selected field for C(397, 2). -/
instance committedEntry_397_2 : CommittedEntry 397 2 where
  entry := Hex.Conway.supportedEntry_397_2

/-- Instance-selected field for C(397, 3). -/
instance committedEntry_397_3 : CommittedEntry 397 3 where
  entry := Hex.Conway.supportedEntry_397_3

/-- Instance-selected field for C(401, 1). -/
instance committedEntry_401_1 : CommittedEntry 401 1 where
  entry := Hex.Conway.supportedEntry_401_1

/-- Instance-selected field for C(401, 2). -/
instance committedEntry_401_2 : CommittedEntry 401 2 where
  entry := Hex.Conway.supportedEntry_401_2

/-- Instance-selected field for C(401, 3). -/
instance committedEntry_401_3 : CommittedEntry 401 3 where
  entry := Hex.Conway.supportedEntry_401_3

/-- Instance-selected field for C(409, 1). -/
instance committedEntry_409_1 : CommittedEntry 409 1 where
  entry := Hex.Conway.supportedEntry_409_1

/-- Instance-selected field for C(409, 2). -/
instance committedEntry_409_2 : CommittedEntry 409 2 where
  entry := Hex.Conway.supportedEntry_409_2

/-- Instance-selected field for C(409, 3). -/
instance committedEntry_409_3 : CommittedEntry 409 3 where
  entry := Hex.Conway.supportedEntry_409_3

/-- Instance-selected field for C(419, 1). -/
instance committedEntry_419_1 : CommittedEntry 419 1 where
  entry := Hex.Conway.supportedEntry_419_1

/-- Instance-selected field for C(419, 2). -/
instance committedEntry_419_2 : CommittedEntry 419 2 where
  entry := Hex.Conway.supportedEntry_419_2

/-- Instance-selected field for C(419, 3). -/
instance committedEntry_419_3 : CommittedEntry 419 3 where
  entry := Hex.Conway.supportedEntry_419_3

/-- Instance-selected field for C(421, 1). -/
instance committedEntry_421_1 : CommittedEntry 421 1 where
  entry := Hex.Conway.supportedEntry_421_1

/-- Instance-selected field for C(421, 2). -/
instance committedEntry_421_2 : CommittedEntry 421 2 where
  entry := Hex.Conway.supportedEntry_421_2

/-- Instance-selected field for C(421, 3). -/
instance committedEntry_421_3 : CommittedEntry 421 3 where
  entry := Hex.Conway.supportedEntry_421_3

/-- Instance-selected field for C(431, 1). -/
instance committedEntry_431_1 : CommittedEntry 431 1 where
  entry := Hex.Conway.supportedEntry_431_1

/-- Instance-selected field for C(431, 2). -/
instance committedEntry_431_2 : CommittedEntry 431 2 where
  entry := Hex.Conway.supportedEntry_431_2

/-- Instance-selected field for C(431, 3). -/
instance committedEntry_431_3 : CommittedEntry 431 3 where
  entry := Hex.Conway.supportedEntry_431_3

/-- Instance-selected field for C(433, 1). -/
instance committedEntry_433_1 : CommittedEntry 433 1 where
  entry := Hex.Conway.supportedEntry_433_1

/-- Instance-selected field for C(433, 2). -/
instance committedEntry_433_2 : CommittedEntry 433 2 where
  entry := Hex.Conway.supportedEntry_433_2

/-- Instance-selected field for C(433, 3). -/
instance committedEntry_433_3 : CommittedEntry 433 3 where
  entry := Hex.Conway.supportedEntry_433_3

/-- Instance-selected field for C(439, 1). -/
instance committedEntry_439_1 : CommittedEntry 439 1 where
  entry := Hex.Conway.supportedEntry_439_1

/-- Instance-selected field for C(439, 2). -/
instance committedEntry_439_2 : CommittedEntry 439 2 where
  entry := Hex.Conway.supportedEntry_439_2

/-- Instance-selected field for C(439, 3). -/
instance committedEntry_439_3 : CommittedEntry 439 3 where
  entry := Hex.Conway.supportedEntry_439_3

/-- Instance-selected field for C(443, 1). -/
instance committedEntry_443_1 : CommittedEntry 443 1 where
  entry := Hex.Conway.supportedEntry_443_1

/-- Instance-selected field for C(443, 2). -/
instance committedEntry_443_2 : CommittedEntry 443 2 where
  entry := Hex.Conway.supportedEntry_443_2

/-- Instance-selected field for C(443, 3). -/
instance committedEntry_443_3 : CommittedEntry 443 3 where
  entry := Hex.Conway.supportedEntry_443_3

/-- Instance-selected field for C(449, 1). -/
instance committedEntry_449_1 : CommittedEntry 449 1 where
  entry := Hex.Conway.supportedEntry_449_1

/-- Instance-selected field for C(449, 2). -/
instance committedEntry_449_2 : CommittedEntry 449 2 where
  entry := Hex.Conway.supportedEntry_449_2

/-- Instance-selected field for C(449, 3). -/
instance committedEntry_449_3 : CommittedEntry 449 3 where
  entry := Hex.Conway.supportedEntry_449_3

/-- Instance-selected field for C(457, 1). -/
instance committedEntry_457_1 : CommittedEntry 457 1 where
  entry := Hex.Conway.supportedEntry_457_1

/-- Instance-selected field for C(457, 2). -/
instance committedEntry_457_2 : CommittedEntry 457 2 where
  entry := Hex.Conway.supportedEntry_457_2

/-- Instance-selected field for C(457, 3). -/
instance committedEntry_457_3 : CommittedEntry 457 3 where
  entry := Hex.Conway.supportedEntry_457_3

/-- Instance-selected field for C(461, 1). -/
instance committedEntry_461_1 : CommittedEntry 461 1 where
  entry := Hex.Conway.supportedEntry_461_1

/-- Instance-selected field for C(461, 2). -/
instance committedEntry_461_2 : CommittedEntry 461 2 where
  entry := Hex.Conway.supportedEntry_461_2

/-- Instance-selected field for C(461, 3). -/
instance committedEntry_461_3 : CommittedEntry 461 3 where
  entry := Hex.Conway.supportedEntry_461_3

/-- Instance-selected field for C(463, 1). -/
instance committedEntry_463_1 : CommittedEntry 463 1 where
  entry := Hex.Conway.supportedEntry_463_1

/-- Instance-selected field for C(463, 2). -/
instance committedEntry_463_2 : CommittedEntry 463 2 where
  entry := Hex.Conway.supportedEntry_463_2

/-- Instance-selected field for C(463, 3). -/
instance committedEntry_463_3 : CommittedEntry 463 3 where
  entry := Hex.Conway.supportedEntry_463_3

/-- Instance-selected field for C(467, 1). -/
instance committedEntry_467_1 : CommittedEntry 467 1 where
  entry := Hex.Conway.supportedEntry_467_1

/-- Instance-selected field for C(467, 2). -/
instance committedEntry_467_2 : CommittedEntry 467 2 where
  entry := Hex.Conway.supportedEntry_467_2

/-- Instance-selected field for C(467, 3). -/
instance committedEntry_467_3 : CommittedEntry 467 3 where
  entry := Hex.Conway.supportedEntry_467_3

/-- Instance-selected field for C(479, 1). -/
instance committedEntry_479_1 : CommittedEntry 479 1 where
  entry := Hex.Conway.supportedEntry_479_1

/-- Instance-selected field for C(479, 2). -/
instance committedEntry_479_2 : CommittedEntry 479 2 where
  entry := Hex.Conway.supportedEntry_479_2

/-- Instance-selected field for C(479, 3). -/
instance committedEntry_479_3 : CommittedEntry 479 3 where
  entry := Hex.Conway.supportedEntry_479_3

/-- Instance-selected field for C(487, 1). -/
instance committedEntry_487_1 : CommittedEntry 487 1 where
  entry := Hex.Conway.supportedEntry_487_1

/-- Instance-selected field for C(487, 2). -/
instance committedEntry_487_2 : CommittedEntry 487 2 where
  entry := Hex.Conway.supportedEntry_487_2

/-- Instance-selected field for C(487, 3). -/
instance committedEntry_487_3 : CommittedEntry 487 3 where
  entry := Hex.Conway.supportedEntry_487_3

/-- Instance-selected field for C(491, 1). -/
instance committedEntry_491_1 : CommittedEntry 491 1 where
  entry := Hex.Conway.supportedEntry_491_1

/-- Instance-selected field for C(491, 2). -/
instance committedEntry_491_2 : CommittedEntry 491 2 where
  entry := Hex.Conway.supportedEntry_491_2

/-- Instance-selected field for C(491, 3). -/
instance committedEntry_491_3 : CommittedEntry 491 3 where
  entry := Hex.Conway.supportedEntry_491_3

/-- Instance-selected field for C(499, 1). -/
instance committedEntry_499_1 : CommittedEntry 499 1 where
  entry := Hex.Conway.supportedEntry_499_1

/-- Instance-selected field for C(499, 2). -/
instance committedEntry_499_2 : CommittedEntry 499 2 where
  entry := Hex.Conway.supportedEntry_499_2

/-- Instance-selected field for C(499, 3). -/
instance committedEntry_499_3 : CommittedEntry 499 3 where
  entry := Hex.Conway.supportedEntry_499_3

/-- Instance-selected field for C(503, 1). -/
instance committedEntry_503_1 : CommittedEntry 503 1 where
  entry := Hex.Conway.supportedEntry_503_1

/-- Instance-selected field for C(503, 2). -/
instance committedEntry_503_2 : CommittedEntry 503 2 where
  entry := Hex.Conway.supportedEntry_503_2

/-- Instance-selected field for C(503, 3). -/
instance committedEntry_503_3 : CommittedEntry 503 3 where
  entry := Hex.Conway.supportedEntry_503_3

/-- Instance-selected field for C(509, 1). -/
instance committedEntry_509_1 : CommittedEntry 509 1 where
  entry := Hex.Conway.supportedEntry_509_1

/-- Instance-selected field for C(509, 2). -/
instance committedEntry_509_2 : CommittedEntry 509 2 where
  entry := Hex.Conway.supportedEntry_509_2

/-- Instance-selected field for C(509, 3). -/
instance committedEntry_509_3 : CommittedEntry 509 3 where
  entry := Hex.Conway.supportedEntry_509_3

/-- Instance-selected field for C(521, 1). -/
instance committedEntry_521_1 : CommittedEntry 521 1 where
  entry := Hex.Conway.supportedEntry_521_1

/-- Instance-selected field for C(521, 2). -/
instance committedEntry_521_2 : CommittedEntry 521 2 where
  entry := Hex.Conway.supportedEntry_521_2

/-- Instance-selected field for C(521, 3). -/
instance committedEntry_521_3 : CommittedEntry 521 3 where
  entry := Hex.Conway.supportedEntry_521_3

end Hex.GFq

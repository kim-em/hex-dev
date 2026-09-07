/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.PrimitivityCore

public section

namespace HexGFqMathlib

/-- The Conway generator of GF(271^1) has order 270. -/
theorem orderOf_gen_271_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_271_1 Hex.FpPoly.X) = 271 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_271_1

/-- The Conway generator of GF(271^2) has order 73440. -/
theorem orderOf_gen_271_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_271_2 Hex.FpPoly.X) = 271 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_271_2

/-- The Conway generator of GF(271^3) has order 19902510. -/
theorem orderOf_gen_271_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_271_3 Hex.FpPoly.X) = 271 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_271_3

/-- The Conway generator of GF(271^4) has order 5393580480. -/
theorem orderOf_gen_271_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_271_4 Hex.FpPoly.X) = 271 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_271_4

/-- The Conway generator of GF(277^1) has order 276. -/
theorem orderOf_gen_277_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_277_1 Hex.FpPoly.X) = 277 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_277_1

/-- The Conway generator of GF(277^2) has order 76728. -/
theorem orderOf_gen_277_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_277_2 Hex.FpPoly.X) = 277 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_277_2

/-- The Conway generator of GF(277^3) has order 21253932. -/
theorem orderOf_gen_277_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_277_3 Hex.FpPoly.X) = 277 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_277_3

/-- The Conway generator of GF(277^4) has order 5887339440. -/
theorem orderOf_gen_277_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_277_4 Hex.FpPoly.X) = 277 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_277_4

/-- The Conway generator of GF(281^1) has order 280. -/
theorem orderOf_gen_281_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_281_1 Hex.FpPoly.X) = 281 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_281_1

/-- The Conway generator of GF(281^2) has order 78960. -/
theorem orderOf_gen_281_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_281_2 Hex.FpPoly.X) = 281 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_281_2

/-- The Conway generator of GF(281^3) has order 22188040. -/
theorem orderOf_gen_281_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_281_3 Hex.FpPoly.X) = 281 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_281_3

/-- The Conway generator of GF(281^4) has order 6234839520. -/
theorem orderOf_gen_281_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_281_4 Hex.FpPoly.X) = 281 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_281_4

/-- The Conway generator of GF(283^1) has order 282. -/
theorem orderOf_gen_283_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_283_1 Hex.FpPoly.X) = 283 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_283_1

/-- The Conway generator of GF(283^2) has order 80088. -/
theorem orderOf_gen_283_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_283_2 Hex.FpPoly.X) = 283 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_283_2

/-- The Conway generator of GF(283^3) has order 22665186. -/
theorem orderOf_gen_283_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_283_3 Hex.FpPoly.X) = 283 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_283_3

/-- The Conway generator of GF(283^4) has order 6414247920. -/
theorem orderOf_gen_283_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_283_4 Hex.FpPoly.X) = 283 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_283_4

/-- The Conway generator of GF(293^1) has order 292. -/
theorem orderOf_gen_293_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_293_1 Hex.FpPoly.X) = 293 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_293_1

/-- The Conway generator of GF(293^2) has order 85848. -/
theorem orderOf_gen_293_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_293_2 Hex.FpPoly.X) = 293 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_293_2

/-- The Conway generator of GF(293^3) has order 25153756. -/
theorem orderOf_gen_293_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_293_3 Hex.FpPoly.X) = 293 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_293_3

/-- The Conway generator of GF(293^4) has order 7370050800. -/
theorem orderOf_gen_293_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_293_4 Hex.FpPoly.X) = 293 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_293_4

/-- The Conway generator of GF(307^1) has order 306. -/
theorem orderOf_gen_307_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_307_1 Hex.FpPoly.X) = 307 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_307_1

/-- The Conway generator of GF(307^2) has order 94248. -/
theorem orderOf_gen_307_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_307_2 Hex.FpPoly.X) = 307 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_307_2

/-- The Conway generator of GF(307^3) has order 28934442. -/
theorem orderOf_gen_307_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_307_3 Hex.FpPoly.X) = 307 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_307_3

/-- The Conway generator of GF(311^1) has order 310. -/
theorem orderOf_gen_311_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_311_1 Hex.FpPoly.X) = 311 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_311_1

/-- The Conway generator of GF(311^2) has order 96720. -/
theorem orderOf_gen_311_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_311_2 Hex.FpPoly.X) = 311 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_311_2

/-- The Conway generator of GF(311^3) has order 30080230. -/
theorem orderOf_gen_311_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_311_3 Hex.FpPoly.X) = 311 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_311_3

/-- The Conway generator of GF(313^1) has order 312. -/
theorem orderOf_gen_313_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_313_1 Hex.FpPoly.X) = 313 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_313_1

/-- The Conway generator of GF(313^2) has order 97968. -/
theorem orderOf_gen_313_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_313_2 Hex.FpPoly.X) = 313 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_313_2

/-- The Conway generator of GF(313^3) has order 30664296. -/
theorem orderOf_gen_313_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_313_3 Hex.FpPoly.X) = 313 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_313_3

/-- The Conway generator of GF(317^1) has order 316. -/
theorem orderOf_gen_317_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_317_1 Hex.FpPoly.X) = 317 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_317_1

/-- The Conway generator of GF(317^2) has order 100488. -/
theorem orderOf_gen_317_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_317_2 Hex.FpPoly.X) = 317 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_317_2

/-- The Conway generator of GF(317^3) has order 31855012. -/
theorem orderOf_gen_317_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_317_3 Hex.FpPoly.X) = 317 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_317_3

/-- The Conway generator of GF(331^1) has order 330. -/
theorem orderOf_gen_331_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_331_1 Hex.FpPoly.X) = 331 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_331_1

/-- The Conway generator of GF(331^2) has order 109560. -/
theorem orderOf_gen_331_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_331_2 Hex.FpPoly.X) = 331 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_331_2

/-- The Conway generator of GF(331^3) has order 36264690. -/
theorem orderOf_gen_331_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_331_3 Hex.FpPoly.X) = 331 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_331_3

/-- The Conway generator of GF(337^1) has order 336. -/
theorem orderOf_gen_337_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_337_1 Hex.FpPoly.X) = 337 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_337_1

/-- The Conway generator of GF(337^2) has order 113568. -/
theorem orderOf_gen_337_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_337_2 Hex.FpPoly.X) = 337 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_337_2

/-- The Conway generator of GF(337^3) has order 38272752. -/
theorem orderOf_gen_337_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_337_3 Hex.FpPoly.X) = 337 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_337_3

/-- The Conway generator of GF(347^1) has order 346. -/
theorem orderOf_gen_347_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_347_1 Hex.FpPoly.X) = 347 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_347_1

/-- The Conway generator of GF(347^2) has order 120408. -/
theorem orderOf_gen_347_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_347_2 Hex.FpPoly.X) = 347 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_347_2

/-- The Conway generator of GF(347^3) has order 41781922. -/
theorem orderOf_gen_347_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_347_3 Hex.FpPoly.X) = 347 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_347_3

/-- The Conway generator of GF(349^1) has order 348. -/
theorem orderOf_gen_349_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_349_1 Hex.FpPoly.X) = 349 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_349_1

/-- The Conway generator of GF(349^2) has order 121800. -/
theorem orderOf_gen_349_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_349_2 Hex.FpPoly.X) = 349 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_349_2

/-- The Conway generator of GF(349^3) has order 42508548. -/
theorem orderOf_gen_349_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_349_3 Hex.FpPoly.X) = 349 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_349_3

/-- The Conway generator of GF(353^1) has order 352. -/
theorem orderOf_gen_353_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_353_1 Hex.FpPoly.X) = 353 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_353_1

/-- The Conway generator of GF(353^2) has order 124608. -/
theorem orderOf_gen_353_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_353_2 Hex.FpPoly.X) = 353 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_353_2

/-- The Conway generator of GF(353^3) has order 43986976. -/
theorem orderOf_gen_353_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_353_3 Hex.FpPoly.X) = 353 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_353_3

/-- The Conway generator of GF(359^1) has order 358. -/
theorem orderOf_gen_359_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_359_1 Hex.FpPoly.X) = 359 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_359_1

/-- The Conway generator of GF(359^2) has order 128880. -/
theorem orderOf_gen_359_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_359_2 Hex.FpPoly.X) = 359 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_359_2

/-- The Conway generator of GF(359^3) has order 46268278. -/
theorem orderOf_gen_359_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_359_3 Hex.FpPoly.X) = 359 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_359_3

/-- The Conway generator of GF(367^1) has order 366. -/
theorem orderOf_gen_367_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_367_1 Hex.FpPoly.X) = 367 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_367_1

/-- The Conway generator of GF(367^2) has order 134688. -/
theorem orderOf_gen_367_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_367_2 Hex.FpPoly.X) = 367 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_367_2

/-- The Conway generator of GF(367^3) has order 49430862. -/
theorem orderOf_gen_367_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_367_3 Hex.FpPoly.X) = 367 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_367_3

/-- The Conway generator of GF(373^1) has order 372. -/
theorem orderOf_gen_373_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_373_1 Hex.FpPoly.X) = 373 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_373_1

/-- The Conway generator of GF(373^2) has order 139128. -/
theorem orderOf_gen_373_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_373_2 Hex.FpPoly.X) = 373 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_373_2

/-- The Conway generator of GF(373^3) has order 51895116. -/
theorem orderOf_gen_373_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_373_3 Hex.FpPoly.X) = 373 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_373_3

/-- The Conway generator of GF(379^1) has order 378. -/
theorem orderOf_gen_379_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_379_1 Hex.FpPoly.X) = 379 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_379_1

/-- The Conway generator of GF(379^2) has order 143640. -/
theorem orderOf_gen_379_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_379_2 Hex.FpPoly.X) = 379 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_379_2

/-- The Conway generator of GF(379^3) has order 54439938. -/
theorem orderOf_gen_379_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_379_3 Hex.FpPoly.X) = 379 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_379_3

/-- The Conway generator of GF(383^1) has order 382. -/
theorem orderOf_gen_383_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_383_1 Hex.FpPoly.X) = 383 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_383_1

/-- The Conway generator of GF(383^2) has order 146688. -/
theorem orderOf_gen_383_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_383_2 Hex.FpPoly.X) = 383 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_383_2

/-- The Conway generator of GF(383^3) has order 56181886. -/
theorem orderOf_gen_383_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_383_3 Hex.FpPoly.X) = 383 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_383_3

/-- The Conway generator of GF(389^1) has order 388. -/
theorem orderOf_gen_389_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_389_1 Hex.FpPoly.X) = 389 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_389_1

/-- The Conway generator of GF(389^2) has order 151320. -/
theorem orderOf_gen_389_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_389_2 Hex.FpPoly.X) = 389 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_389_2

/-- The Conway generator of GF(389^3) has order 58863868. -/
theorem orderOf_gen_389_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_389_3 Hex.FpPoly.X) = 389 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_389_3

/-- The Conway generator of GF(397^1) has order 396. -/
theorem orderOf_gen_397_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_397_1 Hex.FpPoly.X) = 397 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_397_1

/-- The Conway generator of GF(397^2) has order 157608. -/
theorem orderOf_gen_397_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_397_2 Hex.FpPoly.X) = 397 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_397_2

/-- The Conway generator of GF(397^3) has order 62570772. -/
theorem orderOf_gen_397_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_397_3 Hex.FpPoly.X) = 397 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_397_3

/-- The Conway generator of GF(401^1) has order 400. -/
theorem orderOf_gen_401_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_401_1 Hex.FpPoly.X) = 401 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_401_1

/-- The Conway generator of GF(401^2) has order 160800. -/
theorem orderOf_gen_401_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_401_2 Hex.FpPoly.X) = 401 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_401_2

/-- The Conway generator of GF(401^3) has order 64481200. -/
theorem orderOf_gen_401_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_401_3 Hex.FpPoly.X) = 401 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_401_3

/-- The Conway generator of GF(409^1) has order 408. -/
theorem orderOf_gen_409_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_409_1 Hex.FpPoly.X) = 409 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_409_1

/-- The Conway generator of GF(409^2) has order 167280. -/
theorem orderOf_gen_409_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_409_2 Hex.FpPoly.X) = 409 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_409_2

/-- The Conway generator of GF(409^3) has order 68417928. -/
theorem orderOf_gen_409_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_409_3 Hex.FpPoly.X) = 409 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_409_3

/-- The Conway generator of GF(419^1) has order 418. -/
theorem orderOf_gen_419_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_419_1 Hex.FpPoly.X) = 419 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_419_1

/-- The Conway generator of GF(419^2) has order 175560. -/
theorem orderOf_gen_419_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_419_2 Hex.FpPoly.X) = 419 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_419_2

/-- The Conway generator of GF(419^3) has order 73560058. -/
theorem orderOf_gen_419_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_419_3 Hex.FpPoly.X) = 419 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_419_3

/-- The Conway generator of GF(421^1) has order 420. -/
theorem orderOf_gen_421_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_421_1 Hex.FpPoly.X) = 421 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_421_1

/-- The Conway generator of GF(421^2) has order 177240. -/
theorem orderOf_gen_421_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_421_2 Hex.FpPoly.X) = 421 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_421_2

/-- The Conway generator of GF(421^3) has order 74618460. -/
theorem orderOf_gen_421_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_421_3 Hex.FpPoly.X) = 421 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_421_3

/-- The Conway generator of GF(431^1) has order 430. -/
theorem orderOf_gen_431_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_431_1 Hex.FpPoly.X) = 431 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_431_1

/-- The Conway generator of GF(431^2) has order 185760. -/
theorem orderOf_gen_431_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_431_2 Hex.FpPoly.X) = 431 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_431_2

/-- The Conway generator of GF(431^3) has order 80062990. -/
theorem orderOf_gen_431_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_431_3 Hex.FpPoly.X) = 431 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_431_3

/-- The Conway generator of GF(433^1) has order 432. -/
theorem orderOf_gen_433_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_433_1 Hex.FpPoly.X) = 433 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_433_1

/-- The Conway generator of GF(433^2) has order 187488. -/
theorem orderOf_gen_433_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_433_2 Hex.FpPoly.X) = 433 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_433_2

/-- The Conway generator of GF(433^3) has order 81182736. -/
theorem orderOf_gen_433_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_433_3 Hex.FpPoly.X) = 433 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_433_3

/-- The Conway generator of GF(439^1) has order 438. -/
theorem orderOf_gen_439_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_439_1 Hex.FpPoly.X) = 439 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_439_1

/-- The Conway generator of GF(439^2) has order 192720. -/
theorem orderOf_gen_439_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_439_2 Hex.FpPoly.X) = 439 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_439_2

/-- The Conway generator of GF(439^3) has order 84604518. -/
theorem orderOf_gen_439_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_439_3 Hex.FpPoly.X) = 439 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_439_3

/-- The Conway generator of GF(443^1) has order 442. -/
theorem orderOf_gen_443_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_443_1 Hex.FpPoly.X) = 443 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_443_1

/-- The Conway generator of GF(443^2) has order 196248. -/
theorem orderOf_gen_443_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_443_2 Hex.FpPoly.X) = 443 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_443_2

/-- The Conway generator of GF(443^3) has order 86938306. -/
theorem orderOf_gen_443_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_443_3 Hex.FpPoly.X) = 443 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_443_3

/-- The Conway generator of GF(449^1) has order 448. -/
theorem orderOf_gen_449_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_449_1 Hex.FpPoly.X) = 449 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_449_1

/-- The Conway generator of GF(449^2) has order 201600. -/
theorem orderOf_gen_449_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_449_2 Hex.FpPoly.X) = 449 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_449_2

/-- The Conway generator of GF(449^3) has order 90518848. -/
theorem orderOf_gen_449_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_449_3 Hex.FpPoly.X) = 449 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_449_3

/-- The Conway generator of GF(457^1) has order 456. -/
theorem orderOf_gen_457_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_457_1 Hex.FpPoly.X) = 457 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_457_1

/-- The Conway generator of GF(457^2) has order 208848. -/
theorem orderOf_gen_457_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_457_2 Hex.FpPoly.X) = 457 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_457_2

/-- The Conway generator of GF(457^3) has order 95443992. -/
theorem orderOf_gen_457_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_457_3 Hex.FpPoly.X) = 457 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_457_3

/-- The Conway generator of GF(461^1) has order 460. -/
theorem orderOf_gen_461_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_461_1 Hex.FpPoly.X) = 461 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_461_1

/-- The Conway generator of GF(461^2) has order 212520. -/
theorem orderOf_gen_461_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_461_2 Hex.FpPoly.X) = 461 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_461_2

/-- The Conway generator of GF(461^3) has order 97972180. -/
theorem orderOf_gen_461_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_461_3 Hex.FpPoly.X) = 461 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_461_3

/-- The Conway generator of GF(463^1) has order 462. -/
theorem orderOf_gen_463_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_463_1 Hex.FpPoly.X) = 463 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_463_1

/-- The Conway generator of GF(463^2) has order 214368. -/
theorem orderOf_gen_463_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_463_2 Hex.FpPoly.X) = 463 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_463_2

/-- The Conway generator of GF(463^3) has order 99252846. -/
theorem orderOf_gen_463_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_463_3 Hex.FpPoly.X) = 463 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_463_3

/-- The Conway generator of GF(467^1) has order 466. -/
theorem orderOf_gen_467_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_467_1 Hex.FpPoly.X) = 467 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_467_1

/-- The Conway generator of GF(467^2) has order 218088. -/
theorem orderOf_gen_467_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_467_2 Hex.FpPoly.X) = 467 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_467_2

/-- The Conway generator of GF(467^3) has order 101847562. -/
theorem orderOf_gen_467_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_467_3 Hex.FpPoly.X) = 467 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_467_3

/-- The Conway generator of GF(479^1) has order 478. -/
theorem orderOf_gen_479_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_479_1 Hex.FpPoly.X) = 479 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_479_1

/-- The Conway generator of GF(479^2) has order 229440. -/
theorem orderOf_gen_479_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_479_2 Hex.FpPoly.X) = 479 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_479_2

/-- The Conway generator of GF(479^3) has order 109902238. -/
theorem orderOf_gen_479_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_479_3 Hex.FpPoly.X) = 479 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_479_3

/-- The Conway generator of GF(487^1) has order 486. -/
theorem orderOf_gen_487_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_487_1 Hex.FpPoly.X) = 487 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_487_1

/-- The Conway generator of GF(487^2) has order 237168. -/
theorem orderOf_gen_487_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_487_2 Hex.FpPoly.X) = 487 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_487_2

/-- The Conway generator of GF(487^3) has order 115501302. -/
theorem orderOf_gen_487_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_487_3 Hex.FpPoly.X) = 487 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_487_3

/-- The Conway generator of GF(491^1) has order 490. -/
theorem orderOf_gen_491_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_491_1 Hex.FpPoly.X) = 491 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_491_1

/-- The Conway generator of GF(491^2) has order 241080. -/
theorem orderOf_gen_491_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_491_2 Hex.FpPoly.X) = 491 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_491_2

/-- The Conway generator of GF(491^3) has order 118370770. -/
theorem orderOf_gen_491_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_491_3 Hex.FpPoly.X) = 491 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_491_3

/-- The Conway generator of GF(499^1) has order 498. -/
theorem orderOf_gen_499_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_499_1 Hex.FpPoly.X) = 499 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_499_1

/-- The Conway generator of GF(499^2) has order 249000. -/
theorem orderOf_gen_499_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_499_2 Hex.FpPoly.X) = 499 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_499_2

/-- The Conway generator of GF(499^3) has order 124251498. -/
theorem orderOf_gen_499_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_499_3 Hex.FpPoly.X) = 499 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_499_3

/-- The Conway generator of GF(503^1) has order 502. -/
theorem orderOf_gen_503_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_503_1 Hex.FpPoly.X) = 503 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_503_1

/-- The Conway generator of GF(503^2) has order 253008. -/
theorem orderOf_gen_503_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_503_2 Hex.FpPoly.X) = 503 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_503_2

/-- The Conway generator of GF(503^3) has order 127263526. -/
theorem orderOf_gen_503_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_503_3 Hex.FpPoly.X) = 503 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_503_3

/-- The Conway generator of GF(509^1) has order 508. -/
theorem orderOf_gen_509_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_509_1 Hex.FpPoly.X) = 509 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_509_1

/-- The Conway generator of GF(509^2) has order 259080. -/
theorem orderOf_gen_509_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_509_2 Hex.FpPoly.X) = 509 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_509_2

/-- The Conway generator of GF(509^3) has order 131872228. -/
theorem orderOf_gen_509_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_509_3 Hex.FpPoly.X) = 509 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_509_3

/-- The Conway generator of GF(521^1) has order 520. -/
theorem orderOf_gen_521_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_521_1 Hex.FpPoly.X) = 521 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_521_1

/-- The Conway generator of GF(521^2) has order 271440. -/
theorem orderOf_gen_521_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_521_2 Hex.FpPoly.X) = 521 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_521_2

/-- The Conway generator of GF(521^3) has order 141420760. -/
theorem orderOf_gen_521_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_521_3 Hex.FpPoly.X) = 521 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_521_3

end HexGFqMathlib

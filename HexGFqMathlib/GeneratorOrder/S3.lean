/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.PrimitivityCore

public section

namespace HexGFqMathlib

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

/-- The Conway generator of GF(463^4) has order 45954068160. -/
theorem orderOf_gen_463_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_463_4 Hex.FpPoly.X) = 463 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_463_4

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

/-- The Conway generator of GF(467^4) has order 47562811920. -/
theorem orderOf_gen_467_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_467_4 Hex.FpPoly.X) = 467 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_467_4

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

/-- The Conway generator of GF(479^4) has order 52643172480. -/
theorem orderOf_gen_479_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_479_4 Hex.FpPoly.X) = 479 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_479_4

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

/-- The Conway generator of GF(487^4) has order 56249134560. -/
theorem orderOf_gen_487_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_487_4 Hex.FpPoly.X) = 487 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_487_4

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

/-- The Conway generator of GF(491^4) has order 58120048560. -/
theorem orderOf_gen_491_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_491_4 Hex.FpPoly.X) = 491 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_491_4

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

/-- The Conway generator of GF(499^4) has order 62001498000. -/
theorem orderOf_gen_499_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_499_4 Hex.FpPoly.X) = 499 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_499_4

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

/-- The Conway generator of GF(503^4) has order 64013554080. -/
theorem orderOf_gen_503_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_503_4 Hex.FpPoly.X) = 503 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_503_4

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

/-- The Conway generator of GF(509^4) has order 67122964560. -/
theorem orderOf_gen_509_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_509_4 Hex.FpPoly.X) = 509 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_509_4

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

/-- The Conway generator of GF(521^4) has order 73680216480. -/
theorem orderOf_gen_521_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_521_4 Hex.FpPoly.X) = 521 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_521_4

/-- The Conway generator of GF(523^1) has order 522. -/
theorem orderOf_gen_523_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_523_1 Hex.FpPoly.X) = 523 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_523_1

/-- The Conway generator of GF(523^2) has order 273528. -/
theorem orderOf_gen_523_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_523_2 Hex.FpPoly.X) = 523 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_523_2

/-- The Conway generator of GF(523^3) has order 143055666. -/
theorem orderOf_gen_523_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_523_3 Hex.FpPoly.X) = 523 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_523_3

/-- The Conway generator of GF(523^4) has order 74818113840. -/
theorem orderOf_gen_523_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_523_4 Hex.FpPoly.X) = 523 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_523_4

/-- The Conway generator of GF(541^1) has order 540. -/
theorem orderOf_gen_541_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_541_1 Hex.FpPoly.X) = 541 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_541_1

/-- The Conway generator of GF(541^2) has order 292680. -/
theorem orderOf_gen_541_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_541_2 Hex.FpPoly.X) = 541 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_541_2

/-- The Conway generator of GF(541^3) has order 158340420. -/
theorem orderOf_gen_541_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_541_3 Hex.FpPoly.X) = 541 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_541_3

/-- The Conway generator of GF(541^4) has order 85662167760. -/
theorem orderOf_gen_541_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_541_4 Hex.FpPoly.X) = 541 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_541_4

/-- The Conway generator of GF(547^1) has order 546. -/
theorem orderOf_gen_547_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_547_1 Hex.FpPoly.X) = 547 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_547_1

/-- The Conway generator of GF(547^2) has order 299208. -/
theorem orderOf_gen_547_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_547_2 Hex.FpPoly.X) = 547 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_547_2

/-- The Conway generator of GF(547^3) has order 163667322. -/
theorem orderOf_gen_547_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_547_3 Hex.FpPoly.X) = 547 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_547_3

/-- The Conway generator of GF(547^4) has order 89526025680. -/
theorem orderOf_gen_547_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_547_4 Hex.FpPoly.X) = 547 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_547_4

/-- The Conway generator of GF(557^1) has order 556. -/
theorem orderOf_gen_557_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_557_1 Hex.FpPoly.X) = 557 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_557_1

/-- The Conway generator of GF(557^2) has order 310248. -/
theorem orderOf_gen_557_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_557_2 Hex.FpPoly.X) = 557 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_557_2

/-- The Conway generator of GF(557^3) has order 172808692. -/
theorem orderOf_gen_557_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_557_3 Hex.FpPoly.X) = 557 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_557_3

/-- The Conway generator of GF(557^4) has order 96254442000. -/
theorem orderOf_gen_557_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_557_4 Hex.FpPoly.X) = 557 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_557_4

/-- The Conway generator of GF(563^1) has order 562. -/
theorem orderOf_gen_563_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_563_1 Hex.FpPoly.X) = 563 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_563_1

/-- The Conway generator of GF(563^2) has order 316968. -/
theorem orderOf_gen_563_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_563_2 Hex.FpPoly.X) = 563 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_563_2

/-- The Conway generator of GF(563^3) has order 178453546. -/
theorem orderOf_gen_563_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_563_3 Hex.FpPoly.X) = 563 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_563_3

/-- The Conway generator of GF(563^4) has order 100469346960. -/
theorem orderOf_gen_563_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_563_4 Hex.FpPoly.X) = 563 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_563_4

/-- The Conway generator of GF(569^1) has order 568. -/
theorem orderOf_gen_569_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_569_1 Hex.FpPoly.X) = 569 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_569_1

/-- The Conway generator of GF(569^2) has order 323760. -/
theorem orderOf_gen_569_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_569_2 Hex.FpPoly.X) = 569 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_569_2

/-- The Conway generator of GF(569^3) has order 184220008. -/
theorem orderOf_gen_569_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_569_3 Hex.FpPoly.X) = 569 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_569_3

/-- The Conway generator of GF(569^4) has order 104821185120. -/
theorem orderOf_gen_569_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_569_4 Hex.FpPoly.X) = 569 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_569_4

/-- The Conway generator of GF(571^1) has order 570. -/
theorem orderOf_gen_571_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_571_1 Hex.FpPoly.X) = 571 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_571_1

/-- The Conway generator of GF(571^2) has order 326040. -/
theorem orderOf_gen_571_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_571_2 Hex.FpPoly.X) = 571 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_571_2

/-- The Conway generator of GF(571^3) has order 186169410. -/
theorem orderOf_gen_571_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_571_3 Hex.FpPoly.X) = 571 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_571_3

/-- The Conway generator of GF(571^4) has order 106302733680. -/
theorem orderOf_gen_571_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_571_4 Hex.FpPoly.X) = 571 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_571_4

/-- The Conway generator of GF(577^1) has order 576. -/
theorem orderOf_gen_577_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_577_1 Hex.FpPoly.X) = 577 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_577_1

/-- The Conway generator of GF(577^2) has order 332928. -/
theorem orderOf_gen_577_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_577_2 Hex.FpPoly.X) = 577 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_577_2

/-- The Conway generator of GF(577^3) has order 192100032. -/
theorem orderOf_gen_577_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_577_3 Hex.FpPoly.X) = 577 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_577_3

/-- The Conway generator of GF(577^4) has order 110841719040. -/
theorem orderOf_gen_577_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_577_4 Hex.FpPoly.X) = 577 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_577_4

/-- The Conway generator of GF(587^1) has order 586. -/
theorem orderOf_gen_587_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_587_1 Hex.FpPoly.X) = 587 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_587_1

/-- The Conway generator of GF(587^2) has order 344568. -/
theorem orderOf_gen_587_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_587_2 Hex.FpPoly.X) = 587 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_587_2

/-- The Conway generator of GF(587^3) has order 202262002. -/
theorem orderOf_gen_587_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_587_3 Hex.FpPoly.X) = 587 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_587_3

/-- The Conway generator of GF(587^4) has order 118727795760. -/
theorem orderOf_gen_587_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_587_4 Hex.FpPoly.X) = 587 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_587_4

/-- The Conway generator of GF(593^1) has order 592. -/
theorem orderOf_gen_593_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_593_1 Hex.FpPoly.X) = 593 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_593_1

/-- The Conway generator of GF(593^2) has order 351648. -/
theorem orderOf_gen_593_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_593_2 Hex.FpPoly.X) = 593 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_593_2

/-- The Conway generator of GF(593^3) has order 208527856. -/
theorem orderOf_gen_593_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_593_3 Hex.FpPoly.X) = 593 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_593_3

/-- The Conway generator of GF(593^4) has order 123657019200. -/
theorem orderOf_gen_593_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_593_4 Hex.FpPoly.X) = 593 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_593_4

/-- The Conway generator of GF(599^1) has order 598. -/
theorem orderOf_gen_599_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_599_1 Hex.FpPoly.X) = 599 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_599_1

/-- The Conway generator of GF(599^2) has order 358800. -/
theorem orderOf_gen_599_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_599_2 Hex.FpPoly.X) = 599 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_599_2

/-- The Conway generator of GF(599^3) has order 214921798. -/
theorem orderOf_gen_599_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_599_3 Hex.FpPoly.X) = 599 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_599_3

/-- The Conway generator of GF(599^4) has order 128738157600. -/
theorem orderOf_gen_599_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_599_4 Hex.FpPoly.X) = 599 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_599_4

/-- The Conway generator of GF(601^1) has order 600. -/
theorem orderOf_gen_601_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_601_1 Hex.FpPoly.X) = 601 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_601_1

/-- The Conway generator of GF(601^2) has order 361200. -/
theorem orderOf_gen_601_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_601_2 Hex.FpPoly.X) = 601 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_601_2

/-- The Conway generator of GF(601^3) has order 217081800. -/
theorem orderOf_gen_601_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_601_3 Hex.FpPoly.X) = 601 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_601_3

/-- The Conway generator of GF(601^4) has order 130466162400. -/
theorem orderOf_gen_601_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_601_4 Hex.FpPoly.X) = 601 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_601_4

/-- The Conway generator of GF(607^1) has order 606. -/
theorem orderOf_gen_607_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_607_1 Hex.FpPoly.X) = 607 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_607_1

/-- The Conway generator of GF(607^2) has order 368448. -/
theorem orderOf_gen_607_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_607_2 Hex.FpPoly.X) = 607 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_607_2

/-- The Conway generator of GF(607^3) has order 223648542. -/
theorem orderOf_gen_607_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_607_3 Hex.FpPoly.X) = 607 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_607_3

/-- The Conway generator of GF(607^4) has order 135754665600. -/
theorem orderOf_gen_607_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_607_4 Hex.FpPoly.X) = 607 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_607_4

/-- The Conway generator of GF(613^1) has order 612. -/
theorem orderOf_gen_613_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_613_1 Hex.FpPoly.X) = 613 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_613_1

/-- The Conway generator of GF(613^2) has order 375768. -/
theorem orderOf_gen_613_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_613_2 Hex.FpPoly.X) = 613 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_613_2

/-- The Conway generator of GF(613^3) has order 230346396. -/
theorem orderOf_gen_613_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_613_3 Hex.FpPoly.X) = 613 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_613_3

/-- The Conway generator of GF(613^4) has order 141202341360. -/
theorem orderOf_gen_613_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_613_4 Hex.FpPoly.X) = 613 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_613_4

/-- The Conway generator of GF(617^1) has order 616. -/
theorem orderOf_gen_617_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_617_1 Hex.FpPoly.X) = 617 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_617_1

/-- The Conway generator of GF(617^2) has order 380688. -/
theorem orderOf_gen_617_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_617_2 Hex.FpPoly.X) = 617 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_617_2

/-- The Conway generator of GF(617^3) has order 234885112. -/
theorem orderOf_gen_617_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_617_3 Hex.FpPoly.X) = 617 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_617_3

/-- The Conway generator of GF(617^4) has order 144924114720. -/
theorem orderOf_gen_617_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_617_4 Hex.FpPoly.X) = 617 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_617_4

/-- The Conway generator of GF(619^1) has order 618. -/
theorem orderOf_gen_619_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_619_1 Hex.FpPoly.X) = 619 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_619_1

/-- The Conway generator of GF(619^2) has order 383160. -/
theorem orderOf_gen_619_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_619_2 Hex.FpPoly.X) = 619 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_619_2

/-- The Conway generator of GF(619^3) has order 237176658. -/
theorem orderOf_gen_619_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_619_3 Hex.FpPoly.X) = 619 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_619_3

/-- The Conway generator of GF(619^4) has order 146812351920. -/
theorem orderOf_gen_619_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_619_4 Hex.FpPoly.X) = 619 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_619_4

/-- The Conway generator of GF(631^1) has order 630. -/
theorem orderOf_gen_631_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_631_1 Hex.FpPoly.X) = 631 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_631_1

/-- The Conway generator of GF(631^2) has order 398160. -/
theorem orderOf_gen_631_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_631_2 Hex.FpPoly.X) = 631 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_631_2

/-- The Conway generator of GF(631^3) has order 251239590. -/
theorem orderOf_gen_631_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_631_3 Hex.FpPoly.X) = 631 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_631_3

/-- The Conway generator of GF(631^4) has order 158532181920. -/
theorem orderOf_gen_631_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_631_4 Hex.FpPoly.X) = 631 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_631_4

/-- The Conway generator of GF(641^1) has order 640. -/
theorem orderOf_gen_641_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_641_1 Hex.FpPoly.X) = 641 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_641_1

/-- The Conway generator of GF(641^2) has order 410880. -/
theorem orderOf_gen_641_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_641_2 Hex.FpPoly.X) = 641 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_641_2

/-- The Conway generator of GF(641^3) has order 263374720. -/
theorem orderOf_gen_641_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_641_3 Hex.FpPoly.X) = 641 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_641_3

/-- The Conway generator of GF(641^4) has order 168823196160. -/
theorem orderOf_gen_641_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_641_4 Hex.FpPoly.X) = 641 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_641_4

/-- The Conway generator of GF(643^1) has order 642. -/
theorem orderOf_gen_643_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_643_1 Hex.FpPoly.X) = 643 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_643_1

/-- The Conway generator of GF(643^2) has order 413448. -/
theorem orderOf_gen_643_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_643_2 Hex.FpPoly.X) = 643 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_643_2

/-- The Conway generator of GF(643^3) has order 265847706. -/
theorem orderOf_gen_643_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_643_3 Hex.FpPoly.X) = 643 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_643_3

/-- The Conway generator of GF(643^4) has order 170940075600. -/
theorem orderOf_gen_643_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_643_4 Hex.FpPoly.X) = 643 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_643_4

/-- The Conway generator of GF(647^1) has order 646. -/
theorem orderOf_gen_647_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_647_1 Hex.FpPoly.X) = 647 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_647_1

/-- The Conway generator of GF(647^2) has order 418608. -/
theorem orderOf_gen_647_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_647_2 Hex.FpPoly.X) = 647 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_647_2

/-- The Conway generator of GF(647^3) has order 270840022. -/
theorem orderOf_gen_647_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_647_3 Hex.FpPoly.X) = 647 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_647_3

/-- The Conway generator of GF(647^4) has order 175233494880. -/
theorem orderOf_gen_647_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_647_4 Hex.FpPoly.X) = 647 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_647_4

/-- The Conway generator of GF(653^1) has order 652. -/
theorem orderOf_gen_653_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_653_1 Hex.FpPoly.X) = 653 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_653_1

/-- The Conway generator of GF(653^2) has order 426408. -/
theorem orderOf_gen_653_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_653_2 Hex.FpPoly.X) = 653 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_653_2

/-- The Conway generator of GF(653^3) has order 278445076. -/
theorem orderOf_gen_653_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_653_3 Hex.FpPoly.X) = 653 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_653_3

/-- The Conway generator of GF(653^4) has order 181824635280. -/
theorem orderOf_gen_653_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_653_4 Hex.FpPoly.X) = 653 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_653_4

/-- The Conway generator of GF(659^1) has order 658. -/
theorem orderOf_gen_659_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_659_1 Hex.FpPoly.X) = 659 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_659_1

/-- The Conway generator of GF(659^2) has order 434280. -/
theorem orderOf_gen_659_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_659_2 Hex.FpPoly.X) = 659 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_659_2

/-- The Conway generator of GF(659^3) has order 286191178. -/
theorem orderOf_gen_659_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_659_3 Hex.FpPoly.X) = 659 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_659_3

/-- The Conway generator of GF(659^4) has order 188599986960. -/
theorem orderOf_gen_659_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_659_4 Hex.FpPoly.X) = 659 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_659_4

/-- The Conway generator of GF(661^1) has order 660. -/
theorem orderOf_gen_661_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_661_1 Hex.FpPoly.X) = 661 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_661_1

/-- The Conway generator of GF(661^2) has order 436920. -/
theorem orderOf_gen_661_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_661_2 Hex.FpPoly.X) = 661 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_661_2

/-- The Conway generator of GF(661^3) has order 288804780. -/
theorem orderOf_gen_661_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_661_3 Hex.FpPoly.X) = 661 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_661_3

/-- The Conway generator of GF(661^4) has order 190899960240. -/
theorem orderOf_gen_661_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_661_4 Hex.FpPoly.X) = 661 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_661_4

end HexGFqMathlib

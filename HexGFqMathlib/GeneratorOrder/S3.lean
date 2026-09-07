/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.PrimitivityCore

public section

namespace HexGFqMathlib

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

/-- The Conway generator of GF(673^1) has order 672. -/
theorem orderOf_gen_673_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_673_1 Hex.FpPoly.X) = 673 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_673_1

/-- The Conway generator of GF(673^2) has order 452928. -/
theorem orderOf_gen_673_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_673_2 Hex.FpPoly.X) = 673 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_673_2

/-- The Conway generator of GF(673^3) has order 304821216. -/
theorem orderOf_gen_673_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_673_3 Hex.FpPoly.X) = 673 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_673_3

/-- The Conway generator of GF(677^1) has order 676. -/
theorem orderOf_gen_677_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_677_1 Hex.FpPoly.X) = 677 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_677_1

/-- The Conway generator of GF(677^2) has order 458328. -/
theorem orderOf_gen_677_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_677_2 Hex.FpPoly.X) = 677 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_677_2

/-- The Conway generator of GF(677^3) has order 310288732. -/
theorem orderOf_gen_677_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_677_3 Hex.FpPoly.X) = 677 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_677_3

/-- The Conway generator of GF(683^1) has order 682. -/
theorem orderOf_gen_683_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_683_1 Hex.FpPoly.X) = 683 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_683_1

/-- The Conway generator of GF(683^2) has order 466488. -/
theorem orderOf_gen_683_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_683_2 Hex.FpPoly.X) = 683 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_683_2

/-- The Conway generator of GF(683^3) has order 318611986. -/
theorem orderOf_gen_683_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_683_3 Hex.FpPoly.X) = 683 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_683_3

/-- The Conway generator of GF(691^1) has order 690. -/
theorem orderOf_gen_691_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_691_1 Hex.FpPoly.X) = 691 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_691_1

/-- The Conway generator of GF(691^2) has order 477480. -/
theorem orderOf_gen_691_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_691_2 Hex.FpPoly.X) = 691 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_691_2

/-- The Conway generator of GF(691^3) has order 329939370. -/
theorem orderOf_gen_691_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_691_3 Hex.FpPoly.X) = 691 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_691_3

/-- The Conway generator of GF(701^1) has order 700. -/
theorem orderOf_gen_701_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_701_1 Hex.FpPoly.X) = 701 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_701_1

/-- The Conway generator of GF(701^2) has order 491400. -/
theorem orderOf_gen_701_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_701_2 Hex.FpPoly.X) = 701 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_701_2

/-- The Conway generator of GF(701^3) has order 344472100. -/
theorem orderOf_gen_701_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_701_3 Hex.FpPoly.X) = 701 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_701_3

/-- The Conway generator of GF(709^1) has order 708. -/
theorem orderOf_gen_709_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_709_1 Hex.FpPoly.X) = 709 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_709_1

/-- The Conway generator of GF(709^2) has order 502680. -/
theorem orderOf_gen_709_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_709_2 Hex.FpPoly.X) = 709 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_709_2

/-- The Conway generator of GF(709^3) has order 356400828. -/
theorem orderOf_gen_709_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_709_3 Hex.FpPoly.X) = 709 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_709_3

/-- The Conway generator of GF(719^1) has order 718. -/
theorem orderOf_gen_719_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_719_1 Hex.FpPoly.X) = 719 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_719_1

/-- The Conway generator of GF(719^2) has order 516960. -/
theorem orderOf_gen_719_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_719_2 Hex.FpPoly.X) = 719 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_719_2

/-- The Conway generator of GF(719^3) has order 371694958. -/
theorem orderOf_gen_719_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_719_3 Hex.FpPoly.X) = 719 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_719_3

/-- The Conway generator of GF(727^1) has order 726. -/
theorem orderOf_gen_727_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_727_1 Hex.FpPoly.X) = 727 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_727_1

/-- The Conway generator of GF(727^2) has order 528528. -/
theorem orderOf_gen_727_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_727_2 Hex.FpPoly.X) = 727 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_727_2

/-- The Conway generator of GF(727^3) has order 384240582. -/
theorem orderOf_gen_727_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_727_3 Hex.FpPoly.X) = 727 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_727_3

/-- The Conway generator of GF(733^1) has order 732. -/
theorem orderOf_gen_733_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_733_1 Hex.FpPoly.X) = 733 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_733_1

/-- The Conway generator of GF(733^2) has order 537288. -/
theorem orderOf_gen_733_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_733_2 Hex.FpPoly.X) = 733 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_733_2

/-- The Conway generator of GF(733^3) has order 393832836. -/
theorem orderOf_gen_733_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_733_3 Hex.FpPoly.X) = 733 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_733_3

/-- The Conway generator of GF(739^1) has order 738. -/
theorem orderOf_gen_739_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_739_1 Hex.FpPoly.X) = 739 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_739_1

/-- The Conway generator of GF(739^2) has order 546120. -/
theorem orderOf_gen_739_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_739_2 Hex.FpPoly.X) = 739 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_739_2

/-- The Conway generator of GF(739^3) has order 403583418. -/
theorem orderOf_gen_739_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_739_3 Hex.FpPoly.X) = 739 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_739_3

/-- The Conway generator of GF(743^1) has order 742. -/
theorem orderOf_gen_743_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_743_1 Hex.FpPoly.X) = 743 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_743_1

/-- The Conway generator of GF(743^2) has order 552048. -/
theorem orderOf_gen_743_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_743_2 Hex.FpPoly.X) = 743 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_743_2

/-- The Conway generator of GF(743^3) has order 410172406. -/
theorem orderOf_gen_743_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_743_3 Hex.FpPoly.X) = 743 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_743_3

/-- The Conway generator of GF(751^1) has order 750. -/
theorem orderOf_gen_751_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_751_1 Hex.FpPoly.X) = 751 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_751_1

/-- The Conway generator of GF(751^2) has order 564000. -/
theorem orderOf_gen_751_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_751_2 Hex.FpPoly.X) = 751 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_751_2

/-- The Conway generator of GF(751^3) has order 423564750. -/
theorem orderOf_gen_751_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_751_3 Hex.FpPoly.X) = 751 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_751_3

/-- The Conway generator of GF(757^1) has order 756. -/
theorem orderOf_gen_757_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_757_1 Hex.FpPoly.X) = 757 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_757_1

/-- The Conway generator of GF(757^2) has order 573048. -/
theorem orderOf_gen_757_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_757_2 Hex.FpPoly.X) = 757 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_757_2

/-- The Conway generator of GF(757^3) has order 433798092. -/
theorem orderOf_gen_757_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_757_3 Hex.FpPoly.X) = 757 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_757_3

/-- The Conway generator of GF(761^1) has order 760. -/
theorem orderOf_gen_761_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_761_1 Hex.FpPoly.X) = 761 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_761_1

/-- The Conway generator of GF(761^2) has order 579120. -/
theorem orderOf_gen_761_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_761_2 Hex.FpPoly.X) = 761 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_761_2

/-- The Conway generator of GF(761^3) has order 440711080. -/
theorem orderOf_gen_761_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_761_3 Hex.FpPoly.X) = 761 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_761_3

/-- The Conway generator of GF(769^1) has order 768. -/
theorem orderOf_gen_769_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_769_1 Hex.FpPoly.X) = 769 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_769_1

/-- The Conway generator of GF(769^2) has order 591360. -/
theorem orderOf_gen_769_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_769_2 Hex.FpPoly.X) = 769 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_769_2

/-- The Conway generator of GF(769^3) has order 454756608. -/
theorem orderOf_gen_769_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_769_3 Hex.FpPoly.X) = 769 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_769_3

/-- The Conway generator of GF(773^1) has order 772. -/
theorem orderOf_gen_773_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_773_1 Hex.FpPoly.X) = 773 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_773_1

/-- The Conway generator of GF(773^2) has order 597528. -/
theorem orderOf_gen_773_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_773_2 Hex.FpPoly.X) = 773 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_773_2

/-- The Conway generator of GF(773^3) has order 461889916. -/
theorem orderOf_gen_773_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_773_3 Hex.FpPoly.X) = 773 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_773_3

/-- The Conway generator of GF(787^1) has order 786. -/
theorem orderOf_gen_787_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_787_1 Hex.FpPoly.X) = 787 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_787_1

/-- The Conway generator of GF(787^2) has order 619368. -/
theorem orderOf_gen_787_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_787_2 Hex.FpPoly.X) = 787 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_787_2

/-- The Conway generator of GF(787^3) has order 487443402. -/
theorem orderOf_gen_787_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_787_3 Hex.FpPoly.X) = 787 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_787_3

/-- The Conway generator of GF(797^1) has order 796. -/
theorem orderOf_gen_797_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_797_1 Hex.FpPoly.X) = 797 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_797_1

/-- The Conway generator of GF(797^2) has order 635208. -/
theorem orderOf_gen_797_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_797_2 Hex.FpPoly.X) = 797 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_797_2

/-- The Conway generator of GF(797^3) has order 506261572. -/
theorem orderOf_gen_797_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_797_3 Hex.FpPoly.X) = 797 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_797_3

/-- The Conway generator of GF(809^1) has order 808. -/
theorem orderOf_gen_809_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_809_1 Hex.FpPoly.X) = 809 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_809_1

/-- The Conway generator of GF(809^2) has order 654480. -/
theorem orderOf_gen_809_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_809_2 Hex.FpPoly.X) = 809 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_809_2

/-- The Conway generator of GF(809^3) has order 529475128. -/
theorem orderOf_gen_809_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_809_3 Hex.FpPoly.X) = 809 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_809_3

/-- The Conway generator of GF(811^1) has order 810. -/
theorem orderOf_gen_811_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_811_1 Hex.FpPoly.X) = 811 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_811_1

/-- The Conway generator of GF(811^2) has order 657720. -/
theorem orderOf_gen_811_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_811_2 Hex.FpPoly.X) = 811 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_811_2

end HexGFqMathlib

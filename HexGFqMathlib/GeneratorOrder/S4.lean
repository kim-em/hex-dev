/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.PrimitivityCore

public section

namespace HexGFqMathlib

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

/-- The Conway generator of GF(673^4) has order 205144679040. -/
theorem orderOf_gen_673_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_673_4 Hex.FpPoly.X) = 673 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_673_4

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

/-- The Conway generator of GF(677^4) has order 210065472240. -/
theorem orderOf_gen_677_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_677_4 Hex.FpPoly.X) = 677 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_677_4

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

/-- The Conway generator of GF(683^4) has order 217611987120. -/
theorem orderOf_gen_683_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_683_4 Hex.FpPoly.X) = 683 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_683_4

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

/-- The Conway generator of GF(691^4) has order 227988105360. -/
theorem orderOf_gen_691_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_691_4 Hex.FpPoly.X) = 691 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_691_4

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

/-- The Conway generator of GF(701^4) has order 241474942800. -/
theorem orderOf_gen_701_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_701_4 Hex.FpPoly.X) = 701 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_701_4

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

/-- The Conway generator of GF(709^4) has order 252688187760. -/
theorem orderOf_gen_709_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_709_4 Hex.FpPoly.X) = 709 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_709_4

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

/-- The Conway generator of GF(719^4) has order 267248675520. -/
theorem orderOf_gen_719_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_719_4 Hex.FpPoly.X) = 719 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_719_4

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

/-- The Conway generator of GF(727^4) has order 279342903840. -/
theorem orderOf_gen_727_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_727_4 Hex.FpPoly.X) = 727 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_727_4

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

/-- The Conway generator of GF(733^4) has order 288679469520. -/
theorem orderOf_gen_733_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_733_4 Hex.FpPoly.X) = 733 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_733_4

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

/-- The Conway generator of GF(739^4) has order 298248146640. -/
theorem orderOf_gen_739_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_739_4 Hex.FpPoly.X) = 739 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_739_4

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

/-- The Conway generator of GF(743^4) has order 304758098400. -/
theorem orderOf_gen_743_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_743_4 Hex.FpPoly.X) = 743 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_743_4

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

/-- The Conway generator of GF(751^4) has order 318097128000. -/
theorem orderOf_gen_751_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_751_4 Hex.FpPoly.X) = 751 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_751_4

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

/-- The Conway generator of GF(757^4) has order 328385156400. -/
theorem orderOf_gen_757_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_757_4 Hex.FpPoly.X) = 757 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_757_4

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

/-- The Conway generator of GF(761^4) has order 335381132640. -/
theorem orderOf_gen_761_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_761_4 Hex.FpPoly.X) = 761 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_761_4

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

/-- The Conway generator of GF(769^4) has order 349707832320. -/
theorem orderOf_gen_769_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_769_4 Hex.FpPoly.X) = 769 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_769_4

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

/-- The Conway generator of GF(773^4) has order 357040905840. -/
theorem orderOf_gen_773_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_773_4 Hex.FpPoly.X) = 773 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_773_4

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

/-- The Conway generator of GF(787^4) has order 383617958160. -/
theorem orderOf_gen_787_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_787_4 Hex.FpPoly.X) = 787 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_787_4

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

/-- The Conway generator of GF(797^4) has order 403490473680. -/
theorem orderOf_gen_797_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_797_4 Hex.FpPoly.X) = 797 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_797_4

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

/-- The Conway generator of GF(809^4) has order 428345379360. -/
theorem orderOf_gen_809_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_809_4 Hex.FpPoly.X) = 809 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_809_4

/-- The Conway generator of GF(811^1) has order 810. -/
theorem orderOf_gen_811_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_811_1 Hex.FpPoly.X) = 811 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_811_1

/-- The Conway generator of GF(811^2) has order 657720. -/
theorem orderOf_gen_811_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_811_2 Hex.FpPoly.X) = 811 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_811_2

/-- The Conway generator of GF(811^3) has order 533411730. -/
theorem orderOf_gen_811_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_811_3 Hex.FpPoly.X) = 811 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_811_3

/-- The Conway generator of GF(811^4) has order 432596913840. -/
theorem orderOf_gen_811_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_811_4 Hex.FpPoly.X) = 811 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_811_4

/-- The Conway generator of GF(821^1) has order 820. -/
theorem orderOf_gen_821_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_821_1 Hex.FpPoly.X) = 821 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_821_1

/-- The Conway generator of GF(821^2) has order 674040. -/
theorem orderOf_gen_821_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_821_2 Hex.FpPoly.X) = 821 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_821_2

/-- The Conway generator of GF(821^3) has order 553387660. -/
theorem orderOf_gen_821_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_821_3 Hex.FpPoly.X) = 821 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_821_3

/-- The Conway generator of GF(821^4) has order 454331269680. -/
theorem orderOf_gen_821_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_821_4 Hex.FpPoly.X) = 821 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_821_4

/-- The Conway generator of GF(823^1) has order 822. -/
theorem orderOf_gen_823_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_823_1 Hex.FpPoly.X) = 823 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_823_1

/-- The Conway generator of GF(823^2) has order 677328. -/
theorem orderOf_gen_823_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_823_2 Hex.FpPoly.X) = 823 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_823_2

/-- The Conway generator of GF(823^3) has order 557441766. -/
theorem orderOf_gen_823_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_823_3 Hex.FpPoly.X) = 823 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_823_3

/-- The Conway generator of GF(823^4) has order 458774574240. -/
theorem orderOf_gen_823_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_823_4 Hex.FpPoly.X) = 823 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_823_4

/-- The Conway generator of GF(827^1) has order 826. -/
theorem orderOf_gen_827_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_827_1 Hex.FpPoly.X) = 827 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_827_1

/-- The Conway generator of GF(827^2) has order 683928. -/
theorem orderOf_gen_827_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_827_2 Hex.FpPoly.X) = 827 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_827_2

/-- The Conway generator of GF(827^3) has order 565609282. -/
theorem orderOf_gen_827_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_827_3 Hex.FpPoly.X) = 827 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_827_3

/-- The Conway generator of GF(827^4) has order 467758877040. -/
theorem orderOf_gen_827_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_827_4 Hex.FpPoly.X) = 827 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_827_4

/-- The Conway generator of GF(829^1) has order 828. -/
theorem orderOf_gen_829_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_829_1 Hex.FpPoly.X) = 829 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_829_1

/-- The Conway generator of GF(829^2) has order 687240. -/
theorem orderOf_gen_829_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_829_2 Hex.FpPoly.X) = 829 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_829_2

/-- The Conway generator of GF(829^3) has order 569722788. -/
theorem orderOf_gen_829_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_829_3 Hex.FpPoly.X) = 829 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_829_3

/-- The Conway generator of GF(829^4) has order 472300192080. -/
theorem orderOf_gen_829_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_829_4 Hex.FpPoly.X) = 829 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_829_4

/-- The Conway generator of GF(839^1) has order 838. -/
theorem orderOf_gen_839_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_839_1 Hex.FpPoly.X) = 839 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_839_1

/-- The Conway generator of GF(839^2) has order 703920. -/
theorem orderOf_gen_839_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_839_2 Hex.FpPoly.X) = 839 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_839_2

/-- The Conway generator of GF(839^3) has order 590589718. -/
theorem orderOf_gen_839_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_839_3 Hex.FpPoly.X) = 839 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_839_3

/-- The Conway generator of GF(839^4) has order 495504774240. -/
theorem orderOf_gen_839_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_839_4 Hex.FpPoly.X) = 839 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_839_4

/-- The Conway generator of GF(853^1) has order 852. -/
theorem orderOf_gen_853_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_853_1 Hex.FpPoly.X) = 853 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_853_1

/-- The Conway generator of GF(853^2) has order 727608. -/
theorem orderOf_gen_853_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_853_2 Hex.FpPoly.X) = 853 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_853_2

/-- The Conway generator of GF(853^3) has order 620650476. -/
theorem orderOf_gen_853_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_853_3 Hex.FpPoly.X) = 853 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_853_3

/-- The Conway generator of GF(853^4) has order 529414856880. -/
theorem orderOf_gen_853_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_853_4 Hex.FpPoly.X) = 853 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_853_4

/-- The Conway generator of GF(857^1) has order 856. -/
theorem orderOf_gen_857_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_857_1 Hex.FpPoly.X) = 857 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_857_1

/-- The Conway generator of GF(857^2) has order 734448. -/
theorem orderOf_gen_857_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_857_2 Hex.FpPoly.X) = 857 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_857_2

/-- The Conway generator of GF(857^3) has order 629422792. -/
theorem orderOf_gen_857_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_857_3 Hex.FpPoly.X) = 857 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_857_3

/-- The Conway generator of GF(857^4) has order 539415333600. -/
theorem orderOf_gen_857_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_857_4 Hex.FpPoly.X) = 857 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_857_4

/-- The Conway generator of GF(859^1) has order 858. -/
theorem orderOf_gen_859_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_859_1 Hex.FpPoly.X) = 859 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_859_1

/-- The Conway generator of GF(859^2) has order 737880. -/
theorem orderOf_gen_859_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_859_2 Hex.FpPoly.X) = 859 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_859_2

/-- The Conway generator of GF(859^3) has order 633839778. -/
theorem orderOf_gen_859_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_859_3 Hex.FpPoly.X) = 859 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_859_3

/-- The Conway generator of GF(859^4) has order 544468370160. -/
theorem orderOf_gen_859_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_859_4 Hex.FpPoly.X) = 859 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_859_4

/-- The Conway generator of GF(863^1) has order 862. -/
theorem orderOf_gen_863_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_863_1 Hex.FpPoly.X) = 863 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_863_1

/-- The Conway generator of GF(863^2) has order 744768. -/
theorem orderOf_gen_863_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_863_2 Hex.FpPoly.X) = 863 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_863_2

/-- The Conway generator of GF(863^3) has order 642735646. -/
theorem orderOf_gen_863_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_863_3 Hex.FpPoly.X) = 863 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_863_3

/-- The Conway generator of GF(863^4) has order 554680863360. -/
theorem orderOf_gen_863_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_863_4 Hex.FpPoly.X) = 863 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_863_4

/-- The Conway generator of GF(877^1) has order 876. -/
theorem orderOf_gen_877_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_877_1 Hex.FpPoly.X) = 877 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_877_1

/-- The Conway generator of GF(877^2) has order 769128. -/
theorem orderOf_gen_877_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_877_2 Hex.FpPoly.X) = 877 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_877_2

/-- The Conway generator of GF(877^3) has order 674526132. -/
theorem orderOf_gen_877_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_877_3 Hex.FpPoly.X) = 877 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_877_3

/-- The Conway generator of GF(877^4) has order 591559418640. -/
theorem orderOf_gen_877_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_877_4 Hex.FpPoly.X) = 877 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_877_4

/-- The Conway generator of GF(881^1) has order 880. -/
theorem orderOf_gen_881_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_881_1 Hex.FpPoly.X) = 881 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_881_1

/-- The Conway generator of GF(881^2) has order 776160. -/
theorem orderOf_gen_881_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_881_2 Hex.FpPoly.X) = 881 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_881_2

/-- The Conway generator of GF(881^3) has order 683797840. -/
theorem orderOf_gen_881_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_881_3 Hex.FpPoly.X) = 881 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_881_3

/-- The Conway generator of GF(881^4) has order 602425897920. -/
theorem orderOf_gen_881_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_881_4 Hex.FpPoly.X) = 881 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_881_4

/-- The Conway generator of GF(883^1) has order 882. -/
theorem orderOf_gen_883_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_883_1 Hex.FpPoly.X) = 883 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_883_1

/-- The Conway generator of GF(883^2) has order 779688. -/
theorem orderOf_gen_883_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_883_2 Hex.FpPoly.X) = 883 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_883_2

/-- The Conway generator of GF(883^3) has order 688465386. -/
theorem orderOf_gen_883_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_883_3 Hex.FpPoly.X) = 883 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_883_3

/-- The Conway generator of GF(883^4) has order 607914936720. -/
theorem orderOf_gen_883_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_883_4 Hex.FpPoly.X) = 883 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_883_4

end HexGFqMathlib

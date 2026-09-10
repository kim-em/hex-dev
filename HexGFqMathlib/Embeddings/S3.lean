/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.Subfield

public section

namespace HexGFqMathlib.Conway

/-- The canonical embedding of GF(541^1) into GF(541^2). -/
noncomputable def embed_541_1_2 :
    Hex.GFq 541 1 Hex.Conway.supportedEntry_541_1 →+*
      Hex.GFq 541 2 Hex.Conway.supportedEntry_541_2 :=
  conwayEmbed 541 1 2 _ _ Hex.Conway.compat_541_1_2

/-- The canonical embedding of GF(541^1) into GF(541^3). -/
noncomputable def embed_541_1_3 :
    Hex.GFq 541 1 Hex.Conway.supportedEntry_541_1 →+*
      Hex.GFq 541 3 Hex.Conway.supportedEntry_541_3 :=
  conwayEmbed 541 1 3 _ _ Hex.Conway.compat_541_1_3

/-- The canonical embedding of GF(547^1) into GF(547^2). -/
noncomputable def embed_547_1_2 :
    Hex.GFq 547 1 Hex.Conway.supportedEntry_547_1 →+*
      Hex.GFq 547 2 Hex.Conway.supportedEntry_547_2 :=
  conwayEmbed 547 1 2 _ _ Hex.Conway.compat_547_1_2

/-- The canonical embedding of GF(547^1) into GF(547^3). -/
noncomputable def embed_547_1_3 :
    Hex.GFq 547 1 Hex.Conway.supportedEntry_547_1 →+*
      Hex.GFq 547 3 Hex.Conway.supportedEntry_547_3 :=
  conwayEmbed 547 1 3 _ _ Hex.Conway.compat_547_1_3

/-- The canonical embedding of GF(557^1) into GF(557^2). -/
noncomputable def embed_557_1_2 :
    Hex.GFq 557 1 Hex.Conway.supportedEntry_557_1 →+*
      Hex.GFq 557 2 Hex.Conway.supportedEntry_557_2 :=
  conwayEmbed 557 1 2 _ _ Hex.Conway.compat_557_1_2

/-- The canonical embedding of GF(557^1) into GF(557^3). -/
noncomputable def embed_557_1_3 :
    Hex.GFq 557 1 Hex.Conway.supportedEntry_557_1 →+*
      Hex.GFq 557 3 Hex.Conway.supportedEntry_557_3 :=
  conwayEmbed 557 1 3 _ _ Hex.Conway.compat_557_1_3

/-- The canonical embedding of GF(563^1) into GF(563^2). -/
noncomputable def embed_563_1_2 :
    Hex.GFq 563 1 Hex.Conway.supportedEntry_563_1 →+*
      Hex.GFq 563 2 Hex.Conway.supportedEntry_563_2 :=
  conwayEmbed 563 1 2 _ _ Hex.Conway.compat_563_1_2

/-- The canonical embedding of GF(563^1) into GF(563^3). -/
noncomputable def embed_563_1_3 :
    Hex.GFq 563 1 Hex.Conway.supportedEntry_563_1 →+*
      Hex.GFq 563 3 Hex.Conway.supportedEntry_563_3 :=
  conwayEmbed 563 1 3 _ _ Hex.Conway.compat_563_1_3

/-- The canonical embedding of GF(569^1) into GF(569^2). -/
noncomputable def embed_569_1_2 :
    Hex.GFq 569 1 Hex.Conway.supportedEntry_569_1 →+*
      Hex.GFq 569 2 Hex.Conway.supportedEntry_569_2 :=
  conwayEmbed 569 1 2 _ _ Hex.Conway.compat_569_1_2

/-- The canonical embedding of GF(569^1) into GF(569^3). -/
noncomputable def embed_569_1_3 :
    Hex.GFq 569 1 Hex.Conway.supportedEntry_569_1 →+*
      Hex.GFq 569 3 Hex.Conway.supportedEntry_569_3 :=
  conwayEmbed 569 1 3 _ _ Hex.Conway.compat_569_1_3

/-- The canonical embedding of GF(571^1) into GF(571^2). -/
noncomputable def embed_571_1_2 :
    Hex.GFq 571 1 Hex.Conway.supportedEntry_571_1 →+*
      Hex.GFq 571 2 Hex.Conway.supportedEntry_571_2 :=
  conwayEmbed 571 1 2 _ _ Hex.Conway.compat_571_1_2

/-- The canonical embedding of GF(571^1) into GF(571^3). -/
noncomputable def embed_571_1_3 :
    Hex.GFq 571 1 Hex.Conway.supportedEntry_571_1 →+*
      Hex.GFq 571 3 Hex.Conway.supportedEntry_571_3 :=
  conwayEmbed 571 1 3 _ _ Hex.Conway.compat_571_1_3

/-- The canonical embedding of GF(577^1) into GF(577^2). -/
noncomputable def embed_577_1_2 :
    Hex.GFq 577 1 Hex.Conway.supportedEntry_577_1 →+*
      Hex.GFq 577 2 Hex.Conway.supportedEntry_577_2 :=
  conwayEmbed 577 1 2 _ _ Hex.Conway.compat_577_1_2

/-- The canonical embedding of GF(577^1) into GF(577^3). -/
noncomputable def embed_577_1_3 :
    Hex.GFq 577 1 Hex.Conway.supportedEntry_577_1 →+*
      Hex.GFq 577 3 Hex.Conway.supportedEntry_577_3 :=
  conwayEmbed 577 1 3 _ _ Hex.Conway.compat_577_1_3

/-- The canonical embedding of GF(587^1) into GF(587^2). -/
noncomputable def embed_587_1_2 :
    Hex.GFq 587 1 Hex.Conway.supportedEntry_587_1 →+*
      Hex.GFq 587 2 Hex.Conway.supportedEntry_587_2 :=
  conwayEmbed 587 1 2 _ _ Hex.Conway.compat_587_1_2

/-- The canonical embedding of GF(587^1) into GF(587^3). -/
noncomputable def embed_587_1_3 :
    Hex.GFq 587 1 Hex.Conway.supportedEntry_587_1 →+*
      Hex.GFq 587 3 Hex.Conway.supportedEntry_587_3 :=
  conwayEmbed 587 1 3 _ _ Hex.Conway.compat_587_1_3

/-- The canonical embedding of GF(593^1) into GF(593^2). -/
noncomputable def embed_593_1_2 :
    Hex.GFq 593 1 Hex.Conway.supportedEntry_593_1 →+*
      Hex.GFq 593 2 Hex.Conway.supportedEntry_593_2 :=
  conwayEmbed 593 1 2 _ _ Hex.Conway.compat_593_1_2

/-- The canonical embedding of GF(593^1) into GF(593^3). -/
noncomputable def embed_593_1_3 :
    Hex.GFq 593 1 Hex.Conway.supportedEntry_593_1 →+*
      Hex.GFq 593 3 Hex.Conway.supportedEntry_593_3 :=
  conwayEmbed 593 1 3 _ _ Hex.Conway.compat_593_1_3

/-- The canonical embedding of GF(599^1) into GF(599^2). -/
noncomputable def embed_599_1_2 :
    Hex.GFq 599 1 Hex.Conway.supportedEntry_599_1 →+*
      Hex.GFq 599 2 Hex.Conway.supportedEntry_599_2 :=
  conwayEmbed 599 1 2 _ _ Hex.Conway.compat_599_1_2

/-- The canonical embedding of GF(599^1) into GF(599^3). -/
noncomputable def embed_599_1_3 :
    Hex.GFq 599 1 Hex.Conway.supportedEntry_599_1 →+*
      Hex.GFq 599 3 Hex.Conway.supportedEntry_599_3 :=
  conwayEmbed 599 1 3 _ _ Hex.Conway.compat_599_1_3

/-- The canonical embedding of GF(601^1) into GF(601^2). -/
noncomputable def embed_601_1_2 :
    Hex.GFq 601 1 Hex.Conway.supportedEntry_601_1 →+*
      Hex.GFq 601 2 Hex.Conway.supportedEntry_601_2 :=
  conwayEmbed 601 1 2 _ _ Hex.Conway.compat_601_1_2

/-- The canonical embedding of GF(601^1) into GF(601^3). -/
noncomputable def embed_601_1_3 :
    Hex.GFq 601 1 Hex.Conway.supportedEntry_601_1 →+*
      Hex.GFq 601 3 Hex.Conway.supportedEntry_601_3 :=
  conwayEmbed 601 1 3 _ _ Hex.Conway.compat_601_1_3

/-- The canonical embedding of GF(607^1) into GF(607^2). -/
noncomputable def embed_607_1_2 :
    Hex.GFq 607 1 Hex.Conway.supportedEntry_607_1 →+*
      Hex.GFq 607 2 Hex.Conway.supportedEntry_607_2 :=
  conwayEmbed 607 1 2 _ _ Hex.Conway.compat_607_1_2

/-- The canonical embedding of GF(607^1) into GF(607^3). -/
noncomputable def embed_607_1_3 :
    Hex.GFq 607 1 Hex.Conway.supportedEntry_607_1 →+*
      Hex.GFq 607 3 Hex.Conway.supportedEntry_607_3 :=
  conwayEmbed 607 1 3 _ _ Hex.Conway.compat_607_1_3

/-- The canonical embedding of GF(613^1) into GF(613^2). -/
noncomputable def embed_613_1_2 :
    Hex.GFq 613 1 Hex.Conway.supportedEntry_613_1 →+*
      Hex.GFq 613 2 Hex.Conway.supportedEntry_613_2 :=
  conwayEmbed 613 1 2 _ _ Hex.Conway.compat_613_1_2

/-- The canonical embedding of GF(613^1) into GF(613^3). -/
noncomputable def embed_613_1_3 :
    Hex.GFq 613 1 Hex.Conway.supportedEntry_613_1 →+*
      Hex.GFq 613 3 Hex.Conway.supportedEntry_613_3 :=
  conwayEmbed 613 1 3 _ _ Hex.Conway.compat_613_1_3

/-- The canonical embedding of GF(617^1) into GF(617^2). -/
noncomputable def embed_617_1_2 :
    Hex.GFq 617 1 Hex.Conway.supportedEntry_617_1 →+*
      Hex.GFq 617 2 Hex.Conway.supportedEntry_617_2 :=
  conwayEmbed 617 1 2 _ _ Hex.Conway.compat_617_1_2

/-- The canonical embedding of GF(617^1) into GF(617^3). -/
noncomputable def embed_617_1_3 :
    Hex.GFq 617 1 Hex.Conway.supportedEntry_617_1 →+*
      Hex.GFq 617 3 Hex.Conway.supportedEntry_617_3 :=
  conwayEmbed 617 1 3 _ _ Hex.Conway.compat_617_1_3

/-- The canonical embedding of GF(619^1) into GF(619^2). -/
noncomputable def embed_619_1_2 :
    Hex.GFq 619 1 Hex.Conway.supportedEntry_619_1 →+*
      Hex.GFq 619 2 Hex.Conway.supportedEntry_619_2 :=
  conwayEmbed 619 1 2 _ _ Hex.Conway.compat_619_1_2

/-- The canonical embedding of GF(619^1) into GF(619^3). -/
noncomputable def embed_619_1_3 :
    Hex.GFq 619 1 Hex.Conway.supportedEntry_619_1 →+*
      Hex.GFq 619 3 Hex.Conway.supportedEntry_619_3 :=
  conwayEmbed 619 1 3 _ _ Hex.Conway.compat_619_1_3

/-- The canonical embedding of GF(631^1) into GF(631^2). -/
noncomputable def embed_631_1_2 :
    Hex.GFq 631 1 Hex.Conway.supportedEntry_631_1 →+*
      Hex.GFq 631 2 Hex.Conway.supportedEntry_631_2 :=
  conwayEmbed 631 1 2 _ _ Hex.Conway.compat_631_1_2

/-- The canonical embedding of GF(631^1) into GF(631^3). -/
noncomputable def embed_631_1_3 :
    Hex.GFq 631 1 Hex.Conway.supportedEntry_631_1 →+*
      Hex.GFq 631 3 Hex.Conway.supportedEntry_631_3 :=
  conwayEmbed 631 1 3 _ _ Hex.Conway.compat_631_1_3

/-- The canonical embedding of GF(641^1) into GF(641^2). -/
noncomputable def embed_641_1_2 :
    Hex.GFq 641 1 Hex.Conway.supportedEntry_641_1 →+*
      Hex.GFq 641 2 Hex.Conway.supportedEntry_641_2 :=
  conwayEmbed 641 1 2 _ _ Hex.Conway.compat_641_1_2

/-- The canonical embedding of GF(641^1) into GF(641^3). -/
noncomputable def embed_641_1_3 :
    Hex.GFq 641 1 Hex.Conway.supportedEntry_641_1 →+*
      Hex.GFq 641 3 Hex.Conway.supportedEntry_641_3 :=
  conwayEmbed 641 1 3 _ _ Hex.Conway.compat_641_1_3

/-- The canonical embedding of GF(643^1) into GF(643^2). -/
noncomputable def embed_643_1_2 :
    Hex.GFq 643 1 Hex.Conway.supportedEntry_643_1 →+*
      Hex.GFq 643 2 Hex.Conway.supportedEntry_643_2 :=
  conwayEmbed 643 1 2 _ _ Hex.Conway.compat_643_1_2

/-- The canonical embedding of GF(643^1) into GF(643^3). -/
noncomputable def embed_643_1_3 :
    Hex.GFq 643 1 Hex.Conway.supportedEntry_643_1 →+*
      Hex.GFq 643 3 Hex.Conway.supportedEntry_643_3 :=
  conwayEmbed 643 1 3 _ _ Hex.Conway.compat_643_1_3

/-- The canonical embedding of GF(647^1) into GF(647^2). -/
noncomputable def embed_647_1_2 :
    Hex.GFq 647 1 Hex.Conway.supportedEntry_647_1 →+*
      Hex.GFq 647 2 Hex.Conway.supportedEntry_647_2 :=
  conwayEmbed 647 1 2 _ _ Hex.Conway.compat_647_1_2

/-- The canonical embedding of GF(647^1) into GF(647^3). -/
noncomputable def embed_647_1_3 :
    Hex.GFq 647 1 Hex.Conway.supportedEntry_647_1 →+*
      Hex.GFq 647 3 Hex.Conway.supportedEntry_647_3 :=
  conwayEmbed 647 1 3 _ _ Hex.Conway.compat_647_1_3

/-- The canonical embedding of GF(653^1) into GF(653^2). -/
noncomputable def embed_653_1_2 :
    Hex.GFq 653 1 Hex.Conway.supportedEntry_653_1 →+*
      Hex.GFq 653 2 Hex.Conway.supportedEntry_653_2 :=
  conwayEmbed 653 1 2 _ _ Hex.Conway.compat_653_1_2

/-- The canonical embedding of GF(653^1) into GF(653^3). -/
noncomputable def embed_653_1_3 :
    Hex.GFq 653 1 Hex.Conway.supportedEntry_653_1 →+*
      Hex.GFq 653 3 Hex.Conway.supportedEntry_653_3 :=
  conwayEmbed 653 1 3 _ _ Hex.Conway.compat_653_1_3

/-- The canonical embedding of GF(659^1) into GF(659^2). -/
noncomputable def embed_659_1_2 :
    Hex.GFq 659 1 Hex.Conway.supportedEntry_659_1 →+*
      Hex.GFq 659 2 Hex.Conway.supportedEntry_659_2 :=
  conwayEmbed 659 1 2 _ _ Hex.Conway.compat_659_1_2

/-- The canonical embedding of GF(659^1) into GF(659^3). -/
noncomputable def embed_659_1_3 :
    Hex.GFq 659 1 Hex.Conway.supportedEntry_659_1 →+*
      Hex.GFq 659 3 Hex.Conway.supportedEntry_659_3 :=
  conwayEmbed 659 1 3 _ _ Hex.Conway.compat_659_1_3

/-- The canonical embedding of GF(661^1) into GF(661^2). -/
noncomputable def embed_661_1_2 :
    Hex.GFq 661 1 Hex.Conway.supportedEntry_661_1 →+*
      Hex.GFq 661 2 Hex.Conway.supportedEntry_661_2 :=
  conwayEmbed 661 1 2 _ _ Hex.Conway.compat_661_1_2

/-- The canonical embedding of GF(661^1) into GF(661^3). -/
noncomputable def embed_661_1_3 :
    Hex.GFq 661 1 Hex.Conway.supportedEntry_661_1 →+*
      Hex.GFq 661 3 Hex.Conway.supportedEntry_661_3 :=
  conwayEmbed 661 1 3 _ _ Hex.Conway.compat_661_1_3

/-- The canonical embedding of GF(673^1) into GF(673^2). -/
noncomputable def embed_673_1_2 :
    Hex.GFq 673 1 Hex.Conway.supportedEntry_673_1 →+*
      Hex.GFq 673 2 Hex.Conway.supportedEntry_673_2 :=
  conwayEmbed 673 1 2 _ _ Hex.Conway.compat_673_1_2

/-- The canonical embedding of GF(673^1) into GF(673^3). -/
noncomputable def embed_673_1_3 :
    Hex.GFq 673 1 Hex.Conway.supportedEntry_673_1 →+*
      Hex.GFq 673 3 Hex.Conway.supportedEntry_673_3 :=
  conwayEmbed 673 1 3 _ _ Hex.Conway.compat_673_1_3

/-- The canonical embedding of GF(677^1) into GF(677^2). -/
noncomputable def embed_677_1_2 :
    Hex.GFq 677 1 Hex.Conway.supportedEntry_677_1 →+*
      Hex.GFq 677 2 Hex.Conway.supportedEntry_677_2 :=
  conwayEmbed 677 1 2 _ _ Hex.Conway.compat_677_1_2

/-- The canonical embedding of GF(677^1) into GF(677^3). -/
noncomputable def embed_677_1_3 :
    Hex.GFq 677 1 Hex.Conway.supportedEntry_677_1 →+*
      Hex.GFq 677 3 Hex.Conway.supportedEntry_677_3 :=
  conwayEmbed 677 1 3 _ _ Hex.Conway.compat_677_1_3

/-- The canonical embedding of GF(683^1) into GF(683^2). -/
noncomputable def embed_683_1_2 :
    Hex.GFq 683 1 Hex.Conway.supportedEntry_683_1 →+*
      Hex.GFq 683 2 Hex.Conway.supportedEntry_683_2 :=
  conwayEmbed 683 1 2 _ _ Hex.Conway.compat_683_1_2

/-- The canonical embedding of GF(683^1) into GF(683^3). -/
noncomputable def embed_683_1_3 :
    Hex.GFq 683 1 Hex.Conway.supportedEntry_683_1 →+*
      Hex.GFq 683 3 Hex.Conway.supportedEntry_683_3 :=
  conwayEmbed 683 1 3 _ _ Hex.Conway.compat_683_1_3

/-- The canonical embedding of GF(691^1) into GF(691^2). -/
noncomputable def embed_691_1_2 :
    Hex.GFq 691 1 Hex.Conway.supportedEntry_691_1 →+*
      Hex.GFq 691 2 Hex.Conway.supportedEntry_691_2 :=
  conwayEmbed 691 1 2 _ _ Hex.Conway.compat_691_1_2

/-- The canonical embedding of GF(691^1) into GF(691^3). -/
noncomputable def embed_691_1_3 :
    Hex.GFq 691 1 Hex.Conway.supportedEntry_691_1 →+*
      Hex.GFq 691 3 Hex.Conway.supportedEntry_691_3 :=
  conwayEmbed 691 1 3 _ _ Hex.Conway.compat_691_1_3

/-- The canonical embedding of GF(701^1) into GF(701^2). -/
noncomputable def embed_701_1_2 :
    Hex.GFq 701 1 Hex.Conway.supportedEntry_701_1 →+*
      Hex.GFq 701 2 Hex.Conway.supportedEntry_701_2 :=
  conwayEmbed 701 1 2 _ _ Hex.Conway.compat_701_1_2

/-- The canonical embedding of GF(701^1) into GF(701^3). -/
noncomputable def embed_701_1_3 :
    Hex.GFq 701 1 Hex.Conway.supportedEntry_701_1 →+*
      Hex.GFq 701 3 Hex.Conway.supportedEntry_701_3 :=
  conwayEmbed 701 1 3 _ _ Hex.Conway.compat_701_1_3

/-- The canonical embedding of GF(709^1) into GF(709^2). -/
noncomputable def embed_709_1_2 :
    Hex.GFq 709 1 Hex.Conway.supportedEntry_709_1 →+*
      Hex.GFq 709 2 Hex.Conway.supportedEntry_709_2 :=
  conwayEmbed 709 1 2 _ _ Hex.Conway.compat_709_1_2

/-- The canonical embedding of GF(709^1) into GF(709^3). -/
noncomputable def embed_709_1_3 :
    Hex.GFq 709 1 Hex.Conway.supportedEntry_709_1 →+*
      Hex.GFq 709 3 Hex.Conway.supportedEntry_709_3 :=
  conwayEmbed 709 1 3 _ _ Hex.Conway.compat_709_1_3

/-- The canonical embedding of GF(719^1) into GF(719^2). -/
noncomputable def embed_719_1_2 :
    Hex.GFq 719 1 Hex.Conway.supportedEntry_719_1 →+*
      Hex.GFq 719 2 Hex.Conway.supportedEntry_719_2 :=
  conwayEmbed 719 1 2 _ _ Hex.Conway.compat_719_1_2

/-- The canonical embedding of GF(719^1) into GF(719^3). -/
noncomputable def embed_719_1_3 :
    Hex.GFq 719 1 Hex.Conway.supportedEntry_719_1 →+*
      Hex.GFq 719 3 Hex.Conway.supportedEntry_719_3 :=
  conwayEmbed 719 1 3 _ _ Hex.Conway.compat_719_1_3

/-- The canonical embedding of GF(727^1) into GF(727^2). -/
noncomputable def embed_727_1_2 :
    Hex.GFq 727 1 Hex.Conway.supportedEntry_727_1 →+*
      Hex.GFq 727 2 Hex.Conway.supportedEntry_727_2 :=
  conwayEmbed 727 1 2 _ _ Hex.Conway.compat_727_1_2

/-- The canonical embedding of GF(727^1) into GF(727^3). -/
noncomputable def embed_727_1_3 :
    Hex.GFq 727 1 Hex.Conway.supportedEntry_727_1 →+*
      Hex.GFq 727 3 Hex.Conway.supportedEntry_727_3 :=
  conwayEmbed 727 1 3 _ _ Hex.Conway.compat_727_1_3

/-- The canonical embedding of GF(733^1) into GF(733^2). -/
noncomputable def embed_733_1_2 :
    Hex.GFq 733 1 Hex.Conway.supportedEntry_733_1 →+*
      Hex.GFq 733 2 Hex.Conway.supportedEntry_733_2 :=
  conwayEmbed 733 1 2 _ _ Hex.Conway.compat_733_1_2

/-- The canonical embedding of GF(733^1) into GF(733^3). -/
noncomputable def embed_733_1_3 :
    Hex.GFq 733 1 Hex.Conway.supportedEntry_733_1 →+*
      Hex.GFq 733 3 Hex.Conway.supportedEntry_733_3 :=
  conwayEmbed 733 1 3 _ _ Hex.Conway.compat_733_1_3

/-- The canonical embedding of GF(739^1) into GF(739^2). -/
noncomputable def embed_739_1_2 :
    Hex.GFq 739 1 Hex.Conway.supportedEntry_739_1 →+*
      Hex.GFq 739 2 Hex.Conway.supportedEntry_739_2 :=
  conwayEmbed 739 1 2 _ _ Hex.Conway.compat_739_1_2

/-- The canonical embedding of GF(739^1) into GF(739^3). -/
noncomputable def embed_739_1_3 :
    Hex.GFq 739 1 Hex.Conway.supportedEntry_739_1 →+*
      Hex.GFq 739 3 Hex.Conway.supportedEntry_739_3 :=
  conwayEmbed 739 1 3 _ _ Hex.Conway.compat_739_1_3

/-- The canonical embedding of GF(743^1) into GF(743^2). -/
noncomputable def embed_743_1_2 :
    Hex.GFq 743 1 Hex.Conway.supportedEntry_743_1 →+*
      Hex.GFq 743 2 Hex.Conway.supportedEntry_743_2 :=
  conwayEmbed 743 1 2 _ _ Hex.Conway.compat_743_1_2

/-- The canonical embedding of GF(743^1) into GF(743^3). -/
noncomputable def embed_743_1_3 :
    Hex.GFq 743 1 Hex.Conway.supportedEntry_743_1 →+*
      Hex.GFq 743 3 Hex.Conway.supportedEntry_743_3 :=
  conwayEmbed 743 1 3 _ _ Hex.Conway.compat_743_1_3

/-- The canonical embedding of GF(751^1) into GF(751^2). -/
noncomputable def embed_751_1_2 :
    Hex.GFq 751 1 Hex.Conway.supportedEntry_751_1 →+*
      Hex.GFq 751 2 Hex.Conway.supportedEntry_751_2 :=
  conwayEmbed 751 1 2 _ _ Hex.Conway.compat_751_1_2

/-- The canonical embedding of GF(751^1) into GF(751^3). -/
noncomputable def embed_751_1_3 :
    Hex.GFq 751 1 Hex.Conway.supportedEntry_751_1 →+*
      Hex.GFq 751 3 Hex.Conway.supportedEntry_751_3 :=
  conwayEmbed 751 1 3 _ _ Hex.Conway.compat_751_1_3

/-- The canonical embedding of GF(757^1) into GF(757^2). -/
noncomputable def embed_757_1_2 :
    Hex.GFq 757 1 Hex.Conway.supportedEntry_757_1 →+*
      Hex.GFq 757 2 Hex.Conway.supportedEntry_757_2 :=
  conwayEmbed 757 1 2 _ _ Hex.Conway.compat_757_1_2

/-- The canonical embedding of GF(757^1) into GF(757^3). -/
noncomputable def embed_757_1_3 :
    Hex.GFq 757 1 Hex.Conway.supportedEntry_757_1 →+*
      Hex.GFq 757 3 Hex.Conway.supportedEntry_757_3 :=
  conwayEmbed 757 1 3 _ _ Hex.Conway.compat_757_1_3

/-- The canonical embedding of GF(761^1) into GF(761^2). -/
noncomputable def embed_761_1_2 :
    Hex.GFq 761 1 Hex.Conway.supportedEntry_761_1 →+*
      Hex.GFq 761 2 Hex.Conway.supportedEntry_761_2 :=
  conwayEmbed 761 1 2 _ _ Hex.Conway.compat_761_1_2

/-- The canonical embedding of GF(761^1) into GF(761^3). -/
noncomputable def embed_761_1_3 :
    Hex.GFq 761 1 Hex.Conway.supportedEntry_761_1 →+*
      Hex.GFq 761 3 Hex.Conway.supportedEntry_761_3 :=
  conwayEmbed 761 1 3 _ _ Hex.Conway.compat_761_1_3

/-- The canonical embedding of GF(769^1) into GF(769^2). -/
noncomputable def embed_769_1_2 :
    Hex.GFq 769 1 Hex.Conway.supportedEntry_769_1 →+*
      Hex.GFq 769 2 Hex.Conway.supportedEntry_769_2 :=
  conwayEmbed 769 1 2 _ _ Hex.Conway.compat_769_1_2

/-- The canonical embedding of GF(769^1) into GF(769^3). -/
noncomputable def embed_769_1_3 :
    Hex.GFq 769 1 Hex.Conway.supportedEntry_769_1 →+*
      Hex.GFq 769 3 Hex.Conway.supportedEntry_769_3 :=
  conwayEmbed 769 1 3 _ _ Hex.Conway.compat_769_1_3

/-- The canonical embedding of GF(773^1) into GF(773^2). -/
noncomputable def embed_773_1_2 :
    Hex.GFq 773 1 Hex.Conway.supportedEntry_773_1 →+*
      Hex.GFq 773 2 Hex.Conway.supportedEntry_773_2 :=
  conwayEmbed 773 1 2 _ _ Hex.Conway.compat_773_1_2

/-- The canonical embedding of GF(773^1) into GF(773^3). -/
noncomputable def embed_773_1_3 :
    Hex.GFq 773 1 Hex.Conway.supportedEntry_773_1 →+*
      Hex.GFq 773 3 Hex.Conway.supportedEntry_773_3 :=
  conwayEmbed 773 1 3 _ _ Hex.Conway.compat_773_1_3

/-- The canonical embedding of GF(787^1) into GF(787^2). -/
noncomputable def embed_787_1_2 :
    Hex.GFq 787 1 Hex.Conway.supportedEntry_787_1 →+*
      Hex.GFq 787 2 Hex.Conway.supportedEntry_787_2 :=
  conwayEmbed 787 1 2 _ _ Hex.Conway.compat_787_1_2

/-- The canonical embedding of GF(787^1) into GF(787^3). -/
noncomputable def embed_787_1_3 :
    Hex.GFq 787 1 Hex.Conway.supportedEntry_787_1 →+*
      Hex.GFq 787 3 Hex.Conway.supportedEntry_787_3 :=
  conwayEmbed 787 1 3 _ _ Hex.Conway.compat_787_1_3

/-- The canonical embedding of GF(797^1) into GF(797^2). -/
noncomputable def embed_797_1_2 :
    Hex.GFq 797 1 Hex.Conway.supportedEntry_797_1 →+*
      Hex.GFq 797 2 Hex.Conway.supportedEntry_797_2 :=
  conwayEmbed 797 1 2 _ _ Hex.Conway.compat_797_1_2

/-- The canonical embedding of GF(797^1) into GF(797^3). -/
noncomputable def embed_797_1_3 :
    Hex.GFq 797 1 Hex.Conway.supportedEntry_797_1 →+*
      Hex.GFq 797 3 Hex.Conway.supportedEntry_797_3 :=
  conwayEmbed 797 1 3 _ _ Hex.Conway.compat_797_1_3

/-- The canonical embedding of GF(809^1) into GF(809^2). -/
noncomputable def embed_809_1_2 :
    Hex.GFq 809 1 Hex.Conway.supportedEntry_809_1 →+*
      Hex.GFq 809 2 Hex.Conway.supportedEntry_809_2 :=
  conwayEmbed 809 1 2 _ _ Hex.Conway.compat_809_1_2

/-- The canonical embedding of GF(809^1) into GF(809^3). -/
noncomputable def embed_809_1_3 :
    Hex.GFq 809 1 Hex.Conway.supportedEntry_809_1 →+*
      Hex.GFq 809 3 Hex.Conway.supportedEntry_809_3 :=
  conwayEmbed 809 1 3 _ _ Hex.Conway.compat_809_1_3

/-- The canonical embedding of GF(811^1) into GF(811^2). -/
noncomputable def embed_811_1_2 :
    Hex.GFq 811 1 Hex.Conway.supportedEntry_811_1 →+*
      Hex.GFq 811 2 Hex.Conway.supportedEntry_811_2 :=
  conwayEmbed 811 1 2 _ _ Hex.Conway.compat_811_1_2

/-- The canonical embedding of GF(811^1) into GF(811^3). -/
noncomputable def embed_811_1_3 :
    Hex.GFq 811 1 Hex.Conway.supportedEntry_811_1 →+*
      Hex.GFq 811 3 Hex.Conway.supportedEntry_811_3 :=
  conwayEmbed 811 1 3 _ _ Hex.Conway.compat_811_1_3

/-- The canonical embedding of GF(821^1) into GF(821^2). -/
noncomputable def embed_821_1_2 :
    Hex.GFq 821 1 Hex.Conway.supportedEntry_821_1 →+*
      Hex.GFq 821 2 Hex.Conway.supportedEntry_821_2 :=
  conwayEmbed 821 1 2 _ _ Hex.Conway.compat_821_1_2

/-- The canonical embedding of GF(821^1) into GF(821^3). -/
noncomputable def embed_821_1_3 :
    Hex.GFq 821 1 Hex.Conway.supportedEntry_821_1 →+*
      Hex.GFq 821 3 Hex.Conway.supportedEntry_821_3 :=
  conwayEmbed 821 1 3 _ _ Hex.Conway.compat_821_1_3

/-- The canonical embedding of GF(823^1) into GF(823^2). -/
noncomputable def embed_823_1_2 :
    Hex.GFq 823 1 Hex.Conway.supportedEntry_823_1 →+*
      Hex.GFq 823 2 Hex.Conway.supportedEntry_823_2 :=
  conwayEmbed 823 1 2 _ _ Hex.Conway.compat_823_1_2

/-- The canonical embedding of GF(823^1) into GF(823^3). -/
noncomputable def embed_823_1_3 :
    Hex.GFq 823 1 Hex.Conway.supportedEntry_823_1 →+*
      Hex.GFq 823 3 Hex.Conway.supportedEntry_823_3 :=
  conwayEmbed 823 1 3 _ _ Hex.Conway.compat_823_1_3

/-- The canonical embedding of GF(827^1) into GF(827^2). -/
noncomputable def embed_827_1_2 :
    Hex.GFq 827 1 Hex.Conway.supportedEntry_827_1 →+*
      Hex.GFq 827 2 Hex.Conway.supportedEntry_827_2 :=
  conwayEmbed 827 1 2 _ _ Hex.Conway.compat_827_1_2

/-- The canonical embedding of GF(827^1) into GF(827^3). -/
noncomputable def embed_827_1_3 :
    Hex.GFq 827 1 Hex.Conway.supportedEntry_827_1 →+*
      Hex.GFq 827 3 Hex.Conway.supportedEntry_827_3 :=
  conwayEmbed 827 1 3 _ _ Hex.Conway.compat_827_1_3

/-- The canonical embedding of GF(829^1) into GF(829^2). -/
noncomputable def embed_829_1_2 :
    Hex.GFq 829 1 Hex.Conway.supportedEntry_829_1 →+*
      Hex.GFq 829 2 Hex.Conway.supportedEntry_829_2 :=
  conwayEmbed 829 1 2 _ _ Hex.Conway.compat_829_1_2

/-- The canonical embedding of GF(829^1) into GF(829^3). -/
noncomputable def embed_829_1_3 :
    Hex.GFq 829 1 Hex.Conway.supportedEntry_829_1 →+*
      Hex.GFq 829 3 Hex.Conway.supportedEntry_829_3 :=
  conwayEmbed 829 1 3 _ _ Hex.Conway.compat_829_1_3

/-- The canonical embedding of GF(839^1) into GF(839^2). -/
noncomputable def embed_839_1_2 :
    Hex.GFq 839 1 Hex.Conway.supportedEntry_839_1 →+*
      Hex.GFq 839 2 Hex.Conway.supportedEntry_839_2 :=
  conwayEmbed 839 1 2 _ _ Hex.Conway.compat_839_1_2

/-- The canonical embedding of GF(839^1) into GF(839^3). -/
noncomputable def embed_839_1_3 :
    Hex.GFq 839 1 Hex.Conway.supportedEntry_839_1 →+*
      Hex.GFq 839 3 Hex.Conway.supportedEntry_839_3 :=
  conwayEmbed 839 1 3 _ _ Hex.Conway.compat_839_1_3

/-- The canonical embedding of GF(853^1) into GF(853^2). -/
noncomputable def embed_853_1_2 :
    Hex.GFq 853 1 Hex.Conway.supportedEntry_853_1 →+*
      Hex.GFq 853 2 Hex.Conway.supportedEntry_853_2 :=
  conwayEmbed 853 1 2 _ _ Hex.Conway.compat_853_1_2

/-- The canonical embedding of GF(853^1) into GF(853^3). -/
noncomputable def embed_853_1_3 :
    Hex.GFq 853 1 Hex.Conway.supportedEntry_853_1 →+*
      Hex.GFq 853 3 Hex.Conway.supportedEntry_853_3 :=
  conwayEmbed 853 1 3 _ _ Hex.Conway.compat_853_1_3

/-- The canonical embedding of GF(857^1) into GF(857^2). -/
noncomputable def embed_857_1_2 :
    Hex.GFq 857 1 Hex.Conway.supportedEntry_857_1 →+*
      Hex.GFq 857 2 Hex.Conway.supportedEntry_857_2 :=
  conwayEmbed 857 1 2 _ _ Hex.Conway.compat_857_1_2

/-- The canonical embedding of GF(857^1) into GF(857^3). -/
noncomputable def embed_857_1_3 :
    Hex.GFq 857 1 Hex.Conway.supportedEntry_857_1 →+*
      Hex.GFq 857 3 Hex.Conway.supportedEntry_857_3 :=
  conwayEmbed 857 1 3 _ _ Hex.Conway.compat_857_1_3

/-- The canonical embedding of GF(859^1) into GF(859^2). -/
noncomputable def embed_859_1_2 :
    Hex.GFq 859 1 Hex.Conway.supportedEntry_859_1 →+*
      Hex.GFq 859 2 Hex.Conway.supportedEntry_859_2 :=
  conwayEmbed 859 1 2 _ _ Hex.Conway.compat_859_1_2

/-- The canonical embedding of GF(859^1) into GF(859^3). -/
noncomputable def embed_859_1_3 :
    Hex.GFq 859 1 Hex.Conway.supportedEntry_859_1 →+*
      Hex.GFq 859 3 Hex.Conway.supportedEntry_859_3 :=
  conwayEmbed 859 1 3 _ _ Hex.Conway.compat_859_1_3

/-- The canonical embedding of GF(863^1) into GF(863^2). -/
noncomputable def embed_863_1_2 :
    Hex.GFq 863 1 Hex.Conway.supportedEntry_863_1 →+*
      Hex.GFq 863 2 Hex.Conway.supportedEntry_863_2 :=
  conwayEmbed 863 1 2 _ _ Hex.Conway.compat_863_1_2

/-- The canonical embedding of GF(863^1) into GF(863^3). -/
noncomputable def embed_863_1_3 :
    Hex.GFq 863 1 Hex.Conway.supportedEntry_863_1 →+*
      Hex.GFq 863 3 Hex.Conway.supportedEntry_863_3 :=
  conwayEmbed 863 1 3 _ _ Hex.Conway.compat_863_1_3

/-- The canonical embedding of GF(877^1) into GF(877^2). -/
noncomputable def embed_877_1_2 :
    Hex.GFq 877 1 Hex.Conway.supportedEntry_877_1 →+*
      Hex.GFq 877 2 Hex.Conway.supportedEntry_877_2 :=
  conwayEmbed 877 1 2 _ _ Hex.Conway.compat_877_1_2

/-- The canonical embedding of GF(877^1) into GF(877^3). -/
noncomputable def embed_877_1_3 :
    Hex.GFq 877 1 Hex.Conway.supportedEntry_877_1 →+*
      Hex.GFq 877 3 Hex.Conway.supportedEntry_877_3 :=
  conwayEmbed 877 1 3 _ _ Hex.Conway.compat_877_1_3

/-- The canonical embedding of GF(881^1) into GF(881^2). -/
noncomputable def embed_881_1_2 :
    Hex.GFq 881 1 Hex.Conway.supportedEntry_881_1 →+*
      Hex.GFq 881 2 Hex.Conway.supportedEntry_881_2 :=
  conwayEmbed 881 1 2 _ _ Hex.Conway.compat_881_1_2

/-- The canonical embedding of GF(881^1) into GF(881^3). -/
noncomputable def embed_881_1_3 :
    Hex.GFq 881 1 Hex.Conway.supportedEntry_881_1 →+*
      Hex.GFq 881 3 Hex.Conway.supportedEntry_881_3 :=
  conwayEmbed 881 1 3 _ _ Hex.Conway.compat_881_1_3

/-- The canonical embedding of GF(883^1) into GF(883^2). -/
noncomputable def embed_883_1_2 :
    Hex.GFq 883 1 Hex.Conway.supportedEntry_883_1 →+*
      Hex.GFq 883 2 Hex.Conway.supportedEntry_883_2 :=
  conwayEmbed 883 1 2 _ _ Hex.Conway.compat_883_1_2

/-- The canonical embedding of GF(883^1) into GF(883^3). -/
noncomputable def embed_883_1_3 :
    Hex.GFq 883 1 Hex.Conway.supportedEntry_883_1 →+*
      Hex.GFq 883 3 Hex.Conway.supportedEntry_883_3 :=
  conwayEmbed 883 1 3 _ _ Hex.Conway.compat_883_1_3

/-- The canonical embedding of GF(887^1) into GF(887^2). -/
noncomputable def embed_887_1_2 :
    Hex.GFq 887 1 Hex.Conway.supportedEntry_887_1 →+*
      Hex.GFq 887 2 Hex.Conway.supportedEntry_887_2 :=
  conwayEmbed 887 1 2 _ _ Hex.Conway.compat_887_1_2

/-- The canonical embedding of GF(887^1) into GF(887^3). -/
noncomputable def embed_887_1_3 :
    Hex.GFq 887 1 Hex.Conway.supportedEntry_887_1 →+*
      Hex.GFq 887 3 Hex.Conway.supportedEntry_887_3 :=
  conwayEmbed 887 1 3 _ _ Hex.Conway.compat_887_1_3

/-- The canonical embedding of GF(907^1) into GF(907^2). -/
noncomputable def embed_907_1_2 :
    Hex.GFq 907 1 Hex.Conway.supportedEntry_907_1 →+*
      Hex.GFq 907 2 Hex.Conway.supportedEntry_907_2 :=
  conwayEmbed 907 1 2 _ _ Hex.Conway.compat_907_1_2

/-- The canonical embedding of GF(907^1) into GF(907^3). -/
noncomputable def embed_907_1_3 :
    Hex.GFq 907 1 Hex.Conway.supportedEntry_907_1 →+*
      Hex.GFq 907 3 Hex.Conway.supportedEntry_907_3 :=
  conwayEmbed 907 1 3 _ _ Hex.Conway.compat_907_1_3

/-- The canonical embedding of GF(911^1) into GF(911^2). -/
noncomputable def embed_911_1_2 :
    Hex.GFq 911 1 Hex.Conway.supportedEntry_911_1 →+*
      Hex.GFq 911 2 Hex.Conway.supportedEntry_911_2 :=
  conwayEmbed 911 1 2 _ _ Hex.Conway.compat_911_1_2

/-- The canonical embedding of GF(911^1) into GF(911^3). -/
noncomputable def embed_911_1_3 :
    Hex.GFq 911 1 Hex.Conway.supportedEntry_911_1 →+*
      Hex.GFq 911 3 Hex.Conway.supportedEntry_911_3 :=
  conwayEmbed 911 1 3 _ _ Hex.Conway.compat_911_1_3

/-- The canonical embedding of GF(919^1) into GF(919^2). -/
noncomputable def embed_919_1_2 :
    Hex.GFq 919 1 Hex.Conway.supportedEntry_919_1 →+*
      Hex.GFq 919 2 Hex.Conway.supportedEntry_919_2 :=
  conwayEmbed 919 1 2 _ _ Hex.Conway.compat_919_1_2

/-- The canonical embedding of GF(919^1) into GF(919^3). -/
noncomputable def embed_919_1_3 :
    Hex.GFq 919 1 Hex.Conway.supportedEntry_919_1 →+*
      Hex.GFq 919 3 Hex.Conway.supportedEntry_919_3 :=
  conwayEmbed 919 1 3 _ _ Hex.Conway.compat_919_1_3

/-- The canonical embedding of GF(929^1) into GF(929^2). -/
noncomputable def embed_929_1_2 :
    Hex.GFq 929 1 Hex.Conway.supportedEntry_929_1 →+*
      Hex.GFq 929 2 Hex.Conway.supportedEntry_929_2 :=
  conwayEmbed 929 1 2 _ _ Hex.Conway.compat_929_1_2

/-- The canonical embedding of GF(929^1) into GF(929^3). -/
noncomputable def embed_929_1_3 :
    Hex.GFq 929 1 Hex.Conway.supportedEntry_929_1 →+*
      Hex.GFq 929 3 Hex.Conway.supportedEntry_929_3 :=
  conwayEmbed 929 1 3 _ _ Hex.Conway.compat_929_1_3

/-- The canonical embedding of GF(937^1) into GF(937^2). -/
noncomputable def embed_937_1_2 :
    Hex.GFq 937 1 Hex.Conway.supportedEntry_937_1 →+*
      Hex.GFq 937 2 Hex.Conway.supportedEntry_937_2 :=
  conwayEmbed 937 1 2 _ _ Hex.Conway.compat_937_1_2

/-- The canonical embedding of GF(937^1) into GF(937^3). -/
noncomputable def embed_937_1_3 :
    Hex.GFq 937 1 Hex.Conway.supportedEntry_937_1 →+*
      Hex.GFq 937 3 Hex.Conway.supportedEntry_937_3 :=
  conwayEmbed 937 1 3 _ _ Hex.Conway.compat_937_1_3

/-- The canonical embedding of GF(941^1) into GF(941^2). -/
noncomputable def embed_941_1_2 :
    Hex.GFq 941 1 Hex.Conway.supportedEntry_941_1 →+*
      Hex.GFq 941 2 Hex.Conway.supportedEntry_941_2 :=
  conwayEmbed 941 1 2 _ _ Hex.Conway.compat_941_1_2

/-- The canonical embedding of GF(941^1) into GF(941^3). -/
noncomputable def embed_941_1_3 :
    Hex.GFq 941 1 Hex.Conway.supportedEntry_941_1 →+*
      Hex.GFq 941 3 Hex.Conway.supportedEntry_941_3 :=
  conwayEmbed 941 1 3 _ _ Hex.Conway.compat_941_1_3

/-- The canonical embedding of GF(947^1) into GF(947^2). -/
noncomputable def embed_947_1_2 :
    Hex.GFq 947 1 Hex.Conway.supportedEntry_947_1 →+*
      Hex.GFq 947 2 Hex.Conway.supportedEntry_947_2 :=
  conwayEmbed 947 1 2 _ _ Hex.Conway.compat_947_1_2

/-- The canonical embedding of GF(947^1) into GF(947^3). -/
noncomputable def embed_947_1_3 :
    Hex.GFq 947 1 Hex.Conway.supportedEntry_947_1 →+*
      Hex.GFq 947 3 Hex.Conway.supportedEntry_947_3 :=
  conwayEmbed 947 1 3 _ _ Hex.Conway.compat_947_1_3

/-- The canonical embedding of GF(953^1) into GF(953^2). -/
noncomputable def embed_953_1_2 :
    Hex.GFq 953 1 Hex.Conway.supportedEntry_953_1 →+*
      Hex.GFq 953 2 Hex.Conway.supportedEntry_953_2 :=
  conwayEmbed 953 1 2 _ _ Hex.Conway.compat_953_1_2

/-- The canonical embedding of GF(953^1) into GF(953^3). -/
noncomputable def embed_953_1_3 :
    Hex.GFq 953 1 Hex.Conway.supportedEntry_953_1 →+*
      Hex.GFq 953 3 Hex.Conway.supportedEntry_953_3 :=
  conwayEmbed 953 1 3 _ _ Hex.Conway.compat_953_1_3

/-- The canonical embedding of GF(967^1) into GF(967^2). -/
noncomputable def embed_967_1_2 :
    Hex.GFq 967 1 Hex.Conway.supportedEntry_967_1 →+*
      Hex.GFq 967 2 Hex.Conway.supportedEntry_967_2 :=
  conwayEmbed 967 1 2 _ _ Hex.Conway.compat_967_1_2

/-- The canonical embedding of GF(967^1) into GF(967^3). -/
noncomputable def embed_967_1_3 :
    Hex.GFq 967 1 Hex.Conway.supportedEntry_967_1 →+*
      Hex.GFq 967 3 Hex.Conway.supportedEntry_967_3 :=
  conwayEmbed 967 1 3 _ _ Hex.Conway.compat_967_1_3

end HexGFqMathlib.Conway

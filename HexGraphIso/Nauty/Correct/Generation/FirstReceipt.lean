/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Canon
public import HexGraphIso.Nauty.Correct.Generation.Return
public import HexGraphIso.Nauty.Correct.Generation.Receipt

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k} {ctx : Ctx n}

/-- A reference return to a first-path receiver discharges the visited
vertex's full orbit obligation. The canonical source is an earlier child;
the trace's fixed-base premise is supplied by the receiver's stabilization
invariant, rather than by an assumption about arbitrary off-path traces. -/
theorem Cover.receipt {base : List (Fin n)} {guide tv : Fin n}
    {tcell : VSet n} {cursor : Option Nat}
    {tcLevel specFuel level numcells tc len : Nat} {codes bs fs : List Nat}
    {rsLab rsPtn : Array Nat} {entry parent child out : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (h : Cover G base guide tcell cursor)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor entry parent best trail)
    (hnext : tcell.nextElem cursor = some tv.val)
    (hpast : CanonPast level tc cursor parent)
    (hgca : child.gcaCanon = parent.gcaCanon) (hlab : child.canonlab = parent.canonlab)
    (hguide : GuideRel (level + 1) child out)
    (hreceipt : RefReturn ctx out (Int.ofNat level))
    (htrace : ∀ γ ∈ out.genTrace, γ ∈ Aut.trace G)
    (hfix : ∀ γ ∈ out.genTrace, ∀ b ∈ base, γ[b.val]! = b.val)
    (hfirst : out.firstlab[tc]! = guide.val) (hcurrent : out.lab[tc]! = tv.val)
    (hcoset : out.cosetindex = tv.val) : Cover G base guide tcell (some tv.val) := by
  have hlen := hinv.lenTwo
  have hrange := hinv.range
  have hpos : tc < n := by omega
  cases hreceipt with
  | first returned carrier =>
    exact h.reference hnext (fun _ => Aut.Carries.refl G base guide) carrier htrace hfix hpos hfirst hcurrent
  | canon returned carrier =>
    have hat : level = out.gcaCanon := Int.ofNat_inj.mp returned
    obtain ⟨o, ho, hatRef, hearlier, _⟩ := hpast.locate hnext hinv.refs hgca hlab hguide hat.symm
    let u : Fin n := ⟨rsLab[tc + o]!, hinv.frozenLabOk _ (by rw [hinv.frozenLabSize]; omega)⟩
    exact h.reference (u := u) hnext (fun hu => h.before hnext hu hearlier)
      carrier htrace hfix hpos hatRef hcurrent
  | orbit returned payload =>
    apply h.orbitSkip hnext payload.sound
      (fun γ hγ => htrace γ (by simpa using hγ))
      (fun γ hγ => hfix γ (by simpa using hγ))
    have hlt := payload.smaller
    rw [hcoset] at hlt
    omega

end Hex.GraphIso.Nauty.Generation

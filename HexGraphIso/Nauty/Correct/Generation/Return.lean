/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Sweep.Node

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

/-- The automorphism evidence needed by a receiving sweep. Direct
returns identify their stored reference; the special orbit return retains
the pointer justified by the emitted trace. -/
inductive RefReturn (ctx : Ctx n) (out : SearchSt n) (r : Int) : Prop where
  | first (returned : r = Int.ofNat out.gcaFirst)
      (carrier : LabelCarrier ctx out.firstlab out.lab out.genTrace)
  | canon (returned : r = Int.ofNat out.gcaCanon)
      (carrier : LabelCarrier ctx out.canonlab out.lab out.genTrace)
  | orbit (returned : r = Int.ofNat out.gcaFirst)
      (payload : OrbitUnwind ctx out.gcaFirst out)

/-- The first-guide bounds on unwinds, together with the return control,
identify the exact guide for every kind of automorphism evidence. -/
theorem RefReturn.ofUnwind {ctx : Ctx n} {tcLevel target : Nat}
    {out : SearchSt n} {best : Option (Key n)} {r : Int}
    (h : Unwind ctx tcLevel target out best) (hr : r = Int.ofNat target)
    (horder : out.gcaFirst ≤ out.gcaCanon)
    (hcontrol : target = out.gcaFirst ∨ target = out.gcaCanon) :
    RefReturn ctx out r := by
  cases h with
  | first anchor carrier atFirst =>
    have he : target = out.gcaFirst := by rcases hcontrol with h | h <;> omega
    exact .first (hr.trans (congrArg Int.ofNat he)) carrier
  | canon anchor carrier atCanon =>
    exact .canon (hr.trans (congrArg Int.ofNat atCanon)) carrier
  | orbit payload =>
    have hb := payload.bound
    have he : target = out.gcaFirst := by rcases hcontrol with h | h <;> omega
    subst target
    exact .orbit hr payload

/-- Above both saved pruning boundaries, an early child return must
carry automorphism evidence. Ordinary completion, comparison pruning,
and a cheap-cell jump cannot cross this receiving level. -/
theorem RefReturn.ofEarly {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat}
    {codes : List Nat} {st out : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : NodeExit ctx tcLevel specFuel runFuel (level + 1) codes st out numcells
      best outBest trail r)
    (hfuel : runFuel ≠ 0) (hr : r < Int.ofNat level)
    (hcheap : level < out.noncheaplevel) (hsame : level < out.allsamelevel)
    (horder : out.gcaFirst ≤ out.gcaCanon) : RefReturn ctx out r := by
  cases h with
  | done returned exact =>
    simp only [Int.ofNat_eq_natCast] at returned hr
    omega
  | unwind target returned below sound payload located control =>
    exact .ofUnwind payload returned horder control
  | frozen below exact freeze =>
    cases freeze with
    | mk current cs bs codeInv depth stemEq installed incumbent floor boundary =>
      simp only [Int.ofNat_eq_natCast] at *
      rcases boundary with h | h <;> omega
  | cheap boundary returned positive atOrAbove saved exact =>
    simp only [Int.ofNat_eq_natCast] at returned hr
    omega
  | exhausted returned state incumbent emptyFuel => exact (hfuel emptyFuel).elim

/-- An off-path child's saved cheap boundary stays below no new ancestor. -/
theorem _root_.Hex.GraphIso.Nauty.OtherKeep.above {ctx : Ctx n} {level : Nat} {st out : SearchSt n}
    (h : Nauty.OtherKeep ctx (level + 1) st out) (hb : level < st.noncheaplevel) :
    level < out.noncheaplevel := by
  by_cases hn : level < out.noncheaplevel
  · exact hn
  · have he := h.boundary (by omega)
    omega

/-- At a first-path receiver, every reference return is exactly to
that receiver: both stored guides are at least its level. -/
theorem RefReturn.atGuide {ctx : Ctx n} {out : SearchSt n} {r : Int} {level : Nat}
    (h : RefReturn ctx out r) (hfirst : out.gcaFirst = level)
    (horder : out.gcaFirst ≤ out.gcaCanon) (hbelow : r < Int.ofNat (level + 1)) :
    r = Int.ofNat level := by
  cases h with
  | first returned carrier => rw [returned, hfirst]
  | orbit returned payload => rw [returned, hfirst]
  | canon returned carrier =>
    rw [hfirst] at horder
    simp only [returned, Int.ofNat_eq_natCast] at hbelow ⊢
    omega

/-- Removing the visited singleton from the fixed-point set preserves
all returned automorphism evidence. -/
theorem RefReturn.setFixed {ctx : Ctx n} {out : SearchSt n} {r : Int}
    (h : RefReturn ctx out r) (fixedpts : VSet n) :
    RefReturn ctx { out with fixedpts := fixedpts } r := by
  cases h with
  | first returned carrier => exact .first returned carrier
  | canon returned carrier => exact .canon returned carrier
  | orbit returned payload =>
    exact .orbit returned ⟨payload.positive, payload.bound, payload.currentLt,
      payload.smaller, payload.sound⟩

end Hex.GraphIso.Nauty.Generation

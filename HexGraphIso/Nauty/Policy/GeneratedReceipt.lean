/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.GeneratedCover
public import HexGraphIso.Nauty.Policy.ReferenceSweep
import all HexGraphIso.Nauty.Policy.GeneratedCover
import all HexGraphIso.Nauty.Policy.GeneratedTrace
import all HexGraphIso.Nauty.Policy.ReferenceSweep
import all HexGraphIso.Nauty.Policy.ReferenceReturn
import all HexGraphIso.Nauty.Policy.Orbits
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Orbit
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Generation

variable {n k : Nat} {G : Colored n k} {gs : List (Perm n)} {base : List (Fin n)}

/-- A recorded scatter consumes the current child when its reference's
orbit obligation was already discharged. -/
theorem Cover.reference {guide tv u : Fin n} {cell : VSet n} {previous : Option Nat}
    (h : Cover G gs base guide cell previous)
    (hnext : cell.nextElem previous = some tv.val)
    (href : Aut.Orbit G base guide u → Carries G gs base u guide)
    {ctx : Ctx n} {ref cur : Array Nat} {store : Array (Array Nat)} {pos : Nat}
    (hcarrier : LabelCarrier ctx ref cur store) (htrace : Realizes G gs store.toList)
    (hfix : ∀ γ ∈ store, ∀ b ∈ base, γ[b.val]! = b.val)
    (hpos : pos < n) (hatRef : ref[pos]! = u.val) (hatCur : cur[pos]! = tv.val) :
    Cover G gs base guide cell (some tv.val) := by
  have hc := (carries_label hcarrier htrace hfix hpos hatRef hatCur).symm
  exact h.advance hnext fun ho => hc.trans (href (ho.trans hc.orbit))

/-- All three reference-return alternatives discharge the actual first
sweep's current orbit obligation in the supplied final generated group. -/
theorem Cover.receipt {ctx : Ctx n} {tcLevel fuel cfuel level numcells tc tv1 index : Nat}
    {guide tv : Fin n} {cell : VSet n} {previous : Option Nat} {short : Bool}
    {st out : Search n} {l : Max.Loop n} {bs fs : List Nat} {parents : Max.Parents n}
    (h : Cover G gs base guide cell previous)
    (hs : Max.SweepInput G ctx tcLevel fuel cfuel true level numcells tc tv1 (some tv.val)
      cell index st l bs fs parents)
    (hnext : cell.nextElem previous = some tv.val)
    (hpast : Nauty.Generation.CanonPast level tc previous st.view)
    (hcall : node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child true level tc tv.val st) = (.unwind level short, out))
    (hreceipt : RefReturn ctx level out) (horbits : OrbitsOk out)
    (htrace : Realizes G gs out.genTrace.toList)
    (hfix : ∀ γ ∈ out.genTrace, ∀ b ∈ base, γ[b.val]! = b.val)
    (hfirst : out.firstlab[tc]! = guide.val) (hcoset : out.cosetindex = tv.val) :
    Cover G gs base guide cell (some tv.val) := by
  have hpos : tc < n := by have := hs.range; have := hs.len; omega
  have hcurrent := hs.return_chosen (childFirst := false)
  rw [hcall] at hcurrent
  cases hreceipt with
  | first returned carrier =>
    exact h.reference hnext (fun _ => Carries.refl G gs base guide) carrier htrace hfix hpos hfirst hcurrent
  | canon returned carrier =>
    have he := hs.canon_earlier (childFirst := false) hpast hnext
    rw [hcall] at he
    obtain ⟨o, ho, hat, hbefore, _⟩ := he returned.symm
    let u : Fin n := ⟨(l.prepare ctx tcLevel).2.2.2.2.lab[tc + o]!,
      (labOk_of_reach hs.base.labSize hs.base.reach) _ (by rw [hs.base.labSize]; have := hs.range; omega)⟩
    exact h.reference (u := u) hnext (fun hu => h.before hnext hu hbefore)
      carrier htrace hfix hpos hat hcurrent
  | orbit returned smaller =>
    apply h.orbitSkip hnext horbits htrace (fun γ hγ => hfix γ (by simpa using hγ))
    rw [hcoset] at smaller
    omega

end Hex.GraphIso.Nauty.Engine.Generation

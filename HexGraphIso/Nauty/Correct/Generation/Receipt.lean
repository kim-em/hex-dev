/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Sweep
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Orbits

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k} {base : List (Fin n)}

/-- A recorded reference-to-current leaf carrier gives the corresponding
vertex carrier in the generated pointwise stabilizer. -/
theorem carries_label {ctx : Ctx n} {ref cur : Array Nat} {store : Array (Array Nat)}
    {pos : Nat} {u v : Fin n}
    (h : LabelCarrier ctx ref cur store)
    (htrace : ∀ γ ∈ store, γ ∈ Aut.trace G)
    (hfix : ∀ γ ∈ store, ∀ b ∈ base, γ[b.val]! = b.val)
    (hpos : pos < n) (href : ref[pos]! = u.val) (hcur : cur[pos]! = v.val) :
    Aut.Carries G base u v := by
  obtain ⟨γ, hmem, _, hmap⟩ := h
  apply carries_word (w := [γ])
  · intro δ hδ
    rw [List.mem_singleton.mp hδ]
    exact htrace γ hmem
  · intro δ hδ
    rw [List.mem_singleton.mp hδ]
    exact hfix γ hmem
  · simpa only [applyWord, List.foldl_cons, List.foldl_nil, href, hcur] using hmap pos hpos

namespace Cover

variable {guide : Fin n} {tcell : VSet n} {cursor : Option Nat}

/-- A direct first-reference or canonical-reference return consumes the
child when the reference's orbit obligation is already covered. This
uses the emitted carrier even when the orbit partition did not grow. -/
theorem reference (h : Cover G base guide tcell cursor) {tv u : Fin n}
    (hnext : tcell.nextElem cursor = some tv.val)
    (href : Aut.Orbit G base guide u → Aut.Carries G base u guide)
    {ctx : Ctx n} {ref cur : Array Nat} {store : Array (Array Nat)} {pos : Nat}
    (hcarrier : LabelCarrier ctx ref cur store)
    (htrace : ∀ γ ∈ store, γ ∈ Aut.trace G)
    (hfix : ∀ γ ∈ store, ∀ b ∈ base, γ[b.val]! = b.val)
    (hpos : pos < n) (hatRef : ref[pos]! = u.val) (hatCur : cur[pos]! = tv.val) :
    Cover G base guide tcell (some tv.val) := by
  have hc := (carries_label hcarrier htrace hfix hpos hatRef hatCur).symm
  exact h.advance hnext fun ho => hc.trans (href (ho.trans hc.orbit))

/-- The located generator receipt can be consumed without dropping its
carrier. The reference premises are conditional: a canonical reference
outside the guide's full orbit imposes no generation obligation. -/
theorem unwind (h : Cover G base guide tcell cursor) {tv : Fin n}
    (hnext : tcell.nextElem cursor = some tv.val)
    {ctx : Ctx n} {tcLevel level pos : Nat} {out : SearchSt n} {best : Option (Key n)}
    (payload : Unwind ctx tcLevel level out best)
    (htrace : ∀ γ ∈ out.genTrace, γ ∈ Aut.trace G)
    (hfix : ∀ γ ∈ out.genTrace, ∀ b ∈ base, γ[b.val]! = b.val)
    (hpos : pos < n) (hatCur : out.lab[pos]! = tv.val)
    (hfirstLt : out.firstlab[pos]! < n) (hcanonLt : out.canonlab[pos]! < n)
    (hfirst : Aut.Orbit G base guide ⟨out.firstlab[pos]!, hfirstLt⟩ →
      Aut.Carries G base ⟨out.firstlab[pos]!, hfirstLt⟩ guide)
    (hcanon : Aut.Orbit G base guide ⟨out.canonlab[pos]!, hcanonLt⟩ →
      Aut.Carries G base ⟨out.canonlab[pos]!, hcanonLt⟩ guide)
    (hcoset : out.cosetindex = tv.val) : Cover G base guide tcell (some tv.val) := by
  cases payload with
  | first anchor carrier atFirst =>
    exact h.reference hnext hfirst carrier htrace hfix hpos rfl hatCur
  | canon anchor carrier atCanon =>
    exact h.reference hnext hcanon carrier htrace hfix hpos rfl hatCur
  | orbit payload =>
    apply h.orbitSkip hnext payload.sound
      (fun γ hγ => htrace γ (by simpa using hγ))
      (fun γ hγ => hfix γ (by simpa using hγ))
    have hlt := payload.smaller
    rw [hcoset] at hlt
    omega

/-- Generated descending carriers justify a short-prune filter without
requiring its fixed-point bitset to characterize the active base. -/
theorem shortCarriers (h : Cover G base guide tcell cursor) {st : SearchSt n}
    (hlast : ∀ fix mcr, st.autos.back? = some (fix, mcr) → ∀ v : Fin n,
      mcr.mem v.val = false → ∃ u : Fin n, u.val < v.val ∧ Aut.Carries G base v u) :
    Cover G base guide (Nauty.shortprune tcell st) cursor := by
  apply h.filterDesc _ (fun _ hm => shortprune_subset hm)
  intro v _ hm _
  cases hkeep : (Nauty.shortprune tcell st).mem v.val with
  | true => exact Or.inl rfl
  | false =>
    right
    rw [Nauty.shortprune] at hkeep
    split at hkeep
    · next fix mcr he =>
      rw [VSet.mem_inter, hm, Bool.true_and] at hkeep
      obtain ⟨u, hlt, hc⟩ := hlast fix mcr he v hkeep
      exact ⟨u, hc, hlt⟩
    · rw [hm] at hkeep
      cases hkeep

/-- The guiding child's short-prune request preserves generated orbit
coverage once its last ledger pair has generated carriers. -/
theorem shortprune (h : Cover G base guide tcell cursor) {st : SearchSt n}
    (hlast : ∀ fix mcr, st.autos.back? = some (fix, mcr) →
      PairGenerated G fix mcr ∧ ∀ b ∈ base, fix.mem b.val = true) :
    Cover G base guide (Nauty.shortprune tcell st) cursor := by
  apply h.shortCarriers
  intro fix mcr hback v hv
  obtain ⟨hpair, hbase⟩ := hlast fix mcr hback
  exact hpair.carries hbase hv

end Cover

end Hex.GraphIso.Nauty.Generation

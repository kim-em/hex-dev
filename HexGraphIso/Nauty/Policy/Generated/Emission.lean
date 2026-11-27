/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Emission
public import HexGraphIso.Nauty.Policy.Generated.Trace
public import HexGraphIso.Nauty.Invariant.OrbitComplete
import all HexGraphIso.Generated
import all HexGraphIso.Nauty.Invariant.OrbitComplete
import all HexGraphIso.Nauty.Policy.Generated.Trace

public section

namespace Hex.GraphIso.Nauty.Emission

open Generation

variable {n k : Nat} {G : Colored n k} {gs : List (Perm n)}

/-- The stored representatives are flat and justified by the discovery
trace, with the exact root count used to decide a code-two emission. -/
structure Orbits (n : Nat) (l : Log) : Prop where
  sound : OrbSound (OrbConn l.trace.toList n) l.orbits n
  flat : Orbit.Flat l.orbits n
  count : l.numorbits = (List.range n).countP (fun i => l.orbits[i]! == i)

theorem Realizes.bounds {store : List (Array Nat)} (h : Realizes G gs store) :
    ∀ γ ∈ store, ∀ v, v < n → γ[v]! < n := by
  intro γ hγ v hv
  obtain ⟨p, _, _, hval⟩ := h γ hγ
  rw [← hval ⟨v, hv⟩]
  exact (p.get ⟨v, hv⟩).isLt

theorem Realizes.injective {store : List (Array Nat)} (h : Realizes G gs store) :
    ∀ γ ∈ store, ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b := by
  intro γ hγ a b ha hb he
  obtain ⟨p, _, _, hval⟩ := h γ hγ
  rw [← hval ⟨a, ha⟩, ← hval ⟨b, hb⟩] at he
  exact congrArg Fin.val (p.get_inj (Fin.ext he))

theorem Orbits.join {l : Log} {γ : Array Nat} (h : Orbits n l)
    (ht : Realizes G gs (l.trace.push γ).toList) : Orbits n (l.join γ n) := by
  have hb := Realizes.bounds ht
  have hd := Orbit.Descending.ofSound h.sound
  have hm := hb γ (by simp)
  refine ⟨?_, Orbit.flat_orbjoin hd hm, Orbit.count_orbjoin hd hm⟩
  apply orbjoin_orbConn hb (Realizes.injective ht) (by simp)
  exact orbSound_orbConn_mono (fun δ hδ => by simp [hδ]) h.sound

/-- In a first-path sibling sweep, the completed first child supplies the
point stabilizer. An admission with no orbit merge belongs to the group
already generated in that sweep. -/
theorem suppressed_generated {l : Log} {γ : Array Nat} {p : Perm n}
    {guide : Fin n} {base : List (Fin n)} (ho : Orbits n l)
    (ht : Realizes G gs l.trace.toList)
    (hfix : ∀ δ ∈ l.trace.toList, ∀ b ∈ base, δ[b.val]! = b.val)
    (hp : IsIso G G p) (hbase : Perm.Fixes base p)
    (hval : ∀ v : Fin n, (p.get v).val = γ[v.val]!)
    (hstab : ∀ q, IsIso G G q → Perm.Fixes (guide :: base) q → Perm.Generated gs q)
    (hc : (l.join γ n).numorbits = l.numorbits) : Perm.Generated gs p := by
  have hb (v : Nat) (hv : v < n) : γ[v]! < n := by
    rw [← hval ⟨v, hv⟩]
    exact (p.get ⟨v, hv⟩).isLt
  have hd := Orbit.Descending.ofSound ho.sound
  have he : (orbjoin l.orbits γ n).1 = l.orbits :=
    Orbit.orbjoin_eq_of_count hd ho.flat hb (hc.trans ho.count)
  have hs : Orbit.Stable (orbjoin l.orbits γ n).1 n (fun v => l.orbits[v]!) := by
    rw [he]
    exact ho.flat
  have ha := (Orbit.stable_orbjoin hd hb hs).2 guide.val guide.isLt
  rw [← hval guide] at ha
  obtain ⟨u, hu, _, hgu⟩ := carries_pointer (v := guide) ho.sound ht hfix
  obtain ⟨v, hv, _, hpv⟩ := carries_pointer (v := p.get guide) ho.sound ht hfix
  have huv : u = v := Fin.ext (hu.trans (ha.symm.trans hv.symm))
  subst v
  obtain ⟨q, hq, hqiso, hqfix, hqval⟩ := hgu.trans hpv.symm
  have hrest : Perm.Fixes (guide :: base) (q.inv.comp p) := by
    refine Perm.Fixes.cons.mpr ⟨?_, hqfix.inv.comp hbase⟩
    rw [Perm.get_comp, ← hqval, Perm.inv_get_get]
  have hword := hstab (q.inv.comp p) (hp.trans hqiso.symm) hrest
  simpa [← Perm.comp_assoc] using hq.comp hword

/-- The discovery trace is represented in a containing emitted group. -/
structure Realization (G : Colored n k) (gs : List (Perm n)) (l : Log) : Prop where
  orbits : Orbits n l
  trace : Realizes G gs l.trace.toList

/-- The initial search has no discoveries, and each vertex is its own representative. -/
theorem Realization.initial :
    Realization G gs ⟨#[], #[], Array.ofFn (n := n) Fin.val, n, 0⟩ := by
  have hget (v : Nat) (hv : v < n) : (Array.ofFn (n := n) Fin.val)[v]! = v := by
    rw [getElem!_pos _ _ (by simpa using hv), Array.getElem_ofFn]
  refine ⟨⟨orbSound_orbConn_init [], ?_, ?_⟩, ?_⟩
  · intro v hv
    dsimp only
    rw [hget v hv, hget v hv]
  · change n = (List.range n).countP (fun v => (Array.ofFn (n := n) Fin.val)[v]! == v)
    rw [List.countP_eq_length.mpr (fun v hv => by rw [hget v (List.mem_range.mp hv)]; simp),
      List.length_range]
  · intro p hp
    simp at hp

/-- A local traversal invariant with the completed call's trace as a bound.
Using the containing trace supplies validity and base stabilization at the
point of admission without rechecking the graph in the search. -/
@[expose] def Within (G : Colored n k) (gs : List (Perm n))
    (source reported : List (Array Nat)) (l : Log) : Prop :=
  List.Subset l.trace.toList source →
  List.Subset l.emitted.toList reported →
  Realization G gs l

private theorem Realization.join {l : Log} {γ : Array Nat} (h : Realization G gs l)
    (hγ : Realizes G gs [γ]) : Realization G gs (l.join γ n) := by
  have ht : Realizes G gs (l.trace.push γ).toList := by
    intro δ hd
    rw [Array.toList_push, List.mem_append] at hd
    exact hd.elim (h.trace δ) (hγ δ)
  exact ⟨h.orbits.join ht, ht⟩

private theorem Realization.emit {l : Log} (h : Realization G gs l) (γ : Array Nat) :
    Realization G gs (l.emit γ) :=
  ⟨⟨h.orbits.sound, h.orbits.flat, h.orbits.count⟩, h.trace⟩

/-- Within the remaining siblings of a first-path call, every leaf action
preserves realization by the containing emitted generators. -/
theorem within_leaf {κ : Type} {whole : List (Perm n)} {source reported : List (Array Nat)}
    {base : List (Fin n)} {guide : Fin n}
    (hsource : Realizes G whole source)
    (hfix : ∀ γ ∈ source, ∀ b ∈ base, γ[b.val]! = b.val)
    (hemit : Realizes G gs reported)
    (hstab : ∀ q, IsIso G G q → Perm.Fixes (guide :: base) q → Perm.Generated gs q)
    (leaf : Leaf) (level : Nat) (st : SearchState n κ)
    (h : Within G gs source reported (log st)) :
    Within G gs source reported (log (leafExit leaf level st).2) := by
  rw [leaf_log]
  let l := log st
  let γ := st.workperm
  have hj : List.Subset l.trace.toList (l.join γ n).trace.toList := by
    intro δ hd
    simp [Log.join, hd]
  have hex : γ ∈ (l.join γ n).trace.toList := by simp [Log.join]
  have report : Within G gs source reported ((l.join γ n).emit γ) := by
    intro hs he
    have hold := h (fun δ hd => hs (hj hd)) (fun δ hd => he (by
      change δ ∈ l.emitted.toList at hd
      simpa only [Log.emit, Log.join, Array.toList_push, List.mem_append]
        using (show δ ∈ l.emitted.toList ∨ δ ∈ [γ] from .inl hd)))
    have hγ := hemit γ (he (by simp [Log.emit, Log.join]))
    apply Realization.emit _ γ
    apply hold.join
    intro δ hd
    obtain rfl := List.mem_singleton.mp hd
    exact hγ
  cases leaf
  all_goals try first | exact h | exact report
  change Within G gs source reported
    (if (l.join γ n).numorbits == l.numorbits then l.join γ n else (l.join γ n).emit γ)
  split
  · rename_i hc
    intro hs he
    have hold := h (fun δ hd => hs (hj hd)) he
    have hγ := hs hex
    obtain ⟨p, _, hp, hval⟩ := hsource γ hγ
    have hbase : Perm.Fixes base p := fun b hb => Fin.ext ((hval b).trans (hfix γ hγ b hb))
    have hword := suppressed_generated (guide := guide) hold.orbits hold.trace
      (fun δ hd => hfix δ (hs (hj hd))) hp hbase hval hstab (beq_iff_eq.mp hc)
    apply hold.join
    intro δ hd
    obtain rfl := List.mem_singleton.mp hd
    exact ⟨p, hword, hp, hval⟩
  · exact report

end Hex.GraphIso.Nauty.Emission

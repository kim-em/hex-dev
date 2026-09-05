/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Ops
public import HexGraphIso.Nauty.OrbJoin
import all HexGraphIso.Nauty.OrbJoin

public section

/-!
Automorphism generators, vertex orbits and the group order.

The pinned nauty traversal discovers automorphisms as it runs: each
one is a `workperm` recorded at a code-1 or code-2 leaf, in discovery
order, and the same permutations drive the search's own orbit pruning.
`Aut.trace` is that list, transcribed; because the transcription
replays nauty's traversal exactly, the list is deterministic and
conformance-pinnable, not merely the group it generates.

Nothing from the search is believed. Each raw array passes through
`autom?`, which rebuilds it as a `Perm n` and runs the same
`checkIso` the isomorphism surface uses, so `autos_isIso` reads the
membership guarantee straight off the check rather than off the
producer. This is the library's usual producer/checker split, with
`checkIso` as the sole trusted step.

The orbit array replays nauty's `orbjoin` over the checked
generators, which is exactly what the search does with them, so it is
the array nauty reports. `sameOrbit_of_orbits_eq` is its guarantee:
vertices sharing an orbit representative really are carried onto each
other by an automorphism. The converse — that the generators generate
the whole group, so that distinct representatives really are distinct
orbits — is the counting argument, and is not yet proved here.

`Aut.order` is the orbit-stabilizer chain: individualize a vertex of
a non-singleton orbit, recurse on the stabilizer (the search on the
individualized colouring computes it, since a vertex alone in its
cell is fixed by every colour-preserving automorphism), and multiply
the orbit lengths. It is exact whenever the orbit array is the true
orbit partition, and it is pinned against nauty's `grpsize` by
conformance.
-/

namespace Hex.GraphIso

variable {n k : Nat}

/-! # Orbits of the automorphism group -/

/-- Two vertices lie in one orbit of the automorphism group: some
automorphism of `G` carries `u` to `v`. -/
def SameOrbit (G : Colored n k) (u v : Fin n) : Prop :=
  ∃ p, IsIso G G p ∧ p.get u = v

theorem SameOrbit.intro {G : Colored n k} {u v : Fin n} (p : Perm n)
    (hp : IsIso G G p) (h : p.get u = v) : SameOrbit G u v :=
  ⟨p, hp, h⟩

theorem SameOrbit.elim {G : Colored n k} {u v : Fin n} (h : SameOrbit G u v) :
    ∃ p, IsIso G G p ∧ p.get u = v :=
  h

namespace SameOrbit

theorem refl (G : Colored n k) (u : Fin n) : SameOrbit G u u :=
  ⟨Perm.id n, IsIso.refl G, Perm.get_id u⟩

theorem symm {G : Colored n k} {u v : Fin n} (h : SameOrbit G u v) :
    SameOrbit G v u := by
  rcases h with ⟨p, hp, hu⟩
  exact ⟨p.inv, hp.symm, by rw [← hu, Perm.inv_get_get]⟩

theorem trans {G : Colored n k} {u v w : Fin n} (h₁ : SameOrbit G u v)
    (h₂ : SameOrbit G v w) : SameOrbit G u w := by
  rcases h₁ with ⟨p, hp, hu⟩
  rcases h₂ with ⟨q, hq, hv⟩
  exact ⟨q.comp p, hp.trans hq, by rw [Perm.get_comp, hu, hv]⟩

end SameOrbit

/-! # The checked generator list -/

/-- The entries of a checked raw permutation array. -/
theorem Perm.val_get_of_ofNatArray? {a : Array Nat} {p : Perm n}
    (h : Perm.ofNatArray? n a = some p) (i : Fin n) :
    (p.get i).val = a[i.val]! := by
  rw [Perm.ofNatArray?] at h
  split at h
  · rename_i hc
    have hsz : i.val < a.size := hc.1.symm ▸ i.isLt
    rw [Perm.get, Perm.vec_of_ofVector? h]
    rw [getElem!_pos a i.val hsz]
    simp
  · simp at h

/-- Accept one raw generator array from the traversal: rebuild it as a
permutation of `Fin n` and check that it is an automorphism. This is
the only place a generator is believed, and it believes only
`checkIso`. -/
@[expose] def autom? (G : Colored n k) (γ : Array Nat) : Option (Perm n) :=
  match Perm.ofNatArray? n γ with
  | some p => if checkIso G G p then some p else none
  | none => none

theorem autom?_isIso {G : Colored n k} {γ : Array Nat} {p : Perm n}
    (h : autom? G γ = some p) : IsIso G G p := by
  rw [autom?] at h
  split at h
  · split at h
    · rename_i hchk
      rw [← Option.some.inj h]
      exact (checkIso_iff G G _).mp hchk
    · simp at h
  · simp at h

theorem autom?_val_get {G : Colored n k} {γ : Array Nat} {p : Perm n}
    (h : autom? G γ = some p) (i : Fin n) : (p.get i).val = γ[i.val]! := by
  rw [autom?] at h
  split at h
  · rename_i q hq
    split at h
    · rw [← Option.some.inj h]
      exact Perm.val_get_of_ofNatArray? hq i
    · simp at h
  · simp at h

namespace Aut

/-- The raw generator arrays the pinned traversal records, in
discovery order. -/
@[expose] def trace (G : Colored n k) : List (Array Nat) :=
  (Nauty.runColoredTraced G).autos.toList

/-- The generators: the recorded traversal automorphisms that pass the
check, in discovery order. -/
@[expose] def gens (G : Colored n k) : List (Perm n) :=
  (trace G).filterMap (autom? G)

/-- The raw arrays behind `gens`, kept because nauty's orbit
bookkeeping is stated on them. -/
@[expose] def raw (G : Colored n k) : List (Array Nat) :=
  (trace G).filter fun γ => (autom? G γ).isSome

theorem exists_perm_of_mem_raw {G : Colored n k} {γ : Array Nat}
    (h : γ ∈ raw G) :
    ∃ p, IsIso G G p ∧ ∀ i : Fin n, (p.get i).val = γ[i.val]! := by
  rw [raw, List.mem_filter] at h
  rcases hp : autom? G γ with _ | p
  · rw [hp] at h; simp at h
  · exact ⟨p, autom?_isIso hp, fun i => autom?_val_get hp i⟩

theorem lt_of_mem_raw {G : Colored n k} {γ : Array Nat} (h : γ ∈ raw G)
    (v : Nat) (hv : v < n) : γ[v]! < n := by
  rcases exists_perm_of_mem_raw h with ⟨p, -, hval⟩
  rw [← hval ⟨v, hv⟩]
  exact (p.get ⟨v, hv⟩).isLt

theorem inj_of_mem_raw {G : Colored n k} {γ : Array Nat} (h : γ ∈ raw G) :
    ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b := by
  rcases exists_perm_of_mem_raw h with ⟨p, -, hval⟩
  intro a b ha hb hab
  rw [← hval ⟨a, ha⟩, ← hval ⟨b, hb⟩] at hab
  exact congrArg Fin.val (p.get_inj (Fin.ext hab))

/-! # The orbit array -/

/-- nauty's vertex orbits: `orbjoin` folded over the checked
generators, the same computation the search performs on them. Every
entry is the representative of its orbit. -/
@[expose] def orbits (G : Colored n k) : Array Nat :=
  (raw G).foldl (fun o γ => (Nauty.orbjoin o γ n).1)
    (Array.ofFn (n := n) fun i => i.val)

/-- The number of orbits: the vertices that represent themselves. -/
@[expose] def numOrbits (G : Colored n k) : Nat :=
  ((List.range n).filter fun v => (orbits G)[v]! == v).length

/-- The size of the orbit of `v`. -/
@[expose] def orbitSize (G : Colored n k) (v : Nat) : Nat :=
  ((List.range n).filter fun u => (orbits G)[u]! == (orbits G)[v]!).length

private theorem orbSound_foldl {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < n → γ[v]! < n)
    (hinj : ∀ γ ∈ gens, ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b) :
    ∀ (l : List (Array Nat)), (∀ γ ∈ l, γ ∈ gens) → ∀ (o : Array Nat),
      Nauty.OrbSound (Nauty.OrbConn gens n) o n →
      Nauty.OrbSound (Nauty.OrbConn gens n)
        (l.foldl (fun o γ => (Nauty.orbjoin o γ n).1) o) n
  | [], _, o, ho => ho
  | γ :: l, hl, o, ho => by
    refine orbSound_foldl hb hinj l (fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)) _ ?_
    exact Nauty.orbjoin_orbConn hb hinj (hl γ (List.mem_cons_self ..)) ho

theorem orbSound (G : Colored n k) :
    Nauty.OrbSound (Nauty.OrbConn (raw G) n) (orbits G) n :=
  orbSound_foldl (fun _ h => lt_of_mem_raw h) (fun _ h => inj_of_mem_raw h)
    (raw G) (fun _ h => h) _ (Nauty.orbSound_orbConn_init _)

theorem size_orbits (G : Colored n k) : (orbits G).size = n :=
  And.left (orbSound G)

theorem orbits_lt (G : Colored n k) {v : Nat} (hv : v < n) :
    (orbits G)[v]! < n :=
  (Nauty.orbConn_of_ptr (orbSound G) hv).1

/-! # Orbit soundness -/

private theorem sameOrbit_applyWord {G : Colored n k} :
    ∀ (w : List (Array Nat)), (∀ γ ∈ w, γ ∈ raw G) → ∀ (v : Fin n),
      ∃ u : Fin n, u.val = Nauty.applyWord w v.val ∧ SameOrbit G v u
  | [], _, v => ⟨v, rfl, SameOrbit.refl G v⟩
  | γ :: w, hw, v => by
    rcases exists_perm_of_mem_raw (hw γ (List.mem_cons_self ..)) with ⟨p, hp, hval⟩
    rcases sameOrbit_applyWord w (fun δ hδ => hw δ (List.mem_cons_of_mem _ hδ))
        (p.get v) with ⟨u, hu, hsame⟩
    refine ⟨u, ?_, SameOrbit.trans ⟨p, hp, rfl⟩ hsame⟩
    rw [hu, hval v]
    rfl

/-- A vertex is carried onto its orbit representative by an
automorphism. -/
theorem sameOrbit_orbits (G : Colored n k) (v : Fin n) :
    SameOrbit G v ⟨(orbits G)[v.val]!, orbits_lt G v.isLt⟩ := by
  obtain ⟨w, hw, happ⟩ :
      ∃ w : List (Array Nat), (∀ γ ∈ w, γ ∈ raw G) ∧
        Nauty.applyWord w v.val = (orbits G)[v.val]! :=
    (Nauty.orbConn_of_ptr (orbSound G) v.isLt).2
  rcases sameOrbit_applyWord w hw v with ⟨u, hu, hsame⟩
  have : u = (⟨(orbits G)[v.val]!, orbits_lt G v.isLt⟩ : Fin n) :=
    Fin.ext (by rw [hu, happ])
  exact this ▸ hsame

/-- Soundness of the orbit array: vertices sharing a representative
really are in one orbit. -/
theorem sameOrbit_of_orbits_eq (G : Colored n k) (u v : Fin n)
    (h : (orbits G)[u.val]! = (orbits G)[v.val]!) : SameOrbit G u v := by
  refine SameOrbit.trans (sameOrbit_orbits G u) (SameOrbit.symm ?_)
  have := sameOrbit_orbits G v
  rw [show (⟨(orbits G)[v.val]!, orbits_lt G v.isLt⟩ : Fin n) =
      ⟨(orbits G)[u.val]!, orbits_lt G u.isLt⟩ from Fin.ext h.symm] at this
  exact this

/-! # The group order -/

/-- Give `v` a colour of its own, at the end of the colour order.
`none` when `v` is already alone in its cell, where the old colour
would be left unused. Every colour-preserving automorphism of the
result is an automorphism of `G` fixing `v`, so the search on it
computes the stabilizer. -/
@[expose] def indiv? (G : Colored n k) (v : Fin n) : Option (Colored n (k + 1)) :=
  (Coloring.ofVector? (Hex.Vector.ofFn' fun u : Fin n =>
      if u = v then (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))
      else ⟨(G.coloring.cells[u]).val,
        Nat.lt_succ_of_lt (G.coloring.cells[u]).isLt⟩)).map
    fun c => { graph := G.graph, coloring := c }

/-- The orbit-stabilizer chain: multiply the length of one
non-singleton orbit by the order of the stabilizer of a point in it,
individualizing that point to compute the stabilizer. -/
def orderAux (fuel : Nat) {n k : Nat} (G : Colored n k) : Nat :=
  match fuel with
  | 0 => 1
  | fuel + 1 =>
    match (List.finRange n).find? fun v => decide (1 < orbitSize G v.val) with
    | none => 1
    | some v =>
      match indiv? G v with
      | some G' => orbitSize G v.val * orderAux fuel G'
      | none => 1
termination_by fuel

/-- The order of the automorphism group of `G`. -/
@[expose] def order (G : Colored n k) : Nat := orderAux n G

end Aut

/-! # The automorphism surface -/

/-- The automorphism data of a coloured graph: the generators the
pinned traversal discovers, in discovery order, with the vertex
orbits, the orbit count and the group order nauty derives from
them. -/
structure AutResult (n : Nat) where
  /-- The generators, in the traversal's discovery order. -/
  gens : List (Perm n)
  /-- The orbit representative of each vertex. -/
  orbits : Array Nat
  /-- The number of orbits. -/
  numOrbits : Nat
  /-- The order of the automorphism group. -/
  order : Nat

/-- Generators of the automorphism group of a coloured graph, with the
vertex orbits, the orbit count and the group order. Every returned
permutation is an automorphism (`autos_isIso`); vertices sharing an
orbit representative are in one orbit (`autos_sameOrbit`). -/
@[expose] def autos (G : Colored n k) : AutResult n where
  gens := Aut.gens G
  orbits := Aut.orbits G
  numOrbits := Aut.numOrbits G
  order := Aut.order G

/-- Membership: every returned generator is an automorphism. -/
theorem autos_isIso {G : Colored n k} {p : Perm n}
    (h : p ∈ (autos G).gens) : IsIso G G p := by
  rw [autos, Aut.gens, List.mem_filterMap] at h
  rcases h with ⟨γ, -, hγ⟩
  exact autom?_isIso hγ

/-- A returned generator carries `G` onto itself. -/
theorem autos_isomorphic {G : Colored n k} {p : Perm n}
    (h : p ∈ (autos G).gens) : Isomorphic G G :=
  Isomorphic.intro p (autos_isIso h)

/-- The orbit array has one entry per vertex. -/
theorem size_autos_orbits (G : Colored n k) : (autos G).orbits.size = n :=
  Aut.size_orbits G

/-- Every orbit representative is a vertex. -/
theorem autos_orbits_lt (G : Colored n k) {v : Nat} (hv : v < n) :
    (autos G).orbits[v]! < n :=
  Aut.orbits_lt G hv

/-- Soundness of the orbits: vertices sharing a representative are
carried onto each other by an automorphism. -/
theorem autos_sameOrbit (G : Colored n k) (u v : Fin n)
    (h : (autos G).orbits[u.val]! = (autos G).orbits[v.val]!) :
    SameOrbit G u v :=
  Aut.sameOrbit_of_orbits_eq G u v h

end Hex.GraphIso

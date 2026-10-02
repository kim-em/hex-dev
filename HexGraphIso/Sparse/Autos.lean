/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.OrbitExact
public import HexGraphIso.Autos
import all HexGraphIso.Nauty.Sparse.GenerationTrace
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Sparse

variable {n k : Nat}

/-- The full native colour-preserving automorphism orbit relation. -/
def SameOrbit (G : Colored n k) (u v : Fin n) : Prop :=
  ∃ p, IsIso G G p ∧ p.get u = v

namespace Aut

/-- Decode the complete emitted trace of one native sparse traversal. -/
@[expose] def gens (G : Colored n k) : List (Perm n) := (Nauty.Sparse.runColored G).generators

/-- The least representatives stored by the native traversal. -/
@[expose] def orbits (G : Colored n k) : Array Nat := (Nauty.Sparse.runColored G).orbits

/-- The orbit count accumulated by the native joins. -/
@[expose] def numOrbits (G : Colored n k) : Nat := (Nauty.Sparse.runColored G).numorbits

/-- The product of first-path indices accumulated by the native search.
This projection performs one traversal and no individualized reruns. -/
@[expose] def order (G : Colored n k) : Nat := (Nauty.Sparse.runColored G).order

theorem gens_isIso {G : Colored n k} {p : Perm n} (hp : p ∈ gens G) : IsIso G G p :=
  (Nauty.Sparse.runColored_trace G).generator hp

theorem complete (G : Colored n k) {p : Perm n} (hp : IsIso G G p) :
    Perm.Generated (gens G) p := Nauty.Sparse.runColored_generates G hp

theorem generated_iff (G : Colored n k) (p : Perm n) :
    Perm.Generated (gens G) p ↔ IsIso G G p := Nauty.Sparse.generated_iff G p

theorem size_orbits (G : Colored n k) : (orbits G).size = n := (Nauty.Sparse.runColored_orbits G).1

theorem orbits_lt (G : Colored n k) {v : Nat} (hv : v < n) : (orbits G)[v]! < n :=
  Nat.lt_of_le_of_lt ((Nauty.Sparse.runColored_orbits G).2 v hv).1 hv

theorem orbits_flat (G : Colored n k) : Nauty.Orbit.Flat (orbits G) n := Nauty.Sparse.orbits_flat G

theorem sameOrbit_orbits (G : Colored n k) (v : Fin n) :
    SameOrbit G v ⟨(orbits G)[v.val]!, orbits_lt G v.isLt⟩ := by
  obtain ⟨p, hp, he⟩ := Nauty.Sparse.orbit_iso G v
  exact ⟨p, hp, Fin.ext he⟩

theorem orbits_eq_iff_sameOrbit (G : Colored n k) (u v : Fin n) :
    (orbits G)[u.val]! = (orbits G)[v.val]! ↔ SameOrbit G u v := Nauty.Sparse.orbits_eq_iff G u v

theorem orbit_le (G : Colored n k) (u v : Fin n) (h : SameOrbit G u v) :
    (orbits G)[u.val]! ≤ v.val := Nauty.Sparse.orbit_le G u v h

theorem numOrbits_eq_count (G : Colored n k) :
    numOrbits G = (List.range n).countP (fun i => (orbits G)[i]! == i) := Nauty.Sparse.numorbits_eq_count G

end Aut

/-- The native generator list, orbit representatives, orbit count and
first-path index product, extracted together from one sparse traversal. -/
@[expose] def autos (G : Colored n k) : GraphIso.AutResult n :=
  let st := Nauty.Sparse.runColored G
  { gens := st.generators, orbits := st.orbits, numOrbits := st.numorbits, order := st.order }

theorem gens_autos (G : Colored n k) : (autos G).gens = Aut.gens G := rfl
theorem orbits_autos (G : Colored n k) : (autos G).orbits = Aut.orbits G := rfl
theorem numOrbits_autos (G : Colored n k) : (autos G).numOrbits = Aut.numOrbits G := rfl
theorem order_autos (G : Colored n k) : (autos G).order = Aut.order G := rfl

theorem autos_isIso {G : Colored n k} {p : Perm n} (h : p ∈ (autos G).gens) : IsIso G G p :=
  Aut.gens_isIso h

theorem autos_complete (G : Colored n k) {p : Perm n} (h : IsIso G G p) :
    Perm.Generated (autos G).gens p := Aut.complete G h

theorem autos_sameOrbit (G : Colored n k) (u v : Fin n) :
    (autos G).orbits[u.val]! = (autos G).orbits[v.val]! ↔ SameOrbit G u v :=
  Aut.orbits_eq_iff_sameOrbit G u v

end Hex.GraphIso.Sparse

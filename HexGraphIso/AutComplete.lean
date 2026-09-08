/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.AutGroup
public import HexGraphIso.Generated
-- Export the contract without exporting the traversal proof implementation.
import HexGraphIso.Nauty.Policy.Complete
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Autos
import all HexGraphIso.Generated

public section

namespace Hex.GraphIso

variable {n k : Nat}

/-- The discovered generators generate every automorphism of the graph. -/
theorem Aut.complete (G : Colored n k) {p : Perm n} (hp : IsIso G G p) :
    Perm.Generated (Aut.gens G) p := by
  simpa [Aut.gens, Aut.checked, Aut.trace, List.map_filterMap, Option.map_map,
    Function.comp_def, Nauty.runColoredTraced, Nauty.runTraced, Nauty.Engine.runColoredTraced]
    using Nauty.Engine.generators_complete hp

/-- Completeness: every automorphism is a word in the returned generators. -/
theorem autos_complete (G : Colored n k) {p : Perm n} (hp : IsIso G G p) :
    Perm.Generated (autos G).gens p := by
  rw [gens_autos]
  exact Aut.complete G hp


/-- The orbit array is exactly the orbit partition of the full
 automorphism group. -/
theorem Aut.orbits_eq_iff_sameOrbit (G : Colored n k) (u v : Fin n) :
    (Aut.orbits G)[u.val]! = (Aut.orbits G)[v.val]! ↔ SameOrbit G u v := by
  constructor
  · exact Aut.sameOrbit_of_orbits_eq G u v
  · intro h
    obtain ⟨p, hp, hv⟩ := h.elim
    exact Aut.generated_iff_orbits_eq.mp ⟨p, Aut.complete G hp, hv⟩

/-- Two vertices have the same returned representative exactly when
an automorphism carries one onto the other. -/
theorem autos_sameOrbit (G : Colored n k) (u v : Fin n) :
    (autos G).orbits[u.val]! = (autos G).orbits[v.val]! ↔ SameOrbit G u v :=
  Aut.orbits_eq_iff_sameOrbit G u v

end Hex.GraphIso

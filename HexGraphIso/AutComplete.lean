/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Autos
public import HexGraphIso.Generated
-- Export the contract without exporting the traversal proof implementation.
import HexGraphIso.Nauty.Correct.Generation.FirstGeneration
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Incumbent
import all HexGraphIso.Autos
import all HexGraphIso.Generated

public section

namespace Hex.GraphIso

variable {n k : Nat}

/-- The discovered generators generate every automorphism of the graph. -/
theorem Aut.complete (G : Colored n k) {p : Perm n} (hp : IsIso G G p) :
    Perm.Generated (Aut.gens G) p := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    have he : p = Perm.id 0 := Perm.ext (fun v => Fin.elim0 v)
    rw [he]
    exact .id
  · refine Nauty.Generation.first_generates G 100 (n + 2) 1 (Nauty.initialPartition G).2.length []
      (Nauty.rootSt n (Nauty.initialPartition G).1 (Nauty.initialPartition G).2)
      Nauty.FrameTrail.empty [] (Nauty.FirstInv.root hn) Nauty.PathOk.root
      (Nat.le_refl 1) (Nauty.CheapDesc.same { g := Nauty.rowsOf G } 1 _)
      (Nauty.orbSound_orbConn_init _) (Nat.le_refl 1) rfl
      (by simp [Nauty.rootSt]) (by omega) ?_ ?_ p hp ?_
    · intro b
      simp [Nauty.rootSt]
    · intro γ hγ
      simpa only [Aut.trace, Nauty.runColoredTraced, Nauty.runTraced, beq_iff_eq,
        Nat.ne_of_gt hn, ite_false, Id.run_pure, Nauty.rootSt, Array.mem_toList_iff] using hγ
    · intro b hb
      cases hb

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

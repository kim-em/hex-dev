/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.AutGroup
import HexGraphIso.AutComplete
import HexGraphIso.Nauty.Policy.Generated.Root
public import HexGraphIso.Autom
public import HexGraphIso.Nauty.Policy.Result
public import HexGraphIso.Nauty.Invariant.Carrier
import all HexGraphIso.Nauty.Policy.Colors
import all HexGraphIso.Perm
import all HexGraphIso.Nauty.Cert.Cert
import all HexGraphIso.Nauty.Invariant.Trace
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso

variable {n k : Nat}

namespace Aut

open Nauty

/-- Every array in the executable trace is admitted, including redundant
code-two automorphisms. The proof uses the search invariant; it adds no
work to the traversal. These public trace lemmas remain available to
downstream consumers even though whole-group completeness now follows
directly from the search theorem. -/
theorem trace_admitted (G : Colored n k) :
    ∀ γ ∈ trace G, ∃ p, autom? G γ = some p := by
  intro γ hγ
  have hm : γ ∈ (Nauty.runColoredTraced G).autos := by
    simpa only [trace, runColoredTraced, runTraced, Nauty.runColoredTraced,
      Array.mem_toList_iff] using hγ
  exact admit_root (Nauty.runColoredTraced_checked G hm)
    (Nauty.runColoredTraced_stab G hm)

/-- Every emission passes the public filter, which preserves their order. -/
theorem raw_eq_emitted (G : Colored n k) : raw G = emitted G := by
  have h : ∀ xs : List (Array Nat), (∀ γ ∈ xs, ∃ p, autom? G γ = some p) →
      (xs.filterMap fun γ => (autom? G γ).map fun p => (γ, p)).map Prod.fst = xs := by
    intro xs hx
    induction xs with
    | nil => rfl
    | cons γ xs ih =>
        obtain ⟨p, hp⟩ := hx γ (by simp)
        simp only [List.filterMap_cons, hp, Option.map_some, List.map_cons]
        congr 1
        exact ih (fun δ hδ => hx δ (by simp [hδ]))
  exact h (emitted G) (fun _ hγ => emitted_admitted G hγ)

/-- The public list has the length counted by the search. -/
theorem length_gens (G : Colored n k) : (gens G).length = (runColored G).numgenerators := by
  have h := congrArg List.length (raw_eq_emitted G)
  simp only [raw, List.length_map] at h
  have hv := (Emission.run_valid n (rowsOf G) (initialPartition G).1 (initialPartition G).2).size
  rw [gens, List.length_map, h]
  exact Array.length_toList.trans hv

/-- A checked emission belongs to the public generator list. -/
theorem mem_gens {G : Colored n k} {γ : Array Nat} {p : Perm n}
    (hemit : γ ∈ emitted G) (hcheck : autom? G γ = some p) : p ∈ gens G := by
  apply List.mem_map.mpr
  refine ⟨(γ, p), ?_, rfl⟩
  apply List.mem_filterMap.mpr
  exact ⟨γ, hemit, by simp [hcheck]⟩

/-- A recorded leaf carrier supplies a generated permutation with the
same pointwise action on the entire reference labelling. -/
theorem generated_carrier {G : Colored n k} {ctx : Ctx n}
    {ref cur : Array Nat} {store : Array (Array Nat)}
    (h : LabelCarrier ctx ref cur store)
    (hstore : ∀ γ ∈ store, γ ∈ trace G)
    (href : LabOk ref n) (hsize : ref.size = n) :
    ∃ p, Perm.Generated (gens G) p ∧
      ∀ i, (hi : i < n) → (p.get ⟨ref[i]!, href i (by omega)⟩).val = cur[i]! := by
  obtain ⟨γ, hmem, _, hmap⟩ := h
  obtain ⟨p, hp⟩ := trace_admitted G γ (hstore γ hmem)
  exact ⟨p, Aut.complete G (autom?_isIso hp), fun i hi =>
    (autom?_val_get hp ⟨ref[i]!, href i (by omega)⟩).trans (hmap i hi)⟩

/-- Agreement on a reference permutation labelling identifies the whole
permutation. No orbit-count inference is needed for this final step. -/
theorem generated_of_reference {G : Colored n k} {p q : Perm n}
    {ref : Array Nat} (hsize : ref.size = n)
    (href : ref.toList.Perm (List.range n))
    (hq : Perm.Generated (gens G) q)
    (heq : ∀ i, (hi : i < n) → ∀ hv : ref[i]! < n,
      q.get ⟨ref[i]!, hv⟩ = p.get ⟨ref[i]!, hv⟩) :
    Perm.Generated (gens G) p := by
  have hpq : q = p := by
    apply Perm.ext
    intro v
    obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp
      (href.mem_iff.mpr (List.mem_range.mpr v.isLt))
    have hin : i < n := by simpa [hsize] using hi
    have hv : ref[i]! = v.val := by
      rw [getElem!_pos ref i (by omega)]
      exact hiv
    have h := heq i hin (by omega)
    have hv' : (⟨ref[i]!, by omega⟩ : Fin n) = v := Fin.ext hv
    rwa [hv'] at h
  rwa [← hpq]

end Aut

end Hex.GraphIso

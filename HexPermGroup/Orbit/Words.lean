/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normalize

public section

namespace Hex.PermGroup.Orbit

variable {n : Nat} {S : Array (Perm n)} {a : Fin n} {c : Orbit n}

theorem mem_stabilizerGens (h : c.Valid S a) (p : Perm n) :
    p ∈ stabilizerGens h ↔ ∃ (i : Fin S.size) (x : Fin c.points.size),
      schreier h S[i.val] (.generator (Array.getElem_mem i.isLt)) x = p := by
  simp [stabilizerGens]

/-- A program for one recomputed Schreier element, in the same composition order
as `schreier`. Orbit transporter programs retain their internal DAG references. -/
@[expose] def schreierWord (h : c.Valid S a) (i : Fin S.size) (x : Fin c.points.size) : Program :=
  (c.words[(act h S[i.val] (.generator (Array.getElem_mem i.isLt)) x).val]).inv.comp
    ((Generator.ofIndex S i false).program.comp c.words[x.val])

theorem check_schreierWord (h : c.Valid S a) (i : Fin S.size) (x : Fin c.points.size) :
    checkWord S (schreier h S[i.val] (.generator (Array.getElem_mem i.isLt)) x)
      (schreierWord h i x) = true := by
  apply decide_eq_true
  apply Program.eval_comp
  · exact Program.eval_inv (of_decide_eq_true (h.2.2.2.2.1 _).1)
  · apply Program.eval_comp
    · exact of_decide_eq_true (Generator.check_program (Generator.ofIndex S i false))
    · exact of_decide_eq_true (h.2.2.2.2.1 x).1

/-- Provenance for every pair in `stabilizerGens`, in generator-major order. -/
@[expose] def stabilizerWords (h : c.Valid S a) : Vector Program (stabilizerGens h).size :=
  ⟨((List.finRange S.size).flatMap fun i =>
    (List.finRange c.points.size).map fun x => schreierWord h i x).toArray,
    by simp [stabilizerGens, List.length_flatMap]⟩

theorem check_stabilizerWords (h : c.Valid S a) :
    checkWords S (stabilizerGens h) (stabilizerWords h) = true := by
  apply decide_eq_true
  intro j
  let pairs := (List.finRange S.size).flatMap fun i =>
    (List.finRange c.points.size).map fun x => (i, x)
  have hg : stabilizerGens h = (pairs.map fun (i, x) =>
      schreier h S[i.val] (.generator (Array.getElem_mem i.isLt)) x).toArray := by
    simp [pairs, stabilizerGens, List.map_flatMap, List.map_map, Function.comp_def]
  have hw : (stabilizerWords h).toArray = (pairs.map fun (i, x) => schreierWord h i x).toArray := by
    simp [pairs, stabilizerWords, List.map_flatMap, List.map_map, Function.comp_def]
  have hj : j.val < pairs.length := by simpa [hg] using j.isLt
  change checkWord S (stabilizerGens h)[j.val] (stabilizerWords h).toArray[j.val] = true
  simpa only [hg, hw, List.getElem_toArray, List.getElem_map] using
    check_schreierWord h pairs[j.val].1 pairs[j.val].2

theorem stabilizerGens_fixed (h : c.Valid S a) {base : Nat}
    (ha : a.val = base) (hf : Chain.Fixed base S) :
    Chain.Fixed (base + 1) (stabilizerGens h) := by
  intro j x hx
  have hg := (stabilizerGens_spec h _).mp (Generated.generator (Array.getElem_mem j.isLt))
  by_cases he : x = a
  · simpa only [he] using hg.2
  · have hxbase : x.val < base := by
      have hne : x.val ≠ a.val := fun hh => he (Fin.ext hh)
      omega
    apply hg.1.lift (P := fun p => p.get x = x)
      (by simp) (fun p hp => ?_) (fun p q hp hq => by simp [hp, hq])
      (fun p hp => ?_)
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hp
      exact hf ⟨i, hi⟩ x hxbase
    · have hi := congrArg p.inv.get hp
      simpa using hi.symm

end Hex.PermGroup.Orbit

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Build
public import HexPermGroup.Budget

public section

/-! Bounded deterministic chain construction, including discarded suffix rebuilds. -/

namespace Hex.PermGroup.Build

open Execution

/-- A successful bounded computation retains the exact result of its unbounded
counterpart. The equality is erased; it never runs the reference computation. -/
abbrev Computation {α : Type} (budget : Budget) (value : α) := Run budget {result : α // result = value}

/-- Stream the same Schreier candidates as `State.scan`. Every candidate reserves
its permutation work before evaluation, and its word only after a failed sift.
The recursive builder uses the caller's meter, including discarded suffixes. -/
@[expose] def scanWith {n base : Nat} {S : Array (Perm n)} {ι : Type} {budget : Budget}
    (build : (T : Array (Perm n)) → Chain.Fixed base T → Construction T base)
    (bounded : (T : Array (Perm n)) → (h : Chain.Fixed base T) → Computation budget (build T h))
    (family : ι → Candidate S base) (wordSize : ι → Nat)
    (s : State S base) (is : List ι) : Computation budget (s.scan build family is) := do
  match hlist : is with
  | [] => return ⟨s, by simp only [hlist, State.scan]⟩
  | i :: is =>
    reserve .pairs 1
    reserve .images (3 * n)
    let candidate := family i
    reserve .sifts (n - base + 1)
    reserve .images (2 * n * (n - base) + n)
    if hm : s.result.chain.accepts base candidate.value = true then
      let result ← scanWith build bounded family wordSize s is
      return ⟨result.val, by
        simpa only [hlist, State.scan, State.insert, candidate, hm, Bool.true_eq, ↓reduceIte] using result.property⟩
    else
      reserve .certificates (wordSize i)
      reserve .images n
      let seeds := s.seeds.push candidate.value (candidate.word ()) candidate.valid candidate.fixed
      let child ← bounded seeds.generators seeds.fixed
      let next : State S base := ⟨seeds, child.val, s.rebuilds + 1 + child.val.rebuilds⟩
      let result ← scanWith build bounded family wordSize next is
      return ⟨result.val, by
        rw [hlist, State.scan, State.insert]
        simp only [candidate] at hm
        simp only [hm, Bool.false_eq_true, ↓reduceIte]
        simpa only [next, child.property, seeds, candidate] using result.property⟩

/-- Reserve normalization and orbit work in whole bounded batches. The point
allowance covers the full degree, including declared fixed points. -/
@[expose] def bounded {n : Nat} {budget : Budget} (base : Nat) (hb : base ≤ n)
    (S : Array (Perm n)) (hf : Chain.Fixed base S) : Computation budget (build base hb S hf) := do
  reserve .certificates (4 * S.size + 1)
  reserve .images (64 * n * (S.size + 1) ^ 2)
  let normal := normalize S
  if hbase : base < n then
    reserve .points (n * (normal.generators.size + 1))
    reserve .certificates (2 * n)
    reserve .images (2 * n * n + 4 * n)
    let orbit := Orbit.ofSymmetric normal.generators ⟨base, hbase⟩ normal.symmetric
    let family := fun (pair : Fin normal.generators.size × Fin orbit.val.points.size) =>
      let p := Orbit.schreier orbit.property normal.generators[pair.1.val]
        (.generator (Array.getElem_mem pair.1.isLt)) pair.2
      show Candidate normal.generators (base + 1) from
      { value := p
        word := fun _ => Orbit.schreierWord orbit.property pair.1 pair.2
        valid := Orbit.check_schreierWord orbit.property pair.1 pair.2
        fixed := by
          intro x hx
          by_cases he : x.val = base
          · have heq : x = ⟨base, hbase⟩ := Fin.ext he
            simpa only [heq] using Orbit.schreier_fixes orbit.property
              (.generator (Array.getElem_mem pair.1.isLt)) pair.2
          · exact Chain.fixed_generated (normal.fixed hf)
              (Orbit.schreier_generated orbit.property _ _) x (by omega) }
    let pairCount := normal.generators.size * orbit.val.points.size
    reserve .certificates pairCount
    let pairs := (List.finRange normal.generators.size).flatMap fun i =>
      (List.finRange orbit.val.points.size).map fun x => (i, x)
    let recurse := fun T h => build (base + 1) hbase T h
    let limited := fun T h => bounded (base + 1) hbase T h
    let trivial ← limited #[] (Seeds.empty normal.generators (base + 1)).fixed
    let initial : State normal.generators (base + 1) :=
      ⟨Seeds.empty normal.generators (base + 1), trivial.val, trivial.val.rebuilds⟩
    -- Both transporter programs have at most 2*n nodes. The nested products,
    -- inversion and generator literal add four; copying both intermediate DAGs
    -- allocates at most twice the final size.
    let result ← scanWith recurse limited family (fun _ => 8 * n + 8) initial pairs
    -- Reword only the top level of the completed suffix. Signed source
    -- references select one retained program, possibly adding an inverse node.
    let words := result.val.seeds.words
    let normalTail := result.val.result.normal
    let cost := normalTail.sources.toArray.foldl (fun total (source : Fin result.val.seeds.generators.size × Bool) =>
      total + (words.get source.1).nodes.size + 1) 0
    reserve .certificates cost
    let value : Construction S base :=
      { normal := normal
        chain := .cons ⟨normal.generators, normal.words, orbit.val⟩
          (result.val.result.reword result.val.seeds.words)
        generators := rfl
        checked := by
          simp only [Chain.checkFrom, dite_eq_left hbase, dite_eq_left orbit.property]
          apply decide_eq_true
          refine ⟨normal.normalized.1, normal.fixed hf, ?_, ?_, ?_⟩
          · exact result.val.result.reword_words result.val.seeds.words result.val.seeds.valid
          · exact result.val.result.reword_checked result.val.seeds.words
          · intro j
            apply (result.val.result.reword_accepts result.val.seeds.words _).mpr
            obtain ⟨i, x, he⟩ := (Orbit.mem_stabilizerGens orbit.property _).mp
              (Array.getElem_mem j.isLt)
            rw [← he, result.property]
            exact initial.scan_mem recurse family pairs (i, x) (by simp [pairs])
        words := normal.valid
        rebuilds := result.val.rebuilds }
    return ⟨value, by
      rw [build]
      simp only [hbase, ↓reduceDIte]
      dsimp only [value]
      rcases result with ⟨result, hr⟩
      cases hr
      rcases trivial with ⟨trivial, ht⟩
      cases ht
      rfl⟩
  else
    return ⟨
      { normal := normal
        chain := .leaf normal.generators normal.words
        generators := rfl
        checked := by
          apply decide_eq_true
          have he : base = n := by omega
          refine ⟨he, normal.fixed hf, ?_⟩
          intro j
          apply Perm.ext
          intro x
          simpa using normal.fixed hf j x (by simp [he])
        words := normal.valid
        rebuilds := 0 }, by simp only [build, hbase, ↓reduceDIte]; rfl⟩
termination_by n - base

end Hex.PermGroup.Build

namespace Hex.PermGroup.Group

/-- Construct a group using the current producer meter, including every
recursive suffix reconstruction. -/
@[expose] def construct {budget : Execution.Budget} (S : Array (Perm n)) :
    Build.Computation budget (ofGenerators S) := do
  let c ← Build.bounded 0 (Nat.zero_le n) S (by intro _ x hx; omega)
  let G : Group n :=
    { generators := S
      chain := c.val.chain
      valid := by
        apply decide_eq_true
        exact ⟨by simpa only [c.val.generators] using c.val.normal.normalized, c.val.words, c.val.checked⟩ }
  return ⟨G, by simp only [G, c.property, ofGenerators]⟩

/-- Construct a checked group within one shared producer budget. Exhaustion has
no group output, so it cannot supply an ambient order or negative membership.
Successful output is exactly `ofGenerators S`, with its acceptance proof. -/
@[expose] def buildWith (budget : Execution.Budget) (S : Array (Perm n)) :
    Execution.Measured budget {G : Group n // G = ofGenerators S} :=
  Execution.run budget (construct S)

end Hex.PermGroup.Group

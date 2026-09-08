/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Orbit.Build
public import HexPermGroup.Orbit.Words
public import HexPermGroup.Group

public section

namespace Hex.PermGroup

/-- A complete suffix for a supplied input, retaining its normalization map for
provenance transfer when used beneath another chain level. -/
structure Construction (S : Array (Perm n)) (base : Nat) where
  normal : Normalized S
  chain : Chain n
  generators : chain.generators = normal.generators
  checked : chain.checkFrom base = true
  words : checkWords S chain.generators chain.words = true
  /-- Recursive suffix reconstructions triggered by strict subgroup insertions. -/
  rebuilds : Nat

namespace Construction

variable {n : Nat} {S : Array (Perm n)} {base : Nat}

theorem accepts_iff (c : Construction S base) (p : Perm n) :
    c.chain.accepts base p = true ↔ Generated S p := by
  rw [Chain.checkFrom_sound c.checked, c.generators]
  exact c.normal.generated_iff p

/-- Give a complete suffix provenance in its preceding level. -/
@[expose] def reword (c : Construction S base) (words : Vector Program S.size) : Chain n :=
  c.chain.reword ((c.normal.wordsFrom words).cast (congrArg Array.size c.generators).symm)

@[simp] theorem reword_checked (c : Construction S base) (words : Vector Program S.size) :
    (c.reword words).checkFrom base = true := by simp [reword, c.checked]

@[simp] theorem reword_generators (c : Construction S base) (words : Vector Program S.size) :
    (c.reword words).generators = c.normal.generators := by simp [reword, c.generators]

theorem reword_words (c : Construction S base) {T : Array (Perm n)}
    (words : Vector Program S.size) (hw : checkWords T S words = true) :
    checkWords T (c.reword words).generators (c.reword words).words = true := by
  simp only [reword, Chain.checkWords_reword]
  have h := c.normal.check_wordsFrom words hw
  unfold checkWords at *
  apply decide_eq_true
  intro j
  simpa only [Vector.getElem_cast, c.generators] using
    (of_decide_eq_true h) ⟨j.val, by simpa [c.generators] using j.isLt⟩

theorem reword_accepts (c : Construction S base) (words : Vector Program S.size) (p : Perm n) :
    (c.reword words).accepts base p = true ↔ Generated S p := by
  rw [Chain.checkFrom_sound (c.reword_checked words), c.reword_generators]
  exact c.normal.generated_iff p

end Construction

namespace Build

/-- Retained generators, with provenance in the preceding level and fixed-point
conditions for the complete suffix being rebuilt. -/
structure Seeds (S : Array (Perm n)) (base : Nat) where
  generators : Array (Perm n)
  words : Vector Program generators.size
  valid : checkWords S generators words = true
  fixed : Chain.Fixed base generators

namespace Seeds

variable {n : Nat} {S : Array (Perm n)} {base : Nat}

@[expose] def empty (S : Array (Perm n)) (base : Nat) : Seeds S base where
  generators := #[]
  words := #v[]
  valid := by apply decide_eq_true; intro j; exact j.elim0
  fixed := by intro j; exact j.elim0

@[expose] def push (s : Seeds S base) (p : Perm n) (w : Program)
    (hw : checkWord S p w = true) (hf : ∀ x : Fin n, x.val < base → p.get x = x) : Seeds S base where
  generators := s.generators.push p
  words := (s.words.push w).cast (by simp)
  valid := by
    apply decide_eq_true
    intro ⟨j, hj⟩
    by_cases hlt : j < s.generators.size
    · simpa [Array.getElem_push_lt hlt, Vector.getElem_push_lt hlt] using
        (of_decide_eq_true s.valid) ⟨j, hlt⟩
    · have he : j = s.generators.size := by simp at hj; omega
      subst j
      simpa using hw
  fixed := by
    intro ⟨j, hj⟩ x hx
    by_cases hlt : j < s.generators.size
    · simpa [Array.getElem_push_lt hlt] using s.fixed ⟨j, hlt⟩ x hx
    · have he : j = s.generators.size := by simp at hj; omega
      subst j
      simpa using hf x hx

theorem push_mono (s : Seeds S base) (p : Perm n) (w : Program) (hw) (hf)
    {q : Perm n} (hq : Generated s.generators q) :
    Generated (s.push p w hw hf).generators q :=
  hq.mono fun _ h => .generator (Array.mem_push_of_mem _ h)

theorem push_mem (s : Seeds S base) (p : Perm n) (w : Program) (hw) (hf) :
    Generated (s.push p w hw hf).generators p :=
  .generator (by simp [push])

end Seeds

/-- Filtering always keeps a complete chain for exactly the retained generators. -/
structure State (S : Array (Perm n)) (base : Nat) where
  seeds : Seeds S base
  result : Construction seeds.generators base
  /-- Includes reconstructions inside discarded earlier suffixes. -/
  rebuilds : Nat

/-- A candidate's program is delayed until insertion, so discarded Schreier
elements allocate neither copied transporter programs nor provenance arrays. -/
structure Candidate (S : Array (Perm n)) (base : Nat) where
  value : Perm n
  word : Unit → Program
  valid : checkWord S value (word ()) = true
  fixed : ∀ x : Fin n, x.val < base → value.get x = x

namespace State

variable {n : Nat} {S : Array (Perm n)} {base : Nat}

/-- Inspect one candidate using a complete sift. A successful sift leaves the
state alone; a failure inserts the generator and invokes the complete builder. -/
@[expose] def insert
    (build : (T : Array (Perm n)) → Chain.Fixed base T → Construction T base)
    (s : State S base) (p : Perm n) (w : Unit → Program) (hw : checkWord S p (w ()) = true)
    (hf : ∀ x : Fin n, x.val < base → p.get x = x) : State S base :=
  if s.result.chain.accepts base p then s
  else
    let seeds := s.seeds.push p (w ()) hw hf
    let result := build seeds.generators seeds.fixed
    ⟨seeds, result, s.rebuilds + 1 + result.rebuilds⟩

theorem insert_mono (build) (s : State S base) (p : Perm n) (w : Unit → Program) (hw) (hf)
    {q : Perm n} (hq : Generated s.seeds.generators q) :
    Generated (s.insert build p w hw hf).seeds.generators q := by
  unfold insert
  split
  · exact hq
  · exact s.seeds.push_mono p (w ()) hw hf hq

theorem insert_mem (build) (s : State S base) (p : Perm n) (w : Unit → Program) (hw) (hf) :
    Generated (s.insert build p w hw hf).seeds.generators p := by
  unfold insert
  split
  · rename_i h
    exact (s.result.accepts_iff p).mp h
  · exact s.seeds.push_mem p (w ()) hw hf

/-- A failed complete sift supplies a witness that insertion strictly enlarges
the retained subgroup. The same claim is not made for an unfinished chain. -/
theorem insert_strict (build) (s : State S base) (p : Perm n) (w : Unit → Program) (hw) (hf)
    (h : s.result.chain.accepts base p = false) :
    ¬ Generated s.seeds.generators p ∧
      Generated (s.insert build p w hw hf).seeds.generators p := by
  refine ⟨?_, s.insert_mem build p w hw hf⟩
  intro hp
  have he := (s.result.accepts_iff p).mpr hp
  simp [h] at he

/-- Stream candidates in their supplied order, rebuilding only after an exact
nonmembership verdict from the current complete suffix. -/
@[expose] def scan {ι : Type}
    (build : (T : Array (Perm n)) → Chain.Fixed base T → Construction T base)
    (family : ι → Candidate S base) (s : State S base) : List ι → State S base
  | [] => s
  | i :: is =>
    let candidate := family i
    scan build family (s.insert build candidate.value candidate.word candidate.valid candidate.fixed) is

theorem scan_mono {ι : Type} (build) (family : ι → Candidate S base) (s : State S base) (is)
    {p : Perm n} (hp : Generated s.seeds.generators p) :
    Generated (s.scan build family is).seeds.generators p := by
  induction is generalizing s with
  | nil => exact hp
  | cons i is ih => exact ih _ (s.insert_mono build _ _ _ _ hp)

theorem scan_mem {ι : Type} (build) (family : ι → Candidate S base) (s : State S base)
    (is : List ι) (i : ι) (hi : i ∈ is) :
    Generated (s.scan build family is).seeds.generators (family i).value := by
  induction is generalizing s with
  | nil => simp at hi
  | cons j is ih =>
    rcases List.mem_cons.mp hi with hj | hi
    · subst i
      exact scan_mono build family _ is (s.insert_mem build _ _ _ _)
    · exact ih _ hi

end State

/-- Deterministic Schreier-Sims construction. Recursive calls move to the next
base point; each finite scan uses complete suffixes and retains exactly those
Schreier generators that enlarge the subgroup found so far. -/
@[expose] def build (base : Nat) (hb : base ≤ n) (S : Array (Perm n))
    (hf : Chain.Fixed base S) : Construction S base :=
  let normal := normalize S
  if hbase : base < n then
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
    let pairs := (List.finRange normal.generators.size).flatMap fun i =>
      (List.finRange orbit.val.points.size).map fun x => (i, x)
    let recurse := fun T h => build (base + 1) hbase T h
    let trivial := recurse #[] (Seeds.empty normal.generators (base + 1)).fixed
    let initial : State normal.generators (base + 1) :=
      ⟨Seeds.empty normal.generators (base + 1), trivial, trivial.rebuilds⟩
    let result := initial.scan recurse family pairs
    let tail := result.result.reword result.seeds.words
    { normal := normal
      chain := .cons ⟨normal.generators, normal.words, orbit.val⟩ tail
      generators := rfl
      checked := by
        simp only [Chain.checkFrom, dite_eq_left hbase, dite_eq_left orbit.property]
        apply decide_eq_true
        refine ⟨normal.normalized.1, normal.fixed hf, ?_, ?_, ?_⟩
        · exact result.result.reword_words result.seeds.words result.seeds.valid
        · exact result.result.reword_checked result.seeds.words
        · intro j
          apply (result.result.reword_accepts result.seeds.words _).mpr
          obtain ⟨i, x, he⟩ := (Orbit.mem_stabilizerGens orbit.property _).mp
            (Array.getElem_mem j.isLt)
          rw [← he]
          exact initial.scan_mem recurse family pairs (i, x) (by simp [pairs])
      words := normal.valid
      rebuilds := result.rebuilds }
  else
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
      rebuilds := 0 }
termination_by n - base

end Build

namespace Group

/-- Construct a complete checked group for every input generator array. Original
indices are retained even when normalization removes identities or duplicates. -/
@[expose] def ofGenerators (S : Array (Perm n)) : Group n :=
  let c := Build.build 0 (Nat.zero_le n) S (by intro _ x hx; omega)
  { generators := S
    chain := c.chain
    valid := by
      apply decide_eq_true
      exact ⟨by simpa only [c.generators] using c.normal.normalized, c.words, c.checked⟩ }

theorem ofGenerators_checks (S : Array (Perm n)) :
    checkChain S (ofGenerators S).chain = true := (ofGenerators S).valid

@[simp] theorem generators_ofGenerators (S : Array (Perm n)) :
    (ofGenerators S).generators = S := rfl

theorem contains_ofGenerators (S : Array (Perm n)) (p : Perm n) :
    (ofGenerators S).contains p = true ↔ Generated S p :=
  (ofGenerators S).contains_iff p

end Group

end Hex.PermGroup

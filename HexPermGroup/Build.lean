/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Orbit.Build
public import HexPermGroup.Orbit.Words
public import HexPermGroup.Group
public import HexPermGroup.Word.Substitute

public section

namespace Hex.PermGroup

namespace Chain

variable {n : Nat}

/-- Every level of a chain, including the terminal one, has a symmetric working
generator array. -/
@[expose] def AllWorking : Chain n → Prop
  | .leaf S _ => Working S
  | .cons level tail => Working level.generators ∧ tail.AllWorking

theorem AllWorking.working {c : Chain n} (h : c.AllWorking) : Working c.generators := by
  cases c with
  | leaf => exact h
  | cons => exact h.1

@[simp] theorem allWorking_reword (c : Chain n) (words : Vector Program c.generators.size) :
    (c.reword words).AllWorking ↔ c.AllWorking := by
  cases c <;> rfl

/-- The chain below the first level; a terminal chain is its own suffix. -/
@[expose] def suffix : Chain n → Chain n
  | .leaf S words => .leaf S words
  | .cons _ tail => tail

theorem AllWorking.suffix {c : Chain n} (h : c.AllWorking) : c.suffix.AllWorking := by
  cases c with
  | leaf => exact h
  | cons => exact h.2

theorem checkFrom_suffix {c : Chain n} {base : Nat} (hb : base < n)
    (h : c.checkFrom base = true) :
    checkWords c.generators c.suffix.generators c.suffix.words = true ∧
      c.suffix.checkFrom (base + 1) = true := by
  cases c with
  | leaf =>
    have := (of_decide_eq_true h).1
    omega
  | cons level tail =>
    simp only [checkFrom, dite_eq_left hb] at h
    split at h
    · have h := of_decide_eq_true h
      exact ⟨h.2.2.1, h.2.2.2.1⟩
    · contradiction

end Chain

namespace Normalized

variable {n : Nat} {S : Array (Perm n)}

/-- A symmetric working array normalizes to itself, with one generator reference
as the provenance of each element. -/
@[expose] def ofWorking (S : Array (Perm n)) (h : Chain.Working S) : Normalized S where
  generators := S
  sources := Hex.Vector.ofFn' fun j => (j, false)
  source_valid := by intro j; simp [Word.letter]
  words := Hex.Vector.ofFn' fun j => ⟨#[.generator j.val], 0⟩
  normalized := ⟨h, fun j => ⟨j, .inl rfl⟩, fun i => .inr (Array.getElem_mem i.isLt)⟩
  valid := by
    apply decide_eq_true
    intro j
    simp [checkWord, Program.eval, Program.evalCertified, Program.evalNodes,
      Program.evalNode, j.isLt]

/-- Adding an input generator keeps every normalized generator. -/
theorem mem_push (c : Normalized S) {p : Perm n} (d : Normalized (S.push p)) {x : Perm n}
    (hx : x ∈ c.generators) : x ∈ d.generators := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hx
  obtain ⟨hne, -⟩ := c.normalized.1.2.2 ⟨j, hj⟩
  obtain ⟨i, hi⟩ := c.normalized.2.1 ⟨j, hj⟩
  have hpush : (S.push p)[i.val]'(by simp; omega) = S[i.val] := Array.getElem_push_lt i.isLt
  have hmem : S[i.val] ≠ Perm.id n → S[i.val] ∈ d.generators := by
    intro hid
    rcases d.normalized.2.2 ⟨i.val, by simp; omega⟩ with h | h
    · exact absurd (hpush ▸ h) hid
    · exact hpush ▸ h
  rcases hi with hi | hi
  · rw [hi]
    exact hmem (hi ▸ hne)
  · rw [hi]
    have hid : S[i.val] ≠ Perm.id n := by
      intro he
      apply hne
      rw [hi, he, Perm.inv_id]
    obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.mp (hmem hid)
    have := (d.normalized.1.2.2 ⟨k, hk⟩).2
    simpa only [hke] using this

end Normalized

/-- A one-reference program for an element of `U`, or the identity if it is
absent. -/
@[expose] def embedWord (U : Array (Perm n)) (x : Perm n) : Program :=
  match U.finIdxOf? x with
  | some i => ⟨#[.generator i.val], 0⟩
  | none => ⟨#[.id], 0⟩

theorem check_embedWord (U : Array (Perm n)) {x : Perm n} (hx : x ∈ U) :
    checkWord U x (embedWord U x) = true := by
  unfold embedWord
  split
  · rename_i i hi
    have he := (Array.finIdxOf?_eq_some_iff.mp hi).1
    subst he
    simp [checkWord, Program.eval, Program.evalCertified, Program.evalNodes,
      Program.evalNode, i.isLt]
  · rename_i hi
    exact absurd hx (Array.finIdxOf?_eq_none_iff.mp hi)

/-- Programs for the elements of `T` as references into an array `U` containing
them. -/
@[expose] def embedWords (U T : Array (Perm n)) : Vector Program T.size :=
  Hex.Vector.ofFn' fun j => embedWord U T[j.val]

theorem check_embedWords (U T : Array (Perm n)) (h : ∀ x ∈ T, x ∈ U) :
    checkWords U T (embedWords U T) = true := by
  apply decide_eq_true
  intro j
  simpa [embedWords] using check_embedWord U (h _ (Array.getElem_mem j.isLt))

/-- Move programs over `T` to programs over a larger array `U`. -/
@[expose] def transferWords (U : Array (Perm n)) {T R : Array (Perm n)}
    (h : ∀ x ∈ T, x ∈ U) (words : Vector Program R.size)
    (hw : checkWords T R words = true) : Vector Program R.size :=
  Hex.Vector.ofFn' fun j =>
    Program.substitute U T (embedWords U T) (check_embedWords U T h) words[j.val]
      (p := R[j.val]) ((of_decide_eq_true hw) j)

theorem check_transferWords (U : Array (Perm n)) {T R : Array (Perm n)}
    (h : ∀ x ∈ T, x ∈ U) (words : Vector Program R.size)
    (hw : checkWords T R words = true) :
    checkWords U R (transferWords U h words hw) = true := by
  apply decide_eq_true
  intro j
  simpa [transferWords] using Program.check_substitute U T (embedWords U T)
    (check_embedWords U T h) words[j.val] ((of_decide_eq_true hw) j)

/-- A complete suffix for a supplied input, retaining its normalization map for
provenance transfer when used beneath another chain level. -/
structure Construction (S : Array (Perm n)) (base : Nat) where
  normal : Normalized S
  chain : Chain n
  generators : chain.generators = normal.generators
  checked : chain.checkFrom base = true
  words : checkWords S chain.generators chain.words = true
  working : chain.AllWorking
  /-- Strict subgroup insertions made while constructing this suffix, including
  those in its own suffixes. -/
  extensions : Nat

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

theorem reword_working (c : Construction S base) (words : Vector Program S.size) :
    (c.reword words).AllWorking := by
  simpa [reword] using c.working

/-- Reuse a checked chain as a complete suffix for its own top-level generators. -/
@[expose] def ofChain (c : Chain n) (base : Nat) (hc : c.checkFrom base = true)
    (hw : c.AllWorking) : Construction c.generators base where
  normal := Normalized.ofWorking c.generators hw.working
  chain := c.reword (Normalized.ofWorking c.generators hw.working).words
  generators := Chain.generators_reword ..
  checked := (Chain.checkFrom_reword ..).trans hc
  words := (Chain.checkWords_reword ..).trans (Normalized.ofWorking c.generators hw.working).valid
  working := (Chain.allWorking_reword ..).mpr hw
  extensions := 0

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
  /-- Extensions made so far, including those inside suffix extensions. -/
  extensions : Nat

/-- A candidate's program is delayed until insertion, so discarded Schreier
elements allocate neither copied transporter programs nor provenance arrays. -/
structure Candidate (S : Array (Perm n)) (base : Nat) where
  value : Perm n
  word : Unit → Program
  valid : checkWord S value (word ()) = true
  fixed : ∀ x : Fin n, x.val < base → value.get x = x

/-- Extend a complete suffix by one input generator. -/
abbrev Extender (n base : Nat) :=
  (T : Array (Perm n)) → Construction T base → (p : Perm n) → Chain.Fixed base (T.push p) →
    Construction (T.push p) base

namespace State

variable {n : Nat} {S : Array (Perm n)} {base : Nat}

/-- Inspect one candidate using a complete sift. A successful sift leaves the
state alone; a failure inserts the generator and extends the current suffix. -/
@[expose] def insert (extend : Extender n base)
    (s : State S base) (p : Perm n) (w : Unit → Program) (hw : checkWord S p (w ()) = true)
    (hf : ∀ x : Fin n, x.val < base → p.get x = x) : State S base :=
  if s.result.chain.accepts base p then s
  else
    let seeds := s.seeds.push p (w ()) hw hf
    let result := extend s.seeds.generators s.result p seeds.fixed
    ⟨seeds, result, s.extensions + 1 + result.extensions⟩

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

/-- Stream candidates in their supplied order, extending the suffix only after an
exact nonmembership verdict from the current complete suffix. -/
@[expose] def scan {ι : Type} (build : Extender n base)
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

/-- The Schreier candidates of one level: `h(s, x)` for each symmetric
generator `s` and orbit point `x`, with delayed words in the level generators. -/
@[expose] def family {S : Array (Perm n)} {base : Nat} (hbase : base < n)
    (normal : Normalized S) (hf : Chain.Fixed base S)
    (orbit : {c : Orbit n // c.Valid normal.generators ⟨base, hbase⟩})
    (pair : Fin normal.generators.size × Fin orbit.val.points.size) :
    Candidate normal.generators (base + 1) where
  value := Orbit.schreier orbit.property normal.generators[pair.1.val]
    (.generator (Array.getElem_mem pair.1.isLt)) pair.2
  word := fun _ => Orbit.schreierWord orbit.property pair.1 pair.2
  valid := Orbit.check_schreierWord orbit.property pair.1 pair.2
  fixed := by
    intro x hx
    by_cases he : x.val = base
    · have heq : x = ⟨base, hbase⟩ := Fin.ext he
      simpa only [heq] using Orbit.schreier_fixes orbit.property
        (.generator (Array.getElem_mem pair.1.isLt)) pair.2
    · exact Chain.fixed_generated (normal.fixed hf)
        (Orbit.schreier_generated orbit.property _ _) x (by omega)

/-- All Schreier pairs of a level, generator-major. -/
@[expose] def pairs (r q : Nat) : List (Fin r × Fin q) :=
  (List.finRange r).flatMap fun i => (List.finRange q).map fun x => (i, x)

theorem mem_pairs {r q : Nat} (i : Fin r) (x : Fin q) : (i, x) ∈ pairs r q := by
  simp [pairs]

/-- Assemble a level from a final scan state whose retained generators generate
every Schreier candidate of the level. -/
@[expose] def assemble {S : Array (Perm n)} {base : Nat} (hbase : base < n)
    (normal : Normalized S) (hf : Chain.Fixed base S)
    (orbit : {c : Orbit n // c.Valid normal.generators ⟨base, hbase⟩})
    (result : State normal.generators (base + 1))
    (hall : ∀ pair, Generated result.seeds.generators (family hbase normal hf orbit pair).value) :
    Construction S base where
  normal := normal
  chain := .cons ⟨normal.generators, normal.words, orbit.val⟩
    (result.result.reword result.seeds.words)
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
      exact hall (i, x)
  words := normal.valid
  working := ⟨normal.normalized.1, result.result.reword_working result.seeds.words⟩
  extensions := result.extensions

/-- Complete one level from a starting state for its suffix: stream every
Schreier pair against the current complete suffix, extending it at each
rejection. The starting state may already contain retained generators. -/
@[expose] def complete {S : Array (Perm n)} {base : Nat} (hbase : base < n)
    (normal : Normalized S) (hf : Chain.Fixed base S)
    (orbit : {c : Orbit n // c.Valid normal.generators ⟨base, hbase⟩})
    (extend : Extender n (base + 1)) (initial : State normal.generators (base + 1)) :
    Construction S base :=
  assemble hbase normal hf orbit
    (initial.scan extend (family hbase normal hf orbit)
      (pairs normal.generators.size orbit.val.points.size))
    (fun pair => initial.scan_mem extend _ _ pair (mem_pairs pair.1 pair.2))

/-- The terminal level: every generator fixes every point. -/
@[expose] def terminal {S : Array (Perm n)} {base : Nat} (hbase : ¬ base < n) (hb : base ≤ n)
    (normal : Normalized S) (hf : Chain.Fixed base S) : Construction S base where
  normal := normal
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
  working := normal.normalized.1
  extensions := 0

/-- The starting state for extending a complete suffix by one generator: the
suffix below its first level, with provenance moved to the new level's
generators, which contain the old ones. -/
@[expose] def resume {S : Array (Perm n)} {base : Nat} (hbase : base < n)
    (c : Construction S base) {p : Perm n} (normal : Normalized (S.push p)) :
    State normal.generators (base + 1) :=
  have hsuffix := Chain.checkFrom_suffix hbase c.checked
  have hsub : ∀ x ∈ c.chain.generators, x ∈ normal.generators := fun _ hx =>
    c.normal.mem_push normal (c.generators ▸ hx)
  { seeds :=
      { generators := c.chain.suffix.generators
        words := transferWords normal.generators hsub c.chain.suffix.words hsuffix.1
        valid := check_transferWords normal.generators hsub c.chain.suffix.words hsuffix.1
        fixed := Chain.checkFrom_fixed hsuffix.2 }
    result := Construction.ofChain c.chain.suffix (base + 1) hsuffix.2 c.working.suffix
    extensions := 0 }

/-- Add one generator to a complete suffix. The previous suffix below this level
becomes the starting state of the new level's scan, so only Schreier generators
that it rejects cause recursive extensions; nothing is rebuilt from scratch. -/
@[expose] def extend (base : Nat) (hb : base ≤ n) (S : Array (Perm n))
    (c : Construction S base) (p : Perm n) (hf : Chain.Fixed base (S.push p)) :
    Construction (S.push p) base :=
  let normal := normalize (S.push p)
  if hbase : base < n then
    let orbit := Orbit.ofSymmetric normal.generators ⟨base, hbase⟩ normal.symmetric
    complete hbase normal hf orbit (fun T d q hq => extend (base + 1) hbase T d q hq)
      (resume hbase c normal)
  else terminal hbase hb normal hf
termination_by n - base

/-- A complete chain for the trivial subgroup. -/
@[expose] def empty (base : Nat) (hb : base ≤ n) : Construction (#[] : Array (Perm n)) base :=
  let normal := normalize (#[] : Array (Perm n))
  have hf : Chain.Fixed base (#[] : Array (Perm n)) := fun j => j.elim0
  if hbase : base < n then
    let orbit := Orbit.ofSymmetric normal.generators ⟨base, hbase⟩ normal.symmetric
    complete hbase normal hf orbit (fun T d q hq => extend (base + 1) hbase T d q hq)
      ⟨Seeds.empty normal.generators (base + 1), empty (base + 1) hbase, 0⟩
  else terminal hbase hb normal hf
termination_by n - base

/-- Deterministic Schreier-Sims construction. Each level streams its Schreier
generators against a complete chain for those retained so far, extended at
each rejection. The retained generators then receive their own suffix by
recursion, so every stored generator below a level is one of its Schreier
generators. -/
@[expose] def build (base : Nat) (hb : base ≤ n) (S : Array (Perm n))
    (hf : Chain.Fixed base S) : Construction S base :=
  let normal := normalize S
  if hbase : base < n then
    let orbit := Orbit.ofSymmetric normal.generators ⟨base, hbase⟩ normal.symmetric
    let extender : Extender n (base + 1) := fun T d q hq => extend (base + 1) hbase T d q hq
    let initial : State normal.generators (base + 1) :=
      ⟨Seeds.empty normal.generators (base + 1), empty (base + 1) hbase, 0⟩
    let scanned := initial.scan extender (family hbase normal hf orbit)
      (pairs normal.generators.size orbit.val.points.size)
    let tail := build (base + 1) hbase scanned.seeds.generators scanned.seeds.fixed
    assemble hbase normal hf orbit ⟨scanned.seeds, tail, scanned.extensions + tail.extensions⟩
      (fun pair => initial.scan_mem extender _ _ pair (mem_pairs pair.1 pair.2))
  else terminal hbase hb normal hf
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

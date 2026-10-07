/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Build
public import HexPermGroup.Chain.Bounded

public section

/-! Bounded deterministic chain construction, including every suffix extension. -/

namespace Hex.PermGroup.Build

open Execution

/-- A successful bounded computation retains the exact result of its unbounded
counterpart. The equality is erased; it never runs the reference computation. -/
abbrev Computation {α : Type} (budget : Budget) (value : α) := Run budget {result : α // result = value}

/-- Stream the same Schreier candidates as `State.scan`. Every candidate reserves
its permutation work before evaluation, and its word only after a failed sift.
The recursive extender uses the caller's meter. -/
@[expose] def scanBudgeted {n base : Nat} {S : Array (Perm n)} {ι : Type} {budget : Budget}
    (extend : Extender n base)
    (bounded : (T : Array (Perm n)) → (c : Construction T base) → (p : Perm n) →
      (h : Chain.Fixed base (T.push p)) → Computation budget (extend T c p h))
    (family : ι → Candidate S base) (wordSize : ι → Nat)
    (s : State S base) (is : List ι) : Computation budget (s.scan extend family is) := do
  match hlist : is with
  | [] => return ⟨s, by simp only [hlist, State.scan]⟩
  | i :: is =>
    reserve .pairs 1
    reserve .images (3 * n)
    let candidate := family i
    let sifted ← s.result.chain.siftBudgeted base candidate.value
    have he : sifted.val.accepted = s.result.chain.accepts base candidate.value :=
      congrArg SiftResult.accepted sifted.property
    if hm : sifted.val.accepted = true then
      have hm : s.result.chain.accepts base candidate.value = true := he.symm.trans hm
      let result ← scanBudgeted extend bounded family wordSize s is
      return ⟨result.val, by
        simpa only [hlist, State.scan, State.insert, candidate, hm, Bool.true_eq, ↓reduceIte] using result.property⟩
    else
      have hm : s.result.chain.accepts base candidate.value ≠ true := fun h => hm (he.trans h)
      reserve .certificates (wordSize i)
      reserve .storage (2 * (s.seeds.generators.size + 1))
      let seeds := s.seeds.push candidate.value (candidate.word ()) candidate.valid candidate.fixed
      let child ← bounded s.seeds.generators s.result candidate.value seeds.fixed
      let next : State S base := ⟨seeds, child.val, s.extensions + 1 + child.val.extensions⟩
      let result ← scanBudgeted extend bounded family wordSize next is
      return ⟨result.val, by
        rw [hlist, State.scan, State.insert]
        simp only [candidate] at hm
        simp only [hm, Bool.false_eq_true, ↓reduceIte]
        simpa only [next, child.property, seeds, candidate] using result.property⟩

/-- Reserve the work of one level scan and assemble it, as `complete` does. -/
@[expose] def completeBudgeted {n base : Nat} {S : Array (Perm n)} {budget : Budget}
    (hbase : base < n) (normal : Normalized S) (hf : Chain.Fixed base S)
    (orbit : {c : Orbit n // c.Valid normal.generators ⟨base, hbase⟩})
    (extend : Extender n (base + 1))
    (bounded : (T : Array (Perm n)) → (c : Construction T (base + 1)) → (p : Perm n) →
      (h : Chain.Fixed (base + 1) (T.push p)) → Computation budget (extend T c p h))
    (initial : State normal.generators (base + 1)) :
    Computation budget (complete hbase normal hf orbit extend initial) := do
  let q := orbit.val.points.size
  let pairCount := normal.generators.size * q
  reserve .storage (normal.generators.size + 3 * pairCount)
  -- Each transporter has at most 2*q nodes. Inversion reserves 2*q+1;
  -- the generator literal reserves 1. A product of sizes a,b reserves
  -- b + (a+b) + (a+b+1) for map, append, and push respectively.
  -- The inner product therefore reserves 6*q+3, the outer 10*q+9.
  let result ← scanBudgeted extend bounded (family hbase normal hf orbit)
    (fun _ => 18 * q + 14) initial (pairs normal.generators.size q)
  -- Reword only the top level of the completed suffix. Signed source
  -- references select one retained program, possibly adding an inverse node.
  let words := result.val.seeds.words
  let normalTail := result.val.result.normal
  let cost := normalTail.sources.toArray.foldl (fun total (source : Fin result.val.seeds.generators.size × Bool) =>
    total + (words.get source.1).nodes.size + 1) 0
  reserve .certificates cost
  return ⟨assemble hbase normal hf orbit result.val (by
    rw [result.property]
    exact fun pair => initial.scan_mem extend _ _ pair (mem_pairs pair.1 pair.2)), by
    rcases result with ⟨result, hr⟩
    cases hr
    rfl⟩

/-- Reserve normalization work in whole bounded batches. -/
@[expose] def normalizeBudgeted {n : Nat} {budget : Budget} (S : Array (Perm n)) :
    Run budget {normal : Normalized S // normal = normalize S} := do
  reserve .certificates (4 * S.size + 1)
  -- Normalization orders the signed candidates three times. Each pass has
  -- r inverses, at most 2*r identity comparisons, and at most (2*r)^2
  -- ordering comparisons. An ordering comparison constructs four n-lists.
  let r := S.size
  reserve .images (3 * n * (3 * r + 4 * (2 * r) ^ 2))
  -- Signed expansion, filtering, compaction and output conversion use at
  -- most 20*r auxiliary slots per pass. Reserve four lists at each of at
  -- most 2*r merge levels, with at most 2*r entries per level.
  reserve .storage (3 * (20 * r + 4 * (2 * r) ^ 2))
  return ⟨normalize S, rfl⟩

/-- Reserve orbit work in whole bounded batches. The point allowance covers the
full degree, including declared fixed points. -/
@[expose] def orbitBudgeted {n : Nat} {budget : Budget} (S : Array (Perm n)) (a : Fin n)
    (hs : ∀ p ∈ S, p.inv ∈ S) :
    Run budget {orbit : {c : Orbit n // c.Valid S a} // orbit = Orbit.ofSymmetric S a hs} := do
  reserve .points (n * S.size + 1)
  reserve .storage (8 * n * (n + 1))
  let tree := Orbit.breadthFirst S a
  -- Discovery allocates no permutations. Compile only the discovered points:
  -- one identity at the root and one composition per remaining point. Each
  -- point also stores the inverse representative and compares the
  -- representative with a freshly built identity.
  let q := tree.val.points.size
  reserve .certificates (2 * q)
  reserve .images (4 * n * q)
  let programs := (Orbit.Tree.Certificates.empty tree.val).finish
  return ⟨⟨programs.orbit, programs.valid tree.property hs⟩, rfl⟩

/-- Reserve the provenance transfer of `resume`: one index search per old level
generator, and one substitution per retained suffix generator. -/
@[expose] def resumeBudgeted {n base : Nat} {S : Array (Perm n)} {budget : Budget}
    (hbase : base < n) (c : Construction S base) {p : Perm n} (normal : Normalized (S.push p)) :
    Run budget {s : State normal.generators (base + 1) // s = resume hbase c normal} := do
  let old := c.chain.generators.size
  reserve .images (n * old * normal.generators.size + n)
  let tail := c.chain.suffix
  let cost := tail.words.toArray.foldl (fun total w => total + 1 + old + w.nodes.size) 0
  reserve .certificates cost
  reserve .storage (2 * (tail.generators.size + old + 1))
  return ⟨resume hbase c normal, rfl⟩

/-- Extend a complete suffix within the caller's meter. -/
@[expose] def extendBudgeted {n : Nat} {budget : Budget} (base : Nat) (hb : base ≤ n)
    (S : Array (Perm n)) (c : Construction S base) (p : Perm n)
    (hf : Chain.Fixed base (S.push p)) : Computation budget (extend base hb S c p hf) := do
  let normal ← normalizeBudgeted (S.push p)
  if hbase : base < n then
    let orbit ← orbitBudgeted normal.val.generators ⟨base, hbase⟩ normal.val.symmetric
    let initial ← resumeBudgeted hbase c normal.val
    let result ← completeBudgeted hbase normal.val hf orbit.val
      (fun T d q hq => extend (base + 1) hbase T d q hq)
      (fun T d q hq => extendBudgeted (base + 1) hbase T d q hq) initial.val
    return ⟨result.val, by
      rw [extend]
      simp only [hbase, ↓reduceDIte]
      rcases normal with ⟨normal, hn⟩
      cases hn
      rcases orbit with ⟨orbit, ho⟩
      cases ho
      rcases initial with ⟨initial, hi⟩
      cases hi
      exact result.property⟩
  else
    return ⟨terminal hbase hb normal.val hf, by
      rw [extend]
      simp only [hbase, ↓reduceDIte]
      rcases normal with ⟨normal, hn⟩
      cases hn
      rfl⟩
termination_by n - base

/-- The budgeted counterpart of `empty`. -/
@[expose] def emptyBudgeted {n : Nat} {budget : Budget} (base : Nat) (hb : base ≤ n) :
    Computation budget (empty base hb) := do
  let normal ← normalizeBudgeted (#[] : Array (Perm n))
  have hf : Chain.Fixed base (#[] : Array (Perm n)) := fun j => j.elim0
  if hbase : base < n then
    let orbit ← orbitBudgeted normal.val.generators ⟨base, hbase⟩ normal.val.symmetric
    let below ← emptyBudgeted (base + 1) hbase
    let result ← completeBudgeted hbase normal.val hf orbit.val
      (fun T d q hq => extend (base + 1) hbase T d q hq)
      (fun T d q hq => extendBudgeted (base + 1) hbase T d q hq)
      ⟨Seeds.empty normal.val.generators (base + 1), below.val, 0⟩
    return ⟨result.val, by
      unfold empty
      simp only [hbase, ↓reduceDIte]
      rcases normal with ⟨normal, hn⟩
      cases hn
      rcases orbit with ⟨orbit, ho⟩
      cases ho
      rcases below with ⟨below, hb⟩
      cases hb
      exact result.property⟩
  else
    return ⟨terminal hbase hb normal.val hf, by
      unfold empty
      simp only [hbase, ↓reduceDIte]
      rcases normal with ⟨normal, hn⟩
      cases hn
      rfl⟩
termination_by n - base

/-- The budgeted counterpart of `build`, sharing the caller's meter with every
recursive extension. -/
@[expose] def bounded {n : Nat} {budget : Budget} (base : Nat) (hb : base ≤ n)
    (S : Array (Perm n)) (hf : Chain.Fixed base S) : Computation budget (build base hb S hf) := do
  let normal ← normalizeBudgeted S
  if hbase : base < n then
    let orbit ← orbitBudgeted normal.val.generators ⟨base, hbase⟩ normal.val.symmetric
    let trivial ← emptyBudgeted (base + 1) hbase
    let result ← completeBudgeted hbase normal.val hf orbit.val
      (fun T d q hq => extend (base + 1) hbase T d q hq)
      (fun T d q hq => extendBudgeted (base + 1) hbase T d q hq)
      ⟨Seeds.empty normal.val.generators (base + 1), trivial.val, 0⟩
    return ⟨result.val, by
      unfold build
      simp only [hbase, ↓reduceDIte]
      rcases normal with ⟨normal, hn⟩
      cases hn
      rcases orbit with ⟨orbit, ho⟩
      cases ho
      rcases trivial with ⟨trivial, ht⟩
      cases ht
      exact result.property⟩
  else
    return ⟨terminal hbase hb normal.val hf, by
      unfold build
      simp only [hbase, ↓reduceDIte]
      rcases normal with ⟨normal, hn⟩
      cases hn
      rfl⟩

end Hex.PermGroup.Build

namespace Hex.PermGroup.Group

/-- Construct a group using the current producer meter, including every
recursive suffix extension. -/
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
@[expose] def buildBudgeted (budget : Execution.Budget) (S : Array (Perm n)) :
    Execution.Measured budget {G : Group n // G = ofGenerators S} :=
  Execution.run budget (construct S)

end Hex.PermGroup.Group

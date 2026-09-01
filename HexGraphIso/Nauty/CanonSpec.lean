/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Search
public import HexGraphIso.Nauty.Equivariance
public import HexGraphIso.Nauty.CellPerm

public section

/-!
The nauty-semantic canonical form as a total specification: the maximal
leaf key of the unpruned individualization-refinement tree.

A leaf key is the chain of refinement codes ending with the sentinel,
followed by the leaf's `g^lab` adjacency rows; keys compare
lexicographically, codes numerically and rows in nauty's row order.
The production search's canonical leaf realizes this maximum:

- a node whose chain is dominated (`compCanon < 0`) can never supply the
  canonical leaf, and those are exactly the nodes where nauty's
  history-dependent `firsttc` hint applies, so the specification's
  target-cell rule is hint-free; its nontrivial-join test reads the
  cell's neighbour-count multiset (`joinTest`), which agrees with
  nauty's first-vertex test on every equitable partition while being
  invariant under renamings and within-cell reordering — the
  certificate checker verifies agreement with the recorded target cell
  on each replayed node;
- the sentinel exceeds every real (cleaned) refinement code, which
  reproduces nauty's preference for shallower leaves on equal prefixes
  (`level < canonlevel` forcing `compCanon = 1`);
- children may be enumerated in any order under a maximum; the
  specification enumerates the target cell by position, which makes
  renaming-equivariance pointwise.

The branch guard is structural discreteness of the partition rather than
nauty's `numcells` counter; the two agree on every reachable state, and
the certificate checker replays concrete refinements where discreteness
is directly decidable.
-/

namespace Hex.GraphIso.Nauty

/-- A leaf key of the unpruned search tree: the level codes ending with
the sentinel, then the leaf's adjacency rows. -/
structure Key where
  /-- The refinement codes along the path, ending with the sentinel. -/
  codes : List Nat
  /-- The leaf's `g^lab` rows in nauty's row order. -/
  rows : List Nat
deriving Inhabited

/-- Lexicographic list comparison from an element comparison. -/
@[expose] def listCmp (cmp : Nat → Nat → Ordering) :
    List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match cmp a b with
    | .eq => listCmp cmp as bs
    | .lt => .lt
    | .gt => .gt

/-- Key order: level codes first, then rows in nauty's row order. -/
@[expose] def keyCmp (k1 k2 : Key) : Ordering :=
  match listCmp compare k1.codes k2.codes with
  | .eq => listCmp rowCmp k1.rows k2.rows
  | .lt => .lt
  | .gt => .gt

/-- The greater key, the first argument winning ties. -/
@[expose] def keyMax (k1 k2 : Key) : Key :=
  if keyCmp k1 k2 = .lt then k2 else k1

/-- The maximum of a list of keys, seeded by an initial key. -/
@[expose] def keysMax (k : Key) : List Key → Key
  | [] => k
  | k' :: rest => keysMax (keyMax k k') rest

/-- Discreteness of the partition at `level`: every cell a singleton. -/
@[expose] def discreteAt (ptn : Array Nat) (level nn : Nat) : Bool :=
  (cells ptn level nn).all fun p => p.1 == p.2

/-- The specification's nontrivial-join test: some member of the cell
starting at `c1` has a neighbour in the splitter set, and some member
misses part of it. Representative-independent, agreeing with nauty's
first-vertex test on every equitable partition. -/
@[expose] def joinTest (ctx : Ctx) (lab : Array Nat)
    (wset c1 c2 : Nat) : Bool :=
  (countsOf ctx lab wset c1 c2).any (fun c => decide (0 < c)) &&
    (countsOf ctx lab wset c1 c2).any
      (fun c => decide (c < popCount wset))

@[expose] def specBestcellRow (ctx : Ctx) (lab ptn : Array Nat)
    (level : Nat) (startArr : Array Nat) (workset v2 : Nat) :
    List Nat → Array Nat → Array Nat
  | [], bucket => bucket
  | v1 :: rest, bucket =>
    if joinTest ctx lab workset startArr[v1]!
        (cellEnd ptn level startArr[v1]!) then
      specBestcellRow ctx lab ptn level startArr workset v2 rest
        ((bucket.set! v1 (bucket[v1]! + 1)).set! v2 (bucket[v2]! + 1))
    else
      specBestcellRow ctx lab ptn level startArr workset v2 rest bucket

@[expose] def specBestcellRows (ctx : Ctx) (lab ptn : Array Nat)
    (level : Nat) (startArr : Array Nat) :
    List Nat → Array Nat → Array Nat
  | [], bucket => bucket
  | v2 :: rest, bucket =>
    specBestcellRows ctx lab ptn level startArr rest
      (specBestcellRow ctx lab ptn level startArr
        (worksetOf lab startArr[v2]! (cellEnd ptn level startArr[v2]!))
        v2 (List.range v2) bucket)

/-- The specification's `bestcell`: nauty's rule with the join test on
count multisets. -/
@[expose] def specBestcell (ctx : Ctx) (lab ptn : Array Nat)
    (level : Nat) : Nat :=
  let starts := ((cells ptn level ctx.n).filter
    fun (c1, c2) => c1 ≠ c2).map (·.1)
  let nnt := starts.length
  if nnt == 0 then
    ctx.n
  else
    let startArr := starts.toArray
    let bucket := specBestcellRows ctx lab ptn level startArr
      (List.range' 1 (nnt - 1)) (Array.replicate nnt 0)
    startArr[argmaxLoop bucket (List.range' 1 (nnt - 1)) 0 bucket[0]!]!

/-- The specification's hint-free target cell. -/
@[expose] def specTargetcell (ctx : Ctx) (lab ptn : Array Nat)
    (level tcLevel : Nat) : Nat :=
  if level ≤ tcLevel then
    specBestcell ctx lab ptn level
  else
    match (cells ptn level ctx.n).find? (fun (c1, c2) => c1 ≠ c2) with
    | some (c1, _) => c1
    | none => 0

/-- The specification's target cell with its contents and size. -/
@[expose] def specMaketargetcell (ctx : Ctx) (lab ptn : Array Nat)
    (level tcLevel : Nat) : Nat × Nat × Nat :=
  let i := specTargetcell ctx lab ptn level tcLevel
  let j := cellEnd ptn level (i + 1)
  (i, worksetOf lab i j, j - i + 1)

/-- The key of the maximal leaf of the unpruned search tree below one
node. -/
@[expose] def specNode (ctx : Ctx) (tcLevel : Nat) :
    Nat → Nat → Array Nat → Array Nat → Nat → Nat → Key
  | 0, _, _, _, _, _ => ⟨[], []⟩
  | fuel + 1, level, lab, ptn, active, numcells =>
    let rs := refine ctx level lab ptn active numcells
    if discreteAt rs.ptn level ctx.n then
      ⟨[rs.longcode, codeSentinel], leafRows ctx rs.lab⟩
    else
      let tcr := specMaketargetcell ctx rs.lab rs.ptn level tcLevel
      let children := (List.range tcr.2.2).map fun o =>
        let br := breakout rs.lab rs.ptn (level + 1) tcr.1 rs.lab[tcr.1 + o]!
        specNode ctx tcLevel fuel (level + 1) br.1 br.2.1 br.2.2
          (numcells + 1)
      match children with
      | [] => ⟨[], []⟩
      | c :: cs =>
        ⟨rs.longcode :: (keysMax c cs).codes, (keysMax c cs).rows⟩

/-- The canonical key of the unpruned nauty search on `n` vertices with
adjacency rows `g` and initial ordered partition `(lab0, cellEnds)`. -/
@[expose] def canonSpec (n : Nat) (g : Array Nat) (lab0 : Array Nat)
    (cellEnds : List Nat) : Key :=
  if n == 0 then
    ⟨[], []⟩
  else
    specNode { n, g } 100 n 1 lab0 (initPtn n (n + 2) cellEnds)
      (initActive cellEnds) cellEnds.length

variable {n k : Nat}

/-- The nauty-semantic canonical key of a coloured graph. -/
@[expose] def canonSpecKey (G : Colored n k) : Key :=
  canonSpec n (rowsOf G) (initialPartition G).1 (initialPartition G).2

/-! # The row order is a linear order -/

theorem testBit_lt_lowBit :
    ∀ (s i : Nat), i < lowBit s → s.testBit i = false
  | s, i, hi => by
    rw [lowBit_eq] at hi
    rcases Decidable.em (s = 0) with rfl | hs
    · rw [if_pos rfl] at hi
      omega
    · rw [if_neg hs] at hi
      rcases Decidable.em (s % 2 = 1) with ho | ho
      · rw [if_pos ho] at hi
        omega
      · rw [if_neg ho] at hi
        rcases i with _ | j
        · simp only [Nat.testBit_zero]
          simp
          omega
        · rw [Nat.testBit_add_one]
          exact testBit_lt_lowBit (s / 2) j (by omega)
  termination_by s => s
  decreasing_by omega

theorem lowBit_eq_of {s d : Nat} (hd : s.testBit d = true)
    (hlow : ∀ i, i < d → s.testBit i = false) : lowBit s = d := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hd
    simp at hd
  rcases Nat.lt_trichotomy (lowBit s) d with h | h | h
  · exact absurd (testBit_lowBit s hs0) (by rw [hlow _ h]; simp)
  · exact h
  · exact absurd hd (by rw [testBit_lt_lowBit s d h]; simp)

theorem testBit_eq_of_lt_lowBit_xor {a b i : Nat}
    (hi : i < lowBit (a ^^^ b)) : a.testBit i = b.testBit i := by
  have hx := testBit_lt_lowBit (a ^^^ b) i hi
  rw [Nat.testBit_xor] at hx
  rcases ha : a.testBit i with _ | _ <;>
    rcases hb : b.testBit i with _ | _ <;> simp_all

theorem xor_ne_zero_of_ne {a b : Nat} (hab : a ≠ b) : a ^^^ b ≠ 0 := by
  intro h
  refine hab (Nat.eq_of_testBit_eq fun i => ?_)
  have hx := congrArg (fun s => Nat.testBit s i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at hx
  rcases ha : a.testBit i with _ | _ <;>
    rcases hb : b.testBit i with _ | _ <;> simp_all

theorem testBit_ne_at_lowBit_xor {a b : Nat} (hab : a ≠ b) :
    a.testBit (lowBit (a ^^^ b)) ≠ b.testBit (lowBit (a ^^^ b)) := by
  have hx := testBit_lowBit _ (xor_ne_zero_of_ne hab)
  rw [Nat.testBit_xor] at hx
  intro he
  rw [he] at hx
  simp at hx

/-- Eliminate a strict row comparison. -/
theorem rowCmp_gt_elim {a b : Nat} (h : rowCmp a b = .gt) :
    a ≠ b ∧ a.testBit (lowBit (a ^^^ b)) = true ∧
      b.testBit (lowBit (a ^^^ b)) = false := by
  rw [rowCmp] at h
  split at h
  · cases h
  · next hne =>
    split at h
    · next hbit =>
      refine ⟨hne, hbit, ?_⟩
      have := testBit_ne_at_lowBit_xor hne
      rcases hb : b.testBit (lowBit (a ^^^ b)) with _ | _
      · rfl
      · exact absurd (hbit.trans hb.symm) this
    · cases h

/-- Introduce a strict row comparison from the least differing bit. -/
theorem rowCmp_gt_intro {a c d : Nat} (hd : a.testBit d = true)
    (hcd : c.testBit d = false)
    (hagree : ∀ i, i < d → a.testBit i = c.testBit i) :
    rowCmp a c = .gt := by
  have hne : a ≠ c := by
    intro h
    rw [h] at hd
    rw [hd] at hcd
    cases hcd
  have hlow : lowBit (a ^^^ c) = d := by
    refine lowBit_eq_of ?_ ?_
    · rw [Nat.testBit_xor, hd, hcd]
      rfl
    · intro i hi
      rw [Nat.testBit_xor, hagree i hi]
      simp
  rw [rowCmp, if_neg hne, hlow, if_pos hd]

theorem rowCmp_eq_iff {a b : Nat} : rowCmp a b = .eq ↔ a = b := by
  rw [rowCmp]
  split
  · next h => simp [h]
  · next h =>
    split <;> simp [h]

theorem rowCmp_gt_iff_lt {a b : Nat} :
    rowCmp a b = .gt ↔ rowCmp b a = .lt := by
  rcases Decidable.em (a = b) with rfl | hne
  · rw [rowCmp, if_pos rfl]
    simp
  · rw [rowCmp, if_neg hne, rowCmp, if_neg (Ne.symm hne),
      Nat.xor_comm b a]
    have hd := testBit_ne_at_lowBit_xor hne
    rcases ha : a.testBit (lowBit (a ^^^ b)) with _ | _ <;>
      rcases hb : b.testBit (lowBit (a ^^^ b)) with _ | _ <;>
        simp_all

/-- The row order is transitive. -/
theorem rowCmp_gt_trans {a b c : Nat} (h1 : rowCmp a b = .gt)
    (h2 : rowCmp b c = .gt) : rowCmp a c = .gt := by
  obtain ⟨hab, ha1, hb1⟩ := rowCmp_gt_elim h1
  obtain ⟨hbc, hb2, hc2⟩ := rowCmp_gt_elim h2
  rcases Nat.lt_trichotomy (lowBit (a ^^^ b)) (lowBit (b ^^^ c)) with
    hlt | heq | hgt
  · refine rowCmp_gt_intro ha1
      (by rw [← testBit_eq_of_lt_lowBit_xor hlt]; exact hb1)
      (fun i hi => ?_)
    rw [testBit_eq_of_lt_lowBit_xor hi]
    exact testBit_eq_of_lt_lowBit_xor (Nat.lt_trans hi hlt)
  · exfalso
    rw [heq] at hb1
    rw [hb1] at hb2
    cases hb2
  · refine rowCmp_gt_intro
      (by rw [testBit_eq_of_lt_lowBit_xor hgt]; exact hb2) hc2
      (fun i hi => ?_)
    rw [testBit_eq_of_lt_lowBit_xor (Nat.lt_trans hi hgt)]
    exact testBit_eq_of_lt_lowBit_xor hi

/-! # Lexicographic and key order -/

section ListOrder

variable {cmp : Nat → Nat → Ordering}

theorem listCmp_eq_iff (heq : ∀ a b, cmp a b = .eq ↔ a = b) :
    ∀ l1 l2 : List Nat, listCmp cmp l1 l2 = .eq ↔ l1 = l2
  | [], [] => by simp [listCmp]
  | [], _ :: _ => by simp [listCmp]
  | _ :: _, [] => by simp [listCmp]
  | a :: as, b :: bs => by
    rw [listCmp]
    rcases hc : cmp a b with _ | _ | _
    · refine ⟨fun h => Ordering.noConfusion h, fun h => ?_⟩
      injection h with h1 h2
      rw [(heq a b).mpr h1] at hc
      cases hc
    · dsimp only
      have hab := (heq a b).mp hc
      subst hab
      rw [listCmp_eq_iff heq as bs]
      simp
    · refine ⟨fun h => Ordering.noConfusion h, fun h => ?_⟩
      injection h with h1 h2
      rw [(heq a b).mpr h1] at hc
      cases hc

theorem listCmp_gt_iff_lt (heq : ∀ a b, cmp a b = .eq ↔ a = b)
    (hgl : ∀ a b, cmp a b = .gt ↔ cmp b a = .lt) :
    ∀ l1 l2 : List Nat,
      listCmp cmp l1 l2 = .gt ↔ listCmp cmp l2 l1 = .lt
  | [], [] => by simp [listCmp]
  | [], _ :: _ => by simp [listCmp]
  | _ :: _, [] => by simp [listCmp]
  | a :: as, b :: bs => by
    rw [listCmp, listCmp]
    rcases hc : cmp a b with _ | _ | _
    · rw [(hgl b a).mpr hc]
      simp
    · have hab := (heq a b).mp hc
      have hba := (heq b a).mpr hab.symm
      rw [hba]
      dsimp only
      exact listCmp_gt_iff_lt heq hgl as bs
    · rw [(hgl a b).mp hc]
      simp

theorem listCmp_gt_trans (heq : ∀ a b, cmp a b = .eq ↔ a = b)
    (htr : ∀ a b c, cmp a b = .gt → cmp b c = .gt → cmp a c = .gt) :
    ∀ l1 l2 l3 : List Nat, listCmp cmp l1 l2 = .gt →
      listCmp cmp l2 l3 = .gt → listCmp cmp l1 l3 = .gt
  | [], l2, l3 => by
    intro h1
    rcases l2 with _ | ⟨b, bs⟩ <;> simp [listCmp] at h1
  | _ :: _, [], l3 => by
    intro _ h2
    rcases l3 with _ | ⟨c, cs⟩ <;> simp [listCmp] at h2
  | a :: as, b :: bs, [] => by
    intro _ _
    rfl
  | a :: as, b :: bs, c :: cs => by
    intro h1 h2
    rw [listCmp] at h1 h2 ⊢
    rcases hab : cmp a b with _ | _ | _ <;> rw [hab] at h1
    · exact Ordering.noConfusion h1
    · have hab' := (heq a b).mp hab
      subst hab'
      rcases hac : cmp a c with _ | _ | _ <;> rw [hac] at h2
      · exact Ordering.noConfusion h2
      · exact listCmp_gt_trans heq htr as bs cs h1 h2
    · rcases hbc : cmp b c with _ | _ | _ <;> rw [hbc] at h2
      · exact Ordering.noConfusion h2
      · have hbc' := (heq b c).mp hbc
        subst hbc'
        rw [hab]
      · rw [htr a b c hab hbc]

end ListOrder

theorem keyCmp_eq_iff {k1 k2 : Key} : keyCmp k1 k2 = .eq ↔ k1 = k2 := by
  rw [keyCmp]
  rcases hc : listCmp compare k1.codes k2.codes with _ | _ | _
  · refine ⟨fun h => Ordering.noConfusion h, fun h => ?_⟩
    rw [h, (listCmp_eq_iff (fun a b => Nat.compare_eq_eq) _ _).mpr
      rfl] at hc
    cases hc
  · rw [listCmp_eq_iff (fun a b => rowCmp_eq_iff) k1.rows k2.rows]
    have hcodes := (listCmp_eq_iff (fun a b => Nat.compare_eq_eq)
      k1.codes k2.codes).mp hc
    constructor
    · intro hrows
      cases k1
      cases k2
      simp only at hcodes hrows
      rw [hcodes, hrows]
    · intro h
      rw [h]
  · refine ⟨fun h => Ordering.noConfusion h, fun h => ?_⟩
    rw [h, (listCmp_eq_iff (fun a b => Nat.compare_eq_eq) _ _).mpr
      rfl] at hc
    cases hc

theorem keyCmp_gt_iff_lt {k1 k2 : Key} :
    keyCmp k1 k2 = .gt ↔ keyCmp k2 k1 = .lt := by
  rw [keyCmp, keyCmp]
  have hnat : ∀ a b : Nat, compare a b = .gt ↔ compare b a = .lt := by
    intro a b
    rw [Nat.compare_eq_gt, Nat.compare_eq_lt]
  rcases hc : listCmp compare k1.codes k2.codes with _ | _ | _
  · have := (listCmp_gt_iff_lt (fun a b => Nat.compare_eq_eq) hnat
      k2.codes k1.codes).mpr hc
    rw [this]
    simp
  · have hcodes := (listCmp_eq_iff (fun a b => Nat.compare_eq_eq)
      k1.codes k2.codes).mp hc
    have hback : listCmp compare k2.codes k1.codes = .eq :=
      (listCmp_eq_iff (fun a b => Nat.compare_eq_eq) _ _).mpr
        hcodes.symm
    rw [hback]
    exact listCmp_gt_iff_lt (fun a b => rowCmp_eq_iff)
      (fun a b => rowCmp_gt_iff_lt) k1.rows k2.rows
  · have := (listCmp_gt_iff_lt (fun a b => Nat.compare_eq_eq) hnat
      k1.codes k2.codes).mp hc
    rw [this]
    simp

theorem keyCmp_gt_trans {k1 k2 k3 : Key} (h1 : keyCmp k1 k2 = .gt)
    (h2 : keyCmp k2 k3 = .gt) : keyCmp k1 k3 = .gt := by
  have hnattr : ∀ a b c : Nat, compare a b = .gt → compare b c = .gt →
      compare a c = .gt := by
    intro a b c ha hb
    rw [Nat.compare_eq_gt] at ha hb ⊢
    omega
  rw [keyCmp] at h1 h2 ⊢
  rcases hab : listCmp compare k1.codes k2.codes with _ | _ | _ <;>
    rw [hab] at h1
  · cases h1
  · have hcodes := (listCmp_eq_iff (fun a b => Nat.compare_eq_eq)
      _ _).mp hab
    rcases hbc : listCmp compare k2.codes k3.codes with _ | _ | _ <;>
      rw [hbc] at h2
    · cases h2
    · have hcodes2 := (listCmp_eq_iff (fun a b => Nat.compare_eq_eq)
        _ _).mp hbc
      rw [show listCmp compare k1.codes k3.codes = .eq from
        (listCmp_eq_iff (fun a b => Nat.compare_eq_eq) _ _).mpr
          (hcodes.trans hcodes2)]
      exact listCmp_gt_trans (fun a b => rowCmp_eq_iff)
        (fun a b c => rowCmp_gt_trans) k1.rows k2.rows k3.rows h1 h2
    · rw [show listCmp compare k1.codes k3.codes = .gt from
        hcodes ▸ hbc]
  · rcases hbc : listCmp compare k2.codes k3.codes with _ | _ | _ <;>
      rw [hbc] at h2
    · cases h2
    · have hcodes2 := (listCmp_eq_iff (fun a b => Nat.compare_eq_eq)
        _ _).mp hbc
      rw [show listCmp compare k1.codes k3.codes = .gt from
        hcodes2 ▸ hab]
    · rw [listCmp_gt_trans (fun a b => Nat.compare_eq_eq) hnattr
        k1.codes k2.codes k3.codes hab hbc]

theorem keyCmp_self (k : Key) : keyCmp k k = .eq := keyCmp_eq_iff.mpr rfl

theorem keyCmp_ge_trans {k1 k2 k3 : Key} (h1 : keyCmp k1 k2 ≠ .lt)
    (h2 : keyCmp k2 k3 ≠ .lt) : keyCmp k1 k3 ≠ .lt := by
  rcases hc1 : keyCmp k1 k2 with _ | _ | _
  · exact absurd hc1 h1
  · rw [keyCmp_eq_iff.mp hc1]
    exact h2
  · rcases hc2 : keyCmp k2 k3 with _ | _ | _
    · exact absurd hc2 h2
    · rw [← keyCmp_eq_iff.mp hc2]
      rw [hc1]
      simp
    · rw [keyCmp_gt_trans hc1 hc2]
      simp

theorem keyCmp_antisym {k1 k2 : Key} (h1 : keyCmp k1 k2 ≠ .lt)
    (h2 : keyCmp k2 k1 ≠ .lt) : k1 = k2 := by
  rcases hc : keyCmp k1 k2 with _ | _ | _
  · exact absurd hc h1
  · exact keyCmp_eq_iff.mp hc
  · exact absurd (keyCmp_gt_iff_lt.mp hc) h2

theorem keyMax_mem (x y : Key) : keyMax x y = x ∨ keyMax x y = y := by
  rw [keyMax]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem keyMax_not_lt_left (x y : Key) : keyCmp (keyMax x y) x ≠ .lt := by
  rw [keyMax]
  split
  · next h =>
    rw [keyCmp_gt_iff_lt.mpr h]
    simp
  · rw [keyCmp_self]
    simp

theorem keyMax_not_lt_right (x y : Key) :
    keyCmp (keyMax x y) y ≠ .lt := by
  rw [keyMax]
  split
  · rw [keyCmp_self]
    simp
  · next h =>
    exact h

/-- Folding the pairwise maximum is right-commutative, so the running
maximum is permutation-invariant. -/
theorem keyMax_comm2 (b a1 a2 : Key) :
    keyMax (keyMax b a1) a2 = keyMax (keyMax b a2) a1 := by
  have hge1 : ∀ x y z : Key, keyCmp (keyMax (keyMax x y) z) x ≠ .lt :=
    fun x y z => keyCmp_ge_trans (keyMax_not_lt_left _ _)
      (keyMax_not_lt_left _ _)
  have hge2 : ∀ x y z : Key, keyCmp (keyMax (keyMax x y) z) y ≠ .lt :=
    fun x y z => keyCmp_ge_trans (keyMax_not_lt_left _ _)
      (keyMax_not_lt_right _ _)
  have hge3 : ∀ x y z : Key, keyCmp (keyMax (keyMax x y) z) z ≠ .lt :=
    fun x y z => keyMax_not_lt_right _ _
  refine keyCmp_antisym ?_ ?_
  · rcases keyMax_mem (keyMax b a2) a1 with hm | hm <;> rw [hm]
    · rcases keyMax_mem b a2 with hm2 | hm2 <;> rw [hm2]
      · exact hge1 b a1 a2
      · exact hge3 b a1 a2
    · exact hge2 b a1 a2
  · rcases keyMax_mem (keyMax b a1) a2 with hm | hm <;> rw [hm]
    · rcases keyMax_mem b a1 with hm2 | hm2 <;> rw [hm2]
      · exact hge1 b a2 a1
      · exact hge3 b a2 a1
    · exact hge2 b a2 a1

theorem keysMax_eq_foldl : ∀ (l : List Key) (k : Key),
    keysMax k l = l.foldl keyMax k
  | [], _ => rfl
  | k' :: rest, k => by
    rw [keysMax, List.foldl_cons]
    exact keysMax_eq_foldl rest _

/-- The running key maximum is invariant under permutation of the
list. -/
theorem keysMax_perm {l l' : List Key} (h : l.Perm l') (k : Key) :
    keysMax k l = keysMax k l' := by
  rw [keysMax_eq_foldl, keysMax_eq_foldl]
  exact h.foldl_eq' (fun x _ y _ z => keyMax_comm2 z x y) k

/-! # Equivariance of the spec target-cell rule -/

theorem joinTest_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hg : RowsMap σ ctx.g ctx'.g) {lab : Array Nat} (hlab : LabOk lab n)
    {wset : Nat} (hws : wset < 2 ^ n) {c1 c2 : Nat}
    (h2 : c2 < lab.size) :
    joinTest ctx' (lab.map σ.toFun) (image σ n wset) c1 c2 =
      joinTest ctx lab wset c1 c2 := by
  rw [joinTest, joinTest, countsOf_map σ hg hlab hws h2,
    popCount_image σ hws (image_lt σ _)]

theorem specBestcellRow_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hg : RowsMap σ ctx.g ctx'.g) {lab ptn : Array Nat} {level : Nat}
    (hlab : LabOk lab n) (hsl : lab.size = n) (hsp : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) {startArr : Array Nat}
    (hstart : ∀ v : Nat, startArr[v]! < n) {workset : Nat}
    (hws : workset < 2 ^ n) (v2 : Nat) :
    ∀ (vs : List Nat) (bucket : Array Nat),
      specBestcellRow ctx' (lab.map σ.toFun) ptn level startArr
          (image σ n workset) v2 vs bucket =
        specBestcellRow ctx lab ptn level startArr workset v2 vs bucket
  | [], _ => rfl
  | v1 :: rest, bucket => by
    have hce : cellEnd ptn level startArr[v1]! < lab.size := by
      have := cellEnd_lt (ptn := ptn) (level := level)
        (i := startArr[v1]!) (by have := hstart v1; omega) hend
      omega
    rw [specBestcellRow, specBestcellRow,
      joinTest_map σ hg hlab hws hce]
    rcases hj : joinTest ctx lab workset startArr[v1]!
        (cellEnd ptn level startArr[v1]!) with _ | _
    · simp only [Bool.false_eq_true, if_false]
      exact specBestcellRow_map σ hg hlab hsl hsp hend hstart hws v2
        rest bucket
    · simp only [if_true]
      exact specBestcellRow_map σ hg hlab hsl hsp hend hstart hws v2
        rest _

theorem specBestcellRows_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hg : RowsMap σ ctx.g ctx'.g) {lab ptn : Array Nat} {level : Nat}
    (hlab : LabOk lab n) (hsl : lab.size = n) (hsp : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) {startArr : Array Nat}
    (hstart : ∀ v : Nat, startArr[v]! < n) :
    ∀ (vs : List Nat) (bucket : Array Nat),
      specBestcellRows ctx' (lab.map σ.toFun) ptn level startArr vs
          bucket =
        specBestcellRows ctx lab ptn level startArr vs bucket
  | [], _ => rfl
  | v2 :: rest, bucket => by
    rw [specBestcellRows, specBestcellRows]
    have hce : cellEnd ptn level startArr[v2]! < n := by
      have := cellEnd_lt (ptn := ptn) (level := level)
        (i := startArr[v2]!) (by have := hstart v2; omega) hend
      omega
    rw [worksetOf_map σ hlab (lo := startArr[v2]!)
      (hi := cellEnd ptn level startArr[v2]!) (by omega)]
    rw [specBestcellRow_map σ hg hlab hsl hsp hend hstart
      (worksetOf_lt hlab (lo := startArr[v2]!)
        (hi := cellEnd ptn level startArr[v2]!) (by omega)) v2
      (List.range v2) bucket]
    exact specBestcellRows_map σ hg hlab hsl hsp hend hstart rest _

/-- The specification's `bestcell` is position-valued and invariant
under a renaming. -/
theorem specBestcell_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    {lab ptn : Array Nat} (hlab : LabOk lab n) (hsl : lab.size = n)
    (hsp : ptn.size = n) {level : Nat}
    (hend : ptn[ptn.size - 1]! ≤ level) :
    specBestcell ctx' (lab.map σ.toFun) ptn level =
      specBestcell ctx lab ptn level := by
  rw [specBestcell, specBestcell]
  dsimp only
  rw [hn', hn]
  have hml : ∀ x ∈ ((cells ptn level n).filter
      fun (c1, c2) => c1 ≠ c2).map (·.1), x < n := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hpc := List.mem_filter.mp hp
    have hb := cells_bound (nn := n) (by omega) hend p hpc.1
    have hle := cells_le p hpc.1
    omega
  rcases hnnt : ((((cells ptn level n).filter fun (c1, c2) => c1 ≠ c2).map
      (·.1)).length == 0) with _ | _
  · simp only [Bool.false_eq_true, if_false]
    have hlen0 : (((cells ptn level n).filter
        fun (c1, c2) => c1 ≠ c2).map (·.1)).length ≠ 0 := by
      simpa using hnnt
    have hn0 : 0 < n := by
      have hpos : 0 < (((cells ptn level n).filter
          fun (c1, c2) => c1 ≠ c2).map (·.1)).length :=
        Nat.pos_of_ne_zero hlen0
      exact Nat.lt_of_le_of_lt (Nat.zero_le _)
        (hml _ (List.getElem_mem hpos))
    rw [specBestcellRows_map σ hg hlab hsl hsp hend
      (getElem!_list_lt hml hn0)]
  · simp only [if_true]

/-- The specification's target cell is position-valued and invariant
under a renaming. -/
theorem specTargetcell_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    {lab ptn : Array Nat} (hlab : LabOk lab n) (hsl : lab.size = n)
    (hsp : ptn.size = n) {level tcLevel : Nat}
    (hend : ptn[ptn.size - 1]! ≤ level) :
    specTargetcell ctx' (lab.map σ.toFun) ptn level tcLevel =
      specTargetcell ctx lab ptn level tcLevel := by
  rw [specTargetcell, specTargetcell]
  rcases Decidable.em (level ≤ tcLevel) with hB | hB
  · rw [if_pos hB, if_pos hB]
    exact specBestcell_map σ hn hn' hg hlab hsl hsp hend
  · rw [if_neg hB, if_neg hB, hn', hn]

/-- The specification's target-cell data transports position and size
unchanged and the cell set to its image. -/
theorem specMaketargetcell_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    {lab ptn : Array Nat} (hlab : LabOk lab n) (hsl : lab.size = n)
    (hsp : ptn.size = n) {level tcLevel : Nat}
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hi : specTargetcell ctx lab ptn level tcLevel + 1 < n) :
    specMaketargetcell ctx' (lab.map σ.toFun) ptn level tcLevel =
      ((specMaketargetcell ctx lab ptn level tcLevel).1,
        image σ n (specMaketargetcell ctx lab ptn level tcLevel).2.1,
        (specMaketargetcell ctx lab ptn level tcLevel).2.2) := by
  rw [specMaketargetcell, specMaketargetcell]
  rw [specTargetcell_map σ hn hn' hg hlab hsl hsp hend]
  have hce : cellEnd ptn level
      (specTargetcell ctx lab ptn level tcLevel + 1) < n := by
    have := cellEnd_lt (ptn := ptn) (level := level)
      (i := specTargetcell ctx lab ptn level tcLevel + 1) (by omega)
      hend
    omega
  rw [worksetOf_map σ hlab
    (lo := specTargetcell ctx lab ptn level tcLevel)
    (hi := cellEnd ptn level
      (specTargetcell ctx lab ptn level tcLevel + 1))
    (by omega)]

/-- The specification's `bestcell` returns a nonsingleton cell start
when one exists. -/
theorem specBestcell_mem {ctx : Ctx} {lab ptn : Array Nat} {level : Nat}
    (hex : ((cells ptn level ctx.n).filter
      fun (c1, c2) => c1 ≠ c2) ≠ []) :
    specBestcell ctx lab ptn level ∈
      ((cells ptn level ctx.n).filter fun (c1, c2) => c1 ≠ c2).map
        (·.1) := by
  have hlen : (((cells ptn level ctx.n).filter
      fun (c1, c2) => c1 ≠ c2).map (·.1)).length ≠ 0 := by
    rw [List.length_map]
    intro h0
    exact hex (List.length_eq_zero_iff.mp h0)
  have hcond : ((((cells ptn level ctx.n).filter
      fun (c1, c2) => c1 ≠ c2).map (·.1)).length == 0) = false := by
    simpa using hlen
  simp only [specBestcell, hcond, Bool.false_eq_true, if_false]
  refine argmax_start_mem (by simpa using hlen) _ _ _ ?_
  intro j hj
  have h1 := List.mem_range'_1.mp hj
  have h2 : (((cells ptn level ctx.n).filter
      fun x => decide (x.1 ≠ x.2)).map (·.1)).length ≠ 0 := by
    simpa using hlen
  omega

/-- With a nonsingleton cell present, the specification's target cell
is a nonsingleton cell start. -/
theorem specTargetcell_nontrivial {ctx : Ctx} {lab ptn : Array Nat}
    {level tcLevel : Nat}
    (hex : ∃ p ∈ cells ptn level ctx.n, p.1 ≠ p.2) :
    ∃ p ∈ cells ptn level ctx.n, p.1 ≠ p.2 ∧
      specTargetcell ctx lab ptn level tcLevel = p.1 := by
  have hfne : ((cells ptn level ctx.n).filter
      fun (c1, c2) => c1 ≠ c2) ≠ [] := by
    rcases hex with ⟨p, hpm, hpne⟩
    intro hnil
    have hmem : p ∈ ((cells ptn level ctx.n).filter
        fun (c1, c2) => c1 ≠ c2) := by
      rw [List.mem_filter]
      exact ⟨hpm, by simpa using hpne⟩
    rw [hnil] at hmem
    cases hmem
  rw [specTargetcell]
  rcases Decidable.em (level ≤ tcLevel) with hB | hB
  · rw [if_pos hB]
    have hm := specBestcell_mem (lab := lab) hfne
    rcases List.mem_map.mp hm with ⟨p, hpf, hp1⟩
    have hpc := List.mem_filter.mp hpf
    exact ⟨p, hpc.1, by simpa using hpc.2, hp1.symm⟩
  · rw [if_neg hB]
    rcases hf : (cells ptn level ctx.n).find? (fun (c1, c2) => c1 ≠ c2)
      with _ | q
    · rcases hex with ⟨p, hpm, hpne⟩
      have := List.find?_eq_none.mp hf p hpm
      simp [hpne] at this
    · rw [hf]
      dsimp only
      rcases q with ⟨c1, c2⟩
      refine ⟨(c1, c2), List.mem_of_find?_eq_some hf, ?_, rfl⟩
      have := List.find?_some hf
      simpa using this

/-! # Cell-contents invariance of the spec target-cell rule -/

theorem joinTest_perm {ctx : Ctx} {lab lab' : Array Nat}
    {wset c1 c2 : Nat}
    (hseg : (segN lab c1 (c2 + 1 - c1)).Perm
      (segN lab' c1 (c2 + 1 - c1))) :
    joinTest ctx lab wset c1 c2 = joinTest ctx lab' wset c1 c2 := by
  rw [joinTest, joinTest, countsOf_eq_map, countsOf_eq_map]
  have hp := hseg.map fun v => popCount (wset &&& ctx.g[v]!)
  have hany : ∀ p : Nat → Bool,
      ((segN lab c1 (c2 + 1 - c1)).map
        fun v => popCount (wset &&& ctx.g[v]!)).any p =
      ((segN lab' c1 (c2 + 1 - c1)).map
        fun v => popCount (wset &&& ctx.g[v]!)).any p := by
    intro p
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    exact ⟨fun ⟨x, hx, hpx⟩ => ⟨x, hp.mem_iff.mp hx, hpx⟩,
      fun ⟨x, hx, hpx⟩ => ⟨x, hp.mem_iff.mpr hx, hpx⟩⟩
  rw [hany, hany]

theorem specBestcellRow_perm {ctx : Ctx} {lab lab' ptn : Array Nat}
    {level : Nat} (hcp : cellsPerm ptn level lab lab')
    (hend : ptn[ptn.size - 1]! ≤ level) {startArr : Array Nat}
    (hstart : ∀ v : Nat, startArr[v]! < ptn.size)
    (hstart2 : ∀ v : Nat, startArr[v]! = 0 ∨
      ptn[startArr[v]! - 1]! ≤ level) (workset v2 : Nat) :
    ∀ (vs : List Nat) (bucket : Array Nat),
      specBestcellRow ctx lab ptn level startArr workset v2 vs bucket =
        specBestcellRow ctx lab' ptn level startArr workset v2 vs bucket
  | [], _ => rfl
  | v1 :: rest, bucket => by
    rw [specBestcellRow, specBestcellRow]
    have hic := isCell_cellEnd (hstart v1) (hstart2 v1) hend
    rw [joinTest_perm (hcp _ _ hic)]
    rcases hj : joinTest ctx lab' workset startArr[v1]!
        (cellEnd ptn level startArr[v1]!) with _ | _
    · simp only [Bool.false_eq_true, if_false]
      exact specBestcellRow_perm hcp hend hstart hstart2 workset v2
        rest bucket
    · simp only [if_true]
      exact specBestcellRow_perm hcp hend hstart hstart2 workset v2
        rest _

theorem specBestcellRows_perm {ctx : Ctx} {lab lab' ptn : Array Nat}
    {level : Nat} (hcp : cellsPerm ptn level lab lab')
    (hend : ptn[ptn.size - 1]! ≤ level) {startArr : Array Nat}
    (hstart : ∀ v : Nat, startArr[v]! < ptn.size)
    (hstart2 : ∀ v : Nat, startArr[v]! = 0 ∨
      ptn[startArr[v]! - 1]! ≤ level) :
    ∀ (vs : List Nat) (bucket : Array Nat),
      specBestcellRows ctx lab ptn level startArr vs bucket =
        specBestcellRows ctx lab' ptn level startArr vs bucket
  | [], _ => rfl
  | v2 :: rest, bucket => by
    rw [specBestcellRows, specBestcellRows]
    have hic := isCell_cellEnd (hstart v2) (hstart2 v2) hend
    rw [worksetOf_perm (hcp _ _ hic),
      specBestcellRow_perm hcp hend hstart hstart2 _ v2
        (List.range v2) bucket]
    exact specBestcellRows_perm hcp hend hstart hstart2 rest _

/-- The specification's `bestcell` depends on the labelling only through
cell contents. -/
theorem specBestcell_perm {ctx : Ctx} {lab lab' ptn : Array Nat}
    {level : Nat} (hcp : cellsPerm ptn level lab lab')
    (hnn : ctx.n ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level) :
    specBestcell ctx lab ptn level = specBestcell ctx lab' ptn level := by
  rw [specBestcell, specBestcell]
  dsimp only
  rcases hnnt : ((((cells ptn level ctx.n).filter
      fun (c1, c2) => c1 ≠ c2).map (·.1)).length == 0) with _ | _
  · simp only [Bool.false_eq_true, if_false]
    have hml : ∀ x ∈ ((cells ptn level ctx.n).filter
        fun (c1, c2) => c1 ≠ c2).map (·.1),
        x < ptn.size ∧ (x = 0 ∨ ptn[x - 1]! ≤ level) := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
      have hpc := List.mem_filter.mp hp
      have hb := cells_bound hnn hend p hpc.1
      have hle := cells_le p hpc.1
      have hic := cells_isCell hnn hend p hpc.1
      exact ⟨by omega, hic.2.1⟩
    have hlen0 : (((cells ptn level ctx.n).filter
        fun (c1, c2) => c1 ≠ c2).map (·.1)).length ≠ 0 := by
      simpa using hnnt
    have hstart : ∀ v : Nat, ((((cells ptn level ctx.n).filter
        fun (c1, c2) => c1 ≠ c2).map (·.1)).toArray)[v]! < ptn.size := by
      intro v
      rw [List.getElem!_toArray]
      rcases Nat.lt_or_ge v (((cells ptn level ctx.n).filter
          fun (c1, c2) => c1 ≠ c2).map (·.1)).length with hv | hv
      · rw [getElem!_pos _ v hv]
        exact (hml _ (List.getElem_mem hv)).1
      · rw [getElem!_neg _ _ (by omega)]
        have hpos : 0 < (((cells ptn level ctx.n).filter
            fun (c1, c2) => c1 ≠ c2).map (·.1)).length :=
          Nat.pos_of_ne_zero hlen0
        have h1 := (hml _ (List.getElem_mem hpos)).1
        show (0 : Nat) < ptn.size
        omega
    have hstart2 : ∀ v : Nat, ((((cells ptn level ctx.n).filter
        fun (c1, c2) => c1 ≠ c2).map (·.1)).toArray)[v]! = 0 ∨
        ptn[((((cells ptn level ctx.n).filter
          fun (c1, c2) => c1 ≠ c2).map (·.1)).toArray)[v]! - 1]! ≤
            level := by
      intro v
      rw [List.getElem!_toArray]
      rcases Nat.lt_or_ge v (((cells ptn level ctx.n).filter
          fun (c1, c2) => c1 ≠ c2).map (·.1)).length with hv | hv
      · rw [getElem!_pos _ v hv]
        exact (hml _ (List.getElem_mem hv)).2
      · rw [getElem!_neg _ _ (by omega)]
        exact Or.inl rfl
    rw [specBestcellRows_perm hcp hend hstart hstart2]
  · simp only [if_true]

/-- The specification's target cell depends on the labelling only
through cell contents. -/
theorem specTargetcell_perm {ctx : Ctx} {lab lab' ptn : Array Nat}
    {level tcLevel : Nat} (hcp : cellsPerm ptn level lab lab')
    (hnn : ctx.n ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level) :
    specTargetcell ctx lab ptn level tcLevel =
      specTargetcell ctx lab' ptn level tcLevel := by
  rw [specTargetcell, specTargetcell]
  rcases Decidable.em (level ≤ tcLevel) with hB | hB
  · rw [if_pos hB, if_pos hB]
    exact specBestcell_perm hcp hnn hend
  · rw [if_neg hB, if_neg hB]

/-! # Leaves and children under cell equivalence -/

theorem cells_go_cover {ptn : Array Nat} {level nn : Nat} :
    ∀ (fuel c1 i : Nat), c1 ≤ i → i < nn → nn ≤ fuel + c1 →
      ∃ p ∈ cells.go ptn level nn fuel c1, p.1 ≤ i ∧ i ≤ p.2
  | 0, c1, i, hc, hi, hf => absurd hf (by omega)
  | fuel + 1, c1, i, hc, hi, hf => by
    rw [cells.go, if_pos (by omega)]
    rcases Nat.le_total i (cellEnd ptn level c1) with hle | hle2
    · exact ⟨(c1, cellEnd ptn level c1), by simp, hc, hle⟩
    · rcases Nat.eq_or_lt_of_le hle2 with heq | hgt
      · exact ⟨(c1, cellEnd ptn level c1), by simp, hc, by omega⟩
      · have hge : c1 ≤ cellEnd ptn level c1 := cellEnd_ge
        obtain ⟨p, hpm, hp⟩ := cells_go_cover (ptn := ptn)
          (level := level) fuel (cellEnd ptn level c1 + 1) i (by omega)
          hi (by omega)
        exact ⟨p, by simp [hpm], hp⟩

theorem cells_cover {ptn : Array Nat} {level nn : Nat} (i : Nat)
    (hi : i < nn) : ∃ p ∈ cells ptn level nn, p.1 ≤ i ∧ i ≤ p.2 := by
  rw [cells]
  exact cells_go_cover nn 0 i (Nat.zero_le i) hi (by omega)

/-- On a discrete partition, cell-equivalent labellings agree
pointwise. -/
theorem discrete_pointwise {ptn : Array Nat} {level nn : Nat}
    {lab lab' : Array Nat} (hcp : cellsPerm ptn level lab lab')
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    (hdisc : discreteAt ptn level nn = true) :
    ∀ i, i < nn → lab[i]! = lab'[i]! := by
  intro i hi
  obtain ⟨p, hpm, hp1, hp2⟩ := cells_cover i hi
  have hsingle : p.1 = p.2 := by
    rw [discreteAt, List.all_eq_true] at hdisc
    have := hdisc p hpm
    simpa using this
  have hic1 : IsCell ptn level i 1 := by
    have hic := cells_isCell hnn hend p hpm
    rw [show p.2 + 1 - p.1 = 1 by omega] at hic
    rw [show i = p.1 by omega]
    exact hic
  exact cellsPerm_singleton hcp hic1

theorem invPerm_congr {lab lab' : Array Nat} (hsz : lab.size = lab'.size)
    (h : ∀ i, i < lab.size → lab[i]! = lab'[i]!) :
    invPerm lab = invPerm lab' := by
  rw [invPerm, invPerm, hsz]
  suffices hgo : ∀ (is : List Nat) (inv : Array Nat),
      (∀ i ∈ is, i < lab.size) →
      invPerm.go lab is inv = invPerm.go lab' is inv by
    exact hgo _ _ (fun i hi => by
      have := List.mem_range.mp hi
      omega)
  intro is
  induction is with
  | nil => exact fun inv _ => rfl
  | cons i rest ih =>
    intro inv hb
    rw [invPerm.go, invPerm.go, h i (hb i (by simp))]
    exact ih _ (fun j hj => hb j (by simp [hj]))

theorem leafRows_congr {ctx : Ctx} {lab lab' : Array Nat}
    (hsz : lab.size = lab'.size) (hnn : ctx.n ≤ lab.size)
    (h : ∀ i, i < lab.size → lab[i]! = lab'[i]!) :
    leafRows ctx lab = leafRows ctx lab' := by
  rw [leafRows, leafRows, invPerm_congr hsz h]
  refine List.map_congr_left fun i hi => ?_
  rw [h i (by have := List.mem_range.mp hi; omega)]

theorem range_map_eq_segN_map (lab : Array Nat) (lo len : Nat)
    (F : Nat → Key) :
    ((List.range len).map fun o => F lab[lo + o]!) =
      (segN lab lo len).map F := by
  rw [segN, List.map_map]
  exact List.map_congr_left fun o _ => rfl

theorem keysMax_mem : ∀ (l : List Key) (k : Key),
    keysMax k l = k ∨ keysMax k l ∈ l
  | [], _ => Or.inl rfl
  | k' :: rest, k => by
    rw [keysMax]
    rcases keysMax_mem rest (keyMax k k') with he | hm
    · rw [he]
      rcases keyMax_mem k k' with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (by rw [h2]; simp)
    · exact Or.inr (by simp [hm])

theorem keysMax_ge : ∀ (l : List Key) (k : Key) (y : Key),
    (y = k ∨ y ∈ l) → keyCmp (keysMax k l) y ≠ .lt
  | [], k, y, hy => by
    rcases hy with rfl | hm
    · rw [keysMax, keyCmp_self]
      simp
    · cases hm
  | k' :: rest, k, y, hy => by
    rw [keysMax]
    rcases hy with rfl | hm
    · exact keyCmp_ge_trans
        (keysMax_ge rest (keyMax y k') (keyMax y k') (Or.inl rfl))
        (keyMax_not_lt_left y k')
    · rcases List.mem_cons.mp hm with rfl | hm2
      · exact keyCmp_ge_trans
          (keysMax_ge rest (keyMax k y) (keyMax k y) (Or.inl rfl))
          (keyMax_not_lt_right k y)
      · exact keysMax_ge rest (keyMax k k') y (Or.inr hm2)

/-- The head-seeded key maximum is invariant under permutation of the
whole list. -/
theorem keysMax_cons_perm {c c' : Key} {cs cs' : List Key}
    (h : (c :: cs).Perm (c' :: cs')) :
    keysMax c cs = keysMax c' cs' := by
  have hdir : ∀ {d d' : Key} {ds ds' : List Key},
      (d :: ds).Perm (d' :: ds') →
      keyCmp (keysMax d ds) (keysMax d' ds') ≠ .lt := by
    intro d d' ds ds' hp
    have hm' := keysMax_mem ds' d'
    have hmem : keysMax d' ds' = d ∨ keysMax d' ds' ∈ ds := by
      have hin : keysMax d' ds' ∈ d :: ds := hp.mem_iff.mpr (by
        rcases hm' with he | hm2
        · rw [he]
          simp
        · simp [hm2])
      rcases List.mem_cons.mp hin with he | hm2
      · exact Or.inl he
      · exact Or.inr hm2
    exact keysMax_ge ds d _ hmem
  exact keyCmp_antisym (hdir h) (hdir h.symm)

/-! # Equivariance -/

/-- The unpruned search tree's maximal leaf key is invariant under a
vertex renaming: on the renamed graph with the transported labelling,
every node produces the same key. -/
theorem specNode_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat) (active numcells : Nat),
      lab.size = n → LabOk lab n → ptn.size = n → active < 2 ^ n →
      ptn[ptn.size - 1]! ≤ level →
      specNode ctx' tcLevel fuel level (lab.map σ.toFun) ptn active
          numcells =
        specNode ctx tcLevel fuel level lab ptn active numcells
  | 0, _, _, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, level, lab, ptn, active, numcells, hsl, hlab, hsp, hact,
      hend => by
    rw [specNode, specNode,
      refine_map σ hn hn' hg level lab ptn active numcells hsl hlab hsp
        hact hend]
    dsimp only
    rw [hn', hn]
    have hst := refine_stOk (ctx := ctx) hn (level := level)
      (numcells := numcells) hsl hlab hsp hact hend
    generalize hR : refine ctx level lab ptn active numcells = R
    rw [hR] at hst
    rcases hdisc : discreteAt R.ptn level n with _ | _
    · simp only [Bool.false_eq_true, if_false]
      obtain ⟨p, hpm, hpne, hptc⟩ := specTargetcell_nontrivial
        (lab := R.lab) (tcLevel := tcLevel)
        (by
          rw [discreteAt, List.all_eq_false] at hdisc
          rcases hdisc with ⟨q, hqm, hq⟩
          exact ⟨q, by rw [hn]; exact hqm, by simpa using hq⟩)
      have htc1 : specTargetcell ctx R.lab R.ptn level tcLevel + 1 < n := by
        have hb := cells_bound (nn := ctx.n)
          (by
            have h1 := hst.ptnSize
            have h2 := hn
            omega)
          hst.ptnEnd p hpm
        have hl := cells_le p hpm
        have h1 := hst.ptnSize
        rw [hptc]
        omega
      rw [specMaketargetcell_map σ hn hn' hg hst.labOk hst.labSize
        hst.ptnSize hst.ptnEnd htc1]
      dsimp only
      generalize hM : specMaketargetcell ctx R.lab R.ptn level tcLevel = M
      have hM1 : M.1 = specTargetcell ctx R.lab R.ptn level tcLevel := by
        rw [← hM]
        rfl
      have hM22 : M.2.2 = cellEnd R.ptn level
          (specTargetcell ctx R.lab R.ptn level tcLevel + 1) -
            specTargetcell ctx R.lab R.ptn level tcLevel + 1 := by
        rw [← hM]
        rfl
      have htc1' : M.1 + 1 < n := by
        rw [hM1]
        exact htc1
      have hjlt : cellEnd R.ptn level (M.1 + 1) < n := by
        have h1 := cellEnd_lt (ptn := R.ptn) (level := level)
          (i := M.1 + 1)
          (by
            have := hst.ptnSize
            omega)
          hst.ptnEnd
        have h2 := hst.ptnSize
        omega
      have hjge : M.1 + 1 ≤ cellEnd R.ptn level (M.1 + 1) := cellEnd_ge
      congr 1
      refine List.map_congr_left fun o ho => ?_
      have ho' := List.mem_range.mp ho
      have hpos : M.1 + o < R.lab.size := by
        have h1 := hst.labSize
        rw [hM22, ← hM1] at ho'
        omega
      rw [getElem!_map_of_lt σ.toFun R.lab hpos,
        breakout_map σ hst.labOk ⟨M.1 + o, by omega, hpos, rfl⟩]
      dsimp only
      exact specNode_map σ hn hn' hg tcLevel fuel (level + 1) _ _ _ _
        (show ((breakout R.lab R.ptn (level + 1) M.1
              R.lab[M.1 + o]!).1).size = n from
          ((breakout_ok hst.labOk (by omega) (hst.labOk _ hpos)).1).trans
            hst.labSize)
        ((breakout_ok hst.labOk (by omega) (hst.labOk _ hpos)).2)
        (by
          show (R.ptn.set! M.1 (level + 1)).size = n
          rw [Array.size_set!]
          exact hst.ptnSize)
        (by
          show insert 0 M.1 < 2 ^ n
          exact insert_lt (Nat.two_pow_pos n) (by omega))
        (by
          show (R.ptn.set! M.1 (level + 1))[(R.ptn.set! M.1
              (level + 1)).size - 1]! ≤ level + 1
          exact ptnEnd_set! (Nat.le_succ_of_le hst.ptnEnd))
    · simp only [if_true]
      rw [leafRows_map σ hn hn' hg hst.labOk hst.labSize]

end Hex.GraphIso.Nauty

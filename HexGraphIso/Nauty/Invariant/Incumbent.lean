/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Domination
public import HexGraphIso.Nauty.Cert.CertStore
import all HexGraphIso.Nauty.Search.Search

public section

/-!
The incumbent read off the search state: the per-node facts the
quartet induction consumes, and the frame lemmas saying a node's own
work outside its child loop leaves the incumbent alone.
-/

/-!
Per-node facts about the search state: the incumbent read off the
state, the generator a code-one leaf records, the positions a call
leaves fixed, and the root.

`nodeKey` is a node's subtree key under its path codes. `stInc` reads
the incumbent from `SearchSt` and `stInc_eq_ghost` identifies it with
the ghost incumbent `ghostInc` that the induction carries.
`firstScatter_get` reads off the generator `processnode` builds as
`workperm[firstlab[i]] := lab[i]`, so the permutation maps `firstlab`
to `lab` pointwise by construction. The `breakout` lemmas say a
singleton cell away from the target cell survives both refinement and
individualization. `rootSt` and `rootOut` are the initial state and the
run's output, and `stInc_final` and `nodeKey_root` read the incumbent
and the subtree key there.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The subtree key of a node, under its path codes. -/
@[expose] def nodeKey (ctx : Ctx n) (tcLevel fuel level : Nat)
    (cs : List Nat) (st : SearchSt n) (numcells : Nat) : Key n :=
  prefixKey cs
    (specNode ctx tcLevel fuel level st.lab st.ptn st.active numcells)

/-! # The incumbent, read off the state

The incumbent has to be an `Option`, because before the first leaf is
installed there is no incumbent and the state's degenerate contents do
not stand in for one. That is not a stylistic choice: at the root
`canonlevel` is `0`, so the code list is empty and `incKey` would read
`⟨[codeSentinel], _⟩`. Every real refinement code is strictly below
`codeSentinel` (`refine_longcode_lt`), so `listCmp` compares
`codeSentinel` against a real first code and answers `.gt`. The
degenerate reading therefore *outranks every reachable leaf key*, and
`keyMax` keeps it. An absorption equation stated with it would assert
that the final incumbent is the degenerate one, which is false as soon
as the search installs anything.

`CanonSpec` already carries the fix: `incMax : Option (Key n) → Key n →
Key n` with `none` as the bottom.  The semantic induction threads that
option explicitly.  It can
be read back from the imperative state only outside the temporary
upward-comparison window, where `canoncode` contains path codes rather
than the installed incumbent's codes. -/

/-- The incumbent's code list, as `runTraced` reports it. -/
@[expose] def bestCodesOf (st : SearchSt n) : List Nat :=
  (List.range' 1 st.canonlevel).map fun i => st.canoncode[i]!

/-- The incumbent a state carries, or `none` before the first
install. -/
@[expose] def stInc (ctx : Ctx n) (st : SearchSt n) : Option (Key n) :=
  if st.canonlevel = 0 then none
  else some ⟨bestCodesOf st ++ [codeSentinel], leafRows ctx st.canonlab⟩

/-- The semantic incumbent represented by the comparison machine's ghost
code list. -/
@[expose] def ghostInc (ctx : Ctx n) (bs : List Nat)
    (canonlab : Array Nat) : Option (Key n) :=
  if bs = [] then none else some (incKey ctx bs canonlab)

/-- Outside the upward overwrite window, `canoncode` contains exactly the
ghost incumbent codes. -/
theorem bestCodesOf_eq {nn : Nat} {cs bs : List Nat} {st : SearchSt n}
    {compCanon : Int}
    (hinv : CodeCmpInv nn cs bs st.canoncode st.canonlevel
      st.eqlevCanon compCanon)
    (hne : compCanon ≠ 1) :
    bestCodesOf st = bs := by
  unfold bestCodesOf
  refine List.ext_getElem (by simp [hinv.blen]) fun i hi hb => ?_
  rw [List.getElem_map]
  have hcontent := hinv.content (i + 1) (by omega) (by omega)
    (fun h => (hne h).elim)
  have hir : i < (List.range' 1 st.canonlevel).length := by
    simpa using hi
  rw [List.getElem_range' hir]
  have hbcode : bcode bs (i + 1) = bs[i]! :=
    bcode_of_le (by omega) (by omega)
  rw [hbcode, getElem!_pos bs i hb] at hcontent
  simpa [Nat.add_comm] using hcontent

/-- At a stable comparison state, reading the mutable incumbent agrees
with the semantic ghost incumbent. -/
theorem stInc_eq_ghost {nn : Nat} {cs bs : List Nat} {ctx : Ctx n}
    {st : SearchSt n} {compCanon : Int}
    (hinv : CodeCmpInv nn cs bs st.canoncode st.canonlevel
      st.eqlevCanon compCanon)
    (hne : compCanon ≠ 1) :
    stInc ctx st = ghostInc ctx bs st.canonlab := by
  rw [stInc, ghostInc, bestCodesOf_eq hinv hne, hinv.blen]
  cases bs <;> simp [incKey]

/-! # The scatter a code-one admission records

`processnode` builds its generator by `workperm[firstlab[i]] := lab[i]`
over `i < n`, so the permutation maps `firstlab` to `lab` pointwise.
`firstScatter_get` reads that fold back one entry at a time, on the two
`foldl` lemmas below.

`Invariant/Store` has the same fact as a private lemma
(`foldl_scatter_getElem`) and consumes exactly this shape in
`scatter_isPerm`'s `hsc` hypothesis. -/

private theorem foldl_size {lab₁ lab₂ : Array Nat} :
    ∀ (l : List Nat) (base : Array Nat),
      (l.foldl (fun r i => r.set! lab₁[i]! lab₂[i]!) base).size
        = base.size
  | [], _ => rfl
  | _ :: l, base => by
    rw [List.foldl_cons, foldl_size l, Array.size_set!]

private theorem foldl_get {lab₁ lab₂ : Array Nat} {nn : Nat}
    (hinj : ∀ a b, a < nn → b < nn → lab₁[a]! = lab₁[b]! → a = b)
    {base : Array Nat}
    (hbb : ∀ i, i < nn → lab₁[i]! < base.size) :
    ∀ {m : Nat}, m ≤ nn → ∀ {j : Nat}, j < m →
      ((List.range m).foldl
        (fun r i => r.set! lab₁[i]! lab₂[i]!) base)[lab₁[j]!]! =
        lab₂[j]! := by
  intro m
  induction m with
  | zero => intro _ j hj; omega
  | succ p ih =>
    intro hm j hj
    rw [List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    rcases Decidable.em (j = p) with rfl | hne
    · rw [Array.getElem!_set!_self _ _ _
        (by rw [foldl_size]; exact hbb j (by omega))]
    · have hlne : lab₁[p]! ≠ lab₁[j]! := fun h =>
        hne (hinj j p (by omega) (by omega) h.symm)
      rw [Array.getElem!_set!_ne _ _ _ _ hlne, ih (by omega) (by omega)]

/-- The generator `processnode` records maps the first-path labelling
onto the current one pointwise, given only that the first-path
labelling is injective and bounded. Nothing about codes, code
lengths, or where the first path went discrete is used. -/
theorem firstScatter_get {flab lab : Array Nat} {nn : Nat}
    (hinj : ∀ a b, a < nn → b < nn → flab[a]! = flab[b]! → a = b)
    (hlt : ∀ i, i < nn → flab[i]! < nn) :
    ∀ {j : Nat}, j < nn →
      (firstScatter nn flab lab)[flab[j]!]! = lab[j]! := by
  intro j hj
  rw [firstScatter]
  exact foldl_get hinj (base := Array.replicate nn 0)
    (fun i hi => by rw [Array.size_replicate]; exact hlt i hi)
    (Nat.le_refl nn) hj

/-! # The position facts: the step

`payloadAbsorbs_of_positions` takes the two position facts as
hypotheses because they are the descent's bookkeeping. Their base case
is local and is proved here: individualizing offset `o` puts that
offset's vertex at the target position.

The transport of this from the child down to the leaf rests on the
target position being a *singleton cell* from the individualization
onwards. Both steps of that transport are proved below, over one
operation each: `refine` fixes a singleton cell's position, and a
`breakout` elsewhere misses it, because two maximal runs are equal or
disjoint. What is not proved here is the run-level statement that
chains them, since the descent is the mutual recursion itself; see the
note after `breakout_misses_singleton`. -/

/-- Individualizing offset `o` puts that offset's vertex at the target
position. -/
theorem breakout_at_target {lab ptn : Array Nat} {level tc o : Nat}
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size) :
    (breakout n lab ptn (level + 1) tc lab[tc + o]!).1[tc]! =
      lab[tc + o]! := by
  rw [breakout_lab_at hinj hto tc, ite_eq_right (Nat.lt_irrefl tc),
    ite_eq_left rfl]

/-- Individualizing closes the target position, so it becomes a
singleton cell one level down. This is what makes the transport below
apply from the child onwards. -/
theorem isCell_breakout_target {lab ptn : Array Nat}
    {level tc tv : Nat} (hlt : tc < ptn.size)
    (hstart : tc = 0 ∨ ptn[tc - 1]! ≤ level) :
    IsCell (breakout n lab ptn (level + 1) tc tv).2.1 (level + 1) tc 1 := by
  refine ⟨Nat.one_pos, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos tc with rfl | hpos
    · exact Or.inl rfl
    · refine Or.inr ?_
      show (ptn.set! tc (level + 1))[tc - 1]! ≤ level + 1
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      rcases hstart with rfl | hs
      · omega
      · exact Nat.le_succ_of_le hs
  · intro i h1 h2; omega
  · show (ptn.set! tc (level + 1))[tc]! ≤ level + 1
    rw [Array.getElem!_set!_self _ _ _ hlt]
    exact Nat.le_refl _

/-- `refine` leaves a singleton cell's position exactly where it was:
it permutes cell contents, and a singleton cell has only one. -/
theorem refine_fixes_singleton {ctx : Ctx n} {level : Nat}
    {lab ptn : Array Nat} {active : VSet n} {numcells a : Nat}
    (hnn : n ≤ ptn.size) (hs : lab.size = ptn.size)
    (hend : ptn[ptn.size - 1]! ≤ level) (hc : IsCell ptn level a 1) :
    (refine ctx level lab ptn active numcells).lab[a]! = lab[a]! :=
  (cellsPerm_singleton (refine_refInv hnn hs hend).perm hc).symm

/-- A singleton cell lies outside any other cell, so outside the window
a `breakout` at that other cell rotates. -/
theorem singleton_outside_cell {ptn : Array Nat}
    {level a tc len o : Nat} (hca : IsCell ptn level a 1)
    (hct : IsCell ptn level tc len) (hne : a ≠ tc) (ho : o < len) :
    a < tc ∨ tc + o < a := by
  rcases isCell_disj_or_eq hca hct with ⟨h1, _⟩ | h | h
  · exact absurd h1 hne
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- A `breakout` at a different cell leaves a singleton cell's position
alone. Together with `refine_fixes_singleton` this is the whole content
of the descent's position bookkeeping, one operation at a time. -/
theorem breakout_misses_singleton {lab ptn : Array Nat}
    {level a tc o : Nat} (hinj : LabInj lab lab.size)
    (hto : tc + o < lab.size) (hout : a < tc ∨ tc + o < a) :
    (breakout n lab ptn (level + 1) tc lab[tc + o]!).1[a]! = lab[a]! := by
  rw [breakout_lab_at hinj hto a]
  rcases hout with h | h
  · rw [ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-! What remains for the position facts is a run-level frame: that one
call of a quartet function preserves `lab[q]` at every position that is
a singleton cell on entry. Its proof is an induction over the same
mutual recursion as the absorption equation, discharging `refine` by
`refine_fixes_singleton`, each deeper `breakout` by
`singleton_outside_cell` and `breakout_misses_singleton`, and the
persistence of the singleton itself by `refine_frozen` on both `ptn[q]`
and `ptn[q - 1]`, whose values a deeper `set!` at a different position
does not touch. It is stated as part of that induction rather than
before it because a node's effect on `lab` is only defined through the
recursion. -/

/-! # The root assembly

The corrected statement reaches the programme's target. The root call
of `firstPathNode` starts from a state with `canonlevel = 0`, so its
incoming incumbent is `none` and `incMax` discards it; what comes out
is therefore the node key of the root, which is `canonSpec` by
definition, and the state's own incumbent reading is `tracedKey` by
definition. `certifyCanon?_isSome_of_dominated` then closes.

The quartet's root instance is the hypothesis here, and it is the only
thing these theorems assume: the induction that supplies it is the
remaining work. -/

/-- The root state `runTraced` starts from. -/
@[expose] def rootSt (n : Nat) (lab0 : Array Nat)
    (cellEnds : List Nat) : SearchSt n :=
  { lab := lab0, ptn := initPtn n (n + 2) cellEnds,
    active := initActive n cellEnds,
    orbits := .ofFn (n := n) fun i => i.val,
    firstcode := .replicate (n + 2) 0,
    canoncode := .replicate (n + 2) 0,
    firsttc := .replicate (n + 2) (-1),
    firstlab := .replicate n 0,
    canonlab := .replicate n 0,
    canong := .replicate n .empty,
    numorbits := n }

/-- The state the root call returns. -/
@[expose] def rootOut (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : SearchSt n :=
  (firstPathNode { g } (n + 2) 100 (n + 2) 1 cellEnds.length
    (rootSt n lab0 cellEnds)).2

/-- `runTraced`'s reported codes are the returned state's own
reading. -/
theorem bestCodes_runTraced {g : Array (VSet n)} {lab0 : Array Nat} {cellEnds : List Nat}
    (hn0 : n ≠ 0) :
    (runTraced n g lab0 cellEnds).bestCodes =
      bestCodesOf (rootOut n g lab0 cellEnds) := by
  rw [runTraced]
  simp only [beq_iff_eq, hn0, ite_false]
  rfl

/-- `runTraced`'s reported labelling is the returned state's. -/
theorem canonlab_runTraced {g : Array (VSet n)} {lab0 : Array Nat} {cellEnds : List Nat}
    (hn0 : n ≠ 0) :
    (runTraced n g lab0 cellEnds).result.canonlab =
      (rootOut n g lab0 cellEnds).canonlab := by
  rw [runTraced]
  simp only [beq_iff_eq, hn0, ite_false]
  rfl

/-- The traced key is the final state's incumbent, once anything has
been installed. -/
theorem stInc_final {G : Colored n k} (hn0 : n ≠ 0)
    (hinst : (rootOut n (rowsOf G) (initialPartition G).1
      (initialPartition G).2).canonlevel ≠ 0) :
    stInc { g := rowsOf G }
        (rootOut n (rowsOf G) (initialPartition G).1
          (initialPartition G).2) =
      some (tracedKey G) := by
  rw [stInc, ite_eq_right hinst, tracedKey, runColoredTraced,
    bestCodes_runTraced hn0, canonlab_runTraced hn0]

/-- The root's node key is the specification's canonical key. -/
theorem nodeKey_root {G : Colored n k} (hn0 : n ≠ 0) :
    nodeKey { g := rowsOf G } 100 n 1 []
        (rootSt n (initialPartition G).1 (initialPartition G).2)
        (initialPartition G).2.length = canonSpecKey G := by
  rw [nodeKey, prefixKey_nil, canonSpecKey, canonSpec]
  simp only [beq_iff_eq, hn0, ite_false]
  rfl
end Hex.GraphIso.Nauty


/-!
The node steps of the quartet (SPEC § Verified search refinement).

A node's own work, either side of its child loop, never touches the
incumbent: it refines, records its refinement code and target cell,
adjusts the cheap-automorphism level, and on the way out may lower
`allsamelevel`. Every one of those writes leaves `canonlevel`,
`canoncode` and `canonlab` alone, which are the three fields `stInc`
reads. The lemmas here say exactly that, one write at a time, so the
induction can move the incumbent across a node's non-loop operations
without unfolding anything.

Only the leaf arm is different, and it is different in the one way that
matters: `firstterminal` installs, which is what makes a completed
node's `stInc` a `some`.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # The incumbent reads three fields -/

/-- The incumbent reading depends on `canonlevel`, `canoncode` and
`canonlab`, and on nothing else. -/
theorem stInc_congr {ctx : Ctx n} {st st' : SearchSt n}
    (hlv : st'.canonlevel = st.canonlevel)
    (hcc : st'.canoncode = st.canoncode)
    (hcl : st'.canonlab = st.canonlab) :
    stInc ctx st' = stInc ctx st := by
  rw [stInc, stInc, bestCodesOf, bestCodesOf, hlv, hcc, hcl]

/-! # The node's own writes, one at a time

Each of these is the incumbent-invariance of one field update the node
body performs. They are stated over an arbitrary state rather than over
the node's intermediate states, so they compose in either order and do
not depend on how the body is decomposed. -/

/-- Counting a node leaves the incumbent alone. -/
theorem stInc_numnodes {ctx : Ctx n} (st : SearchSt n) (m : Nat) :
    stInc ctx { st with numnodes := m } = stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- Refining leaves the incumbent alone: it writes the labelling, the
partition and the active set. -/
theorem stInc_refined {ctx : Ctx n} (st : SearchSt n)
    (lab ptn : Array Nat) (active : VSet n) :
    stInc ctx { st with lab := lab, ptn := ptn, active := active } =
      stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- Recording this node's refinement code leaves the incumbent alone.
`firstcode` is the first path's ledger, not the incumbent's. -/
theorem stInc_firstcode {ctx : Ctx n} (st : SearchSt n) (fc : Array Nat) :
    stInc ctx { st with firstcode := fc } = stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- Recording this node's target cell leaves the incumbent alone. -/
theorem stInc_firsttc {ctx : Ctx n} (st : SearchSt n) (ftc : Array Int) :
    stInc ctx { st with firsttc := ftc } = stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- Accumulating the target-cell total leaves the incumbent alone. -/
theorem stInc_tctotal {ctx : Ctx n} (st : SearchSt n) (m : Nat) :
    stInc ctx { st with tctotal := m } = stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- Raising the cheap-automorphism level leaves the incumbent alone. -/
theorem stInc_noncheaplevel {ctx : Ctx n} (st : SearchSt n) (m : Nat) :
    stInc ctx { st with noncheaplevel := m } = stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- The node's exit adjustment leaves the incumbent alone. This is the
`allsamelevel` decrement `firstPathNode` performs when its target cell
was exhausted, and it is the only write between the child loop's return
and the node's own. -/
theorem stInc_allsamelevel {ctx : Ctx n} (st : SearchSt n) (m : Nat) :
    stInc ctx { st with allsamelevel := m } = stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- The comparison bookkeeping `otherNode` performs before choosing its
target cell leaves the incumbent alone, except through `canoncode`,
which it rewrites exactly when the current node's code beats the
incumbent's at this level. Stated as the three fields so the caller can
see which one moves. -/
theorem stInc_otherNodePrep (level code : Nat)
    (st : SearchSt n) :
    (otherNodePrep level code st).canonlevel = st.canonlevel ∧
      (otherNodePrep level code st).canonlab = st.canonlab :=
  ⟨(otherNodePrep_frames level code st).2.2.2.1,
    (otherNodePrep_frames level code st).1⟩

/-! # The leaf arm installs

`firstterminal` is where a first-path leaf becomes the incumbent. These
record what it leaves behind, which is what fixes the `some` the
absorption equation needs on the leaf arm. -/

/-- A first-path leaf installs itself: the incumbent's level is this
node's. -/
theorem firstterminal_canonlevel (level : Nat) (st : SearchSt n) :
    (firstterminal level st).canonlevel = level := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

/-- A first-path leaf installs its own labelling. -/
theorem firstterminal_canonlab (level : Nat) (st : SearchSt n) :
    (firstterminal level st).canonlab = st.lab := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

/-- A first-path leaf also records its labelling as the first reference
leaf. -/
theorem firstterminal_firstlab (level : Nat) (st : SearchSt n) :
    (firstterminal level st).firstlab = st.lab := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

/-- A first-path leaf at a positive level leaves something
installed. -/
theorem firstterminal_installed {level : Nat} (hlev : level ≠ 0)
    (st : SearchSt n) : (firstterminal level st).canonlevel ≠ 0 := by
  rw [firstterminal_canonlevel]
  exact hlev

end Hex.GraphIso.Nauty

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CodeFaithful
public import HexGraphIso.Nauty.LeafFaithful
public import HexGraphIso.Nauty.SearchModel
public import HexGraphIso.Nauty.SearchInv
public import HexGraphIso.Nauty.Stabilize
import all HexGraphIso.Nauty.Search

public section

/-!
The domination layer: the key-level reading of the search state's
incumbent, and the per-arm key verdicts of the leaf event. Together
with the comparison machines of `CodeFaithful` and the row clause of
`LeafFaithful`, these are the dischargers the maximality induction
applies at each `processnode` arm to conclude that the traced key
dominates every visited leaf — the `canonSpecKey G = tracedKey G`
equality the replay spine consumes.

The incumbent's key is `⟨bs ++ [codeSentinel], leafRows ctx canonlab⟩`
for the ghost code list `bs` tracked by `CodeCmpInv`; a leaf of the
current path has key `⟨cs ++ [codeSentinel], leafRows ctx lab⟩`. The
verdict lemmas translate the imperative comparison state into
`keyCmp` on those keys:

- `compCanon = -1` or `1` (frozen divergence): the code machine's
  payoff lemmas decide the whole comparison (`codeInv_keyCmp_lt`,
  `codeInv_keyCmp_gt` at `ext := [codeSentinel]`).
- `compCanon = 0` with the path shorter than the incumbent: the leaf
  ends in the sentinel where the incumbent still has a real code, so
  the leaf compares above (`tied_short_keyCmp_gt`) — the short-leaf
  install (`level < canonlevel → code 3`) is correct.
- `compCanon = 0` at the incumbent's depth: the code lists are equal
  outright and the rows decide (`tied_full_keyCmp`), which is the
  `testcanlab` outcome by `leafEvent_faithful`.

The event layer is complete: `processnode_leaf` (the off-first-path
leaf), `processnode_leafFirst` (the first-path-agreeing leaf failing
the admission gate, via the gate-failure reduction
`processnode_gateFail_eq`), `processnode_auto` with `auto_keyMax`
(the gate-passing leaf: comparison state untouched, and the skip
sound at key level once the induction supplies the code agreement
`firstCodeInv_eq_of_tied`, the row transport through the admitted
scatter, and the `firstterminal_firstKeyLe`-seeded
first-key-dominated clause), `recover_machines` with the
`recover_frames`/`otherNodePrep_frames` threading, and the
`firstterminal_*` seeds for all four threads.

What remains is the mutual quartet induction itself, on the
`canonlab_cellsReach` skeleton (`SearchReach.lean`): a `DomOk`
record bundling `SearchOk`, both machines, `CanongInv`, per-stored-
generator `CellStab` (`Stabilize.lean`), the unwinding-correctness
clause (consulting nodes sit above every joined generator's gca,
driving `orbConn_of_ptr`/`childKey_of_orbPruned` at the two orbit
prune sites, Search.lean:296 and :320), the first-key-dominated
clause, and incumbent-maximality (`incKey` equals the `keysMax` of
visited leaves; pruned subtrees dominated through the verdicts
above), concluding at the root that the traced key is
`canonSpecKey`.
-/

namespace Hex.GraphIso.Nauty

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-! # The incumbent key -/

/-- The incumbent's key: the ghost code list with the sentinel
stamped, and the stored best leaf's rows. -/
@[expose] def incKey (ctx : Ctx) (bs : List Nat)
    (canonlab : Array Nat) : Key :=
  ⟨bs ++ [codeSentinel], leafRows ctx canonlab⟩

/-- A leaf key of the current path. -/
@[expose] def pathLeafKey (ctx : Ctx) (cs : List Nat)
    (lab : Array Nat) : Key :=
  ⟨cs ++ [codeSentinel], leafRows ctx lab⟩

private theorem getElem!_append_left {xs ys : List Nat} {i : Nat}
    (h : i < xs.length) : (xs ++ ys)[i]! = xs[i]! := by
  have hxy : i < (xs ++ ys).length := by
    rw [List.length_append]
    omega
  rw [getElem!_pos (xs ++ ys) i hxy, getElem!_pos xs i h,
    List.getElem_append_left h]

/-! # The tied verdicts -/

/-- Under full agreement the path is never deeper than the
incumbent. -/
theorem codeInv_tied_le {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon 0) :
    cs.length ≤ bs.length := by
  rcases hinv.tri with ⟨-, -, hle, -⟩ | ⟨j, -, -, -, -, -, hcase⟩
  · exact hle
  · rcases hcase with ⟨hcc, -⟩ | ⟨hcc, -⟩
    · cases hcc
    · cases hcc

/-- A code-tied leaf strictly above the incumbent's depth compares
above it: the leaf's sentinel meets a real incumbent code. -/
theorem tied_short_keyCmp_gt {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon 0)
    (hshort : cs.length < bs.length) (r1 r2 : List Nat) :
    keyCmp ⟨cs ++ [codeSentinel], r1⟩ ⟨bs ++ [codeSentinel], r2⟩ =
      .gt := by
  rcases hinv.tri with ⟨-, -, -, hmatch⟩ | ⟨j, -, -, -, -, -, hcase⟩
  · rw [keyCmp]
    have hlc : listCmp compare (cs ++ [codeSentinel])
        (bs ++ [codeSentinel]) = .gt := by
      refine listCmp_gt_of_prefix cs.length _ _
        (by rw [List.length_append]; simp)
        (by rw [List.length_append]; simp; omega)
        (fun i hi => ?_) ?_
      · rw [getElem!_append_left hi,
          getElem!_append_sentinel (by omega)]
        have h := hmatch (i + 1) (by omega) (by omega)
        simpa using h
      · rw [getElem!_append_sentinel (bs := cs) (Nat.le_refl _),
          getElem!_append_sentinel (bs := bs) (i := cs.length)
            (by omega),
          bcode_sentinel (bs := cs) (i := cs.length + 1) (by omega)]
        exact bcode_lt hinv.blt (by omega) (by omega)
    rw [hlc]
  · rcases hcase with ⟨hcc, -⟩ | ⟨hcc, -⟩
    · cases hcc
    · cases hcc

/-- A code-tied leaf at the incumbent's depth hands the comparison
to the rows. -/
theorem tied_full_keyCmp {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon 0)
    (hlen : cs.length = bs.length) (r1 r2 : List Nat) :
    keyCmp ⟨cs ++ [codeSentinel], r1⟩ ⟨bs ++ [codeSentinel], r2⟩ =
      listCmp rowCmp r1 r2 := by
  rw [codeInv_eq_of_tied hinv hlen, keyCmp_codes_eq]

/-- The downward-frozen verdict at a leaf, in incumbent-key form. -/
theorem frozen_lt_keyCmp {nn : Nat} {cs bs : List Nat} {ctx : Ctx}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    {lab canonlab : Array Nat}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon
      (-1)) :
    keyCmp (pathLeafKey ctx cs lab) (incKey ctx bs canonlab) =
      .lt :=
  codeInv_keyCmp_lt hinv [codeSentinel] _ _

/-- The upward-frozen verdict at a leaf, in incumbent-key form. -/
theorem frozen_gt_keyCmp {nn : Nat} {cs bs : List Nat} {ctx : Ctx}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    {lab canonlab : Array Nat}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon 1) :
    keyCmp (pathLeafKey ctx cs lab) (incKey ctx bs canonlab) =
      .gt :=
  codeInv_keyCmp_gt hinv [codeSentinel] _ _

/-! # `processnode` arm characterizations -/

private theorem pushAuto_lab (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).lab = st.lab := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_ptn (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).ptn = st.ptn := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_compCanon (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).compCanon = st.compCanon := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_eqlevCanon (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).eqlevCanon = st.eqlevCanon := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_canoncode (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).canoncode = st.canoncode := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_canonlevel (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).canonlevel = st.canonlevel := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_canonlab (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).canonlab = st.canonlab := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_canong (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).canong = st.canong := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_samerows (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).samerows = st.samerows := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_eqlevFirst (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).eqlevFirst = st.eqlevFirst := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_gcaFirst (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).gcaFirst = st.gcaFirst := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_noncheaplevel (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).noncheaplevel = st.noncheaplevel := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_allsamelevel (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).allsamelevel = st.allsamelevel := by
  rw [pushAuto]; split <;> rfl

/-- The unwind level of the shared prune tail. -/
@[expose] def pruneReturn (noncheaplevel allsamelevel : Nat)
    (eqlevCanon : Int) : Int :=
  let save : Int :=
    if Int.ofNat allsamelevel > eqlevCanon then
      Int.ofNat allsamelevel - 1
    else
      eqlevCanon
  if Int.ofNat noncheaplevel ≤ save then
    Int.ofNat noncheaplevel - 1
  else
    save

/-- The pass arm: an internal node with no frozen-downward fast exit
leaves the comparison state alone and returns its own level. -/
theorem processnode_pass {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt}
    (hg : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0))
    (hnc : ¬((numcells == ctx.n) = true)) :
    (processnode ctx level numcells st).1 = Int.ofNat level ∧
    (processnode ctx level numcells st).2.compCanon = st.compCanon ∧
    (processnode ctx level numcells st).2.eqlevCanon = st.eqlevCanon ∧
    (processnode ctx level numcells st).2.canoncode = st.canoncode ∧
    (processnode ctx level numcells st).2.canonlevel = st.canonlevel ∧
    (processnode ctx level numcells st).2.canonlab = st.canonlab ∧
    (processnode ctx level numcells st).2.canong = st.canong ∧
    (processnode ctx level numcells st).2.samerows = st.samerows := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [processnode]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite (fun x : Int × SearchSt => x.1), apply_ite (fun x : Int × SearchSt => x.2), apply_ite (fun st : SearchSt => st.lab), apply_ite (fun st : SearchSt => st.ptn), apply_ite (fun st : SearchSt => st.compCanon), apply_ite (fun st : SearchSt => st.eqlevCanon), apply_ite (fun st : SearchSt => st.canoncode), apply_ite (fun st : SearchSt => st.canonlevel), apply_ite (fun st : SearchSt => st.canonlab), apply_ite (fun st : SearchSt => st.canong), apply_ite (fun st : SearchSt => st.samerows), apply_ite (fun st : SearchSt => st.eqlevFirst), apply_ite (fun st : SearchSt => st.gcaFirst), apply_ite (fun st : SearchSt => st.noncheaplevel), apply_ite (fun st : SearchSt => st.allsamelevel), pushAuto_lab, pushAuto_ptn, pushAuto_compCanon, pushAuto_eqlevCanon, pushAuto_canoncode, pushAuto_canonlevel, pushAuto_canonlab, pushAuto_canong, pushAuto_samerows, pushAuto_eqlevFirst, pushAuto_gcaFirst, pushAuto_noncheaplevel, pushAuto_allsamelevel, ite_self]
    simp [pruneReturn, hg, hnc]

/-- The frozen-downward fast arm: the comparison state is untouched
and the shared prune tail decides the unwind level. -/
theorem processnode_fast {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt}
    (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).1 =
      pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon ∧
    (processnode ctx level numcells st).2.compCanon = st.compCanon ∧
    (processnode ctx level numcells st).2.eqlevCanon = st.eqlevCanon ∧
    (processnode ctx level numcells st).2.canoncode = st.canoncode ∧
    (processnode ctx level numcells st).2.canonlevel = st.canonlevel ∧
    (processnode ctx level numcells st).2.canonlab = st.canonlab ∧
    (processnode ctx level numcells st).2.canong = st.canong ∧
    (processnode ctx level numcells st).2.samerows = st.samerows := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [processnode]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite (fun x : Int × SearchSt => x.1), apply_ite (fun x : Int × SearchSt => x.2), apply_ite (fun st : SearchSt => st.lab), apply_ite (fun st : SearchSt => st.ptn), apply_ite (fun st : SearchSt => st.compCanon), apply_ite (fun st : SearchSt => st.eqlevCanon), apply_ite (fun st : SearchSt => st.canoncode), apply_ite (fun st : SearchSt => st.canonlevel), apply_ite (fun st : SearchSt => st.canonlab), apply_ite (fun st : SearchSt => st.canong), apply_ite (fun st : SearchSt => st.samerows), apply_ite (fun st : SearchSt => st.eqlevFirst), apply_ite (fun st : SearchSt => st.gcaFirst), apply_ite (fun st : SearchSt => st.noncheaplevel), apply_ite (fun st : SearchSt => st.allsamelevel), pushAuto_lab, pushAuto_ptn, pushAuto_compCanon, pushAuto_eqlevCanon, pushAuto_canoncode, pushAuto_canonlevel, pushAuto_canonlab, pushAuto_canong, pushAuto_samerows, pushAuto_eqlevFirst, pushAuto_gcaFirst, pushAuto_noncheaplevel, pushAuto_allsamelevel, ite_self]
    simp [pruneReturn, hg1, hg2, Int.not_lt.mpr, Int.lt_iff_add_one_le]

/-- The short-leaf install: a code-tied leaf strictly above the
incumbent's depth installs itself with no row comparison. -/
theorem processnode_shortInstall {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt}
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true)
    (hcc : st.compCanon = 0)
    (hlt : level < st.canonlevel) :
    (processnode ctx level numcells st).1 =
      pruneReturn st.noncheaplevel st.allsamelevel (Int.ofNat level) ∧
    (processnode ctx level numcells st).2.compCanon = 0 ∧
    (processnode ctx level numcells st).2.eqlevCanon = Int.ofNat level ∧
    (processnode ctx level numcells st).2.canoncode =
      st.canoncode.set! (level + 1) codeSentinel ∧
    (processnode ctx level numcells st).2.canonlevel = level ∧
    (processnode ctx level numcells st).2.canonlab = st.lab ∧
    (processnode ctx level numcells st).2.canong = st.canong ∧
    (processnode ctx level numcells st).2.samerows = 0 := by
  have hg : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0) := by
    rw [hcc]; exact fun h => absurd h.2 (by omega)
  have hlt' : (level < st.canonlevel) := hlt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [processnode]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite (fun x : Int × SearchSt => x.1), apply_ite (fun x : Int × SearchSt => x.2), apply_ite (fun st : SearchSt => st.lab), apply_ite (fun st : SearchSt => st.ptn), apply_ite (fun st : SearchSt => st.compCanon), apply_ite (fun st : SearchSt => st.eqlevCanon), apply_ite (fun st : SearchSt => st.canoncode), apply_ite (fun st : SearchSt => st.canonlevel), apply_ite (fun st : SearchSt => st.canonlab), apply_ite (fun st : SearchSt => st.canong), apply_ite (fun st : SearchSt => st.samerows), apply_ite (fun st : SearchSt => st.eqlevFirst), apply_ite (fun st : SearchSt => st.gcaFirst), apply_ite (fun st : SearchSt => st.noncheaplevel), apply_ite (fun st : SearchSt => st.allsamelevel), pushAuto_lab, pushAuto_ptn, pushAuto_compCanon, pushAuto_eqlevCanon, pushAuto_canoncode, pushAuto_canonlevel, pushAuto_canonlab, pushAuto_canong, pushAuto_samerows, pushAuto_eqlevFirst, pushAuto_gcaFirst, pushAuto_noncheaplevel, pushAuto_allsamelevel, ite_self]
    simp [pruneReturn, hg, hnc, hef, hcc, hlt', Int.lt_iff_add_one_le]

/-- The upward-frozen install: a leaf reached with `compCanon = 1`
installs itself directly. -/
theorem processnode_upInstall {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt}
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true)
    (hcc : st.compCanon = 1) :
    (processnode ctx level numcells st).1 =
      pruneReturn st.noncheaplevel st.allsamelevel (Int.ofNat level) ∧
    (processnode ctx level numcells st).2.compCanon = 0 ∧
    (processnode ctx level numcells st).2.eqlevCanon = Int.ofNat level ∧
    (processnode ctx level numcells st).2.canoncode =
      st.canoncode.set! (level + 1) codeSentinel ∧
    (processnode ctx level numcells st).2.canonlevel = level ∧
    (processnode ctx level numcells st).2.canonlab = st.lab ∧
    (processnode ctx level numcells st).2.canong = st.canong ∧
    (processnode ctx level numcells st).2.samerows = 0 := by
  have hg : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0) := by
    rw [hcc]; exact fun h => absurd h.2 (by omega)
  have hne0 : ¬(st.compCanon = 0) := by rw [hcc]; omega
  have hgt : (0 : Int) < st.compCanon := by rw [hcc]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [processnode]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite (fun x : Int × SearchSt => x.1), apply_ite (fun x : Int × SearchSt => x.2), apply_ite (fun st : SearchSt => st.lab), apply_ite (fun st : SearchSt => st.ptn), apply_ite (fun st : SearchSt => st.compCanon), apply_ite (fun st : SearchSt => st.eqlevCanon), apply_ite (fun st : SearchSt => st.canoncode), apply_ite (fun st : SearchSt => st.canonlevel), apply_ite (fun st : SearchSt => st.canonlab), apply_ite (fun st : SearchSt => st.canong), apply_ite (fun st : SearchSt => st.samerows), apply_ite (fun st : SearchSt => st.eqlevFirst), apply_ite (fun st : SearchSt => st.gcaFirst), apply_ite (fun st : SearchSt => st.noncheaplevel), apply_ite (fun st : SearchSt => st.allsamelevel), pushAuto_lab, pushAuto_ptn, pushAuto_compCanon, pushAuto_eqlevCanon, pushAuto_canoncode, pushAuto_canonlevel, pushAuto_canonlab, pushAuto_canong, pushAuto_samerows, pushAuto_eqlevFirst, pushAuto_gcaFirst, pushAuto_noncheaplevel, pushAuto_allsamelevel, ite_self]
    simp [pruneReturn, hg, hnc, hef, hcc, hne0, hgt, Int.lt_iff_add_one_le]

/-- The row-decided install: a code-tied leaf at the incumbent's
depth whose rows compare above installs itself. -/
theorem processnode_rowInstall {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt}
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true)
    (hcc : st.compCanon = 0)
    (hge : ¬(level < st.canonlevel))
    (hgt : (0 : Int) < (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1) :
    (processnode ctx level numcells st).1 =
      pruneReturn st.noncheaplevel st.allsamelevel (Int.ofNat level) ∧
    (processnode ctx level numcells st).2.compCanon = 0 ∧
    (processnode ctx level numcells st).2.eqlevCanon = Int.ofNat level ∧
    (processnode ctx level numcells st).2.canoncode =
      st.canoncode.set! (level + 1) codeSentinel ∧
    (processnode ctx level numcells st).2.canonlevel = level ∧
    (processnode ctx level numcells st).2.canonlab = st.lab ∧
    (processnode ctx level numcells st).2.canong =
      updatecan ctx st.canong st.canonlab st.samerows ∧
    (processnode ctx level numcells st).2.samerows =
      (testcanlab ctx
        (updatecan ctx st.canong st.canonlab st.samerows) st.lab).2 := by
  have hg : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0) := by
    rw [hcc]; exact fun h => absurd h.2 (by omega)
  have hne0 : ¬((testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0) := by
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [processnode]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite (fun x : Int × SearchSt => x.1), apply_ite (fun x : Int × SearchSt => x.2), apply_ite (fun st : SearchSt => st.lab), apply_ite (fun st : SearchSt => st.ptn), apply_ite (fun st : SearchSt => st.compCanon), apply_ite (fun st : SearchSt => st.eqlevCanon), apply_ite (fun st : SearchSt => st.canoncode), apply_ite (fun st : SearchSt => st.canonlevel), apply_ite (fun st : SearchSt => st.canonlab), apply_ite (fun st : SearchSt => st.canong), apply_ite (fun st : SearchSt => st.samerows), apply_ite (fun st : SearchSt => st.eqlevFirst), apply_ite (fun st : SearchSt => st.gcaFirst), apply_ite (fun st : SearchSt => st.noncheaplevel), apply_ite (fun st : SearchSt => st.allsamelevel), pushAuto_lab, pushAuto_ptn, pushAuto_compCanon, pushAuto_eqlevCanon, pushAuto_canoncode, pushAuto_canonlevel, pushAuto_canonlab, pushAuto_canong, pushAuto_samerows, pushAuto_eqlevFirst, pushAuto_gcaFirst, pushAuto_noncheaplevel, pushAuto_allsamelevel, ite_self]
    simp [pruneReturn, hg, hnc, hef, hcc, hge, hne0, hgt, Int.lt_iff_add_one_le]

/-- The row-decided rejection: a code-tied leaf at the incumbent's
depth whose rows compare below is discarded, freezing the downward
comparison. -/
theorem processnode_rowReject {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt}
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true)
    (hcc : st.compCanon = 0)
    (hge : ¬(level < st.canonlevel))
    (hlt : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 < 0) :
    (processnode ctx level numcells st).1 =
      pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon ∧
    (processnode ctx level numcells st).2.compCanon =
      (testcanlab ctx
        (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 ∧
    (processnode ctx level numcells st).2.eqlevCanon = st.eqlevCanon ∧
    (processnode ctx level numcells st).2.canoncode = st.canoncode ∧
    (processnode ctx level numcells st).2.canonlevel = st.canonlevel ∧
    (processnode ctx level numcells st).2.canonlab = st.canonlab ∧
    (processnode ctx level numcells st).2.canong =
      updatecan ctx st.canong st.canonlab st.samerows ∧
    (processnode ctx level numcells st).2.samerows = ctx.n := by
  have hg : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0) := by
    rw [hcc]; exact fun h => absurd h.2 (by omega)
  have hne0 : ¬((testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0) := by
    omega
  have hngt : ¬((0 : Int) < (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1) := by
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [processnode]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite (fun x : Int × SearchSt => x.1), apply_ite (fun x : Int × SearchSt => x.2), apply_ite (fun st : SearchSt => st.lab), apply_ite (fun st : SearchSt => st.ptn), apply_ite (fun st : SearchSt => st.compCanon), apply_ite (fun st : SearchSt => st.eqlevCanon), apply_ite (fun st : SearchSt => st.canoncode), apply_ite (fun st : SearchSt => st.canonlevel), apply_ite (fun st : SearchSt => st.canonlab), apply_ite (fun st : SearchSt => st.canong), apply_ite (fun st : SearchSt => st.samerows), apply_ite (fun st : SearchSt => st.eqlevFirst), apply_ite (fun st : SearchSt => st.gcaFirst), apply_ite (fun st : SearchSt => st.noncheaplevel), apply_ite (fun st : SearchSt => st.allsamelevel), pushAuto_lab, pushAuto_ptn, pushAuto_compCanon, pushAuto_eqlevCanon, pushAuto_canoncode, pushAuto_canonlevel, pushAuto_canonlab, pushAuto_canong, pushAuto_samerows, pushAuto_eqlevFirst, pushAuto_gcaFirst, pushAuto_noncheaplevel, pushAuto_allsamelevel, ite_self]
    simp [pruneReturn, hg, hnc, hef, hcc, hge, hne0, hngt]

/-! # Comparison-blind frames of `processnode` -/

private theorem pushAuto_gcaCanon (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).gcaCanon = st.gcaCanon := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_firstcode (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).firstcode = st.firstcode := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_firstlab (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).firstlab = st.firstlab := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_firsttc (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).firsttc = st.firsttc := by
  rw [pushAuto]; split <;> rfl

private theorem processnode_lab (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
    (processnode ctx level numcells st).2.lab = st.lab := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.lab), pushAuto_lab,
    ite_self]

private theorem processnode_ptn (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
    (processnode ctx level numcells st).2.ptn = st.ptn := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.ptn), pushAuto_ptn,
    ite_self]

private theorem processnode_eqlevFirst (ctx : Ctx)
    (level numcells : Nat) (st : SearchSt) :
    (processnode ctx level numcells st).2.eqlevFirst =
      st.eqlevFirst := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.eqlevFirst),
    pushAuto_eqlevFirst, ite_self]

private theorem processnode_firstcode (ctx : Ctx)
    (level numcells : Nat) (st : SearchSt) :
    (processnode ctx level numcells st).2.firstcode =
      st.firstcode := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.firstcode),
    pushAuto_firstcode, ite_self]

private theorem processnode_firstlab (ctx : Ctx)
    (level numcells : Nat) (st : SearchSt) :
    (processnode ctx level numcells st).2.firstlab =
      st.firstlab := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.firstlab),
    pushAuto_firstlab, ite_self]

private theorem processnode_firsttc (ctx : Ctx)
    (level numcells : Nat) (st : SearchSt) :
    (processnode ctx level numcells st).2.firsttc = st.firsttc := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.firsttc),
    pushAuto_firsttc, ite_self]

private theorem processnode_gcaFirst (ctx : Ctx)
    (level numcells : Nat) (st : SearchSt) :
    (processnode ctx level numcells st).2.gcaFirst = st.gcaFirst := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.gcaFirst),
    pushAuto_gcaFirst, ite_self]

private theorem processnode_noncheaplevel (ctx : Ctx)
    (level numcells : Nat) (st : SearchSt) :
    (processnode ctx level numcells st).2.noncheaplevel =
      st.noncheaplevel := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.noncheaplevel),
    pushAuto_noncheaplevel, ite_self]

private theorem processnode_allsamelevel (ctx : Ctx)
    (level numcells : Nat) (st : SearchSt) :
    (processnode ctx level numcells st).2.allsamelevel =
      st.allsamelevel := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.allsamelevel),
    pushAuto_allsamelevel, ite_self]

/-- The fields `processnode` never writes: the labelling pair, the
first-path data, and the level bookkeeping consumed by the child
loops. -/
theorem processnode_frames (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
    (processnode ctx level numcells st).2.lab = st.lab ∧
    (processnode ctx level numcells st).2.ptn = st.ptn ∧
    (processnode ctx level numcells st).2.eqlevFirst = st.eqlevFirst ∧
    (processnode ctx level numcells st).2.firstcode = st.firstcode ∧
    (processnode ctx level numcells st).2.firstlab = st.firstlab ∧
    (processnode ctx level numcells st).2.firsttc = st.firsttc ∧
    (processnode ctx level numcells st).2.gcaFirst = st.gcaFirst ∧
    (processnode ctx level numcells st).2.noncheaplevel =
      st.noncheaplevel ∧
    (processnode ctx level numcells st).2.allsamelevel =
      st.allsamelevel :=
  ⟨processnode_lab ctx level numcells st,
    processnode_ptn ctx level numcells st,
    processnode_eqlevFirst ctx level numcells st,
    processnode_firstcode ctx level numcells st,
    processnode_firstlab ctx level numcells st,
    processnode_firsttc ctx level numcells st,
    processnode_gcaFirst ctx level numcells st,
    processnode_noncheaplevel ctx level numcells st,
    processnode_allsamelevel ctx level numcells st⟩

/-- The row-tied arm: a code-tied leaf at the incumbent's depth whose
rows equal the incumbent's is an automorphism candidate (nauty's code
`2`); the incumbent survives unchanged and the unwind returns to one
of the guiding ancestors. -/
theorem processnode_rowTie {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt}
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true)
    (hcc : st.compCanon = 0)
    (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0) :
    ((processnode ctx level numcells st).1 = Int.ofNat st.gcaFirst ∨
      (processnode ctx level numcells st).1 = Int.ofNat st.gcaCanon) ∧
    (processnode ctx level numcells st).2.compCanon = 0 ∧
    (processnode ctx level numcells st).2.eqlevCanon = st.eqlevCanon ∧
    (processnode ctx level numcells st).2.canoncode = st.canoncode ∧
    (processnode ctx level numcells st).2.canonlevel = st.canonlevel ∧
    (processnode ctx level numcells st).2.canonlab = st.canonlab ∧
    (processnode ctx level numcells st).2.canong =
      updatecan ctx st.canong st.canonlab st.samerows ∧
    (processnode ctx level numcells st).2.samerows = ctx.n := by
  have hg : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0) := by
    rw [hcc]; exact fun h => absurd h.2 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [processnode]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite (fun x : Int × SearchSt => x.1), apply_ite (fun x : Int × SearchSt => x.2), apply_ite (fun st : SearchSt => st.lab), apply_ite (fun st : SearchSt => st.ptn), apply_ite (fun st : SearchSt => st.compCanon), apply_ite (fun st : SearchSt => st.eqlevCanon), apply_ite (fun st : SearchSt => st.canoncode), apply_ite (fun st : SearchSt => st.canonlevel), apply_ite (fun st : SearchSt => st.canonlab), apply_ite (fun st : SearchSt => st.canong), apply_ite (fun st : SearchSt => st.samerows), apply_ite (fun st : SearchSt => st.eqlevFirst), apply_ite (fun st : SearchSt => st.gcaFirst), apply_ite (fun st : SearchSt => st.noncheaplevel), apply_ite (fun st : SearchSt => st.allsamelevel), pushAuto_lab, pushAuto_ptn, pushAuto_compCanon, pushAuto_eqlevCanon, pushAuto_canoncode, pushAuto_canonlevel, pushAuto_canonlab, pushAuto_canong, pushAuto_samerows, pushAuto_eqlevFirst, pushAuto_gcaFirst, pushAuto_noncheaplevel, pushAuto_allsamelevel, ite_self]
    simp [pruneReturn, hg, hnc, hef, hcc, hge, htie, pushAuto_gcaCanon,
      pushAuto_gcaFirst]
    repeat' split
    all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | rfl

/-! # The leaf event resolves the incumbent to the key maximum -/

/-- The full leaf event off the first path: at a discrete node,
`processnode` leaves the incumbent at the key maximum of the entry
incumbent and the current leaf, re-establishes the store invariant,
and hands back a comparison machine for the unwind — intact when the
comparison stayed frozen or re-seeded by an install, or in the
reset form when a row rejection repurposed `compCanon`
(`recover_codeInv_reset` consumes it). The return level is one of
the four unwind forms. -/
theorem processnode_leaf {nn : Nat} {ctx : Ctx} {cs bs : List Nat}
    {numcells : Nat} {st : SearchSt}
    (hcinv : CodeCmpInv nn cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hginv : CanongInv ctx st.canong st.canonlab st.samerows)
    (hcsn : cs.length ≤ nn)
    (hef : ¬((st.eqlevFirst == cs.length) = true))
    (hnc : (numcells == ctx.n) = true) :
    ∃ bs' : List Nat,
      incKey ctx bs'
          (processnode ctx cs.length numcells st).2.canonlab =
        keyMax (incKey ctx bs st.canonlab)
          (pathLeafKey ctx cs st.lab) ∧
      CanongInv ctx (processnode ctx cs.length numcells st).2.canong
        (processnode ctx cs.length numcells st).2.canonlab
        (processnode ctx cs.length numcells st).2.samerows ∧
      (((processnode ctx cs.length numcells st).2.compCanon ≤ 0 ∧
        CodeCmpInv nn cs bs'
          (processnode ctx cs.length numcells st).2.canoncode
          (processnode ctx cs.length numcells st).2.canonlevel
          (processnode ctx cs.length numcells st).2.eqlevCanon
          (processnode ctx cs.length numcells st).2.compCanon) ∨
        ((processnode ctx cs.length numcells st).2.compCanon < 0 ∧
          CodeCmpInv nn cs bs'
            (processnode ctx cs.length numcells st).2.canoncode
            (processnode ctx cs.length numcells st).2.canonlevel
            (processnode ctx cs.length numcells st).2.eqlevCanon
            0)) ∧
      ((processnode ctx cs.length numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel
            st.eqlevCanon ∨
        (processnode ctx cs.length numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel
            (Int.ofNat cs.length) ∨
        (processnode ctx cs.length numcells st).1 =
          Int.ofNat st.gcaFirst ∨
        (processnode ctx cs.length numcells st).1 =
          Int.ofNat st.gcaCanon) := by
  rcases hcinv.tri with ⟨hcc, hec, hlecs, hmatch⟩ |
    ⟨j, hj1, hjL, hjm, hec, hpre, hcase⟩
  · -- the comparison is live: the tied arms
    have hcinv0 : CodeCmpInv nn cs bs st.canoncode st.canonlevel
        st.eqlevCanon 0 := hcc ▸ hcinv
    rcases Decidable.em (cs.length < st.canonlevel) with hlt | hge
    · -- the short-leaf install
      obtain ⟨hr, hc2, he2, hcode2, hcl2, hlab2, hg2, hs2⟩ :=
        processnode_shortInstall hef hnc hcc hlt
      refine ⟨cs, ?_, ?_, ?_, Or.inr (Or.inl hr)⟩
      · simp only [incKey, pathLeafKey]
        rw [hlab2]
        have hgt := tied_short_keyCmp_gt hcinv0
          (by have := hcinv.blen; omega)
          (leafRows ctx st.lab) (leafRows ctx st.canonlab)
        rw [keyMax_eq_right (keyCmp_gt_iff_lt.mp hgt)]
      · rw [hg2, hlab2, hs2]
        exact canongInv_zero st.lab (canongInv_size hginv)
      · left
        refine ⟨by rw [hc2]; decide, ?_⟩
        rw [hcode2, hcl2, he2, hc2]
        exact install_codeInv hcinv0 (by decide) hcsn
    · -- the row-decided arms
      have hlen : cs.length = bs.length := by
        have h1 := codeInv_tied_le hcinv0
        have h2 := hcinv.blen
        omega
      obtain ⟨hc1, hcInc, hcNew⟩ :=
        leafEvent_faithful (lab := st.lab) hginv
      have hfull := tied_full_keyCmp hcinv0 hlen
        (leafRows ctx st.lab) (leafRows ctx st.canonlab)
      rcases hlc : listCmp rowCmp (leafRows ctx st.lab)
        (leafRows ctx st.canonlab) with _ | _ | _
      · -- rows below: the rejection
        have hltc : (testcanlab ctx
            (updatecan ctx st.canong st.canonlab st.samerows)
              st.lab).1 < 0 := by
          rw [hc1, hlc]; decide
        obtain ⟨hr, hc2, he2, hcode2, hcl2, hlab2, hg2, hs2⟩ :=
          processnode_rowReject hef hnc hcc hge hltc
        rw [hlc] at hfull
        refine ⟨bs, ?_, ?_, ?_, Or.inl hr⟩
        · simp only [incKey, pathLeafKey]
          rw [hlab2, keyMax_eq_left (show keyLe
            ⟨cs ++ [codeSentinel], leafRows ctx st.lab⟩
            ⟨bs ++ [codeSentinel], leafRows ctx st.canonlab⟩ from by
              show keyCmp _ _ ≠ .gt
              rw [hfull]
              decide)]
        · rw [hg2, hlab2, hs2]
          exact hcInc
        · right
          constructor
          · rw [hc2, hc1, hlc]
            decide
          · rw [hcode2, hcl2, he2]
            exact hcinv0
      · -- rows tied: the automorphism-candidate arm
        have htie : (testcanlab ctx
            (updatecan ctx st.canong st.canonlab st.samerows)
              st.lab).1 = 0 := by
          rw [hc1, hlc]; rfl
        obtain ⟨hrOr, hc2, he2, hcode2, hcl2, hlab2, hg2, hs2⟩ :=
          processnode_rowTie hef hnc hcc hge htie
        rw [hlc] at hfull
        have hpi : (⟨cs ++ [codeSentinel], leafRows ctx st.lab⟩ :
            Key) = ⟨bs ++ [codeSentinel], leafRows ctx st.canonlab⟩ :=
          keyCmp_eq_iff.mp hfull
        refine ⟨bs, ?_, ?_, ?_, ?_⟩
        · simp only [incKey, pathLeafKey]
          rw [hlab2, hpi, keyMax_eq_left (show keyLe
            (⟨bs ++ [codeSentinel], leafRows ctx st.canonlab⟩ : Key)
            ⟨bs ++ [codeSentinel], leafRows ctx st.canonlab⟩ from by
              show keyCmp _ _ ≠ .gt
              rw [keyCmp_eq_iff.mpr rfl]
              decide)]
        · rw [hg2, hlab2, hs2]
          exact hcInc
        · left
          refine ⟨by rw [hc2]; decide, ?_⟩
          rw [hcode2, hcl2, he2, hc2]
          exact hcinv0
        · rcases hrOr with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
      · -- rows above: the install
        have hgtc : (0 : Int) < (testcanlab ctx
            (updatecan ctx st.canong st.canonlab st.samerows)
              st.lab).1 := by
          rw [hc1, hlc]; decide
        obtain ⟨hr, hc2, he2, hcode2, hcl2, hlab2, hg2, hs2⟩ :=
          processnode_rowInstall hef hnc hcc hge hgtc
        rw [hlc] at hfull
        refine ⟨cs, ?_, ?_, ?_, Or.inr (Or.inl hr)⟩
        · simp only [incKey, pathLeafKey]
          rw [hlab2, keyMax_eq_right (keyCmp_gt_iff_lt.mp hfull)]
        · rw [hg2, hlab2, hs2]
          exact hcNew
        · left
          refine ⟨by rw [hc2]; decide, ?_⟩
          rw [hcode2, hcl2, he2, hc2]
          exact install_codeInv hcinv0 (by decide) hcsn
  · -- the comparison is frozen
    rcases hcase with ⟨hcc, hjlt⟩ | ⟨hcc, hjb, hjgt⟩
    · -- frozen downward: the fast rejection
      have hminv : CodeCmpInv nn cs bs st.canoncode st.canonlevel
          st.eqlevCanon (-1) := hcc ▸ hcinv
      have hg : st.eqlevFirst ≠ cs.length ∧ st.compCanon < 0 :=
        ⟨fun h => hef (by rw [h]; exact beq_self_eq_true _),
          by rw [hcc]; decide⟩
      obtain ⟨hr, hc2, he2, hcode2, hcl2, hlab2, hg2, hs2⟩ :=
        processnode_fast hg
      refine ⟨bs, ?_, ?_, ?_, Or.inl hr⟩
      · simp only [incKey, pathLeafKey]
        rw [hlab2, keyMax_eq_left (show keyLe
          (⟨cs ++ [codeSentinel], leafRows ctx st.lab⟩ : Key)
          ⟨bs ++ [codeSentinel], leafRows ctx st.canonlab⟩ from by
            show keyCmp _ _ ≠ .gt
            rw [show keyCmp
              (⟨cs ++ [codeSentinel], leafRows ctx st.lab⟩ : Key)
              ⟨bs ++ [codeSentinel], leafRows ctx st.canonlab⟩ =
                .lt from frozen_lt_keyCmp hminv]
            decide)]
      · rw [hg2, hlab2, hs2]
        exact hginv
      · left
        refine ⟨by rw [hc2, hcc]; decide, ?_⟩
        rw [hcode2, hcl2, he2, hc2]
        exact hcinv
    · -- frozen upward: the direct install
      have hminv : CodeCmpInv nn cs bs st.canoncode st.canonlevel
          st.eqlevCanon 1 := hcc ▸ hcinv
      obtain ⟨hr, hc2, he2, hcode2, hcl2, hlab2, hg2, hs2⟩ :=
        processnode_upInstall hef hnc hcc
      refine ⟨cs, ?_, ?_, ?_, Or.inr (Or.inl hr)⟩
      · simp only [incKey, pathLeafKey]
        rw [hlab2, keyMax_eq_right (keyCmp_gt_iff_lt.mp
          (show keyCmp
            (⟨cs ++ [codeSentinel], leafRows ctx st.lab⟩ : Key)
            ⟨bs ++ [codeSentinel], leafRows ctx st.canonlab⟩ = .gt
            from frozen_gt_keyCmp hminv))]
      · rw [hg2, hlab2, hs2]
        exact canongInv_zero st.lab (canongInv_size hginv)
      · left
        refine ⟨by rw [hc2]; decide, ?_⟩
        rw [hcode2, hcl2, he2, hc2]
        exact install_codeInv hminv (by decide) hcsn

/-! # The unwind carries both machines -/

/-- One `recover` step after a node event: the comparison machine
survives the unwind in whichever mode the event left it — live with
`compCanon ≤ 0`, or the reset mode a row rejection leaves behind —
and the first-path machine is clamped. The induction applies this at
every return to a child loop. -/
theorem recover_machines {nn N inf : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {lvl : Nat}
    (hc : (st.compCanon ≤ 0 ∧
        CodeCmpInv nn cs bs st.canoncode st.canonlevel st.eqlevCanon
          st.compCanon) ∨
      CodeCmpInv nn cs bs st.canoncode st.canonlevel st.eqlevCanon 0)
    (hf : FirstCodeInv nn cs fs st.firstcode st.eqlevFirst)
    (hlvl : lvl ≤ cs.length) :
    CodeCmpInv nn (cs.take lvl) bs
        (recover N inf lvl st).canoncode
        (recover N inf lvl st).canonlevel
        (recover N inf lvl st).eqlevCanon
        (recover N inf lvl st).compCanon ∧
      FirstCodeInv nn (cs.take lvl) fs
        (recover N inf lvl st).firstcode
        (recover N inf lvl st).eqlevFirst := by
  refine ⟨?_, recover_firstCodeInv hf hlvl⟩
  rcases hc with ⟨hle, hinv⟩ | hinv
  · exact recover_codeInv hinv hle hlvl
  · exact recover_codeInv_reset hinv hlvl

/-! # The first-path-agreeing leaf: the code-`1` gate -/

/-- nauty's `workperm` at a first-path-agreeing leaf: the scatter of
the current leaf's labelling over the first leaf's. -/
@[expose] def firstScatter (n : Nat) (firstlab lab : Array Nat) :
    Array Nat :=
  (List.range n).foldl (fun w i => w.set! firstlab[i]! lab[i]!)
    (Array.replicate n 0)

private theorem forIn_range_eq3 {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [0:n] init f : Id β) = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [0:n].start [0:n].size [0:n].step
      = List.range n := by simp [List.range_eq_range']
  rw [hrange]

private theorem forIn_scatter_eq {flab lab : Array Nat} :
    ∀ (l : List Nat) (w : Array Nat),
      (forIn l w (fun i r =>
        pure (ForInStep.yield (r.set! flab[i]! lab[i]!))) :
          Id (Array Nat)) =
      l.foldl (fun r i => r.set! flab[i]! lab[i]!) w
  | [], _ => rfl
  | i :: l, w => by
    rw [List.forIn_cons, List.foldl_cons]
    exact forIn_scatter_eq l _

private theorem firstScatter_fold (n : Nat) (flab lab : Array Nat) :
    (List.range n).foldl (fun w i => w.set! flab[i]! lab[i]!)
      (Array.replicate n 0) = firstScatter n flab lab := rfl

private theorem id_run_eq {α : Type} (x : Id α) : Id.run x = x := rfl

private theorem pushAuto_orbits (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).orbits = st.orbits := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_numorbits (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).numorbits = st.numorbits := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_cosetindex (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).cosetindex = st.cosetindex := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_maxlevel (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).maxlevel = st.maxlevel := by
  rw [pushAuto]; split <;> rfl

/-- The code-`1` arm: a first-path-agreeing leaf passing the
admission gate records a generator and unwinds to `gcaFirst` with
the whole comparison state untouched. -/
theorem processnode_auto {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt}
    (heq : (st.eqlevFirst == level) = true)
    (hnc : (numcells == ctx.n) = true)
    (hpass : st.gcaFirst ≥ st.noncheaplevel ∨
      isautom ctx (firstScatter ctx.n st.firstlab st.lab) = true) :
    (processnode ctx level numcells st).1 =
      Int.ofNat st.gcaFirst ∧
    (processnode ctx level numcells st).2.compCanon = st.compCanon ∧
    (processnode ctx level numcells st).2.eqlevCanon = st.eqlevCanon ∧
    (processnode ctx level numcells st).2.canoncode = st.canoncode ∧
    (processnode ctx level numcells st).2.canonlevel = st.canonlevel ∧
    (processnode ctx level numcells st).2.canonlab = st.canonlab ∧
    (processnode ctx level numcells st).2.canong = st.canong ∧
    (processnode ctx level numcells st).2.samerows = st.samerows := by
  have hg : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0) := by
    intro h
    exact h.1 (beq_iff_eq.mp heq)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [processnode]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite (fun x : Int × SearchSt => x.1), apply_ite (fun x : Int × SearchSt => x.2), apply_ite (fun st : SearchSt => st.lab), apply_ite (fun st : SearchSt => st.ptn), apply_ite (fun st : SearchSt => st.compCanon), apply_ite (fun st : SearchSt => st.eqlevCanon), apply_ite (fun st : SearchSt => st.canoncode), apply_ite (fun st : SearchSt => st.canonlevel), apply_ite (fun st : SearchSt => st.canonlab), apply_ite (fun st : SearchSt => st.canong), apply_ite (fun st : SearchSt => st.samerows), apply_ite (fun st : SearchSt => st.eqlevFirst), apply_ite (fun st : SearchSt => st.gcaFirst), apply_ite (fun st : SearchSt => st.noncheaplevel), apply_ite (fun st : SearchSt => st.allsamelevel), pushAuto_lab, pushAuto_ptn, pushAuto_compCanon, pushAuto_eqlevCanon, pushAuto_canoncode, pushAuto_canonlevel, pushAuto_canonlab, pushAuto_canong, pushAuto_samerows, pushAuto_eqlevFirst, pushAuto_gcaFirst, pushAuto_noncheaplevel, pushAuto_allsamelevel, ite_self]
    rw [forIn_range_eq3, forIn_scatter_eq, firstScatter_fold]
    simp [pruneReturn, hg, hnc, heq]
    intro h1 h2
    rcases hpass with h | h
    · omega
    · have h2' : isautom ctx (firstScatter ctx.n st.firstlab st.lab)
          = false := h2
      rw [h] at h2'
      cases h2'

/-- A first-path-agreeing leaf failing the admission gate behaves,
in the return level and the whole comparison state, exactly as the
same state entered off the first path: the gate's only effect is the
skipped generator. -/
theorem processnode_gateFail_eq {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt}
    (heq : (st.eqlevFirst == level) = true)
    (hnc : (numcells == ctx.n) = true)
    (hfail1 : st.gcaFirst < st.noncheaplevel)
    (hfail2 : isautom ctx (firstScatter ctx.n st.firstlab st.lab)
      = false) :
    ((processnode ctx level numcells st).1 =
        (processnode ctx level numcells
          { st with eqlevFirst := level + 1 }).1 ∨
      (processnode ctx level numcells st).1 =
        Int.ofNat st.gcaFirst ∨
      (processnode ctx level numcells st).1 =
        Int.ofNat st.gcaCanon) ∧
    (processnode ctx level numcells st).2.compCanon =
      (processnode ctx level numcells
        { st with eqlevFirst := level + 1 }).2.compCanon ∧
    (processnode ctx level numcells st).2.eqlevCanon =
      (processnode ctx level numcells
        { st with eqlevFirst := level + 1 }).2.eqlevCanon ∧
    (processnode ctx level numcells st).2.canoncode =
      (processnode ctx level numcells
        { st with eqlevFirst := level + 1 }).2.canoncode ∧
    (processnode ctx level numcells st).2.canonlevel =
      (processnode ctx level numcells
        { st with eqlevFirst := level + 1 }).2.canonlevel ∧
    (processnode ctx level numcells st).2.canonlab =
      (processnode ctx level numcells
        { st with eqlevFirst := level + 1 }).2.canonlab ∧
    (processnode ctx level numcells st).2.canong =
      (processnode ctx level numcells
        { st with eqlevFirst := level + 1 }).2.canong ∧
    (processnode ctx level numcells st).2.samerows =
      (processnode ctx level numcells
        { st with eqlevFirst := level + 1 }).2.samerows := by
  have hg : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0) := by
    intro h
    exact h.1 (beq_iff_eq.mp heq)
  have hge : ¬(st.gcaFirst ≥ st.noncheaplevel) := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [processnode, processnode]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite (fun x : Int × SearchSt => x.1), apply_ite (fun x : Int × SearchSt => x.2), apply_ite (fun st : SearchSt => st.lab), apply_ite (fun st : SearchSt => st.ptn), apply_ite (fun st : SearchSt => st.compCanon), apply_ite (fun st : SearchSt => st.eqlevCanon), apply_ite (fun st : SearchSt => st.canoncode), apply_ite (fun st : SearchSt => st.canonlevel), apply_ite (fun st : SearchSt => st.canonlab), apply_ite (fun st : SearchSt => st.canong), apply_ite (fun st : SearchSt => st.samerows), apply_ite (fun st : SearchSt => st.eqlevFirst), apply_ite (fun st : SearchSt => st.gcaFirst), apply_ite (fun st : SearchSt => st.noncheaplevel), apply_ite (fun st : SearchSt => st.allsamelevel), pushAuto_lab, pushAuto_ptn, pushAuto_compCanon, pushAuto_eqlevCanon, pushAuto_canoncode, pushAuto_canonlevel, pushAuto_canonlab, pushAuto_canong, pushAuto_samerows, pushAuto_eqlevFirst, pushAuto_gcaFirst, pushAuto_noncheaplevel, pushAuto_allsamelevel, pushAuto_orbits, pushAuto_numorbits, pushAuto_cosetindex, pushAuto_maxlevel, pushAuto_gcaCanon, ite_self]
    rw [forIn_range_eq3, forIn_scatter_eq, firstScatter_fold]
    simp [pruneReturn, hg, hnc, heq, hge, hfail2, id_run_eq,
      pushAuto_orbits, pushAuto_numorbits, pushAuto_cosetindex]
    repeat' split
    all_goals first
    | rfl
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
    | omega
    | (exfalso; omega)
    | (intros
       first
       | rfl
       | exact Or.inl rfl
       | exact Or.inr (Or.inl rfl)
       | exact Or.inr (Or.inr rfl)
       | omega)

/-- The leaf event at a first-path-agreeing leaf that fails the
admission gate: identical to `processnode_leaf`, by the gate-failure
reduction. -/
theorem processnode_leafFirst {nn : Nat} {ctx : Ctx}
    {cs bs : List Nat} {numcells : Nat} {st : SearchSt}
    (hcinv : CodeCmpInv nn cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hginv : CanongInv ctx st.canong st.canonlab st.samerows)
    (hcsn : cs.length ≤ nn)
    (heq : (st.eqlevFirst == cs.length) = true)
    (hnc : (numcells == ctx.n) = true)
    (hfail1 : st.gcaFirst < st.noncheaplevel)
    (hfail2 : isautom ctx (firstScatter ctx.n st.firstlab st.lab)
      = false) :
    ∃ bs' : List Nat,
      incKey ctx bs'
          (processnode ctx cs.length numcells st).2.canonlab =
        keyMax (incKey ctx bs st.canonlab)
          (pathLeafKey ctx cs st.lab) ∧
      CanongInv ctx (processnode ctx cs.length numcells st).2.canong
        (processnode ctx cs.length numcells st).2.canonlab
        (processnode ctx cs.length numcells st).2.samerows ∧
      (((processnode ctx cs.length numcells st).2.compCanon ≤ 0 ∧
        CodeCmpInv nn cs bs'
          (processnode ctx cs.length numcells st).2.canoncode
          (processnode ctx cs.length numcells st).2.canonlevel
          (processnode ctx cs.length numcells st).2.eqlevCanon
          (processnode ctx cs.length numcells st).2.compCanon) ∨
        ((processnode ctx cs.length numcells st).2.compCanon < 0 ∧
          CodeCmpInv nn cs bs'
            (processnode ctx cs.length numcells st).2.canoncode
            (processnode ctx cs.length numcells st).2.canonlevel
            (processnode ctx cs.length numcells st).2.eqlevCanon
            0)) ∧
      ((processnode ctx cs.length numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel
            st.eqlevCanon ∨
        (processnode ctx cs.length numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel
            (Int.ofNat cs.length) ∨
        (processnode ctx cs.length numcells st).1 =
          Int.ofNat st.gcaFirst ∨
        (processnode ctx cs.length numcells st).1 =
          Int.ofNat st.gcaCanon) := by
  have hef' : ¬(({ st with eqlevFirst := cs.length + 1 }.eqlevFirst
      == cs.length) = true) := by simp
  obtain ⟨bs', h1, h2, h3, h4⟩ := processnode_leaf
    (st := { st with eqlevFirst := cs.length + 1 })
    hcinv hginv hcsn hef' hnc
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ :=
    processnode_gateFail_eq (level := cs.length) heq hnc hfail1
      hfail2
  refine ⟨bs', ?_, ?_, ?_, ?_⟩
  · rw [e6]
    exact h1
  · rw [e7, e6, e8]
    exact h2
  · rw [e2, e3, e4, e5]
    exact h3
  · rcases e1 with he | he | he
    · rw [he]
      exact h4
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inr (Or.inr he))

/-- The code-`1` skip is sound at key level: with the codes agreeing
with the first path outright and the rows transported by the
admitted automorphism, the leaf's key is the first leaf's key, and
an incumbent dominating the first leaf absorbs it. -/
theorem auto_keyMax {ctx : Ctx} {cs fs bs : List Nat}
    {lab firstlab canonlab : Array Nat}
    (hcs : cs = fs)
    (hrows : leafRows ctx lab = leafRows ctx firstlab)
    (hfirst : keyLe (pathLeafKey ctx fs firstlab)
      (incKey ctx bs canonlab)) :
    keyMax (incKey ctx bs canonlab) (pathLeafKey ctx cs lab) =
      incKey ctx bs canonlab := by
  have hkey : pathLeafKey ctx cs lab =
      pathLeafKey ctx fs firstlab := by
    rw [pathLeafKey, pathLeafKey, hcs, hrows]
  rw [hkey]
  exact keyMax_eq_left hfirst

/-! # Frames of the internal-node steps -/

section Frames

private theorem prepF_canonlab (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).canonlab = st.canonlab := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canonlab, ite_self]
private theorem prepF_canong (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).canong = st.canong := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canong, ite_self]
private theorem prepF_samerows (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).samerows = st.samerows := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.samerows, ite_self]
private theorem prepF_canonlevel (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).canonlevel = st.canonlevel := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canonlevel, ite_self]
private theorem prepF_firstlab (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).firstlab = st.firstlab := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.firstlab, ite_self]
private theorem prepF_firsttc (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).firsttc = st.firsttc := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.firsttc, ite_self]
private theorem prepF_gcaFirst (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).gcaFirst = st.gcaFirst := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.gcaFirst, ite_self]
private theorem prepF_gcaCanon (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).gcaCanon = st.gcaCanon := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.gcaCanon, ite_self]
private theorem prepF_noncheaplevel (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).noncheaplevel = st.noncheaplevel := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.noncheaplevel, ite_self]
private theorem prepF_allsamelevel (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).allsamelevel = st.allsamelevel := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.allsamelevel, ite_self]
private theorem prepF_orbits (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).orbits = st.orbits := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.orbits, ite_self]
private theorem prepF_lab (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).lab = st.lab := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.lab, ite_self]
private theorem prepF_ptn (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).ptn = st.ptn := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.ptn, ite_self]

/-- The fields `otherNodePrep` never writes: everything the store
invariant, the first-path data, and the unwind bookkeeping read. -/
theorem otherNodePrep_frames (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).canonlab = st.canonlab ∧
    (otherNodePrep level code st).canong = st.canong ∧
    (otherNodePrep level code st).samerows = st.samerows ∧
    (otherNodePrep level code st).canonlevel = st.canonlevel ∧
    (otherNodePrep level code st).firstlab = st.firstlab ∧
    (otherNodePrep level code st).firsttc = st.firsttc ∧
    (otherNodePrep level code st).gcaFirst = st.gcaFirst ∧
    (otherNodePrep level code st).gcaCanon = st.gcaCanon ∧
    (otherNodePrep level code st).noncheaplevel = st.noncheaplevel ∧
    (otherNodePrep level code st).allsamelevel = st.allsamelevel ∧
    (otherNodePrep level code st).orbits = st.orbits ∧
    (otherNodePrep level code st).lab = st.lab ∧
    (otherNodePrep level code st).ptn = st.ptn :=
  ⟨prepF_canonlab level code st,
    prepF_canong level code st,
    prepF_samerows level code st,
    prepF_canonlevel level code st,
    prepF_firstlab level code st,
    prepF_firsttc level code st,
    prepF_gcaFirst level code st,
    prepF_gcaCanon level code st,
    prepF_noncheaplevel level code st,
    prepF_allsamelevel level code st,
    prepF_orbits level code st,
    prepF_lab level code st,
    prepF_ptn level code st⟩

private theorem recF_canonlab (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).canonlab = st.canonlab := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canonlab, ite_self]
private theorem recF_canong (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).canong = st.canong := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canong, ite_self]
private theorem recF_samerows (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).samerows = st.samerows := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.samerows, ite_self]
private theorem recF_canonlevel (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).canonlevel = st.canonlevel := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canonlevel, ite_self]
private theorem recF_firstlab (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).firstlab = st.firstlab := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.firstlab, ite_self]
private theorem recF_firsttc (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).firsttc = st.firsttc := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.firsttc, ite_self]
private theorem recF_gcaFirst (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).gcaFirst = st.gcaFirst := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.gcaFirst, ite_self]
private theorem recF_allsamelevel (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).allsamelevel = st.allsamelevel := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.allsamelevel, ite_self]
private theorem recF_orbits (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).orbits = st.orbits := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.orbits, ite_self]
private theorem recF_lab (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).lab = st.lab := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.lab, ite_self]

/-- The fields `recover` never writes: the store invariant's data,
the first-path arrays, and the unwind targets. -/
theorem recover_frames (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).canonlab = st.canonlab ∧
    (recover n inf level st).canong = st.canong ∧
    (recover n inf level st).samerows = st.samerows ∧
    (recover n inf level st).canonlevel = st.canonlevel ∧
    (recover n inf level st).firstlab = st.firstlab ∧
    (recover n inf level st).firsttc = st.firsttc ∧
    (recover n inf level st).gcaFirst = st.gcaFirst ∧
    (recover n inf level st).allsamelevel = st.allsamelevel ∧
    (recover n inf level st).orbits = st.orbits ∧
    (recover n inf level st).lab = st.lab :=
  ⟨recF_canonlab n inf level st,
    recF_canong n inf level st,
    recF_samerows n inf level st,
    recF_canonlevel n inf level st,
    recF_firstlab n inf level st,
    recF_firsttc n inf level st,
    recF_gcaFirst n inf level st,
    recF_allsamelevel n inf level st,
    recF_orbits n inf level st,
    recF_lab n inf level st⟩

/-- `CanongInv` passes through `otherNodePrep` untouched. -/
theorem canongInv_otherNodePrep {ctx : Ctx} {level code : Nat}
    {st : SearchSt}
    (h : CanongInv ctx st.canong st.canonlab st.samerows) :
    CanongInv ctx (otherNodePrep level code st).canong
      (otherNodePrep level code st).canonlab
      (otherNodePrep level code st).samerows := by
  rw [prepF_canong, prepF_canonlab, prepF_samerows]
  exact h

/-- `CanongInv` passes through `recover` untouched. -/
theorem canongInv_recover {ctx : Ctx} {n inf level : Nat}
    {st : SearchSt}
    (h : CanongInv ctx st.canong st.canonlab st.samerows) :
    CanongInv ctx (recover n inf level st).canong
      (recover n inf level st).canonlab
      (recover n inf level st).samerows := by
  rw [recF_canong, recF_canonlab, recF_samerows]
  exact h

end Frames

/-! # The seed: `firstterminal` starts every thread -/

section Seed

private theorem ftF_firstlab (level : Nat) (st : SearchSt) :
    (firstterminal level st).firstlab = st.lab := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_canonlab (level : Nat) (st : SearchSt) :
    (firstterminal level st).canonlab = st.lab := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_canong (level : Nat) (st : SearchSt) :
    (firstterminal level st).canong = st.canong := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_samerows (level : Nat) (st : SearchSt) :
    (firstterminal level st).samerows = 0 := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_eqlevFirst (level : Nat) (st : SearchSt) :
    (firstterminal level st).eqlevFirst = level := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_gcaFirst (level : Nat) (st : SearchSt) :
    (firstterminal level st).gcaFirst = level := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_gcaCanon (level : Nat) (st : SearchSt) :
    (firstterminal level st).gcaCanon = level := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_allsamelevel (level : Nat) (st : SearchSt) :
    (firstterminal level st).allsamelevel = level := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_firstcode (level : Nat) (st : SearchSt) :
    (firstterminal level st).firstcode =
      st.firstcode.set! (level + 1) codeSentinel := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_lab (level : Nat) (st : SearchSt) :
    (firstterminal level st).lab = st.lab := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

/-- `firstterminal` seeds the first-path machine: the just-installed
first leaf agrees with itself at full depth. -/
theorem firstterminal_firstCodeInv {nn : Nat} {cs : List Nat}
    {st : SearchSt}
    (hsize : st.firstcode.size = nn + 2)
    (hLnn : cs.length ≤ nn)
    (hfc : ∀ i, 1 ≤ i → i ≤ cs.length →
      st.firstcode[i]! = cs[i - 1]!)
    (hclt : ∀ c ∈ cs, c < codeSentinel) :
    FirstCodeInv nn cs cs
      (firstterminal cs.length st).firstcode
      (firstterminal cs.length st).eqlevFirst := by
  rw [ftF_firstcode, ftF_eqlevFirst]
  refine ⟨by rw [Array.size_set!]; exact hsize, hLnn, hclt,
    fun i h1 h2 => ?_, ?_, Nat.le_refl _, Nat.le_refl _,
    fun i h1 h2 => rfl⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact hfc i h1 h2
  · rw [Array.getElem!_set!_self _ _ _ (by rw [hsize]; omega)]

/-- `firstterminal` seeds the store invariant: the installed
`canonlab` with `samerows = 0` is vacuously consistent. -/
theorem firstterminal_canongInv {ctx : Ctx} {level : Nat}
    {st : SearchSt} (hg : st.canong.size = ctx.n) :
    CanongInv ctx (firstterminal level st).canong
      (firstterminal level st).canonlab
      (firstterminal level st).samerows := by
  rw [ftF_canong, ftF_canonlab, ftF_samerows]
  exact canongInv_zero st.lab hg

/-- `firstterminal` seeds the domination clause: the incumbent is
exactly the first leaf, so the first leaf's key is dominated
reflexively. -/
theorem firstterminal_firstKeyLe {ctx : Ctx} {cs : List Nat}
    {st : SearchSt} :
    keyLe
      (pathLeafKey ctx cs (firstterminal cs.length st).firstlab)
      (incKey ctx cs (firstterminal cs.length st).canonlab) := by
  rw [ftF_firstlab, ftF_canonlab]
  show keyCmp _ _ ≠ .gt
  rw [pathLeafKey, incKey, keyCmp_eq_iff.mpr rfl]
  decide

end Seed

/-! # The subtree key under a path prefix -/

/-- The absolute key of a spec subtree below the path codes `cs`. -/
@[expose] def prefixKey (cs : List Nat) (kk : Key) : Key :=
  ⟨cs ++ kk.codes, kk.rows⟩

theorem prefixKey_nil (kk : Key) : prefixKey [] kk = kk := rfl

theorem prefixKey_append (cs ds : List Nat) (kk : Key) :
    prefixKey (cs ++ ds) kk = prefixKey cs (prefixKey ds kk) := by
  rw [prefixKey, prefixKey, prefixKey, List.append_assoc]

/-- Prefixing by common path codes commutes with the key maximum. -/
theorem prefixKey_keyMax :
    ∀ (cs : List Nat) (k1 k2 : Key),
      prefixKey cs (keyMax k1 k2) =
        keyMax (prefixKey cs k1) (prefixKey cs k2)
  | [], k1, k2 => by
    rw [prefixKey_nil, prefixKey_nil, prefixKey_nil]
  | c :: cs, k1, k2 => by
    show (⟨c :: (cs ++ (keyMax k1 k2).codes),
        (keyMax k1 k2).rows⟩ : Key) =
      keyMax ⟨c :: (cs ++ k1.codes), k1.rows⟩
        ⟨c :: (cs ++ k2.codes), k2.rows⟩
    rw [keyMax_cons]
    have ih := prefixKey_keyMax cs k1 k2
    rw [prefixKey, prefixKey, prefixKey] at ih
    rw [← ih]

/-- A spec leaf's key under the path prefix is the path leaf key of
the extended path. -/
theorem prefixKey_leafKey (ctx : Ctx) (cs : List Nat) (code : Nat)
    (r : Array Nat) :
    prefixKey cs ⟨[code, codeSentinel], leafRows ctx r⟩ =
      pathLeafKey ctx (cs ++ [code]) r := by
  rw [prefixKey, pathLeafKey, List.append_assoc]
  rfl

/-- The discrete arm of `specNode`, isolated: at a node whose
refinement is discrete, the subtree key is the leaf key. -/
theorem specNode_discrete {ctx : Ctx} {tcLevel fuel level : Nat}
    {lab ptn : Array Nat} {active numcells : Nat}
    (hdisc : discreteAt (refine ctx level lab ptn active
      numcells).ptn level ctx.n = true) :
    specNode ctx tcLevel (fuel + 1) level lab ptn active numcells =
      ⟨[(refine ctx level lab ptn active numcells).longcode,
          codeSentinel],
        leafRows ctx (refine ctx level lab ptn active
          numcells).lab⟩ := by
  rw [specNode]
  simp only [hdisc, ite_true]

/-- Prefixing a common code moves it into the path. -/
theorem prefixKey_cons (cs : List Nat) (code : Nat) (K : Key) :
    prefixKey cs ⟨code :: K.codes, K.rows⟩ =
      prefixKey (cs ++ [code]) K := by
  rw [prefixKey, prefixKey, List.append_assoc]
  rfl

/-- Prefixing distributes over the seeded list maximum. -/
theorem prefixKey_keysMax :
    ∀ (l : List Key) (b : Key) (cs : List Nat),
      prefixKey cs (keysMax b l) =
        keysMax (prefixKey cs b) (l.map (prefixKey cs))
  | [], b, cs => by rw [keysMax, List.map_nil, keysMax]
  | kk :: t, b, cs => by
    rw [keysMax, List.map_cons, keysMax,
      prefixKey_keysMax t (keyMax b kk) cs, prefixKey_keyMax]

/-- One child key of a spec node: the subtree below individualizing
the `o`-th target-cell vertex of the refined state. -/
@[expose] def specChild (ctx : Ctx) (tcLevel fuel level : Nat)
    (lab ptn : Array Nat) (active numcells : Nat) (o : Nat) : Key :=
  let rs := refine ctx level lab ptn active numcells
  let tcr := specMaketargetcell ctx rs.lab rs.ptn level tcLevel
  let br := breakout rs.lab rs.ptn (level + 1) tcr.1
    rs.lab[tcr.1 + o]!
  specNode ctx tcLevel fuel (level + 1) br.1 br.2.1 br.2.2
    (rs.numcells + 1)

/-- The internal arm of `specNode`, isolated: at a non-discrete node
the subtree key under the path prefix is the maximum of the
children's keys under the path extended by the node's own code. -/
theorem specNode_internal {ctx : Ctx} {tcLevel fuel level : Nat}
    {lab ptn : Array Nat} {active numcells : Nat} {len : Nat}
    (cs : List Nat)
    (hdisc : discreteAt (refine ctx level lab ptn active
      numcells).ptn level ctx.n = false)
    (hlen : (specMaketargetcell ctx
        (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn level
          tcLevel).2.2 = len + 1) :
    prefixKey cs
        (specNode ctx tcLevel (fuel + 1) level lab ptn active
          numcells) =
      keysMax
        (prefixKey (cs ++ [(refine ctx level lab ptn active
            numcells).longcode])
          (specChild ctx tcLevel fuel level lab ptn active numcells
            0))
        ((List.range len).map fun o =>
          prefixKey (cs ++ [(refine ctx level lab ptn active
              numcells).longcode])
            (specChild ctx tcLevel fuel level lab ptn active numcells
              (o + 1))) := by
  rw [specNode]
  simp only [hdisc, Bool.false_eq_true, ite_false, hlen,
    List.range_succ_eq_map, List.map_cons, List.map_map]
  rw [prefixKey_cons, prefixKey_keysMax, List.map_map]
  rfl

/-! # The leaf-guard agreement

The imperative search branches on `numcells == n` where the
specification branches on `discreteAt`; under the boundary-count
accuracy the search invariant carries (`SearchOk.count`), the two
guards agree. -/

/-- Discreteness is exactly a full boundary count. -/
theorem discreteAt_iff_bcount {ptn : Array Nat} {level nn : Nat}
    (hnn : nn = ptn.size) (hend : ptn[ptn.size - 1]! ≤ level) :
    discreteAt ptn level nn = true ↔ bcount ptn level nn = nn := by
  have hnn' : nn ≤ ptn.size := Nat.le_of_eq hnn
  constructor
  · intro hdisc
    have h : List.countP (fun q => decide (ptn[q]! ≤ level))
        (List.range nn) = (List.range nn).length := by
      refine List.countP_eq_length.mpr fun q hq => ?_
      have hqn : q < nn := List.mem_range.mp hq
      obtain ⟨p, hpm, hp1, hp2⟩ := cells_cover (ptn := ptn)
        (level := level) q hqn
      have hsingle : p.1 = p.2 := by
        have h := cells_eq_of_discreteAt hdisc p hpm
        simpa using h
      have hic := cells_isCell hnn' hend p hpm
      have hq1 : p.1 = q := by omega
      have hq2 : p.2 = q := by omega
      rw [hq1, hq2] at hic
      have hcl := hic.2.2.2
      rw [show q + (q + 1 - q) - 1 = q from by omega] at hcl
      simpa using hcl
    rw [List.length_range] at h
    rw [bcount]
    exact h
  · intro hb
    have hb' : List.countP (fun q => decide (ptn[q]! ≤ level))
        (List.range nn) = (List.range nn).length := by
      rw [List.length_range]
      rw [bcount] at hb
      exact hb
    have hall : ∀ q, q < nn → ptn[q]! ≤ level := by
      intro q hq
      have h := List.countP_eq_length.mp hb' q
        (List.mem_range.mpr hq)
      simpa using h
    rw [discreteAt, List.all_eq_true]
    intro p hpm
    have hic := cells_isCell hnn' hend p hpm
    have hle := cells_le p hpm
    have hbnd := cells_bound hnn' hend p hpm
    rcases Decidable.em (p.1 = p.2) with heq | hne
    · simpa using heq
    · exfalso
      have hlt : p.1 < p.2 := by omega
      have hint := hic.2.2.1 p.1 (Nat.le_refl _)
        (by omega)
      have := hall p.1 (by omega)
      omega

/-! # The `DomOk` record

The per-node entry invariant of the maximality induction, at a node
about to refine at `level = cs.length + 1`. Two deliberate design
decisions, so the next sitting does not re-litigate them:

- **Incumbent-maximality is a conclusion shape, not a record
  clause.** Following `searchNode_eq`'s `incMax` contract, each
  quartet theorem concludes
  `incKey ctx bs' out.canonlab =
    keyMax (incKey ctx bs st.canonlab) (prefixKey cs (specNode …))`
  rather than storing a fold over visited leaves in the record; the
  `keysMax` algebra composes the per-child equations across the
  sweep, and pruned children contribute through the verdict lemmas
  (`frozen_lt_keyCmp`, `auto_keyMax`, `childKey_of_orbPruned`).

- **Unwinding-correctness is a loop obligation, not a record
  clause.** The orbit consultation in `firstChildLoop` is justified
  by the `stab` clause held at the loop's own node: a loop that
  continues (return level ≥ its level) received only generators
  whose carrier leaves lie inside its subtree, so
  `cellStab_of_scatter` re-establishes `stab` for the newly admitted
  generators; an early unwind exits the loop and discharges nothing.
  The gca return levels enter through `processnode_leaf`'s return
  disjunction, not through a stored clause. -/

variable {n k : Nat}

/-- The entry invariant of the maximality induction at a node about
to refine at `level = cs.length + 1`: the search skeleton, both
comparison machines, the store invariant, cell stabilization of every
recorded generator at this node, and domination of the first leaf by
the incumbent. -/
structure DomOk (G : Colored n k) (ctx : Ctx) (cs bs fs : List Nat)
    (numcells : Nat) (st : SearchSt) : Prop where
  searchOk : SearchOk G (cs.length + 1) numcells st
  codeInv : CodeCmpInv n cs bs st.canoncode st.canonlevel
    st.eqlevCanon st.compCanon
  firstInv : FirstCodeInv n cs fs st.firstcode st.eqlevFirst
  canongInv : CanongInv ctx st.canong st.canonlab st.samerows
  stab : ∀ γ ∈ st.genTrace,
    CellStab st.ptn (cs.length + 1) st.lab γ
  firstKeyLe : keyLe (pathLeafKey ctx fs st.firstlab)
    (incKey ctx bs st.canonlab)

end Hex.GraphIso.Nauty

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Codes
public import HexGraphIso.Nauty.Invariant.Leaves
public import HexGraphIso.Nauty.Spec.CanonSpec
public import HexGraphIso.Nauty.Invariant.Refine
public import HexGraphIso.Nauty.Invariant.Trace
public import HexGraphIso.Nauty.Invariant.Stabilize
public import HexGraphIso.Nauty.Invariant.Autos
public import HexGraphIso.Nauty.SmallCell.Transitive
import all HexGraphIso.Nauty.Invariant.Store
import all HexGraphIso.Nauty.SmallCell.Transitive
import all HexGraphIso.Nauty.Search.State

public section

/-!
The domination layer: the key-level reading of the search state's
incumbent, and the per-arm key verdicts of the leaf event. Together
with the comparison machines of `Invariant/Codes` and the row clause
of `Invariant/Leaves`, these are what the maximality induction applies
at each `processnode` arm to conclude that the traced key dominates
every visited leaf, which is the `canonSpecKey G = tracedKey G`
equality the replay spine consumes.

The incumbent's key is `⟨bs ++ [codeSentinel], leafRows ctx canonlab⟩`
for the ghost code list `bs` tracked by `CodeCmpInv`. A leaf of the
current path has key `⟨cs ++ [codeSentinel], leafRows ctx lab⟩`. The
verdict lemmas translate the imperative comparison state into
`keyCmp` on those keys:

- `compCanon = -1` or `1` (frozen divergence): the code machine's
  payoff lemmas decide the whole comparison (`codeInv_keyCmp_lt`,
  `codeInv_keyCmp_gt` at `ext := [codeSentinel]`).
- `compCanon = 0` with the path shorter than the incumbent: the leaf
  ends in the sentinel where the incumbent still has a real code, so
  the leaf compares above (`tied_short_keyCmp_gt`). That is why the
  short-leaf install (`level < canonlevel → code 3`) is correct.
- `compCanon = 0` at the incumbent's depth: the code lists are equal
  outright and the rows decide (`tied_full_keyCmp`), which is the
  `testcanlab` outcome by `leafEvent_faithful`.

The leaf event is covered arm by arm: `processnode_leaf` (the
off-first-path leaf), `processnode_leafFirst` (the first-path-agreeing
leaf failing the admission test, through the reduction
`processnode_gateFail_eq`), `processnode_auto` with `auto_keyMax` (the
leaf passing the admission test: the comparison state is untouched,
the sentinel guard supplies exact path depth, and the mandatory
`isautom` scan validates the admitted scatter), `recover_machines`
with the `recover_frames`/`compareCodes_frames` threading, and the
`firstterminal_*` seeds for all four threads.

The statement layer of the induction is the `DomOk` record (its
section comment gives the two decisions its shape encodes), the
path-prefix key algebra (`prefixKey` with its `keyMax`/`keysMax`
distribution laws), the two `specNode` arm isolations
(`specNode_discrete`, and `specNode_internal` with `specChild`), and
the leaf-guard agreement `discreteAt_iff_bcount`, which aligns the
imperative `numcells == n` dispatch with the specification's
`discreteAt` through `SearchOk.count`.

A dominated sibling is absorbed in a different place in each of the
two unwind modes.

- A frozen unwind absorbs locally. After a code-4 leaf with the
  machine frozen downward, `pruneLevel`'s `eqlevCanon` and
  `allsamelevel - 1` forms never return below the recorded
  divergence, so the truncated path of every loop left behind still
  contains that divergence: `frozen_take_keyLe` dominates each such
  sibling's whole subtree, loop by loop, on the way up. In this mode
  every quartet theorem concludes the full `keyMax` equation.
- A generator return absorbs wholesale at the gca loop. After a
  code-1 or code-2 admission, the intermediate loops conclude nothing
  locally. The quartet theorems hand up the payload: the admitted
  scatter, its carry between the guiding sibling's and the current
  child's individualized vertices, and its cell stabilization at the
  gca node. The loop at the returned gca level identifies the whole
  current child subtree with the guiding sibling's via
  `childKey_of_carried`, whose key its own fold has already absorbed.
  The conclusion is therefore a disjunction: normal exit or frozen
  unwind with the full equation, generator unwind with the payload.
- The in-loop orbit skips (`st.orbits[tv]! == tv` failing) follow from
  `orbConn_of_ptr`, `wordConn_symm`, `cellStab_of_scatter` and
  `childKey_of_carried` at the loop's own node.

Three supporting facts come from the rest of this layer. The
cheapautom subtree fact is `descPath_leafRows_all` with its
`leafRows_eq_of_descPaths` corollary. Store validity across the leaf
event is `genTraceOk_processnode` and `processnode_checkAutom`. The
`(fix, mcr)` ledger is `Invariant/Autos`, whose `longprune_carried`
and `shortprune_carried` meet `childKey_of_carried`'s hypotheses
exactly. `DomOk` carries both ledgers (`genTraceOk`, `autosOk`), both
ride the internal steps by frame (`compareCodes_store`,
`recover_store`, `firstterminal_store`, transported by
`genTraceOk_of_eq` and `autosOk_of_eq`), and the admission event
preserves store validity under the record. The one row premise the
event needs is the code-2 tie, which is local and proved by
`rows_eq_of_testcanlab_tie`. Code 1 needs no descent geometry
invariant: `processnode` checks the first-path sentinel at
`level + 1` and scans the scatter with `isautom` before admission, so
`firstCodeInv_eq_of_live` supplies equal path codes and
`processnode_checkAutom` validates the generator.

The mutual induction over the four search functions follows the
`canonlab_cellsReach` skeleton (whose composite helpers
`recover_out`/`processnode_searchOk`/`canonlab_or_of` are public) and
threads `DomOk`. It discharges leaf arms by `processnode_leaf`,
`processnode_leafFirst` and `processnode_auto` + `auto_keyMax`
through `specNode_discrete`/`prefixKey_leafKey`, internal arms by
`specNode_internal` (whose `keysMax` fold matches the loop
literally), machines by `compareCodes_codeInv`/`recover_machines`
and the frames, dispatch by `discreteAt_iff_bcount`, and unwinds by
the two modes above. At the root, `specNode_achieved` gives the
achieved direction and the induction the domination direction, so
`canonSpecKey G = tracedKey G`.
-/

namespace Hex.GraphIso.Nauty

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-! # The incumbent key -/

/-- The incumbent's key: the ghost code list with the sentinel
stamped, and the stored best leaf's rows. -/
@[expose] def incKey (ctx : Ctx n) (bs : List Nat)
    (canonlab : Array Nat) : Key n :=
  ⟨bs ++ [codeSentinel], leafRows ctx canonlab⟩

/-- A leaf key of the current path. -/
@[expose] def pathLeafKey (ctx : Ctx n) (cs : List Nat)
    (lab : Array Nat) : Key n :=
  ⟨cs ++ [codeSentinel], leafRows ctx lab⟩

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
    (hshort : cs.length < bs.length) (r1 r2 : List (VSet n)) :
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
    (hlen : cs.length = bs.length) (r1 r2 : List (VSet n)) :
    keyCmp ⟨cs ++ [codeSentinel], r1⟩ ⟨bs ++ [codeSentinel], r2⟩ =
      listCmp VSet.rowCmp r1 r2 := by
  rw [codeInv_eq_of_tied hinv hlen, keyCmp_codes_eq]

/-- The downward-frozen verdict at a leaf, in incumbent-key form. -/
theorem frozen_lt_keyCmp {nn : Nat} {cs bs : List Nat} {ctx : Ctx n}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    {lab canonlab : Array Nat}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon
      (-1)) :
    keyCmp (pathLeafKey ctx cs lab) (incKey ctx bs canonlab) =
      .lt :=
  codeInv_keyCmp_lt hinv [codeSentinel] _ _

/-- The upward-frozen verdict at a leaf, in incumbent-key form. -/
theorem frozen_gt_keyCmp {nn : Nat} {cs bs : List Nat} {ctx : Ctx n}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    {lab canonlab : Array Nat}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon 1) :
    keyCmp (pathLeafKey ctx cs lab) (incKey ctx bs canonlab) =
      .gt :=
  codeInv_keyCmp_gt hinv [codeSentinel] _ _

/-! # `processnode` arm characterizations -/

private theorem pushAuto_lab (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).lab = st.lab := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_ptn (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).ptn = st.ptn := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_compCanon (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).compCanon = st.compCanon := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_eqlevCanon (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).eqlevCanon = st.eqlevCanon := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_canoncode (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).canoncode = st.canoncode := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_canonlevel (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).canonlevel = st.canonlevel := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_canonlab (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).canonlab = st.canonlab := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_canong (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).canong = st.canong := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_samerows (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).samerows = st.samerows := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_eqlevFirst (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).eqlevFirst = st.eqlevFirst := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_gcaFirst (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).gcaFirst = st.gcaFirst := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_noncheaplevel (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).noncheaplevel = st.noncheaplevel := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_allsamelevel (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).allsamelevel = st.allsamelevel := by
  rw [pushAuto]; split <;> rfl

@[expose] def pruneLevel (noncheaplevel allsamelevel : Nat)
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

/-- A faithful comparison machine records its agreement or divergence at
a genuine path level. -/
theorem CodeCmpInv.eqlev_nonneg {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon compCanon : Int}
    (h : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon compCanon) :
    0 ≤ eqlevCanon := by
  rcases h.tri with ⟨_, heq, _⟩ | ⟨j, _, _, _, heq, _⟩
  · rw [heq]
    exact Int.natCast_nonneg _
  · rw [heq]
    exact Int.natCast_nonneg _

/-- The shared prune tail either returns no lower than the frozen code
divergence or jumps to the level immediately above the saved cheap-cell
boundary.  These are the two logically different early-return modes. -/
theorem pruneLevel_split {noncheaplevel allsamelevel : Nat}
    {eqlevCanon : Int} (heqlev : 0 ≤ eqlevCanon) :
    Int.ofNat eqlevCanon.toNat ≤
        pruneLevel noncheaplevel allsamelevel eqlevCanon ∨
      pruneLevel noncheaplevel allsamelevel eqlevCanon =
        Int.ofNat noncheaplevel - 1 := by
  have heqCast : Int.ofNat eqlevCanon.toNat = eqlevCanon := by
    change (eqlevCanon.toNat : Int) = eqlevCanon
    exact Int.toNat_of_nonneg heqlev
  unfold pruneLevel
  split <;> rename_i hsave
  · dsimp only
    split <;> rename_i hboundary
    · exact Or.inr rfl
    · left
      rw [heqCast]
      omega
  · dsimp only
    split <;> rename_i hboundary
    · exact Or.inr rfl
    · left
      rw [heqCast]
      omega

/-- The shared prune tail always returns below its positive saved
cheap-cell boundary. -/
theorem pruneLevel_lt {noncheaplevel allsamelevel : Nat}
    {eqlevCanon : Int} :
    pruneLevel noncheaplevel allsamelevel eqlevCanon <
      Int.ofNat noncheaplevel := by
  unfold pruneLevel
  split <;> dsimp only <;> split <;>
    simp only [Int.ofNat_eq_natCast] at * <;> omega

/-- A nonnegative comparison depth and positive saved boundary make the
shared prune return a genuine natural-number level. -/
theorem pruneLevel_nonneg {noncheaplevel allsamelevel : Nat}
    {eqlevCanon : Int} (hpositive : 0 < noncheaplevel)
    (heqlev : 0 ≤ eqlevCanon) :
    0 ≤ pruneLevel noncheaplevel allsamelevel eqlevCanon := by
  unfold pruneLevel
  split <;> dsimp only <;> split <;>
    simp only [Int.ofNat_eq_natCast] at * <;> omega

/-- The frozen-downward fast arm: the comparison state is untouched
and the shared prune tail decides the unwind level. -/
private theorem pushAuto_gcaCanon (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).gcaCanon = st.gcaCanon := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_firstcode (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).firstcode = st.firstcode := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_firstlab (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).firstlab = st.firstlab := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_firsttc (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).firsttc = st.firsttc := by
  rw [pushAuto]; split <;> rfl

theorem recover_machines {nn inf : Nat} {cs bs fs : List Nat}
    {st : Search n} {lvl : Nat}
    (hc : (st.compCanon ≤ 0 ∧
        CodeCmpInv nn cs bs st.canoncode st.canonlevel st.eqlevCanon
          st.compCanon) ∨
      CodeCmpInv nn cs bs st.canoncode st.canonlevel st.eqlevCanon 0)
    (hf : FirstCodeInv nn cs fs st.firstcode st.eqlevFirst)
    (hlvl : lvl ≤ cs.length) :
    CodeCmpInv nn (cs.take lvl) bs
        (recover n inf lvl st).canoncode
        (recover n inf lvl st).canonlevel
        (recover n inf lvl st).eqlevCanon
        (recover n inf lvl st).compCanon ∧
      FirstCodeInv nn (cs.take lvl) fs
        (recover n inf lvl st).firstcode
        (recover n inf lvl st).eqlevFirst := by
  refine ⟨?_, recover_firstCodeInv hf hlvl⟩
  rcases hc with ⟨hle, hinv⟩ | hinv
  · exact recover_codeInv hinv hle hlvl
  · exact recover_codeInv_reset hinv hlvl

/-! # The first-path-agreeing leaf: the code-`1` admission test -/

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

/-- A first-to-current scatter preserves its fixed `n`-slot workspace
size. -/
theorem firstScatter_size (n : Nat) (lab₁ lab₂ : Array Nat) :
    (firstScatter n lab₁ lab₂).size = n := by
  rw [firstScatter, foldl_scatter_size, Array.size_replicate]

/-- A full scatter from a permutation labelling overwrites every slot,
so its result is independent of the initial workspace contents. -/
theorem scatter_eq_of_full {lab₁ lab₂ base base' : Array Nat} {nn : Nat}
    (hbase : base.size = nn) (hbase' : base'.size = nn)
    (hsize : lab₁.size = nn) (hok : LabOk lab₁ nn)
    (hinj : LabInj lab₁ nn) :
    (List.range nn).foldl (fun r i => r.set! lab₁[i]! lab₂[i]!) base =
      (List.range nn).foldl
        (fun r i => r.set! lab₁[i]! lab₂[i]!) base' := by
  have hs := foldl_scatter_size lab₁ lab₂ (List.range nn) base
  have hs' := foldl_scatter_size lab₁ lab₂ (List.range nn) base'
  apply Array.ext
  · rw [hs, hs', hbase, hbase']
  · intro v hv hv'
    have hvn : v < nn := by rw [hs, hbase] at hv; exact hv
    obtain ⟨i, hi, hiv⟩ := labInj_surj
      (Nat.le_of_eq hsize.symm) hok hinj v hvn
    have hget := foldl_scatter_getElem (lab₂ := lab₂) hinj
      (base := base) (fun j hj => by
        rw [hbase]
        exact hok j (by rw [hsize]; exact hj))
      (m := nn) (Nat.le_refl _) hi
    have hget' := foldl_scatter_getElem (lab₂ := lab₂) hinj
      (base := base') (fun j hj => by
        rw [hbase']
        exact hok j (by rw [hsize]; exact hj))
      (m := nn) (Nat.le_refl _) hi
    rw [hiv] at hget hget'
    simpa only [
      getElem!_pos ((List.range nn).foldl
        (fun r i => r.set! lab₁[i]! lab₂[i]!) base) v hv,
      getElem!_pos ((List.range nn).foldl
        (fun r i => r.set! lab₁[i]! lab₂[i]!) base') v hv'] using
        hget.trans hget'.symm

private theorem id_run_eq {α : Type} (x : Id α) : Id.run x = x := rfl

private theorem pushAuto_orbits (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).orbits = st.orbits := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_numorbits (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).numorbits = st.numorbits := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_cosetindex (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).cosetindex = st.cosetindex := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_maxlevel (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).maxlevel = st.maxlevel := by
  rw [pushAuto]; split <;> rfl

/-- The code-`1` arm: a first-path-agreeing leaf passing the
admission test records a generator and unwinds to `gcaFirst` with
the whole comparison state untouched. -/
@[expose] def canonScatter (n : Nat) (canonlab lab : Array Nat) :
    Array Nat := Id.run do
  let mut workperm := Array.replicate n 0
  for i in [0 : n] do
    workperm := workperm.set! canonlab[i]! lab[i]!
  return workperm

theorem canonScatter_eq_firstScatter (n : Nat)
    (canonlab lab : Array Nat) :
    canonScatter n canonlab lab = firstScatter n canonlab lab := by
  rw [canonScatter, firstScatter]
  simp only [Id.run_bind, Id.run_pure]
  rw [forIn_range_eq3, forIn_scatter_eq]
  exact id_run_eq _

/-- The bounded-ledger effect of the shared code-three/code-four tail. -/
@[expose] def pruneAutos (level : Nat)
    (st : Search n) : Array (VSet n × VSet n) :=
  if level = st.noncheaplevel then st.autos
  else (pushAuto st
    (fmptn st.lab st.ptn st.noncheaplevel n)).autos

/-- Whenever the shared tail admits its implicit pair, bounded workspace
capacity makes that pair the exact newest entry read by `shortprune`. -/
theorem pruneAutos_back {level : Nat} {st : Search n}
    (hworkspace : WorkspaceOk st) (hne : level ≠ st.noncheaplevel) :
    (pruneAutos level st).back? =
      some (fmptn st.lab st.ptn st.noncheaplevel n) := by
  unfold pruneAutos
  rw [ite_eq_right hne]
  exact pushAuto_back hworkspace.1

/-- The frozen-downward fast arm has exactly the shared prune-tail ledger
effect. -/
theorem auto_keyMax {ctx : Ctx n} {cs fs bs : List Nat}
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

private theorem prepF_canonlab (level code : Nat) (st : Search n) :
    (compareCodes level code st).canonlab = st.canonlab := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.canonlab, ite_self]
private theorem prepF_canong (level code : Nat) (st : Search n) :
    (compareCodes level code st).canong = st.canong := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.canong, ite_self]
private theorem prepF_samerows (level code : Nat) (st : Search n) :
    (compareCodes level code st).samerows = st.samerows := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.samerows, ite_self]
private theorem prepF_canonlevel (level code : Nat) (st : Search n) :
    (compareCodes level code st).canonlevel = st.canonlevel := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.canonlevel, ite_self]
private theorem prepF_firstlab (level code : Nat) (st : Search n) :
    (compareCodes level code st).firstlab = st.firstlab := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.firstlab, ite_self]
private theorem prepF_firsttc (level code : Nat) (st : Search n) :
    (compareCodes level code st).firsttc = st.firsttc := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.firsttc, ite_self]
private theorem prepF_gcaFirst (level code : Nat) (st : Search n) :
    (compareCodes level code st).gcaFirst = st.gcaFirst := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.gcaFirst, ite_self]
private theorem prepF_gcaCanon (level code : Nat) (st : Search n) :
    (compareCodes level code st).gcaCanon = st.gcaCanon := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.gcaCanon, ite_self]
private theorem prepF_noncheaplevel (level code : Nat) (st : Search n) :
    (compareCodes level code st).noncheaplevel = st.noncheaplevel := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.noncheaplevel, ite_self]
private theorem prepF_allsamelevel (level code : Nat) (st : Search n) :
    (compareCodes level code st).allsamelevel = st.allsamelevel := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.allsamelevel, ite_self]
private theorem prepF_orbits (level code : Nat) (st : Search n) :
    (compareCodes level code st).orbits = st.orbits := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.orbits, ite_self]
private theorem prepF_lab (level code : Nat) (st : Search n) :
    (compareCodes level code st).lab = st.lab := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.lab, ite_self]
private theorem prepF_ptn (level code : Nat) (st : Search n) :
    (compareCodes level code st).ptn = st.ptn := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.ptn, ite_self]

/-- The fields `compareCodes` never writes: everything the store
invariant, the first-path data, and the unwind bookkeeping read. -/
theorem compareCodes_frames (level code : Nat) (st : Search n) :
    (compareCodes level code st).canonlab = st.canonlab ∧
    (compareCodes level code st).canong = st.canong ∧
    (compareCodes level code st).samerows = st.samerows ∧
    (compareCodes level code st).canonlevel = st.canonlevel ∧
    (compareCodes level code st).firstlab = st.firstlab ∧
    (compareCodes level code st).firsttc = st.firsttc ∧
    (compareCodes level code st).gcaFirst = st.gcaFirst ∧
    (compareCodes level code st).gcaCanon = st.gcaCanon ∧
    (compareCodes level code st).noncheaplevel = st.noncheaplevel ∧
    (compareCodes level code st).allsamelevel = st.allsamelevel ∧
    (compareCodes level code st).orbits = st.orbits ∧
    (compareCodes level code st).lab = st.lab ∧
    (compareCodes level code st).ptn = st.ptn :=
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

private theorem recF_canonlab (n inf level : Nat) (st : Search n) :
    (recover n inf level st).canonlab = st.canonlab := by
  rw [recover, recoverLevels, recoverPtn]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.canonlab, ite_self]
private theorem recF_canong (n inf level : Nat) (st : Search n) :
    (recover n inf level st).canong = st.canong := by
  rw [recover, recoverLevels, recoverPtn]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.canong, ite_self]
private theorem recF_samerows (n inf level : Nat) (st : Search n) :
    (recover n inf level st).samerows = st.samerows := by
  rw [recover, recoverLevels, recoverPtn]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.samerows, ite_self]
private theorem recF_canonlevel (n inf level : Nat) (st : Search n) :
    (recover n inf level st).canonlevel = st.canonlevel := by
  rw [recover, recoverLevels, recoverPtn]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.canonlevel, ite_self]
private theorem recF_firstlab (n inf level : Nat) (st : Search n) :
    (recover n inf level st).firstlab = st.firstlab := by
  rw [recover, recoverLevels, recoverPtn]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.firstlab, ite_self]
private theorem recF_firsttc (n inf level : Nat) (st : Search n) :
    (recover n inf level st).firsttc = st.firsttc := by
  rw [recover, recoverLevels, recoverPtn]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.firsttc, ite_self]
private theorem recF_gcaFirst (n inf level : Nat) (st : Search n) :
    (recover n inf level st).gcaFirst = st.gcaFirst := by
  rw [recover, recoverLevels, recoverPtn]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.gcaFirst, ite_self]
private theorem recF_allsamelevel (n inf level : Nat) (st : Search n) :
    (recover n inf level st).allsamelevel = st.allsamelevel := by
  rw [recover, recoverLevels, recoverPtn]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.allsamelevel, ite_self]
private theorem recF_orbits (n inf level : Nat) (st : Search n) :
    (recover n inf level st).orbits = st.orbits := by
  rw [recover, recoverLevels, recoverPtn]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.orbits, ite_self]
private theorem recF_lab (n inf level : Nat) (st : Search n) :
    (recover n inf level st).lab = st.lab := by
  rw [recover, recoverLevels, recoverPtn]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.lab, ite_self]

/-- The fields `recover` never writes: the store invariant's data,
the first-path arrays, and the unwind targets. -/
theorem recover_frames (n inf level : Nat) (st : Search n) :
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

/-- `CanongInv` passes through `compareCodes` untouched. -/
theorem canongInv_compareCodes {ctx : Ctx n} {level code : Nat}
    {st : Search n}
    (h : CanongInv ctx st.canong st.canonlab st.samerows) :
    CanongInv ctx (compareCodes level code st).canong
      (compareCodes level code st).canonlab
      (compareCodes level code st).samerows := by
  rw [prepF_canong, prepF_canonlab, prepF_samerows]
  exact h

/-- `CanongInv` passes through `recover` untouched. -/
theorem canongInv_recover {ctx : Ctx n} {inf level : Nat}
    {st : Search n}
    (h : CanongInv ctx st.canong st.canonlab st.samerows) :
    CanongInv ctx (recover n inf level st).canong
      (recover n inf level st).canonlab
      (recover n inf level st).samerows := by
  rw [recF_canong, recF_canonlab, recF_samerows]
  exact h

private theorem prepF_genTrace (level code : Nat) (st : Search n) :
    (compareCodes level code st).genTrace = st.genTrace := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.genTrace, ite_self]

private theorem prepF_autos (level code : Nat) (st : Search n) :
    (compareCodes level code st).autos = st.autos := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.autos, ite_self]

private theorem recF_genTrace (n inf level : Nat) (st : Search n) :
    (recover n inf level st).genTrace = st.genTrace := by
  rw [recover, recoverLevels, recoverPtn]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.genTrace, ite_self]

private theorem recF_autos (n inf level : Nat) (st : Search n) :
    (recover n inf level st).autos = st.autos := by
  rw [recover, recoverLevels, recoverPtn]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite Search.autos, ite_self]

/-- The store fields no internal step writes: the generator trace and
the bounded autos workspace pass through `compareCodes` and
`recover` untouched, so both ledger clauses ride the unwind and the
comparison step by frame. -/
theorem compareCodes_store (level code : Nat) (st : Search n) :
    (compareCodes level code st).genTrace = st.genTrace ∧
    (compareCodes level code st).autos = st.autos :=
  ⟨prepF_genTrace level code st, prepF_autos level code st⟩

theorem recover_store (n inf level : Nat) (st : Search n) :
    (recover n inf level st).genTrace = st.genTrace ∧
    (recover n inf level st).autos = st.autos :=
  ⟨recF_genTrace n inf level st, recF_autos n inf level st⟩

end Frames

/-! # The seed: `firstterminal` starts every thread -/

section Seed

private theorem ftF_canonlab (level : Nat) (st : Search n) :
    (firstterminal level st).canonlab = st.lab := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_canong (level : Nat) (st : Search n) :
    (firstterminal level st).canong = st.canong := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_samerows (level : Nat) (st : Search n) :
    (firstterminal level st).samerows = 0 := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_eqlevFirst (level : Nat) (st : Search n) :
    (firstterminal level st).eqlevFirst = level := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_firstcode (level : Nat) (st : Search n) :
    (firstterminal level st).firstcode =
      st.firstcode.set! (level + 1) codeSentinel := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

/-- `firstterminal` seeds the first-path machine: the just-installed
first leaf agrees with itself at full depth. -/
theorem firstterminal_firstCodeInv {nn : Nat} {cs : List Nat}
    {st : Search n}
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
theorem firstterminal_canongInv {ctx : Ctx n} {level : Nat}
    {st : Search n} (hg : st.canong.size = n) :
    CanongInv ctx (firstterminal level st).canong
      (firstterminal level st).canonlab
      (firstterminal level st).samerows := by
  rw [ftF_canong, ftF_canonlab, ftF_samerows]
  exact canongInv_zero st.lab hg

private theorem ftF_genTrace (level : Nat) (st : Search n) :
    (firstterminal level st).genTrace = st.genTrace := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_autos (level : Nat) (st : Search n) :
    (firstterminal level st).autos = st.autos := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

/-- `firstterminal` installs the first leaf without touching either
store, so both ledger clauses are carried across the seed. -/
theorem firstterminal_store (level : Nat) (st : Search n) :
    (firstterminal level st).genTrace = st.genTrace ∧
    (firstterminal level st).autos = st.autos :=
  ⟨ftF_genTrace level st, ftF_autos level st⟩

end Seed

/-! # The subtree key under a path prefix -/

/-- The absolute key of a spec subtree below the path codes `cs`. -/
@[expose] def prefixKey (cs : List Nat) (kk : Key n) : Key n :=
  ⟨cs ++ kk.codes, kk.rows⟩

theorem prefixKey_nil (kk : Key n) : prefixKey [] kk = kk := rfl

/-- Prefixing by common path codes commutes with the key maximum. -/
theorem prefixKey_keyMax :
    ∀ (cs : List Nat) (k1 k2 : Key n),
      prefixKey cs (keyMax k1 k2) =
        keyMax (prefixKey cs k1) (prefixKey cs k2)
  | [], k1, k2 => by
    rw [prefixKey_nil, prefixKey_nil, prefixKey_nil]
  | c :: cs, k1, k2 => by
    show (⟨c :: (cs ++ (keyMax k1 k2).codes),
        (keyMax k1 k2).rows⟩ : Key n) =
      keyMax ⟨c :: (cs ++ k1.codes), k1.rows⟩
        ⟨c :: (cs ++ k2.codes), k2.rows⟩
    rw [keyMax_cons]
    have ih := prefixKey_keyMax cs k1 k2
    rw [prefixKey, prefixKey, prefixKey] at ih
    rw [← ih]

/-- A spec leaf's key under the path prefix is the path leaf key of
the extended path. -/
theorem prefixKey_leafKey (ctx : Ctx n) (cs : List Nat) (code : Nat)
    (r : Array Nat) :
    prefixKey cs ⟨[code, codeSentinel], leafRows ctx r⟩ =
      pathLeafKey ctx (cs ++ [code]) r := by
  rw [prefixKey, pathLeafKey, List.append_assoc]
  rfl

/-- The discrete arm of `specNode`, isolated: at a node whose
refinement is discrete, the subtree key is the leaf key. -/
theorem specNode_discrete {ctx : Ctx n} {tcLevel fuel level : Nat}
    {lab ptn : Array Nat} {active : VSet n} {numcells : Nat}
    (hdisc : discreteAt (refine ctx level lab ptn active
      numcells).ptn level n = true) :
    specNode ctx tcLevel (fuel + 1) level lab ptn active numcells =
      ⟨[(refine ctx level lab ptn active numcells).longcode,
          codeSentinel],
        leafRows ctx (refine ctx level lab ptn active
          numcells).lab⟩ := by
  rw [specNode]
  simp only [hdisc, ite_true]

/-- Prefixing a common code moves it into the path. -/
theorem prefixKey_cons (cs : List Nat) (code : Nat) (K : Key n) :
    prefixKey cs ⟨code :: K.codes, K.rows⟩ =
      prefixKey (cs ++ [code]) K := by
  rw [prefixKey, prefixKey, List.append_assoc]
  rfl

/-- Prefixing distributes over the seeded list maximum. -/
theorem prefixKey_keysMax :
    ∀ (l : List (Key n)) (b : Key n) (cs : List Nat),
      prefixKey cs (keysMax b l) =
        keysMax (prefixKey cs b) (l.map (prefixKey cs))
  | [], b, cs => by rw [keysMax, List.map_nil, keysMax]
  | kk :: t, b, cs => by
    rw [keysMax, List.map_cons, keysMax,
      prefixKey_keysMax t (keyMax b kk) cs, prefixKey_keyMax]

/-- One child key of a spec node: the subtree below individualizing
the `o`-th target-cell vertex of the refined state. -/
@[expose] def specChild (ctx : Ctx n) (tcLevel fuel level : Nat)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) (o : Nat) : Key n :=
  let rs := refine ctx level lab ptn active numcells
  let tcr := specMaketargetcell ctx rs.lab rs.ptn level tcLevel
  let br := breakout n rs.lab rs.ptn (level + 1) tcr.1
    rs.lab[tcr.1 + o]!
  specNode ctx tcLevel fuel (level + 1) br.1 br.2.1 br.2.2
    (rs.numcells + 1)

/-- The internal arm of `specNode`, isolated: at a non-discrete node
the subtree key under the path prefix is the maximum of the
children's keys under the path extended by the node's own code. -/
theorem specNode_internal {ctx : Ctx n} {tcLevel fuel level : Nat}
    {lab ptn : Array Nat} {active : VSet n} {numcells : Nat} {len : Nat}
    (cs : List Nat)
    (hdisc : discreteAt (refine ctx level lab ptn active
      numcells).ptn level n = false)
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
about to refine at `level = cs.length + 1`. Two facts about its
shape:

- **Incumbent-maximality is a conclusion, not a record clause.**
  Following `searchNode_eq`'s `incMax` contract, each quartet theorem
  concludes
  `incKey ctx bs' out.canonlab =
    keyMax (incKey ctx bs st.canonlab) (prefixKey cs (specNode …))`
  rather than storing a fold over visited leaves in the record. The
  `keysMax` algebra composes the per-child equations across the child
  loop, and pruned children contribute through the verdict lemmas
  (`frozen_lt_keyCmp`, `auto_keyMax`, `childKey_of_orbPruned`).

- **Unwinding-correctness is proved at the loop, not stored in the
  record.** The orbit consultation in `firstChildLoop` is justified
  by the `stab` clause held at the loop's own node: a loop that
  continues (return level at least its own level) received only
  generators whose carrier leaves lie inside its subtree, so
  `cellStab_of_scatter` re-establishes `stab` for the newly admitted
  generators. An early unwind exits the loop and proves nothing
  there. The gca return levels enter through `processnode_leaf`'s
  return disjunction, not through a stored clause. -/

variable {n k : Nat}

/-- The entry invariant of the maximality induction at a node about
to refine at `level = cs.length + 1`: the search skeleton, both
comparison machines, the store invariant, cell stabilization of every
recorded generator at this node, and the two ledgers the pruning arms
consume.

`genTraceOk` is store validity: every recorded generator is a checked
automorphism, which is what `childKey_of_carried` needs of the
carriers the gca returns hand up. `autosOk` is the `(fix, mcr)`
ledger of `Invariant/Autos`, anchored at the root partition `rptn`/`rlab`
where it is unconditional; the `shortprune`/`longprune` arms move a
single pair down the path with `pairOk_descend` at the point of
use. -/
structure DomOk (G : Colored n k) (ctx : Ctx n) (rlab rptn : Array Nat)
    (cs bs fs : List Nat) (numcells : Nat) (st : Search n) : Prop where
  searchOk : SearchOk G (cs.length + 1) numcells st
  codeInv : CodeCmpInv n cs bs st.canoncode st.canonlevel
    st.eqlevCanon st.compCanon
  firstInv : FirstCodeInv n cs fs st.firstcode st.eqlevFirst
  canongInv : CanongInv ctx st.canong st.canonlab st.samerows
  stab : ∀ γ ∈ st.genTrace,
    CellStab st.ptn (cs.length + 1) st.lab γ
  genTraceOk : GenTraceOk ctx st (ColorMap G)
  autosOk : AutosOk ctx.g rptn rlab 1 st.autos

/-! # The ledgers ride the internal steps

`processnode` is the only primitive that writes either store, so the
two ledger clauses of `DomOk` cross every other event by frame. These
are the transport forms the induction applies at the unwind and the
comparison step. -/

/-- Store validity crosses a frame-preserving step. -/
theorem genTraceOk_of_eq {ctx : Ctx n} {st st' : Search n}
    {P : Array Nat → Prop}
    (h : st'.genTrace = st.genTrace) (hok : GenTraceOk ctx st P) :
    GenTraceOk ctx st' P := by
  intro γ hγ
  exact hok γ (by rwa [h] at hγ)

/-- The `(fix, mcr)` ledger crosses a frame-preserving step. -/
theorem autosOk_of_eq {g : Array (VSet n)} {rptn rlab : Array Nat}
    {st st' : Search n} (h : st'.autos = st.autos)
    (hok : AutosOk g rptn rlab 1 st.autos) :
    AutosOk g rptn rlab 1 st'.autos := by
  rw [h]; exact hok

/-! # The row equalities the leaf event needs

`processnode_checkAutom` and `genTraceOk_processnode` each leave a row
equality for the induction to supply. The row-tie one is local: a
`testcanlab` tie against the updated store is exactly equality of the
two leaf-row lists, by the store invariant the node already carries.
The first-path one is the cheapautom descent, proved at the use site
from the run's `gcaFirst`/`firsttc` bookkeeping. -/


theorem rows_eq_of_testcanlab_tie {ctx : Ctx n} {st : Search n}
    (hinv : CanongInv ctx st.canong st.canonlab st.samerows)
    (h : (testcanlab ctx
        (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1
        = 0) :
    leafRows ctx st.canonlab = leafRows ctx st.lab := by
  rw [testcanlab_fst, rows_of_canongInv (updatecan_inv hinv)] at h
  have hc : listCmp VSet.rowCmp (leafRows ctx st.lab)
      (leafRows ctx st.canonlab) = .eq := by
    rcases hcc : listCmp VSet.rowCmp (leafRows ctx st.lab)
        (leafRows ctx st.canonlab) with _ | _ | _
    · rw [hcc] at h; exact absurd h (by decide)
    · rfl
    · rw [hcc] at h; exact absurd h (by decide)
  exact ((listCmp_eq_iff (fun _ _ => VSet.rowCmp_eq_iff) _ _).mp hc).symm

/-! # Labelling facts of a reached state

The row equalities and the scatter exits are stated over `LabOk` and
`LabInj`. A reached labelling supplies both, so the induction never
carries them separately from `SearchOk`. -/

/-- A reached labelling lands in the vertex range. -/
theorem labOk_of_reach {G : Colored n k} {lab : Array Nat}
    (hsz : lab.size = n) (h : CellsReach G lab) : LabOk lab n := by
  intro i hi
  exact cellsReach_lt h i (by omega)

/-- A reached labelling is injective: it is a permutation of the
vertex range, hence duplicate-free. -/
theorem labInj_of_reach {G : Colored n k} {lab : Array Nat}
    (hsz : lab.size = n) (hn0 : 0 < n) (h : CellsReach G lab) :
    LabInj lab n := by
  have hp := isPerm_of_cellsReach hsz hn0 h
  have hnd : lab.toList.Nodup := hp.nodup_iff.mpr List.nodup_range
  intro i j hi hj he
  have hi' : i < lab.toList.length := by simp [hsz]; omega
  have hj' : j < lab.toList.length := by simp [hsz]; omega
  rw [getElem!_pos lab i (by omega), getElem!_pos lab j (by omega)]
    at he
  have hg : lab.toList[i] = lab.toList[j] := by simpa using he
  exact (List.Nodup.getElem_inj hnd).mp hg

/-! # The admission event under the node invariant

The remaining row equality packaged with the labelling facts of a
reached state: at a node carrying `DomOk`, `processnode` preserves
store validity outright. The two `reached` hypotheses are what the
induction knows from having passed `firstterminal`, where both the
first leaf and the incumbent are installed from a reached
labelling. -/

/-! # Absorption of dominated sibling suffixes

An early unwind leaves the remaining siblings of every loop strictly
between the return level and the leaf unvisited. Suppose the leaf
event left the comparison machine frozen downward. The recorded
divergence sits at level `eqlevCanon + 1`, and the `pruneLevel`
forms that fire in that mode (`eqlevCanon` itself, or
`allsamelevel - 1` above it) never return below the divergence. The
path prefix of every skipped loop therefore still contains the
divergence, so the whole subtree of every skipped sibling compares
below the incumbent, and the key maximum absorbs the suffix locally,
loop by loop. -/

private theorem getElem!_take'' {l : List Nat} {m i : Nat}
    (him : i < m) (hil : i < l.length) : (l.take m)[i]! = l[i]! := by
  have hti : i < (l.take m).length := by
    rw [List.length_take]
    omega
  rw [getElem!_pos (l.take m) i hti, getElem!_pos l i hil,
    List.getElem_take]

/-- The frozen divergence survives truncation: with the divergence
recorded at level `eqlevCanon + 1`, the path prefix down to any level
at or beyond it still compares below the incumbent, whatever comes
after. -/
theorem codeInv_take_listCmp_lt {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon (-1))
    {M : Nat} (hM : eqlevCanon.toNat < M) (hMcs : M ≤ cs.length)
    (ext : List Nat) :
    listCmp compare (cs.take M ++ ext) (bs ++ [codeSentinel]) =
      .lt := by
  rcases hinv.tri with ⟨hcc, -⟩ | ⟨j, hj1, hjL, hjm, hec, hpre, hcase⟩
  · cases hcc
  rcases hcase with ⟨-, hlt⟩ | ⟨hcc, -⟩
  case inr => cases hcc
  have hjM : j ≤ M := by
    rw [hec] at hM
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast] at hM
    omega
  refine listCmp_lt_of_prefix (j - 1) _ _
    (by rw [List.length_append, List.length_take]; omega)
    (by rw [List.length_append]; simp; omega)
    (fun i hi => ?_) ?_
  · rw [getElem!_append_left
        (as := cs.take M) (by rw [List.length_take]; omega),
      getElem!_append_sentinel (by omega),
      getElem!_take'' (by omega) (by omega)]
    have hp := hpre (i + 1) (by omega) (by omega)
    simpa using hp
  · rw [getElem!_append_left
        (as := cs.take M) (by rw [List.length_take]; omega),
      getElem!_append_sentinel (by omega),
      getElem!_take'' (by omega) (by omega),
      (by omega : j - 1 + 1 = j)]
    exact hlt

/-- The key-level truncated verdict: every subtree hanging below the
truncated path is dominated once the machine froze downward at or
above the truncation level. -/
theorem frozen_take_keyCmp_lt {nn : Nat} {cs bs : List Nat}
    {ctx : Ctx n} {canoncode : Array Nat} {canonlevel : Nat}
    {eqlevCanon : Int} {canonlab : Array Nat}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon (-1))
    {M : Nat} (hM : eqlevCanon.toNat < M) (hMcs : M ≤ cs.length)
    (K : Key n) :
    keyCmp (prefixKey (cs.take M) K) (incKey ctx bs canonlab) =
      .lt := by
  rw [prefixKey, incKey, keyCmp]
  show (match listCmp compare (cs.take M ++ K.codes)
      (bs ++ [codeSentinel]) with
    | .eq => listCmp VSet.rowCmp K.rows (leafRows ctx canonlab)
    | .lt => .lt
    | .gt => .gt) = .lt
  rw [codeInv_take_listCmp_lt hinv hM hMcs K.codes]

/-- `frozen_take_keyCmp_lt` in the `keyLe` form the absorption
consumes. -/
theorem frozen_take_keyLe {nn : Nat} {cs bs : List Nat}
    {ctx : Ctx n} {canoncode : Array Nat} {canonlevel : Nat}
    {eqlevCanon : Int} {canonlab : Array Nat}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon (-1))
    {M : Nat} (hM : eqlevCanon.toNat < M) (hMcs : M ≤ cs.length)
    (K : Key n) :
    keyLe (prefixKey (cs.take M) K) (incKey ctx bs canonlab) := by
  show keyCmp _ _ ≠ .gt
  rw [frozen_take_keyCmp_lt hinv hM hMcs K]
  intro h
  cases h

/-- The whole-path instance: with the machine frozen downward, every
subtree below the current path is dominated. -/
theorem frozen_keyLe {nn : Nat} {cs bs : List Nat} {ctx : Ctx n}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    {canonlab : Array Nat}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon (-1))
    (K : Key n) :
    keyLe (prefixKey cs K) (incKey ctx bs canonlab) := by
  have hM : eqlevCanon.toNat < cs.length := by
    rcases hinv.tri with ⟨hcc, -⟩ |
      ⟨j, hj1, hjL, hjm, hec, hpre, hcase⟩
    · cases hcc
    rw [hec]
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
    omega
  have h := frozen_take_keyLe (ctx := ctx) (canonlab := canonlab)
    hinv hM (Nat.le_refl cs.length) K
  rwa [List.take_length] at h

/-! # One child against its node's subtree key -/

/-! # The generator-return transport

At the loop where a generator return lands (`gcaFirst` for a code-1
admission, `gcaCanon` for a code-2 admission), the whole partially
explored child subtree is absorbed at once: the admitted scatter is a
checked automorphism that stabilizes the loop's cells and carries the
guiding sibling's individualized vertex onto the current child's, so
the two children's subtree keys are equal, and the guiding sibling's
key is already folded into the incumbent. The intermediate loops
below need no local justification in this mode. The return level being
the gca is exactly what lets their whole enclosing child subtree be
absorbed here. -/

/-- A checked automorphism stabilizing the refined node's cells and
carrying one target-cell vertex onto another identifies the two
children's subtree keys. -/
theorem childKey_of_carried {ctx : Ctx n}
    (hgsz : ctx.g.size = n) {γ : Array Nat}
    (hAut : checkAutom ctx.g γ = true)
    (tcLevel fuel level : Nat) {rsLab rsPtn : Array Nat}
    {tc lenT numcells o o' : Nat}
    (hstab : CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc lenT) (hrange : tc + lenT ≤ n)
    (ho : o < lenT) (ho' : o' < lenT)
    (hlf : level + 1 + fuel ≤ n + 1)
    (hcarry : γ[rsLab[tc + o']!]! = rsLab[tc + o]!) :
    childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o =
      childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o' := by
  rcases Decidable.em (o = o') with rfl | hne
  · rfl
  obtain ⟨σ, hσeq, hσrows⟩ := checkAutom_sound hgsz hAut
  have hvO : rsLab[tc + o]! < n := hok _ (by omega)
  have hvO' : rsLab[tc + o']! < n := hok _ (by omega)
  have hσv : σ.toFun rsLab[tc + o']! = rsLab[tc + o]! := by
    rw [hσeq _ hvO']
    exact hcarry
  obtain ⟨L, rfl⟩ : ∃ L, lenT = L + 1 := ⟨lenT - 1, by omega⟩
  have hbsz : (breakout n rsLab rsPtn (level + 1) tc
      rsLab[tc + o']!).1.size = n := by
    show (breakout.go rsLab[tc + o']! (rsLab.size + 1) rsLab tc
      rsLab[tc + o']!).size = n
    rw [breakout_go_size, hs]
  have hsegO : segN (breakout n rsLab rsPtn (level + 1) tc
      rsLab[tc + o]!).1 tc (L + 1) =
      rsLab[tc + o]! ::
        (segN rsLab tc (L + 1)).erase rsLab[tc + o]! := by
    show segN (breakout.go rsLab[tc + o]! (rsLab.size + 1) rsLab tc
      rsLab[tc + o]!) tc (L + 1) = _
    exact breakout_go_seg (rsLab.size + 1) (L + 1) rsLab tc
      rsLab[tc + o]! ⟨tc + o, by omega, by omega, by omega, rfl⟩
      (by omega) (by omega)
  have hsegO' : segN (breakout n rsLab rsPtn (level + 1) tc
      rsLab[tc + o']!).1 tc (L + 1) =
      rsLab[tc + o']! ::
        (segN rsLab tc (L + 1)).erase rsLab[tc + o']! := by
    show segN (breakout.go rsLab[tc + o']! (rsLab.size + 1) rsLab tc
      rsLab[tc + o']!) tc (L + 1) = _
    exact breakout_go_seg (rsLab.size + 1) (L + 1) rsLab tc
      rsLab[tc + o']! ⟨tc + o', by omega, by omega, by omega, rfl⟩
      (by omega) (by omega)
  rw [segN_cons] at hsegO
  rw [segN_cons] at hsegO'
  injection hsegO with hheadO htailO
  injection hsegO' with hheadO' htailO'
  have hstabSeg : ∀ (a l : Nat), IsCell rsPtn level a l → a + l ≤ n →
      (segN rsLab a l).Perm ((segN rsLab a l).map σ.toFun) := by
    intro a l hicl hbnd
    have h := hstab a l hicl
    rw [segN_map_of_le _ _ _ _ (by omega)] at h
    have hcg : (segN rsLab a l).map (fun w => γ[w]!) =
        (segN rsLab a l).map σ.toFun := by
      refine List.map_congr_left fun x hx => ?_
      rw [segN] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hilt := List.mem_range.mp hi
      exact (hσeq _ (hok _ (by omega))).symm
    rw [hcg] at h
    exact h
  have hicS : IsCell rsPtn (level + 1) tc (L + 1) :=
    isCell_succ hvals (by omega) hic
  have hend' : rsPtn[n - 1]! ≤ level := by
    have h := hend
    rwa [hsp] at h
  have hcp : cellsPerm (rsPtn.set! tc (level + 1)) (level + 1)
      (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1
      ((breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1.map
        σ.toFun) := by
    refine cellsPerm_set! hicS (by omega) (Nat.le_refl tc)
      (by omega) ?_ ?_ ?_
    · rw [show tc + 1 - tc = 1 by omega, segN_cons, segN_zero,
        segN_cons, segN_zero, hheadO,
        getElem!_map_of_lt σ.toFun _ (by rw [hbsz]; omega), hheadO',
        hσv]
    · rw [show tc + (L + 1) - (tc + 1) = L by omega, htailO,
        segN_map_of_le _ _ _ _ (by rw [hbsz]; omega), htailO']
      have hCstab := hstabSeg tc (L + 1) hic hrange
      have hvoC : rsLab[tc + o]! ∈ segN rsLab tc (L + 1) := by
        rw [segN]
        exact List.mem_map.mpr ⟨o, List.mem_range.mpr ho, rfl⟩
      have hvo'C : rsLab[tc + o']! ∈ segN rsLab tc (L + 1) := by
        rw [segN]
        exact List.mem_map.mpr ⟨o', List.mem_range.mpr ho', rfl⟩
      have h5 : ((segN rsLab tc (L + 1)).map σ.toFun).Perm
          (rsLab[tc + o]! ::
            ((segN rsLab tc (L + 1)).erase rsLab[tc + o']!).map
              σ.toFun) := by
        have h := (List.perm_cons_erase hvo'C).map σ.toFun
        rw [List.map_cons, hσv] at h
        exact h
      exact ((List.perm_cons_erase hvoC).symm.trans
        (hCstab.trans h5)).cons_inv
    · intro a l hicA hdisj
      have hlabOeq : segN (breakout n rsLab rsPtn (level + 1) tc
          rsLab[tc + o]!).1 a l = segN rsLab a l := by
        refine segN_congr fun q hq => ?_
        show (breakout.go rsLab[tc + o]! (rsLab.size + 1) rsLab tc
          rsLab[tc + o]!)[a + q]! = rsLab[a + q]!
        rcases hdisj with hd | hd
        · exact breakout_go_outside _ _ _ _ _ (by omega)
        · exact breakout_go_outside_right _ (L + 1) _ _ _
            ⟨tc + o, by omega, by omega, by omega, rfl⟩ _ (by omega)
      have hlabO'eq : segN (breakout n rsLab rsPtn (level + 1) tc
          rsLab[tc + o']!).1 a l = segN rsLab a l := by
        refine segN_congr fun q hq => ?_
        show (breakout.go rsLab[tc + o']! (rsLab.size + 1) rsLab tc
          rsLab[tc + o']!)[a + q]! = rsLab[a + q]!
        rcases hdisj with hd | hd
        · exact breakout_go_outside _ _ _ _ _ (by omega)
        · exact breakout_go_outside_right _ (L + 1) _ _ _
            ⟨tc + o', by omega, by omega, by omega, rfl⟩ _ (by omega)
      rcases Nat.lt_or_ge a n with han | han
      · have hbnd : a + l ≤ n := by
          rcases Nat.lt_or_ge (a + l) (n + 1) with h1 | h1
          · omega
          · exfalso
            have hi := hicA.2.2.1 (n - 1) (by omega) (by omega)
            omega
        have hicL : IsCell rsPtn level a l :=
          isCell_pred hvals (by omega) hicA
        rw [hlabOeq,
          segN_map_of_le _ _ _ _ (by rw [hbsz]; exact hbnd),
          hlabO'eq]
        exact hstabSeg a l hicL hbnd
      · have hl1 : l = 1 := by
          rcases Nat.lt_or_ge l 2 with h2 | h2
          · have := hicA.1
            omega
          · exfalso
            have hi := hicA.2.2.1 a (Nat.le_refl a) (by omega)
            rw [getElem!_neg _ _ (by omega)] at hi
            have hd : (default : Nat) = 0 := rfl
            omega
        subst hl1
        rw [hlabOeq, segN_cons, segN_zero, segN_cons, segN_zero,
          getElem!_neg rsLab a (by omega),
          getElem!_neg ((breakout n rsLab rsPtn (level + 1) tc
              rsLab[tc + o']!).1.map σ.toFun) a
            (by rw [Array.size_map, hbsz]; omega)]
  have hokc := childNodeOk hs hok hsp hend hvals hic hrange ho
  have hokc' := childNodeOk hs hok hsp hend hvals hic hrange ho'
  exact (specNode_autom hσrows tcLevel fuel (level + 1)
    (lab₁ := (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1)
    (lab₂ := (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1)
    (ptn := (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o']!).2.1)
    (active := (breakout n rsLab rsPtn (level + 1) tc
      rsLab[tc + o']!).2.2)
    (numcells := numcells + 1) hcp hokc.labSize hokc'.labSize
    hokc.labOk hokc'.labOk hokc'.ptnSize hokc'.ptnEnd
    hokc'.starts hokc'.vals (by omega)).symm

end Hex.GraphIso.Nauty

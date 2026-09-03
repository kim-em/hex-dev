/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CodeFaithful
public import HexGraphIso.Nauty.LeafFaithful
public import HexGraphIso.Nauty.SearchModel
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

end Hex.GraphIso.Nauty

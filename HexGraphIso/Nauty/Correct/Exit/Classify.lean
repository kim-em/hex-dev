/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Exit.Final
import all HexGraphIso.Nauty.Search.Search

public section

/-!
Comparison-prune producers and the classification of why a node
returned early.

Local exactness and the reason for an early return are separate: a
comparison-frozen or cheap-cell child may be exact at its own node while
still causing its parent loop to skip a suffix.

This module builds on `Correct.Exit.Final`.  `Correct.Sweep.Base` and
`Correct.Sweep.Carry` carry `NodeRun`, `LoopRun`, and the exit types
defined here through the sibling-sweep induction.
-/

/-! Comparison-prune producers for the search outcomes. -/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Below a saved cheap-cell boundary, the current refined node remains in
the small-cell subtree generated at that boundary.  At the boundary itself
the implication is dormant until the executable guard either validates the
shape or parks the boundary at the child. -/
@[expose] def CheapDesc (ctx : Ctx n) (level boundary : Nat)
    (st : RefineSt n) : Prop :=
  boundary < level → SubtreeOk ctx level st

namespace CheapDesc

/-- A boundary created at the current node imposes no condition on its
strict descendants yet. -/
theorem same (ctx : Ctx n) (level : Nat) (st : RefineSt n) :
    CheapDesc ctx level level st := by
  intro h
  omega

/-- At an entered sibling sweep, a saved boundary at or above the current
node supplies the small-cell subtree fact.  A strictly shallower boundary
uses the inherited descent invariant.  Equality is exactly the case in
which the current cheap-cell guard must have succeeded. -/
theorem atLevel {ctx : Ctx n} {level boundary : Nat} {st : RefineSt n}
    (h : CheapDesc ctx level boundary st)
    (hit : IterOk ctx level st) (heq : Equitable ctx level st.lab st.ptn)
    (hcount : bcount st.ptn level n = st.numcells)
    (hle : boundary ≤ level)
    (hguard : boundary = level → cheapautom st.ptn level n = true) :
    SubtreeOk ctx level st := by
  rcases Nat.lt_or_eq_of_le hle with hlt | heqBoundary
  · exact h hlt
  · exact subtreeOk_of_cheapautom hit heq hcount
      (hguard heqBoundary)

/-- The executable cheap-cell boundary update carries the small-cell
subtree invariant into every individualized child. -/
theorem child {ctx : Ctx n} {level boundary tc len o : Nat}
    {st : RefineSt n}
    (h : CheapDesc ctx level boundary st)
    (hit : IterOk ctx level st) (heq : Equitable ctx level st.lab st.ptn)
    (hcount : bcount st.ptn level n = st.numcells)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hlvl : level < n)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len) :
    let boundary' := if boundary ≥ level ∧
        ¬cheapautom st.ptn level n then level + 1 else boundary
    CheapDesc ctx (level + 1) boundary'
      (childSt ctx level st tc st.lab[tc + o]!) := by
  dsimp only
  let boundary' := if boundary ≥ level ∧
      ¬cheapautom st.ptn level n then level + 1 else boundary
  intro hbelow
  have hparent : SubtreeOk ctx level st := by
    rcases Nat.lt_or_ge boundary level with hold | hge
    · exact h hold
    · have hcheap : cheapautom st.ptn level n = true := by
        rcases hc : cheapautom st.ptn level n with _ | _
        · have hguard : boundary ≥ level ∧
              ¬cheapautom st.ptn level n := ⟨hge, by simp [hc]⟩
          change (if boundary ≥ level ∧
            ¬cheapautom st.ptn level n then level + 1 else boundary) <
              level + 1 at hbelow
          rw [ite_eq_left hguard] at hbelow
          exfalso
          omega
        · rfl
      exact subtreeOk_of_cheapautom hit heq hcount hcheap
  exact subtreeOk_child hparent hlvl hsymm
    (mem_cells_of_isCell (by rw [hit.ok.ptnSize]; exact Nat.le_refl _)
      hit.ok.ptnEnd hcell (by omega)
      (by rw [hit.ok.ptnSize]; exact hrange))
    (by omega) (by omega)

end CheapDesc

namespace FrozenOut

/-- Expose a shorter ancestor prefix while retaining the same frozen
comparison.  This is the transport used as an early return crosses nested
node and loop frames. -/
theorem shrink {ctx : Ctx n} {stem ancestor : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int}
    (h : FrozenOut ctx stem out best r)
    (hprefix : stem.take ancestor.length = ancestor) :
    FrozenOut ctx ancestor out best r := by
  rcases h with
    ⟨current, codes, bestCodes, hcode, hdepth, hstem, hinstalled, hbest,
      hfloor⟩
  apply FrozenOut.mk current codes bestCodes hcode hdepth
  · have hlen := congrArg List.length hprefix
    simp only [List.length_take] at hlen
    have hle : ancestor.length ≤ stem.length := by omega
    calc
      codes.take ancestor.length =
          (codes.take stem.length).take ancestor.length := by
            rw [List.take_take, Nat.min_eq_left hle]
      _ = ancestor := by rw [hstem, hprefix]
  · exact hinstalled
  · exact hbest
  · exact hfloor

/-- Fixed-point cleanup changes none of a frozen comparison's fields. -/
theorem setFixed {ctx : Ctx n} {stem : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int} (h : FrozenOut ctx stem out best r)
    (fixedpts : VSet n) :
    FrozenOut ctx stem { out with fixedpts := fixedpts } best r := by
  rcases h with
    ⟨current, codes, bestCodes, hcode, hdepth, hstem, hinstalled, hbest,
      hfloor⟩
  exact .mk current codes bestCodes hcode hdepth hstem hinstalled hbest
    hfloor

/-- Resetting first-path return controls changes none of a frozen
comparison's fields. -/
theorem setFirst {ctx : Ctx n} {stem : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int} (h : FrozenOut ctx stem out best r)
    (gcaFirst stabvertex : Nat) :
    FrozenOut ctx stem
      { out with gcaFirst := gcaFirst, stabvertex := stabvertex } best r := by
  rcases h with
    ⟨current, codes, bestCodes, hcode, hdepth, hstem, hinstalled, hbest,
      hfloor⟩
  exact .mk current codes bestCodes hcode hdepth hstem hinstalled hbest
    hfloor

end FrozenOut

namespace RunPrep

/-- A negative comparison branch whose prune tail stays below the recorded
divergence produces a frozen-code witness without changing the incumbent. -/
theorem frozen {G : Colored n k} {ctx : Ctx n}
    {tcLevel current numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
   
    (h : RunPrep G ctx tcLevel current codes bs fs numcells st best trail)
    (hpath : current = codes.length)
    (hstem : codes.take stem.length = stem)
    (hfirst : st.eqlevFirst ≠ current) (hneg : st.compCanon < 0)
    (hfloor : Int.ofNat st.eqlevCanon.toNat ≤
      pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon) :
    FrozenOut ctx stem (processnode ctx current numcells st).2 best
      (processnode ctx current numcells st).1 := by
  have hcc : st.compCanon = -1 := by
    rcases h.codeInv.tri with hzero |
      ⟨_, _, _, _, _, _, hdown | hup⟩
    · omega
    · exact hdown.1
    · omega
  have hinv := h.codeInv
  rw [hcc] at hinv
  obtain ⟨hr, _, heq, hcode, hcanonlevel, hcanonlab, _, _⟩ :=
    processnode_fast (ctx := ctx) (level := current)
      (numcells := numcells) (st := st) ⟨hfirst, hneg⟩
  apply FrozenOut.mk current codes bs
  · rw [hcode, hcanonlevel, heq]
    exact hinv
  · exact hpath
  · exact hstem
  · exact h.bestCodes
  · rw [hcanonlab]
    exact h.incumbent
  · rw [heq, hr]
    exact hfloor

/-- Every negative off-path leaf prune is either comparison-frozen or a
jump to the saved cheap-cell boundary. -/
theorem pruneMode {G : Colored n k} {ctx : Ctx n}
    {tcLevel current numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
   
    (h : RunPrep G ctx tcLevel current codes bs fs numcells st best trail)
    (hpath : current = codes.length)
    (hstem : codes.take stem.length = stem)
    (hfirst : st.eqlevFirst ≠ current) (hneg : st.compCanon < 0) :
    FrozenOut ctx stem (processnode ctx current numcells st).2 best
        (processnode ctx current numcells st).1 ∨
      (processnode ctx current numcells st).1 =
        Int.ofNat st.noncheaplevel - 1 := by
  have hr := (processnode_fast (ctx := ctx) (level := current)
    (numcells := numcells) (st := st) ⟨hfirst, hneg⟩).1
  rcases pruneReturn_split h.codeInv.eqlev_nonneg with hfloor | hjump
  · exact Or.inl (h.frozen hpath hstem hfirst hneg hfloor)
  · exact Or.inr (hr.trans hjump)

end RunPrep

end Hex.GraphIso.Nauty

/-!
Return classifications for the mutual search induction.

Local exactness and the reason for an early return are separate.  A
comparison-frozen or cheap-cell child may be exact at its own node while
still causing its parent loop to skip a suffix.  The extra payload is what
justifies that skipped suffix.
-/

namespace Hex.GraphIso.Nauty

/-- Two states describe the same recovered search frame at `level` when
their partitions agree and their current labellings differ only within
that partition's cells. -/
structure FrameRel (level : Nat) (st out : SearchSt n) : Prop where
  ptn : out.ptn = st.ptn
  lab : cellsPerm st.ptn level st.lab out.lab

namespace FrameRel

theorem refl (level : Nat) (st : SearchSt n) : FrameRel level st st :=
  ⟨rfl, cellsPerm_refl _ _ _⟩

theorem symm {level : Nat} {st out : SearchSt n}
    (h : FrameRel level st out) : FrameRel level out st := by
  constructor
  · exact h.ptn.symm
  · rw [h.ptn]
    exact cellsPerm_symm h.lab

theorem trans {level : Nat} {a b c : SearchSt n}
    (hab : FrameRel level a b) (hbc : FrameRel level b c) :
    FrameRel level a c := by
  constructor
  · exact hbc.ptn.trans hab.ptn
  · have hbcLab := hbc.lab
    rw [hab.ptn] at hbcLab
    exact cellsPerm_trans hab.lab hbcLab

/-- A recovered `SearchOut` between valid endpoints is exactly a frame
relation. -/
theorem ofSearchOut {G : Colored n k} {level numcells : Nat}
    {st out : SearchSt n} (h : SearchOut G level level st out)
    (hst : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out) : FrameRel level st out :=
  ⟨h.ptnEq hst hout, h.perm⟩

end FrameRel

/-- The guide-control facts preserved by every off-path search fragment.
The second canonical alternative records a newly installed descendant of
the fragment's entry frame. -/
structure GuideRel (level : Nat) (st out : SearchSt n) : Prop where
  first : out.gcaFirst = st.gcaFirst
  order : out.gcaFirst ≤ out.gcaCanon
  canon :
    (out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (level ≤ out.gcaCanon ∧ cellsPerm st.ptn level st.lab out.canonlab)

namespace GuideRel

theorem refl {level : Nat} {st : SearchSt n}
    (horder : st.gcaFirst ≤ st.gcaCanon) : GuideRel level st st :=
  ⟨rfl, horder, Or.inl ⟨rfl, rfl⟩⟩

/-- Guide relations compose across an equivalent recovered frame. -/
theorem trans {level : Nat} {a b c : SearchSt n}
    (hab : GuideRel level a b) (hbc : GuideRel level b c)
    (hframe : FrameRel level a b) : GuideRel level a c := by
  constructor
  · exact hbc.first.trans hab.first
  · exact hbc.order
  · rcases hbc.canon with hold | hnew
    · rw [hold.1, hold.2]
      exact hab.canon
    · right
      refine ⟨hnew.1, ?_⟩
      rw [hframe.ptn] at hnew
      exact cellsPerm_trans hframe.lab hnew.2

end GuideRel

/-- Result of one node call.  `done` is the ordinary one-level return.
`frozen` and `cheap` retain the distinct witnesses needed when the return
crosses more than one loop, and `unwind` carries a stored generator. -/
inductive NodeExit (ctx : Ctx n) (tcLevel specFuel runFuel level : Nat)
    (codes : List Nat) (st out : SearchSt n) (numcells : Nat)
    (best outBest : Option (Key n)) (trail : FrameTrail) (r : Int) : Prop where
  | done
      (returned : r = Int.ofNat level - 1)
      (exact : outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel level codes st numcells)))
  | unwind (target : Nat)
      (returned : r = Int.ofNat target) (below : target < level)
      (sound : NodeSound ctx tcLevel specFuel level codes st numcells
        best outBest)
      (payload : Unwind ctx tcLevel target out outBest)
      (located : payload.Located trail)
      (control : target = out.gcaFirst ∨ target = out.gcaCanon)
  | frozen
      (below : r < Int.ofNat level)
      (exact : outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel level codes st numcells)))
      (freeze : FrozenOut ctx codes out outBest r)
  | cheap (boundary : Nat)
      (returned : r = Int.ofNat boundary - 1)
      (positive : 1 ≤ boundary) (atOrAbove : boundary ≤ level)
      (saved : out.noncheaplevel = boundary)
      (exact : outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel level codes st numcells)))
  | exhausted
      (returned : r = 0) (state : out = st) (incumbent : outBest = best)
      (emptyFuel : runFuel = 0)

/-- Provenance of the newest workspace pair while the one-shot
`needshortprune` request is live.  Explicit code-two pairs are already
valid at their returned frame.  Implicit cheap-cell pairs retain root
validity and the deeper boundary needed to localize them when the return
reaches its receiving loop. -/
inductive ShortSource (G : Colored n k) (ctx : Ctx n) (out : SearchSt n)
    (trail : FrameTrail) (r : Int) : Prop where
  | explicit (target : Nat) (fix mcr : VSet n)
      (returned : r = Int.ofNat target)
      (back : out.autos.back? = some (fix, mcr))
      (valid : ∀ entry, trail target = some entry →
        PairOk ctx.g entry.frame.rsPtn entry.frame.rsLab target
          fix mcr)
  | implicit (target : Nat)
      (returned : r = Int.ofNat target)
      (below : target < out.noncheaplevel)
      (back : out.autos.back? = some
        (fmptn out.lab out.ptn out.noncheaplevel n))
      (root : PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1
        (fmptn out.lab out.ptn out.noncheaplevel n).1
        (fmptn out.lab out.ptn out.noncheaplevel n).2)

namespace ShortSource

/-- Fixed-point cleanup after a child return does not affect the stored
pair or its source evidence. -/
theorem setFixed {G : Colored n k} {ctx : Ctx n} {out : SearchSt n}
    {trail : FrameTrail} {r : Int}
    (h : ShortSource G ctx out trail r) (fixedpts : VSet n) :
    ShortSource G ctx { out with fixedpts := fixedpts } trail r := by
  cases h with
  | explicit target fix mcr returned back valid =>
      exact .explicit target fix mcr returned back valid
  | implicit target returned below back root =>
      exact .implicit target returned below back root

/-- The final first-path counter adjustment changes none of the fields
used by a live short-prune source. -/
theorem firstFinish {G : Colored n k} {ctx : Ctx n} {out : SearchSt n}
    {trail : FrameTrail} {r : Int} {level size index : Nat}
    (h : ShortSource G ctx out trail r) :
    ShortSource G ctx (Nauty.firstFinish level size index out) trail r := by
  rw [Nauty.firstFinish]
  split
  · cases h with
    | explicit target fix mcr returned back valid =>
        exact .explicit target fix mcr returned back valid
    | implicit target returned below back root =>
        exact .implicit target returned below back root
  · exact h

end ShortSource

namespace NodeExit

/-- Every result of a positive-level node lies strictly below that node's
level.  This is the one-step bound that lets a receiving loop identify an
explicit or implicit short-prune source with its own level. -/
theorem below {ctx : Ctx n} {tcLevel specFuel runFuel level numcells : Nat}
    {codes : List Nat} {st out : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : NodeExit ctx tcLevel specFuel runFuel level codes st out numcells
      best outBest trail r) (hlevel : 0 < level) :
    r < Int.ofNat level := by
  cases h with
  | done returned exact => rw [returned]; omega
  | unwind target returned below sound payload located control =>
      rw [returned]
      exact Int.ofNat_lt.mpr below
  | frozen below exact freeze => exact below
  | cheap boundary returned positive atOrAbove saved exact =>
      rw [returned]
      simp only [Int.ofNat_eq_natCast]
      omega
  | exhausted returned state incumbent emptyFuel =>
      rw [returned]
      exact Int.natCast_pos.mpr hlevel

/-- The final first-path counter adjustment preserves every node exit,
including the payload of a located unwind. -/
theorem firstFinish {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {codes : List Nat} {st out : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (hfuel : runFuel ≠ 0)
    (h : NodeExit ctx tcLevel specFuel runFuel level codes st out numcells
      best outBest trail r) :
    NodeExit ctx tcLevel specFuel runFuel level codes st
      (Nauty.firstFinish level size index out) numcells best outBest trail
      r := by
  cases h with
  | done returned exact => exact .done returned exact
  | unwind target returned below sound payload located control =>
      apply NodeExit.unwind target returned below sound payload.firstFinish
        located.firstFinish
      unfold Nauty.firstFinish
      split <;> exact control
  | frozen below exact freeze =>
      apply NodeExit.frozen below exact
      rw [Nauty.firstFinish]
      split
      · cases freeze with
        | mk current cs bs codeInv depth stemEq installed incumbent floor =>
            exact .mk current cs bs codeInv depth stemEq installed incumbent
              floor
      · exact freeze
  | cheap boundary returned positive atOrAbove saved exact =>
      apply NodeExit.cheap boundary returned positive atOrAbove
      · unfold Nauty.firstFinish
        split <;> exact saved
      · exact exact
  | exhausted returned state incumbent emptyFuel =>
      exact (hfuel emptyFuel).elim

end NodeExit

/-- Result of a sibling loop.  Early comparison and cheap-cell exits carry
both the exact loop maximum and the payload required to cross an older
frame.  Cursor-fuel exhaustion remains explicit and cannot be confused
with completion. -/
inductive LoopExit (ctx : Ctx n) (tcLevel specFuel runFuel loopFuel level : Nat)
    (codes : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n)) (trail : FrameTrail)
    (r : Option Int) : Prop where
  | done
      (returned : r = none)
      (exact : outBest = some (incMax best bound))
  | unwind (target : Nat)
      (returned : r = some (Int.ofNat target)) (below : target < level)
      (sound : LoopSound ctx bound best outBest)
      (payload : Unwind ctx tcLevel target out outBest)
      (located : payload.Located trail)
      (control : target = out.gcaFirst ∨ target = out.gcaCanon)
  | frozen (value : Int)
      (returned : r = some value)
      (below : value < Int.ofNat level)
      (exact : outBest = some (incMax best bound))
      (freeze : FrozenOut ctx codes out outBest value)
  | cheap (boundary : Nat)
      (returned : r = some (Int.ofNat boundary - 1))
      (positive : 1 ≤ boundary) (below : boundary ≤ level)
      (saved : out.noncheaplevel = boundary)
      (exact : outBest = some (incMax best bound))
  | exhausted
      (returned : r = none) (finalCursor : Option Nat)
      (progress : cursorRank cursor + loopFuel ≤ cursorRank finalCursor)
      (bounded : ∀ v, finalCursor = some v → v < n)

/-- Concrete node result paired with its return classification.
The event and trail clauses are independent of the semantic maximum and
remain reusable from the established leaf machinery. -/
structure NodeRun (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel level : Nat) (codes fs : List Nat)
    (st out : SearchSt n) (numcells : Nat) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  exit : NodeExit ctx tcLevel specFuel runFuel level codes st out numcells
    best outBest receiptTrail r
  event : EventOut G ctx tcLevel codes fs out outBest eventTrail r
  preserved : TrailExt level receiptTrail eventTrail
  fixed : out.fixedpts = st.fixedpts
  short : out.needshortprune = true →
    ShortSource G ctx out eventTrail r

/-- Off-path nodes additionally preserve the first-path control and coset
cursor needed by their enclosing sibling loop. -/
structure OtherRun (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel level : Nat) (codes fs : List Nat)
    (st out : SearchSt n) (numcells : Nat) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  node : NodeRun G ctx tcLevel specFuel runFuel level codes fs st out
    numcells best outBest receiptTrail eventTrail r
  firstGuide : out.gcaFirst = st.gcaFirst
  order : out.gcaFirst ≤ out.gcaCanon
  canonGuide :
    (out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (level ≤ out.gcaCanon ∧ cellsPerm st.ptn level st.lab out.canonlab)
  coset : out.cosetindex = st.cosetindex

/-- A sibling-loop proof paired with its exit reason.  The established
proof retains coverage, event, and recovery facts.  `exit` separately
records why an unfinished suffix is nevertheless absorbed. -/
structure LoopRun (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  proof : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
    fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail eventTrail r
  exit : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
    rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail r
  short : out.needshortprune = true → ∃ value,
    r = some value ∧ ShortSource G ctx out eventTrail value

/-- An off-path sibling sweep additionally retains its coset cursor. -/
structure OtherLoopRun (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  proof : OtherLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
    codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
    outBest receiptTrail eventTrail r
  exit : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
    rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail r
  short : out.needshortprune = true → ∃ value,
    r = some value ∧ ShortSource G ctx out eventTrail value

/-- The first-path sibling sweep retains both reference histories in its
established proof, together with the reason for abandoning any suffix. -/
structure FirstLoopRun (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  proof : FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
    codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
    outBest receiptTrail eventTrail r
  exit : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
    rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail r
  short : out.needshortprune = true → ∃ value,
    r = some value ∧ ShortSource G ctx out eventTrail value

namespace NodeRun

/-- A node run can be viewed through the local outcome interface.  The
conversion holds at a single node, where both early exit variants already
carry exactness.  It says nothing about the enclosing loop: an early exit
is not coverage of the later siblings. -/
theorem toOutcome {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : NodeRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeOutcome G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r := by
  have hreceipt : NodeReceipt receiptTrail ctx tcLevel specFuel runFuel
      level codes st out numcells best outBest r := by
    cases h.exit with
    | done returned exact =>
        apply NodeReceipt.complete (NodeSound.ofExact exact) returned
        · exact canonlevel_ne_zero_of_stInc (h.event.read.trans exact)
        · exact h.event.read
        · exact exact
    | unwind target returned below sound payload located control =>
        exact NodeReceipt.unwind sound target returned below payload located
    | frozen below exact freeze =>
        apply NodeReceipt.pruned (NodeSound.ofExact exact) r rfl below
        · exact canonlevel_ne_zero_of_stInc (h.event.read.trans exact)
        · exact h.event.read
        · exact exact
    | cheap boundary returned positive atOrAbove saved exact =>
        apply NodeReceipt.pruned (NodeSound.ofExact exact) r rfl
        · rw [returned]
          simp only [Int.ofNat_eq_natCast]
          omega
        · exact canonlevel_ne_zero_of_stInc (h.event.read.trans exact)
        · exact h.event.read
        · exact exact
    | exhausted returned state incumbent emptyFuel =>
        exact NodeReceipt.exhausted emptyFuel returned state incumbent
  exact ⟨hreceipt, h.event, h.preserved⟩

/-- Restore the established result interface used by the invariant
transport lemmas after the exit has been classified. -/
theorem toProof {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : NodeRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeProof G ctx tcLevel specFuel runFuel level codes fs st out numcells
      best outBest receiptTrail eventTrail r :=
  ⟨h.toOutcome, h.fixed⟩

end NodeRun

namespace OtherRun

/-- Forget the semantic receipt and expose the off-path guide relation. -/
theorem guide {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : OtherRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r) :
    GuideRel level st out :=
  ⟨h.firstGuide, h.order, h.canonGuide⟩

/-- Restore the established off-path interface for ordinary parent-level
consumption and recovery. -/
theorem toProof {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : OtherRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r) :
    OtherProof G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r :=
  ⟨⟨h.node.toOutcome, h.firstGuide, h.order, h.canonGuide⟩,
    h.node.fixed, h.coset⟩

end OtherRun

namespace LoopExit

/-- Changing only the mutable live set leaves an already classified loop
exit unchanged. -/
theorem reindexSet {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tc len numcells : Nat}
    {tcell tcell' : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail} {r : Option Int}
    (h : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
      rsPtn tc len numcells tcell cursor bound st out best outBest trail r) :
    LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab rsPtn
      tc len numcells tcell' cursor bound st out best outBest trail r := by
  cases h with
  | done returned exact => exact .done returned exact
  | unwind target returned below sound payload located control =>
      exact .unwind target returned below sound payload located control
  | frozen value returned below exact freeze =>
      exact .frozen value returned below exact freeze
  | cheap boundary returned positive below saved exact =>
      exact .cheap boundary returned positive below saved exact
  | exhausted returned finalCursor progress bounded =>
      exact .exhausted returned finalCursor progress bounded

/-- One processed cursor step increases both the loop fuel and its
starting-rank budget. -/
theorem step {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tv tc len numcells : Nat} {tcell : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
      rsPtn tc len numcells tcell (some tv) bound st out best outBest trail
      r) :
    LoopExit ctx tcLevel specFuel runFuel (loopFuel + 1) level codes rsLab
      rsPtn tc len numcells tcell cursor bound st out best outBest trail r := by
  cases h with
  | done returned exact => exact .done returned exact
  | unwind target returned below sound payload located control =>
      exact .unwind target returned below sound payload located control
  | frozen value returned below exact freeze =>
      exact .frozen value returned below exact freeze
  | cheap boundary returned positive below saved exact =>
      exact .cheap boundary returned positive below saved exact
  | exhausted returned finalCursor progress bounded =>
      apply LoopExit.exhausted returned finalCursor
      · have hrank := cursorRank_step ha
        omega
      · exact bounded

/-- A sound processed child changes only the incoming incumbent of the
classified recursive tail. -/
theorem prepend {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tc len numcells : Nat} {tcell : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound : Key n} {st recSt out : SearchSt n}
    {best mid outBest : Option (Key n)} {trail : FrameTrail} {r : Option Int}
    (hpre : LoopSound ctx bound best mid)
    (h : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
      rsPtn tc len numcells tcell cursor bound recSt out mid outBest trail
      r) :
    LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab rsPtn
      tc len numcells tcell cursor bound st out best outBest trail r := by
  cases h with
  | done returned exact =>
      exact .done returned
        ((hpre.trans (LoopSound.ofExact exact)).exact exact
          (keyLe_incMax_right mid bound))
  | unwind target returned below sound payload located control =>
      exact .unwind target returned below (hpre.trans sound) payload located
        control
  | frozen value returned below exact freeze =>
      exact .frozen value returned below
        ((hpre.trans (LoopSound.ofExact exact)).exact exact
          (keyLe_incMax_right mid bound)) freeze
  | cheap boundary returned positive below saved exact =>
      exact .cheap boundary returned positive below saved
        ((hpre.trans (LoopSound.ofExact exact)).exact exact
          (keyLe_incMax_right mid bound))
  | exhausted returned finalCursor progress bounded =>
      exact .exhausted returned finalCursor progress bounded

/-- At a small-cell node, exactness of the selected child is exactness of
the whole sibling sweep, so the saved-boundary return remains a cheap exit
after fixed-point cleanup. -/
theorem ofCheap {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level boundary tc len numcells : Nat} {tcell fixedpts : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound childKey : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)} {trail : FrameTrail}
    (hboundary : 1 ≤ boundary) (hbelow : boundary ≤ level)
    (hsaved : out.noncheaplevel = boundary)
    (hbound : bound = childKey)
    (hexact : outBest = some (incMax best childKey)) :
    LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab rsPtn
      tc len numcells tcell cursor bound st { out with fixedpts := fixedpts }
      best outBest trail (some (Int.ofNat boundary - 1)) := by
  apply LoopExit.cheap boundary rfl hboundary hbelow
  · simpa only using hsaved
  rwa [hbound]

/-- An early frozen child absorbs both the explored prefix and every live
suffix child, yielding the exact loop maximum while retaining the frozen
payload for the next enclosing frame. -/
theorem ofFrozen {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tail tc len numcells : Nat} {tcell fixedpts : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail} {value : Int}
    (hfreeze : FrozenOut ctx codes out outBest value)
    (hlevel : level = codes.length) (hbelow : value < Int.ofNat level)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells (o + 1)))
    (hlen : len = tail + 1)
    (hcover : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc
      len numcells tcell cursor outBest)
    (hsound : LoopSound ctx bound best outBest) :
    LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab rsPtn
      tc len numcells tcell cursor bound st { out with fixedpts := fixedpts }
      best outBest trail (some value) := by
  have hfreeze' := hfreeze.setFixed fixedpts
  apply LoopExit.frozen value rfl hbelow
  · rw [hlen] at hcover
    exact hfreeze.exactLoop hlevel hbelow hbound hcover hsound
  · exact hfreeze'

/-- Convert an integer-valued loop exit to the enclosing node, shortening
the frozen comparison prefix at the node boundary. -/
theorem toNodeSome {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {nodeCodes loopCodes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {trail : FrameTrail} {value : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hprefix : loopCodes.take nodeCodes.length = nodeCodes)
    (h : LoopExit ctx tcLevel loopSpecFuel runFuel loopFuel level loopCodes
      rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out best
      outBest trail (some value)) :
    NodeExit ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes nodeSt out
      nodeNumcells best outBest trail value := by
  cases h with
  | done returned => cases returned
  | unwind target returned below sound payload located control =>
      refine NodeExit.unwind (target := target)
        (returned := Option.some.inj returned) (below := below)
        (sound := ?_) (payload := payload) located control
      constructor
      · intro b hb
        rw [← hbound]
        exact sound.upper b hb
      · exact sound.grows
  | frozen value returned below exact freeze =>
      cases Option.some.inj returned
      apply NodeExit.frozen
      · exact below
      · simpa only [← hbound] using exact
      · exact (freeze.shrink hprefix)
  | cheap boundary returned positive below saved exact =>
      apply NodeExit.cheap boundary (Option.some.inj returned) positive below
      · exact saved
      simpa only [← hbound] using exact
  | exhausted returned => cases returned

/-- With nonzero cursor fuel, a `none` loop result is genuine completion
and supplies the enclosing node's ordinary one-level return. -/
theorem toNodeNone {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {nodeCodes loopCodes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {trail : FrameTrail}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hfuel : n < cursorRank cursor + loopFuel)
    (h : LoopExit ctx tcLevel loopSpecFuel runFuel loopFuel level loopCodes
      rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out best
      outBest trail none) :
    NodeExit ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes nodeSt out
      nodeNumcells best outBest trail (Int.ofNat level - 1) := by
  cases h with
  | done _ exact =>
      apply NodeExit.done rfl
      simpa only [← hbound] using exact
  | unwind _ returned => cases returned
  | frozen _ returned => cases returned
  | cheap _ returned => cases returned
  | exhausted _ finalCursor progress bounded =>
      exact (LoopResult.exhaustion_false hfuel progress bounded).elim

end LoopExit

namespace RunPrep

/-- A fresh request from the frozen-downward `processnode` arm records
the implicit pair admitted at the saved cheap-cell boundary. -/
theorem fastSource {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hbound : st.noncheaplevel ≤ level)
    (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0)
    (hclear : st.needshortprune = false)
    (hshort : (processnode ctx level numcells st).2.needshortprune = true) :
    ShortSource G ctx (processnode ctx level numcells st).2 trail
      (processnode ctx level numcells st).1 := by
  let value := pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon
  have hnonneg : 0 ≤ value :=
    pruneReturn_nonneg h.cheap.positive h.codeInv.eqlev_nonneg
  have hne : level ≠ st.noncheaplevel :=
    processnode_fast_short_ne hg hclear hshort
  apply ShortSource.implicit value.toNat
  · rw [(processnode_fast hg).1]
    exact (Int.toNat_of_nonneg hnonneg).symm
  · rw [(processnode_frames ctx level numcells st).2.2.2.2.2.2.2.1]
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg hnonneg]
    exact pruneReturn_lt
  · rw [processnode_fast_autos hg]
    have hback := pruneAutos_back h.workspace hne
    rw [(processnode_frames ctx level numcells st).1,
      (processnode_frames ctx level numcells st).2.1,
      (processnode_frames ctx level numcells st).2.2.2.2.2.2.2.1]
    exact hback
  · rw [(processnode_frames ctx level numcells st).1,
      (processnode_frames ctx level numcells st).2.1,
      (processnode_frames ctx level numcells st).2.2.2.2.2.2.2.1]
    exact h.cheap.ready hbound hne

end RunPrep

namespace NodeInv

/-- A negative, non-generator discrete leaf produces its exit
classification: ordinary comparison pruning retains its frozen prefix, and
the other return is the explicit cheap-cell jump. -/
theorem negativeLeaf {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = true)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hgen : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hearly : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      NodeRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf hn0 hlevel hpath
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  obtain ⟨outBest, houtcome, hexact⟩ := hnode.plainLeaf
    (inf := inf) (specFuel := specFuel) (fuel := fuel) hn0
    hsymm hloop hlevel hpath hcheap hnum hdisc hef hgen hearly hlive
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  have hfirstNe : leaf.eqlevFirst ≠ level := by
    intro heq
    apply hef
    simp only [leaf, heq, beq_self_eq_true]
  have hmode := hprep.pruneMode hfull hstem hfirstNe hneg
  have hexit : NodeExit ctx tcLevel (specFuel + 1) (fuel + 1) level
      codes st (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
    rcases hmode with hfreeze | hjump
    · rw [hout]
      apply NodeExit.frozen hearly hexact
      have hreadOut : stInc ctx (processnode ctx level n leaf).2 =
          outBest := by
        rw [← hout]
        exact houtcome.event.read
      have hsame : best = outBest := hfreeze.read.symm.trans hreadOut
      rw [← hsame]
      simpa only [leaf] using hfreeze
    · apply NodeExit.cheap leaf.noncheaplevel
      · rw [hout]
        exact hjump
      · exact hprep.cheap.positive
      · exact hcheap'
      · rw [hout]
        exact (processnode_frames ctx level n leaf).2.2.2.2.2.2.2.1
      · exact hexact
  refine ⟨outBest, ?_⟩
  exact {
    exit := hexit
    event := houtcome.event
    preserved := houtcome.preserved
    fixed := otherNode_leaf_early_fixedpts ctx inf tcLevel fuel level
      numcells st hnum hearly
    short := by
      rw [hout]
      intro hshort
      apply hprep.fastSource hcheap' ⟨hfirstNe, hneg⟩
        (by rw [otherLeafSt_short, hnode.shortClear]) hshort }

/-- An early off-path leaf also preserves the guide and coset fields used
when its unwind stops at the immediately enclosing sibling loop. -/
theorem earlyOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hpath : level = codes.length + 1)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hearly : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hrun : NodeRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs
      st (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  let leaf := otherLeafSt ctx level numcells st
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  have hprep := hnode.run.otherLeaf hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hfirst : (processnode ctx level n leaf).2.gcaFirst =
      st.gcaFirst :=
    (processnode_frames ctx level n leaf).2.2.2.2.2.2.1 |>.trans
      (by simpa only [leaf] using
        (RefTrail.otherLeaf_gcaFirst ctx level numcells st))
  have horder : (processnode ctx level n leaf).2.gcaFirst ≤
      (processnode ctx level n leaf).2.gcaCanon :=
    (hlive'.processnode (by simpa only [leaf] using hprep.trailOk)
      (by simpa only [leaf] using hprep.firstBound)).2
  have hleafCanonGca : leaf.gcaCanon = st.gcaCanon := by
    simpa only [leaf] using
      (RefTrail.otherLeaf_gcaCanon ctx level numcells st)
  have hleafCanonLab : leaf.canonlab = st.canonlab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt n :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    change (otherNodePrep level rs.longcode base).canonlab = st.canonlab
    rw [(otherNodePrep_frames level rs.longcode base).1]
  have hleafLab : leaf.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt n :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    change (otherNodePrep level rs.longcode base).lab = rs.lab
    exact (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.2.2.2.2.2.1
  have hcanon :
      ((processnode ctx level n leaf).2.gcaCanon = st.gcaCanon ∧
          (processnode ctx level n leaf).2.canonlab = st.canonlab) ∨
        (level ≤ (processnode ctx level n leaf).2.gcaCanon ∧
          cellsPerm st.ptn level st.lab
            (processnode ctx level n leaf).2.canonlab) := by
    rcases processnode_canonGuide ctx level n leaf with hold | hnew
    · exact Or.inl ⟨hold.1.trans hleafCanonGca,
        hold.2.trans hleafCanonLab⟩
    · right
      constructor
      · rw [hnew.1]
        exact Nat.le_refl level
      · rw [hnew.2, hleafLab]
        exact (refine_refInv (ctx := ctx)
          (by
            rw [hnode.run.searchOk.ptnSize]
            exact Nat.le_refl n)
          (hnode.run.searchOk.labSize.trans
            hnode.run.searchOk.ptnSize.symm)
          (searchOk_end hn0 hnode.run.searchOk hlevel)).perm
  exact {
    node := hrun
    firstGuide := by rw [hout]; exact hfirst
    order := by rw [hout]; exact horder
    canonGuide := by rw [hout]; exact hcanon
    coset := by
      rw [hout]
      exact (processnode_coset ctx level n leaf).trans
        (by simpa only [leaf] using
          (OtherProof.otherLeafSt_coset ctx level numcells st)) }

/-- A code-one automorphism leaf returns the stored first-path unwind,
with all off-path control fields retained for the enclosing sibling loop. -/
theorem firstOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hnp : (otherLeafSt ctx level numcells st).compCanon ≤ 0)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true)
    (hsent : (otherLeafSt ctx level numcells st).firstcode[level + 1]! =
      codeSentinel)
    (hpass : isautom ctx (firstScatter n
      (otherLeafSt ctx level numcells st).firstlab
      (otherLeafSt ctx level numcells st).lab) = true)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  obtain ⟨houtcome, target, hreturned, hbelow, hcontrol, payload, hloc⟩ :=
    hnode.firstLeaf (inf := inf) (specFuel := specFuel) (fuel := fuel)
      hn0 hgsz hsymm hloop hlevel hpath hnum hnp heq hsent hpass
      hlive
  let leaf := otherLeafSt ctx level numcells st
  have hfirstBelow : leaf.gcaFirst < level := by
    change (otherLeafSt ctx level numcells st).gcaFirst < level
    rw [RefTrail.otherLeaf_gcaFirst]
    exact hnode.firstBelow
  have hreturn := (processnode_auto (ctx := ctx) (level := level)
    (numcells := n) (st := leaf) heq hsent (by simp) hpass).1
  have hearly : (processnode ctx level n leaf).1 <
      Int.ofNat level := by
    rw [hreturn]
    exact Int.ofNat_lt.mpr hfirstBelow
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  have hrun : NodeRun G ctx tcLevel (specFuel + 1) (fuel + 1) level
      codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := {
    exit := NodeExit.unwind target hreturned hbelow
      (NodeSound.refl ctx tcLevel (specFuel + 1) level codes st numcells
        best)
      payload hloc hcontrol
    event := houtcome.event
    preserved := houtcome.preserved
    fixed := otherNode_leaf_early_fixedpts ctx inf tcLevel fuel level
      numcells st hnum hearly
    short := by
      intro hshort
      rw [hout] at hshort
      have hleafClear : leaf.needshortprune = false := by
        rw [otherLeafSt_short, hnode.shortClear]
      rw [processnode_auto_short heq hsent (by simp) hpass,
        hleafClear] at hshort
      cases hshort }
  exact hnode.earlyOther hn0 hlevel hpath hnum hearly hlive hrun

/-- A code-two row tie returns either its canonical guide or its
first-ancestor orbit guide, retaining the chosen unwind explicitly. -/
theorem tiedOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hcc : (otherLeafSt ctx level numcells st).compCanon = 0)
    (hge : ¬(level < (otherLeafSt ctx level numcells st).canonlevel))
    (htie : (testcanlab ctx (updatecan ctx
      (otherLeafSt ctx level numcells st).canong
      (otherLeafSt ctx level numcells st).canonlab
      (otherLeafSt ctx level numcells st).samerows)
      (otherLeafSt ctx level numcells st).lab).1 = 0)
    (hcoset : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.cosetindex < n)
    (horbit : OrbSound (OrbConn (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.genTrace.toList n)
      (processnode ctx level n
        (otherLeafSt ctx level numcells st)).2.orbits n)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  obtain ⟨houtcome, target, hreturned, hbelow, hcontrol, payload, hloc⟩ :=
    hnode.tiedLeaf (inf := inf) (specFuel := specFuel) (fuel := fuel)
      hn0 hgsz hsymm hloop hlevel hpath hcheap hnum hef hcc hge
      htie hcoset horbit hlive
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hprep : RunPrep G ctx tcLevel level full bs fs n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hcanonBelow : leaf.gcaCanon < level := by
    change (otherLeafSt ctx level numcells st).gcaCanon < level
    rw [RefTrail.otherLeaf_gcaCanon]
    exact hnode.canonBelow
  have hfirstBelow : leaf.gcaFirst < level :=
    Nat.lt_of_le_of_lt hlive'.order hcanonBelow
  have hreturns := (processnode_rowTie (ctx := ctx) (level := level)
    (numcells := n) (st := leaf) hef (by simp) hcc hge htie).1
  have hearly : (processnode ctx level n leaf).1 <
      Int.ofNat level := by
    rcases hreturns with hfirst | hcanon
    · rw [hfirst]
      exact Int.ofNat_lt.mpr hfirstBelow
    · rw [hcanon]
      exact Int.ofNat_lt.mpr hcanonBelow
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  have hrun : NodeRun G ctx tcLevel (specFuel + 1) (fuel + 1) level
      codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := {
    exit := NodeExit.unwind target hreturned hbelow
      (NodeSound.refl ctx tcLevel (specFuel + 1) level codes st numcells
        best)
      payload hloc hcontrol
    event := houtcome.event
    preserved := houtcome.preserved
    fixed := otherNode_leaf_early_fixedpts ctx inf tcLevel fuel level
      numcells st hnum hearly
    short := by
      rw [hout]
      intro hshort
      have hleafClear : leaf.needshortprune = false := by
        rw [otherLeafSt_short, hnode.shortClear]
      apply ShortSource.explicit leaf.gcaCanon
        (fmperm (canonScatter n leaf.canonlab leaf.lab) n).1
        (fmperm (canonScatter n leaf.canonlab leaf.lab) n).2
      · exact processnode_rowTie_short hef (by simp) hcc hge htie
          hleafClear hshort
      · exact hprep.rowTieBack hef (by simp) hcc hge htie
      · intro entry hentry
        exact hlive'.rowTiePair hn0 hprep hcanonBelow htie hentry }
  exact hnode.earlyOther hn0 hlevel hpath hnum hearly hlive hrun

/-- The negative non-generator leaf, with the off-path fields needed by
its parent loop retained. -/
theorem negativeOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = true)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hgen : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hearly : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  obtain ⟨outBest, hrun⟩ := hnode.negativeLeaf
    (inf := inf) (specFuel := specFuel) (fuel := fuel) hn0 hsymm
    hloop hlevel hpath hcheap hnum hdisc hef hneg hgen hearly hlive
  exact ⟨outBest, hnode.earlyOther hn0 hlevel hpath hnum hearly
    hlive hrun⟩

/-- A non-generator leaf whose return remains at the current boundary is
an ordinary exact off-path node run. -/
theorem doneLeaf {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = true)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hgen : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hdone : ¬((processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  obtain ⟨outBest, houtcome, hexact⟩ := hnode.plainLeafDone
    (inf := inf) (specFuel := specFuel) (fuel := fuel) hn0 hsymm
    hloop hlevel hpath hcheap hnum hdisc hef hgen hdone hlive
  let leaf := otherLeafSt ctx level numcells st
  let final := leafFinish level (processnode ctx level n leaf).2
  have hout := otherNode_leaf_done_state ctx inf tcLevel fuel level
    numcells st hnum hdone
  have hfirstProc : (processnode ctx level n leaf).2.gcaFirst =
      leaf.gcaFirst :=
    (processnode_frames ctx level n leaf).2.2.2.2.2.2.1
  have hfirstLeaf : leaf.gcaFirst = st.gcaFirst := by
    simpa only [leaf] using
      (RefTrail.otherLeaf_gcaFirst ctx level numcells st)
  have hfirst : final.gcaFirst = st.gcaFirst := by
    have heq : final.gcaFirst =
        (processnode ctx level n leaf).2.gcaFirst := by
      unfold final
      rw [leafFinish]
      split <;> split <;> rfl
    exact heq.trans (hfirstProc.trans hfirstLeaf)
  have horderProc : (processnode ctx level n leaf).2.gcaFirst ≤
      (processnode ctx level n leaf).2.gcaCanon :=
    (hlive.otherLeaf (numcells := numcells) |>.processnode
      (by simpa only [leaf] using
        (hnode.run.otherLeaf hn0 hlevel hpath).trailOk)
      (by simpa only [leaf] using
        (hnode.run.otherLeaf hn0 hlevel hpath).firstBound)).2
  have horder : final.gcaFirst ≤ final.gcaCanon := by
    have hfirstEq : final.gcaFirst =
        (processnode ctx level n leaf).2.gcaFirst := by
      unfold final
      rw [leafFinish]
      split <;> split <;> rfl
    have hcanonEq : final.gcaCanon =
        (processnode ctx level n leaf).2.gcaCanon := by
      unfold final
      rw [leafFinish]
      split <;> split <;> rfl
    rw [hfirstEq, hcanonEq]
    exact horderProc
  have hcanonGca : final.gcaCanon =
      (processnode ctx level n leaf).2.gcaCanon := by
    unfold final
    rw [leafFinish]
    split <;> split <;> rfl
  have hcanonLab : final.canonlab =
      (processnode ctx level n leaf).2.canonlab := by
    unfold final
    rw [leafFinish]
    split <;> split <;> rfl
  have hleafCanonGca : leaf.gcaCanon = st.gcaCanon := by
    simpa only [leaf] using
      (RefTrail.otherLeaf_gcaCanon ctx level numcells st)
  have hleafCanonLab : leaf.canonlab = st.canonlab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt n :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    change (otherNodePrep level rs.longcode base).canonlab = st.canonlab
    rw [(otherNodePrep_frames level rs.longcode base).1]
  have hleafLab : leaf.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt n :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    change (otherNodePrep level rs.longcode base).lab = rs.lab
    exact (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.2.2.2.2.2.1
  have hcanon :
      (final.gcaCanon = st.gcaCanon ∧ final.canonlab = st.canonlab) ∨
        (level ≤ final.gcaCanon ∧
          cellsPerm st.ptn level st.lab final.canonlab) := by
    rcases processnode_canonGuide ctx level n leaf with hold | hnew
    · left
      exact ⟨hcanonGca.trans (hold.1.trans hleafCanonGca),
        hcanonLab.trans (hold.2.trans hleafCanonLab)⟩
    · right
      constructor
      · rw [hcanonGca, hnew.1]
        exact Nat.le_refl level
      · rw [hcanonLab, hnew.2, hleafLab]
        exact (refine_refInv (ctx := ctx)
          (by
            rw [hnode.run.searchOk.ptnSize]
            exact Nat.le_refl n)
          (hnode.run.searchOk.labSize.trans
            hnode.run.searchOk.ptnSize.symm)
          (searchOk_end hn0 hnode.run.searchOk hlevel)).perm
  have hother : OtherOutcome G ctx tcLevel (specFuel + 1) (fuel + 1)
      level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := {
    node := houtcome
    firstGuide := by rw [hout]; exact hfirst
    order := by rw [hout]; exact horder
    canonGuide := by rw [hout]; exact hcanon }
  have hproof := OtherProof.ofLeafDone hnum hdone hother
  refine ⟨outBest, ?_⟩
  exact {
    node := {
      exit := NodeExit.done (congrArg Prod.fst hout) hexact
      event := houtcome.event
      preserved := houtcome.preserved
      fixed := hproof.fixed
      short := by
        intro hshort
        rw [hout, leafFinish_short] at hshort
        cases hshort }
    firstGuide := hproof.outcome.firstGuide
    order := hproof.outcome.order
    canonGuide := hproof.outcome.canonGuide
    coset := hproof.coset }

end NodeInv

end Hex.GraphIso.Nauty

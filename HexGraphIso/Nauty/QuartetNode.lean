/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.QuartetStmt
import all HexGraphIso.Nauty.Search

public section

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
theorem stInc_congr {ctx : Ctx} {st st' : SearchSt}
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
theorem stInc_numnodes {ctx : Ctx} (st : SearchSt) (m : Nat) :
    stInc ctx { st with numnodes := m } = stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- Refining leaves the incumbent alone: it writes the labelling, the
partition and the active set. -/
theorem stInc_refined {ctx : Ctx} (st : SearchSt)
    (lab ptn : Array Nat) (active : Nat) :
    stInc ctx { st with lab := lab, ptn := ptn, active := active } =
      stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- Recording this node's refinement code leaves the incumbent alone.
`firstcode` is the first path's ledger, not the incumbent's. -/
theorem stInc_firstcode {ctx : Ctx} (st : SearchSt) (fc : Array Nat) :
    stInc ctx { st with firstcode := fc } = stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- Recording this node's target cell leaves the incumbent alone. -/
theorem stInc_firsttc {ctx : Ctx} (st : SearchSt) (ftc : Array Int) :
    stInc ctx { st with firsttc := ftc } = stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- Accumulating the target-cell total leaves the incumbent alone. -/
theorem stInc_tctotal {ctx : Ctx} (st : SearchSt) (m : Nat) :
    stInc ctx { st with tctotal := m } = stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- Raising the cheap-automorphism level leaves the incumbent alone. -/
theorem stInc_noncheaplevel {ctx : Ctx} (st : SearchSt) (m : Nat) :
    stInc ctx { st with noncheaplevel := m } = stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- The node's exit adjustment leaves the incumbent alone. This is the
`allsamelevel` decrement `firstPathNode` performs when its target cell
was exhausted, and it is the only write between the child loop's return
and the node's own. -/
theorem stInc_allsamelevel {ctx : Ctx} (st : SearchSt) (m : Nat) :
    stInc ctx { st with allsamelevel := m } = stInc ctx st :=
  stInc_congr rfl rfl rfl

/-- The comparison bookkeeping `otherNode` performs before choosing its
target cell leaves the incumbent alone, except through `canoncode`,
which it rewrites exactly when the current node's code beats the
incumbent's at this level. Stated as the three fields so the caller can
see which one moves. -/
theorem stInc_otherNodePrep {ctx : Ctx} (level code : Nat)
    (st : SearchSt) :
    (otherNodePrep level code st).canonlevel = st.canonlevel ∧
      (otherNodePrep level code st).canonlab = st.canonlab :=
  ⟨(otherNodePrep_frames level code st).2.2.2.1,
    (otherNodePrep_frames level code st).1⟩

/-! # The leaf arm installs

`firstterminal` is where a first-path leaf becomes the incumbent. These
record what it leaves behind, which is what makes `NodeConcl.installed`
true on the leaf arm and fixes the `some` the absorption equation
needs. -/

/-- A first-path leaf installs itself: the incumbent's level is this
node's. -/
theorem firstterminal_canonlevel (level : Nat) (st : SearchSt) :
    (firstterminal level st).canonlevel = level := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

/-- A first-path leaf installs its own labelling. -/
theorem firstterminal_canonlab (level : Nat) (st : SearchSt) :
    (firstterminal level st).canonlab = st.lab := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

/-- A first-path leaf at a positive level leaves something installed,
which is `NodeConcl.installed` on the leaf arm. -/
theorem firstterminal_installed {level : Nat} (hlev : level ≠ 0)
    (st : SearchSt) : (firstterminal level st).canonlevel ≠ 0 := by
  rw [firstterminal_canonlevel]
  exact hlev

/-! # A boundary case `NodeConcl` does not separate

`NodeConcl` splits on the returned level: `full` fires at
`Int.ofNat level - 1` and `carried` strictly below it. The search does
not respect that split, because a node returns `Int.ofNat level - 1` in
two different ways.

`firstChildLoop` at `level` abandons its sweep exactly when a child
returns below `level` (`Search.lean`, the `rtnlevel < Int.ofNat level`
test), handing back `some rtnlevel`; `firstPathNode` then returns that
value unchanged. Since `Int.ofNat level - 1 < Int.ofNat level`, a child
returning `level - 1` makes the node return `Int.ofNat level - 1` with
its loop cut short, so the children after the abandoned one were never
visited. `NodeConcl.full` nonetheless demands the whole subtree's
absorption there, while `NodeConcl.carried`, whose guard is strict,
supplies nothing. `otherNode` has the same shape twice, once after
`processnode` and once after its loop.

The configuration is reachable, not vacuous. `firstChildLoop` sets
`gcaFirst := level` after its `tv1` child returns, so once the loop at
`level - 1` has taken its first-path child, the state carries
`gcaFirst = level - 1`; a later sibling of that loop runs `otherNode` at
`level`, and a code-one `processnode` anywhere below returns
`gcaFirst`, which is `level - 1`. That value propagates up to the node
at `level`, which returns it through the abandoning branch.

The repair is to let the completed case carry a payload too, so that
`full` at `Int.ofNat level - 1` offers the absorption equation *or* a
`CarrierOut`, and the caller's loop discharges the payload at the
ancestor it names. That matches the architecture the file's design note
describes, where a generator return is absorbed at the greatest common
ancestor rather than at the leaf, and it is what lets the loop at
`level - 1` continue instead of propagating. It is not made here
because the root assembly consumes the equation directly
(`dominated_of_root`), so changing the shape means re-deriving that
assembly and checking the root's own boundary, where the node at level
one returns zero. -/

end Hex.GraphIso.Nauty

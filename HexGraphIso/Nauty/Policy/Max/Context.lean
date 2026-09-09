/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Frame
import all HexGraphIso.Nauty.Policy.Canon.Ref
import all HexGraphIso.Nauty.Policy.First.Entry
import all HexGraphIso.Nauty.Policy.First.Run
import all HexGraphIso.Nauty.Policy.FilterCover
import all HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- The geometric and path bounds of a frozen node. -/
structure Frame.Valid (G : Colored n k) (f : Frame n) : Prop where
  positive : 1 ≤ f.level
  depth : f.level ≤ n
  length : f.codes.length + 1 = f.level
  partition : SearchOk G f.level f.numcells f.entry

/-- A frozen node's target selection, before its children are visited. -/
structure Loop (n : Nat) where
  node : Frame n
  first : Bool

/-- The engine's common preparation of an internal node's sweep. -/
def Loop.prepare (ctx : Ctx n) (tcLevel : Nat) (l : Loop n) :
    Nat × Int × VSet n × Nat × Search n :=
  let f := l.node
  let (nc, code, st) := visit ctx f.level f.numcells f.entry
  let st := if l.first then recordFirst f.level code st else compareCodes f.level code st
  let (tc, cell, len, st) := chooseTarget l.first ctx tcLevel f.level nc st
  (nc, tc, cell, len, cheapCheck l.first f.level st)

/-- The common code prefix of the chosen children. -/
def Loop.codes (ctx : Ctx n) (l : Loop n) : List Nat :=
  l.node.codes ++ [l.node.code ctx]

/-- A child's full specification key in the frozen sweep ordering. -/
def Loop.key (ctx : Ctx n) (tcLevel : Nat) (l : Loop n) (v : Nat) : Key n :=
  let p := l.prepare ctx tcLevel
  prefixKey (l.codes ctx) (vertexKey ctx tcLevel (n - l.node.level) l.node.level
    p.2.2.2.2.lab p.2.2.2.2.ptn p.2.1.toNat p.1 v)

/-- A target agrees with the specification, or a negative code comparison
already bounds the entire frozen node by the incumbent. -/
def Loop.Choice (ctx : Ctx n) (tcLevel : Nat) (l : Loop n) (best : Option (Key n)) : Prop :=
  let r := l.node.entry.refined ctx l.node.level l.node.numcells
  specTargetcell ctx r.lab r.ptn l.node.level tcLevel =
    (l.prepare ctx tcLevel).2.1.toNat ∨ Generic.Covers (l.node.key ctx tcLevel) best

/-- A suspended parent retains the state at its chosen child's entry,
including the incumbent codes used by its already covered references. -/
structure Parent (n : Nat) where
  loop : Loop n
  state : Search n
  chosen : Nat
  bs : List Nat
  fs : List Nat

/-- The actual individualization at a suspended parent. -/
def Parent.child (ctx : Ctx n) (tcLevel : Nat) (p : Parent n) : Frame n :=
  let r := p.loop.prepare ctx tcLevel
  { level := p.loop.node.level + 1
    numcells := r.1 + 1
    codes := p.loop.codes ctx
    entry := Nauty.child p.loop.first p.loop.node.level r.2.1.toNat p.chosen p.state }

/-- Reference and geometric facts retained at a suspended parent. -/
structure Parent.Valid (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat)
    (p : Parent n) : Prop where
  node : p.loop.node.Valid G
  partition : SearchOk G p.loop.node.level (p.loop.prepare ctx tcLevel).1 p.state
  effect : SearchOut G p.loop.node.level p.loop.node.level
    (p.loop.prepare ctx tcLevel).2.2.2.2 p.state
  equitable : Equitable ctx p.loop.node.level p.state.lab p.state.ptn
  cell : IsCell (p.loop.prepare ctx tcLevel).2.2.2.2.ptn p.loop.node.level
    (p.loop.prepare ctx tcLevel).2.1.toNat (p.loop.prepare ctx tcLevel).2.2.2.1
  len : 2 ≤ (p.loop.prepare ctx tcLevel).2.2.2.1
  range : (p.loop.prepare ctx tcLevel).2.1.toNat +
    (p.loop.prepare ctx tcLevel).2.2.2.1 ≤ n
  chosen : (windowSet n p.state.lab (p.loop.prepare ctx tcLevel).2.1.toNat
    (p.loop.prepare ctx tcLevel).2.2.2.1).mem p.chosen = true
  path : PathInv G ctx p.loop.node.level p.state
  choice : p.loop.Choice ctx tcLevel (p.state.key ctx p.bs)
  canonical : CanonGuide p.loop.node.level (p.loop.prepare ctx tcLevel).2.1.toNat
    (p.loop.prepare ctx tcLevel).2.2.2.2 (p.loop.key ctx tcLevel) (p.state.key ctx p.bs) p.state
  first : p.state.gcaFirst = p.loop.node.level →
    Generic.Covers (p.loop.key ctx tcLevel p.state.firstlab[(p.loop.prepare ctx tcLevel).2.1.toNat]!)
      (p.state.key ctx p.bs) ∧
      cellsPerm (p.loop.prepare ctx tcLevel).2.2.2.2.ptn p.loop.node.level
        (p.loop.prepare ctx tcLevel).2.2.2.2.lab p.state.firstlab
  small : p.state.noncheaplevel ≤ p.loop.node.level →
    SubtreeOk ctx p.loop.node.level
      ⟨p.state.lab, p.state.ptn, p.state.active, (p.loop.prepare ctx tcLevel).1, 0, 0, 0⟩
  earlier : ∀ v, (windowSet n (p.loop.prepare ctx tcLevel).2.2.2.2.lab
    (p.loop.prepare ctx tcLevel).2.1.toNat (p.loop.prepare ctx tcLevel).2.2.2.1).mem v = true →
    v < p.chosen → Generic.Covers (p.loop.key ctx tcLevel v) (p.state.key ctx p.bs)

/-- Suspended ancestors indexed by their sweep levels. -/
abbrev Parents (n : Nat) := Nat → Option (Parent n)

/-- Each suspended parent names its current child's specification subtree.
The outermost parent also retains the root subtree at return target zero. -/
def Parents.frames (ctx : Ctx n) (tcLevel : Nat) (parents : Parents n) : Frames n :=
  fun level => if level = 0 then (parents 1).map (fun p => p.loop.node)
    else (parents level).map (Parent.child ctx tcLevel)

/-- The current call retains each ancestor's cell frame, chosen vertex,
reference location, code prefix, and previously installed incumbent. -/
structure Scope (G : Colored n k) (ctx : Ctx n) (tcLevel level : Nat)
    (cs bs : List Nat) (st : Search n) (parents : Parents n) : Prop where
  complete : ∀ t, 1 ≤ t → t < level → ∃ p, parents t = some p
  valid : ∀ t p, parents t = some p →
    1 ≤ t ∧ t < level ∧ p.loop.node.level = t ∧ p.Valid G ctx tcLevel
  codes : ∀ t p, parents t = some p → p.loop.codes ctx <+: cs
  code : ∀ t p, parents t = some p → t < cs.length →
    (p.child ctx tcLevel).code ctx = cs[t]!
  grows : ∀ t p, parents t = some p → Generic.Grows (p.state.key ctx p.bs) (st.key ctx bs)
  effect : ∀ t p, parents t = some p → SearchOut G t t p.state st
  chosen : ∀ t p, parents t = some p → st.lab[(p.loop.prepare ctx tcLevel).2.1.toNat]! = p.chosen
  canonical : ∀ t p, parents t = some p → st.gcaCanon ≤ t →
    st.gcaCanon = p.state.gcaCanon ∧ st.canonlab = p.state.canonlab
  first : ∀ t p, parents t = some p → st.gcaFirst ≤ t →
    st.gcaFirst = p.state.gcaFirst ∧ st.firstlab = p.state.firstlab
  boundary : ∀ t p, parents t = some p →
    st.noncheaplevel = p.state.noncheaplevel ∨ t + 1 ≤ st.noncheaplevel
  generators : ∀ t p, parents t = some p → p.loop.first = true →
    ∀ γ ∈ st.genTrace, CellStab p.state.ptn t p.state.lab γ
  coset : ∀ t p, parents t = some p → 0 < st.canonlevel → st.gcaFirst = t →
    p.loop.first = true ∧ st.cosetindex = p.chosen
  chain : ∀ t p, parents t = some p → 1 < t →
    ∃ prev, parents (t - 1) = some prev ∧ prev.child ctx tcLevel = p.loop.node

/-- The first node has no suspended ancestors. -/
theorem Scope.root (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat)
    (bs : List Nat) (st : Search n) : Scope G ctx tcLevel 1 [] bs st (fun _ => none) := by
  constructor
  · intro t ht hl; omega
  all_goals intro t p hp; cases hp

/-- Before the first leaf, only the first path's stored code prefix is needed.
Later entries have both comparison machines and an installed incumbent. -/
def Entry (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat) (first : Bool)
    (f : Frame n) (bs fs : List Nat) : Prop :=
  if first then
    FirstPre G ctx f.level f.numcells f.entry ∧ bs = [] ∧ fs = [] ∧
      f.entry.canonlevel = 0 ∧ f.entry.genTrace = #[] ∧
      f.entry.canoncode.size = n + 2 ∧ StoredCodes f.entry.firstcode 1 f.codes ∧
      (∀ code ∈ f.codes, code < codeSentinel) ∧
      f.entry.gcaFirst < f.level ∧ f.entry.gcaCanon < f.level
  else
    Nauty.NodePre G ctx tcLevel f.level f.numcells f.entry ∧
      Comparison ctx f.codes bs fs f.entry

/-- A node contract is quantified over its actual semantic context. -/
structure NodeInput (G : Colored n k) (ctx : Ctx n) (tcLevel fuel : Nat)
    (first : Bool) (f : Frame n) (bs fs : List Nat) (parents : Parents n) : Prop where
  frame : f.Valid G
  fuel : n + 1 ≤ f.level + fuel
  entry : Entry G ctx tcLevel first f bs fs
  scope : Scope G ctx tcLevel f.level f.codes bs f.entry parents
  parent : 1 < f.level →
    ∃ p, parents (f.level - 1) = some p ∧ p.child ctx tcLevel = f
  counters : 0 < f.entry.canonlevel →
    0 < f.entry.gcaFirst ∧ f.entry.gcaFirst ≤ f.entry.gcaCanon

end Hex.GraphIso.Nauty.Max

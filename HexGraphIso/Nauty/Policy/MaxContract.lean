/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxContext
public import HexGraphIso.Nauty.Policy.MaxCarry
import all HexGraphIso.Nauty.Policy.MaxCarry
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxFrame
import all HexGraphIso.Nauty.Policy.FilterCover
import all HexGraphIso.Nauty.Policy.FirstEntry
import all HexGraphIso.Nauty.Policy.Fuel
import all HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- The full chosen-cell bound, including vertices subsequently filtered out. -/
def Loop.bound (ctx : Ctx n) (tcLevel : Nat) (l : Loop n) : Key n :=
  let p := l.prepare ctx tcLevel
  keysMax (l.key ctx tcLevel p.2.2.2.2.lab[p.2.1.toNat]!)
    ((List.range' 1 (p.2.2.2.1 - 1)).map fun o =>
      l.key ctx tcLevel p.2.2.2.2.lab[p.2.1.toNat + o]!)

/-- A cursor names the next vertex to consider, not the previous vertex. -/
def Remaining (cursor : Option Nat) (cell : VSet n) (v : Nat) : Prop :=
  cell.mem v = true ∧ ∃ tv, cursor = some tv ∧ tv ≤ v

/-- A sweep starts before its first leaf or resumes with both comparisons
initialized. Both cases retain coverage in the original target window. -/
structure SweepInput (G : Colored n k) (ctx : Ctx n) (tcLevel fuel cfuel : Nat)
    (first : Bool) (level numcells tc tv1 : Nat) (cursor : Option Nat) (cell : VSet n)
    (index : Nat) (st : Search n) (l : Loop n) (bs fs : List Nat)
    (parents : Parents n) : Prop where
  node : l.node.Valid G
  first_eq : first = l.first
  level_eq : level = l.node.level
  numcells_eq : numcells = (l.prepare ctx tcLevel).1
  tc_eq : tc = (l.prepare ctx tcLevel).2.1.toNat
  tv1_eq : tv1 = ((l.prepare ctx tcLevel).2.2.1.nextElem none).getD 0
  origin : ∃ bs₀ fs₀, Entry G ctx tcLevel first l.node bs₀ fs₀
  base : SearchOk G level numcells (l.prepare ctx tcLevel).2.2.2.2.view
  partition : SearchOk G level numcells st.view
  effect : SearchOut G level level (l.prepare ctx tcLevel).2.2.2.2.view st.view
  equitable : Equitable ctx level st.lab st.ptn
  target : Generic.Target Search.view level tc cell st
  window : IsCell (l.prepare ctx tcLevel).2.2.2.2.ptn level tc (l.prepare ctx tcLevel).2.2.2.1
  len : 2 ≤ (l.prepare ctx tcLevel).2.2.2.1
  range : tc + (l.prepare ctx tcLevel).2.2.2.1 ≤ n
  subset : ∀ v, cell.mem v = true →
    (windowSet n (l.prepare ctx tcLevel).2.2.2.2.lab tc (l.prepare ctx tcLevel).2.2.2.1).mem v = true
  cursor_mem : ∀ tv, cursor = some tv → cell.mem tv = true
  fuel : n ≤ level + fuel
  cursor_fuel : Generic.CursorFuel n cfuel cursor
  path : PathInv G ctx level st
  choice : l.Choice ctx tcLevel (st.key ctx bs)
  small : st.noncheaplevel ≤ level →
    SubtreeOk ctx level ⟨st.lab, st.ptn, st.active, numcells, 0, 0, 0⟩
  phase :
    (first = true ∧ bs = [] ∧ fs = [] ∧ st = (l.prepare ctx tcLevel).2.2.2.2 ∧
      cell = (l.prepare ctx tcLevel).2.2.1 ∧ cursor = cell.nextElem none ∧ index = 0) ∨
    (Engine.SweepPre G ctx tcLevel first level numcells tc tv1 cursor cell st ∧
      Comparison ctx (l.codes ctx) bs fs st ∧
      (st.compCanon ≤ 0 ∨ first = false ∧ cursor.isSome))
  coverage : CellCover ctx tcLevel (n - level) level numcells tc
    (l.prepare ctx tcLevel).2.2.2.1 (l.codes ctx) (l.prepare ctx tcLevel).2.2.2.2
    (Remaining cursor cell) (st.key ctx bs)
  canonical : CanonGuide level tc (l.prepare ctx tcLevel).2.2.2.2
    (l.key ctx tcLevel) (st.key ctx bs) st
  first_ref : st.gcaFirst = level →
    Generic.Covers (l.key ctx tcLevel st.firstlab[tc]!) (st.key ctx bs) ∧
      cellsPerm (l.prepare ctx tcLevel).2.2.2.2.ptn level
        (l.prepare ctx tcLevel).2.2.2.2.lab st.firstlab
  generators : first = true → ∀ γ ∈ st.genTrace,
    CellStab (l.prepare ctx tcLevel).2.2.2.2.ptn level (l.prepare ctx tcLevel).2.2.2.2.lab γ
  scope : Scope G ctx tcLevel level (l.codes ctx) bs st parents
  parent : 1 < level → ∃ p, parents (level - 1) = some p ∧ p.child ctx tcLevel = l.node
  counters : 0 < st.canonlevel → 0 < st.gcaFirst ∧ st.gcaFirst ≤ st.gcaCanon
  control : 0 < st.canonlevel →
    (first = true → st.gcaFirst = level) ∧ (first = false → st.gcaFirst < level)

/-- The maximum contract uses ghost incumbent codes at entry and a
settled executable incumbent at return. Each nonlocal witness names a
frozen ancestor subtree rather than the current child by assumption. -/
def keyContract (G : Colored n k) (tcLevel : Nat) : Generic.Contract (Search n) n where
  nodePre _ _ _ _ _ := True
  nodePost fuel first level numcells st result := ∀ cs bs fs parents,
    NodeInput G { g := rowsOf G } tcLevel fuel first ⟨level, numcells, cs, st⟩ bs fs parents →
      Generic.Result (Frame.key { g := rowsOf G } tcLevel ⟨level, numcells, cs, st⟩)
        (st.key { g := rowsOf G } bs) (result.2.best { g := rowsOf G }) (level - 1)
        (Witness { g := rowsOf G } tcLevel (parents.frames { g := rowsOf G } tcLevel)) result.1
  sweepPre _ _ _ _ _ _ _ _ _ _ _ := True
  sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st result := ∀ l bs fs parents,
    SweepInput G { g := rowsOf G } tcLevel fuel cfuel first level numcells tc tv1 cursor cell index
      st l bs fs parents →
      Generic.Result (l.bound { g := rowsOf G } tcLevel)
        (st.key { g := rowsOf G } bs) (result.2.2.best { g := rowsOf G }) level
        (Witness { g := rowsOf G } tcLevel
          ((parents.frames { g := rowsOf G } tcLevel).insert l.node)) result.1

/-- The single recursive contract combines key bounds with preservation
of every accumulated generator at each surviving first ancestor. -/
def contract (G : Colored n k) (tcLevel : Nat) : Generic.Contract (Search n) n where
  nodePre _ _ _ _ _ := True
  nodePost fuel first level numcells st result :=
    (keyContract G tcLevel).nodePost fuel first level numcells st result ∧
      ∀ cs bs fs parents,
        NodeInput G { g := rowsOf G } tcLevel fuel first ⟨level, numcells, cs, st⟩ bs fs parents →
          Keeps parents result.1 result.2
  sweepPre _ _ _ _ _ _ _ _ _ _ _ := True
  sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st result :=
    (keyContract G tcLevel).sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st result ∧
      ∀ l bs fs parents,
        SweepInput G { g := rowsOf G } tcLevel fuel cfuel first level numcells tc tv1 cursor cell index
          st l bs fs parents → Keeps parents result.1 result.2.2

/-- A node with no executable fuel cannot satisfy the adequate-fuel input. -/
theorem node_zero (G : Colored n k) (tcLevel : Nat) (first : Bool)
    (level numcells : Nat) (st : Search n) :
    (contract G tcLevel).nodePost 0 first level numcells st (.fuel, st) := by
  constructor <;> intro cs bs fs parents h
  all_goals
    have hd := h.frame.depth
    have hf := h.fuel
    change level ≤ n at hd
    change n + 1 ≤ level + 0 at hf
    omega

/-- A live cursor with zero sweep fuel cannot satisfy its iteration bound. -/
theorem sweep_zero (G : Colored n k) (tcLevel fuel : Nat) (first : Bool)
    (level numcells tc tv1 tv : Nat) (cell : VSet n) (index : Nat) (st : Search n) :
    (contract G tcLevel).sweepPost fuel 0 first level numcells tc tv1 (some tv) cell index st
      (.fuel, index, st) := by
  constructor <;> intro l bs fs parents h
  all_goals
    have ht := VSet.mem_lt (h.cursor_mem tv rfl)
    have hf := h.cursor_fuel tv rfl
    omega

end Hex.GraphIso.Nauty.Engine.Max

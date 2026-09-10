/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Generation.Orbit

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

/-- Every leaf below a refined state has the same key and target-position
sequence. This is stronger than equality of maximal subtree keys. -/
def Uniform (ctx : Ctx n) (tcLevel level : Nat) (st : RefineSt n)
    (targets : List Nat) (key : Key n) : Prop :=
  ∀ targets' key', HasLeaf ctx tcLevel level st targets' key' → targets' = targets ∧ key' = key

/-- A discrete node has exactly its own leaf key. -/
theorem Uniform.leaf {tcLevel level : Nat} {st : RefineSt n}
    (hok : IterOk ctx level st) (hdisc : ∀ q, q < n → st.ptn[q]! ≤ level) :
    Uniform ctx tcLevel level st [] ⟨[st.longcode, codeSentinel], leafRows ctx st.lab⟩ := by
  intro targets key h
  exact h.discrete hok hdisc

/-- Uniform target children with a common suffix make their parent
uniform, retaining the refinement code and target hint. -/
theorem Uniform.node {tcLevel level tc e : Nat} {st : RefineSt n}
    {targets : List Nat} {key : Key n}
    (hok : IterOk ctx level st) (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (htarget : tc = specTargetcell ctx st.lab st.ptn level tcLevel)
    (hchildren : ∀ o, o ≤ e - tc → Uniform ctx tcLevel (level + 1)
      (childSt ctx level st tc st.lab[tc + o]!) targets key) :
    Uniform ctx tcLevel level st (tc :: targets) ⟨st.longcode :: key.codes, key.rows⟩ := by
  intro targets' key' h
  rcases h.cases with ⟨hdisc, _, _⟩ | ⟨tc', e', o, rest, tail, _, hcell', _, ho, htarget', hchild, rfl, rfl⟩
  · have he := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
    have hopen := target_open hok.ok.ptnSize hok.ok.ptnEnd hcell tc (Nat.le_refl _) hne
    have hc := hdisc tc (by omega)
    omega
  · have htc : tc' = tc := htarget'.trans htarget.symm
    subst htc
    have he : e' = e := cells_eq_of_start (by rw [hok.ok.ptnSize]; exact Nat.le_refl _)
      hok.ok.ptnEnd hcell' hcell
    subst he
    obtain ⟨rfl, rfl⟩ := hchildren o ho rest tail hchild
    exact ⟨rfl, rfl⟩

/-- Each child of a uniform node has the same uniform suffix. -/
theorem Uniform.child {tcLevel level tc e o : Nat} {rs : RefineSt n}
    {targets : List Nat} {key : Key n}
    (h : Uniform ctx tcLevel level rs (tc :: targets) ⟨rs.longcode :: key.codes, key.rows⟩)
    (hlvl : level < n) (hcell : (tc, e) ∈ cells rs.ptn level n) (hne : tc < e)
    (htarget : tc = specTargetcell ctx rs.lab rs.ptn level tcLevel) (ho : o ≤ e - tc) :
    Uniform ctx tcLevel (level + 1) (childSt ctx level rs tc rs.lab[tc + o]!) targets key := by
  intro targets' key' hleaf
  obtain ⟨ht, hk⟩ := h _ _ (hleaf.step hlvl hcell hne ho htarget)
  refine ⟨(List.cons.inj ht).2, ?_⟩
  have hc := (List.cons.inj (congrArg Key.codes hk)).2
  have hr := congrArg Key.rows hk
  cases key
  cases key'
  congr

/-- Checked cell stabilizers carrying every child to one uniform child
make the whole target subtree uniform. -/
theorem Uniform.carriers {tcLevel level tc e oGuide : Nat} {rs : RefineSt n}
    {targets : List Nat} {key : Key n}
    (hok : IterOk ctx level rs) (hlvl : level < n) (hgsz : ctx.g.size = n)
    (hcell : (tc, e) ∈ cells rs.ptn level n) (hne : tc < e)
    (htarget : tc = specTargetcell ctx rs.lab rs.ptn level tcLevel) (hoGuide : oGuide ≤ e - tc)
    (hcarriers : ∀ o, o ≤ e - tc → ∃ γ, checkAutom ctx.g γ = true ∧
      CellStab rs.ptn level rs.lab γ ∧ γ[rs.lab[tc + o]!]! = rs.lab[tc + oGuide]!)
    (hguide : Uniform ctx tcLevel (level + 1)
      (childSt ctx level rs tc rs.lab[tc + oGuide]!) targets key) :
    Uniform ctx tcLevel level rs (tc :: targets) ⟨rs.longcode :: key.codes, key.rows⟩ := by
  apply Uniform.node hok hcell hne htarget
  intro o ho targets' key' hleaf
  obtain ⟨γ, hc, hs, hmap⟩ := hcarriers o ho
  exact hguide targets' key' (hleaf.carried hok hlvl hgsz hc hs hcell hne ho hoGuide hmap)

/-- Transitivity on the target cell extends the uniform first child to
all children. The carriers need only be true automorphisms fixing the
current path; no completeness theorem is used. -/
theorem Uniform.orbit {k : Nat} {G : Colored n k} {base : List (Fin n)}
    {rs : RefineSt n} {st : Search n} {tcLevel level tc e oGuide : Nat}
    {targets : List Nat} {key : Key n} {guide : Fin n}
    (hok : IterOk { g := rowsOf G } level rs) (hlvl : level < n)
    (hpath : PathStab { g := rowsOf G }
      (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 level st)
    (hlab : st.lab = rs.lab) (hptn : st.ptn = rs.ptn)
    (hbase : ∀ b : Fin n, st.fixedpts.mem b.val = true → b ∈ base)
    (hcell : (tc, e) ∈ cells rs.ptn level n) (hne : tc < e)
    (htarget : tc = specTargetcell { g := rowsOf G } rs.lab rs.ptn level tcLevel)
    (hoGuide : oGuide ≤ e - tc) (hatGuide : rs.lab[tc + oGuide]! = guide.val)
    (horbits : ∀ o, o ≤ e - tc → ∃ hv : rs.lab[tc + o]! < n,
      Aut.Orbit G base guide ⟨rs.lab[tc + o]!, hv⟩)
    (hguide : Uniform { g := rowsOf G } tcLevel (level + 1)
      (childSt { g := rowsOf G } level rs tc rs.lab[tc + oGuide]!) targets key) :
    Uniform { g := rowsOf G } tcLevel level rs (tc :: targets) ⟨rs.longcode :: key.codes, key.rows⟩ := by
  apply Uniform.node hok hcell hne htarget
  intro o ho targets' key' hleaf
  obtain ⟨hv, horbit⟩ := horbits o ho
  exact hguide targets' key' (hleaf.orbit hok hlvl hpath hlab hptn hbase hcell hne ho hoGuide
    (rfl : rs.lab[tc + o]! = (⟨rs.lab[tc + o]!, hv⟩ : Fin n).val) hatGuide horbit.symm)

end Hex.GraphIso.Nauty.Generation

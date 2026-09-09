/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Generation.Coverage
public import HexGraphIso.Nauty.Generation.Match
import all HexGraphIso.Nauty.Invariant.Store
import all HexGraphIso.Nauty.Invariant.Domination

public import HexGraphIso.Nauty.Invariant.Domination

public import HexGraphIso.Nauty.Invariant.Carrier

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

/-- A reference occurrence agrees with the stored first-leaf comparison
at this level, including every target hint and the terminal row array. -/
structure Matches (ctx : Ctx n) (level : Nat) (st : Search n)
    (targets : List Nat) (key : Key n) : Prop where
  codes : ∀ i, i < key.codes.length → key.codes[i]! = st.firstcode[level + i]!
  targets : ∀ i, i < targets.length → Int.ofNat targets[i]! = st.firsttc[level + i]!
  rows : key.rows = leafRows ctx st.firstlab

namespace Matches

variable {level : Nat} {st : Search n} {targets : List Nat} {key : Key n}

/-- The comparison witness depends only on the stored first reference. -/
theorem stateEq (h : Matches ctx level st targets key) {out : Search n}
    (hcode : out.firstcode = st.firstcode) (htc : out.firsttc = st.firsttc)
    (hlab : out.firstlab = st.firstlab) : Matches ctx level out targets key := by
  constructor
  · simpa only [hcode] using h.codes
  · simpa only [htc] using h.targets
  · simpa only [hlab] using h.rows

/-- Descending one target consumes one code and one target hint. -/
theorem tail {tc code : Nat} (h : Matches ctx level st (tc :: targets)
    ⟨code :: key.codes, key.rows⟩) : Matches ctx (level + 1) st targets key := by
  constructor
  · intro i hi
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.codes (i + 1) (by simp; omega)
  · intro i hi
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.targets (i + 1) (by simp; omega)
  · exact h.rows

/-- Returning from a reference child restores the enclosing code and
hint once the recursive call's unchanged prefix supplies those entries. -/
theorem cons {tc code : Nat} (h : Matches ctx (level + 1) st targets key)
    (hcode : code = st.firstcode[level]!) (htc : Int.ofNat tc = st.firsttc[level]!) :
    Matches ctx level st (tc :: targets) ⟨code :: key.codes, key.rows⟩ := by
  constructor
  · intro i hi
    cases i with
    | zero => simpa using hcode
    | succ i =>
      have hi' : i < key.codes.length := by simpa using hi
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.codes i hi'
  · intro i hi
    cases i with
    | zero => simpa using htc
    | succ i =>
      have hi' : i < targets.length := by simpa using hi
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.targets i hi'
  · exact h.rows

/-- The head of the occurrence justifies advancing the first-reference
comparison in the executable preparation step. -/
theorem prep {tcLevel : Nat} {rs : RefineSt n}
    (h : Matches ctx level st targets key)
    (hleaf : HasLeaf ctx tcLevel level rs targets key)
    (hlevel : st.eqlevFirst = level - 1) :
    (compareCodes level rs.longcode st).eqlevFirst = level := by
  obtain ⟨tail, hhead⟩ := hleaf.head
  have hc := h.codes 0 (by rw [hhead]; simp)
  rw [hhead] at hc
  exact match_prep hlevel (by simpa using hc)

/-- The first target of a nonterminal occurrence justifies the stored
hint, not merely the equality of refinement codes. -/
theorem target {tcLevel tc : Nat} {rest : List Nat} {rs : RefineSt n}
    (h : Matches ctx level st (tc :: rest) key)
    (hleaf : HasLeaf ctx tcLevel level rs (tc :: rest) key)
    (hok : IterOk ctx level rs) (heq : Equitable ctx level rs.lab rs.ptn) :
    Int.ofNat (maketargetcell ctx rs.lab rs.ptn level tcLevel st.firsttc[level]!).1 =
      st.firsttc[level]! := by
  have htc := h.targets 0 (by simp)
  have hspec : tc = specTargetcell ctx rs.lab rs.ptn level tcLevel := by
    rcases hleaf.cases with ⟨_, ht, _⟩ | ⟨tc', _, _, rest', _, _, _, _, _, ht, _, htcs, _⟩
    · cases ht
    · exact (List.cons.inj htcs).1.trans ht
  apply match_target heq hok.ok.labOk hok.ok.labSize hok.ok.ptnSize hok.ok.ptnEnd
  simpa only [List.getElem!_cons_zero, Nat.add_zero, hspec] using htc.symm

/-- A matching reference's complete hinted target record agrees with the
specification, including the vertex set and its size. -/
theorem target_spec {tcLevel tc : Nat} {rest : List Nat} {rs : RefineSt n}
    (h : Matches ctx level st (tc :: rest) key)
    (hleaf : HasLeaf ctx tcLevel level rs (tc :: rest) key)
    (hok : IterOk ctx level rs) (heq : Equitable ctx level rs.lab rs.ptn) :
    maketargetcell ctx rs.lab rs.ptn level tcLevel st.firsttc[level]! =
      specMaketargetcell ctx rs.lab rs.ptn level tcLevel := by
  have htc := h.targets 0 (by simp)
  have hspec : tc = specTargetcell ctx rs.lab rs.ptn level tcLevel := by
    rcases hleaf.cases with ⟨_, ht, _⟩ | ⟨tc', _, _, rest', _, _, _, _, _, ht, _, htcs, _⟩
    · cases ht
    · exact (List.cons.inj htcs).1.trans ht
  have hchoice := h.target hleaf hok heq
  simp only [List.getElem!_cons_zero, Nat.add_zero] at htc
  rw [← htc] at hchoice
  have ht : targetcell ctx rs.lab rs.ptn level tcLevel st.firsttc[level]! =
      specTargetcell ctx rs.lab rs.ptn level tcLevel := by
    have hp := congrArg Int.toNat hchoice
    change targetcell ctx rs.lab rs.ptn level tcLevel (Int.ofNat tc) = tc at hp
    rw [← htc, ← hspec]
    exact hp
  rw [maketargetcell, specMaketargetcell, ht]

/-- At a discrete matching occurrence the terminal sentinel and row
comparison are both exact, even if the canonical incumbent is larger. -/
theorem discrete {tcLevel : Nat} {rs : RefineSt n}
    (h : Matches ctx level st targets key)
    (hleaf : HasLeaf ctx tcLevel level rs targets key)
    (hok : IterOk ctx level rs) (hdisc : ∀ q, q < n → rs.ptn[q]! ≤ level) :
    st.firstcode[level + 1]! = codeSentinel ∧ leafRows ctx st.firstlab = leafRows ctx rs.lab := by
  obtain ⟨_, rfl⟩ := hleaf.discrete hok hdisc
  exact ⟨(h.codes 1 (by simp)).symm, h.rows.symm⟩

end Matches

end Hex.GraphIso.Nauty.Generation

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CodeOrder
public import HexGraphIso.Nauty.Sparse.CanonAutom
public import HexGraphIso.Nauty.Policy.Canon.Verdict
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Native canonical classification chooses the exact maximum of the
incoming incumbent and candidate. The returned codes describe the actual
installed label, including the code overwrite window and row rejection. -/
theorem canonVerdict_max {G : Hex.SparseGraph n} {cs bs : List Nat} {st : State n}
    {l c : Label n} (h : Codes cs bs st) (hlen : cs.length ≤ n)
    (hl : Label.ofArray? n st.lab = some l) (hc : Label.ofArray? n st.canonlab = some c)
    (hR : st.canong.toRows.Prefix (G.relabel c.perm) st.samerows) :
    let out := resolve cs.length (canonVerdict (.ofGraph G) cs.length st)
    ∃ bs' d, Label.ofArray? n out.canonlab = some d ∧
      (⟨bs' ++ [codeSentinel], G.relabel d.perm⟩ : Key n) =
        Key.max ⟨bs ++ [codeSentinel], G.relabel c.perm⟩
          ⟨cs ++ [codeSentinel], G.relabel l.perm⟩ ∧ Settled cs bs' out := by
  rcases h.tri with ⟨hcomp, _, _, _⟩ | ⟨_, _, _, _, _, _, hd⟩
  · have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon 0 := hcomp ▸ h
    by_cases hs : cs.length < st.canonlevel
    · have hout : resolve cs.length (canonVerdict (.ofGraph G) cs.length st) =
          install cs.length 0 { st with compCanon := 1 } := by
        simp [canonVerdict, hcomp, hs, resolve]
      rw [hout]
      refine ⟨cs, l, hl, ?_, .codes (install_codeInv hm (by decide) hlen) (by change (0 : Int) ≤ 0; decide)⟩
      exact (Key.max_eq_right (codes_short hm (by have := h.blen; omega) _ _)).symm
    · have heq : cs.length = bs.length := by
        have := codeInv_tied_le hm
        have := h.blen
        omega
      have hfull := codes_tied hm heq (G.relabel l.perm) (G.relabel c.perm)
      have htest := testcanlab_fst G (G.relabel c.perm)
        (updatecan (.ofGraph G) st.canong.toRows st.canonlab st.samerows) st.lab l hl
        (updatecan_relabel G st.canong.toRows st.canonlab c st.samerows hc hR)
      let updated : State n := { st with
        canong := st.canong.update (.ofGraph G) st.canonlab st.samerows, samerows := n }
      cases hr : graphCmp (G.relabel l.perm) (G.relabel c.perm) with
      | lt =>
        have hout : resolve cs.length (canonVerdict (.ofGraph G) cs.length st) =
            { updated with compCanon := -1 } := by
          simp [canonVerdict, hcomp, hs, resolve, Storage.update, htest, hr, ordInt, updated]
        rw [hout]
        refine ⟨bs, c, hc, ?_, .rows hm (by change (-1 : Int) < 0; decide)⟩
        apply Eq.symm
        apply Key.max_eq_left
        simp only [Key.Le, hfull, hr]
        decide
      | eq =>
        have hout : resolve cs.length (canonVerdict (.ofGraph G) cs.length st) =
            scatter st.canonlab { updated with compCanon := 0 } := by
          simp [canonVerdict, hcomp, hs, resolve, Storage.update, htest, hr, ordInt, updated]
        rw [hout, scatter_eq]
        refine ⟨bs, c, hc, ?_, .codes hm (by change (0 : Int) ≤ 0; decide)⟩
        apply Eq.symm
        apply Key.max_eq_left
        simp only [Key.Le, hfull, hr]
        decide
      | gt =>
        let sr := (testcanlab (.ofGraph G) updated.canong.toRows st.lab).2
        have hout : resolve cs.length (canonVerdict (.ofGraph G) cs.length st) =
            install cs.length sr { updated with compCanon := 1 } := by
          simp [canonVerdict, hcomp, hs, resolve, Storage.update, htest, hr, ordInt, updated, sr]
        rw [hout]
        refine ⟨cs, l, hl, ?_, .codes (install_codeInv hm (by decide) hlen) (by change (0 : Int) ≤ 0; decide)⟩
        exact (Key.max_eq_right (hfull.trans hr)).symm
  · rcases hd with ⟨hcomp, _⟩ | ⟨hcomp, _, _⟩
    · have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon (-1) := hcomp ▸ h
      have hout : resolve cs.length (canonVerdict (.ofGraph G) cs.length st) = st := by
        simp [canonVerdict, hcomp, resolve]
      rw [hout]
      refine ⟨bs, c, hc, ?_, .codes h (by omega)⟩
      apply Eq.symm
      apply Key.max_eq_left
      simp only [Key.Le, codes_less hm [codeSentinel]]
      decide
    · have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon 1 := hcomp ▸ h
      have hout : resolve cs.length (canonVerdict (.ofGraph G) cs.length st) =
          install cs.length 0 st := by
        simp [canonVerdict, hcomp, resolve]
      rw [hout]
      refine ⟨cs, l, hl, ?_, .codes (Codes.install h (by omega) hlen 0) (by change (0 : Int) ≤ 0; decide)⟩
      exact (Key.max_eq_right (codes_greater hm [codeSentinel] _ _)).symm

/-- A candidate bounded by the incumbent cannot have an upward frozen
code verdict, including when first-reference admission skips row scanning. -/
theorem codes_nonpos {G : Hex.SparseGraph n} {cs bs : List Nat} {st : State n}
    {l c : Label n} (h : Codes cs bs st)
    (hle : Key.Le ⟨cs ++ [codeSentinel], G.relabel l.perm⟩
      ⟨bs ++ [codeSentinel], G.relabel c.perm⟩) : st.compCanon ≤ 0 := by
  rcases h.tri with ⟨hc, _⟩ | ⟨_, _, _, _, _, _, hd⟩
  · omega
  · rcases hd with ⟨hc, _⟩ | ⟨hc, _, _⟩
    · omega
    · have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon 1 := hc ▸ h
      simp only [Key.Le, codes_greater hm [codeSentinel]] at hle
      contradiction

/-- The complete native discrete classifier chooses the maximum once the
first-reference branch is bounded by its retained history. -/
theorem classify_max {G : Hex.SparseGraph n} {cs bs : List Nat} {st : State n}
    {l c : Label n} (h : Codes cs bs st) (hlen : cs.length ≤ n)
    (hl : Label.ofArray? n st.lab = some l) (hc : Label.ofArray? n st.canonlab = some c)
    (hR : st.canong.toRows.Prefix (G.relabel c.perm) st.samerows)
    (hfirst : (classify (.ofGraph G) cs.length n st).1 = .autoFirst →
      Key.Le ⟨cs ++ [codeSentinel], G.relabel l.perm⟩
        ⟨bs ++ [codeSentinel], G.relabel c.perm⟩) :
    let out := resolve cs.length (classify (.ofGraph G) cs.length n st)
    ∃ bs' d, Label.ofArray? n out.canonlab = some d ∧
      (⟨bs' ++ [codeSentinel], G.relabel d.perm⟩ : Key n) =
        Key.max ⟨bs ++ [codeSentinel], G.relabel c.perm⟩
          ⟨cs ++ [codeSentinel], G.relabel l.perm⟩ ∧ Settled cs bs' out := by
  rw [classify_eq]
  split
  · rename_i hbad
    have hd : st.eqlevFirst ≠ cs.length ∧ st.compCanon < 0 := by simpa using hbad
    have hcomp : st.compCanon = -1 := by
      rcases h.tri with ⟨he, _⟩ | ⟨_, _, _, _, _, _, he⟩
      · omega
      · rcases he with ⟨he, _⟩ | ⟨he, _, _⟩ <;> omega
    have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon (-1) := hcomp ▸ h
    refine ⟨bs, c, hc, ?_, .codes h (by change st.compCanon ≤ 0; omega)⟩
    apply Eq.symm
    apply Key.max_eq_left
    simp only [Key.Le, codes_less hm [codeSentinel]]
    decide
  · rename_i hbad
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    split
    · rename_i heq
      split
      · rename_i hguard
        have ha : (classify (.ofGraph G) cs.length n st).1 = .autoFirst := by
          rw [classify_eq]
          simp only [hbad, ite_false, bne_self_eq_false, Bool.false_eq_true, heq, ite_true, hguard]
        have hk := hfirst ha
        rw [scatter_eq]
        exact ⟨bs, c, hc, (Key.max_eq_left hk).symm, .codes h (codes_nonpos h hk)⟩
      · have hm : Codes cs bs (scatter st.firstlab st) := by simpa only [scatter_eq] using h
        apply canonVerdict_max hm hlen
        · simpa only [scatter_eq] using hl
        · simpa only [scatter_eq] using hc
        · simpa only [scatter_eq] using hR
    · exact canonVerdict_max h hlen hl hc hR

/-- Shared exit bookkeeping retains the exact native maximum and settled
code state chosen by classification, for every automorphism/return arm. -/
theorem leaf_max {G : Hex.SparseGraph n} {cs bs : List Nat} {st : State n}
    {l c : Label n} (h : Codes cs bs st) (hlen : cs.length ≤ n)
    (hl : Label.ofArray? n st.lab = some l) (hc : Label.ofArray? n st.canonlab = some c)
    (hR : st.canong.toRows.Prefix (G.relabel c.perm) st.samerows)
    (hfirst : (classify (.ofGraph G) cs.length n st).1 = .autoFirst →
      Key.Le ⟨cs ++ [codeSentinel], G.relabel l.perm⟩
        ⟨bs ++ [codeSentinel], G.relabel c.perm⟩) :
    let verdict := classify (.ofGraph G) cs.length n st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    ∃ bs' d, Label.ofArray? n out.canonlab = some d ∧
      (⟨bs' ++ [codeSentinel], G.relabel d.perm⟩ : Key n) =
        Key.max ⟨bs ++ [codeSentinel], G.relabel c.perm⟩
          ⟨cs ++ [codeSentinel], G.relabel l.perm⟩ ∧ Settled cs bs' out := by
  obtain ⟨bs', d, hd, hmax, hm⟩ := classify_max h hlen hl hc hR hfirst
  let verdict := classify (.ofGraph G) cs.length n st
  have he := leafExit_canonical verdict.1 cs.length verdict.2
  have heq := congrArg (fun r => r.2.2.2.2.1) he
  change (leafExit verdict.1 cs.length verdict.2).2.canonlab =
    (resolve cs.length verdict).canonlab at heq
  refine ⟨bs', d, ?_, hmax, hm.canonical he⟩
  change Label.ofArray? n (leafExit verdict.1 cs.length verdict.2).2.canonlab = some d
  rw [heq]
  exact hd

end Hex.GraphIso.Nauty.Sparse

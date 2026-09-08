/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.CodeState
public import HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Invariant.Domination
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

/-- Canonical fields affected by a leaf verdict. Admission and return
bookkeeping preserve this projection. -/
@[expose] def Search.canonical (st : Search n) :=
  (st.canoncode, st.canonlevel, st.eqlevCanon, st.compCanon, st.canonlab,
    st.canong, st.samerows)

private theorem pushAuto_canonical (st : Search n) (pair : VSet n × VSet n) :
    (pushAuto st pair).canonical = st.canonical := by
  unfold pushAuto
  split <;> rfl

private theorem admit_canonical (st : Search n) :
    (admit st).canonical = st.canonical := by
  unfold admit
  simp only [Id.run_pure]
  change (pushAuto _ _).canonical = _
  rw [pushAuto_canonical]
  rfl

private theorem pruneReturn_canonical (level : Nat) (st : Search n) :
    (pruneReturn level st).2.canonical = st.canonical := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run,
    apply_ite (fun r : Exit × Search n => r.2.canonical)]
  split
  · exact pushAuto_canonical _ _
  · rfl

/-- The canonical effect of a classified leaf, independent of its exit. -/
@[expose] def resolve (level : Nat) (r : Leaf × Search n) : Search n :=
  match r.1 with
  | .better sr => install level sr r.2
  | _ => r.2

/-- Only a better verdict changes canonical fields after classification. -/
theorem leafExit_canonical (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).2.canonical = (resolve level (leaf, st)).canonical := by
  unfold leafExit
  cases leaf <;> simp only [resolve, Id.run_pure, apply_ite Id.run,
    apply_ite (fun r : Exit × Search n => r.2.canonical), pruneReturn_canonical,
    admit_canonical]
  all_goals repeat' split
  all_goals first | exact admit_canonical _ | rfl

/-- Canonical-field equality preserves the settled comparison machine. -/
theorem Settled.canonical {cs bs : List Nat} {st out : Search n}
    (h : Settled cs bs st) (he : out.canonical = st.canonical) : Settled cs bs out := by
  exact h.congr (congrArg Prod.fst he)
    (congrArg (fun r => r.2.1) he) (congrArg (fun r => r.2.2.1) he)
    (congrArg (fun r => r.2.2.2.1) he)

/-- Canonical-field equality preserves every ghost incumbent. -/
theorem key_canonical {ctx : Ctx n} {bs : List Nat} {st out : Search n}
    (he : out.canonical = st.canonical) : out.key ctx bs = st.key ctx bs := by
  have hl : out.canonlab = st.canonlab := congrArg (fun r => r.2.2.2.2.1) he
  simp only [Search.key, incKey, hl]

/-- Canonical classification of a code-tied leaf at a shorter depth
installs the candidate, since its sentinel precedes a real incumbent code. -/
theorem canonVerdict_short {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st) (hc : st.compCanon = 0)
    (hshort : cs.length < st.canonlevel) (hlen : cs.length ≤ n) :
    let out := resolve cs.length (canonVerdict ctx cs.length st)
    incKey ctx cs out.canonlab = keyMax (incKey ctx bs st.canonlab)
      (pathLeafKey ctx cs st.lab) ∧ Settled cs cs out := by
  have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon 0 := hc ▸ h
  have hgt := tied_short_keyCmp_gt hm (by have := h.blen; omega)
    (leafRows ctx st.lab) (leafRows ctx st.canonlab)
  have hout : resolve cs.length (canonVerdict ctx cs.length st) =
      install cs.length 0 { st with compCanon := 1 } := by
    simp [canonVerdict, hc, hshort, resolve]
  dsimp only
  rw [hout]
  refine ⟨?_, .codes ?_ (by change (0 : Int) ≤ 0; omega)⟩
  · simp only [incKey, pathLeafKey]
    rw [keyMax_eq_right (keyCmp_gt_iff_lt.mp hgt)]
    rfl
  · exact install_codeInv hm (by decide) hlen

/-- A frozen upward code comparison installs the candidate independently
of its adjacency rows. -/
theorem canonVerdict_greater {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st) (hc : st.compCanon = 1) (hlen : cs.length ≤ n) :
    let out := resolve cs.length (canonVerdict ctx cs.length st)
    incKey ctx cs out.canonlab = keyMax (incKey ctx bs st.canonlab)
      (pathLeafKey ctx cs st.lab) ∧ Settled cs cs out := by
  have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon 1 := hc ▸ h
  have hgt := frozen_gt_keyCmp (ctx := ctx) (lab := st.lab) (canonlab := st.canonlab) hm
  have hout : resolve cs.length (canonVerdict ctx cs.length st) = install cs.length 0 st := by
    simp [canonVerdict, hc, resolve]
  dsimp only
  rw [hout]
  refine ⟨?_, .codes (Codes.install h (by omega) hlen 0)
    (by change (0 : Int) ≤ 0; omega)⟩
  rw [keyMax_eq_right (keyCmp_gt_iff_lt.mp hgt)]
  rfl

/-- A frozen downward code comparison retains the incumbent independently
of its adjacency rows. -/
theorem canonVerdict_less {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st) (hc : st.compCanon = -1) :
    let out := resolve cs.length (canonVerdict ctx cs.length st)
    incKey ctx bs out.canonlab = keyMax (incKey ctx bs st.canonlab)
      (pathLeafKey ctx cs st.lab) ∧ Settled cs bs out := by
  have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon (-1) := hc ▸ h
  have hlt := frozen_lt_keyCmp (ctx := ctx) (lab := st.lab) (canonlab := st.canonlab) hm
  have hout : resolve cs.length (canonVerdict ctx cs.length st) = st := by
    simp [canonVerdict, hc, resolve]
  dsimp only
  rw [hout]
  refine ⟨?_, .codes h (by omega)⟩
  exact (keyMax_eq_left (show keyLe (pathLeafKey ctx cs st.lab)
    (incKey ctx bs st.canonlab) from by rw [keyLe, hlt]; decide)).symm

/-- At equal code paths, the adjacency-row comparison chooses the exact
maximum and leaves a comparison machine that recovery can restore. -/
theorem canonVerdict_rows {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st) (hc : st.compCanon = 0) (hlen : cs.length = bs.length)
    (hcache : CanongInv ctx st.canong st.canonlab st.samerows) :
    let out := resolve cs.length (canonVerdict ctx cs.length st)
    ∃ bs', incKey ctx bs' out.canonlab = keyMax (incKey ctx bs st.canonlab)
      (pathLeafKey ctx cs st.lab) ∧ Settled cs bs' out := by
  have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon 0 := hc ▸ h
  have hge : ¬cs.length < st.canonlevel := by have := h.blen; omega
  have hbound : cs.length ≤ n := by have := h.bbound; omega
  have htest := (leafEvent_faithful (lab := st.lab) hcache).1
  have hfull := tied_full_keyCmp hm hlen (leafRows ctx st.lab) (leafRows ctx st.canonlab)
  let updated : Search n := { st with
    canong := updatecan ctx st.canong st.canonlab st.samerows, samerows := n }
  cases hr : listCmp VSet.rowCmp (leafRows ctx st.lab) (leafRows ctx st.canonlab) with
  | lt =>
    have hout : resolve cs.length (canonVerdict ctx cs.length st) =
        { updated with compCanon := -1 } := by
      simp [canonVerdict, hc, hge, resolve, htest, hr, ordInt, updated]
    dsimp only
    rw [hout]
    refine ⟨bs, ?_, .rows hm (by change (-1 : Int) < 0; decide)⟩
    have hk : keyLe (pathLeafKey ctx cs st.lab) (incKey ctx bs st.canonlab) := by
      simp only [keyLe, incKey, pathLeafKey, hfull, hr]
      decide
    exact (keyMax_eq_left hk).symm
  | eq =>
    have hout : resolve cs.length (canonVerdict ctx cs.length st) =
        scatter st.canonlab { updated with compCanon := 0 } := by
      simp [canonVerdict, hc, hge, resolve, htest, hr, ordInt, updated]
    dsimp only
    rw [hout, scatter_eq]
    refine ⟨bs, ?_, .codes hm (by change (0 : Int) ≤ 0; decide)⟩
    have hk : keyLe (pathLeafKey ctx cs st.lab) (incKey ctx bs st.canonlab) := by
      simp only [keyLe, incKey, pathLeafKey, hfull, hr]
      decide
    exact (keyMax_eq_left hk).symm
  | gt =>
    let sr := (testcanlab ctx updated.canong st.lab).2
    have hout : resolve cs.length (canonVerdict ctx cs.length st) =
        install cs.length sr { updated with compCanon := 1 } := by
      simp [canonVerdict, hc, hge, resolve, htest, hr, ordInt, updated, sr]
    dsimp only
    rw [hout]
    refine ⟨cs, ?_, .codes (install_codeInv hm (by decide) hbound)
      (by change (0 : Int) ≤ 0; decide)⟩
    simp only [incKey, pathLeafKey]
    rw [hr] at hfull
    rw [keyMax_eq_right (keyCmp_gt_iff_lt.mp hfull)]
    rfl

/-- Canonical leaf classification computes the incumbent maximum. The
ghost codes survive the overwrite window and are readable after resolution. -/
theorem canonVerdict_max {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st) (hlen : cs.length ≤ n)
    (hcache : CanongInv ctx st.canong st.canonlab st.samerows) :
    let out := resolve cs.length (canonVerdict ctx cs.length st)
    ∃ bs', incKey ctx bs' out.canonlab = keyMax (incKey ctx bs st.canonlab)
      (pathLeafKey ctx cs st.lab) ∧ Settled cs bs' out := by
  rcases h.tri with ⟨hc, _, _, _⟩ | ⟨_, _, _, _, _, _, hd⟩
  · by_cases hs : cs.length < st.canonlevel
    · exact ⟨cs, canonVerdict_short h hc hs hlen⟩
    · apply canonVerdict_rows h hc ?_ hcache
      have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon 0 := hc ▸ h
      have := codeInv_tied_le hm
      have := h.blen
      omega
  · rcases hd with ⟨hc, _⟩ | ⟨hc, _, _⟩
    · exact ⟨bs, canonVerdict_less h hc⟩
    · exact ⟨cs, canonVerdict_greater h hc hlen⟩

/-- A leaf bounded by the incumbent cannot have an upward frozen code
verdict. This also applies to a first-reference automorphism return. -/
theorem Codes.nonpos {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st)
    (hle : keyLe (pathLeafKey ctx cs st.lab) (incKey ctx bs st.canonlab)) :
    st.compCanon ≤ 0 := by
  rcases h.tri with ⟨hc, _⟩ | ⟨_, _, _, _, _, _, hd⟩
  · omega
  · rcases hd with ⟨hc, _⟩ | ⟨hc, _, _⟩
    · omega
    · have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon 1 := hc ▸ h
      exact (hle (frozen_gt_keyCmp hm)).elim

/-- All discrete classifications choose the incumbent maximum, provided
a first-reference return is covered by its saved reference. -/
theorem classify_max {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st) (hlen : cs.length ≤ n)
    (hcache : CanongInv ctx st.canong st.canonlab st.samerows)
    (hfirst : (classify ctx cs.length n st).1 = .autoFirst →
      keyLe (pathLeafKey ctx cs st.lab) (incKey ctx bs st.canonlab)) :
    let out := resolve cs.length (classify ctx cs.length n st)
    ∃ bs', incKey ctx bs' out.canonlab = keyMax (incKey ctx bs st.canonlab)
      (pathLeafKey ctx cs st.lab) ∧ Settled cs bs' out := by
  rw [classify_eq]
  split
  · rename_i hbad
    have hd : st.eqlevFirst ≠ cs.length ∧ st.compCanon < 0 := by simpa using hbad
    have hn := hd.2
    have hc : st.compCanon = -1 := by
      rcases h.tri with ⟨hc, _⟩ | ⟨_, _, _, _, _, _, hd⟩
      · omega
      · rcases hd with ⟨hc, _⟩ | ⟨hc, _, _⟩ <;> omega
    have hk : keyLe (pathLeafKey ctx cs st.lab) (incKey ctx bs st.canonlab) := by
      have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon (-1) := hc ▸ h
      rw [keyLe, frozen_lt_keyCmp hm]
      decide
    exact ⟨bs, (keyMax_eq_left hk).symm, .codes h (by change st.compCanon ≤ 0; omega)⟩
  · rename_i hbad
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    split
    · rename_i heq
      split
      · rename_i hguard
        have hleaf : (classify ctx cs.length n st).1 = .autoFirst := by
          rw [classify_eq]
          simp only [hbad, ite_false, bne_self_eq_false, Bool.false_eq_true, heq, ite_true, hguard]
        have hk := hfirst hleaf
        have hn := Codes.nonpos h hk
        rw [scatter_eq]
        exact ⟨bs, (keyMax_eq_left hk).symm, .codes h hn⟩
      · have hm : Codes cs bs (scatter st.firstlab st) := by simpa only [scatter_eq] using h
        have hg : CanongInv ctx (scatter st.firstlab st).canong
            (scatter st.firstlab st).canonlab (scatter st.firstlab st).samerows := by
          simpa only [scatter_eq] using hcache
        simpa only [scatter_eq] using canonVerdict_max hm hlen hg
    · exact canonVerdict_max h hlen hcache

private theorem max_codes_ne {ctx : Ctx n} {cs bs bs' : List Nat}
    {lab canonlab outlab : Array Nat} (hcs : cs ≠ []) (hbs : bs ≠ [])
    (hmax : incKey ctx bs' outlab = keyMax (incKey ctx bs canonlab)
      (pathLeafKey ctx cs lab)) : bs' ≠ [] := by
  intro he
  subst bs'
  rcases keyMax_mem (incKey ctx bs canonlab) (pathLeafKey ctx cs lab) with hk | hk
  · rw [hk] at hmax
    have hl := congrArg (fun key : Key n => key.codes.length) hmax
    simp only [incKey, List.length_append, List.length_singleton, List.length_nil] at hl
    exact hbs (List.length_eq_zero_iff.mp (by omega))
  · rw [hk] at hmax
    have hl := congrArg (fun key : Key n => key.codes.length) hmax
    simp only [incKey, pathLeafKey, List.length_append, List.length_singleton, List.length_nil] at hl
    exact hcs (List.length_eq_zero_iff.mp (by omega))

/-- The actual leaf action installs the optional incumbent maximum and
returns its ghost codes with a recoverable comparison machine. -/
theorem leaf_max {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st) (hlen : cs.length ≤ n) (hcs : cs ≠ []) (hbs : bs ≠ [])
    (hcache : CanongInv ctx st.canong st.canonlab st.samerows)
    (hfirst : (classify ctx cs.length n st).1 = .autoFirst →
      keyLe (pathLeafKey ctx cs st.lab) (incKey ctx bs st.canonlab)) :
    let verdict := classify ctx cs.length n st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    ∃ bs', Settled cs bs' out ∧ out.key ctx bs' =
      some (incMax (st.key ctx bs) (pathLeafKey ctx cs st.lab)) := by
  obtain ⟨bs', hmax, hm⟩ := classify_max h hlen hcache hfirst
  have hne := max_codes_ne hcs hbs hmax
  let verdict := classify ctx cs.length n st
  let out := (leafExit verdict.1 cs.length verdict.2).2
  have he : out.canonical = (resolve cs.length verdict).canonical :=
    leafExit_canonical verdict.1 cs.length verdict.2
  refine ⟨bs', hm.canonical he, ?_⟩
  change out.key ctx bs' = _
  rw [key_canonical he]
  simp only [Search.key, hne, hbs, ↓reduceIte, incMax]
  exact congrArg some hmax

/-- After a leaf action the executable incumbent is the maximum; the
proof uses ghost codes for the incoming overwrite window. -/
theorem leaf_best {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st) (hlen : cs.length ≤ n) (hcs : cs ≠ []) (hbs : bs ≠ [])
    (hcache : CanongInv ctx st.canong st.canonlab st.samerows)
    (hfirst : (classify ctx cs.length n st).1 = .autoFirst →
      keyLe (pathLeafKey ctx cs st.lab) (incKey ctx bs st.canonlab)) :
    let verdict := classify ctx cs.length n st
    (leafExit verdict.1 cs.length verdict.2).2.best ctx =
      some (incMax (st.key ctx bs) (pathLeafKey ctx cs st.lab)) := by
  obtain ⟨bs', hm, hk⟩ := leaf_max h hlen hcs hbs hcache hfirst
  exact hm.read.trans hk

end Hex.GraphIso.Nauty.Engine

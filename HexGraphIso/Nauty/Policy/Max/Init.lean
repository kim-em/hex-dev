/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Control
public import HexGraphIso.Nauty.Policy.Max.Small
import all HexGraphIso.Nauty.Policy.Max.Small
import all HexGraphIso.Nauty.Policy.Max.Position
import all HexGraphIso.Nauty.Policy.Max.Entry
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.Max.Prepare
import all HexGraphIso.Nauty.Policy.Max.Bound
import all HexGraphIso.Nauty.Policy.Max.Choice
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.First.Entry
import all HexGraphIso.Nauty.Policy.First.Path
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- A node refinement preserves every strictly older ancestor frame. -/
theorem extend_refinement {G : Colored n k} {t level nc mc : Nat} {base st out : Search n}
    (ht : 1 ≤ t) (htl : t < level) (hb : SearchOk G t nc base)
    (hs : SearchOk G level mc st) (he : SearchOut G t t base st)
    (ho : SearchOut G (level - 1) level st out) :
    SearchOut G t t base out := by
  have hn0 : 0 < n := by have := hb.bc; have := bcount_le base.ptn t n; omega
  have hp : ∀ lab, lab.size = st.lab.size → cellsPerm st.ptn level st.lab lab →
      cellsPerm base.ptn t st.lab lab := by
    intro lab hsize hperm
    exact cellsPerm_coarsen he.ptnSize.symm
      (hs.labSize.trans hs.ptnSize.symm)
      (hsize.trans (hs.labSize.trans hs.ptnSize.symm)) hperm
      (searchOk_end hn0 hs (by omega)) (searchOk_end hn0 hb ht)
      (fun q hq => by rw [he.low q (Or.inl hq)]; omega)
  refine ⟨ho.labSize.trans he.labSize, ho.ptnSize.trans he.ptnSize, ho.reach,
    ?_, cellsPerm_trans he.perm (hp _ ho.labSize ho.perm), ?_, ?_, ?_⟩
  · intro q hq
    rcases hq with hq | hq
    · have hh := he.low q (Or.inl hq)
      rw [ho.low q (Or.inl (by omega)), hh]
    · have hh := ho.low q (Or.inr (by omega))
      rw [hh, he.low q (Or.inr (by omega))]
  · rcases ho.firstStore with hf | ⟨hs, hf⟩
    · rw [hf]; exact he.firstStore
    · exact Or.inr ⟨hs.trans he.labSize, cellsPerm_trans he.perm (hp _ hs hf)⟩
  · rcases ho.canonStore with hc | ⟨hs, hc⟩
    · rw [hc]; exact he.canonStore
    · exact Or.inr ⟨hs.trans he.labSize, cellsPerm_trans he.perm (hp _ hs hc)⟩
  · rcases ho.canon with hc | hc
    · rw [hc]; exact he.canon
    · exact Or.inr hc

/-- Ancestor chosen vertices are singletons at the actual node entry. -/
theorem NodeInput.singletons {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents)
    {t : Nat} {p : Parent n} (hp : parents t = some p) :
    IsCell f.entry.ptn f.level (p.loop.prepare ctx tcLevel).2.1.toNat 1 := by
  obtain ⟨ht, htl, hpl, hv⟩ := h.scope.valid t p hp
  have hs := (p.picked hv).1
  by_cases he : t + 1 = f.level
  · obtain ⟨q, hq, hchild⟩ := h.parent (by omega)
    rw [show f.level - 1 = t by omega, hp] at hq
    cases hq
    rwa [hchild] at hs
  · obtain ⟨q, hq⟩ := h.scope.complete (t + 1) (by omega) (by omega)
    obtain ⟨_, _, hql, hqv⟩ := h.scope.valid (t + 1) q hq
    obtain ⟨prev, hprev, hchild⟩ := h.scope.chain (t + 1) q hq (by omega)
    simp only [Nat.add_sub_cancel, hp, Option.some.injEq] at hprev
    subst prev
    rw [hchild] at hs
    have hh := q.singleton hqv hs
    rw [hql] at hh
    exact isCell_one_mono (isCell_of_low (h.scope.effect (t + 1) q hq).low hh) (by omega)

/-- Preparing a node preserves every saved ancestor and extends the
actual code prefix consumed by its child sweep. -/
theorem NodeInput.prepare_scope {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents) :
    let l : Loop n := ⟨f, first⟩
    let out := (l.prepare ctx tcLevel).2.2.2.2
    Scope G ctx tcLevel f.level (l.codes ctx) bs out parents := by
  intro l out
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  let R := reachPolicy G ctx tcLevel hn0
  let v := visit ctx f.level f.numcells f.entry
  let c := if first then recordFirst f.level v.2.1 v.2.2 else compareCodes f.level v.2.1 v.2.2
  have hv := R.visit f.level f.numcells f.entry h.frame.positive h.frame.partition
  have hc : Generic.Local G (fun st => st) f.level v.1 v.2.2 c := by
    dsimp only [c]
    split
    · exact R.record _ _ _ _ hv.1
    · exact R.compare _ _ _ _ hv.1
  have ht := R.target first f.level v.1 c h.frame.positive hc.ok
  have hh := R.cheap first f.level _ _ ht.1.ok
  have ho : SearchOut G (f.level - 1) f.level f.entry out :=
    hv.2 _ (hc.effect.trans (ht.1.effect.trans hh.effect))
  have hfirst : out.firstlab = f.entry.firstlab := by
    dsimp only [out, Loop.prepare, l]
    simp only [cheapCheck, apply_ite Search.firstlab, ite_self]
    rw [(chooseTarget_frame ..).2.2.1]
    split
    · rfl
    · exact (compareCodes_frame ..).2.2.1
  have hcanon : out.canonlab = f.entry.canonlab := by
    dsimp only [out, Loop.prepare, l]
    simp only [cheapCheck, apply_ite Search.canonlab, ite_self]
    rw [(chooseTarget_frame ..).2.2.2]
    split
    · rfl
    · exact (compareCodes_frame ..).2.2.2
  have htrace : out.genTrace = f.entry.genTrace := by
    dsimp only [out, Loop.prepare, l]
    simp only [cheapCheck, apply_ite Search.genTrace, ite_self]
    cases first
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [chooseTarget_fields]
      unfold compareCodes
      simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.genTrace, ite_self]
      rfl
    · simp only [↓reduceIte]
      rw [chooseFirst_fields]; rfl
  have hbound : out.noncheaplevel = f.entry.noncheaplevel ∨ f.level ≤ out.noncheaplevel := by
    dsimp only [out, Loop.prepare, l]
    cases first
    all_goals simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals unfold cheapCheck
    all_goals split
    all_goals first
      | exact Or.inr (Nat.le_succ _)
      | left; rw [chooseTarget_fields, compare_noncheap]; rfl
      | left; rw [chooseFirst_fields]; rfl
  refine ⟨h.scope.complete, h.scope.valid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.scope.chain⟩
  · intro t p hp
    exact (h.scope.codes t p hp).trans (List.prefix_append _ _)
  · intro t p hp hcode
    have ht := (h.scope.valid t p hp).2.1
    by_cases hi : t < f.codes.length
    · rw [show l.codes ctx = f.codes ++ [f.code ctx] from rfl, getElem!_append_left hi]
      exact h.scope.code t p hp hi
    · have he : t = f.level - 1 := by have := h.frame.length; omega
      obtain ⟨q, hq, hchild⟩ := h.parent (by have := (h.scope.valid t p hp).1; omega)
      rw [← he, hp] at hq
      cases hq
      rw [hchild]
      change f.code ctx = (f.codes ++ [f.code ctx])[t]!
      rw [show t = f.codes.length by have := h.frame.length; omega, getElem!_append_right (Nat.le_refl _)]
      all_goals simp only [Nat.sub_self, List.getElem!_cons_zero, List.length_singleton, Nat.zero_lt_one]
  · intro t p hp
    rw [l.prepare_key]
    exact h.scope.grows t p hp
  · intro t p hp
    obtain ⟨ht, htl, hpl, hpv⟩ := h.scope.valid t p hp
    have hok := hpv.partition
    rw [hpl] at hok
    exact extend_refinement ht htl hok h.frame.partition (h.scope.effect t p hp) ho
  · intro t p hp
    exact (ho.atSingleton (h.singletons hp)).trans (h.scope.chosen t p hp)
  · intro t p hp ht
    have he : out.gcaCanon = f.entry.gcaCanon := (l.ancestors ctx tcLevel).2
    rw [he] at ht ⊢
    rw [hcanon]
    exact h.scope.canonical t p hp ht
  · intro t p hp ht
    have he : out.gcaFirst = f.entry.gcaFirst := (l.ancestors ctx tcLevel).1
    rw [he] at ht ⊢
    rw [hfirst]
    exact h.scope.first t p hp ht
  · intro t p hp
    rcases hbound with he | he
    · rw [he]; exact h.scope.boundary t p hp
    · have ht := (h.scope.valid t p hp).2.1; exact Or.inr (by omega)
  · intro t p hp hf γ hγ
    rw [htrace] at hγ
    exact h.scope.generators t p hp hf γ hγ
  · intro t p hp hc ht
    change 0 < (l.prepare ctx tcLevel).2.2.2.2.canonlevel at hc
    change (l.prepare ctx tcLevel).2.2.2.2.gcaFirst = t at ht
    rw [l.canonlevel] at hc
    rw [(l.ancestors ctx tcLevel).1] at ht
    have hh := h.scope.coset t p hp hc ht
    exact ⟨hh.1, (l.coset ctx tcLevel).trans hh.2⟩

/-- The initialized sweep inherits the node's installed-reference counters. -/
theorem NodeInput.prepare_counters {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents) :
    let l : Loop n := ⟨f, first⟩
    let st := (l.prepare ctx tcLevel).2.2.2.2
    0 < st.canonlevel → 0 < st.gcaFirst ∧ st.gcaFirst ≤ st.gcaCanon := by
  intro l st hc
  change 0 < (l.prepare ctx tcLevel).2.2.2.2.canonlevel at hc
  rw [l.canonlevel] at hc
  have he := l.ancestors ctx tcLevel
  change 0 < (l.prepare ctx tcLevel).2.2.2.2.gcaFirst ∧
    (l.prepare ctx tcLevel).2.2.2.2.gcaFirst ≤ (l.prepare ctx tcLevel).2.2.2.2.gcaCanon
  rw [he.1, he.2]
  exact h.counters hc

/-- The first internal node selects the whole actual nontrivial cell. -/
theorem Loop.first_shape {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat} {l : Loop n}
    (h : l.node.Valid G) (hf : l.first = true) (hnc : (l.prepare ctx tcLevel).1 < n) :
    let p := l.prepare ctx tcLevel
    IsCell p.2.2.2.2.ptn l.node.level p.2.1.toNat p.2.2.2.1 ∧
      2 ≤ p.2.2.2.1 ∧ p.2.1.toNat + p.2.2.2.1 ≤ n ∧
      p.2.2.1 = windowSet n p.2.2.2.2.lab p.2.1.toNat p.2.2.2.1 := by
  let v := visit ctx l.node.level l.node.numcells l.node.entry
  let c := recordFirst l.node.level v.2.1 v.2.2
  have hn0 : 0 < n := by have := h.positive; have := h.depth; omega
  have hv := (reachPolicy G ctx tcLevel hn0).visit _ _ _ h.positive h.partition |>.1
  have hc := (reachPolicy G ctx tcLevel hn0).record l.node.level v.2.1 v.1 v.2.2 hv |>.ok
  have hlt : bcount c.ptn l.node.level n < n := by
    have hh : v.1 = bcount c.ptn l.node.level n := hc.count
    have hh' : v.1 < n := hnc
    omega
  obtain ⟨tc, len, hm, hcell, hlen, hr⟩ := maketargetcell_open (ctx := ctx) (lab := c.lab)
    (tcLevel := tcLevel) (hint := -1) h.positive hc.ptnSize (searchOk_end hn0 hc h.positive) hlt
  change maketargetcell ctx c.lab c.ptn l.node.level tcLevel (-1) =
    (tc, worksetOf n c.lab tc (tc + len - 1), len) at hm
  have hne : v.1 ≠ n := Nat.ne_of_lt hnc
  have hprep : l.prepare ctx tcLevel =
      (v.1, Int.ofNat tc, worksetOf n c.lab tc (tc + len - 1), len,
        cheapCheck true l.node.level { c with
          firsttc := c.firsttc.set! l.node.level (Int.ofNat tc)
          tctotal := c.tctotal + len }) := by
    dsimp only [Loop.prepare]
    simp only [hf, ↓reduceIte]
    change (v.1, (chooseTarget true ctx tcLevel l.node.level v.1 c).1,
      (chooseTarget true ctx tcLevel l.node.level v.1 c).2.1,
      (chooseTarget true ctx tcLevel l.node.level v.1 c).2.2.1,
      cheapCheck true l.node.level (chooseTarget true ctx tcLevel l.node.level v.1 c).2.2.2) = _
    simp only [chooseTarget, bne_iff_ne.mpr hne, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, hm, Id.run_pure]
  rw [hprep]
  simp only [cheapCheck, apply_ite Search.lab, apply_ite Search.ptn, ite_self]
  refine ⟨hcell, hlen, hr, ?_⟩
  apply VSet.ext
  intro v
  apply Bool.eq_iff_iff.mpr
  rw [mem_worksetOf_iff, mem_windowSet]
  simp only [show tc + len - 1 + 1 - tc = len by omega ]
  rfl

/-- The first internal node initializes the complete sweep contract at
its actual prepared state, before any child has been covered. -/
theorem NodeInput.first_input {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel (fuel + 1) true f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hnc : (Generic.prepareFirst ctx tcLevel f.level f.numcells f.entry).1 ≠ n) :
    let l : Loop n := ⟨f, true⟩
    let p := l.prepare ctx tcLevel
    SweepInput G ctx tcLevel fuel (n + 1) true f.level p.1 p.2.1.toNat
      ((p.2.2.1.nextElem none).getD 0) (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2
      l bs fs parents := by
  intro l p
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hok := l.prepare_ok (ctx := ctx) (tcLevel := tcLevel) h.frame
  have hlt : p.1 < n := by
    have hh := hok.count
    have hb := bcount_le p.2.2.2.2.ptn f.level n
    change p.1 = bcount p.2.2.2.2.ptn f.level n at hh
    have he : p.1 ≠ n := hnc
    omega
  obtain ⟨hcell, hlen, hr, hset⟩ := l.first_shape h.frame rfl hlt
  have hpre := h.entry.1
  have hsmall := h.small hgsz hsymm hloop (by intro hf; cases hf)
  have href := h.references
  change p.2.2.2.2.gcaFirst < f.level ∧ _ at href
  have htrace : p.2.2.2.2.genTrace = #[] := by
    have he := l.first_prepare (ctx := ctx) (tcLevel := tcLevel) rfl
    change (l.prepare ctx tcLevel).2.2.2.2.genTrace = #[]
    rw [he]
    dsimp only
    unfold cheapCheck
    split <;> exact (prepareFirst_stores ctx tcLevel f.level f.numcells f.entry).2.2.2.2.trans h.entry.2.2.2.2.1
  have heq : Equitable ctx f.level p.2.2.2.2.lab p.2.2.2.2.ptn := by
    obtain ⟨_, hl, hp⟩ := l.prepare_frame ctx tcLevel
    rw [hl, hp]
    exact hpre.equitable
  have hpath : PathInv G ctx f.level p.2.2.2.2 := by
    have he := l.first_prepare (ctx := ctx) (tcLevel := tcLevel) rfl
    change PathInv G ctx f.level (l.prepare ctx tcLevel).2.2.2.2
    rw [he]
    exact (hpre.prepare_path hn0 hgsz tcLevel).cheap true
  refine ⟨h.frame, rfl, rfl, rfl, rfl, rfl, ⟨bs, fs, h.entry⟩, hok, hok,
    SearchOut.refl G _ _ hok.reach, heq, ?_, hcell, hlen, hr, ?_,
    (fun _ hv => VSet.nextElem_mem hv), (by have := h.fuel; omega),
    (by intro v hv; omega), hpath, l.choice_prepared h.frame h.entry hlt,
    hsmall, Or.inl ⟨rfl, h.entry.2.1, h.entry.2.2.1, rfl, rfl, rfl, rfl⟩,
    ?_, href.2, (fun ht => by have hh := href.1; omega), ?_, h.prepare_scope, h.parent, h.prepare_counters, ?_⟩
  · refine ⟨p.2.2.2.1, fun _ => ⟨hcell, hlen, hr⟩, ?_⟩
    intro v hv
    rw [hset] at hv
    exact (mem_windowSet.mp hv).2
  · intro v hv
    rwa [← hset]
  · intro v hv
    right
    refine ⟨v, ?_, rfl, Nat.le_refl _⟩
    have hm : p.2.2.1.mem v = true := by rwa [hset]
    refine ⟨hm, ?_⟩
    cases he : p.2.2.1.nextElem none with
    | none =>
      have hh := VSet.nextElem_none he v (Nat.zero_le _)
      rw [hm] at hh; cases hh
    | some w =>
      refine ⟨w, rfl, ?_⟩
      by_cases hle : w ≤ v
      · exact hle
      · have hh := (VSet.nextElem_some he).2.2 v (Nat.zero_le _) (by omega)
        rw [hm] at hh; cases hh
  · intro _ γ hγ
    simp only [htrace, Array.not_mem_empty] at hγ
  · intro hc
    change 0 < (l.prepare ctx tcLevel).2.2.2.2.canonlevel at hc
    rw [l.canonlevel] at hc
    have hz : f.entry.canonlevel = 0 := h.entry.2.2.2.1
    change 0 < f.entry.canonlevel at hc
    omega

/-- An off-path internal classification requires an active target. -/
theorem target_active {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (hnc : numcells < n)
    (hi : (classify ctx level numcells (chooseTarget false ctx tcLevel level numcells st).2.2.2).1 = .internal) :
    st.eqlevFirst = level ∨ 0 ≤ st.compCanon := by
  by_cases ha : st.eqlevFirst = level ∨ 0 ≤ st.compCanon
  · exact ha
  · have hne : st.eqlevFirst ≠ level := fun he => ha (Or.inl he)
    have hneg : st.compCanon < 0 := by
      have hh : ¬ 0 ≤ st.compCanon := fun he => ha (Or.inr he)
      omega
    have ht : (chooseTarget false ctx tcLevel level numcells st).2.2.2 = st := by
      simp only [chooseTarget, Bool.false_eq_true, ↓reduceIte, hnc, decide_true,
        beq_eq_false_iff_ne.mpr hne, Bool.false_or, decide_eq_false (by omega : ¬ 0 ≤ st.compCanon),
        Bool.true_and, Id.run_pure]
    rw [ht] at hi
    exact ((classify_internal ctx level numcells st).mp hi).1 ⟨hne, hneg⟩ |>.elim

/-- The off-path internal node selects a complete target window, including
the hinted target used while harvesting generators in a dominated tree. -/
theorem Loop.other_shape {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat} {l : Loop n}
    (h : l.node.Valid G) (hf : l.first = false) (hnc : (l.prepare ctx tcLevel).1 < n)
    (hi : let p := prepareOther ctx tcLevel l.node.level l.node.numcells l.node.entry
      (classify ctx l.node.level p.1 p.2.2.2.2.2).1 = .internal) :
    let p := l.prepare ctx tcLevel
    IsCell p.2.2.2.2.ptn l.node.level p.2.1.toNat p.2.2.2.1 ∧
      2 ≤ p.2.2.2.1 ∧ p.2.1.toNat + p.2.2.2.1 ≤ n ∧
      p.2.2.1 = windowSet n p.2.2.2.2.lab p.2.1.toNat p.2.2.2.1 := by
  let v := visit ctx l.node.level l.node.numcells l.node.entry
  let c := compareCodes l.node.level v.2.1 v.2.2
  have hn0 : 0 < n := by have := h.positive; have := h.depth; omega
  have hv := (reachPolicy G ctx tcLevel hn0).visit _ _ _ h.positive h.partition |>.1
  have hc := (reachPolicy G ctx tcLevel hn0).compare l.node.level v.2.1 v.1 v.2.2 hv |>.ok
  have hlt : bcount c.ptn l.node.level n < n := by
    have hh : v.1 = bcount c.ptn l.node.level n := hc.count
    have hh' : v.1 < n := hnc
    omega
  have ha := target_active (show v.1 < n from hnc) hi
  have hactive : (v.1 < n && (c.eqlevFirst == l.node.level || c.compCanon >= 0)) = true := by
    simp only [show v.1 < n from hnc, decide_true, Bool.true_and, Bool.or_eq_true,
      beq_iff_eq, decide_eq_true_eq]
    exact ha
  let hint : Int := if c.compCanon < 0 then c.firsttc[l.node.level]! else -1
  obtain ⟨tc, len, hm, hcell, hlen, hr⟩ := maketargetcell_open (ctx := ctx) (lab := c.lab)
    (tcLevel := tcLevel) (hint := hint) h.positive hc.ptnSize (searchOk_end hn0 hc h.positive) hlt
  change maketargetcell ctx c.lab c.ptn l.node.level tcLevel hint =
    (tc, worksetOf n c.lab tc (tc + len - 1), len) at hm
  have hprep : (l.prepare ctx tcLevel).2.1 = Int.ofNat tc ∧
      (l.prepare ctx tcLevel).2.2.1 = worksetOf n c.lab tc (tc + len - 1) ∧
      (l.prepare ctx tcLevel).2.2.2.1 = len := by
    dsimp only [Loop.prepare]
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    change (chooseTarget false ctx tcLevel l.node.level v.1 c).1 = _ ∧
      (chooseTarget false ctx tcLevel l.node.level v.1 c).2.1 = _ ∧
      (chooseTarget false ctx tcLevel l.node.level v.1 c).2.2.1 = _
    simp only [chooseTarget, Bool.false_eq_true, ↓reduceIte, hactive, Bool.not_false,
      Bool.true_and, decide_eq_true_eq,
      show (if c.compCanon < 0 then c.firsttc[l.node.level]! else -1) = hint from rfl,
      hm, Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, ite_self]
    repeat' split
    all_goals simp only [and_self]
  have hfields : (l.prepare ctx tcLevel).2.2.2.2.lab = c.lab ∧
      (l.prepare ctx tcLevel).2.2.2.2.ptn = c.ptn := by
    dsimp only [Loop.prepare]
    simp only [hf, Bool.false_eq_true, ↓reduceIte, cheapCheck,
      apply_ite Search.lab, apply_ite Search.ptn, ite_self]
    rw [chooseTarget_fields]
    exact ⟨rfl, rfl⟩
  dsimp only
  rw [hprep.1, hprep.2.1, hprep.2.2, hfields.1, hfields.2]
  refine ⟨hcell, hlen, hr, ?_⟩
  apply VSet.ext
  intro v
  apply Bool.eq_iff_iff.mpr
  rw [mem_worksetOf_iff, mem_windowSet]
  simp only [show tc + len - 1 + 1 - tc = len by omega]
  rfl

/-- An internal off-path node initializes the same complete sweep
contract, allowing the first child to settle a positive comparison. -/
theorem NodeInput.other_input {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel (fuel + 1) false f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hinternal : let p := prepareOther ctx tcLevel f.level f.numcells f.entry
      (classify ctx f.level p.1 p.2.2.2.2.2).1 = .internal) :
    let l : Loop n := ⟨f, false⟩
    let p := l.prepare ctx tcLevel
    SweepInput G ctx tcLevel fuel (n + 1) false f.level p.1 p.2.1.toNat
      ((p.2.2.1.nextElem none).getD 0) (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2
      l bs fs parents := by
  intro l p
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hok := l.prepare_ok (ctx := ctx) (tcLevel := tcLevel) h.frame
  have hlt : p.1 < n := by
    have hh := hok.count
    have hb := bcount_le p.2.2.2.2.ptn f.level n
    change p.1 = bcount p.2.2.2.2.ptn f.level n at hh
    have he : p.1 ≠ n := ((classify_internal ..).mp hinternal).2
    omega
  obtain ⟨hcell, hlen, hr, hset⟩ := l.other_shape h.frame rfl hlt hinternal
  have hp := (h.entry.1.prepare hn0 hgsz hsymm hloop).2.2.2.2 hinternal
  have hphase := h.entry.1.phase hn0 hinternal
  have hcomp := l.comparison h.frame rfl h.entry
  have href := h.references
  change p.2.2.2.2.gcaFirst < f.level ∧ _ at href
  change Nauty.SweepPre G ctx tcLevel false f.level p.1 p.2.1.toNat
    ((p.2.2.1.nextElem none).getD 0) (p.2.2.1.nextElem none) p.2.2.1 p.2.2.2.2 at hp
  refine ⟨h.frame, rfl, rfl, rfl, rfl, rfl, ⟨bs, fs, h.entry⟩, hok, hok,
    SearchOut.refl G _ _ hok.reach, hp.equitable, hp.target, hcell, hlen, hr, ?_,
    hp.cursor_mem, (by have := h.fuel; omega), (by intro v hv; omega), hp.path,
    l.choice_prepared h.frame h.entry hlt, hp.subtree hn0,
    Or.inr ⟨hp, hcomp, ?_⟩, ?_, href.2, (fun ht => by have hh := href.1; omega),
    (by intro hf; cases hf), h.prepare_scope, h.parent, h.prepare_counters, ?_⟩
  · intro v hv
    rwa [← hset]
  · rcases hphase with hc | hc
    · left
      dsimp only [p, Loop.prepare, l]
      simp only [Bool.false_eq_true, ↓reduceIte, cheapCheck,
        apply_ite Search.compCanon, ite_self]
      exact hc
    · exact Or.inr ⟨rfl, hc⟩
  · intro v hv
    right
    refine ⟨v, ?_, rfl, Nat.le_refl _⟩
    have hm : p.2.2.1.mem v = true := by rwa [hset]
    refine ⟨hm, ?_⟩
    cases he : p.2.2.1.nextElem none with
    | none =>
      have hh := VSet.nextElem_none he v (Nat.zero_le _)
      rw [hm] at hh; cases hh
    | some w =>
      refine ⟨w, rfl, ?_⟩
      by_cases hle : w ≤ v
      · exact hle
      · have hh := (VSet.nextElem_some he).2.2 v (Nat.zero_le _) (by omega)
        rw [hm] at hh; cases hh
  · intro _
    exact ⟨(by intro hf; cases hf), fun _ => href.1⟩

end Hex.GraphIso.Nauty.Max

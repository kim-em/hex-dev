/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.RouteKey
import all HexGraphIso.Nauty.Policy.RouteKey
import all HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.Target
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

/-! The two reference-code comparisons and the lower bound contributed
by the first leaf. Canonical codes remain semantic values until the
completed leaf verdict restores readable code storage. -/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The first-reference comparison at a current code path. -/
abbrev FirstCodes (cs fs : List Nat) (st : Search n) : Prop :=
  FirstCodeInv n cs fs st.firstcode st.eqlevFirst

/-- Changes outside the code machine preserve its meaning. -/
theorem FirstCodes.congr {cs fs : List Nat} {st out : Search n}
    (h : FirstCodes cs fs st) (hc : out.firstcode = st.firstcode)
    (he : out.eqlevFirst = st.eqlevFirst) : FirstCodes cs fs out := by
  change FirstCodeInv n cs fs _ _
  rwa [hc, he]

/-- Comparing a new refinement code extends the current first-code path. -/
theorem FirstCodes.compare {cs fs : List Nat} {st : Search n} {code : Nat}
    (h : FirstCodes cs fs st) (hc : code < codeSentinel) :
    FirstCodes (cs ++ [code]) fs (compareCodes (cs.length + 1) code st) := by
  have hm := compareCodes_firstCodeInv (st := st) h hc

  exact hm

/-- Target selection can lower first-path agreement without changing its codes. -/
theorem FirstCodes.target {ctx : Ctx n} {cs fs : List Nat} {st : Search n}
    (h : FirstCodes cs fs st) (tcLevel numcells : Nat) :
    FirstCodes cs fs (chooseTarget false ctx tcLevel cs.length numcells st).2.2.2 := by
  have hc := congrArg Prod.fst ((referencePolicy ctx 0 tcLevel).target cs.length numcells st)
  change (chooseTarget false ctx tcLevel cs.length numcells st).2.2.2.firstcode = st.firstcode at hc
  change FirstCodeInv n cs fs _ _
  rw [hc]
  exact firstCodeInv_mono h (chooseTarget_le ctx tcLevel cs.length numcells st)

/-- Classification preserves the first-reference code comparison. -/
theorem FirstCodes.classify {ctx : Ctx n} {cs fs : List Nat} {st : Search n}
    (h : FirstCodes cs fs st) (numcells : Nat) :
    FirstCodes cs fs (Nauty.classify ctx cs.length numcells st).2 :=
  h.congr (congrArg Prod.fst (classify_reference ctx cs.length numcells st))
    (classify_eqlev ctx cs.length numcells st)

/-- Leaf actions preserve the first-reference code comparison. -/
theorem FirstCodes.leaf {cs fs : List Nat} {st : Search n}
    (h : FirstCodes cs fs st) (leaf : Leaf) :
    FirstCodes cs fs (leafExit leaf cs.length st).2 :=
  h.congr (congrArg Prod.fst (leafExit_reference leaf cs.length st))
    (leafExit_eqlev leaf cs.length st)

/-- Recovery truncates the current path at the receiving ancestor. -/
theorem FirstCodes.recover {cs fs : List Nat} {st : Search n} {level : Nat}
    (h : FirstCodes cs fs st) (hlen : level ≤ cs.length) (inf : Nat) :
    FirstCodes (cs.take level) fs (Nauty.recover inf level st) := by
  exact recover_firstCodeInv (st := st) (inf := inf) h hlen

/-- The two comparisons and the saved first leaf's incumbent bound. -/
structure Comparison (ctx : Ctx n) (cs bs fs : List Nat) (st : Search n) : Prop where
  /-- Canonical-code comparison, with semantic codes during overwriting. -/
  canonical : Codes cs bs st
  /-- Agreement with the first reference's code path. -/
  first : FirstCodes cs fs st
  /-- An incumbent has already been installed. -/
  nonempty : bs ≠ []
  /-- The incumbent bounds the first leaf. -/
  lower : keyLe (incKey ctx fs st.firstlab) (incKey ctx bs st.canonlab)

/-- Changes outside both comparisons and both saved labels preserve their bounds. -/
theorem Comparison.congr {ctx : Ctx n} {cs bs fs : List Nat} {st out : Search n}
    (h : Comparison ctx cs bs fs st)
    (hcc : out.canoncode = st.canoncode) (hcl : out.canonlevel = st.canonlevel)
    (hce : out.eqlevCanon = st.eqlevCanon) (hcmp : out.compCanon = st.compCanon)
    (hfc : out.firstcode = st.firstcode) (hfe : out.eqlevFirst = st.eqlevFirst)
    (hfl : out.firstlab = st.firstlab) (hcan : out.canonlab = st.canonlab) :
    Comparison ctx cs bs fs out := by
  refine ⟨?_, h.first.congr hfc hfe, h.nonempty, ?_⟩
  · change CodeCmpInv n cs bs _ _ _ _
    rw [hcc, hcl, hce, hcmp]
    exact h.canonical
  · rw [hfl, hcan]
    exact h.lower

/-- Refinement changes neither saved reference nor either comparison machine. -/
theorem Comparison.visit {ctx : Ctx n} {cs bs fs : List Nat} {st : Search n}
    (h : Comparison ctx cs bs fs st) (level numcells : Nat) :
    Comparison ctx cs bs fs (Nauty.visit ctx level numcells st).2.2 :=
  h.congr rfl rfl rfl rfl rfl rfl rfl rfl

/-- The next refinement code advances both comparison machines. -/
theorem Comparison.compare {ctx : Ctx n} {cs bs fs : List Nat} {st : Search n} {code : Nat}
    (h : Comparison ctx cs bs fs st) (hc : code < codeSentinel) (hlen : cs.length ≤ n) :
    Comparison ctx (cs ++ [code]) bs fs (compareCodes (cs.length + 1) code st) := by
  refine ⟨h.canonical.compare hc hlen, h.first.compare hc, h.nonempty, ?_⟩
  obtain ⟨_, _, hf, hcan⟩ := compareCodes_frame (cs.length + 1) code st
  rw [hf, hcan]
  exact h.lower

/-- Choosing the sweep target retains the canonical comparison and its lower bound. -/
theorem Comparison.target {ctx : Ctx n} {cs bs fs : List Nat} {st : Search n}
    (h : Comparison ctx cs bs fs st) (tcLevel numcells : Nat) :
    Comparison ctx cs bs fs (chooseTarget false ctx tcLevel cs.length numcells st).2.2.2 := by
  refine ⟨?_, h.first.target tcLevel numcells, h.nonempty, ?_⟩
  · rw [chooseTarget_fields]
    exact h.canonical
  · rw [chooseTarget_fields]
    exact h.lower

/-- Individualization changes no saved code or labelling. -/
theorem Comparison.child {ctx : Ctx n} {cs bs fs : List Nat} {st : Search n}
    (h : Comparison ctx cs bs fs st) (first : Bool) (level tc tv : Nat) :
    Comparison ctx cs bs fs (Nauty.child first level tc tv st) := by
  cases first <;> exact h.congr rfl rfl rfl rfl rfl rfl rfl rfl

/-- The cheap guard preserves both comparisons and both references. -/
theorem Comparison.cheap {ctx : Ctx n} {cs bs fs : List Nat} {st : Search n}
    (h : Comparison ctx cs bs fs st) (first : Bool) (level : Nat) :
    Comparison ctx cs bs fs (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h.congr rfl rfl rfl rfl rfl rfl rfl rfl

/-- The first leaf initializes both comparisons and bounds itself. -/
theorem comparison_firstterminal {ctx : Ctx n} {cs : List Nat} {st : Search n}
    (hne : cs ≠ []) (hcsize : st.canoncode.size = n + 2)
    (hfsize : st.firstcode.size = n + 2) (hlen : cs.length ≤ n)
    (hcodes : ∀ i, 1 ≤ i → i ≤ cs.length → st.firstcode[i]! = cs[i - 1]!)
    (hlt : ∀ c ∈ cs, c < codeSentinel) :
    Comparison ctx cs cs cs (firstterminal cs.length st) := by
  refine ⟨firstterminal_codes hcsize hlen hcodes hlt, ?_, hne, keyLe_refl _⟩
  have hm := firstterminal_firstCodeInv (st := st) hfsize hlen hcodes hlt

  exact hm

/-- A resolved leaf keeps both comparisons recoverable, retains the
first-key bound, and installs the exact incumbent maximum. -/
theorem Comparison.leaf {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {cs bs fs : List Nat} {st : Search n}
    (h : Comparison ctx cs bs fs st)
    (hh : History ctx tcLevel cs.length cs.length n st)
    (hinv : RunInv G ctx st) (hn0 : 0 < n) (hlevel : 1 ≤ cs.length)
    (hok : SearchOk G cs.length n st) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let verdict := Nauty.classify ctx cs.length n st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    ∃ bs', Settled cs bs' out ∧ FirstCodes cs fs out ∧ bs' ≠ [] ∧
      keyLe (incKey ctx fs out.firstlab) (incKey ctx bs' out.canonlab) ∧
      out.key ctx bs' = some (incMax (st.key ctx bs) (pathLeafKey ctx cs st.lab)) := by
  let verdict := Nauty.classify ctx cs.length n st
  let out := (leafExit verdict.1 cs.length verdict.2).2
  obtain ⟨bs', hm, hk⟩ := hh.leaf_max hinv hn0 hlevel hok h.canonical h.first
    h.nonempty h.lower hgsz hsymm hloop
  have hne : bs' ≠ [] := by
    intro he
    simp only [Search.key, he, ↓reduceIte] at hk
    contradiction
  have hf : out.firstlab = st.firstlab := by
    have hr := (leafExit_reference verdict.1 cs.length verdict.2).trans
      (classify_reference ctx cs.length n st)
    exact congrArg (fun r => r.2.2) hr
  have hmax : incKey ctx bs' out.canonlab =
      keyMax (incKey ctx bs st.canonlab) (pathLeafKey ctx cs st.lab) := by
    apply Option.some.inj
    simpa only [Search.key, hne, h.nonempty, ↓reduceIte, incMax] using hk
  refine ⟨bs', hm, (h.first.classify n).leaf verdict.1, hne, ?_, hk⟩
  rw [hf, hmax]
  exact keyLe_trans h.lower (keyLe_iff.mpr (keyMax_not_lt_left _ _))

/-- At any receiving ancestor, a settled leaf restores both comparisons
and their saved-reference bound. -/
theorem comparison_recover {ctx : Ctx n} {cs bs fs : List Nat} {st : Search n}
    (hc : Settled cs bs st) (hf : FirstCodes cs fs st) (hne : bs ≠ [])
    (hlower : keyLe (incKey ctx fs st.firstlab) (incKey ctx bs st.canonlab))
    {level : Nat} (hlen : level ≤ cs.length) (inf : Nat) :
    Comparison ctx (cs.take level) bs fs (Nauty.recover inf level st) := by
  refine ⟨hc.recover hlen inf, hf.recover hlen inf, hne, ?_⟩
  have hfirst := congrArg (fun r => r.2.2) ((referencePolicy ctx inf 0).recover level st)
  have hcanon : (Nauty.recover inf level st).canonlab = st.canonlab := by
    unfold Nauty.recover recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite Search.canonlab, ite_self]
  change (Nauty.recover inf level st).firstlab = st.firstlab at hfirst
  rw [hfirst, hcanon]
  exact hlower

end Hex.GraphIso.Nauty

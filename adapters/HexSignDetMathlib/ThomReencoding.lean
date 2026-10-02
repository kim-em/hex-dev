/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.Thom
public import HexSignDetMathlib.ReencodingRefinement

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret HexRealRootsMathlib

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))

variable [Neg E] [Inv E]
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

include hz h1 ha hs hm hnat hn hi hsign in
/-- Re-encoding succeeds on any valid target polynomial and interval containing
the source root. Tau Ceti Thom injectivity supplies count-one target words;
the original constraints select the source root from the joint table. This
requires neither equality of heads nor containment in the original interval. -/
theorem Descriptor.buildReencoding_success {context : Ctx}
    (source : Descriptor E Ctx sign context) (head : DensePoly E) (a b : Endpoint E)
    (hdom : HexSturmMathlib.Domain f hz head a b)
    (hmem : source.root f hz h1 ha hs hm hnat hsign ∈
      Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f)) :
    ∃ r : Reencoding source head a b,
      source.buildReencoding head a b = .ok (some r) ∧
      r.target.root f hz h1 ha hs hm hnat hsign =
        source.root f hz h1 ha hs hm hnat hsign := by
  let raw : RawDescriptor E Ctx := ⟨context, head, a, b, [], []⟩
  let fullQueries := (raw.full []).queries
  let x := source.root f hz h1 ha hs hm hnat hsign
  let fullWord := signsAt f hz fullQueries x
  let word := fullWord ++ source.raw.constraintSigns
  let targetRaw := raw.full fullWord
  have hsg := HexSturmMathlib.sign_spec f sign hsign
  have hprepared : (Sturm.prepare sign head a b).isSome = true :=
    (HexSturmMathlib.prepare_isSome f hz ha hs hm sign
      (fun a => (hsg a).2.1) (fun a => (hsg a).2.2.1)
      h1 hn hi hnat (fun a => (hsg a).1) head a b).mpr hdom
  cases hd : Sturm.prepare sign head a b with
  | none => simp only [hd, Option.isSome_none, Bool.false_eq_true] at hprepared
  | some domain =>
    have bindings := Sturm.prepare_eq_some sign head a b domain hd
    obtain ⟨t, ht, _⟩ := buildPrepared_roots f hz h1 ha hs hm hnat hn hi sign hsign
      context domain bindings.1 (fullQueries ++ source.raw.constraints) true
    have hc : t.val.check sign context head a b
        (fullQueries ++ source.raw.constraints) = true := by
      simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using t.property
    have hrows : (t.val.node.system.tableRows.toList.filter fun row =>
        decide (row.1.drop fullQueries.length = source.raw.constraintSigns)) = [(word, 1)] :=
      source.reencoding_rows f hz h1 ha hs hm hnat hsign head a b hmem t.val hc
    have hp : 0 < raw.head.natDegree := by
      have hpositive := Finset.card_pos.mpr ⟨x, hmem⟩
      have hbound := Tarski.rootsIn_card_le (interpret f hz head) (a.map f) (b.map f)
      rw [natDegree_interpret] at hbound
      change 0 < head.natDegree
      omega
    have hlen : fullWord.length = raw.head.natDegree := by
      simpa only [fullWord, signsAt, List.length_map, fullQueries] using raw.full_queries_length []
    have hsigns : fullWord.all (fun s => decide (s = -1 ∨ s = 0 ∨ s = 1)) = true := by
      apply List.all_eq_true.mpr
      intro s hs
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hs
      generalize SignType.sign ((interpret f hz q).eval x) = z
      cases z <;> simp
    have hw : targetRaw.wellFormed = true := raw.full_wellFormed fullWord hp hlen hsigns
    have hfiber := raw.full_fiber f hz hm hnat hdom.1
      (Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f))
      (fun z hz => (Polynomial.isRoot_of_mem_roots
        ((Tarski.mem_rootsIn _ _ _ z).mp hz).1).eq_zero) x hmem
    have hone : ((Tarski.rootsIn (interpret f hz targetRaw.head)
        (targetRaw.lower.map f) (targetRaw.upper.map f)).filter
          (fun y => signsAt f hz targetRaw.queries y = targetRaw.signs)).card = 1 := by
      change ((Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f)).filter
        (fun y => signsAt f hz fullQueries y = fullWord)).card = 1
      rw [hfiber, Finset.card_singleton]
    obtain ⟨target, hbuild⟩ := Descriptor.build_of_unique_root f hz h1 ha hs hm hnat hn hi
      sign hsign context targetRaw rfl hw domain hd hone
    have hraw := Descriptor.build_raw hbuild
    have hmember : (word, 1) ∈ t.val.node.system.tableRows.toList := by
      have h : (word, 1) ∈ (t.val.node.system.tableRows.toList.filter fun row =>
          decide (row.1.drop fullQueries.length = source.raw.constraintSigns)) := by
        rw [hrows]
        exact List.mem_singleton_self _
      exact (List.mem_filter.mp h).1
    have htableMember : (word, 1) ∈ (t.val.table hc).rows.toList := by
      simpa only [Replay.table_rows] using hmember
    have hcount : t.val.node.system.count word = 1 :=
      (t.val.table_lookup hc word).symm.trans ((t.val.table hc).count_mem htableMember)
    have hcheck : source.checkReencoding target head a b t.val = true := by
      simp only [Descriptor.checkReencoding, hraw, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨rfl, rfl, rfl⟩, hc⟩, hcount⟩
    have htake : word.take fullQueries.length = fullWord := by
      have hl : fullWord.length = fullQueries.length := by simp only [fullWord, signsAt, List.length_map]
      simp only [word, ← hl, List.take_left]
    obtain ⟨r, hr⟩ := source.buildReencoding_ofTable head a b domain hd t ht
      word hrows target (by
        change Descriptor.build sign context (raw.full (word.take fullQueries.length)) = _
        rw [htake]
        exact hbuild) hcheck
    exact ⟨r, hr, r.root_eq_source f hz h1 ha hs hm hnat hsign⟩

end Hex.SignDet

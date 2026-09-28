/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.SelectedProducer

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret HexRealRootsMathlib

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

include hz h1 ha hs hm hnat hn hi hsign in
/-- If the selected source root is absent from the target domain, the actual
re-encoding producer returns `none`, rather than an internal error. This also
covers invalid target domains, nonzero constants, and excluded roots. No
Thom ordering theorem, separating interval or injective representation is used. -/
theorem Descriptor.buildReencoding_absent {context : Ctx}
    (source : Descriptor E Ctx sign context) (head : DensePoly E) (a b : Endpoint E)
    (habsent : source.root f hz h1 ha hs hm hnat hsign ∉
      Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f)) :
    source.buildReencoding head a b = .ok none := by
  cases hd : Sturm.prepare sign head a b with
  | none => exact source.buildReencoding_ofNone head a b hd
  | some domain =>
    have bindings := Sturm.prepare_eq_some sign head a b domain hd
    let raw : RawDescriptor E Ctx := ⟨context, head, a, b, [], []⟩
    let qs := (raw.full []).queries ++ source.raw.constraints
    obtain ⟨t, ht, _⟩ := buildPrepared_roots f hz h1 ha hs hm hnat hn hi sign hsign
      context domain bindings.1 qs true
    have hc : t.val.check sign context head a b qs = true := by
      simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using t.property
    have empty : (t.val.node.system.tableRows.toList.filter fun row =>
        decide (row.1.drop (raw.full []).queries.length = source.raw.constraintSigns)) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro row hrow
      obtain ⟨hmrow, hp⟩ := List.mem_filter.mp hrow
      let table := t.val.table hc
      have member : row ∈ table.rows.toList := by
        simpa only [table, t.val.table_rows hc] using hmrow
      have positive := (table.wellFormed row member).2.2
      have count := table.count_mem member
      have semantic := t.val.count_roots f hz h1 ha hs hm hnat sign hsign
        context head a b qs hc row.1
      rw [← t.val.table_lookup hc] at semantic
      have cardpos : 0 < ((Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f)).filter
          (fun x => signsAt f hz qs x = row.1)).card := by
        rw [← semantic]
        exact count.symm ▸ positive
      obtain ⟨x, hx⟩ := Finset.card_pos.mp cardpos
      obtain ⟨hxd, hword⟩ := Finset.mem_filter.mp hx
      have tail := congrArg (List.drop (raw.full []).queries.length) hword
      have constraints : signsAt f hz source.raw.constraints x = source.raw.constraintSigns := by
        simpa [qs, signsAt, of_decide_eq_true hp] using tail
      have same := (source.constraints_iff f hz h1 ha hs hm hnat hsign x).mp constraints
      exact habsent (same ▸ hxd)
    exact source.buildReencoding_ofEmpty head a b domain hd t ht empty

end Hex.SignDet

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.DagSigns
public import HexSignDet.DagReplay
public import HexSignDet.SelectedSigns

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Construct selected-query evidence from an already checked table and its
unique extending row. No tree replay is repeated. -/
@[expose] def SelectedSigns.ofTable {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) (qs : List (DensePoly E))
    (values : Vector Int qs.length) (t : Replay E Ctx)
    (hc : t.check sign context d.raw.head d.raw.lower d.raw.upper (d.raw.queries ++ qs) = true)
    (hr : t.node.system.tableRows.toList.filter
      (fun row => decide (row.1.take d.raw.queries.length = d.raw.signs)) =
        [(d.raw.signs ++ values.toList, 1)]) : SelectedSigns d qs where
  values := values
  evidence := t
  accepted := by
    obtain ⟨hw, hctx, _, _⟩ := RawDescriptor.check_eq d.accepted
    simp only [Descriptor.checkSigns, RawDescriptor.checkSigns, hw, hctx,
      decide_true, Bool.true_and, hc, hr]

namespace Dag

/-- Replay a supplied graph for the selected descriptor's formal derivatives
and additional ordered queries, then require the exact claimed extending row.
Every stored graph entry is checked once, including unreachable entries. The
returned selected-sign evidence reuses the checked graph's literal tree. -/
@[expose] def selectedSigns? {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) (qs : List (DensePoly E))
    (values : Vector Int qs.length) (dag : Dag E Ctx) : Option (SelectedSigns d qs) := do
  let t ← dag.replay? sign context d.raw.head d.raw.lower d.raw.upper (d.raw.queries ++ qs)
  if hr : t.val.node.system.tableRows.toList.filter
      (fun row => decide (row.1.take d.raw.queries.length = d.raw.signs)) =
        [(d.raw.signs ++ values.toList, 1)] then
    return SelectedSigns.ofTable d qs values t.val t.property hr
  else none

/-- Successful selected-sign extraction preserves every supplied sign and the
actual checked graph replay, without producing replacement query evidence. -/
theorem selectedSigns_evidence {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} {qs : List (DensePoly E)}
    {values : Vector Int qs.length} {dag : Dag E Ctx} {s : SelectedSigns d qs}
    (h : dag.selectedSigns? d qs values = some s) :
    ∃ t, dag.replay? sign context d.raw.head d.raw.lower d.raw.upper
        (d.raw.queries ++ qs) = some t ∧ s.values = values ∧ s.evidence = t.val := by
  unfold selectedSigns? at h
  cases ht : dag.replay? sign context d.raw.head d.raw.lower d.raw.upper
      (d.raw.queries ++ qs) with
  | none => simp [ht, bind, Option.bind] at h
  | some t =>
    simp only [ht, bind, Option.bind] at h
    split at h
    · simp only [pure, Option.some.injEq] at h
      subst s
      exact ⟨t, rfl, rfl, rfl⟩
    · simp at h

/-- Accepted selected-sign graph evidence passes the existing independent
selected-root tree checker on the caller's exact descriptor and query list. -/
theorem selectedSigns_checked {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} {qs : List (DensePoly E)}
    {values : Vector Int qs.length} {dag : Dag E Ctx} {s : SelectedSigns d qs}
    (h : dag.selectedSigns? d qs values = some s) :
    d.checkSigns qs values s.evidence = true := by
  obtain ⟨_, _, hv, _⟩ := selectedSigns_evidence h
  simpa only [hv] using s.accepted

/-- Once graph replay succeeds, selected-sign extraction agrees with the
existing tree checker on acceptance and rejection of the exact claimed vector. -/
theorem selectedSigns_replay {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} {qs : List (DensePoly E)}
    (values : Vector Int qs.length) {dag : Dag E Ctx}
    {t : {t : Replay E Ctx //
      t.check sign context d.raw.head d.raw.lower d.raw.upper (d.raw.queries ++ qs) = true}}
    (h : dag.replay? sign context d.raw.head d.raw.lower d.raw.upper
      (d.raw.queries ++ qs) = some t) :
    (dag.selectedSigns? d qs values).isSome = d.checkSigns qs values t.val := by
  obtain ⟨hw, hctx, _, _⟩ := RawDescriptor.check_eq d.accepted
  unfold selectedSigns?
  simp only [h, bind, Option.bind, Descriptor.checkSigns, RawDescriptor.checkSigns,
    hw, hctx, decide_true, Bool.true_and, t.property]
  split <;> simp_all [pure]

/-- Every checked selected-sign tree, encoded with sharing, is accepted again
with the exact same sign vector and literal evidence. -/
theorem selectedSigns_encode [Hashable E] [Hashable Ctx]
    {sign : E → Int} {context : Ctx} {d : Descriptor E Ctx sign context}
    {qs : List (DensePoly E)} (s : SelectedSigns d qs) :
    ((encode s.evidence).selectedSigns? d qs s.values).map (fun result => result.evidence) =
      some s.evidence := by
  obtain ⟨hc, hr⟩ := s.check_eq
  rw [s.evidence.table_rows hc] at hr
  simp [selectedSigns?, replay_encode hc, hr, bind, Option.bind, pure, SelectedSigns.ofTable]

/-- Agreement on every stored graph node preserves rejection and the literal
selected-query signs and evidence. The caller descriptors must name the same
raw root identity; their proof fields and source replay need not coincide. -/
theorem selectedSigns_sign_congr (sign sign' : E → Int) (context : Ctx)
    (d : Descriptor E Ctx sign context) (d' : Descriptor E Ctx sign' context)
    (hraw : d'.raw = d.raw) (qs : List (DensePoly E)) (values : Vector Int qs.length)
    (dag : Dag E Ctx)
    (h : ∀ x ∈ dag.signOperands d.raw.head d.raw.lower d.raw.upper, sign x = sign' x) :
    (dag.selectedSigns? d qs values).map (fun s => (s.values, s.evidence)) =
      (dag.selectedSigns? d' qs values).map (fun s => (s.values, s.evidence)) := by
  have he := dag.replay_sign_congr sign sign' context d.raw.head d.raw.lower d.raw.upper
    (d.raw.queries ++ qs) h
  have he' :
      (dag.replay? sign context d.raw.head d.raw.lower d.raw.upper (d.raw.queries ++ qs)).map
        Subtype.val =
      (dag.replay? sign' context d'.raw.head d'.raw.lower d'.raw.upper
        (d'.raw.queries ++ qs)).map Subtype.val := by
    rw [hraw]
    exact he
  unfold selectedSigns?
  cases ht : dag.replay? sign context d.raw.head d.raw.lower d.raw.upper
      (d.raw.queries ++ qs) with
  | none =>
    have ht' : dag.replay? sign' context d'.raw.head d'.raw.lower d'.raw.upper
        (d'.raw.queries ++ qs) = none := by
      simpa only [ht, Option.map_none, Option.map_eq_none_iff] using he'.symm
    simp [ht', bind, Option.bind, Option.map_none]
  | some t =>
    cases ht' : dag.replay? sign' context d'.raw.head d'.raw.lower d'.raw.upper
        (d'.raw.queries ++ qs) with
    | none => simp [ht, ht'] at he'
    | some t' =>
      have htree : t.val = t'.val := by simpa only [ht, ht', Option.map_some,
        Option.some.injEq] using he'
      rcases t with ⟨tree, accepted⟩
      rcases t' with ⟨tree', accepted'⟩
      dsimp only at htree
      subst tree'
      simp only [bind, Option.bind, hraw]
      split <;> simp [pure, SelectedSigns.ofTable]

end Dag
end Hex.SignDet

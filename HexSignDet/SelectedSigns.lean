/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Descriptor

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Joint table replay on the selected formal derivatives and the exact
additional query list. Filtering must give exactly the claimed count-one
row, including every requested sign. No singleton-interval shortcut is used. -/
@[expose] def RawDescriptor.checkSigns (sign : E → Int) (context : Ctx)
    (raw : RawDescriptor E Ctx) (qs : List (DensePoly E))
    (values : Vector Int qs.length) (t : Replay E Ctx) : Bool :=
  raw.wellFormed && decide (raw.context = context) &&
  t.check sign context raw.head raw.lower raw.upper (raw.queries ++ qs) &&
    decide ((t.node.system.tableRows.toList.filter fun row =>
      decide (row.1.take raw.queries.length = raw.signs)) = [(raw.signs ++ values.toList, 1)])

/-- The validated-descriptor interface to the same literal selected-sign checker. -/
@[expose] def Descriptor.checkSigns {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) (qs : List (DensePoly E))
    (values : Vector Int qs.length) (t : Replay E Ctx) : Bool :=
  d.raw.checkSigns sign context qs values t

/-- A finite certificate for all query signs at a selected root. Context and
descriptor identity are part of its type as well as checked replay operands. -/
structure SelectedSigns {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) (qs : List (DensePoly E)) where
  values : Vector Int qs.length
  evidence : Replay E Ctx
  accepted : d.checkSigns qs values evidence = true

/-- A single selected query has a total sign accessor, without a default for
missing output. Semantic evaluation correspondence is a companion obligation. -/
def SelectedSigns.value {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} {q : DensePoly E} (s : SelectedSigns d [q]) : Int :=
  s.values[0]

theorem SelectedSigns.check_eq {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} {qs : List (DensePoly E)} (s : SelectedSigns d qs) :
    ∃ h : s.evidence.check sign context d.raw.head d.raw.lower d.raw.upper
        (d.raw.queries ++ qs) = true,
      ((s.evidence.table h).rows.toList.filter fun row =>
        decide (row.1.take d.raw.queries.length = d.raw.signs)) =
          [(d.raw.signs ++ s.values.toList, 1)] := by
  have h := s.accepted
  simp only [Descriptor.checkSigns, RawDescriptor.checkSigns, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, _⟩, hc⟩, hr⟩ := h
  refine ⟨hc, ?_⟩
  rw [s.evidence.table_rows hc]
  exact hr

/-- Every accepted selected sign is a literal ternary code. This finite
conclusion already follows from the complete table's structural invariants. -/
theorem SelectedSigns.ternary {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} {qs : List (DensePoly E)} (s : SelectedSigns d qs)
    (i : Fin qs.length) : s.values[i] = -1 ∨ s.values[i] = 0 ∨ s.values[i] = 1 := by
  obtain ⟨hc, he⟩ := s.check_eq
  have hm : (d.raw.signs ++ s.values.toList, 1) ∈ (s.evidence.table hc).rows.toList := by
    have hmem := List.mem_singleton_self (d.raw.signs ++ s.values.toList, (1 : Nat))
    rw [← he] at hmem
    exact (List.mem_filter.mp hmem).1
  apply ((s.evidence.table hc).wellFormed _ hm).2.1
  exact List.mem_append_right _ (List.getElem_mem (by simp))

/-- Accepted selected-query evidence asserts one matching finite observation.
Root interpretation still requires the shared root-sum soundness bridge. -/
theorem SelectedSigns.count {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} {qs : List (DensePoly E)} (s : SelectedSigns d qs)
    {xs : List (List Int)} (ho : Observations (d.raw.queries ++ qs).length xs)
    (hm : s.evidence.Interprets (d.raw.queries ++ qs).length xs) :
    xs.countP (fun x => decide (x = d.raw.signs ++ s.values.toList)) = 1 := by
  obtain ⟨hc, he⟩ := s.check_eq
  have hrow : (d.raw.signs ++ s.values.toList, 1) ∈ (s.evidence.table hc).rows.toList := by
    have hmem := List.mem_singleton_self (d.raw.signs ++ s.values.toList, (1 : Nat))
    rw [← he] at hmem
    exact (List.mem_filter.mp hmem).1
  rw [← s.evidence.table_count hc ho hm, SignTable.count_mem _ hrow]

/-- Every observation matching the descriptor's constraints has exactly the
returned query signs. Completeness, including omitted table rows, is essential
here; a count-one row alone would not exclude another matching observation. -/
theorem SelectedSigns.signs_eq {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} {qs : List (DensePoly E)} (s : SelectedSigns d qs)
    {xs : List (List Int)} (ho : Observations (d.raw.queries ++ qs).length xs)
    (hm : s.evidence.Interprets (d.raw.queries ++ qs).length xs)
    {x : List Int} (hx : x ∈ xs) (hp : x.take d.raw.queries.length = d.raw.signs) :
    x = d.raw.signs ++ s.values.toList := by
  obtain ⟨hc, he⟩ := s.check_eq
  have hpos : 0 < xs.countP (fun y => decide (y = x)) := by
    by_cases hn : 0 < xs.countP (fun y => decide (y = x))
    · exact hn
    · have hz : xs.countP (fun y => decide (y = x)) = 0 := by omega
      have hf := List.countP_eq_zero.mp hz x hx
      simp at hf
  obtain ⟨n, hn⟩ := (s.evidence.table hc).mem_of_count_pos
    (by rw [s.evidence.table_count hc ho hm]; exact hpos)
  have hf : (x, n) ∈ (s.evidence.table hc).rows.toList.filter
      (fun row => decide (row.1.take d.raw.queries.length = d.raw.signs)) :=
    List.mem_filter.mpr ⟨hn, by simp only [hp, decide_true]⟩
  rw [he] at hf
  exact congrArg Prod.fst (List.mem_singleton.mp hf)

variable [Neg E] [Inv E]

/-- Build joint selected-root signs. Internal diagnostics remain visible
until total producer completeness rules them out on validated descriptors. -/
def Descriptor.buildSigns {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) (qs : List (DensePoly E)) :
    Except BuildError (SelectedSigns d qs) :=
  match Sturm.prepare sign d.raw.head d.raw.lower d.raw.upper with
  | none => .error .replay
  | some domain =>
    match buildPrepared context domain (d.raw.queries ++ qs) with
    | .error err => .error err
    | .ok t =>
      let candidates := (t.val.table t.property).rows.toList.filter fun row =>
        decide (row.1.take d.raw.queries.length = d.raw.signs)
      match candidates with
      | [(signs, 1)] =>
        let values := signs.drop d.raw.queries.length
        if hv : values.length = qs.length then
          let v : Vector Int qs.length := ⟨values.toArray, by simpa using hv⟩
          if h : d.checkSigns qs v t.val = true then .ok ⟨v, t.val, h⟩
          else .error .replay
        else .error .dimensions
      | _ => .error .system

end Hex.SignDet

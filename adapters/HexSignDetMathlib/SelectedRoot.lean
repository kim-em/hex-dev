/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.SelectedSigns
public import HexSignDet.Reencode
public import HexSignDet.Compare
public import HexSignDetMathlib.RootModel
public import HexSignDetMathlib.Derivatives
public import HexSignDetMathlib.Reencode

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

include h1 ha hs hm hnat hsign in
/-- Count-one replay identifies exactly one root satisfying all selected
formal-derivative signs jointly, for partial as well as full encodings. -/
theorem Descriptor.existsUnique_root {context : Ctx} (d : Descriptor E Ctx sign context) :
    ∃! x, x ∈ Tarski.rootsIn (interpret f hz d.raw.head)
        (d.raw.lower.map f) (d.raw.upper.map f) ∧
      signsAt f hz d.raw.queries x = d.raw.signs := by
  have accepted := d.accepted
  simp only [RawDescriptor.check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have counted := d.evidence.count_roots f hz h1 ha hs hm hnat sign hsign context
    d.raw.head d.raw.lower d.raw.upper d.raw.queries accepted.1.2 d.raw.signs
  have hone : ((Tarski.rootsIn (interpret f hz d.raw.head)
      (d.raw.lower.map f) (d.raw.upper.map f)).filter
      (fun x => signsAt f hz d.raw.queries x = d.raw.signs)).card = 1 :=
    counted.symm.trans accepted.2
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
  have mem : x ∈ (Tarski.rootsIn (interpret f hz d.raw.head)
      (d.raw.lower.map f) (d.raw.upper.map f)).filter
      (fun x => signsAt f hz d.raw.queries x = d.raw.signs) := by
    rw [hx]
    exact Finset.mem_singleton_self x
  refine ⟨x, Finset.mem_filter.mp mem, ?_⟩
  intro y hy
  have member : y ∈ (Tarski.rootsIn (interpret f hz d.raw.head)
      (d.raw.lower.map f) (d.raw.upper.map f)).filter
      (fun x => signsAt f hz d.raw.queries x = d.raw.signs) := Finset.mem_filter.mpr hy
  rw [hx] at member
  exact Finset.mem_singleton.mp member

/-- The mathematical root identified by an accepted descriptor. -/
noncomputable def Descriptor.root {context : Ctx} (d : Descriptor E Ctx sign context) : K :=
  Classical.choose (d.existsUnique_root f hz h1 ha hs hm hnat hsign)

/-- The selected root lies in the descriptor's interval and satisfies all
of its derivative signs at that same point. -/
theorem Descriptor.root_spec {context : Ctx} (d : Descriptor E Ctx sign context) :
    d.root f hz h1 ha hs hm hnat hsign ∈
        Tarski.rootsIn (interpret f hz d.raw.head) (d.raw.lower.map f) (d.raw.upper.map f) ∧
      signsAt f hz d.raw.queries (d.root f hz h1 ha hs hm hnat hsign) = d.raw.signs := by
  exact (Classical.choose_spec (d.existsUnique_root f hz h1 ha hs hm hnat hsign)).1

include h1 ha hs hm hnat hsign in
/-- The selected root realizes the formal derivative signs named by the
descriptor indices, not merely the stored query polynomials. -/
theorem Descriptor.root_derivatives {context : Ctx} (d : Descriptor E Ctx sign context) :
    d.raw.signs = d.raw.indices.map (fun j =>
      (SignType.sign ((Polynomial.derivative^[j]
        (interpret f hz d.raw.head)).eval (d.root f hz h1 ha hs hm hnat hsign)) : Int)) := by
  have hw : d.raw.wellFormed = true := (RawDescriptor.check_eq d.accepted).1
  have hquery := d.raw.querySigns f hz hnat hm hw
    (d.root f hz h1 ha hs hm hnat hsign)
  exact (d.root_spec f hz h1 ha hs hm hnat hsign).2.symm.trans
    (by simpa only [signsAt] using hquery)

/-- Any root with the checked encoding denotes the same selected value. -/
theorem Descriptor.root_unique {context : Ctx} (d : Descriptor E Ctx sign context) (x : K)
    (hx : x ∈ Tarski.rootsIn (interpret f hz d.raw.head)
      (d.raw.lower.map f) (d.raw.upper.map f))
    (hxs : signsAt f hz d.raw.queries x = d.raw.signs) :
    x = d.root f hz h1 ha hs hm hnat hsign := by
  exact (Classical.choose_spec (d.existsUnique_root f hz h1 ha hs hm hnat hsign)).2 x ⟨hx, hxs⟩

include h1 ha hs hm hnat hsign in
/-- Every sign returned by checked joint determination is the sign of the
requested polynomial at the root selected by the descriptor. -/
theorem SelectedSigns.values_at_root {context : Ctx}
    {d : Descriptor E Ctx sign context} {qs : List (DensePoly E)}
    (s : SelectedSigns d qs) :
    s.values.toList = signsAt f hz qs (d.root f hz h1 ha hs hm hnat hsign) := by
  let x := d.root f hz h1 ha hs hm hnat hsign
  obtain ⟨hx, hsx⟩ := d.root_spec f hz h1 ha hs hm hnat hsign
  obtain ⟨hc, _⟩ := s.check_eq
  have ho := rootObservations_valid f hz d.raw.head (d.raw.queries ++ qs)
    d.raw.lower d.raw.upper
  have hinterprets := s.evidence.check_interprets f hz h1 ha hs hm hnat sign hsign
    context d.raw.head d.raw.lower d.raw.upper (d.raw.queries ++ qs) hc
  have hobs : signsAt f hz (d.raw.queries ++ qs) x ∈
      rootObservations f hz d.raw.head (d.raw.queries ++ qs)
        d.raw.lower d.raw.upper := by
    simp only [rootObservations, List.mem_map, Finset.mem_toList]
    exact ⟨x, hx, rfl⟩
  have hprefix : (signsAt f hz (d.raw.queries ++ qs) x).take d.raw.queries.length =
      d.raw.signs := by
    simpa [signsAt, x] using hsx
  have hrow := s.signs_eq ho hinterprets hobs hprefix
  have hlength : d.raw.signs.length = d.raw.queries.length := by
    simpa [signsAt] using congrArg List.length hsx.symm
  have htail := congrArg (List.drop d.raw.queries.length) hrow
  have hleft : (d.raw.signs ++ s.values.toList).drop d.raw.queries.length =
      s.values.toList := by
    rw [← hlength]
    simp
  rw [hleft] at htail
  simpa [signsAt, x] using htail.symm

include h1 ha hs hm hnat hsign in
/-- The public one-query accessor has the sign of that polynomial at the
selected real root. -/
theorem SelectedSigns.value_at_root {context : Ctx}
    {d : Descriptor E Ctx sign context} {q : DensePoly E}
    (s : SelectedSigns d [q]) :
    s.value = (SignType.sign ((interpret f hz q).eval
      (d.root f hz h1 ha hs hm hnat hsign)) : Int) := by
  have h := s.values_at_root f hz h1 ha hs hm hnat hsign
  have hhead := congrArg List.head? h
  have hfirst : s.values.toList.head? = some s.values[0] := by
    simp [List.head?_eq_getElem?]
  rw [hfirst] at hhead
  simpa [SelectedSigns.value, signsAt] using Option.some.inj hhead

include h1 ha hs hm hnat hsign in
/-- Accepted joint re-encoding evidence contains a real root in the target
domain with both the target derivative word and every old-root constraint. -/
theorem Reencoding.exists_root {context : Ctx}
    {source : Descriptor E Ctx sign context} {head : DensePoly E}
    {a b : Endpoint E} (r : Reencoding source head a b) :
    ∃ x ∈ Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f),
      signsAt f hz (r.target.raw.queries ++ source.raw.constraints) x =
        r.target.raw.signs ++ source.raw.constraintSigns := by
  obtain ⟨_, hc, hcount⟩ := r.check_eq
  have hcard := r.evidence.count_roots f hz h1 ha hs hm hnat sign hsign
    context head a b (r.target.raw.queries ++ source.raw.constraints) hc
    (r.target.raw.signs ++ source.raw.constraintSigns)
  rw [r.evidence.table_lookup hc] at hcount
  rw [hcount] at hcard
  have hpos : 0 < ((Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f)).filter
      (fun x => signsAt f hz (r.target.raw.queries ++ source.raw.constraints) x =
        r.target.raw.signs ++ source.raw.constraintSigns)).card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

include h1 ha hs hm hnat hsign in
/-- The target descriptor's selected root satisfies every constraint copied
from the source descriptor; there is no free choice of another target root. -/
theorem Reencoding.target_constraints {context : Ctx}
    {source : Descriptor E Ctx sign context} {head : DensePoly E}
    {a b : Endpoint E} (r : Reencoding source head a b) :
    signsAt f hz source.raw.constraints
      (r.target.root f hz h1 ha hs hm hnat hsign) = source.raw.constraintSigns := by
  obtain ⟨x, hx, hsx⟩ := r.exists_root f hz h1 ha hs hm hnat hsign
  obtain ⟨⟨hhead, hlower, hupper⟩, _, _⟩ := r.check_eq
  have htargetDomain : x ∈ Tarski.rootsIn (interpret f hz r.target.raw.head)
      (r.target.raw.lower.map f) (r.target.raw.upper.map f) := by
    simpa only [hhead, hlower, hupper] using hx
  have hlen : r.target.raw.signs.length = r.target.raw.queries.length := by
    have hspec := (r.target.root_spec f hz h1 ha hs hm hnat hsign).2
    simpa [signsAt] using congrArg List.length hspec.symm
  have htarget : signsAt f hz r.target.raw.queries x = r.target.raw.signs := by
    have h := congrArg (List.take r.target.raw.queries.length) hsx
    simpa [signsAt, ← hlen] using h
  have hsource : signsAt f hz source.raw.constraints x = source.raw.constraintSigns := by
    have h := congrArg (List.drop r.target.raw.queries.length) hsx
    simpa [signsAt, ← hlen] using h
  have heq := r.target.root_unique f hz h1 ha hs hm hnat hsign x
    htargetDomain htarget
  simpa only [heq] using hsource

omit [IsStrictOrderedRing K] [IsRealClosed K] in
/-- The first copied constraint is the old defining equation. -/
theorem Descriptor.constraints_head {context : Ctx}
    (d : Descriptor E Ctx sign context) (x : K)
    (h : signsAt f hz d.raw.constraints x = d.raw.constraintSigns) :
    (interpret f hz d.raw.head).eval x = 0 := by
  have hhead := congrArg List.head? h
  simp only [signsAt, RawDescriptor.constraints, RawDescriptor.constraintSigns] at hhead
  have hs0 : (SignType.sign ((interpret f hz d.raw.head).eval x) : Int) = 0 :=
    Option.some.inj hhead
  have hs0' : SignType.sign ((interpret f hz d.raw.head).eval x) = 0 := by
    cases hsg : SignType.sign ((interpret f hz d.raw.head).eval x) <;>
      simp [hsg] at hs0 ⊢
  exact sign_eq_zero_iff.mp hs0'

omit [IsStrictOrderedRing K] [IsRealClosed K] in
/-- Copied derivative constraints retain the source descriptor's joint word. -/
theorem Descriptor.constraints_queries {context : Ctx}
    (d : Descriptor E Ctx sign context) (x : K)
    (h : signsAt f hz d.raw.constraints x = d.raw.constraintSigns) :
    signsAt f hz d.raw.queries x = d.raw.signs := by
  have htail := congrArg List.tail h
  simp [signsAt, RawDescriptor.constraints, RawDescriptor.constraintSigns] at htail
  have htake := congrArg (List.take d.raw.queries.length) htail
  have hw := (RawDescriptor.check_eq d.accepted).1
  simp only [RawDescriptor.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
  have hlen : d.raw.signs.length = d.raw.queries.length := by
    simpa [RawDescriptor.queries] using hw.1.1.1.2.symm
  simpa [signsAt, ← hlen] using htake

omit [IsStrictOrderedRing K] [IsRealClosed K] in
/-- The suffix of the copied constraints retains both endpoint signs. -/
theorem Descriptor.constraints_bounds {context : Ctx}
    (d : Descriptor E Ctx sign context) (x : K)
    (h : signsAt f hz d.raw.constraints x = d.raw.constraintSigns) :
    signsAt f hz
      ((match d.raw.lower with
        | .finite a => [DensePoly.ofCoeffs #[0, 1] - DensePoly.C a]
        | _ => []) ++
       (match d.raw.upper with
        | .finite a => [DensePoly.ofCoeffs #[0, 1] - DensePoly.C a]
        | _ => [])) x =
      ((match d.raw.lower with | .finite _ => [1] | _ => []) ++
       (match d.raw.upper with | .finite _ => [-1] | _ => [])) := by
  have hw := (RawDescriptor.check_eq d.accepted).1
  simp only [RawDescriptor.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
  have hlen : d.raw.signs.length = d.raw.queries.length := by
    simpa [RawDescriptor.queries] using hw.1.1.1.2.symm
  have hdrop := congrArg (List.drop (d.raw.queries.length + 1)) h
  simp [signsAt, RawDescriptor.constraints, RawDescriptor.constraintSigns, ← hlen] at hdrop
  simp only [signsAt, List.map_append]
  exact hdrop

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
private theorem castSignPos (y : K) :
    (SignType.sign y : Int) = 1 ↔ 0 < y := by
  constructor
  · intro h
    have hs : SignType.sign y = 1 := by
      cases heq : SignType.sign y <;> simp [heq] at h ⊢
    exact sign_eq_one_iff.mp hs
  · intro h
    rw [sign_eq_one_iff.mpr h]
    rfl

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
private theorem castSignNeg (y : K) :
    (SignType.sign y : Int) = -1 ↔ y < 0 := by
  constructor
  · intro h
    have hs : SignType.sign y = -1 := by
      cases heq : SignType.sign y <;> simp [heq] at h ⊢
    exact sign_eq_neg_one_iff.mp hs
  · intro h
    rw [sign_eq_neg_one_iff.mpr h]
    rfl

include h1 ha hs hm hnat hsign in
/-- Copied finite endpoint signs express the source open interval; impossible
infinite endpoint orientations are excluded by source acceptance. -/
theorem Descriptor.constraints_interval {context : Ctx}
    (d : Descriptor E Ctx sign context) (x : K)
    (h : signsAt f hz d.raw.constraints x = d.raw.constraintSigns) :
    Tarski.InInterval (d.raw.lower.map f) (d.raw.upper.map f) x := by
  have hb := d.constraints_bounds f hz x h
  have hp := ((Tarski.mem_rootsIn _ _ _ _).mp
    (d.root_spec f hz h1 ha hs hm hnat hsign).1).2
  cases hl : d.raw.lower <;> cases hu : d.raw.upper <;>
    simp_all [Tarski.inInterval_iff, Endpoint.map, signsAt,
      endpoint_eval f hz h1 hs, castSignPos, castSignNeg]

/-- An accepted positive-degree descriptor has a nonzero interpreted head. -/
theorem Descriptor.head_ne_zero {context : Ctx}
    (d : Descriptor E Ctx sign context) : interpret f hz d.raw.head ≠ 0 := by
  have hw := (RawDescriptor.check_eq d.accepted).1
  simp only [RawDescriptor.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
  intro hzero
  have hdegree := congrArg Polynomial.natDegree hzero
  rw [natDegree_interpret] at hdegree
  simp at hdegree
  omega

include h1 ha hs hm hnat hsign in
/-- Checked re-encoding preserves the exact selected real root across heads. -/
theorem Reencoding.root_eq_source {context : Ctx}
    {source : Descriptor E Ctx sign context} {head : DensePoly E}
    {a b : Endpoint E} (r : Reencoding source head a b) :
    r.target.root f hz h1 ha hs hm hnat hsign =
      source.root f hz h1 ha hs hm hnat hsign := by
  let x := r.target.root f hz h1 ha hs hm hnat hsign
  have hc := r.target_constraints f hz h1 ha hs hm hnat hsign
  have hx : x ∈ Tarski.rootsIn (interpret f hz source.raw.head)
      (source.raw.lower.map f) (source.raw.upper.map f) := by
    apply (Tarski.mem_rootsIn_iff _ (source.head_ne_zero f hz) _ _ _).mpr
    exact ⟨source.constraints_head f hz x hc,
      source.constraints_interval f hz h1 ha hs hm hnat hsign x hc⟩
  exact source.root_unique f hz h1 ha hs hm hnat hsign x hx
    (source.constraints_queries f hz x hc)

include h1 ha hs hm hnat hsign in
/-- Equality returned by a checked cross-polynomial comparison identifies the
same real root, using the common descriptor's count-one evidence. This does
not require the Thom theorem for strict order. -/
private theorem Comparison.eq_root {context : Ctx}
    {left right : Descriptor E Ctx sign context} (c : Comparison left right)
    (heq : c.order = .eq) :
    left.root f hz h1 ha hs hm hnat hsign =
      right.root f hz h1 ha hs hm hnat hsign := by
  have horder : c.leftEncoding.target.fullOrder c.rightEncoding.target = some .eq := by
    simpa only [heq] using c.ordered
  obtain ⟨hguard, hsigns⟩ := Descriptor.fullOrder_eq horder
  have hwords : c.leftEncoding.target.raw.signs = c.rightEncoding.target.raw.signs :=
    Thom.compareSigns_eq hsigns
  obtain ⟨hleftHead, hleftLower, hleftUpper⟩ := c.leftEncoding.check_eq.1
  obtain ⟨hrightHead, hrightLower, hrightUpper⟩ := c.rightEncoding.check_eq.1
  have hhead : c.leftEncoding.target.raw.head = c.rightEncoding.target.raw.head :=
    hleftHead.trans hrightHead.symm
  have hlower : c.leftEncoding.target.raw.lower = c.rightEncoding.target.raw.lower :=
    hleftLower.trans hrightLower.symm
  have hupper : c.leftEncoding.target.raw.upper = c.rightEncoding.target.raw.upper :=
    hleftUpper.trans hrightUpper.symm
  have hindices : c.leftEncoding.target.raw.indices =
      c.rightEncoding.target.raw.indices := by
    rw [hguard.2.1, hguard.2.2, ← hhead]
  have hqueries : c.leftEncoding.target.raw.queries =
      c.rightEncoding.target.raw.queries := by
    simp only [RawDescriptor.queries, hhead, hindices]
  let x := c.leftEncoding.target.root f hz h1 ha hs hm hnat hsign
  have hmem : x ∈ Tarski.rootsIn (interpret f hz c.rightEncoding.target.raw.head)
      (c.rightEncoding.target.raw.lower.map f)
      (c.rightEncoding.target.raw.upper.map f) := by
    simpa only [← hhead, ← hlower, ← hupper] using
      (c.leftEncoding.target.root_spec f hz h1 ha hs hm hnat hsign).1
  have hsignAt : signsAt f hz c.rightEncoding.target.raw.queries x =
      c.rightEncoding.target.raw.signs := by
    simpa only [← hqueries, ← hwords] using
      (c.leftEncoding.target.root_spec f hz h1 ha hs hm hnat hsign).2
  calc
    left.root f hz h1 ha hs hm hnat hsign = x :=
      (c.leftEncoding.root_eq_source f hz h1 ha hs hm hnat hsign).symm
    _ = c.rightEncoding.target.root f hz h1 ha hs hm hnat hsign :=
      c.rightEncoding.target.root_unique f hz h1 ha hs hm hnat hsign x hmem hsignAt
    _ = right.root f hz h1 ha hs hm hnat hsign :=
      c.rightEncoding.root_eq_source f hz h1 ha hs hm hnat hsign

include h1 ha hs hm hnat hsign in
/-- If the two selected real roots coincide, their checked common full
derivative encodings are identical and the finite comparison returns equality. -/
private theorem Comparison.root_eq {context : Ctx}
    {left right : Descriptor E Ctx sign context} (c : Comparison left right)
    (heq : left.root f hz h1 ha hs hm hnat hsign =
      right.root f hz h1 ha hs hm hnat hsign) : c.order = .eq := by
  obtain ⟨hguard, _⟩ := Descriptor.fullOrder_eq c.ordered
  obtain ⟨hleftHead, _, _⟩ := c.leftEncoding.check_eq.1
  obtain ⟨hrightHead, _, _⟩ := c.rightEncoding.check_eq.1
  have hhead : c.leftEncoding.target.raw.head = c.rightEncoding.target.raw.head :=
    hleftHead.trans hrightHead.symm
  have hindices : c.leftEncoding.target.raw.indices =
      c.rightEncoding.target.raw.indices := by
    rw [hguard.2.1, hguard.2.2, ← hhead]
  have hroots : c.leftEncoding.target.root f hz h1 ha hs hm hnat hsign =
      c.rightEncoding.target.root f hz h1 ha hs hm hnat hsign := by
    calc
      _ = left.root f hz h1 ha hs hm hnat hsign :=
        c.leftEncoding.root_eq_source f hz h1 ha hs hm hnat hsign
      _ = right.root f hz h1 ha hs hm hnat hsign := heq
      _ = _ := (c.rightEncoding.root_eq_source f hz h1 ha hs hm hnat hsign).symm
  have hleft := c.leftEncoding.target.root_derivatives f hz h1 ha hs hm hnat hsign
  have hright := c.rightEncoding.target.root_derivatives f hz h1 ha hs hm hnat hsign
  rw [hhead, hindices, hroots] at hleft
  have hwords : c.leftEncoding.target.raw.signs = c.rightEncoding.target.raw.signs :=
    hleft.trans hright.symm
  have hwell := (RawDescriptor.check_eq c.leftEncoding.target.accepted).1
  simp only [RawDescriptor.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hwell
  have hne : c.leftEncoding.target.raw.signs ≠ [] := by
    intro hnil
    have hlen := hwell.1.1.1.2
    rw [hguard.2.1] at hlen
    simp only [hnil, List.length_nil, List.length_map, List.length_range] at hlen
    omega
  have hnotEmpty : c.leftEncoding.target.raw.signs.isEmpty = false := by
    cases hs : c.leftEncoding.target.raw.signs with
    | nil => exact False.elim (hne hs)
    | cons _ _ => rfl
  have hcmp : Thom.compareSigns c.leftEncoding.target.raw.signs
      c.leftEncoding.target.raw.signs = some .eq := by
    simp only [Thom.compareSigns, hnotEmpty, hwell.2, Bool.not_true,
      Bool.false_or, Thom.compareFrom_self]
    simp
  have horder : c.leftEncoding.target.fullOrder c.rightEncoding.target = some .eq := by
    unfold Descriptor.fullOrder
    rw [ite_eq_left hguard]
    rw [← hwords]
    exact hcmp
  exact Option.some.inj (c.ordered.symm.trans horder)

include h1 ha hs hm hnat hsign in
/-- Equality is the exact semantic meaning of the equality branch of the
checked common-product comparison. Strict order has a separate Thom gate. -/
theorem Comparison.eq_iff_root_eq {context : Ctx}
    {left right : Descriptor E Ctx sign context} (c : Comparison left right) :
    c.order = .eq ↔
      left.root f hz h1 ha hs hm hnat hsign =
        right.root f hz h1 ha hs hm hnat hsign := by
  exact ⟨c.eq_root f hz h1 ha hs hm hnat hsign,
    c.root_eq f hz h1 ha hs hm hnat hsign⟩

end Hex.SignDet

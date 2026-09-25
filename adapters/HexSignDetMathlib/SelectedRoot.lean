/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.SelectedSigns
public import HexSignDet.Reencode
public import HexSignDetMathlib.RootModel
public import HexSignDetMathlib.Derivatives

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
  simp only [RawDescriptor.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
  have hb : ∀ j ∈ d.raw.indices, 1 ≤ j ∧ j ≤ d.raw.head.natDegree := by
    intro j hj
    exact of_decide_eq_true (List.all_eq_true.mp hw.1.2 j hj)
  rw [← (d.root_spec f hz h1 ha hs hm hnat hsign).2]
  simp only [signsAt, RawDescriptor.queries, List.map_map]
  apply List.map_congr_left
  intro j hj
  obtain ⟨hjpos, hjdeg⟩ := hb j hj
  have hlt : j - 1 < d.raw.head.natDegree := by omega
  have hindex : j - 1 < (derivativesFrom d.raw.head d.raw.head.natDegree).length := by
    rw [derivativesFrom_length]
    exact hlt
  simp only [Function.comp_apply, derivatives]
  rw [List.getElem?_eq_getElem hindex, Option.getD_some]
  rw [derivativesFrom_get f hz hnat hm d.raw.head d.raw.head.natDegree (j - 1) hlt]
  simpa only [Nat.sub_add_cancel hjpos]

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

end Hex.SignDet

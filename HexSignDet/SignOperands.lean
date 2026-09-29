/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.SignOperands
public import HexSignDet.Replay

public section

/-!
Finite coefficient-sign dependencies for product reductions, moments, BKR nodes
and recursive replay. The same inventories cover acceptance and rejection;
query order, literal context bindings, integer matrix identities and child
support checks retain the existing implementation.

The inventories list occurrences rather than identify shared proof nodes.
They provide the finite agreement rule needed by checked coefficient evidence;
they do not encode a dependency graph across coefficient-field levels.
-/

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]

/-- The two scale signs used by a supplied product-reduction step. -/
@[expose] def ReductionStep.signOperands (s : ReductionStep E) : List E :=
  [s.witness.leftScale, s.witness.rightScale]

/-- All supplied product-reduction scales, including unused malformed steps. -/
@[expose] def reductionOperands (ss : List (ReductionStep E)) : List E :=
  ss.flatMap ReductionStep.signOperands

variable [One E] [Add E] [Sub E] [Mul E]

omit [One E] in
/-- Reduction replay depends only on the supplied scale signs. -/
theorem ReductionStep.check_sign_congr (sign sign' : E → Int)
    (p prev factor : DensePoly E) (i : Nat) (s : ReductionStep E)
    (h : ∀ x ∈ s.signOperands, sign x = sign' x) :
    s.check sign p prev factor i = s.check sign' p prev factor i := by
  have hl := h s.witness.leftScale (by simp [signOperands])
  have hr := h s.witness.rightScale (by simp [signOperands])
  simp only [check, hl, hr]

omit [One E] in
/-- Agreement on the literal scales preserves full reduction replay,
including missing or extra factors and witnesses. -/
theorem Reduction.checkFrom_sign_congr (sign sign' : E → Int)
    (p prev : DensePoly E) (fs : List (Nat × DensePoly E))
    (ss : List (ReductionStep E)) (result : DensePoly E)
    (h : ∀ x ∈ reductionOperands ss, sign x = sign' x) :
    checkFrom sign p prev fs ss result = checkFrom sign' p prev fs ss result := by
  induction ss generalizing prev fs with
  | nil => cases fs <;> rfl
  | cons s ss ih =>
    cases fs with
    | nil => rfl
    | cons factor fs =>
      have hs := s.check_sign_congr sign sign' p prev factor.2 factor.1
        (fun x hx => h x (by simp [reductionOperands, hx]))
      have ht := ih s.next fs (fun x hx => h x (by simpa [reductionOperands] using Or.inr hx))
      simp only [checkFrom, hs, ht]

/-- Preprocessing every query uses the same finite scale dependency rule. -/
theorem QueryReduction.checkFrom_sign_congr (sign sign' : E → Int)
    (p : DensePoly E) (i : Nat) (qs : List (DensePoly E)) (ss : List (ReductionStep E))
    (h : ∀ x ∈ reductionOperands ss, sign x = sign' x) :
    checkFrom sign p i qs ss = checkFrom sign' p i qs ss := by
  induction ss generalizing i qs with
  | nil => cases qs <;> rfl
  | cons s ss ih =>
    cases qs with
    | nil => rfl
    | cons q qs =>
      have hs := s.check_sign_congr sign sign' p 1 q i
        (fun x hx => h x (by simp [reductionOperands, hx]))
      have ht := ih (i + 1) qs (fun x hx => h x (by simpa [reductionOperands] using Or.inr hx))
      simp only [checkFrom, hs, ht]

variable [NatCast E]

/-- The signs needed by a supplied moment: scale reductions followed by the
actual shared Tarski certificate's sign operands. -/
@[expose] def momentSignOperands (p : DensePoly E) (a b : Endpoint E)
    (cert : TarskiCertificate E E Ctx)
    (reduction : Option (Reduction E)) : List E :=
  (reduction.toList.flatMap fun r => reductionOperands r.steps) ++
    TarskiCertificate.signOperands p a b cert

/-- Finite agreement preserves the existing moment checker. Arithmetic
identities, integer values and literal bindings retain their existing checks. -/
theorem checkMoment_sign_congr [DecidableEq Ctx] (sign sign' : E → Int) (context : Ctx)
    (p : DensePoly E) (a b : Endpoint E) (qs : List (DensePoly E)) (es : List Nat)
    (value : Int) (cert : TarskiCertificate E E Ctx) (reduction : Option (Reduction E))
    (h : ∀ x ∈ momentSignOperands p a b cert reduction, sign x = sign' x) :
    checkMoment sign context p a b qs es value cert reduction =
      checkMoment sign' context p a b qs es value cert reduction := by
  have hc := TarskiCertificate.check_sign_congr sign sign' context p (queryPoly qs es reduction)
    a b value cert (fun x hx => h x (by simp [momentSignOperands, hx]))
  simp only [checkMoment_eq, Sturm.check, hc]
  cases reduction with
  | none => rfl
  | some r =>
    have hr := Reduction.checkFrom_sign_congr sign sign' p 1 (factors qs es) r.steps r.result
      (fun x hx => h x (by simp [momentSignOperands, hx]))
    simp only [Reduction.check, hr]

/-- The finite coefficient-sign dependencies of one BKR node. The inventory
covers full domain replay even when a checked domain cache saves native work. -/
@[expose] def Node.signOperands (p : DensePoly E) (a b : Endpoint E) (n : Node E Ctx) : List E :=
  (n.preparation.toList.flatMap fun r => reductionOperands r.steps) ++
    (List.finRange n.size).flatMap fun i =>
      momentSignOperands p a b n.moments[i] n.reductions[i]

/-- A BKR node's result is preserved by finite sign agreement, for arbitrary
supplied matrices and witnesses. Literal rank/support/context checks remain
exact; a cached domain cannot justify omitting a dependency from this rule. -/
theorem Node.check_sign_congr [DecidableEq Ctx] (sign sign' : E → Int) (context : Ctx)
    (p : DensePoly E) (a b : Endpoint E) (qs : List (DensePoly E)) (n : Node E Ctx)
    (h : ∀ x ∈ n.signOperands p a b, sign x = sign' x) :
    n.check sign context p a b qs = n.check sign' context p a b qs := by
  have hm (i : Fin n.size) := checkMoment_sign_congr sign sign' context p a b
    (QueryReduction.operands qs n.preparation) n.system.rows[i] n.system.values[i]
    n.moments[i] n.reductions[i] (fun x hx => h x (by
      simp only [signOperands, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr ⟨i, by simp, hx⟩)))
  have hp : (match n.preparation with | none => true | some r => r.check sign p qs) =
      (match n.preparation with | none => true | some r => r.check sign' p qs) := by
    cases hd : n.preparation with
    | none => rfl
    | some r =>
      have hr := QueryReduction.checkFrom_sign_congr sign sign' p 0 qs r.steps
        (fun x hx => h x (by simp [signOperands, hd, hx]))
      simp only [QueryReduction.check, hr]
  simp only [check_eq, hm]
  cases hd : n.preparation <;> simp_all only

/-- All node inventories of the literal tree. Repeated values and repeated
subtrees remain occurrences here; a dependency graph may share their facts. -/
@[expose] def Replay.signOperands (p : DensePoly E) (a b : Endpoint E) : Replay E Ctx → List E
  | .leaf n => n.signOperands p a b
  | .split n l r => n.signOperands p a b ++ l.signOperands p a b ++ r.signOperands p a b

/-- Finite coefficient-sign agreement preserves the complete recursive BKR
checker, including child support completeness and all rejection paths. -/
theorem Replay.check_sign_congr [DecidableEq Ctx] (sign sign' : E → Int) (context : Ctx)
    (p : DensePoly E) (a b : Endpoint E) (qs : List (DensePoly E)) (t : Replay E Ctx)
    (h : ∀ x ∈ t.signOperands p a b, sign x = sign' x) :
    t.check sign context p a b qs = t.check sign' context p a b qs := by
  induction t generalizing qs with
  | leaf n =>
    have hn := n.check_sign_congr sign sign' context p a b qs h
    simp only [check, hn]
  | split n l r ihl ihr =>
    have hn := n.check_sign_congr sign sign' context p a b qs
      (fun x hx => h x (by simp [signOperands, hx]))
    have hl := ihl (qs.take (qs.length / 2))
      (fun x hx => h x (by simp [signOperands, hx]))
    have hr := ihr (qs.drop (qs.length / 2))
      (fun x hx => h x (by simp [signOperands, hx]))
    simp only [check, hn, hl, hr]

end Hex.SignDet

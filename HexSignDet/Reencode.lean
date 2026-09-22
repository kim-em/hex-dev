/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Complete

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Old-root constraints include the defining equation, formal derivative
signs and strict finite endpoint inequalities. Infinite endpoints need no
query on a validated domain. -/
@[expose] def RawDescriptor.constraints (d : RawDescriptor E Ctx) : List (DensePoly E) :=
  let endpoint := fun e => match e with
    | Endpoint.finite a => [DensePoly.ofCoeffs #[0, 1] - DensePoly.C a]
    | _ => []
  d.head :: d.queries ++ endpoint d.lower ++ endpoint d.upper

@[expose] def RawDescriptor.constraintSigns (d : RawDescriptor E Ctx) : List Int :=
  0 :: d.signs ++ (match d.lower with | .finite _ => [1] | _ => []) ++
    (match d.upper with | .finite _ => [-1] | _ => [])

/-- Joint count-one evidence that the target descriptor also satisfies the
old root's defining equation, derivative conditions and open interval. -/
@[expose] def Descriptor.checkReencoding {sign : E → Int} {context : Ctx}
    (source target : Descriptor E Ctx sign context) (head : DensePoly E) (a b : Endpoint E)
    (t : Replay E Ctx) : Bool :=
  decide (target.raw.head = head ∧ target.raw.lower = a ∧ target.raw.upper = b) &&
  t.check sign context head a b (target.raw.queries ++ source.raw.constraints) &&
  decide (t.node.system.count (target.raw.signs ++ source.raw.constraintSigns) = 1)

structure Reencoding {sign : E → Int} {context : Ctx}
    (source : Descriptor E Ctx sign context) (head : DensePoly E) (a b : Endpoint E) where
  target : Descriptor E Ctx sign context
  evidence : Replay E Ctx
  accepted : source.checkReencoding target head a b evidence = true

theorem Reencoding.check_eq {sign : E → Int} {context : Ctx}
    {source : Descriptor E Ctx sign context} {head : DensePoly E} {a b : Endpoint E}
    (r : Reencoding source head a b) :
    (r.target.raw.head = head ∧ r.target.raw.lower = a ∧ r.target.raw.upper = b) ∧
    ∃ h : r.evidence.check sign context head a b
        (r.target.raw.queries ++ source.raw.constraints) = true,
      (r.evidence.table h).count (r.target.raw.signs ++ source.raw.constraintSigns) = 1 := by
  have h := r.accepted
  simp only [Descriptor.checkReencoding, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, (r.evidence.table_lookup h.1.2 _).trans h.2⟩

/-- The actual accepted joint replay gives exactly one observation satisfying
both the target descriptor and every old-root constraint. -/
theorem Reencoding.count {sign : E → Int} {context : Ctx}
    {source : Descriptor E Ctx sign context} {head : DensePoly E} {a b : Endpoint E}
    (r : Reencoding source head a b) {xs : List (List Int)}
    (ho : Observations (r.target.raw.queries ++ source.raw.constraints).length xs)
    (hm : r.evidence.Interprets (r.target.raw.queries ++ source.raw.constraints).length xs) :
    xs.countP (fun x => decide (x = r.target.raw.signs ++ source.raw.constraintSigns)) = 1 := by
  obtain ⟨_, hc, hn⟩ := r.check_eq
  exact (r.evidence.table_count hc ho hm _).symm.trans hn

variable [Neg E] [Inv E]

/-- Re-encode by joint sign determination on the target domain. An invalid
target domain or no matching root returns `none`; failed internal invariants
remain separate diagnostics. The old interval is expressed by query signs,
so an old endpoint may be a root of the target head outside the selected root. -/
def Descriptor.buildReencoding {sign : E → Int} {context : Ctx}
    (source : Descriptor E Ctx sign context) (head : DensePoly E) (a b : Endpoint E) :
    Except BuildError (Option (Reencoding source head a b)) :=
  match Sturm.prepare sign head a b with
  | none => .ok none
  | some domain =>
    let raw : RawDescriptor E Ctx := ⟨context, head, a, b, [], []⟩
    let full := raw.full []
    match buildPrepared context domain (full.queries ++ source.raw.constraints) with
    | .error err => .error err
    | .ok t =>
      let candidates := (t.val.table t.property).rows.toList.filter fun row =>
        decide (row.1.drop full.queries.length = source.raw.constraintSigns)
      match candidates with
      | [] => .ok none
      | [(word, 1)] =>
        match Descriptor.build sign context (raw.full (word.take full.queries.length)) with
        | .error err => .error err
        | .ok (.error _) => .error .replay
        | .ok (.ok target) =>
          if h : source.checkReencoding target head a b t.val = true then .ok (some ⟨target, t.val, h⟩)
          else .error .replay
      | _ => .error .system

end Hex.SignDet

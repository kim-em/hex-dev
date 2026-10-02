/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerTransport
public import HexSignDetMathlib.Embedding

public section

namespace Hex.RealClosure.Tower.Model

variable {registry : BaseContext.Registry} {context : Context registry}
variable {K : Type u} {L : Type v}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
variable [Field L] [LinearOrder L] [DecidableEq L] [IsStrictOrderedRing L] [IsRealClosed L]

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
  [Field L] [LinearOrder L] [DecidableEq L] [IsStrictOrderedRing L] [IsRealClosed L] in
/-- A native model is determined by its interpretation of stored values. -/
theorem value_ext (left right : Model context K)
    (agree : ∀ a, left.value a = right.value a) : left = right := by
  cases left
  cases right
  cases funext agree
  rfl

/-- Adjoining a validated root commutes with an ordered ambient embedding.
The equality describes every actual stored child value, including general
nonmonic representatives; no syntax injectivity is assumed. -/
theorem map_adjoin (model : Model context K) (embedding : K →+* L)
    (ordered : StrictMono embedding)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (a : (context.adjoin descriptor).context.Value) :
    ((model.map embedding ordered).adjoin descriptor).value a =
      embedding ((model.adjoin descriptor).value a) := by
  rw [(model.map embedding ordered).adjoin_value, model.adjoin_value,
    (model.map embedding ordered).adjoin_generator, model.adjoin_generator]
  rw [SignDet.interpret_embedding model.value model.zero_iff
    (model.map embedding ordered).value (model.map embedding ordered).zero_iff
    embedding (fun _ => rfl)]
  rw [SignDet.Descriptor.root_map model.value model.zero_iff
    (model.map embedding ordered).value (model.map embedding ordered).zero_iff
    embedding ordered (fun _ => rfl) model.one model.add model.sub model.mul model.nat
    (model.map embedding ordered).one (model.map embedding ordered).add
    (model.map embedding ordered).sub (model.map embedding ordered).mul
    (model.map embedding ordered).nat model.sign (model.map embedding ordered).sign]
  exact Polynomial.eval_map_apply _ _

/-- Rebuilding the interpretation of a finite validated root suffix commutes
with the same ordered ambient embedding at every depth. -/
theorem map_extend {source : Context registry} (model : Model source K)
    (embedding : K →+* L) (ordered : StrictMono embedding) (suffix : Suffix source)
    (a : suffix.context.Value) :
    ((model.map embedding ordered).extend suffix).value a =
      embedding ((model.extend suffix).value a) := by
  induction suffix with
  | nil => rfl
  | root descriptor rest ih =>
    have same : (model.map embedding ordered).adjoin descriptor =
        (model.adjoin descriptor).map embedding ordered :=
      value_ext _ _ (model.map_adjoin embedding ordered descriptor)
    change (((model.map embedding ordered).adjoin descriptor).extend rest).value a = _
    rw [same]
    exact ih (model.adjoin descriptor) a

end Hex.RealClosure.Tower.Model

/-- info: 'Hex.RealClosure.Tower.Model.map_adjoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.map_adjoin

/-- info: 'Hex.RealClosure.Tower.Model.map_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.map_extend

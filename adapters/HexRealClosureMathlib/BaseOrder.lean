/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseStagedSubsequence
public import HexRealClosureMathlib.BaseModel
public import HexRealClosureMathlib.BaseMap
public import HexRealClosureMathlib.Ambient
public import Mathlib.Algebra.Order.Hom.Monoid

public section

namespace Hex.RealClosure.BaseContext

open OrderedFn OrderedFn.Oracle

variable {registry : Registry} {K : Type} [Lean.Grind.Field K] [DecidableEq K]
variable {sign : K → Int}

/-- The ordered interpretation of one actual native staged coefficient field.
Its Mathlib field keeps the native dictionary, and the order agrees with the
computed native sign. -/
structure Chain.Ordered (chain : Chain registry K sign) where
  order : LinearOrder K
  ordered : letI : Field K := HexPolyMathlib.fieldOfGrind
    letI := order
    IsStrictOrderedRing K
  sign : letI : Field K := HexPolyMathlib.fieldOfGrind
    letI := order
    ∀ a, sign a = (SignType.sign a : Int)

/-- A provider-derived real prefix obtains its order from its actual injective
real embedding. -/
noncomputable def RealContext.Interpretation.ordered
    {approx : K → Rat → Bounds} {nativeSign : K → Int}
    {parent : RealContext registry K approx nativeSign} (model : parent.Interpretation) :
    Chain.Ordered (.real parent.chain) := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : LinearOrder K := LinearOrder.lift' model.hom model.hom.injective
  refine ⟨inferInstance, ?_, ?_⟩
  · exact Function.Injective.isStrictOrderedRing model.hom
      (map_zero _) (map_one _) (map_add _) (map_mul _) (by intros; rfl) (by intros; rfl)
  · intro a
    rw [model.sign]
    have monotone : StrictMono model.hom := by intro a b hab; exact hab
    exact congrArg (fun s : SignType => (s : Int)) (monotone.sign_comp a)

/-- The next native fraction field has the Hahn order of a positive
infinitesimal over the entire preceding coefficient field. -/
noncomputable def Chain.Ordered.infinitesimal {parent : Chain registry K sign}
    (original : parent.Ordered) : parent.infinitesimal.Ordered := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : LinearOrder K := original.order
  letI : IsStrictOrderedRing K := original.ordered
  have compatible : Field.toGrindField (K := K) = (inferInstance : Lean.Grind.Field K) :=
    HexPolyMathlib.toGrind_fieldOfGrind
  refine ⟨InfinitesimalModel.linearOrder compatible,
    InfinitesimalModel.strictOrderedRing compatible, ?_⟩
  intro f
  exact Element.infinitesimal_orderSign compatible (Context.ofChain parent) original.sign ⟨f⟩

/-- Every provider-derived staged realization constructs its ordered native
coefficient model, retaining all real and infinitesimal predecessors. -/
noncomputable def Chain.Realization.ordered {chain : Chain registry K sign}
    (realization : chain.Realization registry) : chain.Ordered := by
  induction realization with
  | real parent model previous =>
    simpa only [RealContext.ofChain_chain] using model.ordered
  | infinitesimal parent previous ih => exact ih.infinitesimal

/-- Native sign preservation makes the same checked field hom strictly
monotone in the two constructed coefficient orders. -/
theorem FieldEmbedding.strictMono
    {L : Type} [Lean.Grind.Field L] [DecidableEq L] {targetSign : L → Int}
    {source : Chain registry K sign} {target : Chain registry L targetSign}
    (original : source.Ordered) (following : target.Ordered) (map : FieldEmbedding K L)
    (preserved : ∀ a, targetSign (map.value a) = sign a) :
    letI : Field K := HexPolyMathlib.fieldOfGrind
    letI : Field L := HexPolyMathlib.fieldOfGrind
    letI := original.order
    letI := following.order
    StrictMono map.hom := by
  let : Field K := HexPolyMathlib.fieldOfGrind
  let : Field L := HexPolyMathlib.fieldOfGrind
  let : LinearOrder K := original.order
  let : LinearOrder L := following.order
  let : IsStrictOrderedRing K := original.ordered
  let : IsStrictOrderedRing L := following.ordered
  apply (strictMono_iff_map_pos map.hom).mpr
  intro a positive
  have old : sign a = 1 := by
    rw [original.sign]
    exact congrArg (fun s : SignType => (s : Int)) (sign_eq_one_iff.mpr positive)
  have integer : (SignType.sign (map.hom a) : Int) = 1 := by
    rw [FieldEmbedding.hom_apply, ← following.sign, preserved, old]
  apply sign_eq_one_iff.mp
  cases result : SignType.sign (map.hom a) <;> simp_all

/-- The actual checked staged inclusion constructs a strictly monotone field
hom without any additional coefficient-agreement premise. -/
theorem Chain.Realization.embedding_mono
    {S : Type} [Lean.Grind.Field S] [DecidableEq S] {sourceSign : S → Int}
    {target : Chain registry K sign} (following : target.Realization registry)
    (source : Chain registry S sourceSign) (original : source.Realization registry)
    (map : FieldEmbedding S K)
    (produced : target.embedding? (.pack (Context.ofChain source)) = some map) :
    letI : Field S := HexPolyMathlib.fieldOfGrind
    letI : Field K := HexPolyMathlib.fieldOfGrind
    letI := original.ordered.order
    letI := following.ordered.order
    StrictMono map.hom :=
  map.strictMono original.ordered following.ordered
    (fun a => following.embedding_sign source original map produced a)

/-- Construct a real-closed ambient of the actual ordered native coefficient
field, using the existing ordered real-closure existence theorem. -/
noncomputable def Chain.Ordered.ambient {chain : Chain registry K sign}
    (model : chain.Ordered) :
    letI : Field K := HexPolyMathlib.fieldOfGrind
    letI := model.order
    Ambient K := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : LinearOrder K := model.order
  letI : IsStrictOrderedRing K := model.ordered
  exact Ambient.ofField K

/-- The same native base obtains its tower interpretation in the constructed
ambient; no coefficient interpretation is supplied by the caller. -/
noncomputable def Chain.Ordered.towerModel {chain : Chain registry K sign}
    (model : chain.Ordered) :
    letI : Field K := HexPolyMathlib.fieldOfGrind
    letI := model.order
    Tower.Model (Tower.Context.base (Context.ofChain chain)) model.ambient.Carrier := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : LinearOrder K := model.order
  let ambient := model.ambient
  have correct : ∀ a, sign a = (SignType.sign (ambient.inclusion a) : Int) := by
    intro a
    exact (model.sign a).trans (congrArg (fun s : SignType => (s : Int))
      (ambient.monotone.sign_comp a).symm)
  exact Tower.Model.base (Context.ofChain chain) ambient.inclusion correct

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.ordered

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.embedding_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.embedding_mono

/-- info: 'Hex.RealClosure.BaseContext.Chain.Ordered.towerModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Ordered.towerModel

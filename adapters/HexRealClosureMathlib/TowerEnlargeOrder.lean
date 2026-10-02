/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerEnlarge
public import HexRealClosure.TowerEnlargement
public import HexRealClosureMathlib.TowerRestriction
public import HexRealClosureMathlib.BaseBound
public import HexRealClosureMathlib.BaseAlgebraicity

public section

namespace Hex.RealClosure.Tower.Model

open scoped Hex.OrderedFn.Infinitesimal

variable {registry : BaseContext.Registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Restrict an arbitrary finite tower model to the algebraic real closure of
its actual initial coefficient field inside its old ambient interpretation. -/
@[expose] noncomputable def suffixRestrict {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    {S : Type v} [Field S] [LinearOrder S] [DecidableEq S]
    [IsStrictOrderedRing S] [IsRealClosed S]
    (reference : Model (Context.base base) S) (old : Model suffix.context K) :
    let initial := suffix.restrict reference old
    letI : Field B := HexPolyMathlib.fieldOfGrind
    letI : Algebra B K := (initial.baseHom base).toAlgebra
    Model suffix.context (Union.Carrier B K) := by
  let initial := suffix.restrict reference old
  letI : Field B := HexPolyMathlib.fieldOfGrind
  letI : Algebra B K := (initial.baseHom base).toAlgebra
  exact old.restrictUnion (suffix_algebraic base suffix reference old)

/-- Inclusion of the restricted model gives every original value exactly. -/
@[simp] theorem suffixRestrict_value {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    {S : Type v} [Field S] [LinearOrder S] [DecidableEq S]
    [IsStrictOrderedRing S] [IsRealClosed S]
    (reference : Model (Context.base base) S) (old : Model suffix.context K) :
    let initial := suffix.restrict reference old
    letI : Field B := HexPolyMathlib.fieldOfGrind
    letI : Algebra B K := (initial.baseHom base).toAlgebra
    ∀ a : suffix.context.Value, ((suffixRestrict base suffix reference old).value a : K) =
      old.value a := by
  intro initial
  intro a
  rfl

/-- The initial coefficient map of the restricted native tower is precisely
its relative algebraic union's base map. -/
theorem suffixRestrict_baseHom {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    {S : Type v} [Field S] [LinearOrder S] [DecidableEq S]
    [IsStrictOrderedRing S] [IsRealClosed S]
    (reference : Model (Context.base base) S) (old : Model suffix.context K) :
    let initial := suffix.restrict reference old
    letI : Field B := HexPolyMathlib.fieldOfGrind
    letI : Algebra B K := (initial.baseHom base).toAlgebra
    (suffix.restrict reference (suffixRestrict base suffix reference old)).baseHom base =
      algebraMap B (Union.Carrier B K) := by
  intro initial
  ext a
  rfl

/-- Enlarging the actual restricted tower produces an ambient algebraic over
the new native infinitesimal base, even when the old ambient itself has
transcendental elements over the initial coefficient field. -/
theorem suffixRestrict_algebraic {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    {S : Type v} [Field S] [LinearOrder S] [DecidableEq S]
    [IsStrictOrderedRing S] [IsRealClosed S]
    (reference : Model (Context.base base) S) (old : Model suffix.context K) :
    let initial := suffix.restrict reference old
    letI : Field B := HexPolyMathlib.fieldOfGrind
    letI : Algebra B K := (initial.baseHom base).toAlgebra
    ∀ ambient : Ambient (Hex.RationalFn (Union.Carrier B K)),
    let restricted := suffixRestrict base suffix reference old
    let coefficient := (suffix.restrict reference restricted).baseHom base
    letI : Field (Hex.RationalFn B) := HexPolyMathlib.fieldOfGrind
    letI : Algebra (Hex.RationalFn B) ambient.Carrier :=
      (Ambient.mappedNativeHom HexPolyMathlib.toGrind_fieldOfGrind coefficient ambient).toAlgebra
    Algebra.IsAlgebraic (Hex.RationalFn B) ambient.Carrier := by
  intro initial ambient
  letI : Field B := HexPolyMathlib.fieldOfGrind
  letI : Algebra B K := (initial.baseHom base).toAlgebra
  let coefficient := (suffix.restrict reference (suffixRestrict base suffix reference old)).baseHom base
  have coefficient_eq : coefficient = algebraMap B (Union.Carrier B K) :=
    suffixRestrict_baseHom base suffix reference old
  have algebraic : letI : Algebra B (Union.Carrier B K) := coefficient.toAlgebra;
      Algebra.IsAlgebraic B (Union.Carrier B K) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p, nonzero, root⟩ := Union.algebraic (B := B) (R := K) x
    refine ⟨p, nonzero, ?_⟩
    change p.eval₂ coefficient x = 0
    rw [coefficient_eq]
    exact root
  exact Ambient.mappedNative_algebraic HexPolyMathlib.toGrind_fieldOfGrind coefficient
    algebraic ambient

/-- Infinitesimality only over the actual initial coefficient map suffices
for every positive old tower value, by its local algebraic bound. -/
theorem suffix_infinitesimal {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    {S : Type v} [Field S] [LinearOrder S] [DecidableEq S]
    [IsStrictOrderedRing S] [IsRealClosed S]
    (reference : Model (Context.base base) S) (old : Model suffix.context K)
    {L : Type w} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (embedding : K →+* L) (ordered : StrictMono embedding) (parameter : L) :
    let initial := suffix.restrict reference old
    letI : Field B := HexPolyMathlib.fieldOfGrind
    (∀ b, 0 < initial.baseHom base b → parameter < embedding (initial.baseHom base b)) →
      ∀ a, 0 < old.value a → parameter < embedding (old.value a) := by
  intro initial small a positive
  letI : Field B := HexPolyMathlib.fieldOfGrind
  exact infinitesimal_lt_algebraic (initial.baseHom base) embedding ordered parameter small
    (old.value a) positive (suffix_algebraic base suffix reference old a)

end Hex.RealClosure.Tower.Model

namespace Hex.RealClosure.Tower.Conversion.Model

open scoped Hex.OrderedFn.Infinitesimal

variable {registry : BaseContext.Registry}
variable {R : Type u} [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R]

/-- The actual native new-base parameter denotes the ambient infinitesimal
used to interpret the rebuilt tower. -/
theorem infinitesimalMapped_parameter {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* R)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (ambient : Ambient (Hex.RationalFn R)) :
    (infinitesimalMapped base f hsign ambient).target.value (Conversion.parameter base) =
      ambient.inclusion (Hex.RationalFn.X : Hex.RationalFn R) := by
  exact infinitesimalMapped_X base f hsign ambient

end Hex.RealClosure.Tower.Conversion.Model

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

private theorem value_heq {source target : Context registry} (same : source = target)
    (original : Model source K) (actual : Model target K) (aligned : HEq actual original)
    (a : source.Value) (b : target.Value) (owned : HEq b a) :
    actual.value b = original.value a := by
  cases same
  cases eq_of_heq aligned
  cases eq_of_heq owned
  rfl

/-- The parameter stored in the returned rebuilt context agrees with the
actual new-base parameter under the aligned target interpretation. -/
theorem Rebuilt.parameter_value {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    {suffix : Suffix (Context.base base)} {context : Context registry}
    (target_eq : suffix.context = context)
    (rebuilt : Rebuilt (Conversion.infinitesimal base) suffix)
    (input : Model (Conversion.infinitesimal base).context K) (old : Model context K)
    (model : Conversion.Model (rebuilt.result.cast target_eq) old)
    (aligned : HEq model.target (input.extend rebuilt.suffix)) :
    model.target.value
      (_root_.cast (congrArg Context.Value (rebuilt.result.cast_spec target_eq).1.symm)
        (rebuilt.parameter base)) = input.value (Conversion.parameter base) := by
  have owned : HEq
      (_root_.cast (congrArg Context.Value (rebuilt.result.cast_spec target_eq).1.symm)
        (rebuilt.parameter base)) (rebuilt.suffix.embed (Conversion.parameter base)) :=
    (_root_.cast_heq _ _).trans (_root_.cast_heq _ _)
  exact (value_heq
    (rebuilt.context_eq.trans (rebuilt.result.cast_spec target_eq).1.symm)
    (input.extend rebuilt.suffix) model.target aligned _ _ owned).trans
      (input.extend_embed rebuilt.suffix _)

open scoped Hex.OrderedFn.Infinitesimal in
/-- The checked rebuilt context contains a positive native parameter below
every positive old tower value, through its actual returned conversion. -/
theorem Context.enlarge?_ordered {context : Context registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base)) (target_eq : suffix.context = context)
    {R : Type v} [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R]
    {S : Type w} [Field S] [LinearOrder S] [DecidableEq S]
    [IsStrictOrderedRing S] [IsRealClosed S]
    (reference : Model (Context.base base) S) (old : Model context R)
    (ambient : Ambient (Hex.RationalFn R)) :
    ∃ rebuilt : Rebuilt (Conversion.infinitesimal base) suffix,
      (Conversion.infinitesimal base).rebuild? suffix = some rebuilt ∧
        context.enlarge? = some (rebuilt.result.cast target_eq) ∧
        ∃ model : Conversion.Model (rebuilt.result.cast target_eq) (old.liftInfinitesimal ambient),
          let parameter := _root_.cast
            (congrArg Context.Value (rebuilt.result.cast_spec target_eq).1.symm)
            (rebuilt.parameter base)
          (rebuilt.result.cast target_eq).context.sign parameter = 1 ∧
            ∀ a, context.sign a = 1 → (rebuilt.result.cast target_eq).context.sign
              (parameter - (rebuilt.result.cast target_eq).value a) = -1 := by
  let initial := suffix.restrict reference (target_eq.symm ▸ old)
  let input := Conversion.Model.infinitesimalMapped base (initial.baseHom base)
    (Model.baseHom_sign base initial) ambient
  obtain ⟨rebuilt, produced, enlarged, model, aligned⟩ :=
    Context.enlarge?_constructed base suffix target_eq reference old ambient
  have parameter := (Rebuilt.parameter_value base target_eq rebuilt input.target
    (old.liftInfinitesimal ambient) model aligned).trans
      (Conversion.Model.infinitesimalMapped_parameter base (initial.baseHom base)
        (Model.baseHom_sign base initial) ambient)
  refine ⟨rebuilt, produced, enlarged, model, ?_, ?_⟩
  · rw [model.target.sign, parameter, sign_eq_one_iff.mpr (Ambient.X_pos ambient)]
    rfl
  · intro a positive
    have positiveValue : 0 < old.value a := by
      apply sign_eq_one_iff.mp
      have native := (old.sign a).symm.trans positive
      cases s : SignType.sign (old.value a) <;> simp_all
    have small := old.liftInfinitesimal_X_lt ambient a positiveValue
    rw [model.target.sign, model.target.sub, parameter, model.value,
      sign_eq_neg_one_iff.mpr (sub_neg.mpr small)]
    rfl

open scoped Hex.OrderedFn.Infinitesimal in
/-- Checked enlargement exposes its actual new parameter, its interpretation,
and the exact target model aligned with the actual rebuilt suffix. -/
theorem Context.enlargeWithParameter?_model {context : Context registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base)) (target_eq : suffix.context = context)
    {R : Type v} [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R]
    {S : Type w} [Field S] [LinearOrder S] [DecidableEq S]
    [IsStrictOrderedRing S] [IsRealClosed S]
    (reference : Model (Context.base base) S) (old : Model context R)
    (ambient : Ambient (Hex.RationalFn R)) :
    let initial := suffix.restrict reference (target_eq.symm ▸ old)
    let input := Conversion.Model.infinitesimalMapped base (initial.baseHom base)
      (Model.baseHom_sign base initial) ambient
    ∃ rebuilt : Rebuilt (Conversion.infinitesimal base) suffix,
      let result := rebuilt.enlargement base target_eq
      context.enlargeWithParameter? = some result ∧
        ∃ model : Conversion.Model result.conversion (old.liftInfinitesimal ambient),
          HEq model.target (input.target.extend rebuilt.suffix) ∧
          model.target.value result.parameter = ambient.inclusion Hex.RationalFn.X ∧
          result.conversion.context.sign result.parameter = 1 ∧
          ∀ a, context.sign a = 1 → result.conversion.context.sign
            (result.parameter - result.conversion.value a) = -1 := by
  intro initial input
  obtain ⟨rebuilt, produced, _, model, aligned⟩ :=
    Context.enlarge?_constructed base suffix target_eq reference old ambient
  obtain ⟨other, other_produced, _, _, positive, small⟩ :=
    Context.enlarge?_ordered base suffix target_eq reference old ambient
  have same : other = rebuilt := Option.some.inj (other_produced.symm.trans produced)
  subst other
  refine ⟨rebuilt, ?_, model, aligned, ?_, positive, small⟩
  · rw [Context.enlargeWithParameter?_eq base suffix target_eq, produced]
    rfl
  · exact (Rebuilt.parameter_value base target_eq rebuilt input.target
      (old.liftInfinitesimal ambient) model aligned).trans
        (Conversion.Model.infinitesimalMapped_parameter base (initial.baseHom base)
          (Model.baseHom_sign base initial) ambient)

/-- Native parameter order needs only a lawful reference interpretation of the
initial base; no caller-supplied old model or ambient field is required. -/
theorem Context.enlargeWithParameter?_ordered {context : Context registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base)) (target_eq : suffix.context = context)
    {S : Type v} [Field S] [LinearOrder S] [DecidableEq S]
    [IsStrictOrderedRing S] [IsRealClosed S]
    (reference : Model (Context.base base) S) :
    ∃ result : Enlargement context, context.enlargeWithParameter? = some result ∧
      result.conversion.context.sign result.parameter = 1 ∧
      ∀ a, context.sign a = 1 → result.conversion.context.sign
        (result.parameter - result.conversion.value a) = -1 := by
  obtain ⟨rebuilt, produced, _, _, _, positive, small⟩ :=
    Context.enlargeWithParameter?_model base suffix target_eq reference
      (target_eq ▸ reference.extend suffix) (Ambient.infinitesimal S)
  exact ⟨rebuilt.enlargement base target_eq, produced, positive, small⟩

open scoped Hex.OrderedFn.Infinitesimal in
/-- Restrict the actual old model, enlarge over its algebraic union, and retain
one returned parameter with value, native order and rebuilt-target agreement.
The same new-base map makes the whole enlarged ambient algebraic. -/
theorem Context.enlargeWithParameter?_algebraic
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign) (suffix : Suffix (Context.base base))
    {S : Type v} [Field S] [LinearOrder S] [DecidableEq S]
    [IsStrictOrderedRing S] [IsRealClosed S]
    (reference : Model (Context.base base) S) (old : Model suffix.context K) :
    let initial := suffix.restrict reference old
    letI : Field B := HexPolyMathlib.fieldOfGrind
    letI : Algebra B K := (initial.baseHom base).toAlgebra
    ∀ ambient : Ambient (Hex.RationalFn (Union.Carrier B K)),
      let restricted := Model.suffixRestrict base suffix reference old
      let coefficient := (suffix.restrict reference restricted).baseHom base
      let input := Conversion.Model.infinitesimalMapped base coefficient
        (Model.baseHom_sign base (suffix.restrict reference restricted)) ambient
      letI : Field (Hex.RationalFn B) := HexPolyMathlib.fieldOfGrind
      letI : Algebra (Hex.RationalFn B) ambient.Carrier :=
        (Ambient.mappedNativeHom HexPolyMathlib.toGrind_fieldOfGrind coefficient ambient).toAlgebra
      (∀ a, (restricted.value a : K) = old.value a) ∧
      Algebra.IsAlgebraic (Hex.RationalFn B) ambient.Carrier ∧
      ∃ rebuilt : Rebuilt (Conversion.infinitesimal base) suffix,
        let result := rebuilt.enlargement base rfl
        suffix.context.enlargeWithParameter? = some result ∧
          ∃ model : Conversion.Model result.conversion (restricted.liftInfinitesimal ambient),
            HEq model.target (input.target.extend rebuilt.suffix) ∧
            model.target.value result.parameter = ambient.inclusion Hex.RationalFn.X ∧
            result.conversion.context.sign result.parameter = 1 ∧
            ∀ a, suffix.context.sign a = 1 → result.conversion.context.sign
              (result.parameter - result.conversion.value a) = -1 := by
  intro initial ambient
  letI : Field B := HexPolyMathlib.fieldOfGrind
  letI : Algebra B K := (initial.baseHom base).toAlgebra
  refine ⟨Model.suffixRestrict_value base suffix reference old,
    Model.suffixRestrict_algebraic base suffix reference old ambient, ?_⟩
  exact Context.enlargeWithParameter?_model base suffix rfl reference
    (Model.suffixRestrict base suffix reference old) ambient

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Model.suffixRestrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.suffixRestrict

/-- info: 'Hex.RealClosure.Tower.Model.suffixRestrict_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.suffixRestrict_value

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.infinitesimalMapped_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Conversion.Model.infinitesimalMapped_parameter

/-- info: 'Hex.RealClosure.Tower.Rebuilt.parameter_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Rebuilt.parameter_value

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.enlarge?_ordered

/-- info: 'Hex.RealClosure.Tower.Model.suffixRestrict_baseHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.suffixRestrict_baseHom

/-- info: 'Hex.RealClosure.Tower.Model.suffixRestrict_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.suffixRestrict_algebraic

/-- info: 'Hex.RealClosure.Tower.Context.enlargeWithParameter?_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.enlargeWithParameter?_model

/-- info: 'Hex.RealClosure.Tower.Model.suffix_infinitesimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.suffix_infinitesimal

/-- info: 'Hex.RealClosure.Tower.Context.enlargeWithParameter?_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.enlargeWithParameter?_algebraic

/-- info: 'Hex.RealClosure.Tower.Context.enlargeWithParameter?_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.enlargeWithParameter?_ordered

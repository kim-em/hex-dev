/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.InversePacking
public import HexRealClosureMathlib.Packing
public import HexRealClosureMathlib.Algebraic
import all HexRealClosureMathlib.Packing
import all HexRealClosure.InversePacking

public section

namespace Hex.RealClosure.Algebraic.Packing
open Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent} {entry : Packing context}
variable [Field K] [DecidableEq K] [LinearOrder K]

/-- A checked inverse equation gives the actual field inverse at the selected
point. The only predecessor arithmetic premises are the reached polynomial
product and subtraction operations, together with zero and unit preservation.
No whole-field embedding, ambient model or closed-domain law is required. -/
theorem Inverse.eval_inv (record : Inverse entry) (read : E → K)
    (zero : read 0 = 0) (unit : read 1 = 1) (x : K)
    (product : Transport.Product read record.argument.polynomial entry.value.polynomial)
    (difference : Transport.Difference read
      (record.argument.polynomial * entry.value.polynomial) 1)
    (observed : signsAt (fun y : K => y) (fun _ => Iff.rfl)
      ([record.argument.polynomial,
        record.argument.polynomial * entry.value.polynomial - 1].map
          (Transport.polynomial read)) x = [record.argument.sign, 0]) :
    eval read x entry.value.polynomial = (eval read x record.argument.polynomial)⁻¹ := by
  have signs : (SignType.sign (eval read x record.argument.polynomial) : Int) =
      record.argument.sign ∧
      (SignType.sign (eval read x
        (record.argument.polynomial * entry.value.polynomial - 1)) : Int) = 0 := by
    simpa only [signsAt, List.map_cons, List.map_nil, List.cons.injEq, and_true, eval]
      using observed
  have nonzero : eval read x record.argument.polynomial ≠ 0 := by
    intro vanished
    apply record.nonzero
    rw [← signs.1, vanished]
    simp
  have vanished : eval read x
      (record.argument.polynomial * entry.value.polynomial - 1) = 0 := by
    apply sign_eq_zero_iff.mp
    cases sign : SignType.sign (eval read x
      (record.argument.polynomial * entry.value.polynomial - 1)) <;>
      simp [sign] at signs ⊢
  have multiplied : eval read x record.argument.polynomial *
      eval read x entry.value.polynomial = 1 := by
    unfold eval at vanished ⊢
    rw [Transport.Ring.polynomial_sub read zero _ _ difference.differences,
      Transport.Ring.polynomial_mul read zero _ _ product.products product.sums,
      Transport.polynomial_one read zero unit,
      interpret_sub (fun y : K => y) (fun _ => Iff.rfl) (fun _ _ => rfl),
      interpret_mul (fun y : K => y) (fun _ => Iff.rfl) (fun _ _ => rfl)
        (fun _ _ => rfl),
      interpret_one (fun y : K => y) (fun _ => Iff.rfl) rfl,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one] at vanished
    exact sub_eq_zero.mp vanished
  have reversed : eval read x entry.value.polynomial *
      eval read x record.argument.polynomial = 1 := (mul_comm _ _).trans multiplied
  calc
    eval read x entry.value.polynomial = eval read x entry.value.polynomial *
        (eval read x record.argument.polynomial * (eval read x record.argument.polynomial)⁻¹) := by
      rw [mul_inv_cancel₀ nonzero, mul_one]
    _ = (eval read x entry.value.polynomial * eval read x record.argument.polynomial) *
        (eval read x record.argument.polynomial)⁻¹ := by rw [mul_assoc]
    _ = (eval read x record.argument.polynomial)⁻¹ := by rw [reversed, one_mul]

/-- Reached finite coefficient operations and literal replays of one packing
and its inverse equation, retaining their exact independent query slices. -/
structure Inverse.Data (record : Inverse entry) (read : E → K) : Prop where
  packing : Transport.Finite.ReplayData read coeffSign (fun x : K => (SignType.sign x : Int))
    context.root.raw.head context.root.raw.lower context.root.raw.upper
    (context.root.raw.queries ++ [entry.representative, entry.original - entry.representative])
    entry.signs.evidence
  original : Transport.Difference read entry.original entry.representative
  inverse : Transport.Finite.ReplayData read coeffSign (fun x : K => (SignType.sign x : Int))
    context.root.raw.head context.root.raw.lower context.root.raw.upper
    (context.root.raw.queries ++
      [record.argument.polynomial, record.argument.polynomial * entry.value.polynomial - 1])
    record.signs.evidence
  product : Transport.Product read record.argument.polynomial entry.value.polynomial
  difference : Transport.Difference read (record.argument.polynomial * entry.value.polynomial) 1

/-- One selected point realizes every raw packing equation, inverse operation
and cached sign together. The predecessor's finite arithmetic and replay data
remain explicit; their recursive construction belongs to the tower exporter. -/
theorem Inverse.realize_many [IsStrictOrderedRing K] [IsRealClosed K]
    (entries : List (Packing context))
    (records : List (Σ entry : Packing context, Inverse entry)) (read : E → K)
    (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (packingData : ∀ entry ∈ entries,
      Transport.Finite.ReplayData read coeffSign (fun x : K => (SignType.sign x : Int))
        context.root.raw.head context.root.raw.lower context.root.raw.upper
        (context.root.raw.queries ++ [entry.representative, entry.original - entry.representative])
        entry.signs.evidence ∧
      Transport.Difference read entry.original entry.representative)
    (data : ∀ record ∈ records, Inverse.Data record.2 read) :
    ∃ x : K,
      x ∈ Tarski.rootsIn
        (interpret (fun y : K => y) (fun _ => Iff.rfl)
          (Transport.polynomial read context.root.raw.head))
        ((Transport.endpoint read context.root.raw.lower).map (fun y : K => y))
        ((Transport.endpoint read context.root.raw.upper).map (fun y : K => y)) ∧
      signsAt (fun y : K => y) (fun _ => Iff.rfl)
        (context.root.raw.queries.map (Transport.polynomial read)) x = context.root.raw.signs ∧
      (∀ entry ∈ entries, eval read x entry.value.polynomial = eval read x entry.original ∧
        (SignType.sign (eval read x entry.original) : Int) = entry.value.sign) ∧
      ∀ record ∈ records,
        eval read x record.1.value.polynomial = eval read x record.1.original ∧
        eval read x record.1.value.polynomial = (eval read x record.2.argument.polynomial)⁻¹ ∧
        (SignType.sign (eval read x record.1.value.polynomial) : Int) = record.1.value.sign ∧
        (SignType.sign (eval read x record.2.argument.polynomial) : Int) = record.2.argument.sign := by
  let mapped := Transport.Finite.checkedDescriptor read zero unit (fun c : Ctx => c)
    coeffSign (fun x : K => (SignType.sign x : Int)) parent context.root descriptorData
  let point := mapped.root (fun y : K => y) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have raw : mapped.raw = Transport.descriptor read (fun c : Ctx => c) context.root.raw :=
    Transport.Finite.checkedDescriptor_raw read zero unit (fun c : Ctx => c)
      coeffSign _ parent context.root descriptorData
  have queries := Transport.Finite.descriptor_queries read zero (fun c : Ctx => c)
    context.root.raw descriptorData.derivatives descriptorData.head
  have spec := mapped.root_spec (fun y : K => y) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  change point ∈ _ ∧ _ at spec
  rw [raw, queries] at spec
  simp only [Transport.descriptor] at spec
  refine ⟨point, spec.1, spec.2, ?_, ?_⟩
  · intro entry member
    have observed := (Transport.Finite.selected_signs read zero unit (fun c : Ctx => c)
      coeffSign parent context.root descriptorData _ entry.signs
        (packingData entry member).1).trans entry.observed
    have equal := eval_original entry read zero point (packingData entry member).2 observed
    refine ⟨equal, ?_⟩
    rw [← equal]
    exact eval_sign entry read zero point observed
  intro record member
  have packing := (Transport.Finite.selected_signs read zero unit (fun c : Ctx => c)
    coeffSign parent context.root descriptorData _ record.1.signs
      (data record member).packing).trans record.1.observed
  have inverse := (Transport.Finite.selected_signs read zero unit (fun c : Ctx => c)
    coeffSign parent context.root descriptorData _ record.2.signs
      (data record member).inverse).trans record.2.observed
  have argument : (SignType.sign (eval read point record.2.argument.polynomial) : Int) =
      record.2.argument.sign := by
    have pair : (SignType.sign (eval read point record.2.argument.polynomial) : Int) =
        record.2.argument.sign ∧
        (SignType.sign (eval read point
          (record.2.argument.polynomial * record.1.value.polynomial - 1)) : Int) = 0 := by
      simpa only [signsAt, List.map_cons, List.map_nil, List.cons.injEq, and_true, eval]
        using inverse
    exact pair.1
  exact ⟨eval_original record.1 read zero point (data record member).original packing,
    record.2.eval_inv read zero unit point (data record member).product
      (data record member).difference inverse,
    eval_sign record.1 read zero point packing, argument⟩

end Hex.RealClosure.Algebraic.Packing

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.eval_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.eval_inv

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.realize_many' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.realize_many

namespace Hex.RealClosure.Algebraic.Packing
open Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- The inverse replay producer succeeds for the actual nonzero operand and
native candidate under a lawful predecessor interpretation. Its sign query
and gcd/cofactor equations are proved; successful production is not a premise.
This does not construct a finite predecessor interpretation from an inventory. -/
theorem Inverse.build?_success
    (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
    (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
    (hs : ∀ a b, f (a - b) = f a - f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (hnat : ∀ n : Nat, f (n : E) = (n : K))
    (hsign : ∀ a, coeffSign a = (SignType.sign (f a) : Int))
    (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
    (hd : ∀ a b, f (a / b) = f a / f b)
    (argument : Element context) (entry : Packing context)
    (nonzero : argument.sign ≠ 0) (candidate : entry.original = argument.inverseCandidate) :
    ∃ record, Inverse.build? argument entry = .ok record := by
  have valueNonzero : argument.denote f hz h1 ha hs hm hnat hsign ≠ 0 := by
    intro vanished
    apply nonzero
    rw [argument.sign_spec f hz h1 ha hs hm hnat hsign hn hi, vanished]
    simp only [_root_.sign_zero, SignType.coe_zero]
  have inverseValue : entry.value.denote f hz h1 ha hs hm hnat hsign =
      (argument.denote f hz h1 ha hs hm hnat hsign)⁻¹ := by
    rw [entry.native, Element.denote_ofPoly f hz h1 ha hs hm hnat hsign hn hi, candidate]
    exact argument.candidate_spec f hz h1 ha hs hm hnat hsign hi hd valueNonzero
  let query := argument.polynomial * entry.value.polynomial - 1
  have equation : context.evalPoly f hz h1 ha hs hm hnat hsign query = 0 := by
    unfold query Context.evalPoly
    rw [interpret_sub f hz hs, interpret_mul f hz ha hm, interpret_one f hz h1,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one]
    change argument.denote f hz h1 ha hs hm hnat hsign *
      entry.value.denote f hz h1 ha hs hm hnat hsign - 1 = 0
    rw [inverseValue, mul_inv_cancel₀ valueNonzero, sub_self]
  obtain ⟨signs, produced⟩ := context.root.buildSigns_success
    f hz h1 ha hs hm hnat hsign hn hi [argument.polynomial, query]
  have observed : signs.values.toList = [argument.sign, 0] := by
    rw [signs.values_at_root f hz h1 ha hs hm hnat hsign]
    simp only [signsAt, List.map_cons, List.map_nil]
    change [(SignType.sign (argument.denote f hz h1 ha hs hm hnat hsign) : Int),
      (SignType.sign (context.evalPoly f hz h1 ha hs hm hnat hsign query) : Int)] = _
    rw [← argument.sign_spec f hz h1 ha hs hm hnat hsign hn hi, equation]
    simp only [_root_.sign_zero, SignType.coe_zero]
  change context.root.buildSigns
    [argument.polynomial, argument.polynomial * entry.value.polynomial - 1] = .ok signs at produced
  simp [Inverse.build?, context.buildSigns_eq, produced, bind, Except.bind,
    Inverse.make?, nonzero, candidate, observed, pure, Except.pure]

end Hex.RealClosure.Algebraic.Packing

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.build?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.build?_success

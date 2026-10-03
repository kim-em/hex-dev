/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SignFacts
public meta import HexRealClosureMathlib.SignFacts
public import HexRealClosureMathlib.SignCodecConformance
public meta import HexRealClosureMathlib.SignCodecConformance
public meta import HexSignDet.CrossCheck
public meta import HexSignDetMathlib.GraphSignsConformance
import all HexRealClosure.Algebraic
import all HexSignDet.Descriptor
import all HexPoly.Euclid.DivGcd
import all HexRealClosure.SignCodec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json

public section

namespace Hex.RealClosure.Algebraic.SignFactsConformance

open Hex.SignDet Hex.SignDet.Conformance
open Hex.SignDetMathlib.GraphSignsConformance
open Hex.SignDet.CrossCheck
open CoefficientSignsConformance PackingConformance

theorem rational_sign (x : Rat) :
    Sturm.orderSign x = (SignType.sign (x : ℝ) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono x).symm

/-- The interpretation appears only in erased correctness proofs. The
executable reader selects supplied graph rows rather than producing signs. -/
@[expose] def readFact (p : DensePoly Rat) (s : Int)
    (memo : Array (Dag.Checked Sturm.orderSign 7 source.raw.head
      source.raw.lower source.raw.upper)) (index : Nat) : Option (SignFact context) :=
  context.readSignFact? (fun q : Rat => (q : ℝ))
    (fun _ => Rat.cast_eq_zero) (by simp)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) rational_sign
    (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _) p s memo index

/-- Distinct stored representatives use the same checked reduced-query row;
the decoder preserves each original polynomial literally. -/
@[expose] def sharedReaderPass : Bool :=
  (do
    let memo ← full.validate? Sturm.orderSign 7 source.raw.head source.raw.lower source.raw.upper
    let storedFact ← readFact stored 1 memo 0
    let smallFact ← readFact (2 * Sturm.Fixtures.x) 1 memo 0
    let reader := Element.signCodec ValueCodec.rat [storedFact, smallFact]
    let decoded ← (reader.decode ((Element.codec ValueCodec.rat).encode literal)).toOption
    let decodedSmall ← (reader.decode ((Element.codec ValueCodec.rat).encode small)).toOption
    pure (decoded == literal && decodedSmall == small &&
      storedFact.polynomial == stored && smallFact.polynomial == 2 * Sturm.Fixtures.x &&
      (readFact stored (-1) memo 0).isNone &&
      (readFact stored 0 memo 0).isNone &&
      (readFact (stored + 1) 1 memo 0).isNone &&
      (readFact stored 1 memo 1).isNone && (readFact stored 1 memo 3).isNone &&
      (readFact stored 1 #[] 0).isNone)) == some true

#guard sharedReaderPass

set_option maxRecDepth 32768 in
@[expose] def leafMemo : Array (Dag.Checked Sturm.orderSign 7 source.raw.head
    source.raw.lower source.raw.upper) :=
  #[⟨.leaf firstNode, by
    simp only [source_raw, Replay.check, Node.check_eq, checkMoment_eq, queryPoly,
      Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
      ← Array.all_toList, Array.toList_range]
    decide +kernel⟩]

set_option maxRecDepth 32768 in
private theorem query_eq : context.queryPoly stored = 2 * Sturm.Fixtures.x := by
  simp only [Context.queryPoly, Context.queryRemainder, context,
    Context.root_adjoin, source_raw, stored, singletonRaw, DensePoly.pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
theorem selected_kernel :
    (SelectedSigns.readMemo? context.root [context.queryPoly stored] #v[1] leafMemo 0).isSome = true ∧
    (SelectedSigns.readMemo? context.root [context.queryPoly stored] #v[-1] leafMemo 0).isSome = false := by
  rw [query_eq]
  simp only [leafMemo, context, Context.root_adjoin, source, Descriptor.ofTable,
    SelectedSigns.readMemo?, SelectedSigns.ofMemo?, Dag.bindDomain?, Dag.select?]
  decide +kernel

theorem literal_fact_kernel :
    (readFact stored 1 leafMemo 0).map (fun fact => (fact.polynomial, fact.sign)) =
      some (stored, 1) ∧
    (readFact stored (-1) leafMemo 0).isNone = true := by
  have accept (s : Int) := Context.readSignFact_accept
    (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero) (by simp)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) rational_sign
    (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _) context stored s leafMemo 0
  have good : (readFact stored 1 leafMemo 0).isSome = true := (accept 1).trans selected_kernel.1
  have bad : (readFact stored (-1) leafMemo 0).isSome = false := (accept (-1)).trans selected_kernel.2
  constructor
  · cases h : readFact stored 1 leafMemo 0 with
    | none => simp [h] at good
    | some fact =>
      have fields := Context.readSignFact_fields
        (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero) (by simp)
        (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
        (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) rational_sign
        (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _) context stored 1 leafMemo 0 fact h
      simp only [Option.map_some, fields.1, fields.2]
  · cases h : readFact stored (-1) leafMemo 0 <;> simp_all

/-- info: 'Hex.RealClosure.Algebraic.Context.readSignFact?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Context.readSignFact?

/-- info: 'Hex.RealClosure.Algebraic.SignFactsConformance.literal_fact_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms literal_fact_kernel

end Hex.RealClosure.Algebraic.SignFactsConformance

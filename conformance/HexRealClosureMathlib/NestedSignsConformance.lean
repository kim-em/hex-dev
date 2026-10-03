/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.PackingConformance
public meta import HexRealClosureMathlib.PackingConformance
public import HexRealClosureMathlib.AlgebraicTower
public meta import HexRealClosureMathlib.CoefficientSignsConformance
import all HexRealClosure.Algebraic
import all HexPoly.Euclid.DivGcd

public section

namespace Hex.RealClosure.Algebraic.NestedSignsConformance

open Hex.SignDet Hex.SignDet.Conformance
open CoefficientSignsConformance PackingConformance
open scoped Hex

@[expose] def endpointQuery : DensePoly Rat := 2 * Sturm.Fixtures.x - 1

@[expose] def endpointMoment : TarskiCertificate Rat Rat Nat :=
  {singletonQuery with
    queryPoly := endpointQuery
    remainders := {
      chain := #[Sturm.Fixtures.p, 2 - Sturm.Fixtures.x, -1]
      degrees := #[2, 1, 0]
      initial := ⟨1, 4, 2⟩
      steps := #[⟨1, -Sturm.Fixtures.x - 2, 3⟩]
      terminal := some (1, Sturm.Fixtures.x - 2)}
    lowerSigns := #[-1, 1, -1]
    upperSigns := #[1, 0, -1]
    lowerVariations := 2
    upperVariations := 1}

@[expose] def endpointSquare : TarskiCertificate Rat Rat Nat :=
  {singletonQuery with
    queryPoly := endpointQuery * endpointQuery
    remainders := {
      chain := #[Sturm.Fixtures.p, 5 * Sturm.Fixtures.x - 4, 1]
      degrees := #[2, 1, 0]
      initial := ⟨1, 8 * Sturm.Fixtures.x - 8, 2⟩
      steps := #[⟨25, 5 * Sturm.Fixtures.x + 4, 9⟩]
      terminal := some (1, 5 * Sturm.Fixtures.x - 4)}
    lowerSigns := #[-1, -1, 1]
    upperSigns := #[1, 1, 1]}

@[expose] def endpointNode : Node Rat Nat :=
  {selectedNode with
    queries := [endpointQuery]
    moments := #v[singletonQuery, endpointMoment, endpointSquare]}

set_option maxRecDepth 32768 in
theorem endpoint_checked :
    source.checkSigns [endpointQuery] #v[1] (.leaf endpointNode) = true := by
  simp only [Descriptor.checkSigns, source_raw, RawDescriptor.checkSigns,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

private theorem query_eq : context.queryPoly endpointQuery = endpointQuery := by
  simp only [Context.queryPoly, context, Context.root_adjoin, source_raw, singletonRaw]
  decide +kernel

private theorem rational_sign (x : Rat) :
    Sturm.orderSign x = (SignType.sign (x : ℝ) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono x).symm

theorem endpoint_sign : context.signPoly endpointQuery = 1 := by
  let signs : SelectedSigns context.root [context.queryPoly endpointQuery] :=
    ⟨#v[1], .leaf endpointNode, by
      rw [query_eq]
      simpa only [context, Context.root_adjoin] using endpoint_checked⟩
  have h := context.signPoly_checked (fun q : Rat => (q : ℝ))
    (fun _ => Rat.cast_eq_zero) (by simp)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) rational_sign
    (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _) endpointQuery signs
  simpa [signs, SelectedSigns.value] using h

@[expose] def facts : List (SignFact context) :=
  PackingConformance.facts ++ [⟨endpointQuery, 1, endpoint_sign⟩]

@[expose] def rational (a : Rat) : Element context :=
  Element.pack reduction reduction_eq facts (DensePoly.C a)

/-- The literal leading coefficient denotes two but retains its unreduced
degree-two polynomial. The new selected root is one half. -/
@[expose] def linearHead : DensePoly (Element context) :=
  DensePoly.ofCoeffs #[rational (-1), literal]

@[expose] def unitPoly : DensePoly (Element context) :=
  DensePoly.ofCoeffs #[rational 1]

@[expose] def linearChain : SignedRemainderChain (Element context) where
  chain := #[linearHead, unitPoly]
  degrees := #[1, 0]
  initial := ⟨rational 1, 0, literal⟩
  steps := #[]
  terminal := some (rational 1, linearHead)

@[expose] def linearCount : TarskiCertificate (Element context) (Element context) Nat where
  context := 8
  head := linearHead
  queryPoly := unitPoly
  lower := .finite (rational 0)
  upper := .finite (rational 1)
  squarefree := linearChain
  remainders := linearChain
  lowerSigns := #[-1, 1]
  upperSigns := #[1, 1]
  lowerVariations := 1
  upperVariations := 0
  value := 1

@[expose] def linearNode : Node (Element context) Nat where
  context := 8
  head := linearHead
  lower := .finite (rational 0)
  upper := .finite (rational 1)
  queries := []
  size := 1
  system := singletonNode.system
  moments := #v[linearCount]
  basis := singletonNode.basis

@[expose] def linearRaw : RawDescriptor (Element context) Nat :=
  ⟨8, linearHead, .finite (rational 0), .finite (rational 1), [], []⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem linear_cached :
    letI := Element.cachedOne reduction reduction_eq facts
    letI := Element.cachedAdd reduction reduction_eq facts
    letI := Element.cachedSub reduction reduction_eq facts
    letI := Element.cachedMul reduction reduction_eq facts
    letI := Element.cachedNatCast reduction reduction_eq facts
    linearRaw.check Element.sign 8 (.leaf linearNode) = true := by
  simp only [RawDescriptor.check, Replay.check, Node.check_eq, checkMoment_eq,
    queryPoly, Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

theorem linear_checked : linearRaw.check Element.sign 8 (.leaf linearNode) = true := by
  have h := linear_cached
  rw [Element.cachedOne_eq reduction reduction_eq facts,
    Element.cachedAdd_eq reduction reduction_eq facts,
    Element.cachedSub_eq reduction reduction_eq facts,
    Element.cachedMul_eq reduction reduction_eq facts,
    Element.cachedNatCast_eq reduction reduction_eq facts] at h
  exact h

@[expose] def root : Descriptor (Element context) Nat Element.sign 8 := by
  have h := RawDescriptor.check_eq linear_checked
  have hc : (Replay.leaf linearNode).check Element.sign 8 linearRaw.head
      linearRaw.lower linearRaw.upper linearRaw.queries = true := by
    obtain ⟨hc, _⟩ := h.2.2
    exact hc
  exact Descriptor.ofTable linearRaw (.leaf linearNode) h.1 h.2.1 hc (by
    obtain ⟨_, hone⟩ := h.2.2
    exact hone)

theorem root_raw : root.raw = linearRaw := by
  simp only [root, Descriptor.ofTable_raw]

@[expose] def next := context.extend root

@[expose] def nextQuery : DensePoly (Element context) :=
  DensePoly.ofCoeffs #[rational 0, rational 1]

set_option maxRecDepth 32768 in
theorem next_query : next.queryPoly nextQuery = unitPoly := by
  simp only [Context.queryPoly, Context.queryRemainder, next, Context.extend,
    Context.root_adjoin, root_raw, linearRaw]
  have h1 := Element.cachedOne_eq reduction reduction_eq facts
  have ha := Element.cachedAdd_eq reduction reduction_eq facts
  have hs := Element.cachedSub_eq reduction reduction_eq facts
  have hm := Element.cachedMul_eq reduction reduction_eq facts
  dsimp only [inferInstance] at h1 ha hs hm
  rw [← h1, ← ha, ← hs, ← hm]
  simp only [DensePoly.pseudoDivMod, ← Array.foldl_toList, Array.toList_range]
  decide +kernel

@[expose] def queryNode : Node (Element context) Nat :=
  {linearNode with
    queries := [unitPoly]
    size := 3
    system := selectedNode.system
    moments := #v[linearCount, linearCount, linearCount]
    reductions := #v[none, none, none]
    basis := selectedNode.basis}

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem query_cached :
    letI := Element.cachedOne reduction reduction_eq facts
    letI := Element.cachedAdd reduction reduction_eq facts
    letI := Element.cachedSub reduction reduction_eq facts
    letI := Element.cachedMul reduction reduction_eq facts
    letI := Element.cachedNatCast reduction reduction_eq facts
    linearRaw.checkSigns Element.sign 8 [unitPoly] #v[1] (.leaf queryNode) = true := by
  simp only [RawDescriptor.checkSigns, Replay.check, Node.check_eq, checkMoment_eq,
    queryPoly, Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

theorem query_checked : root.checkSigns [unitPoly] #v[1] (.leaf queryNode) = true := by
  have h := query_cached
  rw [Element.cachedOne_eq reduction reduction_eq facts,
    Element.cachedAdd_eq reduction reduction_eq facts,
    Element.cachedSub_eq reduction reduction_eq facts,
    Element.cachedMul_eq reduction reduction_eq facts,
    Element.cachedNatCast_eq reduction reduction_eq facts] at h
  simpa only [Descriptor.checkSigns, root_raw] using h

/-- The shared checker validates both stored entries before selecting the
second entry. Its coefficient signs come from the same finite lower-root facts
as the individual tree checks. -/
@[expose] def graph : Dag (Element context) Nat :=
  ⟨#[⟨linearNode, none⟩, ⟨queryNode, none⟩], 1⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem graph_cached :
    letI := Element.cachedOne reduction reduction_eq facts
    letI := Element.cachedAdd reduction reduction_eq facts
    letI := Element.cachedSub reduction reduction_eq facts
    letI := Element.cachedMul reduction reduction_eq facts
    letI := Element.cachedNatCast reduction reduction_eq facts
    graph.check Element.sign 8 linearHead linearRaw.lower linearRaw.upper [unitPoly] = true := by
  simp only [Dag.check, Dag.replay_eq, Dag.step_eq, Replay.check, Node.check_eq,
    checkMoment_eq, queryPoly, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

theorem graph_checked :
    graph.check Element.sign 8 linearHead linearRaw.lower linearRaw.upper [unitPoly] = true := by
  have h := graph_cached
  rw [Element.cachedOne_eq reduction reduction_eq facts,
    Element.cachedAdd_eq reduction reduction_eq facts,
    Element.cachedSub_eq reduction reduction_eq facts,
    Element.cachedMul_eq reduction reduction_eq facts,
    Element.cachedNatCast_eq reduction reduction_eq facts] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
/-- The kernel retains both literal nodes at their original indices, so
several selections can use one checked graph. -/
theorem graph_memo_cached :
    letI := Element.cachedOne reduction reduction_eq facts
    letI := Element.cachedAdd reduction reduction_eq facts
    letI := Element.cachedSub reduction reduction_eq facts
    letI := Element.cachedMul reduction reduction_eq facts
    letI := Element.cachedNatCast reduction reduction_eq facts
    (graph.validate? Element.sign 8 linearHead linearRaw.lower linearRaw.upper).map
      (fun memo => memo.map (fun checked => checked.value.node)) =
        some #[linearNode, queryNode] := by
  simp only [Dag.validate?, Dag.step_cache, Dag.step_eq, Replay.check, Node.check_eq,
    checkMoment_eq, queryPoly, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

theorem graph_memo :
    (graph.validate? Element.sign 8 linearHead linearRaw.lower linearRaw.upper).map
      (fun memo => memo.map (fun checked => checked.value.node)) =
        some #[linearNode, queryNode] := by
  have h := graph_memo_cached
  rw [Element.cachedOne_eq reduction reduction_eq facts,
    Element.cachedAdd_eq reduction reduction_eq facts,
    Element.cachedSub_eq reduction reduction_eq facts,
    Element.cachedMul_eq reduction reduction_eq facts,
    Element.cachedNatCast_eq reduction reduction_eq facts] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
/-- A false unreachable entry still rejects the whole graph. Forward edges,
missing selected entries, changed endpoints and mismatched root queries also
reject when checked with supplied lower-level facts. -/
theorem graph_rejected :
    letI := Element.cachedOne reduction reduction_eq facts
    letI := Element.cachedAdd reduction reduction_eq facts
    letI := Element.cachedSub reduction reduction_eq facts
    letI := Element.cachedMul reduction reduction_eq facts
    letI := Element.cachedNatCast reduction reduction_eq facts
    (⟨#[⟨{linearNode with context := 9}, none⟩, ⟨queryNode, none⟩], 1⟩ :
      Dag (Element context) Nat).check Element.sign 8 linearHead
        linearRaw.lower linearRaw.upper [unitPoly] = false ∧
    (⟨#[⟨linearNode, some (0, 0)⟩, ⟨queryNode, none⟩], 1⟩ :
      Dag (Element context) Nat).check Element.sign 8 linearHead
        linearRaw.lower linearRaw.upper [unitPoly] = false ∧
    ({graph with root := 2}).check Element.sign 8 linearHead
      linearRaw.lower linearRaw.upper [unitPoly] = false ∧
    graph.check Element.sign 8 linearHead linearRaw.lower
      (.finite (rational 2)) [unitPoly] = false ∧
    ({graph with root := 0}).check Element.sign 8 linearHead
      linearRaw.lower linearRaw.upper [unitPoly] = false := by
  simp only [Dag.check, Dag.replay_eq, Dag.step_eq, Replay.check, Node.check_eq,
    checkMoment_eq, queryPoly, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

noncomputable def embedding : Element context → ℝ :=
  Element.denote (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero) (by simp)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) rational_sign

theorem next_sign : next.signPoly nextQuery = 1 := by
  let signs : SelectedSigns next.root [next.queryPoly nextQuery] :=
    ⟨#v[1], .leaf queryNode, by
      rw [next_query]
      simpa only [next, Context.extend, Context.root_adjoin] using query_checked⟩
  have h := next.signPoly_checked embedding
    (Element.denote_eq_zero (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_one (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_add (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_sub (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_mul (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_nat (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.sign_spec (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_neg (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_inv (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _)
      (fun _ _ => Rat.cast_div _ _)) nextQuery signs
  simpa [signs, SelectedSigns.value] using h

@[expose] def nextLiteral : Element next :=
  Element.restore nextQuery 1 next_sign (by decide +kernel)

theorem next_literal : nextLiteral.sign = 1 ∧ nextLiteral.polynomial = nextQuery := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem rejected_cached :
    letI := Element.cachedOne reduction reduction_eq facts
    letI := Element.cachedAdd reduction reduction_eq facts
    letI := Element.cachedSub reduction reduction_eq facts
    letI := Element.cachedMul reduction reduction_eq facts
    letI := Element.cachedNatCast reduction reduction_eq facts
    linearRaw.checkSigns Element.sign 8 [unitPoly] #v[-1] (.leaf queryNode) = false ∧
    linearRaw.checkSigns Element.sign 9 [unitPoly] #v[1] (.leaf queryNode) = false ∧
    ({linearRaw with upper := .finite (rational 2)}).checkSigns
      Element.sign 8 [unitPoly] #v[1] (.leaf queryNode) = false := by
  simp only [RawDescriptor.checkSigns, Replay.check, Node.check_eq, checkMoment_eq,
    queryPoly, Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
example :
    letI := Element.cachedAdd reduction reduction_eq PackingConformance.facts
    letI := Element.cachedMul reduction reduction_eq PackingConformance.facts
    rational (-1) + literal * rational 1 = (Element.missing endpointQuery).val := by
  let input := (rational (-1)).polynomial +
    ((Element.cachedMul reduction reduction_eq PackingConformance.facts).mul literal
      (rational 1)).polynomial
  change Element.pack reduction reduction_eq PackingConformance.facts input = _
  have hp : input = endpointQuery := by decide +kernel
  rw [← hp]
  apply Element.pack_missing
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
example : True := by
  fail_if_success
    have :
        letI := Element.cachedOne reduction reduction_eq PackingConformance.facts
        letI := Element.cachedAdd reduction reduction_eq PackingConformance.facts
        letI := Element.cachedSub reduction reduction_eq PackingConformance.facts
        letI := Element.cachedMul reduction reduction_eq PackingConformance.facts
        letI := Element.cachedNatCast reduction reduction_eq PackingConformance.facts
        linearRaw.check Element.sign 8 (.leaf linearNode) = true := by
      simp only [RawDescriptor.check, Replay.check, Node.check_eq, checkMoment_eq,
        queryPoly, Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
        ← Array.all_toList, Array.toList_range]
      decide +kernel
  trivial

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
/-- Removing the sign of the exact endpoint polynomial blocks graph proof
assembly, just as it blocks the individual tree check. -/
example : True := by
  fail_if_success
    have :
        letI := Element.cachedOne reduction reduction_eq PackingConformance.facts
        letI := Element.cachedAdd reduction reduction_eq PackingConformance.facts
        letI := Element.cachedSub reduction reduction_eq PackingConformance.facts
        letI := Element.cachedMul reduction reduction_eq PackingConformance.facts
        letI := Element.cachedNatCast reduction reduction_eq PackingConformance.facts
        graph.check Element.sign 8 linearHead linearRaw.lower linearRaw.upper [unitPoly] = true := by
      simp only [Dag.check, Dag.replay_eq, Dag.step_eq, Replay.check, Node.check_eq,
        checkMoment_eq, queryPoly, Sturm.check, TarskiCertificate.check_eq,
        SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
      decide +kernel
  trivial

#guard graph.check Element.sign 8 linearHead linearRaw.lower linearRaw.upper [unitPoly]

/-- info: 'Hex.RealClosure.Algebraic.NestedSignsConformance.graph_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graph_checked

/-- info: 'Hex.RealClosure.Algebraic.NestedSignsConformance.graph_memo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graph_memo

#guard linearRaw.check Element.sign 8 (.leaf linearNode)
#guard root.checkSigns [unitPoly] #v[1] (.leaf queryNode)
#guard next.signPoly nextQuery == 1

/-- info: 'Hex.RealClosure.Algebraic.NestedSignsConformance.linear_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms linear_checked

/-- info: 'Hex.RealClosure.Algebraic.NestedSignsConformance.next_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms next_sign

end Hex.RealClosure.Algebraic.NestedSignsConformance

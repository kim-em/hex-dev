/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ContextOperations
public import HexRealClosureTheory.CoefficientSignsConformance
import all HexRealClosure.Algebraic
import all HexRealRoots.SignedRemainderChain
import all HexSignDet.Descriptor
import all HexSignDet.QueryHandle

public section

namespace Hex.RealClosure.Algebraic.ContextOperationsConformance

open CoefficientSignsConformance

abbrev sourceUnit : DensePoly Rat :=
  @One.one (DensePoly Rat) (@DensePoly.instOne Rat _ _ (inferInstance : One Rat))

set_option maxRecDepth 32768 in
theorem source_chain :
    SignedRemainderChain.build Sturm.orderSign (Sturm.normalize Sturm.orderSign)
      Sturm.Fixtures.p sourceUnit = Sturm.Fixtures.literalChain := by
  have derivative : sourceUnit * Sturm.Fixtures.p.derivative =
      2 * Sturm.Fixtures.x := by decide +kernel
  have initial : DensePoly.positivePseudoDiv Sturm.orderSign
      (2 * Sturm.Fixtures.x) Sturm.Fixtures.p = ⟨1, 0, 2 * Sturm.Fixtures.x⟩ := by
    have smaller : (2 * Sturm.Fixtures.x).size < Sturm.Fixtures.p.size := by decide +kernel
    simp [DensePoly.positivePseudoDiv, DensePoly.pseudoExponent, smaller,
      DensePoly.pseudoDiv_of_size_lt _ _ smaller]
  simp only [SignedRemainderChain.build, derivative, initial]
  have normalized : Sturm.normalize Sturm.orderSign (2 * Sturm.Fixtures.x) =
      (2, Sturm.Fixtures.x) := by decide +kernel
  rw [normalized]
  have degree : Sturm.Fixtures.p.natDegree = 2 := by decide +kernel
  rw [degree]
  simp only [SignedRemainderChain.buildAux, DensePoly.positivePseudoDiv,
    DensePoly.pseudoDiv, DensePoly.pseudoExponent, DensePoly.pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel

@[expose] def sourceDomain : Sturm.PreparedDomain Rat :=
  Sturm.PreparedDomain.ofChecked Sturm.orderSign Sturm.Fixtures.p (.finite 0) (.finite 2)
    Sturm.Fixtures.literalChain (by decide +kernel) (by decide +kernel) source_chain.symm

private theorem source_prepared :
    Sturm.prepare Sturm.orderSign Sturm.Fixtures.p (.finite 0) (.finite 2) = some sourceDomain :=
  Sturm.prepare_ofChecked _ _ _ _ _ _ _ _

@[expose] def sourceHandle : Hex.SignDet.QueryHandle source :=
  Hex.SignDet.QueryHandle.ofChecked source sourceDomain (by
    simpa only [source_raw, Hex.SignDet.Conformance.singletonRaw] using source_prepared)

private theorem source_cached : source.prepareQueries = some sourceHandle := by
  unfold sourceHandle
  apply Hex.SignDet.Descriptor.prepareQueries_eq

set_option maxRecDepth 32768 in
/-- The original prepared context counts the single positive root. -/
theorem source_count : context.rootCount = some 1 := by
  simp only [context, Context.adjoin, source_cached, sourceHandle,
    Hex.SignDet.QueryHandle.ofChecked, sourceDomain, @Sturm.PreparedDomain.ofChecked_sign,
    @Sturm.PreparedDomain.ofChecked_head, @Sturm.PreparedDomain.ofChecked_lower,
    @Sturm.PreparedDomain.ofChecked_upper, @Sturm.PreparedDomain.ofChecked_squarefree,
    Option.map_some, Sturm.countPrepared, Sturm.certifyCountPrepared,
    TarskiCertificate.fromChains, TarskiCertificate.signs, signVar]
  decide +kernel

/-- The target operation equals rational addition, but the kernel cannot
execute its value. Its equality is used only in erased validity proofs. -/
opaque targetAdd : {operation : Add Rat // operation = Rat.instAdd} := ⟨inferInstance, rfl⟩

/-- Retain the native context's data under the equal opaque operation. -/
@[expose] def transported :
    @Context Rat Nat _ _ inferInstance targetAdd.val inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance _ Sturm.orderSign 7 :=
  @Context.changeOps Rat Nat _ _ _ inferInstance targetAdd.val inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    rfl targetAdd.property.symm rfl rfl rfl rfl rfl rfl Sturm.orderSign 7 context

set_option maxRecDepth 32768 in
/-- The actual transported fields compute without evaluating the opaque
addition or using an equation between the transported and native contexts. -/
theorem stored_fields :
    let : Add Rat := targetAdd.val
    transported.root.raw = Hex.SignDet.Conformance.singletonRaw ∧
    transported.rootCount = some 1 ∧ transported.canReduce = true ∧
    transported.cleanCoeff 37 = true ∧
    transported.handle.map (fun handle => handle.domain.squarefree.chain) =
      some #[Sturm.Fixtures.p, Sturm.Fixtures.x, sourceUnit] := by
  let : Add Rat := targetAdd.val
  simp only [transported, Context.changeOps, Context.ofChecked,
    Hex.SignDet.Descriptor.changeOps, Hex.SignDet.Descriptor.ofChecked,
    Hex.SignDet.QueryHandle.ofChecked,
    context, Context.adjoin, source_cached, sourceHandle, source_raw,
    Hex.SignDet.Conformance.singletonRaw, sourceDomain, @Sturm.PreparedDomain.ofChecked_sign,
    @Sturm.PreparedDomain.ofChecked_head, @Sturm.PreparedDomain.ofChecked_lower,
    @Sturm.PreparedDomain.ofChecked_upper, @Sturm.PreparedDomain.ofChecked_squarefree,
    Option.map_some, Sturm.countPrepared, Sturm.certifyCountPrepared]
  dsimp only [context, Context.adjoin, Option.map]
  simp only [TarskiCertificate.fromChains, TarskiCertificate.signs, signVar,
    ← Array.all_toList, Hex.SignDet.QueryHandle.changeOps, Hex.SignDet.QueryHandle.ofChecked,
    Sturm.PreparedDomain.changeOps, @Sturm.PreparedDomain.ofChecked_sign,
    @Sturm.PreparedDomain.ofChecked_head, @Sturm.PreparedDomain.ofChecked_lower,
    @Sturm.PreparedDomain.ofChecked_upper, @Sturm.PreparedDomain.ofChecked_squarefree]
  decide +kernel

set_option maxRecDepth 32768 in
/-- The target operation itself is unavailable to kernel computation. -/
example : True := by
  fail_if_success
    have : targetAdd.val.add 1 1 = 2 := by decide +kernel
  trivial

end Hex.RealClosure.Algebraic.ContextOperationsConformance

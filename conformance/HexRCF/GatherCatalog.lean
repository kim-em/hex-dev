/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Gather
public meta import HexRCF.RealCoefficients.Gather
public meta import Lean.Util.CollectAxioms
public import HexOrderedFnMathlib.LiouvilleTests
public meta import HexOrderedFnMathlib.LiouvilleTests

open scoped List

public section
namespace Hex.RCF.RealCoefficients.GatherCatalog
open Hex RealClosure RealClosure.Tower

private def registry : BaseContext.Registry := fun _ => none
private abbrev base := Context.base (BaseContext.rational registry)

/-- Automatic selection retains both real conjugates, another field and a
repeated owner. Compiled results are controls, not source-goal proofs. -/
def decisions : Bool := Id.run do
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let raw := fun n lo hi =>
    ({context := base.signature, head := x*x - DensePoly.C n,
      lower := .finite lo, upper := .finite hi, indices := [], signs := []} :
      SignDet.RawDescriptor base.Value Signature)
  let some first := SignDet.Descriptor.validate base.sign base.signature
      (raw (1+1) 1 (1+1)) | return false
  let some negative := SignDet.Descriptor.validate base.sign base.signature
      (raw (1+1) (-(1+1)) (-1)) | return false
  let some second := SignDet.Descriptor.validate base.sign base.signature
      (raw (1+1+1) 1 (1+1)) | return false
  let a := base.adjoin first
  let b := base.adjoin negative
  let c := base.adjoin second
  let owners := [a.context, b.context, c.context, a.context]
  let coefficients : (i : Fin owners.length) → (owners[i]).Value := by
    change (i : Fin 4) → ([a.context, b.context, c.context, a.context][i]).Value
    exact Fin.cases a.generator (Fin.cases b.generator
      (Fin.cases c.generator (Fin.cases a.generator (fun i => Fin.elim0 i))))
  let v : RealFormula.Poly 5 := MvPoly.X 4
  let root := RealFormula.QF.and (.atom ⟨v^2 - MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨v-1, .gt⟩) (.atom ⟨v-MvPoly.X 2, .lt⟩))
  let wrong := RealFormula.QF.atom ⟨v^2 - MvPoly.X 1, .eq⟩
  let leading := RealFormula.QF.atom
    ⟨(MvPoly.X 0 - MvPoly.X 3)*v^4 + v^2, .ge⟩
  let zero := RealFormula.QF.atom ⟨MvPoly.X 0 + MvPoly.X 1, .eq⟩
  let catalog := BaseContext.Catalog.empty registry
  let some selected := Shared.gatherFrom? catalog owners | return false
  return selected.1.depth == 0 && selected.1.signature.constants.isEmpty &&
    Gather.runFrom? catalog coefficients root .existsReal == some true &&
    Gather.runFrom? catalog coefficients wrong .existsReal == some false &&
    Gather.runFrom? catalog coefficients leading .forallReal == some true &&
    Gather.runFrom? catalog coefficients zero .forallReal == some true

#guard decisions

/-- The empty catalog's rational prefix handles an empty coefficient list. -/
def empty : Bool :=
  Gather.runFrom? (owners := []) (BaseContext.Catalog.empty registry)
    (fun i : Fin 0 => Fin.elim0 i)
    (.atom ⟨MvPoly.X 0 ^ 2, .ge⟩) .forallReal == some true

#guard empty

/-- No jointly admissible installed prefix means failure before a verdict. -/
theorem unavailable {providers : BaseContext.Registry} {owners : List (Context providers)}
    (catalog : BaseContext.Catalog providers)
    (absent : ∀ entry ∈ catalog.prefixes, ∃ owner ∈ owners,
      ¬ owner.origin.base.signature.constants <+ entry.keys)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length+1)) (quantifier : RealFormula.Quantifier) :
    Gather.runFrom? catalog coefficients formula quantifier = none := by
  have missing : SharedBase.choose? catalog (owners.map (·.origin.base)) = none := by
    cases chosen : SharedBase.choose? catalog (owners.map (·.origin.base)) with
    | none => rfl
    | some selected =>
      obtain ⟨entry, member, compatible⟩ :=
        (SharedBase.choose?_isSome catalog _).mp (by rw [chosen]; rfl)
      obtain ⟨owner, present, refused⟩ := absent entry member
      have included := compatible owner.origin.base (List.mem_map.mpr ⟨owner, present, rfl⟩)
      have keys := ((Inclusion.base?_isSome _ _).mp included).1
      simp only [BaseContext.PackedContext.extend_signature,
        BaseContext.RealPrefix.finish_signature] at keys
      exact False.elim (refused keys)
  simp only [Gather.runFrom?, Shared.gatherFrom?, missing, bind, Option.bind]

/-- An installed `[α, β]` provider admits an independently constructed β owner.
The always-present rational prefix is inadmissible and needs no supplied model.
The formula conclusion uses the provider-induced owner model; separately
authenticated original models use `Gather.runFrom?_original`. -/
theorem registered {providers : BaseContext.Registry}
    (source provider : BaseContext.RealPrefix.Model providers)
    (α β : BaseContext.ConstantKey) (different : β ≠ α) (sourceKeys : source.context.keys = [β])
    (providerKeys : provider.context.keys = [α, β])
    (catalog : BaseContext.Catalog providers)
    (installed : (BaseContext.Catalog.empty providers).insert provider.context = some catalog)
    (suffix : Suffix (Context.ofBase source.context.finish))
    (coefficients : (i : Fin [suffix.context].length) → ([suffix.context][i]).Value)
    (formula : RealFormula.QF 2) (quantifier : RealFormula.Quantifier) :
    ¬ source.context.keys <+: provider.context.keys ∧
    ∃ (selected : BaseContext.PackedContext providers)
      (shared : Shared selected [suffix.context]),
      Shared.gatherFrom? catalog [suffix.context] = some ⟨selected, shared⟩ ∧
      ∃ (following : selected.Realization) (reference : Model (Context.ofBase selected) ℝ)
        (model : Shared.Model shared following reference),
        ∃ result, Gather.runFrom? catalog coefficients formula quantifier = some result ∧
          (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
            (fun i => (model.owners.get i).1.value (coefficients i))) := by
  have original : suffix.context.origin.base = source.context.finish := by
    rw [Suffix.base_eq]
    generalize source.context.finish = original
    cases original with
    | pack original =>
      simp only [Context.ofBase, Context.origin_base, Origin.base]
      rfl
  constructor
  · rw [sourceKeys, providerKeys, List.singleton_prefix_cons_iff]
    exact different
  apply Gather.gather_catalog catalog _ provider.context _ _ coefficients formula quantifier
  · intro entry member admitted
    rcases (BaseContext.Catalog.mem_prefixes_of_insert _ _ _ _ installed).mp member with
      same | rational
    · exact ⟨provider, same.symm⟩
    · rw [BaseContext.Catalog.prefixes_empty] at rational
      have same := List.mem_singleton.mp rational
      have keys := admitted suffix.context (by simp)
      rw [original, BaseContext.RealPrefix.finish_signature, sourceKeys, same] at keys
      simp only [BaseContext.RealPrefix.keys_rational, List.sublist_nil, List.cons_ne_self] at keys
  · exact (BaseContext.Catalog.mem_prefixes_of_insert _ _ _ _ installed).mpr (Or.inl rfl)
  · intro owner member
    have same : owner = suffix.context := List.mem_singleton.mp member
    subst owner
    rw [original]
    constructor
    · rw [BaseContext.RealPrefix.finish_signature, sourceKeys, providerKeys]
      exact List.sublist_append_right [α] [β]
    · simp [BaseContext.PackedContext.depth, BaseContext.RealPrefix.finish_signature]

/-- An installed fresh provider still refuses an original stale β version. -/
theorem stale {providers : BaseContext.Registry} (provider : BaseContext.RealPrefix.Model providers)
    (providerKeys : provider.context.keys = [⟨"alpha", 1⟩, ⟨"beta", 1⟩])
    (catalog : BaseContext.Catalog providers)
    (installed : (BaseContext.Catalog.empty providers).insert provider.context = some catalog)
    (owner : Context providers) (sourceKeys : owner.origin.base.signature.constants = [⟨"beta", 0⟩])
    (coefficients : (i : Fin [owner].length) → ([owner][i]).Value)
    (formula : RealFormula.QF 2) (quantifier : RealFormula.Quantifier) :
    Gather.runFrom? catalog coefficients formula quantifier = none := by
  apply unavailable catalog _ coefficients formula quantifier
  intro entry member
  refine ⟨owner, by simp, ?_⟩
  intro included
  rcases (BaseContext.Catalog.mem_prefixes_of_insert _ _ _ _ installed).mp member with
    same | rational
  · rw [sourceKeys, same, providerKeys] at included
    have member : 0 ∈ [1, 1] :=
      (included.map BaseContext.ConstantKey.version).subset (by simp)
    simp at member
  · rw [BaseContext.Catalog.prefixes_empty] at rational
    rw [sourceKeys, List.mem_singleton.mp rational] at included
    simp only [BaseContext.RealPrefix.keys_rational, List.sublist_nil, List.cons_ne_self] at included

/-! Native controls reuse the owner's actual one-constant Liouville fixture.
No second independent provider or joint-transcendence premise is fabricated. -/
open OrderedFn OrderedFn.Oracle

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat
private def namedKey (version : Nat) : BaseContext.ConstantKey := ⟨"liouville", version⟩
private def namedRegistry : BaseContext.Registry := fun k =>
  if k.name = "liouville" then some OrderedFn.LiouvilleTests.provider else none
private abbrev initial := BaseContext.RealContext.rational namedRegistry

private theorem namedPresent (version : Nat) :
    (namedRegistry (namedKey version)).isSome = true := by simp [namedRegistry, namedKey]

private theorem castSource (F G : Lean.Grind.Field Rat) (same : F = G)
    (equal : @Real.Registration Rat F inferInstance = @Real.Registration Rat G inferInstance)
    (source : @Real.Registration Rat F inferInstance) :
    @Real.Registration.source Rat G inferInstance (cast equal source) =
      @Real.Registration.source Rat F inferInstance source := by
  cases same
  rfl

private theorem namedSource (version : Nat) :
    initial.source (namedKey version) (namedPresent version) =
      OrderedFn.LiouvilleCoreTests.registered.source := by
  simp only [OrderedFn.LiouvilleCoreTests.registered,
    castSource _ _ HexRationalFnMathlib.ratField_eq]
  rfl

private theorem namedSign (version : Nat) (f : RationalFn Rat) :
    Acc (Next (Real.attempt (initial.source (namedKey version) (namedPresent version)) f)) 0 := by
  rw [namedSource]
  exact OrderedFn.LiouvilleCoreTests.registered.signProgress f

private theorem namedApprox (version : Nat) (f : RationalFn Rat) (δ : Rat) :
    Acc (Next (Real.approxAttempt (initial.source (namedKey version) (namedPresent version))
      f (Real.requestWidth δ))) 0 := by
  rw [namedSource]
  exact OrderedFn.LiouvilleCoreTests.registered.approxProgress f δ

private abbrev namedPrefix (version : Nat) : BaseContext.RealPrefix namedRegistry :=
  .pack (initial.constant (namedKey version) (namedPresent version)
    (namedSign version) (namedApprox version))

/-- A native version mismatch declines before decision production. With both
versions installed, selection skips the newer incompatible entry; empty owners
choose the rational prefix even when both installed entries qualify. -/
def nativeProviders : Bool := Id.run do
  let empty := BaseContext.Catalog.empty namedRegistry
  let some fresh := empty.insert (namedPrefix 2) | return false
  let some old := empty.insert (namedPrefix 1) | return false
  let some both := old.insert (namedPrefix 2) | return false
  let owner := Context.ofBase (namedPrefix 1).finish
  let owners := [owner]
  let coordinate : owner.Value := ⟨RationalFn.X⟩
  let coefficients : (i : Fin owners.length) → (owners[i]).Value := by
    change (i : Fin 1) → ([owner][i]).Value
    exact Fin.cases coordinate (fun i => Fin.elim0 i)
  let positive : RealFormula.QF 2 := .atom ⟨MvPoly.X 0, .gt⟩
  let negative : RealFormula.QF 2 := .atom ⟨MvPoly.X 0, .lt⟩
  let stale := Gather.runFrom? fresh coefficients .tt .forallReal
  let accepted := Gather.runFrom? both coefficients positive .forallReal
  let refused := Gather.runFrom? both coefficients negative .forallReal
  let selected := (Shared.gatherFrom? both owners).map (fun result => result.1.signature)
  let rational := (Shared.gatherFrom? both []).map (fun result => result.1.signature)
  return stale == none && accepted == some true && refused == some false &&
    selected == some ⟨[namedKey 1], 0⟩ && rational == some ⟨[], 0⟩

#guard nativeProviders

run_meta do
  for name in #[``Gather.runFrom?_spec, ``Gather.runFrom?_original, ``Gather.gather_catalog, ``unavailable, ``registered, ``stale] do
    let _ ← Lean.getConstInfo name
    let axioms ← Lean.collectAxioms name
    unless axioms == #[`propext, `Classical.choice, `Quot.sound] do
      throwError "unexpected complete axiom inventory in {name}: {axioms}"
    Lean.logInfo m!"catalog gathering axioms {name}: {axioms}"
  for name in #[``namedPresent, ``castSource, ``namedSource, ``namedSign, ``namedApprox] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "unexpected provider-support axiom {axiomName} in {name}"
    Lean.logInfo m!"provider-support axioms {name}: {axioms}"

end Hex.RCF.RealCoefficients.GatherCatalog

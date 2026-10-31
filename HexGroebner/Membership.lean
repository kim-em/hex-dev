/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.NormalForm
public import HexGroebner.CertificateNonmember
public import HexGroebner.CertificateBasisReplay

public section

namespace Hex.Groebner

/-- Standalone positive witness checked against the original generators. -/
structure CheckedMember (basis : CheckedBasis) (target : Certificate.Polynomial) where
  private mk ::
  witness : Certificate.Member
  accepted : checkMember basis.context basis.generators target witness = true

/-- Negative membership data with independent complete acceptance. -/
structure CheckedNonmember (basis : CheckedBasis) (target : Certificate.Polynomial) where
  private mk ::
  witness : Certificate.Nonmember
  accepted : checkNonmember basis.context basis.generators target witness = true

/-- Resumption retains either unfinished checked division or a completed
receipt awaiting the final membership classification within the same budget. -/
structure MemberState (basis : CheckedBasis) (target : Certificate.Polynomial) where
  private mk ::
  stage : Sum (DivideState basis.context basis.polynomials target)
    (Certificate.CheckedDivision basis.context basis.polynomials target × Certificate.Usage)

/-- Positive results retain explicit cofactors against the accepted basis, a
checked zero remainder and a standalone shared derivation against the original
generators. Negative results contain a complete independently checked witness. -/
inductive MemberResult (basis : CheckedBasis) (target : Certificate.Polynomial) where
  | member (division : Certificate.CheckedDivision basis.context basis.polynomials target)
      (certificate : CheckedMember basis target)
      (zero : Hex.MvPoly.Kernel.isZero division.value.remainder = true) (usage : Certificate.Usage)
  | nonmember (value : CheckedNonmember basis target) (usage : Certificate.Usage)
  | invalid (index : Nat) (usage : Certificate.Usage)
  | rejected (usage : Certificate.Usage)
  | exhausted (resource : Certificate.Resource) (state : MemberState basis target)
  | address (state : MemberState basis target)
  | internal (usage : Certificate.Usage)

private def produceMember (basis : CheckedBasis) (budget : Certificate.Budget)
    (division : Certificate.Division) : Certificate.Work Certificate.Member := do
  let remaining := budget.nodes - (← get).nodes
  let mut count := 0
  for _ in basis.certificate.forward.nodes do
    Certificate.spend budget 1
    count := count+1
    if count > remaining then throw (.exhausted .nodes)
  Certificate.reserveBytes budget (count*64)
  if basis.certificate.forward.roots.size != division.quotients.size then throw .arithmetic
  let mut extra : List Certificate.Node := []
  if count ≥ remaining then throw (.exhausted .nodes)
  Certificate.reserveBytes budget 64
  Certificate.spend budget 1
  let mut root := count
  extra := .zero :: extra
  count := count+1
  for i in [:division.quotients.size] do
    Certificate.spend budget 1
    if !division.quotients[i]!.isEmpty then
      if count+2 > remaining then throw (.exhausted .nodes)
      Certificate.reserveBytes budget 128
      extra := .multiply division.quotients[i]! basis.certificate.forward.roots[i]! :: extra
      extra := .add root count :: extra
      root := count+1
      count := count+2
  Certificate.reserveBytes budget (count*24)
  Certificate.spend budget count
  return ⟨basis.certificate.forward.nodes ++ extra.reverse,root⟩

private def finishPositive (basis : CheckedBasis) (budget : Certificate.Budget)
    (target : Certificate.Polynomial)
    (value : Certificate.CheckedDivision basis.context basis.polynomials target)
    (zero : Hex.MvPoly.Kernel.isZero value.value.remainder = true)
    (initial : Certificate.Usage) : MemberResult basis target := Id.run do
  let action : Certificate.Work Certificate.Member := do
    let witness ← produceMember basis budget value.value
    let before ← get
    for i in [:basis.generators.size] do
      Certificate.Arithmetic.validate basis.context budget i basis.generators[i]!
    Certificate.Arithmetic.validate basis.context budget basis.generators.size target
    let after ← get
    Certificate.spend budget (after.work-before.work)
    Certificate.BasisVerification.reserveContainment basis.context budget basis.generators #[target]
      ⟨witness.nodes,#[witness.root]⟩
    return witness
  let (result,usage) := action.run initial
  match result with
  | .error (.exhausted r) => return .exhausted r ⟨.inr (value,usage)⟩
  | .error .address => return .address ⟨.inr (value,usage)⟩
  | .error _ => return .internal usage
  | .ok witness =>
    if accepted : checkMember basis.context basis.generators target witness = true then
      return .member value ⟨witness,accepted⟩ zero usage
    else return .internal usage

private def finishMember (basis : CheckedBasis) (budget : Certificate.Budget)
    (target : Certificate.Polynomial)
    (value : Certificate.CheckedDivision basis.context basis.polynomials target)
    (initial : Certificate.Usage) : MemberResult basis target := Id.run do
  if basis.context.variables > budget.variables then return .exhausted .variables ⟨.inr (value, initial)⟩
  match Certificate.checkUsage budget initial with
  | .error (.exhausted r) => return .exhausted r ⟨.inr (value, initial)⟩
  | .error _ => return .internal initial
  | .ok _ => pure ()
  let action : Certificate.Work Unit := do
    Certificate.spend budget 1
    Certificate.reserveBytes budget 64
  let (result, usage) := action.run initial
  match result with
  | .error (.exhausted r) => return .exhausted r ⟨.inr (value, usage)⟩
  | .error .address => return .address ⟨.inr (value, usage)⟩
  | .error _ => return .internal usage
  | .ok _ =>
    match hz : Hex.MvPoly.Kernel.isZero value.value.remainder with
    | true => return finishPositive basis budget target value hz usage
    | false =>
      let witness : Certificate.Nonmember := ⟨basis.polynomials, basis.certificate, value.value⟩
      have accepted : checkNonmember basis.context basis.generators target witness = true := by
        simp [checkNonmember, witness, basis.accepted, value.accepted, hz]
      return .nonmember ⟨witness, accepted⟩ usage

private def classified (basis : CheckedBasis) (budget : Certificate.Budget)
    (target : Certificate.Polynomial) :
    DivideResult basis.context basis.polynomials target → MemberResult basis target
  | .success value usage => finishMember basis budget target value usage
  | .invalid i usage => .invalid i usage
  | .rejected usage => .rejected usage
  | .exhausted r state => .exhausted r ⟨.inl state⟩
  | .address state => .address ⟨.inl state⟩
  | .internal usage => .internal usage

/-- Resume without changing the accepted basis, original ideal or target. -/
def resumeMemberWith {basis : CheckedBasis} {target : Certificate.Polynomial}
    (budget : Certificate.Budget) (state : MemberState basis target) : MemberResult basis target :=
  match state.stage with
  | .inl division => classified basis budget target (resumeDivideWith budget division)
  | .inr (value, usage) => finishMember basis budget target value usage

/-- Bounded positive/negative membership against an accepted complete basis.
Division, independent replay and final classification share one allowance.
No exhaustion result is interpreted as evidence of nonmembership. -/
def memberWith (basis : CheckedBasis) (budget : Certificate.Budget)
    (target : Certificate.Polynomial) : MemberResult basis target :=
  classified basis budget target (normalFormWith basis budget target)

end Hex.Groebner

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RootBuild
public import HexRCF.RealCoefficients.ScalarPacket
public import HexRCF.RealCoefficients.SourceIdentity
public section

namespace Hex.RCF.RealCoefficients.SourceBuild
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

inductive Error where
  | roots (error : RootBuild.Error)
  | production (error : BuildError)
  | descriptor (error : DescriptorError)
  | equation
  | enclosure
  | ambiguous
  | unselected
  deriving Repr

/-- Native proposals for one source root and the two independent scalar
packets demanded by source authentication. The sign equalities only describe
the proposed literal fields; they are not proof evidence about real values. -/
structure Result (parent : Tower.Context registry) where
  root : Descriptor parent.Value Signature parent.sign parent.signature
  equation : ScalarPacket.Proposal
  enclosure : ScalarPacket.Proposal
  zero : equation.sign = 0
  positive : enclosure.sign = 1

/-- Visit every enumerated root. Failure to produce a row is terminal, and a
second positive window match rejects an ambiguous source rather than choosing
an arbitrary conjugate. No equation or enclosure is silently substituted. -/
def select (polynomial window : DensePoly parent.Value)
    (roots : List (Descriptor parent.Value Signature parent.sign parent.signature)) :
    Except Error (Result parent) := do
  let mut selected : Option (Result parent) := none
  for root in roots do
    let context := Algebraic.Context.adjoin root parent.isClean
    let some equation := ScalarPacket.buildParts context parent.codec polynomial
      | throw .equation
    if zero : equation.sign = 0 then
      let some enclosure := ScalarPacket.buildParts context parent.codec window
        | throw .enclosure
      if positive : enclosure.sign = 1 then
        if selected.isSome then throw .ambiguous
        selected := some ⟨root,equation,enclosure,zero,positive⟩
      else unless enclosure.sign = 0 || enclosure.sign = -1 do throw .enclosure
    else throw .equation
  match selected with
  | none => throw .unselected
  | some result => return result

/-- A lawful selected root satisfying the original equation and strictly
positive window produces both scalar packets. No successful producer output
or table is assumed. This establishes proposal progress, not frozen replay. -/
theorem select_single (model : Model parent ℝ)
    (root : Descriptor parent.Value Signature parent.sign parent.signature)
    (polynomial window : DensePoly parent.Value)
    (zero : (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial).eval
      (root.root model.value model.zero_iff model.one model.add model.sub model.mul model.nat model.sign) = 0)
    (positive : 0 < (HexPolyTheory.Interpret.interpret model.value model.zero_iff window).eval
      (root.root model.value model.zero_iff model.one model.add model.sub model.mul model.nat model.sign)) :
    ∃ result, select polynomial window [root] = .ok result := by
  let context := Algebraic.Context.adjoin root parent.isClean
  have equationSign : context.signPoly polynomial = 0 := by
    rw [context.signPoly_spec model.value model.zero_iff model.one model.add model.sub
      model.mul model.nat model.sign model.neg model.inv]
    simp [Algebraic.Context.evalPoly, Algebraic.Context.rootValue,
      context, Algebraic.Context.root_adjoin, zero]
  have windowSign : context.signPoly window = 1 := by
    rw [context.signPoly_spec model.value model.zero_iff model.one model.add model.sub
      model.mul model.nat model.sign model.neg model.inv]
    have sign := congrArg (fun sign : SignType => (sign : Int)) (sign_eq_one_iff.mpr positive)
    simpa [Algebraic.Context.evalPoly, Algebraic.Context.rootValue,
      context, Algebraic.Context.root_adjoin] using sign
  obtain ⟨equation, equationBuilt⟩ := ScalarPacket.buildParts_success model context parent.codec polynomial
  obtain ⟨enclosure, enclosureBuilt⟩ := ScalarPacket.buildParts_success model context parent.codec window
  have equationZero := (ScalarPacket.buildParts_sign model context parent.codec polynomial equation equationBuilt).trans equationSign
  have enclosurePositive := (ScalarPacket.buildParts_sign model context parent.codec window enclosure enclosureBuilt).trans windowSign
  dsimp only [context] at equationBuilt enclosureBuilt
  refine ⟨⟨root,equation,enclosure,equationZero,enclosurePositive⟩, ?_⟩
  simp [select, equationBuilt, enclosureBuilt, equationZero, enclosurePositive,
    pure, Except.pure, bind, Except.bind]

/-- Successful singleton selection retains two independently accepted scalar
packets at its exact root, using the canonical predecessor codec. -/
theorem select_checked (model : Model parent ℝ)
    (root : Descriptor parent.Value Signature parent.sign parent.signature)
    (polynomial window : DensePoly parent.Value) (result : Result parent)
    (produced : select polynomial window [root] = .ok result) :
    result.root = root ∧
    result.equation.polynomial = Codec.poly parent.codec polynomial ∧
    result.enclosure.polynomial = Codec.poly parent.codec window ∧
    (let context := Algebraic.Context.adjoin result.root parent.isClean
     (ScalarPacket.read model parent.codec context result.equation.polynomial
       result.equation.sign result.equation.evidence).isSome = true ∧
     (ScalarPacket.read model parent.codec context result.enclosure.polynomial
       result.enclosure.sign result.enclosure.evidence).isSome = true) := by
  cases equationBuilt : ScalarPacket.buildParts (Algebraic.Context.adjoin root parent.isClean)
      parent.codec polynomial with
  | none => simp [select, equationBuilt, pure, Except.pure, bind, Except.bind] at produced
  | some equation =>
    by_cases zero : equation.sign = 0
    · cases enclosureBuilt : ScalarPacket.buildParts (Algebraic.Context.adjoin root parent.isClean)
          parent.codec window with
      | none => simp [select, equationBuilt, zero, enclosureBuilt, pure, Except.pure, bind, Except.bind] at produced
      | some enclosure =>
        by_cases positive : enclosure.sign = 1
        · simp [select, equationBuilt, zero, enclosureBuilt, positive,
            pure, Except.pure, bind, Except.bind] at produced
          cases produced
          exact ⟨rfl, ScalarPacket.buildParts_poly _ parent.codec polynomial equation equationBuilt,
            ScalarPacket.buildParts_poly _ parent.codec window enclosure enclosureBuilt,
            ScalarPacket.buildParts_accepted model _ parent.codec parent.codec_lawful
              polynomial equation equationBuilt,
            ScalarPacket.buildParts_accepted model _ parent.codec parent.codec_lawful
              window enclosure enclosureBuilt⟩
        · by_cases absent : enclosure.sign = 0 ∨ enclosure.sign = -1 <;>
            simp [select, equationBuilt, zero, enclosureBuilt, positive, absent,
              pure, Except.pure, bind, Except.bind, throw] at produced
    · simp [select, equationBuilt, zero, pure, Except.pure, bind, Except.bind] at produced

/-- Enumerate with the existing owner root producer and select exactly one
root using the supplied enclosure polynomial. The usual window is the source
isolating-square margin. Its original-source interpretation and selected-root
identity are subsequently checked by `SourceIdentity.quoteWith`; this producer
does not prove them, reconstruct a frozen parent, or establish completeness. -/
def build (polynomial window : DensePoly parent.Value) : Except Error (Result parent) := do
  let roots ← RootBuild.build polynomial |>.mapError Error.roots
  select polynomial window roots.roots

/-- Propose a source in an open interval with root-free endpoints. The
owner checks the endpoints and exactly one root before constructing a
descriptor with no derivative queries. The independent equation and original
window packets are still required. Invalid domains, absent/ambiguous roots
and production failures remain distinct; no all-real enumeration is retried.
This is certificate production, not source identification or completeness. -/
def buildOn (polynomial window : DensePoly parent.Value)
    (lower upper : Endpoint parent.Value) : Except Error (Result parent) := do
  let raw : RawDescriptor parent.Value Signature :=
    ⟨parent.signature, polynomial, lower, upper, [], []⟩
  let root ← match Descriptor.build parent.sign parent.signature raw with
    | .error error => .error (.production error)
    | .ok (.error error) => .error (.descriptor error)
    | .ok (.ok root) => .ok root
  select polynomial window [root]

/-- Actual bounded production implies independent acceptance of its original
equation and enclosure packets. No serialization or graph-shape premise is
added; the canonical parent codec already has its owner roundtrip law. -/
theorem buildOn_checked (model : Model parent ℝ)
    (polynomial window : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (result : Result parent) (produced : buildOn polynomial window lower upper = .ok result) :
    result.root.raw = ⟨parent.signature,polynomial,lower,upper,[],[]⟩ ∧
    result.equation.polynomial = Codec.poly parent.codec polynomial ∧
    result.enclosure.polynomial = Codec.poly parent.codec window ∧
    (let context := Algebraic.Context.adjoin result.root parent.isClean
     (ScalarPacket.read model parent.codec context result.equation.polynomial
       result.equation.sign result.equation.evidence).isSome = true ∧
     (ScalarPacket.read model parent.codec context result.enclosure.polynomial
       result.enclosure.sign result.enclosure.evidence).isSome = true) := by
  cases built : Descriptor.build parent.sign parent.signature
      (⟨parent.signature,polynomial,lower,upper,[],[]⟩ : RawDescriptor parent.Value Signature) with
  | error error => simp [buildOn, built, bind, Except.bind] at produced
  | ok outcome =>
    cases outcome with
    | error error => simp [buildOn, built, bind, Except.bind] at produced
    | ok root =>
      have selected : select polynomial window [root] = .ok result := by
        simpa only [buildOn, built, bind, Except.bind] using produced
      obtain ⟨same, equation, enclosure, checked⟩ := select_checked model root polynomial window result selected
      exact ⟨(congrArg (·.raw) same).trans (Descriptor.build_raw built), equation, enclosure, checked⟩

/-- Accepted produced packets identify the original selected source. The
source witness, alias selection and coefficient-map laws are inputs; scalar
vanishing and window positivity are derived from the returned packets. This
soundness law does not replace independent frozen quotation. -/
theorem buildOn_identify (model : Model parent ℝ)
    (polynomial window : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (result : Result parent) (produced : buildOn polynomial window lower upper = .ok result)
    (sourceP : ZPoly) (square : DyadicSquare)
    (hw : atomWitness sourceP square) (hp : (mahlerPrec sourceP : Int) ≤ square.prec)
    (anchor : ℝ) (selected : (Field.literalRep sourceP square hw hp).root.re = anchor)
    (equationValue : HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial =
      LiteralSign.realPoly (ZPoly.toRatPoly sourceP))
    (enclosureValue : HexPolyTheory.Interpret.interpret model.value model.zero_iff window =
      LiteralSign.realPoly (SourceIdentity.margin square)) :
    result.root.root model.value model.zero_iff model.one model.add model.sub model.mul
      model.nat model.sign = anchor := by
  obtain ⟨_, equationKey, enclosureKey, equationRead, enclosureRead⟩ :=
    buildOn_checked model polynomial window lower upper result produced
  let context := Algebraic.Context.adjoin result.root parent.isClean
  let equation := ScalarPacket.restore model parent.codec context result.equation.polynomial
    result.equation.sign result.equation.evidence equationRead
  let enclosure := ScalarPacket.restore model parent.codec context result.enclosure.polynomial
    result.enclosure.sign result.enclosure.evidence enclosureRead
  have equationPoly : equation.polynomial = polynomial := by
    change ScalarPacket.key parent.codec result.equation.polynomial = polynomial
    rw [equationKey]
    simp only [ScalarPacket.key, Codec.read_poly parent.codec parent.codec_lawful,
      Except.toOption, Option.getD_some]
  have enclosurePoly : enclosure.polynomial = window := by
    change ScalarPacket.key parent.codec result.enclosure.polynomial = window
    rw [enclosureKey]
    simp only [ScalarPacket.key, Codec.read_poly parent.codec parent.codec_lawful,
      Except.toOption, Option.getD_some]
  apply SourceIdentity.identify model result.root sourceP square hw hp anchor selected equation enclosure
  · rw [equationPoly]
    exact equationValue
  · rw [enclosurePoly]
    exact enclosureValue
  · exact result.zero
  · exact result.positive

/-- An ordinary-real count-one domain with a positive original window yields
an actual bounded source proposal. The domain, count and sign premises are
mathematical properties of the input, not successful producer equations.
Frozen serialization acceptance and source alias identification are separate. -/
theorem buildOn_success (model : Model parent ℝ)
    (polynomial window : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (domain : HexSturmTheory.Domain model.value model.zero_iff polynomial lower upper)
    (one : (HexRealRootsTheory.Tarski.rootsIn
      (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial)
      (lower.map model.value) (upper.map model.value)).card = 1)
    (positive : ∀ x ∈ HexRealRootsTheory.Tarski.rootsIn
      (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial)
      (lower.map model.value) (upper.map model.value),
      0 < (HexPolyTheory.Interpret.interpret model.value model.zero_iff window).eval x) :
    ∃ result, buildOn polynomial window lower upper = .ok result := by
  classical
  have countPositive : 0 < (HexRealRootsTheory.Tarski.rootsIn
      (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial)
      (lower.map model.value) (upper.map model.value)).card := by
    rw [one]
    exact Nat.zero_lt_one
  obtain ⟨witness, inDomain⟩ := Finset.card_pos.mp countPositive
  have rootZero := ((HexRealRootsTheory.Tarski.mem_rootsIn_iff _ domain.1 _ _ _).mp inDomain).1
  have semanticDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
    (Polynomial.degree_pos_of_root domain.1 rootZero)
  have degree : 0 < polynomial.natDegree := by
    simpa only [HexPolyTheory.Interpret.natDegree_interpret] using semanticDegree
  let raw : RawDescriptor parent.Value Signature :=
    ⟨parent.signature,polynomial,lower,upper,[],[]⟩
  obtain ⟨root, built⟩ := (Descriptor.build_success_iff model.value model.zero_iff
    model.one model.add model.sub model.mul model.nat model.neg model.inv
    parent.sign model.sign parent.signature raw).mpr
    ⟨rfl, by simp [raw, RawDescriptor.wellFormed, degree], domain,
      by simpa [raw, RawDescriptor.queries, signsAt] using one⟩
  have retained := Descriptor.build_raw built
  have member : root.root model.value model.zero_iff model.one model.add model.sub
      model.mul model.nat model.sign ∈ HexRealRootsTheory.Tarski.rootsIn
      (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial)
      (lower.map model.value) (upper.map model.value) := by
    simpa only [retained] using (root.root_spec model.value model.zero_iff model.one
      model.add model.sub model.mul model.nat model.sign).1
  have zero := ((HexRealRootsTheory.Tarski.mem_rootsIn_iff _ domain.1 _ _ _).mp member).1
  obtain ⟨result, selected⟩ := select_single model root polynomial window zero (positive _ member)
  dsimp only [raw] at built
  refine ⟨result, ?_⟩
  simpa only [buildOn, built, bind, Except.bind] using selected

/-- Valid count-one real inputs yield actual bounded production, exact literal
subjects and two independently accepted scalar packets. The codec law belongs
to the canonical parent; no accepted-output or serialization premise is added.
This does not reconstruct a frozen parent history or identify a source alias. -/
theorem buildOn_checks (model : Model parent ℝ)
    (polynomial window : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (domain : HexSturmTheory.Domain model.value model.zero_iff polynomial lower upper)
    (one : (HexRealRootsTheory.Tarski.rootsIn
      (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial)
      (lower.map model.value) (upper.map model.value)).card = 1)
    (positive : ∀ x ∈ HexRealRootsTheory.Tarski.rootsIn
      (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial)
      (lower.map model.value) (upper.map model.value),
      0 < (HexPolyTheory.Interpret.interpret model.value model.zero_iff window).eval x) :
    ∃ result, buildOn polynomial window lower upper = .ok result ∧
      result.root.raw = ⟨parent.signature,polynomial,lower,upper,[],[]⟩ ∧
      result.equation.polynomial = Codec.poly parent.codec polynomial ∧
      result.enclosure.polynomial = Codec.poly parent.codec window ∧
      (let context := Algebraic.Context.adjoin result.root parent.isClean
       (ScalarPacket.read model parent.codec context result.equation.polynomial
         result.equation.sign result.equation.evidence).isSome = true ∧
       (ScalarPacket.read model parent.codec context result.enclosure.polynomial
         result.enclosure.sign result.enclosure.evidence).isSome = true) := by
  obtain ⟨result, produced⟩ := buildOn_success model polynomial window lower upper domain one positive
  exact ⟨result, produced, buildOn_checked model polynomial window lower upper result produced⟩

end Hex.RCF.RealCoefficients.SourceBuild

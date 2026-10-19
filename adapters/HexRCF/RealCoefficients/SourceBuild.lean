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

/-- A list of actual roots with exactly one positive window match produces a
source. These are semantic input conditions; no scalar packet or successful
producer result is assumed. -/
theorem select_success (model : Model parent ℝ)
    (polynomial window : DensePoly parent.Value)
    (roots : List (Descriptor parent.Value Signature parent.sign parent.signature))
    (zero : ∀ root ∈ roots,
      (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial).eval
        (root.root model.value model.zero_iff model.one model.add model.sub model.mul
          model.nat model.sign) = 0)
    (one : (roots.filter fun root => Decidable.decide (0 <
      (HexPolyTheory.Interpret.interpret model.value model.zero_iff window).eval
        (root.root model.value model.zero_iff model.one model.add model.sub model.mul
          model.nat model.sign))).length = 1) :
    ∃ result, select polynomial window roots = .ok result := by
  classical
  let value (root : Descriptor parent.Value Signature parent.sign parent.signature) :=
    root.root model.value model.zero_iff model.one model.add model.sub model.mul model.nat model.sign
  let query root := (HexPolyTheory.Interpret.interpret model.value model.zero_iff window).eval (value root)
  let marked root := Decidable.decide (0 < query root)
  let step (root : Descriptor parent.Value Signature parent.sign parent.signature)
      (state : Option (Result parent)) : Except Error (ForInStep (Option (Result parent))) := do
    let context := Algebraic.Context.adjoin root parent.isClean
    let some equation := ScalarPacket.buildParts context parent.codec polynomial | throw .equation
    if zero : equation.sign = 0 then
      let some enclosure := ScalarPacket.buildParts context parent.codec window | throw .enclosure
      if positive : enclosure.sign = 1 then
        if state.isSome then throw .ambiguous
        return .yield (some ⟨root,equation,enclosure,zero,positive⟩)
      else
        unless enclosure.sign = 0 || enclosure.sign = -1 do throw .enclosure
        return .yield state
    else throw .equation
  have advances (root) (member : root ∈ roots) (state : Option (Result parent))
      (capacity : marked root = true → state.isSome = false) :
      ∃ next, step root state = .ok (.yield next) ∧
        (if next.isSome then 1 else 0) =
          (if state.isSome then 1 else 0) + (if marked root then 1 else 0) := by
    let context := Algebraic.Context.adjoin root parent.isClean
    obtain ⟨equation,equationBuilt⟩ := ScalarPacket.buildParts_success model context parent.codec polynomial
    obtain ⟨enclosure,enclosureBuilt⟩ := ScalarPacket.buildParts_success model context parent.codec window
    have equationZero : equation.sign = 0 := by
      rw [ScalarPacket.buildParts_sign model context parent.codec polynomial equation equationBuilt,
        context.signPoly_spec model.value model.zero_iff model.one model.add model.sub
          model.mul model.nat model.sign model.neg model.inv]
      simp [Algebraic.Context.evalPoly, Algebraic.Context.rootValue, context,
        Algebraic.Context.root_adjoin, zero root member]
    have enclosureSign : enclosure.sign = (SignType.sign (query root) : Int) := by
      rw [ScalarPacket.buildParts_sign model context parent.codec window enclosure enclosureBuilt,
        context.signPoly_spec model.value model.zero_iff model.one model.add model.sub
          model.mul model.nat model.sign model.neg model.inv]
      simp [Algebraic.Context.evalPoly, Algebraic.Context.rootValue, context,
        Algebraic.Context.root_adjoin, query, value]
    dsimp only [context] at equationBuilt enclosureBuilt
    by_cases positive : 0 < query root
    · have enclosurePositive : enclosure.sign = 1 := enclosureSign.trans
        (congrArg (fun sign : SignType => (sign : Int)) (sign_eq_one_iff.mpr positive))
      have empty := capacity (by simp [marked,positive])
      refine ⟨some ⟨root,equation,enclosure,equationZero,enclosurePositive⟩, ?_, ?_⟩
      · simp [step,equationBuilt,enclosureBuilt,equationZero,enclosurePositive,empty,
          bind,Except.bind,pure,Except.pure]
      · simp [empty,marked,positive]
    · have allowed : enclosure.sign = 0 ∨ enclosure.sign = -1 := by
        rcases lt_or_eq_of_le (le_of_not_gt positive) with negative | equal
        · exact Or.inr (enclosureSign.trans
            (congrArg (fun sign : SignType => (sign : Int)) (sign_eq_neg_one_iff.mpr negative)))
        · exact Or.inl (by simpa [equal] using enclosureSign)
      have notOne : enclosure.sign ≠ 1 := by rcases allowed with h | h <;> omega
      refine ⟨state, ?_, ?_⟩
      · simp [step,equationBuilt,enclosureBuilt,equationZero,notOne,allowed,
          bind,Except.bind,pure,Except.pure]
      · simp [marked,positive]
  have loop (rest : List _) (members : ∀ root ∈ rest, root ∈ roots) (state : Option (Result parent))
      (count : (rest.filter marked).length + (if state.isSome then 1 else 0) = 1) :
      ∃ output, forIn rest state step = .ok output ∧ output.isSome = true := by
    induction rest generalizing state with
    | nil =>
      cases state with
      | none => simp at count
      | some source => exact ⟨some source, by simp [pure,Except.pure], rfl⟩
    | cons root rest ih =>
      have capacity : marked root = true → state.isSome = false := by
        intro positive
        have bound := count
        simp only [List.filter_cons,positive,↓reduceIte,List.length_cons] at bound
        cases occupied : state.isSome <;> simp_all
      obtain ⟨next,advanced,flags⟩ := advances root (members root (by simp)) state capacity
      have remaining : (rest.filter marked).length + (if next.isSome then 1 else 0) = 1 := by
        cases positive : marked root <;> simp [positive] at count flags <;> omega
      obtain ⟨output,returned,present⟩ := ih (fun root member => members root (by simp [member])) next remaining
      exact ⟨output, by simpa [List.forIn_cons,advanced,bind,Except.bind] using returned, present⟩
  obtain ⟨state,returned,present⟩ := loop roots (fun _ member => member) none (by simpa [marked,query,value] using one)
  cases state with
  | none => simp at present
  | some source =>
    refine ⟨source, ?_⟩
    change (do
      let state ← forIn roots (none : Option (Result parent)) step
      match state with
      | none => throw Error.unselected
      | some source => pure source) = .ok source
    simp [returned,bind,Except.bind,pure,Except.pure]

/-- Every successful selection from an arbitrary root list retains a member
of that list and independently accepted packets for the original two keys.
No singleton-list, producer-success or serialization premise is required. -/
theorem select_checks (model : Model parent ℝ)
    (polynomial window : DensePoly parent.Value)
    (roots : List (Descriptor parent.Value Signature parent.sign parent.signature))
    (result : Result parent) (produced : select polynomial window roots = .ok result) :
    result.root ∈ roots ∧
    result.equation.polynomial = Codec.poly parent.codec polynomial ∧
    result.enclosure.polynomial = Codec.poly parent.codec window ∧
    (let context := Algebraic.Context.adjoin result.root parent.isClean
     (ScalarPacket.read model parent.codec context result.equation.polynomial
       result.equation.sign result.equation.evidence).isSome = true ∧
     (ScalarPacket.read model parent.codec context result.enclosure.polynomial
       result.enclosure.sign result.enclosure.evidence).isSome = true) := by
  let checked (source : Result parent) : Prop :=
    source.root ∈ roots ∧
    source.equation.polynomial = Codec.poly parent.codec polynomial ∧
    source.enclosure.polynomial = Codec.poly parent.codec window ∧
    (let context := Algebraic.Context.adjoin source.root parent.isClean
     (ScalarPacket.read model parent.codec context source.equation.polynomial
       source.equation.sign source.equation.evidence).isSome = true ∧
     (ScalarPacket.read model parent.codec context source.enclosure.polynomial
       source.enclosure.sign source.enclosure.evidence).isSome = true)
  let invariant (state : Option (Result parent)) : Prop :=
    ∀ source, state = some source → checked source
  let step (root : Descriptor parent.Value Signature parent.sign parent.signature)
      (state : Option (Result parent)) : Except Error (ForInStep (Option (Result parent))) := do
    let context := Algebraic.Context.adjoin root parent.isClean
    let some equation := ScalarPacket.buildParts context parent.codec polynomial
      | throw .equation
    if zero : equation.sign = 0 then
      let some enclosure := ScalarPacket.buildParts context parent.codec window
        | throw .enclosure
      if positive : enclosure.sign = 1 then
        if state.isSome then throw .ambiguous
        return .yield (some ⟨root,equation,enclosure,zero,positive⟩)
      else
        unless enclosure.sign = 0 || enclosure.sign = -1 do throw .enclosure
        return .yield state
    else throw .equation
  have preserves (root) (member : root ∈ roots) (state) (valid : invariant state)
      (next) (returned : step root state = .ok next) : invariant next.value := by
    cases equationBuilt : ScalarPacket.buildParts (Algebraic.Context.adjoin root parent.isClean)
        parent.codec polynomial with
    | none => simp [step, equationBuilt, bind, Except.bind] at returned
    | some equation =>
      by_cases zero : equation.sign = 0
      · cases enclosureBuilt : ScalarPacket.buildParts (Algebraic.Context.adjoin root parent.isClean)
          parent.codec window with
        | none => simp [step, equationBuilt, zero, enclosureBuilt, bind, Except.bind] at returned
        | some enclosure =>
          by_cases positive : enclosure.sign = 1
          · by_cases occupied : state.isSome = true
            · simp [step, equationBuilt, zero, enclosureBuilt, positive, occupied,
                bind, Except.bind] at returned
            · simp [step, equationBuilt, zero, enclosureBuilt, positive, occupied,
                bind, Except.bind, pure, Except.pure] at returned
              cases returned
              have accepted : checked ⟨root,equation,enclosure,zero,positive⟩ :=
                ⟨member, ScalarPacket.buildParts_poly _ parent.codec polynomial equation equationBuilt,
                  ScalarPacket.buildParts_poly _ parent.codec window enclosure enclosureBuilt,
                  ScalarPacket.buildParts_accepted model _ parent.codec parent.codec_lawful
                    polynomial equation equationBuilt,
                  ScalarPacket.buildParts_accepted model _ parent.codec parent.codec_lawful
                    window enclosure enclosureBuilt⟩
              simpa [invariant] using accepted
          · by_cases allowed : enclosure.sign = 0 ∨ enclosure.sign = -1
            · simp [step, equationBuilt, zero, enclosureBuilt, positive, allowed,
                bind, Except.bind, pure, Except.pure] at returned
              cases returned
              exact valid
            · simp [step, equationBuilt, zero, enclosureBuilt, positive, allowed,
                bind, Except.bind] at returned
      · simp [step, equationBuilt, zero, bind, Except.bind] at returned
  have loop (rest : List _) (members : ∀ root ∈ rest, root ∈ roots)
      (state output) (valid : invariant state)
      (returned : forIn rest state step = .ok output) : invariant output := by
    induction rest generalizing state output with
    | nil =>
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at returned
      cases returned
      exact valid
    | cons root rest ih =>
      rw [List.forIn_cons] at returned
      cases advanced : step root state with
      | error cause => simp [advanced, bind, Except.bind] at returned
      | ok next =>
        have validNext := preserves root (members root (by simp)) state valid next advanced
        cases next with
        | done next =>
          simp [advanced, bind, Except.bind, pure, Except.pure] at returned
          cases returned
          exact validNext
        | yield next =>
          exact ih (fun root member => members root (by simp [member])) next output validNext
            (by simpa [advanced, bind, Except.bind] using returned)
  change (do
    let state ← forIn roots (none : Option (Result parent)) step
    match state with
    | none => throw Error.unselected
    | some source => pure source) = .ok result at produced
  cases returned : forIn roots (none : Option (Result parent)) step with
  | error cause => simp [returned, bind, Except.bind] at produced
  | ok state =>
    have valid := loop roots (fun _ member => member) none state
      (by intro source impossible; cases impossible) returned
    cases state with
    | none => simp [returned, bind, Except.bind] at produced
    | some source =>
      simp [returned, bind, Except.bind, pure, Except.pure] at produced
      cases produced
      exact valid result rfl

/-- Enumerate with the existing owner root producer and select exactly one
root using the supplied enclosure polynomial. The usual window is the source
isolating-square margin. Its original-source interpretation and selected-root
identity are subsequently checked by `SourceIdentity.quoteWith`; this producer
does not prove them, reconstruct a frozen parent, or establish completeness. -/
def build (polynomial window : DensePoly parent.Value) : Except Error (Result parent) := do
  let roots ← RootBuild.build polynomial |>.mapError Error.roots
  select polynomial window roots.roots

/-- A squarefree real head with exactly one positive window root produces a
source by complete enumeration. Coverage and absence of duplicate real roots
come from the owner's checked table; neither a native root list nor a
successful scalar production result is supplied as a premise. -/
theorem build_success (model : Model parent ℝ)
    (polynomial window : DensePoly parent.Value)
    (squarefree : Squarefree (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial))
    (unique : ∃! x : ℝ,
      x ∈ HexRealRootsTheory.Tarski.rootsIn
        (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial) .negInf .posInf ∧
      0 < (HexPolyTheory.Interpret.interpret model.value model.zero_iff window).eval x) :
    ∃ result, build polynomial window = .ok result := by
  classical
  obtain ⟨roots,enumerated⟩ := RootBuild.success model polynomial squarefree
  let value (root : Descriptor parent.Value Signature parent.sign parent.signature) :=
    root.root model.value model.zero_iff model.one model.add model.sub model.mul model.nat model.sign
  let positive (x : ℝ) := Decidable.decide
    (0 < (HexPolyTheory.Interpret.interpret model.value model.zero_iff window).eval x)
  let chosen := (roots.values model).filter positive
  have coverage := roots.coverage model
  obtain ⟨anchor,selected,only⟩ := unique
  have subset : chosen ⊆ [anchor] := by
    intro x member
    obtain ⟨root,window⟩ := List.mem_filter.mp member
    exact List.mem_singleton.mpr (only x ⟨(coverage.1 x).mpr root, of_decide_eq_true window⟩)
  have bound : chosen.length ≤ 1 := by
    simpa using (coverage.2.filter positive).length_le_of_subset subset
  have present : anchor ∈ chosen :=
    List.mem_filter.mpr ⟨(coverage.1 anchor).mp selected.1, by simpa [positive] using selected.2⟩
  have nonzero : chosen.length ≠ 0 := by
    intro empty
    simp [List.length_eq_zero_iff.mp empty] at present
  have one : chosen.length = 1 := by omega
  have mapped : (roots.roots.filter (fun root => positive (value root))).map value = chosen := by
    simp only [chosen, RootReplay.Result.values, List.filter_map, Function.comp_def, value]
  have count : (roots.roots.filter fun root => Decidable.decide (0 <
      (HexPolyTheory.Interpret.interpret model.value model.zero_iff window).eval
        (root.root model.value model.zero_iff model.one model.add model.sub model.mul
          model.nat model.sign))).length = 1 := by
    change (roots.roots.filter (fun root => positive (value root))).length = 1
    rw [← List.length_map value, mapped]
    exact one
  obtain ⟨result,produced⟩ := select_success model polynomial window roots.roots
    (fun root member => ((HexRealRootsTheory.Tarski.mem_rootsIn_iff _ squarefree.ne_zero _ _ _).mp
      (roots.root_spec model root member)).1) count
  refine ⟨result, ?_⟩
  simp [build,enumerated,Except.mapError,produced,bind,Except.bind]

/-- Successful enumeration retains the exact original full descriptor, an
actual real root and independently accepted original equation/window packets.
The root and serialization facts are checked conclusions, not assumptions.
Predecessor reconstruction and source-alias identification remain separate. -/
theorem build_checked (model : Model parent ℝ)
    (polynomial window : DensePoly parent.Value) (result : Result parent)
    (produced : build polynomial window = .ok result) :
    ∃ word, result.root.raw = (RootReplay.subject polynomial .negInf .posInf).full word ∧
      result.root.root model.value model.zero_iff model.one model.add model.sub model.mul
        model.nat model.sign ∈ HexRealRootsTheory.Tarski.rootsIn
          (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial)
          .negInf .posInf ∧
      result.equation.polynomial = Codec.poly parent.codec polynomial ∧
      result.enclosure.polynomial = Codec.poly parent.codec window ∧
      (let context := Algebraic.Context.adjoin result.root parent.isClean
       (ScalarPacket.read model parent.codec context result.equation.polynomial
         result.equation.sign result.equation.evidence).isSome = true ∧
       (ScalarPacket.read model parent.codec context result.enclosure.polynomial
         result.enclosure.sign result.enclosure.evidence).isSome = true) := by
  cases enumerated : RootBuild.build polynomial with
  | error cause => simp [build, enumerated, Except.mapError, bind, Except.bind] at produced
  | ok roots =>
    have selected : select polynomial window roots.roots = .ok result := by
      simpa [build, enumerated, Except.mapError, bind, Except.bind] using produced
    obtain ⟨member,equation,enclosure,accepted⟩ :=
      select_checks model polynomial window roots.roots result selected
    obtain ⟨word,raw⟩ := roots.fields result.root member
    exact ⟨word,raw,roots.root_spec model result.root member,equation,enclosure,accepted⟩

/-- The real uniqueness condition yields actual production and accepted
literal packets together, retaining the exact full descriptor and original
keys. This is source-packet progress, not arbitrary history reconstruction or
completeness of the full source-goal tactic. -/
theorem build_checks (model : Model parent ℝ)
    (polynomial window : DensePoly parent.Value)
    (squarefree : Squarefree (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial))
    (unique : ∃! x : ℝ,
      x ∈ HexRealRootsTheory.Tarski.rootsIn
        (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial) .negInf .posInf ∧
      0 < (HexPolyTheory.Interpret.interpret model.value model.zero_iff window).eval x) :
    ∃ result, build polynomial window = .ok result ∧
      ∃ word, result.root.raw = (RootReplay.subject polynomial .negInf .posInf).full word ∧
        result.root.root model.value model.zero_iff model.one model.add model.sub model.mul
          model.nat model.sign ∈ HexRealRootsTheory.Tarski.rootsIn
            (HexPolyTheory.Interpret.interpret model.value model.zero_iff polynomial)
            .negInf .posInf ∧
        result.equation.polynomial = Codec.poly parent.codec polynomial ∧
        result.enclosure.polynomial = Codec.poly parent.codec window ∧
        (let context := Algebraic.Context.adjoin result.root parent.isClean
         (ScalarPacket.read model parent.codec context result.equation.polynomial
           result.equation.sign result.equation.evidence).isSome = true ∧
         (ScalarPacket.read model parent.codec context result.enclosure.polynomial
           result.enclosure.sign result.enclosure.evidence).isSome = true) := by
  obtain ⟨result,produced⟩ := build_success model polynomial window squarefree unique
  exact ⟨result,produced,build_checked model polynomial window result produced⟩

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

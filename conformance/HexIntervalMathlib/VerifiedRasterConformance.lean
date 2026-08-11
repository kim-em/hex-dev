/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.Centered
import HexIntervalMathlib.Experiment.VerifiedRaster
import HexInterval.Experiment.PayloadSession
import HexInterval.Experiment.ProofEmitter

/-!
# Verified raster graph conformance

This is a bounded end-to-end prototype.  A live arbitrary-function package
proposes the exact range `[0,1/4]` for its opaque centered operation on
`[0,1]`; generic proof replay turns that proposal into a theorem.  The theorem
then certifies a 2-by-2 mask over `[0,1] × [0,1/2]`.

Rows run from bottom to top and columns from left to right.  The left column is
`[0,1/2)` and the right column is `[1/2,1]`.  The lower row is `[0,1/4]`
and the upper row is `(1/4,1/2]`.  Consequently every boundary point belongs
to exactly one column and one row.  The lower two pixels are marked and the
upper two are blank.
-/

namespace Hex.IntervalMathlib.VerifiedRasterConformance

open Hex.Interval Hex.Interval.Experiment
open Propagator PayloadArena PayloadSession SemanticReplay ChronologicalReplay ProofEmitter
open DyadicInterval DyadicRules Centered VerifiedRaster

private def real : DomainId := { index := 0 }
private def sourceKey : OpKey := { name := "verified-raster.source" }

private def operations : Array Operation :=
  ((arithmeticOperations real).push
    { key := sourceKey, inputs := [], output := real }).push
      { key := centeredOp, inputs := [real], output := real }

private def sourceInstruction : Node :=
  { domain := real, op := { index := 6 }, args := [] }

private def curveInstruction : Node :=
  { domain := real, op := { index := 7 }, args := [{ index := 0 }] }

private def program : Program :=
  { operations, nodes := #[sourceInstruction, curveInstruction] }

private def config : Config :=
  { endpointLimit := Centered.endpointLimit
    reciprocalBasePrecision := 2
    maxReciprocalEffort := 0 }

private def limits : Propagator.Limits :=
  { maxOperations := 16
    maxNodes := 8
    maxRules := 8
    maxRegistryEntries := 16
    maxReplayFormats := 8
    maxArity := 2
    maxApplications := 16
    maxQueueEntries := 32
    maxActions := 16
    maxAcceptedFacts := 8
    maxRetainedSuggestions := 8
    maxEffort := 0
    maxObservationValue := 32
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 2
    maxOutcomeSuggestions := 2
    maxProposalItems := 4
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 4
    maxEqualities := 0
    splitEndpointLimit := Centered.endpointLimit }

private def arenaLimits : PayloadArena.Limits :=
  { maxEntries := PayloadSession.requiredUses limits
    maxBodyCells := 0
    maxDrafts := PayloadSession.requiredUses limits
    maxDraftCells := 0
    maxAtom := 0
    maxSchema := 0
    maxUses := PayloadSession.requiredUses limits }

private def session? : Option (PayloadSession.Session DyadicInterval.Fact) :=
  match PayloadSession.Session.start
      (DyadicInterval.factDomain Centered.endpointLimit) program
      #[centeredPackage config real] #[unitRange, .whole]
      limits arenaLimits with
  | .ok session => some session
  | .error _ => none

private def run? : Option (PayloadSession.Run DyadicInterval.Fact) := do
  let session ← session?
  pure (session.drive 8)

private def node (index : Nat) : NodeId := { index }
private def payload : PayloadId := { index := 0 }

private def action : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := centeredForwardKey
    node := node 1
    kind := .forward
    effort := 0
    generation := 0
    inputs := [{ node := node 0, version := 0 }]
    writes := [node 1] }

private def event : FactEvent DyadicInterval.Fact :=
  { programVersion := 0
    node := node 1
    previous := { node := node 1, version := 0 }
    fact := quarterRange
    version := 1
    cause := .rule action quarterRange payload }

private def entry : Entry :=
  { origin := action, role := .fact, schema := 0, body := [] }

private def step : RuleStep DyadicInterval.Fact :=
  { event, payload, entry
    assumptions := [{ node := node 0, fact := unitRange }]
    previous := .whole }

private def sameEntry (left right : Entry) : Bool :=
  left.origin == right.origin && left.role == right.role &&
    left.schema == right.schema && left.body == right.body

private def sameEvent (left right : FactEvent DyadicInterval.Fact) : Bool :=
  left.programVersion == right.programVersion && left.node == right.node &&
    left.previous == right.previous && left.fact == right.fact &&
    left.version == right.version &&
      match left.cause, right.cause with
      | .rule leftAction leftFact leftPayload,
          .rule rightAction rightFact rightPayload =>
          leftAction == rightAction && leftFact == rightFact &&
            leftPayload == rightPayload
      | .transport leftEquality leftSource,
          .transport rightEquality rightSource =>
          leftEquality == rightEquality && leftSource == rightSource
      | _, _ => false

private def quoteIsLive : Bool :=
  match run? with
  | some run =>
      run.stop == .saturated && run.session.complete &&
        run.session.engine.history.size == 1 &&
        run.session.arena.entries.size == 1 &&
        match run.session.engine.history[0]?,
            run.session.arena.entry? payload .fact with
        | some actualEvent, some actualEntry =>
            sameEvent actualEvent event && sameEntry actualEntry entry
        | _, _ => false
  | none => false

#guard quoteIsLive

private def checkerInput : CheckerInput DyadicInterval.Fact :=
  { baseProgram := program
    initialFacts := #[unitRange, .whole]
    target := { node := node 1, fact := quarterRange } }

private def base : List (NodeFact DyadicInterval.Fact) :=
  [{ node := node 0, fact := unitRange }, { node := node 1, fact := .whole }]

private def inputSound : Evidence
    (Centered.semantics.Entails program base
      { node := node 0, fact := unitRange }) :=
  ProofEmitter.assumed (by simp [base])

private def previousSound : Evidence
    (Centered.semantics.Entails program base
      { node := node 1, fact := step.previous }) := by
  apply ProofEmitter.assumed
  simp [step, base]

private def assumptionsSound : Evidence
    (InputsSound Centered.semantics program base step.assumptions) := by
  simpa [step, event] using (EntailsList.singleton inputSound)

private def replayed :=
  ProofEmitter.replayRule Centered.centeredFactSchema Centered.domain
    checkerInput program (ProgramPrefix.refl program) base step
    previousSound assumptionsSound

#guard replayed.isSome

/-- The exact live package quote replayed as an ordinary theorem. -/
theorem emittedRange :
    Centered.semantics.Entails program base checkerInput.target := by
  exact ProofEmitter.proofOfReplay replayed (by rfl)

private noncomputable def curve (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) - (x - (1 / 2 : ℝ)) ^ 2

private noncomputable def valuation (x : ℝ) : NodeId → ℝ
  | ⟨0⟩ => x
  | ⟨1⟩ => curve x
  | _ => 0

private theorem models (x : ℝ) : Centered.Models program (valuation x) := by
  intro output instruction found operation operationFound key
  rcases output with ⟨index⟩
  cases index with
  | zero =>
      simp [Program.node?, program, sourceInstruction] at found
      subst instruction
      simp [Program.operation?, program, operations, arithmeticOperations,
        sourceKey, centeredOp] at operationFound
      subst operation
      simp [centeredOp] at key
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, program, curveInstruction] at found
          subst instruction
          refine ⟨node 0, rfl, ?_⟩
          simp [node, valuation, curve]
      | succ index =>
          simp [Program.node?, program] at found

/-- The interval theorem consumed by raster assembly.  Its proof passes
through the generic replay boundary above, not a function case in the raster
layer. -/
private theorem curveRange (x : ℝ) (nonnegative : 0 ≤ x) (atMostOne : x ≤ 1) :
    0 ≤ curve x ∧ curve x ≤ 1 / 4 := by
  have result := emittedRange (valuation x) (models x) (by
    intro assumption member
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change unitRange.Contains (valuation x (node 0))
      simpa only [unitRange, DyadicInterval.Fact.Contains, rawContains,
        lowerContains, upperContains, DyadicInterval.toReal_zero,
        Centered.toReal_one, node, valuation, and_true] using
          And.intro nonnegative atMostOne
    · change DyadicInterval.Fact.whole.Contains (valuation x (node 1))
      simp [DyadicInterval.Fact.Contains, DyadicInterval.Fact.whole,
        rawContains, lowerContains, upperContains])
  change quarterRange.Contains (valuation x (node 1)) at result
  simpa only [quarterRange, DyadicInterval.Fact.Contains, rawContains,
    lowerContains, upperContains, DyadicInterval.toReal_zero,
    Centered.toReal_quarter, node, valuation, curve, and_true] using result

private def leftX : DyadicInterval.Fact :=
  ⟨.bounds (.finite 0 false) (.finite half true), by decide⟩

private def rightX : DyadicInterval.Fact :=
  ⟨.bounds (.finite half false) (.finite 1 false), by decide⟩

private def upperY : DyadicInterval.Fact :=
  ⟨.bounds (.finite quarter true) (.finite half false), by decide⟩

private def viewportY : DyadicInterval.Fact :=
  ⟨.bounds (.finite 0 false) (.finite half false), by decide⟩

private def lowerLeft : Pixel :=
  { x := leftX, y := quarterRange, marked := true }

private def lowerRight : Pixel :=
  { x := rightX, y := quarterRange, marked := true }

private def upperLeft : Pixel :=
  { x := leftX, y := upperY, marked := false }

private def upperRight : Pixel :=
  { x := rightX, y := upperY, marked := false }

/-- Bottom-to-top, left-to-right 2-by-2 raster. -/
def raster : Raster :=
  { width := 2
    height := 2
    xViewport := unitRange
    yViewport := viewportY
    cells := [lowerLeft, lowerRight, upperLeft, upperRight]
    shape := by decide }

private def mask : List Bool := raster.cells.map (fun pixel => pixel.marked)

#guard mask == [true, true, false, false]

/-- The coverage obligation is not vacuous: the concrete horizontal viewport
contains an ordinary real point. -/
theorem rasterNonempty : ∃ x : ℝ, raster.xViewport.Contains x := by
  refine ⟨0, ?_⟩
  simp [raster, unitRange, DyadicInterval.Fact.Contains, rawContains,
    lowerContains, upperContains, DyadicInterval.toReal_zero,
    Centered.toReal_one]

private theorem inLeft {x : ℝ} (inside : leftX.Contains x) :
    0 ≤ x ∧ x < 1 / 2 := by
  simpa [leftX, DyadicInterval.Fact.Contains, rawContains, lowerContains,
    upperContains, DyadicInterval.toReal_zero, Centered.toReal_half] using inside

private theorem inRight {x : ℝ} (inside : rightX.Contains x) :
    1 / 2 ≤ x ∧ x ≤ 1 := by
  simpa [rightX, DyadicInterval.Fact.Contains, rawContains, lowerContains,
    upperContains, Centered.toReal_half, Centered.toReal_one] using inside

private theorem inViewport {x : ℝ} (inside : unitRange.Contains x) :
    0 ≤ x ∧ x ≤ 1 := by
  simpa [unitRange, DyadicInterval.Fact.Contains, rawContains, lowerContains,
    upperContains, DyadicInterval.toReal_zero, Centered.toReal_one] using inside

private theorem inLower {y : ℝ} (inside : quarterRange.Contains y) :
    0 ≤ y ∧ y ≤ 1 / 4 := by
  simpa [quarterRange, DyadicInterval.Fact.Contains, rawContains, lowerContains,
    upperContains, DyadicInterval.toReal_zero, Centered.toReal_quarter] using inside

private theorem inUpper {y : ℝ} (inside : upperY.Contains y) :
    1 / 4 < y ∧ y ≤ 1 / 2 := by
  simpa [upperY, DyadicInterval.Fact.Contains, rawContains, lowerContains,
    upperContains, Centered.toReal_quarter, Centered.toReal_half] using inside

private theorem leftContained {x : ℝ} (inside : leftX.Contains x) :
    unitRange.Contains x := by
  have bounds := inLeft inside
  simpa [unitRange, DyadicInterval.Fact.Contains, rawContains, lowerContains,
    upperContains, DyadicInterval.toReal_zero, Centered.toReal_one] using
      And.intro bounds.1 (le_trans (le_of_lt bounds.2) (by norm_num))

private theorem rightContained {x : ℝ} (inside : rightX.Contains x) :
    unitRange.Contains x := by
  have bounds := inRight inside
  simpa [unitRange, DyadicInterval.Fact.Contains, rawContains, lowerContains,
    upperContains, DyadicInterval.toReal_zero, Centered.toReal_one] using
      And.intro (le_trans (by norm_num) bounds.1) bounds.2

private theorem lowerContained {y : ℝ} (inside : quarterRange.Contains y) :
    viewportY.Contains y := by
  have bounds := inLower inside
  simpa [viewportY, DyadicInterval.Fact.Contains, rawContains, lowerContains,
    upperContains, DyadicInterval.toReal_zero, Centered.toReal_half] using
      And.intro bounds.1 (le_trans bounds.2 (by norm_num))

private theorem upperContained {y : ℝ} (inside : upperY.Contains y) :
    viewportY.Contains y := by
  have bounds := inUpper inside
  simpa [viewportY, DyadicInterval.Fact.Contains, rawContains, lowerContains,
    upperContains, DyadicInterval.toReal_zero, Centered.toReal_half] using
      And.intro (le_trans (by norm_num) (le_of_lt bounds.1)) bounds.2

/-- The finite mask is a sound conservative rendering of the opaque centered
operation.  In particular, every blank pixel is proved blank.  The statement
does not claim that every marked pixel is hit. -/
theorem centeredRasterCorrect : Correct raster curve := by
  constructor
  · intro pixel member x y inside
    simp only [raster, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨leftContained inside.1, lowerContained inside.2⟩
    · exact ⟨rightContained inside.1, lowerContained inside.2⟩
    · exact ⟨leftContained inside.1, upperContained inside.2⟩
    · exact ⟨rightContained inside.1, upperContained inside.2⟩
  · intro x inside
    have domain := inViewport inside
    have range := curveRange x domain.1 domain.2
    by_cases left : x < 1 / 2
    · refine ⟨lowerLeft, by simp [raster], rfl, ?_⟩
      exact ⟨by
        change leftX.Contains x
        simpa [leftX, DyadicInterval.Fact.Contains, rawContains, lowerContains,
          upperContains, DyadicInterval.toReal_zero, Centered.toReal_half]
            using And.intro domain.1 left,
        by
          change quarterRange.Contains (curve x)
          simpa [quarterRange, DyadicInterval.Fact.Contains, rawContains,
            lowerContains, upperContains, DyadicInterval.toReal_zero,
            Centered.toReal_quarter] using range⟩
    · refine ⟨lowerRight, by simp [raster], rfl, ?_⟩
      exact ⟨by
        change rightX.Contains x
        simpa [rightX, DyadicInterval.Fact.Contains, rawContains, lowerContains,
          upperContains, Centered.toReal_half, Centered.toReal_one]
            using And.intro (le_of_not_gt left) domain.2,
        by
          change quarterRange.Contains (curve x)
          simpa [quarterRange, DyadicInterval.Fact.Contains, rawContains,
            lowerContains, upperContains, DyadicInterval.toReal_zero,
            Centered.toReal_quarter] using range⟩
  · intro pixel member blank x inside
    simp only [raster, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · contradiction
    · contradiction
    · intro inBlank
      have xBounds := inLeft inside
      have range := curveRange x xBounds.1 (le_trans (le_of_lt xBounds.2) (by norm_num))
      have yBounds := inUpper inBlank
      linarith
    · intro inBlank
      have xBounds := inRight inside
      have range := curveRange x (le_trans (by norm_num) xBounds.1) xBounds.2
      have yBounds := inUpper inBlank
      linarith

/--
info: 'Hex.IntervalMathlib.VerifiedRasterConformance.centeredRasterCorrect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms centeredRasterCorrect

end Hex.IntervalMathlib.VerifiedRasterConformance

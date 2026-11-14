/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import VersoManual
import HexRCF.RealCoefficients
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

#doc (Manual) "Specialization and ordinary real enclosures" =>
%%%
tag := "hex-rcf-specialization-enclosures"
%%%

The explicit preparation API is
{name}`Hex.RCF.RealCoefficients.Coefficients.prepare`. It returns authenticated
fixed-field coordinates in the original coefficient order, their identities
with the closed source expressions, and every original divisor before
cancellation. Rational-only sources remain with the existing base solver;
unsupported exact sources return a structured decline, while authentication,
search and kernel failures are terminal.

{name}`Hex.RCF.RealCoefficients.Coefficients.Coordinates.build` returns a frozen
certificate for either verdict.
{name}`Hex.RCF.RealCoefficients.Coefficients.Coordinates.check` checks the exact
expected sentence, coefficients and original divisors, then quotes finite
real-cell evidence and transports a true result to the original goal. It
does not repeat search or require a quoted common-field irreducibility proof.
False certificates remain diagnostic. A failed attempt restores caller state.
Before production or replay, the API binds the polynomial, selected root,
matrix, quantifier, coefficients and divisor coordinates to their stored
expressions, checking source, valuation and original-divisor proofs at their
required types. Edited records fail input validation before a false verdict.
Validation-only checks leave no unused theorem declarations.
The tactic assembles its freshly constructed data through a private path;
the dispatcher checks its complete original-goal proof. The comparison option
`rcf.algebraic.validateFresh` repeats public validation for fresh tactic data
and defaults to false. Public preparation and replay always validate editable
inputs independently of this comparison control.
The existing `rcf` tactic retains its documented quotation options.

This direct frontend example separates preparation, production and replay:

```lean
open Lean Meta Elab Tactic Hex.RCF.RealCoefficients

elab "prepared_rcf" : tactic => do
  let goal ← getMainGoal
  let .ok prepared ← Coefficients.prepare (← goal.getType) |
    throwError "unsupported algebraic coefficient source"
  let certificate ← prepared.build
  let proof ← prepared.check certificate
  goal.assign proof
  replaceMainGoal []

example : ∀ x : ℝ,
    x^2 + 1 / (Real.sqrt 2 + 1) > 0 := by prepared_rcf
```

The explicit
{name}`Hex.RCF.RealCoefficients.Coefficients.Coordinates.buildTotal` method
uses complete algebraic root construction rather than a finite refinement
allowance. Its result uses the same frozen checker. The convenience method
`proveTotal` builds and checks the certificate. These calls can take longer
than a bounded attempt; they do not change the default `rcf` resource limits.
For example, this direct API proof disables the quick bisection strategy:

```lean
set_option rcf.algebraic.directDepth 0 in
example : ∃ x : ℝ,
    x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by
  run_tac do
    let goal ← getMainGoal
    let .ok prepared ←
      Coefficients.prepare (← goal.getType) |
      throwError "unsupported algebraic coefficient source"
    let certificate ← prepared.buildTotal
    goal.assign (← prepared.check certificate)
    replaceMainGoal []
```

{name}`Hex.RCF.RealCoefficients.FieldCells.produce` constructs the complete
root/cell evidence for the grouped source polynomials, recording every required
sign and original divisor. It normalizes the carrier core to be monic, retaining
checked identities with the original product. This grouped producer and
`Replay.buildCellsTotal` both default to direct depth 256. The prepared method
passes `rcf.algebraic.directDepth`, also defaulting to 256.
{name}`Hex.RCF.RealCoefficients.Replay.buildCellsTotal_spec` proves that each
valid prepared algebraic input produces an accepted correct Boolean answer:

```lean
open Hex Hex.RCF.RealCoefficients

example {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s}
    {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p]
    {Ctx : Type} [DecidableEq Ctx]
    (input : Replay.Input p s hw hp Ctx n)
    (real : s.meetsRealAxis = true) (depth : Nat)
    (domains : ∀ divisor ∈ input.divisors, divisor ≠ 0) :
    ∃ cert value,
      Replay.buildCellsTotal input real depth = .ok cert ∧
      Replay.checkCells input cert = .ok value ∧
      (value = true ↔ input.toProp) :=
  Replay.buildCellsTotal_spec input real depth domains
```

The field instance above justifies native construction. Frozen acceptance and
the resulting source proof require no new irreducibility theorem for the
combined coefficient field. This theorem starts after source authentication;
it does not prove preparation complete for every closed algebraic expression.

{name}`Hex.RCF.RealCoefficients.Coefficients.prepareField` retains explicit
whole-field preparation into an editable `Environment`. Its
{name}`Hex.RCF.RealCoefficients.Coefficients.Environment.proveReplay` and
`proveTotalReplay` methods independently validate the quoted irreducibility
proof before using the corresponding legacy field replay laws.

{name}`Hex.RCF.RealCoefficients.Replay.Input` records the coefficient order,
shared formula, quantifier, original divisor coordinates and context. Its type
fixes the defining polynomial and the selected root. Domain restrictions remain
formula atoms. The prepared-coordinate `build` method uses bounded root/cell
production and checks all original divisors before searching.
{name}`Hex.RCF.RealCoefficients.Replay.checkCells` reads only frozen evidence, returning
an accepted Boolean or a structured binding, divisor, evidence or unresolved
error. It never repeats root isolation, gcd or sign search. An accepted false
verdict is diagnostic and provides no proof of the user's goal.

{name}`Hex.RCF.RealCoefficients.Replay.checkCells_domains` proves that every retained
original divisor is nonzero at the selected embedding, even for a zero atom or
an empty domain. {name}`Hex.RCF.RealCoefficients.Replay.checkCells_spec` identifies the
accepted Boolean with the fixed-field real sentence.

```lean
open Hex Hex.RCF.RealCoefficients

example {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s}
    {hp : (mahlerPrec p : Int) ≤ s.prec}
    {Ctx : Type} [DecidableEq Ctx]
    (input : Replay.Input p s hw hp Ctx n)
    (cert : Replay.Certificate p s hw hp Ctx n)
    (accepted : Replay.checkCells input cert = .ok true) :
    input.toProp :=
  Replay.checkCells_sound input cert accepted
```

For an already authenticated exact field,
{name}`Hex.RCF.RealCoefficients.Replay.buildTotal` uses the existing complete
producer rather than a finite refinement limit. It preflights every original
divisor before production and preserves false as a diagnostic.
{name}`Hex.RCF.RealCoefficients.Replay.buildTotal_spec` proves that each valid
input produces an accepted correct verdict, independently of the direct
proposal depth. The nonzero-divisor hypothesis below describes valid input;
certificate acceptance and the verdict are conclusions.

```lean
example {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s}
    {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p]
    {Ctx : Type} [DecidableEq Ctx]
    (input : Replay.Input p s hw hp Ctx n)
    (real : s.meetsRealAxis = true) (depth : Nat)
    (domains : ∀ divisor ∈ input.divisors, divisor ≠ 0) :
    ∃ cert value,
      Replay.buildTotal input real depth = .ok cert ∧
      Replay.check input cert = .ok value ∧
      (value = true ↔ input.toProp) :=
  Replay.buildTotal_spec input real depth domains
```

{name}`Hex.RCF.RealCoefficients.Coefficients.Environment.proveTotalReplay`
quotes the resulting finite evidence and transports the accepted true verdict
to the exact original target. Its fresh Ioc proof regression uses direct depth
zero; the generated proof contains no producer or search call. This explicit
API retains raw carrier production and does not change the bounded `rcf`
default. It does not prove recognition or irreducibility quotation complete
for every closed algebraic source, or make Lean elaboration resource limits
unbounded. The total producer has no finite search budget. Native production
runs synchronously without heartbeat or cancellation polls inside the call;
cancellation is polled after the production result is matched in meta code. Quotation and
kernel checking retain Lean’s ordinary resource limits.

The legacy `Environment` replay API uses linear recorded-sign lookup and one
kernel decision. The coordinate API shares the tactic's finite quotation,
including its indexed lookup and split/combined replay options. Both paths use
the same literal evidence reduction lemmas. Original guard coordinates remain
in the public certificate even after
cancellation; exact nonvanishing and their source identities are checked
separately from the quantifier fold.

This fixed-field API covers the documented exact algebraic fragment. The
caller-registration path below has its own frozen bounds and subject/version
bindings; it does not supply a total field for general root algorithms. General
frontend certification and tower realization remain incomplete.

The shared formula records coefficient parameters and the quantified variable.
Specialization evaluates the parameters in their fixed real embeddings and
combines equal powers of the variable. Leading terms can disappear when
independently named coefficients denote the same value.
{name}`Hex.RCF.RealCoefficients.Specialize.degree` proves that the resulting
polynomial's degree agrees with its real interpretation, including constants
and zero. {name}`Hex.RCF.RealCoefficients.FieldSpecialize.literal_degree` gives
the same guarantee for the literal fixed-field compiler.

{name}`Hex.RCF.RealCoefficients.Specialize.prepare` and
{name}`Hex.RCF.RealCoefficients.FieldSpecialize.prepare` retain all atoms in the
shared traversal, including repeated atoms, zero polynomials and domain guards.
Their `prepare_eval` and `prepare_degrees` laws apply after coefficient
cancellation; filtering zero polynomials for carrier construction does not
remove their Boolean atoms or original divisor conditions.

```lean
open Hex.RCF.RealCoefficients

example (values : Fin n → Hex.RealAlgebraicNumber)
    (p : Hex.RealFormula.Poly (n + 1)) :
    ((HexPolyTheory.toPolynomial
      (Specialize.polynomial values p)).map
      Hex.RealAlgebraicNumber.toRealHom).natDegree =
      (Specialize.polynomial values p).natDegree :=
  Specialize.degree values p

example (root : Hex.RealAlgebraicNumber)
    (precision : Nat) :
    (rootInterval root precision).isSome = true := by
  obtain ⟨interval, produced, _, _, _⟩ :=
    rootInterval_spec root precision
  rw [produced]
  rfl
```

{name}`Hex.RCF.RealCoefficients.rootInterval_spec` also proves that the root
lies strictly between the returned endpoints and that their distance is at
most `4 · 2⁻precision`. The extra dyadic margin keeps exact rational roots,
including zero, inside an interval of positive width.
{name}`Hex.RCF.RealCoefficients.rootInterval_progress` proves that every
precision schedule tending to infinity eventually reaches any positive width
request. These points and endpoints are ordinary real numbers. The algebraic
tactic doubles fallback precision within its configured refinement budget.

{name}`Hex.RCF.RealCoefficients.proposeIsolations_isSome_iff` establishes
finite proposal production for exactly the nonzero dense heads. The canonical
solver receives exactly the interpreted polynomial. Zero has a universal
root set; a nonzero constant has an empty finite set. This is the direct
canonical-carrier API. The tactic specializes to fixed-field coordinates,
squarefrees its carrier and checks proposed intervals over those coordinates;
its fallback uses these same strict enclosures.

{name}`Hex.RCF.RealCoefficients.isolateAt_progress` proves that every nonzero
squarefree canonical head eventually yields accepted isolation evidence along
any precision schedule tending to infinity. Separation, root-free endpoints,
complete root coverage and interval counts are derived using the owner's
complete sorted root list and the literal Sturm checker.
{name}`Hex.RCF.RealCoefficients.FieldBuild.isolateAt_progress` gives the same
guarantee over original fixed-field coordinates at a checked selected real
embedding, including the complete selected-field fallback after bounded direct
search fails. `FieldBuild.roots_meaning` identifies the owner's root output
with the original real polynomial; `roots_sorted` and `roots_finite` give
its distinct ordered finite list for every nonzero head. `proposeRoots_spec`
and `proposeRoots_accepted` derive complete coverage and accepted replay from
strict enclosures of that list.
The corresponding `isolate` entry points double successive precisions and
return isolation evidence together with its checker acceptance proof and
exact binding to the builder that produced the shared squarefree chain.
The preferred fixed-field search and complete root solving run once.
The fallback passes the polynomial to the existing number-field root driver
in its selected presentation. Refinement repeats interval construction and gap checks;
the accepted Sturm replay evidence is built once after the gaps pass.
These are compiled producers. A quoted proof must recheck the emitted literal
certificate in the ordinary kernel.
Their termination follows from these progress laws for nonzero squarefree
inputs. The bounded `build`/`isolateAt` interfaces remain available for callers
that choose an explicit precision.

{name}`Hex.RCF.RealCoefficients.FieldRootSigns.Table.build_success` proves
that atom-query production succeeds after isolation construction succeeds.
Queries retain the shared squarefree chain and are checked at the same root
interval and original head.
{name}`Hex.RCF.RealCoefficients.FieldBuild.isolateFormula_queries` composes
this query production with the total formula isolation entry point.

{name}`Hex.RCF.RealCoefficients.RadicalCert.build_success_real` proves that
the actual bounded derivative-gcd quotient search produces accepted radical
evidence for every nonzero head under the checked real arithmetic interpretation.
{name}`Hex.RCF.RealCoefficients.RadicalCert.build_squarefree` derives
squarefreeness of the returned core from the producer's exact quotient and the
owner's Yun invariant. It is not a hypothesis supplied to the radical checker.
Nonzero constants are included; zero still has no finite root list.
The core need not be monic: for `X³` the raw derivative gcd yields `X/3`.

The executable `RadicalCert.reduce` entry point takes the proved progress law,
returns the builder's certificate and retains exact production binding plus
literal acceptance. The real interpretation is used only in the proof, so a
fixed field's noncomputable real embedding is not passed to compiled arithmetic.

{name}`Hex.RCF.RealCoefficients.FieldBuild.isolateFormula` composes this
reduction with precision search for the complete shared formula carrier,
including repeated/common roots, zero atoms and formulas without atoms.
The shared formula keeps its guard atoms, whose nonzero endpoint polynomials
enter the carrier. Squarefreeness is derived before isolation; it is not an
extra admission required from the caller.
The complete library pipeline consumes this root envelope through
{name}`Hex.RCF.RealCoefficients.FieldBuild.produce`. This compiled producer
constructs the radical, complete root isolations, every atom query and a finite
rational sign table, returning checker acceptance and a recorded hit for every
replay or open-cell sign operand. Exact duplicate coordinate keys share one
sign-table entry. The chosen literal square fixes the rational count-one
interval used for all coordinate signs. The producer captures a prepared domain
as data before building its sign closure.
{name}`Hex.RCF.RealCoefficients.Field.prepareSign_spec` proves that prepared
rational Tarski queries give the selected real embedding's signs. Search does
not isolate a new algebraic number for each coordinate sign.
{name}`Hex.RCF.RealCoefficients.FieldBuild.build_progress` also proves success
of the bounded builder along every cofinal precision schedule. That builder
also captures its prepared rational sign domain once, rather than converting
each coordinate into a separate algebraic number.

The `Result.allValue` and `Result.anyValue` compiled folds use only recorded
signs. Their `forall_decision` and `exists_decision` theorems prove that the
strict Boolean result is defined and agrees with the real quantified formula.
A valid envelope for a false sentence yields a false diagnostic; it is never
assigned as a proof. These laws cover fixed-field algebraic decision after
source authentication. They do not assert total registered-constant search or
unbounded elaboration of every quoted proof. Kernel quotation still checks the
literal certificate and the exact original-goal equivalence. General nested
joint realization and the remaining adapter evidence obligations are separate.

```lean
example : ∀ x : ℝ,
    x ^ 2 - 2 * Real.sqrt 2 * x + 2 ≥ 0 := by rcf

example : ∃ x : ℝ,
    x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by rcf
```

The first example has a repeated root at the selected positive square root;
the second produces a further algebraic root and checks simultaneous sign
conditions on that section. Both use the optional algebraic handler, with
ordinary real sectors between its root sections. The explicit legacy
`FieldBuild.produce` API
accepts a direct bisection depth, defaulting to 256, before its proved
selected-field fallback. Both the complete producer and frontend retain that
field presentation and share its complete root output across precision attempts.
The owner's root driver still constructs exact algebraic roots; this is not
a claim that root solving has no exactification cost.
The existing bounded isolation API retains its
128-level default.
The direct proposal can also fail at its bounded bracketing, pivot or gap
searches; no unchecked interval is accepted.

The tactic uses `produceWithin` with `rcf.algebraic.directDepth` (default 256)
and `rcf.algebraic.maxDoublings` (default 10). The latter bounds fallback
interval attempts at precisions 1, 2, 4, …; a zero limit disables fallback.
This frontend calls the existing fixed-field root driver directly and retains
its selected coordinates, avoiding a redundant common-field reconstruction.
Exhaustion reports `rcf: algebraic interval refinement budget exhausted` and
is terminal. Rejected construction/replay has a different terminal diagnostic.
The complete library producer retains raw cores and its progress/decision laws
are unaffected by the frontend budget or the tactic's monic default. Increasing
the limits permits further refinement;
it does not bypass kernel replay. Lean cancellation is checked before and
after native production. Individual native root computations run until they
return and do not check Lean's cancellation token or elaboration heartbeats.



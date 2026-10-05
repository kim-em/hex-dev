# OrderedFn computational declaration review

Scope: the five production computational modules at
`79b991882a486a8c8d05fd26aaf1656358834b7e`. This is the computational part of
the declaration review, not a Phase-6 completion claim. The companion review and
performance findings remain separate requirements.

Each row identifies the declaration's intended public use and its proof/API
boundary. Automatically generated structure eliminators, projections, equation
lemmas and instances are covered by the corresponding declaration; they are
not additional handwritten algorithms.

## Search

| Declaration | API and proof assessment |
| --- | --- |
| `Next` | The successor relation advances only after a failed trial. Its argument order agrees with accessibility recursion. No monotonicity premise is encoded. |
| `acc_of_success` | A single successful trial terminates search from any earlier start. Strong induction on the distance to that trial is valid even if later trials fail. |
| `next_acc` | Eventual success yields accessibility for every start by choosing `max N n`. The stronger premise is useful for convergence consumers; it does not replace the finite-witness lemma. |
| `accessibleWf` | Private instance supplies the termination elaborator's accessible-subtype relation. Absence of a constant reference in compiled proof bodies does not make this instance unused. |
| `firstSome` | Executes the actual trial repeatedly; the proof argument erases. No classical witness selection, hidden fuel or oracle supplies the runtime result. |
| `firstSome_some` | Public immediate-success equation; consumers need not unfold the recursive definition. |
| `firstSome_none` | Public failed-trial equation with the corresponding accessibility proof. |
| `firstSome_first` | Characterizes the first successful index, not just an arbitrary eventual output. The induction covers both immediate and delayed success. |
| `firstSome_spec` | Weaker, convenient existence characterization obtained from the first-success theorem. Used by sign and approximation soundness/width proofs. |
| `firstSome_eq` | Finite successful output plus agreement of successful values determines the total answer. Termination alone does not imply semantic agreement. |

## Oracle

| Declaration | API and proof assessment |
| --- | --- |
| `Bounds` | Rational endpoints plus an endpoint-order proof. Contains neither accuracy nor semantic membership claims. Proof irrelevance justifies endpoint extensionality. |
| `Bounds.ext` | Two endpoint equalities suffice. The ext attribute enables ordinary extensionality; disabling generated iff avoids an undocumented duplicate. |
| `Bounds.ext_iff` | Bidirectional endpoint characterization used by `inter_eq_some`; explicit statement avoids proof-field unfolding. |
| `Bounds.width` | Exact rational subtraction; `width_nonneg` supplies the semantic nonnegativity fact. |
| `Bounds.singleton` | Includes one rational point exactly. Width normalization and companion containment characterize it. |
| `Bounds.ofDyadic` | Exact dyadic-to-rational conversion; companion containment is the consumer-facing correctness law. |
| `Bounds.neg` | Endpoints reverse under negation. Structural order proof, companion containment and width preservation are separate. |
| `Bounds.add` | Endpoint addition with exact width additivity and companion containment. |
| `Bounds.hull4` | Minimum/maximum of all four values; multiplication and division use all corner products, with no endpoint-sign shortcut. |
| `Bounds.mul` | All four corner products are retained; companion `mul_bounds` and containment law handle intervals crossing zero. |
| `Bounds.inter` | Returns the ordered overlap or none. Success and returned endpoints are publicly characterized. |
| `Bounds.inter_isSome` | Exact Boolean success condition, registered for simp. |
| `Bounds.inter_eq_some` | Both directions are valid, including the disjoint case via the proposed returned bound's structural order. |
| `Bounds.separated` | Strict zero separation; a zero-containing interval cannot pass. |
| `Bounds.div?` | Separation guards both denominator endpoints. Four-corner division yields enclosure; rejection is distinct from total field division by zero. |
| `Bounds.sign?` | Gives only nonzero signs from strict separation. Failure means insufficient information, not algebraic zero. |
| `Bounds.exactSign?` | Additionally accepts the exact zero singleton. It does not accept a wider interval containing zero. |
| `Bounds.width_nonneg` | Follows from structural order without provider assumptions. |
| `Bounds.width_singleton` | Useful simp normalization for exact coefficients and formal-zero approximation. |
| `Bounds.width_neg` | Useful exported simp normalization; no compiled named reference is required for its elaborator/consumer use. |
| `Bounds.width_add` | Useful exported simp normalization for composed error bounds. |
| `Approximation` | Executable coefficient and constant providers only. No false automatic correctness or shrinking assumption. |
| `Approximation.ofConstant` | Exact rational coefficients leave the caller responsible for the supplied constant. |
| `ApproximationWidth` | Width bounds only for strictly positive requests. Containment remains a companion hypothesis. |
| `ApproximationWidth.ofConstant` | Reduces width obligations to the constant provider without assuming containment. |

## Real

| Declaration | API and proof assessment |
| --- | --- |
| `precision` | Positive geometric widths; convergence/progress characterize the refinement schedule. |
| `enclose` | Actual dense-array Horner fold refines every coefficient and the argument at the same width. Companion soundness and convergence track that fold. |
| `attempt` | Canonical zero returns immediately; other fractions require separated numerator and denominator. Progress and semantic correctness remain explicit. |
| `sign` | Executes accessibility-founded search. Public zero and companion sign specifications avoid requiring consumers to unfold recursion. |
| `approxAttempt` | Canonical zero accepts nonnegative requested width; other results require separated denominator and the actual returned width bound. |
| `requestWidth` | Nonpositive requests normalize to one; no impossible zero-width convergence requirement is introduced. |
| `requestWidth_of_pos` | Public simp characterization preserves positive caller requests. |
| `requestWidth_of_nonpos` | Public simp characterization exposes the coarse fallback. |
| `requestWidth_pos` | Supplies the positivity needed by registered approximation progress. |
| `approx` | Runs the same search at normalized width; containment is not inferred from width alone. |
| `finiteAttempt` | Checks stored denominator before allowing an exact singleton-zero numerator. Applicable without relative transcendence, unlike the total extension's hypotheses. |
| `sign?` / `sign?.go` | Fuel counts consecutive trials from zero. The internal recursion is executed and cannot be deleted as a proof helper. Finite exhaustion is an optional diagnostic result. |
| `attempt_zero` | Provider-independent formal-zero equation. |
| `sign_zero` | Applies the immediate-success search law; no new search implementation. |
| `approxAttempt_width` | Covers both zero and nonzero branches, including rejection and successful quotient output. |
| `approx_width_le` | Characterizes the actual searched result's normalized width via a successful trial. |
| `approx_width` | Specializes the normalized bound for positive caller requests. |

## Extension

| Declaration | API and proof assessment |
| --- | --- |
| `Registration` | Fixes the exact executable providers and erased progress proofs for all field queries. It supplies no field-order or semantic correctness claim by itself. |
| `Extension` | Wraps one canonical rational function at a fixed registration; its value field is the computational representation. |
| `ext` / `ext_iff` | Equality is equality of the stored fraction; registration proof fields are not compared. Useful public extensionality. |
| decidable equality | Derived from the stored canonical fraction; no real equality oracle. |
| native field instance | Transfers existing canonical-fraction operations and laws. Companion `coreField_eq` checks equality with the Mathlib field dictionary rather than introducing different runtime arithmetic. |
| `C` / `X` | Coefficient and indeterminate constructors of this fixed registration. |
| `val_C` / `val_X` | Exported simp storage laws avoid constructor unfolding in consumers. |
| `sign` | Executes this registration's actual total search; semantic assumptions belong to `Valid`/`OrderValid`. |
| `approx` | Executes the registered approximation search at normalized width. |
| `compare` | Uses the sign of the difference. Companion comparison correspondence proves all three outcomes. |
| `LE` / `LT` and decision instances | Defined by integer sign; ordering laws are deliberately supplied only by the proved companion hypotheses. |
| `approx_width` | Width guarantee follows from the registered search independently of semantic containment. |
| `transport` | Rewraps the identical fraction with another provider registration. This is representation transport, not an automatic same-subject or order-preservation proof. |
| `transport_val` | Public representation characterization; semantic transport laws require the companion's same-subject hypotheses. |
| `approximation` | Reuses actual extension approximation for next-level coefficients, plus a caller constant provider. |
| `approximation_width` | The next-level width obligations reduce to existing approximation width and the new constant's bound. No missing semantic hypothesis is synthesized. |

## Infinitesimal

| Declaration | API and proof assessment |
| --- | --- |
| `orderSign` | Computational trichotomy procedure under minimal decidable comparison assumptions. Correctness relative to a linear order is separate. |
| `orderSign_range` | Range is minus one, zero or one even with the minimal comparison hypotheses; no hidden order-law assumption. |
| `lowestIndex` | Scans the actual dense coefficient array for the first nonzero entry; zero uses the array's sentinel behavior. Companion trailing-degree theorem handles zero separately. |
| `lowestCoeff` | Reads the scanned coefficient. Zero behavior is covered by the trailing-coefficient correspondence. |
| `sign` | Multiplies numerator and denominator lowest-coefficient signs, with the canonical zero branch. Denominator sign must not be omitted. |
| `sign_range` | Assumes a three-valued base sign and proves the same range for fractions; it does not claim order correctness from range alone. |
| `compare` | Compares via sign of the canonical difference. Companion laws connect it to the Laurent interpretation. |
| scoped `instLE` / `instLT` / `instDecidableLE` / `instDecidableLT` | Explicit scoped relations avoid a global unproved ordered-field instance in the computational library. |

The compiled declaration audit contains 545 constants including generated
proofs, projections, equations and instances. Their axiom union is exactly
`propext`, `Classical.choice`, `Quot.sound`. A zero reference count is not a
safe deletion criterion: elaborator instance/ext/simp registration and anonymous
Verso examples are not fully represented in named proof-body references.
No alternate unused handwritten computational algorithm was identified by this
source review. Public characterizing lemmas above are intentional API; the
companion review assesses its exported laws on the same basis.

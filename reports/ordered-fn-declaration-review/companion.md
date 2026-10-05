# OrderedFn companion declaration review

Scope: eight production companion modules at
`79b991882a486a8c8d05fd26aaf1656358834b7e`. Each handwritten nontrivial
semantic declaration is assessed below. This complements the computational
review; it does not discharge the outstanding performance finding or attest
Phase 6. All semantic constructions stay in the Mathlib companion.

## Oracle

| Declaration | API and proof assessment |
| --- | --- |
| `sgn` | Integer image of Mathlib sign; semantic, noncomputable, and excluded from the runtime library. |
| `cast_sign_neg` | Generic linear-order characterization with only zero and order assumptions. Shared by real and infinitesimal order proofs. |
| `cast_sign_nonpos` | Nonstrict companion characterization; covers zero explicitly. |
| `sgn_div` | Total division, including zero, respects sign multiplication. Does not itself prove the denominator is nonzero. |
| `Contains` | Membership in the actual rational-endpoint interval after casting to reals. Does not include a width hypothesis. |
| `ApproximationCorrect` | Binds the exact coefficient provider, constant provider, embedding and real subject at every positive request. |
| `ApproximationCorrect.ofConstant` | Exact rational coefficients reduce containment to the caller constant. |
| `Contains.singleton` | Exact rational containment, appropriate simp fact. |
| `Contains.ofDyadic` | Exact conversion containment; public dyadic input API. |
| `Contains.neg` | Both inequalities reverse; no sign case assumption. |
| `Contains.add` | Composes containment by endpoint addition. |
| `mul_bounds` | Private four-corner proof handles both signs of a factor. Used by multiplication and division; no duplicate executable arithmetic. |
| `Contains.mul` | Connects the actual four-product hull to multiplication of the subjects. |
| `Contains.inter_isSome` | A common subject implies nonempty overlap by maximum/minimum inequalities. Useful producer-success law. |
| `Contains.inter` | Arbitrary successful overlap retains common subjects via the public endpoint characterization. |
| `Contains.ne_zero` | Strict separation excludes zero; mere containment is insufficient. |
| `Contains.div` | Returns both quotient containment and denominator nonvanishing. The negative and positive denominator branches use the correct inverse inequalities. |
| `Contains.sign` | Successful separated sign certifies both the sign and nonzero subject. |
| `Contains.exactSign` | Exact zero requires both endpoints zero; other results reuse separated-sign soundness. |

## Evaluation

| Declaration | API and proof assessment |
| --- | --- |
| `RelativeTranscendence` | Quantifies over the entire coefficient field and the specified embedding, not only rational coefficients. |
| `RelativeTranscendence.ne_image` | Uses `X-C c` to exclude any already-present coefficient. |
| `RelativeTranscendence.preserves_nonzero` | Supplies the localization denominator premise from relative transcendence. |
| `evalHom` | Field embedding composed with the canonical-fraction equivalence; ordinary Lean-checked nonzero evidence backs localization. |
| `evalHom_apply` | Evaluates the actual stored numerator and denominator rather than an alternate presentation. |
| `evalHom_injective` | Public field-embedding injectivity, available without unfolding the composition. |
| `eval_den_ne_zero` | Canonical denominator is a nonzero polynomial and cannot vanish under the given hypothesis. |
| `evalHom_eq_ratFunc` | Restriction to `Type` is documented and follows Mathlib's same-universe evaluator; the underlying embedding remains universe-polymorphic. |
| `evalHom_C` | Simp characterization on predecessor coefficients. |
| `evalHom_X` | Simp characterization on the new subject. |

## Real

| Declaration | API and proof assessment |
| --- | --- |
| `eval` | Stored-fraction total real division, explicitly not a field embedding at poles. |
| `precision_pos` | Supplies positivity for every executed refinement request. |
| `enclose_sound` | Induction tracks the actual array Horner recurrence and all coefficient requests. |
| `attempt_sound` | Arbitrary successful trial is sound from containment alone; formal zero and separated nonzero branches are distinct. |
| `attempt_unique` | Successful trials agree via the same canonical evaluation, independently of termination evidence. |
| `sign_sound` | Applies the search specification to an actual successful trial. Does not infer semantics from accessibility alone. |
| `sign_of_attempt` | Finite supplied success identifies the total result through the generic agreement law. Avoids kernel evaluation of unbounded search. |
| `approxAttempt_contains` | Covers formal zero and successful guarded quotient; width is handled by a separate computational lemma. |
| `approx_contains` | Transfers actual successful-trial containment to the searched output, including normalized nonpositive requests. |
| `finiteAttempt_sound` | Also proves nonvanishing of the stored denominator. Original expression divisors remain the consuming frontend's responsibility. |
| `sign?_sound` | Induction over the executed finite recursion; preserves denominator regularity and sign for any accepted finite output. |

## Convergence

| Declaration | API and proof assessment |
| --- | --- |
| `Contains.endpoint_error` | Both endpoint errors are at most interval width, using actual containment and endpoint order. |
| `Contains.product_error` | Retains the simultaneous-error cross term. Nonnegativity of error bounds is derived from the stated absolute-value bounds. |
| `Contains.mul_width_le` | Applies the product estimate to all four corners and bounds the actual hull width. |
| `Contains.add_converges` | Exact width addition transports convergence. No containment hypothesis is unnecessarily imposed. |
| `Contains.mul_converges` | Squeezes the actual product width using containment and both shrinking widths. |
| `Contains.endpoints_tendsto` | Containment plus shrinking width forces both endpoints to the same subject. |
| `Contains.quotient_converges` | All four quotient corners converge when the limiting denominator is nonzero. This hull limit does not claim division succeeds at every early precision. |
| `Contains.sign_eventually` | Nonzero subject plus narrowing gives eventual strict separation; handles both signs. |
| `precision_tendsto` | Geometric requests tend to zero. |
| `width_tendsto` | Positive-request width bounds squeeze the actual provider requests; nonpositive requests are not assumed. |
| `horner_converges` | List induction corresponds exactly to the array fold and simultaneously refines coefficients and argument. It does not freeze coefficients as exact. |

## Progress

| Declaration | API and proof assessment |
| --- | --- |
| `enclose_sign_eventually` | Combines containment, actual Horner convergence and relative-transcendence nonvanishing. |
| `attempt_progress` | Both numerator and denominator eventually separate; canonical zero succeeds immediately. |
| `approx_progress` | Denominator eventually separates and all four quotient corners narrow to every positive requested width. |
| `approx_acc` | Uses normalized strictly positive width, covering coarse requests too. |
| `sign_acc` | Supplies accessibility for the same executable attempt at any start. |
| `sign_eq` | Agrees with the injective embedding via existing successful-trial soundness; no second computational sign. |
| `sign_eq_zero_iff` | Injectivity supplies algebraic zero equivalence; range or convergence alone could not prove this. |

## Extension

| Declaration | API and proof assessment |
| --- | --- |
| `Valid` | Existential semantic witnesses stay in Prop; binds containment, width and transcendence for the exact provider. |
| `registration` | Eliminates those witnesses only into progress proofs. Executable source is still the supplied provider. |
| `registration_source` | Public simp identity exposing that source without registration unfolding. |
| `equiv` | Wrapper/canonical-fraction equivalence, not an embedding into reals. |
| `fieldModel` | Transports existing field laws; adjusts subtraction to the actual native wrapper operation. |
| `field` | Retains native dictionary arithmetic, casts, powers and scalar operations while importing semantic field laws. |
| `coreField_eq` | Verifies the companion induces precisely the computational field dictionary. Its definitional proof is appropriate for implementation identity, rather than an omitted user-facing mathematical theorem. |
| `valHom` | Homomorphism forgets registration and uses the actual fraction operations. |
| `evalHom` | Composes the proved canonical evaluation with the wrapper homomorphism. |
| `evalHom_apply` | Public stored-fraction characterization. |
| `sign_eq` | Correctness refers to this registration's provider and subject. |
| `evalHom_C` | Simp law for the specified predecessor embedding. |
| `evalHom_X` | Simp law for the specified new real subject. |
| `sign_neg` | Semantic sign negation obtained from the field homomorphism; no executable replacement. |
| `sign_mul` | Semantic sign multiplication includes zero. |
| `sign_eq_zero_iff` | Formal zero iff native total sign is zero, under containment and relative transcendence. |
| `sign_of_attempt` | Finite evidence identifies the existing total sign using containment; registration already contains termination. |
| `compare_eq` | Trichotomy handles all three comparison outcomes. |
| `eval_lt` | Characterizes native strict order through evaluation and sign of a difference. |
| `eval_le` | Nonstrict counterpart includes equality. |
| `sign_pos_iff` | Actual registered positivity corresponds to sign one. |
| `sign_neg_iff` | Actual registered negativity corresponds to sign minus one. |
| `C_lt` | Explicit strict monotonicity of the predecessor embedding is necessary to preserve an already-chosen predecessor order. |
| `OrderValid` | Containment and relative transcendence suffice for order once searches are registered. Width was needed earlier for constructing registration. |
| `linearOrder` | Data consists of existing core comparisons and decisions; semantic witnesses occur only in proof fields. Injectivity establishes antisymmetry. |
| `eval_strictMono` | States monotonicity for the particular proved native linear order. |
| `strictOrderedRing` | Uses injective transfer with both order correspondences and field homomorphism laws. |
| `orderedRing` | Supplies the core grind dictionary's laws for the same native order; complements the Mathlib ordered-ring class. |
| `OrderValid.strictOrderedRing` | Existential-witness wrapper useful for ordinary callers without exposing a chosen evaluation witness. |
| `OrderValid.orderedRing` | Corresponding core dictionary wrapper; no new computational instance. |
| `approx_contains` | Semantic containment separately from native width guarantees. |
| `eval_transport` | Literal stored-fraction identity preserves evaluation for the same embedding/subject. |
| `transport_lt` | Both providers must be checked against the same embedding and subject; arbitrary re-registration cannot imply preservation. |
| `sign_transport` | Same-subject two-provider correctness preserves the sign. |
| `approximation_correct` | Supplies next-level coefficient containment from this same extension's evaluation and approximation. The new constant remains an explicit caller premise. |
| `Valid.orderValid` | Reuses registration's semantic witnesses; does not incorrectly claim the predecessor embedding preserves a pre-existing order. |

## Hahn

| Declaration | API and proof assessment |
| --- | --- |
| `mapHom` | Coefficient field homomorphism acts on the actual Hahn series, wrapped in lexicographic order. |
| `map_support` | Field homomorphism injectivity preserves zero/nonzero coefficients and hence the support, including zero series. |
| `map_orderTop` | Support-order preservation includes the zero/top case. |
| `map_leadingCoeff` | Handles zero separately and transports the nonzero leading coefficient at the preserved exponent. |
| `map_lt` | Explicit strict monotonicity of coefficients preserves and reflects lexicographic comparison. |
| `map_le` | Uses strict comparison and homomorphism injectivity to include equality. |
| `map_C` | Constant embedding commutes with coefficient mapping without unnecessary order hypotheses. |

## Infinitesimal

| Declaration | API and proof assessment |
| --- | --- |
| `lowestIndex_eq` | Exact dense-array scan agrees with trailing degree; zero/sentinel and nonzero-coefficient cases are handled explicitly. |
| `lowestCoeff_eq` | Characterizes the scanned coefficient mathematically. |
| `embed` | Canonical rational-function equivalence composed with the Laurent/Hahn embedding; interpretation only, not runtime computation. |
| `embed_injective` | Public injectivity of the actual interpretation. |
| `embed_C` | Simp law: coefficient at exponent zero. |
| `embed_X` | Simp law: new indeterminate at exponent one. |
| `poly_coeff` | Private coefficient characterization supports negative-exponent vanishing and nonnegative exponents. |
| `poly_order` | Requires nonzero polynomial for finite lowest exponent. |
| `poly_leadingCoeff` | Includes the zero polynomial and identifies the trailing coefficient. |
| `embed_eq` | Public actual numerator/denominator characterization. |
| `embed_fraction` | Any representation with explicitly nonzero original denominator has the same interpretation. |
| `poly_ne_zero` | Private injectivity bridge used in division/order proofs. |
| `embed_leadingCoeff` | Fraction leading coefficient is the quotient of trailing coefficients; stored denominator nonzero justifies cancellation. |
| `embed_order` | Nonzero fraction order is the difference of numerator/denominator lowest indices. Explicit nonzero premise is essential. |
| `orderSign_eq` | Executable predecessor sign agrees with semantic trichotomy; unnecessary strict ordered-ring assumptions are omitted. |
| `sign_poly` | Private leading-coefficient sign correspondence, reused by fraction and normalization proofs. |
| `sign_eq` | Both numerator and denominator signs contribute; a correct supplied base sign yields the Hahn sign. |
| `sign_orderSign` | Convenient specialization to the native ordered predecessor sign. |
| `lowestIndex_map` | Private coefficient injection preserves precisely the zeros tested by the actual scan. |
| `lowestCoeff_map` | Private transport of the selected coefficient, relying on the preserved index. |
| `mapHom_sign` | Strictly monotone coefficient embedding preserves the native infinitesimal sign. |
| `mapHom_sign_of` | Handles an arbitrary supplied base sign with pointwise agreement in the target; does not require an independently chosen source order. |
| `sign_fraction` | Arbitrary fraction presentation's sign remains valid with the original denominator's nonzero premise. |
| `sign_normalize` | Exposes normalization/cancellation invariance through the actual representation theorem. |
| `sign_neg` | Semantic embedding proves native sign negation. |
| `sign_mul` | Semantic embedding proves native sign multiplication. |
| `sign_eq_zero_iff` | Injectivity identifies formal zero. |
| `compare_eq` | All native comparison outcomes agree with the Hahn order. |
| `embed_lt` | Characterizes the actual scoped strict order. |
| `embed_le` | Nonstrict order characterization. |
| `linearOrder` | Injective transfer retains the executable scoped comparison decisions. |
| `strictOrderedRing` | Transfers ordered field laws for that same native order. |
| `orderedRing` | Corresponding grind ordered-ring dictionary, separate from the Mathlib class. |
| `sign_of_neg` | Convenient sign minus one characterization for negative fractions. |
| `sign_of_pos` | Convenient sign one characterization for positive fractions. |
| `C_lt` | Predecessor constants retain their order. |
| `X_pos` | New exponent-one monomial is positive. |
| `X_lt_C` | New infinitesimal is below every positive predecessor coefficient. |
| `C_lt_inv_X` | Its reciprocal exceeds every predecessor coefficient, including negative coefficients. |
| `intCast_lt_inv_X` | Specializes the coefficient result to integer casts using the actual constant homomorphism. |
| `X_lt_pow` | Second infinitesimal is below every natural power of the first, including power zero. |
| `embed_strictMono` | Public strict monotonicity used in coefficient-level Hahn transport. |
| `mapHom_strictMono` | Preserves the native rational-function order under an ordered coefficient-field embedding. |
| `towerEmbed` | Two-level interpretation composes coefficient mapping and the Laurent interpretation. Does not assert real closedness or an ordinary-real realization of infinitesimals. |
| `towerEmbed_lt` | Preserves and reflects the two-level order using both existing correspondence laws. |
| `towerEmbed_C` | Public constant characterization at the second level. |

## Reuse and outstanding acceptance

No unused alternate handwritten semantic algorithm was identified. Private
helpers have actual proof or elaboration consumers. Zero compiled named-reference
counts for exported laws do not by themselves justify removing public
normalization, order, embedding or transport APIs; those laws characterize the
library's promised behavior, and some are used through simp or anonymous examples.
The declaration-use artifact records these limits explicitly rather than treating
reference counts as a linter-based proof of API quality.

The compiled audit's 545 production constants have only `propext`,
`Classical.choice`, `Quot.sound` as axioms. The prior full builds and lint target
provide diagnostics; the substantive source assessments above provide a different
part of Phase 6. Final performance acceptance and independent review of the
combined declaration review remain outstanding. No phase counters are changed
by this review.

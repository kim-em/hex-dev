# Automation, imports and naming

This supplements the individual source assessments. It records a remaining
import-minimality finding rather than claiming all Phase-6 quality gates passed.

| Module | Automation and API assessment |
| --- | --- |
| Search | Public search equations remain explicit: uncontrolled rewriting of recursion or accessibility evidence is unsuitable for simp/grind. `firstSome_spec` and `firstSome_eq` give consumers finite proof routes. |
| Oracle | Endpoint extensionality uses ext; intersection success and exact width identities use simp. These terminating normalizations expose behavior without recursive unfolding. |
| Real | Positive/nonpositive width normalization and formal-zero laws use simp. General search soundness/progress require the exact provider hypotheses and remain explicit. |
| Extension (core) | Extensionality and constructor/transport storage equations support ordinary normalization. The native field dictionary is separate from conditional order laws. |
| Infinitesimal (core) | Canonical-zero sign is simp; scan and range statements remain explicit. Scoped relations avoid an unproved global order. |
| Oracle (companion) | Containment transfer and divisor/sign regularity have explicit subjects and successful-output premises. Automatic global rewriting should not invent those premises. |
| Evaluation | Constructor evaluations use simp. Relative transcendence and arbitrary embeddings remain explicit hypotheses; no automatic choice of semantic subject is imposed. |
| Real (companion) | Successful-trial soundness and total-search correctness remain explicit to avoid kernel reduction of unbounded computation. |
| Convergence | Analytic estimates and eventual statements use their stated containment/width hypotheses. Making all of them global automation rules would not replace those proof obligations. The existing width-add characterization can be reused more directly in `add_converges`. |
| Progress | Accessibility follows the same executed trials. Eventual success is applied explicitly rather than installed as a generic search/automation rule. |
| Extension (companion) | Constructor evaluations normalize with simp. Order instances need an explicit `OrderValid`; same-subject transport requires both providers. Unconditional simp/grind rules for these existential subjects would be misleading. |
| Hahn | Constant mapping uses simp; support, leading coefficient and order-reflection laws retain their embedding/monotonicity hypotheses. |
| Infinitesimal (companion) | Constant/indeterminate embedding equations use simp; arbitrary fraction, normalization and successive-level order results remain explicit. Scoped instances select the intended order. |

The source has no `@[grind]` declarations. This is not itself a quality failure:
existing simp normalization, explicit characterizations and conditional transfer
lemmas support the current examples. New grind annotations need useful downstream
applications; indiscriminately installing conditional evaluation/progress laws
would add unresolved witnesses or recursive proof work.

The public names use short forms within their semantic namespaces (`sign_eq`,
`eval_lt`, `map_support`, `X_lt_C`). Long generated elaborator names are not
handwritten API. Local `open` and instance directives remain scoped; computational
modules use Init/native Hex requirements, and semantic interpretation stays in
the Mathlib companion. Production umbrellas omit the API lint target.

**Import finding:** `HexOrderedFnMathlib.Infinitesimal` imports semantic
`HexOrderedFnMathlib.Oracle` for the two generic integer-sign/order bridges.
That also brings real interval containment into the infinitesimal interpretation.
A small shared sign module could retain the existing public names while giving
both consumers lighter imports. This is a remaining Phase-6 polishing decision,
not a change applied by the retained-source assessment.

The zero-reference table records why public characterizing laws remain exported;
intentional API is distinct from a discovered production caller. Final acceptance
must consider those dispositions and the import finding along with the unresolved
computational regression evidence. No phase counter advances here.

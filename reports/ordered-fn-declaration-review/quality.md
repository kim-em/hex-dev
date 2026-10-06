# Automation, imports and naming

This supplements the individual source assessments. It records the current
import structure without claiming all Phase-6 quality gates passed.

| Module | Automation and API assessment |
| --- | --- |
| Search | Public search equations remain explicit: uncontrolled rewriting of recursion or accessibility evidence is unsuitable for simp/grind. `firstSome_spec` and `firstSome_eq` give consumers finite proof routes. |
| Oracle | Endpoint extensionality uses ext; intersection success and exact width identities use simp. These terminating normalizations expose behavior without recursive unfolding. |
| Real | Positive/nonpositive width normalization and formal-zero laws use simp. General search soundness/progress require the exact provider hypotheses and remain explicit. |
| Extension (core) | Extensionality and constructor/transport storage equations support ordinary normalization. The native field dictionary is separate from conditional order laws. |
| Infinitesimal (core) | Canonical-zero sign is simp; scan and range statements remain explicit. Scoped relations avoid an unproved global order. |
| Sign (companion) | The shared integer-sign/order equivalences retain their generic zero and linear-order hypotheses. Both interpretations use them explicitly without choosing a semantic subject. |
| Oracle (companion) | Containment transfer and divisor/sign regularity have explicit subjects and successful-output premises. Automatic global rewriting should not invent those premises. |
| Evaluation | Constructor evaluations use simp. Relative transcendence and arbitrary embeddings remain explicit hypotheses; no automatic choice of semantic subject is imposed. |
| Real (companion) | Successful-trial soundness and total-search correctness remain explicit to avoid kernel reduction of unbounded computation. |
| Convergence | Analytic estimates and eventual statements use their stated containment/width hypotheses. Making all of them global automation rules would not replace those proof obligations. `add_converges` uses the existing width-add characterization without unfolding endpoints. |
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

The generic `Oracle.cast_sign_neg` and `Oracle.cast_sign_nonpos` proofs live in
`HexOrderedFnMathlib.Sign`, which imports only Mathlib's generic sign layer.
`Oracle` and `Infinitesimal` share that module; the infinitesimal interpretation
does not import real interval containment. Existing names and umbrella access are
preserved. This is an internal companion module split, with no package or
computational dependency change.

The declaration inventory and individual tables retain their pinned source
snapshot. `Sign` moves the two already-assessed generic proofs unchanged; their
public statements, automation choices and semantic hypotheses are identical.

The zero-reference table records why public characterizing laws remain exported;
intentional API is distinct from a discovered production caller. Final acceptance
must consider those dispositions along with the unresolved
computational regression evidence. No phase counter advances here.

# Independent review disposition

[Complete Fable opinion](results/fable-review.txt). The opinion reviewed the
initial experiment and plan; its source line numbers refer to that snapshot.
Fable had read-only access and could not run builds. The local build and
oracle checks were run again after the corrections below.

Fable accepts the central representation and conditional-transfer argument.
Its recommendation is to proceed with the architecture correction and the
selected-root proof work, while withholding a general batching recommendation.

Validated findings and resulting changes:

1. Raw degree growth: the report now explains the unbounded growth, the
   monic-clean remainder option, and the storage-policy decision before
   concrete scalar proofs. Retaining the computed remainder need not perform
   another division, but requires a constructor/invariant change; it is not
   automatically appropriate for non-monic or non-clean defining polynomials.
2. Performance scope: the plan now requires division/gcd, cheaper zero tests,
   and a nested workload before choosing a production policy. No additional
   performance results are claimed, and multiplication data are retained unchanged.
3. Cancellation: replaced the literal-cancellation fixture by `[X,1]*[−2,X]`,
   whose inner raw coefficient is the nonzero polynomial `X²−2`. The check
   confirms root selection is needed and both products pack that coefficient to zero.
4. Validity: the next proof statements explicitly require `valid d = true`,
   and the proposed production constructor must enforce executable validation.
5. Sign and Tarski: corrected the plan to say Tarski queries are specified but
   unimplemented; added general rational-algebraic sign to the initial slice.
6. Instrumentation: output agreement is described only as a check of the
   shadow product. Counts are justified by inspecting the actual convolution,
   not by claiming its output equality proves call-count correspondence.
7. Oracle: the discarded factor must equal FLINT's exact monic gcd. Sign is
   now checked by exact rational enclosure bisection, independent of Lean's
   squared-magnitude formula. Missing/truncated records fail verification.
8. Splitting/context identity: explicitly recorded the local-inverse versus
   persistent-refinement distinction and the unresolved dependent-handle design.
9. Presentation: renamed the timing column to identify whole-product time.

The proof plan is split into zero/arithmetic/sign, inversion/transport, and
transfer instantiation. The available real-root theorem is correctly named
`HexRealRootsMathlib.sturmCount_eq_card_roots`; it supports the rational slice
in ℝ, not arbitrary non-Archimedean semantics.

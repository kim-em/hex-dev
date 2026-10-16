# Acceptance at original algebraic sources

`AlgebraicCells.accepts` states two concrete facts: the existing algebraic
producer returns a packet, and the complete packet checker returns accepted
true. Its source tuple, coefficient indices, original-divisor indices, shared
matrix and quantifier are fixed arguments. This is mathematical acceptance
of the actual total producer and checker, not a new certificate format.

`accepts_iff` proves that acceptance is equivalent to every original real
divisor being nonzero and the shared sentence holding at its original fixed
algebraic values. It composes the existing `build_complete`, `build_sound`
and `build_domains` laws. It assumes no successful child calculation, supplied
root table or sector function. `accepts_tuple` separates ordered coefficient
and divisor coordinates. `accepts_source` transports that result through
checked source identities and the shared frontend's exact original-goal
equivalence. A semantically trivial source does not remove its divisor
conjuncts: an empty domain with an original zero divisor remains invalid.

`AlgebraicPreparation.Inputs.acceptanceIff` constructs this proof from the
retained kernel algebraic expressions. It checks each expression and its exact
`toReal` equality, constructs the ordered finite functions, reads the quantifier
and matrix from the checked source formula, and checks the source equivalence.
It does not use the separately evaluated runtime proposals or the editable
runtime formula/quantifier fields as proof evidence. The result's right side
is exactly the original real target together with all original nonzero guards.

The helper continues the preparation's aggregate proof budget. It charges
proofs before checking them, returns the updated aggregate usage for later
stages, preserves caller metavariables on success and
restores the complete state after exhaustion or failure. Successful private
proof auxiliaries remain available for the returned ordinary proof.

Source-specific consumers cover rational zero-coordinate input, an
irrational positive source, a false source, both original quotient/inverse
occurrences, a cancelled semantically zero divisor, reversed intervals with
and without a zero divisor, and a local real alias with its equality hypothesis.
They compare the exact original target and ordered source-expression tuple.
Editing runtime proposals, the runtime matrix and the runtime quantifier must
leave the returned theorem type unchanged. Continued usage must increase;
one node below the measured cumulative proof limit refuses, and the exact
limit succeeds. Heartbeat, recursion and interruption entry checks remain
terminal, with state/declaration rollback. Those resource tests do not force
a failure halfway through kernel checking. Edited identity and exhausted-budget
cases separately exercise rollback after auxiliary proof work.

A fresh importing module checks the actual theorem bodies and their transitive
axiom closure, requiring the real producer completeness and domain laws. An
ordinary-public-import consumer unfolds `accepts` and constructs an accepted
empty-input packet from `build_complete`, without an acceptance premise.
Its body is included in the fresh audit. The only axioms are `propext`,
`Classical.choice` and `Quot.sound`.

The expanded consumer selection at `b1f0c80539` has 11,036 jobs, takes
3m14.332s and peaks at 4 GiB with no swap. Its manual/dependency selection
passes 11,681 jobs in 6m19.764s at 13.1 GiB; the actual revised chapter rebuilds
in 5.9s. The final identity-retention correction puts every retained identity
inside the same cumulative preparation budget and preserves a caller's lowered
recursion limit through the options wrapper. Its combined consumer, fresh
body-audit, public-import and manual selection passes 11,681 jobs in 2m44.798s
at 3.6 GiB. The chapter takes 5.2s. These observations include incremental
dependency work and different test scopes; they are not matched performance
comparisons or isolated replay/scaling measurements.

All own local builds remain serial under 32 GiB aggregate memory, no swap and
two Lean threads. Successful calls retain private proof auxiliaries for the
returned evidence. Repeated retention and guard-only algebraic inputs contribute
to the remaining depth, memory and expanded-work measurements.

This does not prove a computed proposal equal to a frozen literal or reconstruct
provider/predecessor histories. It does not install a generic tactic handler,
authenticate a compiled complete packet, establish strict rejection of missing
intermediate records, or close #10358. General literal-source quotation,
resource-scheduled acceptance, realization and remaining stress/performance
work retain their own obligations. The manual explains the distinction and
runs the meta helper on an original irrational-coefficient statement.

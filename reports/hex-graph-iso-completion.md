# Structured-search completion plan

Complete #10043 by proving the structured engine through the generic recursion,
switching the public search, and deleting the superseded traversal. Preserve
canonicalization, certification, generator completeness, and public orbit
theorems. Line-count reduction is not an acceptance criterion. Future changes
should have clear, local proof obligations.

Keep production on the legacy implementation and PR #10107 in draft until
replacement correctness holds. Retain the direct engine and its proved equality
with the generic recursion. Reuse compiled maximum and cheap-descent proofs.
Do not repeat passed experiments unless a contract change invalidates them.
Do not add performance tuning or compiler-specialization work.

## Feasibility: six additional focused hours

Allow four hours for generation and then two for proof locality. These are
investigation limits, not completion estimates. Exclude unattended builds and
CI; include diagnosis and proof repair. Allowances do not restart with revised
contracts. Stop at unsuccessful checkpoints without borrowing another stage's
allowance, and return control with the exact missing statement.

### Generation: four hours

Use actual node and sweep calls. Parameterize generation by a final containing
trace, with child and suffix inclusion proved at their calls. Do not use the
legacy search's generator list.

| Checkpoint | Work | Passing evidence |
|---|---|---|
| First hour | First-path return and reference contract | Actual guiding child and sibling tail return to their receiver, preserving reference occurrence and uniformity needed by filters |
| Next two hours | Generated orbit coverage | Required images have generated carriers through orbit skips, both filters, and nonlocal returns |
| Final hour | Nonterminal stabilizer step | Actual smaller-child generation and actual sweep image coverage instantiate `Perm.Generated.of_stabilizer` |

Reuse checked cheap matching-reference descent and off-path return bounds.
Derive generated carriers for implicit workspace pairs from the smaller point
stabilizer. Automorphism validity alone is insufficient. Keep reference
occurrence separate from maximum-key coverage.

Pass only with a compiled complete step using smaller-call induction hypotheses
and proved local rules. Construct actual inputs, trace inclusion, and return
consumers. Check terminal and root preconditions. Classify remaining legacy
imports as reusable mathematics or outstanding traversal proofs. A wrapper
assuming image coverage does not pass.

Stop at a failed checkpoint, an invariant that cannot be initialized or
preserved, or circular use of the parent's conclusion at a child. Distinguish
contract defects, mathematical obstructions, and underestimated effort.

### Proof locality: two hours

After generation passes, test a temporary long-prune policy scanning only the
newest 32 stored pairs. This changes pruning strength and possibly traversal,
so helper equality cannot discharge the experiment.

Express filter obligations through live-set and cursor bounds, coverage of
removed children, and generated carriers for removals. Instantiate them for
both the production full scan and bounded scan. Check actual receiving and
resumed-sweep rules for maximum coverage and generation while reusing the
generic recursion and ancestor-return argument.

Compare the legacy proof dependencies for the same change. Do not claim an
exclusive advantage if the legacy change is equally local. Pass when both
variants compile through complete relevant local rules with changes confined
to filter contracts, justifications, and policy wiring. Stop if a new global
invariant, rewritten recursive return argument, or more than two hours is needed.

Exclude the diagnostic implementation from the final PR. Retain the findings
and only contract improvements used by production. Do not claim a measured
speedup or change the production policy from the spike.

## Correctness assembly: eight focused hours

Proceed after both feasibility experiments pass and their evidence is reported.
Finish first-leaf installation and exhausted-cursor maximum rules. Complete
generation and extraction from the engine's actual trace. Derive whole-engine
theorems without legacy recursive correctness assumptions.

Preserve the positive-size hypothesis of key equality. Handle the empty graph
through its separate certificate case and sentinel conventions. Complete
policy-independent reach and adequate-fuel results. Add completed modules to
the ordinary build graph; explicit experimental builds do not suffice for delivery.

Pass when maximum, generation, reach, and termination compile together against
the engine, without superseded traversal proofs in their dependency closure.
Stop if a new global invariant is required or the allowance expires.

## Migration: four focused hours

Re-point `runColoredTraced` and `tracedKey`. Preserve the public statements of
`canonSpecKey_eq_tracedKey`, `certifyCanon?_isSome`, `Ops`, `Aut.complete`, and
orbit characterizations, and the certification and canonical-form interfaces.

Give the engine the `Search` name and retain its nauty correspondence table.
Extract reusable mathematics, then delete the literal recursion,
`Nauty/Correct/`, and superseded invariant material. Do not relocate the old
traversal proof to satisfy deletion. Update manual references, imports, and
release test manifests. Stop on an unresolved mathematical dependency or
expired allowance. Source size alone is not a stopping criterion.

## Validation and delivery

Build with `lake build` after every proof step and fix diagnostics immediately.
Build both libraries, registered tests, `HexManual`, and conformance targets.
Run fixtures, campaign, real nauty oracle, and twin checks. Preserve spike
results for labels, rows, generator discovery order, path codes, orbits,
traversal statistics, and normal root termination.

Check empty input, explicit fuel exhaustion, cheap admission, workspace
overwrite, both short flags, canonical returns with changed and unchanged
orbits, and coset-index returns. Audit dependencies and exclude `sorry`,
`axiom`, and `native_decide` from delivered changes.

Before pushing covered source batches, freeze source and run the required
chungus2 cactus sweep. Commit data, manifest, and figures. Check freshness and
existing performance bounds without relaxing them. Batch moves and deletions.
Rebase onto performance-baseline changes and repeat affected validation.

Update PR #10107 around the completed implementation. Immediately request a
fresh Claude Opus second opinion while CI runs, including generation, proof
locality, and hidden legacy dependencies. Address findings and CI failures.
Monitor each Actions run with one `gh run watch` process and inspect failed
job logs. Resolve conflicts and revalidate affected changes. Mark ready only
after acceptance. Merge with `gh pr merge --squash --auto`, without
`--delete-branch`.

At checkpoints report the established theorem, remaining assumptions, build
result, and uncertainty reduced. Expiration returns control for a decision;
it does not authorize abandoning the branch, reverting #10041, or deleting
the working implementation. If a directive premise is false, explain its
concrete contradiction on the issue rather than weakening the public theorem.

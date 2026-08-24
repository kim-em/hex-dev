# Typed runtime public tactic audit

## Accomplished

- Stacked the repeated-slot scheduler, built-in `RuntimeRule`, and
  `RuntimeTerminal` commits on current `origin/main` in an isolated worktree.
- Resolved the umbrella, SPEC, and Lake target overlap by retaining both the
  runtime-rule and runtime-terminal layers.
- Audited the public tactic from reification through proof installation and
  checked the typed controller/target/replay route against the existing
  experimental proof-emission design.
- Built `RuntimeRule`, `RuntimeTerminal`, and both conformance targets from a
  fresh dependency checkout; all 8,712 transitive jobs passed.

## Current frontier

The forward controller and exact target terminal are sufficient for the
current public arithmetic tactic without a split adapter. The remaining
blocker is proof syntax: `RuntimeTerminal.Checked.replayWithin` returns a
compiled `Proof.Evidence` value, while a tactic must install a `Lean.Expr`.
No supported quotation maps the sealed runtime bundle and package schemas to
a transparent replay expression. The current tactic instead reconstructs an
independent arithmetic theorem expression, which cannot be retained under the
requested load-bearing typed path.

## Next step

Promote the narrow root-only portion of `Experiment.ProofEmitter` and
`Experiment.ProofRegistry`: package-local emitter handles paired exactly with
the runtime proof schema keys, transparent fact/instance/equality/transport
composition over the plain chronology extracted from a sealed checked token,
and a transactional Meta boundary returning an exactly checked Evidence
expression. Then the tactic can eliminate that expression with
`Frontend.closeSources` and use the existing endpoint closures.

## Blockers

- Runtime proof values contain erased proposition proofs and cannot be turned
  into syntax by `ToExpr`.
- `RuntimeProof.Registry` contains executable formats and runtime theorem
  callbacks but no elaborator emitter handles or transparent quotation API.
- General split emission remains out of scope; the public forward route only
  needs a one-node target-terminal tree.

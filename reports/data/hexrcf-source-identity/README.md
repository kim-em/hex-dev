# Selected-source authentication evidence

Run `python3 reports/data/hexrcf-source-identity/verify.py --check-head`.
The optional flag compares the pinned implementation with current sources.
`context.json` binds 106 sources and 198 artifacts to implementation
`a4b44be2efdba00c6b40f7b932db40d1c44beb27`.

For current sources use `python3 reports/data/hexrcf-source-identity/verify_header_repair.py`.
CI caught missing copyright prefixes in two newly tracked conformance files;
the original local checker had excluded untracked files. The repair at
`2475e17ee6ef365a7a317bb12e84ef78ec56125f` changes only those comments.
The repair verifier checks every pinned source and the exact two added prefixes;
the original `--check-head` deliberately detects this source difference.
Failed CI logs are retained under `header-repair/`. The original record keeps
its source pin and is not republished as validation of the later commit.

The record covers independently quoted equation/margin packets, selected-source
authentication, its use in the full original algebraic source proof, exact/below
budgets, wrong-conjugate and wrong-value-law refusal, full caller restoration,
fresh actual-body/axiom audits, 45 affected targets and the complete manual.
All twelve final desktop/narrow captures were actually inspected. Active
resource limits, invocation arguments, constructor checks and failed diagnostic
attempts with available exact inputs are retained.

The original anchor selection, coefficient value laws, fixed parent and seed
facts remain supplied. General history assembly and the full tactic remain
incomplete. Earlier evidence keeps its original pins. See the
[report](../../hexrcf-source-identity.md) for timings, failures and limits.

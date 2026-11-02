# Replay helper type quotation

`RootQuote` preserves data type arguments while rewriting their Boolean
computations. It collects dependencies appearing in closed helper types in
dependency order, retains exposed function definitions as local lets, and
keeps opaque helpers as parameters. Partial applications of demanded
function-valued conditionals retain their subsequent arguments. Every
candidate still receives ordinary-kernel checking at the original target.

The second complete-source experiment failed after 45m55.490s, peak 4.3G
and no swap, when `Replay.table` received a proof referring to an abstract
replay function while requiring the concrete checker. It reached neither
complete acceptance nor original-source finishing. Small public-module
controls reproduce that mismatch in 8.713s and a related typed-array
rewrite failure in 8.673s. The retained logs distinguish these failed
attempts from the final production repair.

## Checked controls

Stored arrays with replay-dependent element types and functions with fixed
replay-dependent proof types both pass. Matching and changed contexts
produce the checked results 1 and 23 respectively. Their charged node
counts are 95,378/8,388 and 81,812/7,272. Both matching cases check exact and
one-node-below limits, wrong-goal proposals and complete caller metavariable
and declaration restoration. These are reader equations, not new real-goal
proofs or assumptions of complete root coverage.

A fresh importing audit checks 96 theorem bodies, three definitions and
99 nonempty kernel traces. It requires the public replay leaf and table
equations, excludes old fixture acceptance proofs, preserves the producer
denylist and checks the full permitted axiom closure. No new axiom or proof
admission is introduced. Existing row, boundary, callback, packet and
recursive audits retain their guards.

All 33 selected targets and the complete manual pass: 14,398 jobs with
unchanged dependencies reused, 12m1.096s and peak 2.8G/no swap. This is the
affected selection, not the entire default build. Existing function-valued
reader controls caught a flattened-application traversal regression; the
final run includes its repair. Failed compatibility runs remain retained.

The prepared packet consumes 3,031,749 nodes including publication. Its
test-only allowance is four million after the previous three-million test
exhausted at 2,998,466 consumed plus 1,535 requested. Library defaults are
unchanged. Exact/below controls consume 3,029,330 nodes. The independent
wrong-sign test now runs in its own command under the same twelve-million
heartbeat limit: its predecessor command had completed the three budget
runs before exhausting the cumulative heartbeat allowance. Wrong-sign and
all three malformed-input checks retain full caller restoration and pass.
Both failed resource runs are retained.

The complete manual and HTML render pass. All ten changed desktop/narrow
captures were actually inspected and have zero local overflow; existing
section/page overflow is recorded separately. The manual records observed
shared, recursive and packet costs and scoped elaborator limits. All seven
metadata checks pass. The [source-bound record](data/hexrcf-replay-helpers/README.md)
pins 77 artifacts and 95 sources; earlier evidence keeps its original pins.

## Scope and limits

The subsequent full production-source attempt is outside this immutable
record until it terminates. Focused repairs and an accepted prepared packet
do not establish complete source acceptance, algebraic completeness or a
practical general tactic. No matched speedup, scaling or physical-sharing
claim follows from these diagnostic runs or charged node counts.

Generic source/provider/predecessor and frozen-history assembly, complete-cell
tactic quotation and acceptance, conversion/joint realization and the remaining
API/manual/evidence scope remain part of #10358. Existing owner requests remain
distinct gates. No owner proof, issue, PR or downstream worker is duplicated.
#10358 remains open under #10331, preserving the earlier #10633/#10634 work.
All own local builds and browser processes run serially under an aggregate
32 GiB hard limit, swap disabled and two Lean threads.

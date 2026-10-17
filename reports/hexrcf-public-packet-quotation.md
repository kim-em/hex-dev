# Public scalar-packet quotation

The implementation question is whether the original `ScalarPacket.read`
equation can be quoted from an ordinary public module for a nonconstant
selected-field coefficient, with its actual imported proof bodies checked
within the declared module scope without running the sign producer there.

The public fixture reads the sign of X at the selected root of X³−3. Its
graph nodes and nested moments retain closed applications of the existing
canonical signature encoder. The numerical proposal is checked for matching
context slots before those slots are expressed this way. This is the same
wire format, but it is not an independently frozen numerical signature: the
separate public literal/encoding equation remains requested from #10378.
`Signature.codec_lawful` checks the actual signature argument of each encoded
payload; the callback does not substitute a fixed parent for an arbitrary input.
The fixture also supplies a Boolean normalizer using the checked `root_raw`
binding and the public `root_adjoin` equation. The generic quotation changes
do not discover that source identity themselves.

Two generic quotation changes make this path work.

- A dependent match can retain branch-equality proofs after its major argument.
  Quotation now transports those proofs by equality elimination instead of
  replacing the major while leaving their types unchanged. The result type
  must remain fixed. Independent trailing data is retained; genuinely dependent
  data is refused. Transport is proved with an abstract major and instantiated
  with separately checked moved proofs.
- Meta-level irreducibility does not stop ordinary kernel conversion from
  unfolding a concrete replay function. When the protected function occurs
  explicitly in the original expression, quotation first checks the congruence
  with that function abstracted, then instantiates it with the actual function
  and its checked public equation. Other steps retain the existing congruence
  construction. No exception selects another
  solver, and no kernel or producer guard is relaxed.

The second change addresses an observed full-body kernel timeout. A retained
diagnostic isolates one generated `checkMoment` congruence: its replay rule
and plain congruence check, while its left and right normalization conversions
time out under the diagnostic limit. Joint expression sharing alone still
times out. Abstracting the replay function lets both the universal proof and
its instantiation at the **original target** pass. The full fresh audit then
checks all reachable bodies in its declared module scope. Exported module
axiom placeholders are not used as a substitute for imported bodies.

Folded-reader conversion has a second checked abstraction at canonical
`Element.codec` reads. It binds the codec constructor and every closed proof
helper whose type mentions that constructor, then instantiates the resulting
equation with the original constructor, helpers, result and checked equation.
Abstracting one codec value was insufficient for successive reads with distinct
predecessor-codec expressions: a retained importing diagnostic observes native
sign and query preparation at that conversion. The constructor abstraction
covers both reads. The actual-codec regressions use the recursive
`ScalarQuote.decoderWith` callback and audit their source helper proofs too.
No kernel or producer guard is removed. A separate fresh importing audit
checks 61 theorem bodies and four definitions for the actual-codec readers,
with 56 nonempty traces. Its declared scope includes the source helper proofs
and their generated private proofs; the axiom closure is fully transitive.
The synthetic dependent-match audit checks 114 theorem bodies and 14 definitions,
with 64 nonempty traces. Both retain the unchanged native-producer guard.

The coefficient consumer uses only the newly quoted packet fact for canonical
decoding. It proves that the decoded value is the original selected real root
and that it is positive, using the owner's sign interpretation. The exact
reader equation, original context, polynomial and claimed sign remain bound.
Its fresh importing audit rechecks 656 theorem bodies and 67 definitions in
seven named modules, with 713 nonempty diagnostic traces and the complete
standard-three axiom closure. The source explicitly lists that body scope;
the axiom closure is transitive without that restriction. It rejects any
dependency on the legacy fixed list of fixture facts.

| Request | Charged proof nodes |
| --- | ---: |
| Public original scalar-packet reader | 861,536 |
| Canonical coefficient decode from its fact | 3,249 |
| One dependent match | 1,036 |
| Nested dependent matches | 2,196 |
| Canonical decode retaining its sign proof | 10,035 |
| Successive decodes with distinct predecessor-codec expressions | 19,984 |

These counts charge checked syntax, including repeated occurrences. They are
not unique DAG nodes or evidence of physical sharing.
The additional universal equations also count toward existing requests. The
legacy parent-plus-packet regression now charges 73,992 nodes, its standalone
packet 44,385, and its separate coefficient decode 966. One node below the
standalone budget exhausts at 44,362 plus a requested 23 nodes. Its fresh audit
checks 89 theorem bodies and 11 definitions with 90 nonempty traces. Earlier
source-bound reports retain their original counts and source revisions.

The permanent controls cover one and nested dependent matches, full caller
metavariable restoration, charged callback decline, exact and one-below proof
budgets, wrong proofs, terminal callback failures, independent trailing data
and genuine dependent-data refusal. Further readers continue computing after
transport, retain two trailing proofs and preserve a Boolean branch equality.
Literal Boolean results bypass the callback.
Actual packet controls distinguish compiled rejection from ordinary quotation
refusal and check caller restoration for a wrong sign, a changed polynomial,
an empty graph and context swaps in a node or a nested moment.

These are build-only validation and proof-cost diagnostics with reused
dependencies. They establish no general speedup, scaling law, physical proof
sharing, compiled adapter timing or algebraic completeness. The failed and
cancelled attempts must be distinguished from passing builds; a cancelled
diagnostic is not an audit success.
The [dependent-quotation record](data/hexrcf-dependent-quotation/) binds the
current validation to 40 committed source files and retains 67 artifacts,
including all three fresh audits and desktop/narrow captures. The
[initial packet record](data/hexrcf-public-packet/) retains its own earlier
source revision, counts and two profile captures. Its public-audit target also
passed in a build whose other targets failed; that partial target success is
recorded separately from successful integration. Failed and cancelled builds
and diagnostics that observe forbidden reductions remain distinguishable from
passing acceptance audits.

The [checked manual](../HexManual/Chapters/HexRCF/RootQuote.lean) explains the
public consumer and its boundary. #10358 remains open for general original
source/provider/predecessor assembly, complete-cell tactic quotation and
accepted algebraic completeness, remaining conversion/realization integration
and acceptance evidence. Strict compiled arbitrary-missing-record rejection
and native inverse/xgcd stress remain with their existing owner. No arithmetic
or codec proof is duplicated in this adapter.

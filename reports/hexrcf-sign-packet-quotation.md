# Original sign-packet quotation

The implementation question is whether a supplied optional sign-packet reader
can produce an ordinary proof of its original result after a parent descriptor
has been reconstructed, without relying on the old fixed list of fixture facts.

`RootQuote.quoteOptionWith` lifts an optional reader into checked quotation and
transports the result back to that exact reader. `ScalarPacket.quoteWith` checks
an equality with a prepared context, quotes there, and uses `read_restore` to
restore the fact in the original context. Its model, coefficient codec,
polynomial, claimed sign and graph arguments retain their original expressions.
The context binder is identified by its name and checked type. No owner
arithmetic, decoder representation or mathematical hypothesis changes.
The `fromOption` and `option_eq` definitions operate on `Type` data, as do the
family records; they do not claim support for higher-universe payloads.

The selected positive square-root fixture quotes the parent and the packet for
−2X. Its resulting fact alone supplies the sign evidence for coefficient
decoding. `decoded_value` composes the exact coefficient reader equation with
its ordinary real interpretation as −2√2. The fresh importing audit rejects a
dependency on the legacy `CellReplay.Algebraic.Records` fact list.
It separately requires `decoded_value`'s own dependency closure to include the
new fact and the canonical reader law. The audit rechecks 96 actual theorem
bodies and 11 definitions, with 97 nonempty diagnostic traces and exactly the
standard three axioms in the complete closure. The producer guard is unchanged,
and temporary audit copies are discarded.
The original `Data.lower` still obtains its parent from the legacy
`lowerAccepted` proof made with `decide +kernel`. Quotation supplies an equal
prepared descriptor; it does not remove that original acceptance proof. The
complete axiom closure includes it, while the body diagnostics cover the three
modules named in the record and do not claim to audit that older parent body.

| Request | Proof-node accounting |
| --- | ---: |
| Parent reconstruction and original packet quotation | 105,037 |
| Packet with the checked prepared context already available | 69,973 |
| Coefficient decoding from the new fact, separate request | 966 |
| One-below packet budget | exhausted after 69,950, requesting 23 |

These counts sum syntax checked at each stage, including repeated occurrences.
They are not unique DAG-node counts, sharing measurements, scaling trials or
speedup comparisons. Reused-dependency Lake builds are validation observations.
All own builds use the retained aggregate 32 GiB/no-swap wrapper and two Lean
threads, one build at a time.

The controls include exact and one-below budgets, actual caller metavariable
assignment and restoration on success and final exhaustion, an empty graph,
and a valid graph paired with a wrong sign or a different polynomial. The last
two must reach decoding, reject and restore the mutated caller. A forged
context proof presents the expected type hint but must fail before decoding;
its inputs otherwise match an accepted control. Diagnostics are not parsed to
classify failures or select another solver.

The [checked manual](../HexManual/Chapters/HexRCF/RootQuote.lean) shows the
reader/value composition. The [source-bound record](data/hexrcf-sign-packet-quotation/context.json)
retains validation, failed experiments, audit inventories and review evidence.

The ordinary public-module packet path uses checked header reconstruction and
`SignatureQuote.decoder` with the owner's public full-literal equation. Its
fully numerical counterpart and current proof scope are described in the
[root/header report](hexrcf-root-header-quotation.md). The
[retained-context report](hexrcf-root-preparation.md) covers anonymous original
readers, checked data retention and ordinary public consumers. The original
signature-codec request is satisfied; independently frozen deeper frames still
need the public graph-encoding interface requested from the existing owner.
The historical [source-bound record](data/hexrcf-sign-packet-quotation/context.json)
keeps its original counts and failed probes at its recorded source revision.

No general original
source/provider/predecessor discovery, strict compiled missing-record guarantee,
native inverse/xgcd repair, accepted algebraic completeness or general tactic
installation is claimed. Those and the remaining conversion, realization,
manual and evidence requirements keep #10358 open.

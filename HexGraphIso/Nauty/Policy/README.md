# Search correctness

The production state and operations are in `../Search/State.lean`.
`../Search/Search.lean` contains the direct node/sweep recursion and the
public entry points. `Instance.lean` supplies `Generic.Policy (Search n) n`
and proves the direct recursion equal to the policy recursion in
`../Search/Generic.lean`.

`KeyComplete.lean` proves `canonSpecKey_eq_tracedKey` for nonempty graphs.
The empty graph has a separate certificate case. `Complete.lean` proves
`generators_complete` for every graph, using the actual emitted trace.
Canonicalization imports the key proof without importing generator
completeness. `Result.lean` supplies reachability, labelling, row and trace
facts used by certification.

| Files | Responsibility |
|---|---|
| `Generic/` | Call contracts, `SoundPolicy`, fuel bounds, reach, incumbent bounds, return witnesses and exhaustive-policy agreement with the specification. |
| `Max/` | The actual search invariant, local decision rules, child calls, sweep coverage and received unwind witnesses; `Combine.lean` assembles the rules. |
| `First/` | The first path, its stored codes and target sequence, and its uniform-subtree boundary. |
| `Reference/` | Off-path reference occurrences, their transport through filters, and the returned scatter or orbit witness. |
| `Generated/` | Generated carriers from sibling coverage and the induction through the smaller point stabilizer. |
| `Canon/` | Canonical reference effects, leaf verdicts and their composition through calls. |
| `Cheap/` | Small-cell shape and key equalities used by cheap returns. |
| Shared root files | Partition, comparison, workspace, orbit and trace transitions used by more than one proof family. |

An unwind below the current level transports a witness about a suspended
ancestor child. Intermediate sweeps preserve that witness. Its receiving
sweep turns it into coverage of the child subtree; the maximum contract
combines coverage with the upper bound. Generator completeness additionally
uses emitted scatters and first-path sibling coverage, followed by the
smaller guiding child's generation theorem.

Operations such as recovery and workspace filtering have one production
definition. A change inside an operation is justified by its local
partition, comparison, carrier and trace lemmas and the corresponding
policy rules. A change to control flow also requires the generic recursion,
its call contracts and the direct-recursion equality to agree. Frozen trace
records detect operational changes; the independent nauty campaign checks
canonical answers, and the cactus sweep measures their cost.

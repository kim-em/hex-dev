# Fixed-field quoted proof syntax

The selected-field producer emits literal isolation, radical, root-query and
sign-table evidence before ordinary-kernel quotation. This audit addresses
whether the resulting proof syntax can be represented compactly despite
repeated references. It does not measure elaboration, kernel runtime or the
computational cost of root search.

The retained [audit](data/hexrcf-production-sharing/6a4e48a76/audit.json) and
[complete compiler output](data/hexrcf-production-sharing/6a4e48a76/compiler.log)
come from committed source `6a4e48a76a20a6f18c978786d4fc74b77e0085ce` with Lean
4.35.0-rc3. The audit records 694 repository-local source hashes, dependency
checkout identities and compiled module hashes. Both actual quoted theorems
use only `propext`, `Classical.choice` and `Quot.sound`.

| Actual proof | Reachable local declarations | Distinct syntax nodes | Local expression tree nodes | Expanded local references | Public / private module bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| `closeSections` | 7 | 15,435 | 114,982,423,636 | 114,982,427,770 | 71,288 / 613,776 |
| `furtherSection` | 7 | 23,716 | 426,722,662,510 | 426,722,666,644 | 70,696 / 835,184 |

`closeSections` selects `sqrt(2)` with a second section separated by `2^-132`.
`furtherSection` asks for a real square root of `sqrt(2)` between 1 and 2.
The source modules have matched imports. These are two different formulas;
the table does not isolate precision, degree, atom count or root-count scaling.
The separately retained [production timing report](hexrcf-production-proofs.md)
has different source identities and remains a separate observation.

The [inspection module](../bench/HexRCF/ProofProbe/Production/Sharing.lean)
starts at each theorem and visits the types and bodies of every referenced
declaration emitted in that theorem's own module, including quotation's
auxiliary check theorems. Imported library declarations remain constant leaves.
Missing local bodies and local dependency cycles are errors. Private imports
are used only for inspection of completed proofs; the proof modules themselves
use ordinary imports.

Distinct nodes use structural `Expr` equality, not physical heap identity.
Local expression tree nodes count each reachable declaration once, with
constants as leaves, but expand repeated expression subtrees. Expanded local
references additionally substitute a local declaration's type and body at
every occurrence of its constant. Universe levels and binder names are not
separate nodes. The counter memoizes exact natural-number cardinalities rather
than allocating those expanded trees. Small application checks and a depth-40
shared expression check pin the counting rules: 41 distinct nodes represent
`2^41 - 1` tree nodes.

Most of the large counts here arise from expansion of repeated expression
subtrees, rather than substitution across the seven declarations. The module
byte counts show the size of the actual serialized artifacts, including module
metadata; they are not standalone proof sizes. These observations account for
potential syntax expansion without asserting that quotation physically shares
every structurally equal node, or that the kernel performs one operation per
expanded node. No flattened proof was constructed or timed.

Reproduce the deterministic audit with an unused output directory:

```sh
python3 scripts/bench/hexrcf_production_sharing.py --output reports/data/hexrcf-production-sharing/local
```

The collector builds through Lake, retains its complete output, and rejects a
source change during the build or a missing/duplicate proof result. It records
the checkout state, so a dirty reproduction remains visibly distinct. There
is no host timing schedule or discarded timing sample in this structural audit.
Independent degree/atom/coefficient/precision measurements, phase attribution
and nested tower-depth evidence remain required for the complete extension.

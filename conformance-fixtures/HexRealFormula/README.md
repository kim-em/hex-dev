The schema `hex-real-formula`, version `1`, records exact data in JSONL.
Regenerate with `lake exe hexrealformula_emit_fixtures`; validate with
`python3 scripts/oracle/real_formula.py < formula.jsonl`.

Every row declares its library, profile, seed, case identifier, kind, arity,
and ordered free-coordinate names. Names are display metadata; indices carry
binding identity. Distinct binders may have the same name.

* `qf` rows carry a wire version and a Boolean tree. An atom's `terms` are
  pairs `[exponents, integerCoefficient]`, with one exponent per coordinate.
  `normalized` is the decoded canonical tree, or `null` on rejection. Samples
  carry one reduced `[numerator, positiveDenominator]` pair per coordinate
  and both tree and list evaluator results. Rejected inputs have null results.
  `operations` records node and polynomial counts, degrees, support, NNF,
  lifting, and every checked coordinate removal.
* `rename` rows include the source-to-target index map, target arity and
  normalized result. Noninjective maps combine exponents and may cancel terms.
* `dag` rows carry all nodes, an explicit input array, and a root index.
  Node references must address earlier nodes; input identifiers address that
  input array. Validation includes unreachable nodes. `decoded` is the expanded
  tree or `null`; `dagNodes` and `treeNodes` report sharing separately.
* `prenex` rows record the ordered prefix, binder names, total matrix arity,
  matrix tree, and checked round trip. Coordinates are free parameters first,
  then binders in prefix order.

The independent Python oracle normalizes sparse terms using integer
dictionaries and evaluates Boolean trees with `fractions.Fraction`. It also
checks the DAG and binding metadata. It does not assign rational-sample truth
values to real quantified sentences. Those equivalences are proved in the
companion conformance modules.

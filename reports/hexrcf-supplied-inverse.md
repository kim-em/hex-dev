# Supplied inverse source certificates

[InverseReplay](../adapters/HexRCF/RealCoefficients/InverseReplay.lean) uses the
supplied-equation reader merged through #10844,
`bc79fcf944365a376ed844cefadf100f120b5773`. Its input already contains a checked
context, an actual operand, a checked original packing, and a checked memo.
It preflights every supplied original divisor and the operand before selecting
the equation. A zero divisor produces `Replay.Error.divisor`; absent or
mismatched equation evidence produces `Replay.Error.evidence`. No diagnostic
string chooses a solver, and neither refusal starts another solver.

`check_parts` binds the returned equation to the exact requested operand and
establishes guard preflight. `check_domains` interprets every supplied guard
at the same selected root under the authenticated ordinary-real predecessor
model. `check_source` identifies the supplied output with the inverse of its
exact authenticated source and proves that source nonzero. Source equality
is explicit; a key or polynomial equation alone does not select a real value.
The checker reads the supplied equation without computing an inverse candidate.

The [fresh-module proof](../conformance/HexRCF/SelectedRoot/InverseReplay.lean)
uses the existing selected positive root of `X²−2`. Its supplied original
polynomial is `X²+X/2−2`, which reduces to `X/2`. The scalar graph authenticates
the retained representative; the packing graph checks the original equation;
the inverse graph checks the operand and product-minus-one signs jointly.
The accepted source theorem identifies the output with `(Real.sqrt 2)⁻¹` and
proves the original source divisor nonzero. This example changes the original
packing request; it does not claim a different packed representative.

[Refusal proofs](../conformance/HexRCF/SelectedRoot/InverseControls.lean)
cover a zero in the supplied original guard list, a zero operand, an empty memo
and an out-of-range memo index. Zero precedes missing evidence. The mathematical
reader's domain and query bindings remain those of the actual owner interface.
The ten complete axiom inventories consist of three public source laws,
packet acceptance, the concrete source/domain laws and four refusal laws;
each contains only `propext`, `Classical.choice` and `Quot.sound`.

The [Mathlib-free producer](../conformance/HexRCF/InverseFixture.lean)
regenerates the 17,922-byte [fixture](../conformance-fixtures/HexRCF/selected-inverse.json).
The existing [literal renderer](../scripts/rcf/selected_literals.py) shares
constructor data and independently checks its canonical regeneration. Native
construction is separate from the ordinary-kernel proof of the stored data.
The existing lower context/model setup is reused; these tests are not a
production-free reconstruction of arbitrary contexts.

```sh
lake exe hexrcf_inverse_fixture
python3 scripts/rcf/selected_literals.py --check
lake build HexRCF.SelectedRoot.InverseReplay HexRCF.SelectedRoot.InverseControls
```

[Source bindings and retained checks](data/hexrcf-supplied-inverse/context.json)
separate accepted integration from failed proof drafts. The constructor module
contains 131 shared arrays in 11,329 bytes; the expanded JSON contains 2,648
integer occurrences, with magnitude at most three bits. These are syntax
counts, not executed-work or physical-sharing measurements. The native
producer has 168 local modules in its import cone and only Init/Std at its
external frontier.

The existing optional default target and umbrella include the public module;
the conformance modules extend the existing target. The base rational umbrella
remains independent. The existing rcf manual retains its examples and describes
the source/guard contract. Its new paragraphs are inspected at desktop and
narrow widths. Operational build durations are not new scientific samples or
scaling evidence.

This is coefficient-source replay. The caller still supplies authenticated
source identities, the complete original divisor list and the lawful
ordinary-real predecessor model. The supplied equation is a semantic equality
at the selected root; it cannot replace native arithmetic dictionaries that
require literal equality with the native inverse representation. General
context reconstruction, all-live arithmetic/transport assembly, recursive
reached-data export, whole finite-joint realization and accepted-certificate
completeness retain the [adapter inventory](hexrcf-adapter-evidence.md)
obligations. No new syntax handler or full-tactic completeness is claimed.

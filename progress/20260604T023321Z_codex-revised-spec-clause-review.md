# 20260604T023321Z Codex revised SPEC clause review

## Accomplished

Reviewed the revised proof-layer hygiene clause in
`SPEC/design-principles.md` and its PR #6502 worked instance in
`SPEC/Libraries/hex-matrix.md`.

Checked the surrounding placement next to "Push sorries earlier", the
matrix proof-surface section, and nearby project-wide bridge conventions.

## Current frontier

The revised rule is broadly shippable. The remaining risk is the phrase
"when that theorem is being used as proof authority", which preserves the
intended distinction between definitions/computational lemmas and proof
dependencies but may invite classification games.

## Next step

Tighten that sentence by making the prohibition syntactic/proof-graph
based for sorry-bearing theorem dependencies, while separately permitting
use of definitions and explicitly sorry-free computational lemmas.

## Blockers

No blocker. This was a review-only turn; no Lean code or SPEC source was
modified beyond this progress note.

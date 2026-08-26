# README → reference-manual links

## Accomplished

- Added a low-key `# Reference manual` section, placed just before
  `# Contributing`, to the 12 released-library READMEs (the six
  Mathlib-free libraries and their six `*Mathlib` bridges).
- Linked each via Verso's stable tag-based permalink
  (`find/?domain=Verso.Genre.Manual.section&name=<tag>`), which redirects
  by chapter tag and survives title/slug changes, rather than the
  title-derived page slug.
- Computational READMEs point at their own chapter tag; five bridge
  READMEs point at the computational chapter ("covers this library and
  its computational base"); `HexMatrixMathlib` points at the dedicated
  `hex-matrix-mathlib` "Mathlib correspondence" section, the only bridge
  with its own section tag.
- Confirmed every target tag resolves (HTTP 200) and is present in the
  published manual's `xref.json`.

## Current frontier

Codex second opinion incorporated: tightened bridge wording and the
`HexMatrixMathlib` target. PR opened.

## Next step

Edits land through the normal `sync-released` publish to the split repos;
no hand-editing of mirrors.

## Blockers

None.

# LLL README trim

## Accomplished

Two prose-only follow-ups to the merged #8450 README rewrite, on branch
`lll-readme-trim`:

- `HexLLL/README.md`: collapsed the five-constant dump (`requestedEta`,
  `requestedDelta`, `intervalPrec`, `dispatchFactor`, `steerDimThreshold`)
  in the size-reduction-constants section into one sentence. The names are
  internal tuning the reader can neither act on nor needs; they live at
  their definition sites.
- `HexLLLMathlib/README.md`: glossed the first mention of `121/400` as
  `(11/20)²` with a pointer to `hex-lll`, so a reader landing on the
  headline-result repo first is not met by the constant cold.

## Current frontier

Edits made; no build needed (prose only, no code blocks touched). Opening
a fresh PR because #8450 already merged.

## Next step

Push branch, open PR against `main`.

## Blockers

None.

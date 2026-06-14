## Current state

`HexGF2/Basic.lean` has a cluster of **undocumented** `private`
helper lemmas spanning lines ~275–401 that establish the
`UInt64`-word bit-inspection and `shiftLeft`-with-carry facts behind
`highestSetBit?`, the `GF2Poly` xor, and the one-hot / packed-word
machinery. Each currently has no preceding `/-- … -/` docstring.
This is part of the library's Phase 6 (proof polishing)
docstring-coverage exit criterion.

The 8 declarations in the cluster (verify line numbers at claim time):

- `bit_eq_one_eq_testBit`
- `Nat.testBit_eq_false_of_lt`
- `UInt64.wordBitIsSet_eq_testBit`
- `highestSetBit?_isSome_of_ne_zero`
- `UInt64.bit_xor_bne`
- `UInt64.shiftLeft_or_carry_high_bit`
- `UInt64.shiftLeft_or_carry_low_bit`
- `oneHotWord_bit_toNat`

## Deliverables

1. Add a one- to three-sentence `/-- … -/` docstring to each of the
   8 lemmas above, stating what bit-level fact it proves and where it
   is used (the `highestSetBit?` search, the xor coefficient bridge,
   or the `shiftLeft`-or-carry word reindexing). Note for the two
   `shiftLeft_or_carry_*` lemmas the distinction between the
   high-bit branch (`old + shift < 64`, reads from `w`) and the
   low-bit branch (`64 ≤ old + shift`, reads the carried bits of
   `prev`).
2. Doc-only change: do **not** touch any signature, statement, proof,
   `simp`/`grind` attribute, declaration order, or `private`
   modifier. Additions must be docstring lines only.

## Context

- This matches the established "Phase 6 docstrings for the … helper
  cluster" issue pattern. Describe the *fact*, not the tactic script.
- Do **not** also document the nearby `trimTrailingZeroWordsList_*`
  or `wordBitIsSet` / `highestSetBitBelow?` helpers in this issue —
  keeping the edit to one contiguous region avoids churn; those are a
  separate future batch.
- Phase 6 doc rule: `SPEC/design-principles.md`; `PLAN/Phase6.md`.
- If the cluster has already been documented by a racing PR,
  `coordination skip` with that note rather than forcing edits.

## Verification

- `lake build HexGF2.Basic`: green.
- `git diff --numstat -- HexGF2/Basic.lean`: additions only (`N 0`).
- `git diff --check`: clean.
- Added-line grep finds no `sorry` / `axiom` / `native_decide` /
  `TODO` / `FIXME`.
- `python3 scripts/check_dag.py`: exit 0.

# HexPosDef

Mathlib-free integer and Gaussian-integer positive-definiteness certificates,
structural list checkers, and native no-swap fraction-free production.

`Hex.PosDef.Int.certify` defaults to the triangular method. The explicitly
selected positive-vector method uses exact rational solving and common
denominator clearing. `Hex.PosDef.Gaussian.certify` uses triangular elimination.
Successful results are independently rechecked; unsupported methods and
producer-certificate rejection are separate errors.

The mathematical interpretation and `pos_def` tactic are in `HexPosDefTheory`.
See [the SPEC](SPEC/hex-pos-def.md) and the shared Manual chapter
[`HexManual/Chapters/HexPosDef.lean`](../HexManual/Chapters/HexPosDef.lean).

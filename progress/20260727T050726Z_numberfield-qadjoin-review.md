# HexNumberField QAdjoin review repair

## Accomplished

- Removed the data-producing `sorry` from `QAdjoin.reduce`: certified root
  witnesses now prove positive defining-polynomial degree in HexRoots, and the
  public rational remainder law closes the canonical degree invariant.
- Restated the invariant with `degree?.getD 0`, matching the executable division
  API, and added `QAdjoin.ext` plus `DecidableEq` for canonical coordinates.
- Added a one-sided extended gcd with proved agreement to both relevant fields
  of the existing full algorithm, then switched fixed-field inversion to it.
- Removed the ungated inverse-coordinate footgun and the redundant second
  reduction; inversion now checks for a constant gcd inside the checked API.
- Added compiled guards that construct a real certified root and exercise the
  shipped multiplication, addition, scalar, equality, zero, and one paths.
- Added nonmonic reduction and inverse-coordinate regressions for `2X² - 1`.
- Pinned the Mathlib companion's rational scalar action to avoid a `qsmul`
  instance diamond.
- Rebuilt `HexNumberField` and reran all repository structural/source checks.

## Current frontier

The QAdjoin data path is free of `sorry`, its canonical invariant is backed by
kernel proofs, and the executable regressions now reach the public quotient
operations. The core scaffold retains only its three isolated propositional
zero-certificate obligations.

## Next step

Propagate the core and QAdjoin repair commits to their owning stacked branches,
rebase the approximation PR, and resume the reviewed resultant PRS repairs.

## Blockers

None.

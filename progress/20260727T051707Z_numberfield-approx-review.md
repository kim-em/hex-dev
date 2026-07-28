# HexNumberField approximation review repair

## Accomplished

- Preserved and exposed the refined representative's `SimpleRoot` equality so
  callers can actually thread the result into the next approximation.
- Replaced the global Cauchy guard-bit multiplier with a certified magnitude
  bound from the selected root's current isolation square.
- Moved generic complex-ball zero, addition, multiplication, and rational
  enclosure operations into their owning HexRoots layer.
- Removed intermediate-list allocation and the redundant top-coefficient
  multiplication from rational Horner evaluation.
- Added compiled negative-rounding, nonzero-radius complex-product, and
  end-to-end 64-bit square-root approximation regressions.
- Made the approximation module explicit in the umbrella and corrected the
  fixed-field file organization and threading contract in the SPEC.
- Rebuilt `HexRoots` and `HexNumberField` successfully.

## Current frontier

The approximation milestone now addresses every correctness, performance,
coverage, and layering issue raised by its independent review. Its only
remaining review item is asynchronous verification of the repaired diff.

## Next step

Push the repair, launch its re-review without waiting, and repair/rebase the
Resultant PRS milestone onto the merged resultant contract.

## Blockers

None.

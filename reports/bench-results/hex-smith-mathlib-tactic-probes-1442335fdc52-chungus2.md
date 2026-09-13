# Structural tactic proof evidence

Comparator status: **no-comparable-surface-in-named-comparator**.

Source commit: `1442335fdc528569abce32b9923b5ce364a0b2c4`. Each row retains six adjacent, alternating import-baseline/candidate pairs. The absolute ceiling is 60 seconds per candidate; every completed sample counts.

Kernel seconds are Lean's cumulative `type checking` profile. Certificate statistics and profiler output are included in the measured frontend cost. Full compiler output, raw timings, source hashes, axiom sets, artifact sizes, and host context are in the JSON.

| Module | Fresh median (s) | Fresh max (s) | Paired delta median (s) | Kernel median (s) | Budget |
|---|---:|---:|---:|---:|---|
| `HexSmithMathlib.ProofProbe.ChainConjugateN16M16Bits32Quotient` | 4.029 | 4.142 | 1.477 | 1.305 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN16M16Bits8Quotient` | 3.938 | 4.040 | 1.365 | 1.205 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN2M2Bits32Quotient` | 2.630 | 2.647 | 0.033 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN2M2Bits8Quotient` | 2.637 | 2.691 | 0.024 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN4M4Bits32Quotient` | 2.675 | 2.748 | 0.088 | 0.022 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN4M4Bits8Quotient` | 2.715 | 2.739 | 0.099 | 0.022 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN8M8Bits32Quotient` | 2.831 | 2.958 | 0.260 | 0.153 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN8M8Bits8Quotient` | 2.839 | 2.864 | 0.193 | 0.147 | passed |
| `HexSmithMathlib.ProofProbe.EmptyColumnsN3M0Bits0Quotient` | 2.604 | 2.657 | 0.053 | 0.004 | passed |
| `HexSmithMathlib.ProofProbe.EmptyRowsN3M3Bits0Quotient` | 2.638 | 2.731 | 0.084 | 0.004 | passed |
| `HexSmithMathlib.ProofProbe.EntrywiseLiteralN16M16Bits8Quotient` | 18.630 | 18.764 | 16.093 | 2.825 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN16M16Bits256Quotient` | 4.161 | 4.237 | 1.644 | 1.395 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN16M16Bits32Quotient` | 4.083 | 4.151 | 1.497 | 1.340 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN16M16Bits64Quotient` | 4.026 | 4.049 | 1.407 | 1.250 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN16M16Bits8Quotient` | 3.924 | 4.033 | 1.393 | 1.145 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN2M2Bits256Quotient` | 2.638 | 2.666 | 0.017 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN2M2Bits32Quotient` | 2.656 | 2.796 | 0.101 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN2M2Bits64Quotient` | 2.657 | 2.672 | 0.042 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN2M2Bits8Quotient` | 2.628 | 2.656 | 0.023 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN4M4Bits256Quotient` | 2.652 | 2.739 | 0.097 | 0.024 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN4M4Bits32Quotient` | 2.622 | 2.743 | 0.098 | 0.022 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN4M4Bits64Quotient` | 2.669 | 2.738 | 0.098 | 0.022 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN4M4Bits8Quotient` | 2.728 | 2.779 | 0.100 | 0.022 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN8M8Bits256Quotient` | 2.813 | 2.853 | 0.275 | 0.158 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN8M8Bits32Quotient` | 2.815 | 2.836 | 0.206 | 0.149 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN8M8Bits64Quotient` | 2.805 | 2.832 | 0.193 | 0.144 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN8M8Bits8Quotient` | 2.824 | 2.856 | 0.220 | 0.143 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN16M16Bits32Quotient` | 3.823 | 3.827 | 1.197 | 1.045 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN16M16Bits8Quotient` | 3.712 | 3.926 | 1.097 | 1.008 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN2M2Bits32Quotient` | 2.633 | 2.654 | 0.056 | 0.005 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN2M2Bits8Quotient` | 2.637 | 2.666 | 0.019 | 0.005 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN4M4Bits32Quotient` | 2.677 | 2.792 | 0.091 | 0.020 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN4M4Bits8Quotient` | 2.658 | 2.733 | 0.084 | 0.020 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN8M8Bits32Quotient` | 2.824 | 2.928 | 0.219 | 0.123 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN8M8Bits8Quotient` | 2.778 | 2.830 | 0.205 | 0.121 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN16M16Bits32Quotient` | 6.443 | 6.470 | 3.859 | 3.580 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN16M16Bits8Quotient` | 6.263 | 6.336 | 3.683 | 3.405 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN16M32Bits32Quotient` | 8.229 | 8.329 | 5.640 | 5.395 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN16M32Bits8Quotient` | 7.959 | 8.137 | 5.398 | 5.115 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN2M2Bits32Quotient` | 2.626 | 2.760 | 0.073 | 0.011 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN2M2Bits8Quotient` | 2.635 | 2.767 | 0.084 | 0.012 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN2M4Bits32Quotient` | 2.633 | 2.667 | 0.087 | 0.013 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN2M4Bits8Quotient` | 2.659 | 2.810 | 0.082 | 0.013 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN4M4Bits32Quotient` | 2.723 | 2.728 | 0.172 | 0.055 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN4M4Bits8Quotient` | 2.721 | 2.741 | 0.140 | 0.056 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN4M8Bits32Quotient` | 2.723 | 2.747 | 0.166 | 0.067 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN4M8Bits8Quotient` | 2.731 | 2.762 | 0.145 | 0.069 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN8M16Bits32Quotient` | 3.311 | 3.344 | 0.698 | 0.623 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN8M16Bits8Quotient` | 3.298 | 3.323 | 0.708 | 0.625 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN8M8Bits32Quotient` | 3.114 | 3.229 | 0.537 | 0.449 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN8M8Bits8Quotient` | 3.126 | 3.225 | 0.499 | 0.450 | passed |

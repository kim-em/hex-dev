# Structural tactic proof evidence

Comparator status: **no-comparable-surface-in-named-comparator**.

Source commit: `abf57a6f24ade1e687c7d0ebb6d83ad59fc3dfef`. Each row retains six adjacent, alternating import-baseline/candidate pairs. The absolute ceiling is 60 seconds per candidate; every completed sample counts.

Kernel seconds are Lean's cumulative `type checking` profile. Certificate statistics and profiler output are included in the measured frontend cost. Full compiler output, raw timings, source hashes, axiom sets, artifact sizes, and host context are in the JSON.

| Module | Fresh median (s) | Fresh max (s) | Paired delta median (s) | Kernel median (s) | Budget |
|---|---:|---:|---:|---:|---|
| `HexSmithMathlib.ProofProbe.ChainConjugateN16M16Bits32Quotient` | 4.031 | 4.074 | 1.451 | 1.260 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN16M16Bits8Quotient` | 3.921 | 3.958 | 1.333 | 1.165 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN2M2Bits32Quotient` | 2.639 | 2.652 | 0.021 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN2M2Bits8Quotient` | 2.640 | 2.663 | 0.055 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN4M4Bits32Quotient` | 2.635 | 2.723 | 0.094 | 0.021 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN4M4Bits8Quotient` | 2.679 | 2.739 | 0.108 | 0.021 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN8M8Bits32Quotient` | 2.777 | 2.831 | 0.209 | 0.140 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN8M8Bits8Quotient` | 2.769 | 2.832 | 0.192 | 0.141 | passed |
| `HexSmithMathlib.ProofProbe.EmptyColumnsN3M0Bits0Quotient` | 2.631 | 2.681 | 0.061 | 0.004 | passed |
| `HexSmithMathlib.ProofProbe.EmptyRowsN3M3Bits0Quotient` | 2.633 | 2.740 | 0.087 | 0.004 | passed |
| `HexSmithMathlib.ProofProbe.EntrywiseLiteralN16M16Bits8Quotient` | 18.337 | 18.466 | 15.762 | 2.680 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN16M16Bits256Quotient` | 4.077 | 4.142 | 1.514 | 1.345 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN16M16Bits32Quotient` | 3.985 | 4.055 | 1.388 | 1.235 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN16M16Bits64Quotient` | 3.979 | 4.035 | 1.381 | 1.220 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN16M16Bits8Quotient` | 3.936 | 3.983 | 1.331 | 1.170 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN2M2Bits256Quotient` | 2.636 | 2.705 | 0.096 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN2M2Bits32Quotient` | 2.624 | 2.639 | 0.059 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN2M2Bits64Quotient` | 2.625 | 2.634 | 0.014 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN2M2Bits8Quotient` | 2.620 | 2.636 | 0.045 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN4M4Bits256Quotient` | 2.645 | 2.709 | 0.090 | 0.023 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN4M4Bits32Quotient` | 2.623 | 2.731 | 0.083 | 0.021 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN4M4Bits64Quotient` | 2.622 | 2.707 | 0.080 | 0.021 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN4M4Bits8Quotient` | 2.639 | 2.718 | 0.087 | 0.021 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN8M8Bits256Quotient` | 2.817 | 2.843 | 0.239 | 0.158 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN8M8Bits32Quotient` | 2.817 | 2.830 | 0.230 | 0.140 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN8M8Bits64Quotient` | 2.819 | 2.834 | 0.229 | 0.142 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN8M8Bits8Quotient` | 2.825 | 2.848 | 0.279 | 0.133 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN16M16Bits32Quotient` | 3.781 | 3.846 | 1.204 | 1.030 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN16M16Bits8Quotient` | 3.729 | 3.762 | 1.173 | 0.968 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN2M2Bits32Quotient` | 2.631 | 2.663 | 0.069 | 0.005 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN2M2Bits8Quotient` | 2.638 | 2.658 | 0.083 | 0.005 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN4M4Bits32Quotient` | 2.680 | 2.725 | 0.101 | 0.019 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN4M4Bits8Quotient` | 2.624 | 2.710 | 0.088 | 0.019 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN8M8Bits32Quotient` | 2.777 | 2.830 | 0.229 | 0.121 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN8M8Bits8Quotient` | 2.760 | 2.851 | 0.206 | 0.113 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN16M16Bits32Quotient` | 6.276 | 6.337 | 3.686 | 3.395 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN16M16Bits8Quotient` | 6.112 | 6.237 | 3.546 | 3.245 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN16M32Bits32Quotient` | 8.131 | 8.240 | 5.510 | 5.190 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN16M32Bits8Quotient` | 7.731 | 7.823 | 5.195 | 4.885 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN2M2Bits32Quotient` | 2.630 | 2.650 | 0.081 | 0.011 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN2M2Bits8Quotient` | 2.623 | 2.661 | 0.035 | 0.011 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN2M4Bits32Quotient` | 2.630 | 2.720 | 0.017 | 0.012 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN2M4Bits8Quotient` | 2.631 | 2.709 | 0.076 | 0.012 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN4M4Bits32Quotient` | 2.718 | 2.752 | 0.114 | 0.049 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN4M4Bits8Quotient` | 2.713 | 2.745 | 0.107 | 0.052 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN4M8Bits32Quotient` | 2.712 | 2.750 | 0.103 | 0.068 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN4M8Bits8Quotient` | 2.722 | 2.742 | 0.139 | 0.066 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN8M16Bits32Quotient` | 3.321 | 3.338 | 0.693 | 0.611 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN8M16Bits8Quotient` | 3.240 | 3.332 | 0.652 | 0.557 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN8M8Bits32Quotient` | 3.129 | 3.286 | 0.557 | 0.432 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN8M8Bits8Quotient` | 3.054 | 3.138 | 0.518 | 0.400 | passed |

# Structural tactic proof evidence

Comparator status: **no-comparable-surface-in-named-comparator**.

Source commit: `652e9d9b706e5852f48ef32588a79452fe7ca3d8`. Each row retains six adjacent, alternating import-baseline/candidate pairs. The absolute ceiling is 60 seconds per candidate; every completed sample counts.

Kernel seconds are Lean's cumulative `type checking` profile. Certificate statistics and profiler output are included in the measured frontend cost. Full compiler output, raw timings, source hashes, axiom sets, artifact sizes, and host context are in the JSON.

| Module | Fresh median (s) | Fresh max (s) | Paired delta median (s) | Kernel median (s) | Budget |
|---|---:|---:|---:|---:|---|
| `HexSmithMathlib.ProofProbe.ChainConjugateN16M16Bits32Quotient` | 4.041 | 4.117 | 1.460 | 1.290 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN16M16Bits8Quotient` | 3.927 | 3.947 | 1.287 | 1.150 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN2M2Bits32Quotient` | 2.627 | 2.655 | 0.083 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN2M2Bits8Quotient` | 2.648 | 2.683 | 0.036 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN4M4Bits32Quotient` | 2.628 | 2.829 | 0.092 | 0.021 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN4M4Bits8Quotient` | 2.672 | 2.781 | 0.088 | 0.022 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN8M8Bits32Quotient` | 2.835 | 2.898 | 0.203 | 0.148 | passed |
| `HexSmithMathlib.ProofProbe.ChainConjugateN8M8Bits8Quotient` | 2.822 | 2.858 | 0.207 | 0.136 | passed |
| `HexSmithMathlib.ProofProbe.EmptyColumnsN3M0Bits0Quotient` | 2.647 | 2.680 | 0.090 | 0.004 | passed |
| `HexSmithMathlib.ProofProbe.EmptyRowsN3M3Bits0Quotient` | 2.641 | 2.725 | 0.083 | 0.004 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN16M16Bits256Quotient` | 4.089 | 4.137 | 1.460 | 1.325 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN16M16Bits32Quotient` | 4.019 | 4.134 | 1.407 | 1.240 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN16M16Bits64Quotient` | 4.029 | 4.141 | 1.449 | 1.260 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN16M16Bits8Quotient` | 3.936 | 4.063 | 1.325 | 1.185 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN2M2Bits256Quotient` | 2.641 | 2.714 | 0.084 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN2M2Bits32Quotient` | 2.635 | 2.687 | 0.026 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN2M2Bits64Quotient` | 2.654 | 2.690 | 0.034 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN2M2Bits8Quotient` | 2.638 | 2.682 | 0.018 | 0.006 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN4M4Bits256Quotient` | 2.664 | 2.727 | 0.080 | 0.024 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN4M4Bits32Quotient` | 2.637 | 2.745 | 0.077 | 0.021 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN4M4Bits64Quotient` | 2.664 | 2.724 | 0.048 | 0.021 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN4M4Bits8Quotient` | 2.670 | 2.734 | 0.064 | 0.021 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN8M8Bits256Quotient` | 2.823 | 2.900 | 0.207 | 0.156 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN8M8Bits32Quotient` | 2.815 | 2.927 | 0.280 | 0.140 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN8M8Bits64Quotient` | 2.820 | 2.917 | 0.221 | 0.138 | passed |
| `HexSmithMathlib.ProofProbe.LargeCoefficientsN8M8Bits8Quotient` | 2.832 | 2.845 | 0.196 | 0.138 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN16M16Bits32Quotient` | 3.833 | 3.924 | 1.187 | 1.025 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN16M16Bits8Quotient` | 3.729 | 4.024 | 1.097 | 0.966 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN2M2Bits32Quotient` | 2.638 | 2.654 | 0.029 | 0.005 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN2M2Bits8Quotient` | 2.649 | 2.725 | 0.010 | 0.005 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN4M4Bits32Quotient` | 2.660 | 2.718 | 0.087 | 0.020 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN4M4Bits8Quotient` | 2.645 | 2.739 | 0.031 | 0.019 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN8M8Bits32Quotient` | 2.817 | 2.846 | 0.203 | 0.120 | passed |
| `HexSmithMathlib.ProofProbe.RankDeficientN8M8Bits8Quotient` | 2.821 | 2.833 | 0.192 | 0.115 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN16M16Bits32Quotient` | 6.331 | 6.372 | 3.702 | 3.410 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN16M16Bits8Quotient` | 6.194 | 6.257 | 3.588 | 3.295 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN16M32Bits32Quotient` | 8.136 | 8.262 | 5.537 | 5.210 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN16M32Bits8Quotient` | 7.847 | 7.888 | 5.207 | 4.950 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN2M2Bits32Quotient` | 2.672 | 2.723 | 0.040 | 0.011 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN2M2Bits8Quotient` | 2.659 | 2.724 | 0.058 | 0.011 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN2M4Bits32Quotient` | 2.705 | 2.742 | 0.077 | 0.012 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN2M4Bits8Quotient` | 2.722 | 2.739 | 0.081 | 0.012 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN4M4Bits32Quotient` | 2.745 | 2.839 | 0.114 | 0.053 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN4M4Bits8Quotient` | 2.727 | 2.771 | 0.100 | 0.053 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN4M8Bits32Quotient` | 2.745 | 2.757 | 0.106 | 0.064 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN4M8Bits8Quotient` | 2.732 | 2.841 | 0.102 | 0.067 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN8M16Bits32Quotient` | 3.334 | 3.524 | 0.695 | 0.611 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN8M16Bits8Quotient` | 3.333 | 3.401 | 0.692 | 0.587 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN8M8Bits32Quotient` | 3.147 | 3.236 | 0.570 | 0.431 | passed |
| `HexSmithMathlib.ProofProbe.RectangularPresentationN8M8Bits8Quotient` | 3.156 | 3.177 | 0.505 | 0.421 | passed |

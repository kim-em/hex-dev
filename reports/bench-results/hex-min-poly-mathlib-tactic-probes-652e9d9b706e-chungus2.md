# Structural tactic proof evidence

Comparator status: **no-comparable-surface-in-named-comparator**.

Source commit: `652e9d9b706e5852f48ef32588a79452fe7ca3d8`. Each row retains six adjacent, alternating import-baseline/candidate pairs. The absolute ceiling is 60 seconds per candidate; every completed sample counts.

Kernel seconds are Lean's cumulative `type checking` profile. Certificate statistics and profiler output are included in the measured frontend cost. Full compiler output, raw timings, source hashes, axiom sets, artifact sizes, and host context are in the JSON.

| Module | Fresh median (s) | Fresh max (s) | Paired delta median (s) | Kernel median (s) | Budget |
|---|---:|---:|---:|---:|---|
| `HexMinPolyMathlib.ProofProbe.CyclicN16M16Bits32Equality` | 17.442 | 17.556 | 14.843 | 13.650 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN16M16Bits8Equality` | 17.261 | 17.362 | 14.743 | 13.600 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN2M2Bits32Equality` | 2.647 | 2.715 | 0.103 | 0.020 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN2M2Bits8Equality` | 2.696 | 2.726 | 0.081 | 0.020 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN4M4Bits32Equality` | 2.821 | 2.841 | 0.212 | 0.085 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN4M4Bits8Equality` | 2.779 | 2.829 | 0.199 | 0.088 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN8M8Bits32Equality` | 3.825 | 3.839 | 1.230 | 0.974 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN8M8Bits8Equality` | 3.839 | 3.895 | 1.284 | 0.986 | passed |
| `HexMinPolyMathlib.ProofProbe.EmptyN0M0Bits0Equality` | 2.624 | 2.630 | 0.069 | 0.002 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN16M16Bits32Equality` | 7.650 | 7.751 | 5.084 | 4.795 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN16M16Bits8Equality` | 7.646 | 7.734 | 5.074 | 4.795 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN2M2Bits32Equality` | 2.643 | 2.726 | 0.099 | 0.014 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN2M2Bits8Equality` | 2.635 | 2.660 | 0.083 | 0.014 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN4M4Bits32Equality` | 2.738 | 2.743 | 0.154 | 0.047 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN4M4Bits8Equality` | 2.740 | 2.800 | 0.135 | 0.048 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN8M8Bits32Equality` | 3.044 | 3.131 | 0.501 | 0.404 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN8M8Bits8Equality` | 3.074 | 3.146 | 0.489 | 0.400 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN16M16Bits32Equality` | 29.486 | 29.576 | 26.927 | 18.000 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN16M16Bits8Equality` | 23.801 | 24.342 | 21.160 | 17.900 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN2M2Bits32Equality` | 2.725 | 2.737 | 0.085 | 0.022 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN2M2Bits8Equality` | 2.723 | 2.746 | 0.094 | 0.021 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN4M4Bits32Equality` | 2.827 | 2.841 | 0.208 | 0.095 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN4M4Bits8Equality` | 2.828 | 2.871 | 0.210 | 0.096 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN8M8Bits32Equality` | 4.233 | 4.350 | 1.670 | 1.180 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN8M8Bits8Equality` | 4.126 | 4.241 | 1.550 | 1.165 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN16M16Bits32Equality` | 7.540 | 7.635 | 4.971 | 4.410 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN16M16Bits8Equality` | 7.454 | 7.563 | 4.903 | 4.360 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN2M2Bits32Equality` | 2.647 | 2.726 | 0.106 | 0.013 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN2M2Bits8Equality` | 2.626 | 2.748 | 0.085 | 0.012 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN4M4Bits32Equality` | 2.725 | 2.755 | 0.174 | 0.038 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN4M4Bits8Equality` | 2.727 | 2.737 | 0.170 | 0.039 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN8M8Bits32Equality` | 3.030 | 3.050 | 0.453 | 0.309 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN8M8Bits8Equality` | 3.028 | 3.034 | 0.444 | 0.307 | passed |

# Structural tactic proof evidence

Comparator status: **no-comparable-surface-in-named-comparator**.

Source commit: `1442335fdc528569abce32b9923b5ce364a0b2c4`. Each row retains six adjacent, alternating import-baseline/candidate pairs. The absolute ceiling is 60 seconds per candidate; every completed sample counts.

Kernel seconds are Lean's cumulative `type checking` profile. Certificate statistics and profiler output are included in the measured frontend cost. Full compiler output, raw timings, source hashes, axiom sets, artifact sizes, and host context are in the JSON.

| Module | Fresh median (s) | Fresh max (s) | Paired delta median (s) | Kernel median (s) | Budget |
|---|---:|---:|---:|---:|---|
| `HexMinPolyMathlib.ProofProbe.CyclicN16M16Bits32Equality` | 18.492 | 18.561 | 15.923 | 14.650 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN16M16Bits8Equality` | 18.086 | 18.190 | 15.489 | 14.450 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN2M2Bits32Equality` | 2.631 | 2.741 | 0.094 | 0.020 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN2M2Bits8Equality` | 2.704 | 2.755 | 0.082 | 0.020 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN4M4Bits32Equality` | 2.790 | 2.845 | 0.226 | 0.093 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN4M4Bits8Equality` | 2.773 | 2.831 | 0.204 | 0.083 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN8M8Bits32Equality` | 3.813 | 3.916 | 1.270 | 0.998 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN8M8Bits8Equality` | 3.860 | 3.938 | 1.320 | 1.055 | passed |
| `HexMinPolyMathlib.ProofProbe.EmptyN0M0Bits0Equality` | 2.623 | 2.638 | 0.088 | 0.003 | passed |
| `HexMinPolyMathlib.ProofProbe.EntrywiseLiteralN16M16Bits8Equality` | 18.425 | 18.470 | 15.798 | 2.690 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN16M16Bits32Equality` | 7.834 | 8.074 | 5.256 | 5.000 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN16M16Bits8Equality` | 7.879 | 7.957 | 5.311 | 5.005 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN2M2Bits32Equality` | 2.710 | 2.752 | 0.095 | 0.013 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN2M2Bits8Equality` | 2.681 | 2.758 | 0.113 | 0.013 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN4M4Bits32Equality` | 2.707 | 2.782 | 0.093 | 0.044 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN4M4Bits8Equality` | 2.717 | 2.741 | 0.090 | 0.043 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN8M8Bits32Equality` | 3.067 | 3.129 | 0.493 | 0.415 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN8M8Bits8Equality` | 3.134 | 3.162 | 0.517 | 0.405 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN16M16Bits32Equality` | 30.748 | 31.026 | 28.130 | 19.200 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN16M16Bits8Equality` | 24.994 | 25.199 | 22.435 | 19.050 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN2M2Bits32Equality` | 2.720 | 2.744 | 0.109 | 0.022 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN2M2Bits8Equality` | 2.722 | 2.729 | 0.094 | 0.023 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN4M4Bits32Equality` | 2.813 | 2.934 | 0.205 | 0.098 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN4M4Bits8Equality` | 2.818 | 2.848 | 0.206 | 0.101 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN8M8Bits32Equality` | 4.333 | 4.369 | 1.757 | 1.240 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN8M8Bits8Equality` | 4.209 | 4.335 | 1.645 | 1.200 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN16M16Bits32Equality` | 7.816 | 7.845 | 5.203 | 4.680 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN16M16Bits8Equality` | 7.762 | 7.831 | 5.180 | 4.620 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN2M2Bits32Equality` | 2.698 | 2.727 | 0.099 | 0.013 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN2M2Bits8Equality` | 2.703 | 2.715 | 0.105 | 0.013 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN4M4Bits32Equality` | 2.710 | 2.740 | 0.096 | 0.040 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN4M4Bits8Equality` | 2.716 | 2.746 | 0.106 | 0.039 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN8M8Bits32Equality` | 3.022 | 3.154 | 0.457 | 0.295 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN8M8Bits8Equality` | 3.025 | 3.052 | 0.427 | 0.298 | passed |

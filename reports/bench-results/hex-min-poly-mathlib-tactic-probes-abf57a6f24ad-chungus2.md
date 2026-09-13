# Structural tactic proof evidence

Comparator status: **no-comparable-surface-in-named-comparator**.

Source commit: `abf57a6f24ade1e687c7d0ebb6d83ad59fc3dfef`. Each row retains six adjacent, alternating import-baseline/candidate pairs. The absolute ceiling is 60 seconds per candidate; every completed sample counts.

Kernel seconds are Lean's cumulative `type checking` profile. Certificate statistics and profiler output are included in the measured frontend cost. Full compiler output, raw timings, source hashes, axiom sets, artifact sizes, and host context are in the JSON.

| Module | Fresh median (s) | Fresh max (s) | Paired delta median (s) | Kernel median (s) | Budget |
|---|---:|---:|---:|---:|---|
| `HexMinPolyMathlib.ProofProbe.CyclicN16M16Bits32Equality` | 17.112 | 17.212 | 14.615 | 13.400 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN16M16Bits8Equality` | 17.078 | 17.519 | 14.571 | 13.400 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN2M2Bits32Equality` | 2.611 | 2.664 | 0.103 | 0.019 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN2M2Bits8Equality` | 2.601 | 2.609 | 0.102 | 0.019 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN4M4Bits32Equality` | 2.700 | 2.708 | 0.199 | 0.074 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN4M4Bits8Equality` | 2.695 | 2.733 | 0.198 | 0.073 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN8M8Bits32Equality` | 3.699 | 3.704 | 1.183 | 0.902 | passed |
| `HexMinPolyMathlib.ProofProbe.CyclicN8M8Bits8Equality` | 3.661 | 3.716 | 1.158 | 0.899 | passed |
| `HexMinPolyMathlib.ProofProbe.EmptyN0M0Bits0Equality` | 2.558 | 2.607 | 0.056 | 0.002 | passed |
| `HexMinPolyMathlib.ProofProbe.EntrywiseLiteralN16M16Bits8Equality` | 17.707 | 17.814 | 15.199 | 2.420 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN16M16Bits32Equality` | 7.307 | 7.415 | 4.812 | 4.570 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN16M16Bits8Equality` | 7.309 | 7.402 | 4.804 | 4.585 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN2M2Bits32Equality` | 2.563 | 2.666 | 0.061 | 0.013 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN2M2Bits8Equality` | 2.567 | 2.606 | 0.040 | 0.013 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN4M4Bits32Equality` | 2.605 | 2.625 | 0.103 | 0.040 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN4M4Bits8Equality` | 2.604 | 2.621 | 0.107 | 0.040 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN8M8Bits32Equality` | 2.959 | 3.006 | 0.413 | 0.348 | passed |
| `HexMinPolyMathlib.ProofProbe.NilpotentN8M8Bits8Equality` | 2.997 | 3.006 | 0.489 | 0.348 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN16M16Bits32Equality` | 29.018 | 29.139 | 26.511 | 17.600 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN16M16Bits8Equality` | 23.379 | 23.915 | 20.882 | 17.500 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN2M2Bits32Equality` | 2.615 | 2.646 | 0.105 | 0.020 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN2M2Bits8Equality` | 2.605 | 2.628 | 0.101 | 0.020 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN4M4Bits32Equality` | 2.728 | 2.798 | 0.218 | 0.084 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN4M4Bits8Equality` | 2.719 | 2.738 | 0.209 | 0.083 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN8M8Bits32Equality` | 4.104 | 4.119 | 1.578 | 1.080 | passed |
| `HexMinPolyMathlib.ProofProbe.RationalDenseN8M8Bits8Equality` | 4.000 | 4.029 | 1.497 | 1.070 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN16M16Bits32Equality` | 7.308 | 7.370 | 4.806 | 4.250 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN16M16Bits8Equality` | 7.312 | 7.393 | 4.771 | 4.240 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN2M2Bits32Equality` | 2.601 | 2.680 | 0.101 | 0.013 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN2M2Bits8Equality` | 2.564 | 2.608 | 0.037 | 0.012 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN4M4Bits32Equality` | 2.613 | 2.637 | 0.106 | 0.035 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN4M4Bits8Equality` | 2.657 | 2.732 | 0.136 | 0.035 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN8M8Bits32Equality` | 2.913 | 2.923 | 0.408 | 0.277 | passed |
| `HexMinPolyMathlib.ProofProbe.RepeatedBlockN8M8Bits8Equality` | 2.912 | 2.952 | 0.405 | 0.277 | passed |

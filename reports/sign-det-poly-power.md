# Polynomial powers in direct sign determination

Binary polynomial exponentiation returns the input at exponent one. It no
longer computes and discards that polynomial's square. At exponent two this
also avoids computing and discarding a fourth power. The ordinary power laws,
coefficient-map correspondence, sign-determination semantics and radical
correspondence remain proved. Finite coefficient evidence follows the shorter
computation: exponent one requires no multiplication facts.

## Small current comparison

The retained collection at
[data/sign-det-power-pairs/a3d2df3182](data/sign-det-power-pairs/a3d2df3182)
uses source a3d2df3182 after this correction. It compares actual reduced and
direct moment construction and replay on the same joint binomial inputs at
degrees 3, 7 and 15. Six trial-major rounds run adjacent arms, alternating
AB/BA. The shared lean-bench child runs one cold callback per process.
All 72 observations are retained. The independent known-root inventory and
callback validators pass; every observed digest matches its validated answer.
Source, binary, harness, automatically leased CPU and host load are recorded.
The source reconstruction patch and unchanged collector are retained.

Times below are medians in milliseconds. Ratios are geometric means of the
six adjacent direct/reduced pairs, not ratios of separately pooled medians.

| Degree | Reduced production | Direct production | Direct/reduced pairs | Reduced replay | Direct replay | Direct/reduced pairs |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 6.238 | 6.087 | 0.970 | 3.228 | 3.027 | 0.937 |
| 7 | 36.752 | 38.102 | 1.119 | 19.420 | 19.025 | 0.981 |
| 15 | 233.622 | 261.887 | 1.089 | 120.921 | 128.368 | 1.087 |

Native whole-child peak resident medians range from 72.34 to 72.90 MiB and
include startup and input preparation. They do not isolate callback memory
or measure peak live heap.

These small observations support no uniform winner. There is no fitted
scaling model and no before/after timing claim. The historical collections
use different preparation and warm inner repetitions; their ratios remain
historical observations and cannot isolate the speedup of this correction.
The saved work is established by the executable recursion and its proofs.
No unchanged rerun or large ladder is required to interpret this comparison.

## Verification

Local validation built HexPoly, HexPolyMathlib, HexSignDetMathlib,
HexQuerySemantics and HexConformance together with the native drivers
successfully (13123 build jobs). All 33 field checks and all six joint
benchmark correctness checks passed. The finite nonclosed-reader example
and ordinary-kernel axiom guards remain valid. These correctness checks
complement the recorded measurements; they are not complexity evidence.

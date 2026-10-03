# Extended-GCD backport

Hex backports leanprover/lean4#15160 at
`3c93b48cf60f7053b0a5b3f2ce646a5196c4fc2f`. The natural-number definition
and proofs follow upstream; the runtime adapter uses installed Lean/GMP ABI
functions rather than Lean's private C++ runtime classes. The old signed C
attachment and duplicated C Euclidean algorithm are removed.

`HexArith.Int.extGcd` keeps its signed logical definition. Its proved compiler
rewrite reverses nonnegative inputs to `Nat.extendedGcd` and exchanges the
returned coefficients. Negative inputs retain the signed Lean algorithm.
This establishes exact tuple equality, including zero and equal inputs.

## ECPP comparison

[Raw adjacent AB/BA samples](extended-gcd-paired.json) retain all three trial
pairs, selected CPU, host load, executable hashes, source hashes and commands.
Both executables include the same arithmetic backport; A uses ECPP's established
pure-Nat inverse producer, and B uses the repaired signed API on nonnegative
inputs. Every result hash agrees. These are shared-host compiled runtime
observations, not kernel-check timings or a claimed general speedup.

| # | Operation | A median ms | B median ms | Median paired speedup |
|---|---|---:|---:|---:|
| 1 | `runConvert65` | 0.853 | 0.700 | 1.22× |
| 2 | `runConvert256` | 72.111 | 30.549 | 2.60× |
| 3 | `runConvert512` | 442.482 | 109.955 | 4.02× |
| 4 | `runNative128` | 60.401 | 29.416 | 2.05× |
| 5 | `runNative256` | 745.528 | 192.923 | 3.94× |
| 6 | `runNativeHard` | 1678.709 | 544.139 | 3.00× |

## Verification and removal

The upstream exact-agreement cases, all small signed pairs, multi-limb signed
boundaries and compiled callers compare against references without the compiler
rewrite. Both primitive and signed zero/negative conventions have kernel checks.
The fresh generated split client exercises both the GMP branch and exported Lean
fallback, and its generated release test target builds without Mathlib;
[split evidence](extended-gcd-split.json) records the checked client.

The archive references `__gmpz_gcdext` and no longer exports
`lean_hex_mpz_gcdext`. Affected CRT, inverse and Smith proof consumers build,
as do integer-factorization and ECPP computational targets. All six HexArith
benchmark smoke checks and all 110 release-tool unit tests pass.

Once #15160 lands and the pinned toolchain provides `Nat.extendedGcd`, remove
`HexArith/Nat/ExtendedGcd.lean`, `HexArith/ffi/extended_gcd.c`, the local fallback
export, the object's build entry and copied primitive tests. Import the core
module and recheck the proved bridge against the landed API. Retain Hex's signed
compatibility tests and the ECPP consumer call. Removal comments live beside
these code and build locations as well as in the arithmetic SPEC.

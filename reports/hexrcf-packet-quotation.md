# Quoting an algebraic root table

This prototype quotes the existing checked root-table reader for
`X² − α`, where `α` is the selected positive root of `X² − 2`, and proves
`∃ x : ℝ, x² = Real.sqrt 2 ∧ 1 < x ∧ x < 2`. It tests the complete table
boundary beyond individual scalar and polynomial readers. The source checkpoint
is `250c4bbb5b2c6bfab8cac140bd64a782c7496be8`; all client modules, diagnostics,
logs and artifact digests are retained in the [record](data/hexrcf-packet-quotation/context.json).
The prototype clients are separate from the repository's default conformance
target and manual. This is direct API evidence, not a general tactic result.

## Checked path

`RootQuote` accepts an `Except ε α` reader with a structured error type.
The successful branch still proves the original reader's `toOption` equation;
a structured error remains terminal. The previous `String` restriction rejected
`RootTable.read`, whose error type is the adapter's `Replay.Error`.

The polynomial coefficients are quoted first with `ScalarQuote.quotePolyWith`,
using supplied checked sign facts in the original selected-root context. The
parent defining polynomial is frozen with a proved equality to the original
reduction operation. This avoids unfolding the native source polynomial and
parent descriptor computation during root-table quotation. The stored reader
then consumes the actual owner root literals and proves that its complete table
contains two roots.

The semantic client transports cached operations through their existing equality
laws, applies `RootReplay.fromTable`, and uses its real root-coverage conclusion.
The coefficient interpretation proves that the polynomial is exactly
`X² − C (Real.sqrt 2)`. Taking the absolute value of an interpreted root gives
one ordinary real point satisfying all three witness conditions. No symbolic
infinitesimal or assumed realization is used.

## Proof and resource evidence

The successful structured reader, polynomial and table requests account for
34, 1,224 and 121,995 proof nodes respectively. The fresh importing audit checks
70 actual theorem bodies and 14 definitions, including private auxiliaries and
the final real witness. Its complete transitive axiom closure is exactly
`propext`, `Classical.choice`, `Quot.sound`. Kernel reduction diagnostics reject
native coefficient producers, and the dependency inventory excludes the old
source-polynomial computation and scalar-packet builders.

The final audit build passes 11,030 jobs in 40.499 seconds, using 38.298 CPU
seconds and a 3.1 GiB cgroup peak, with no swap. The retained wrapper enforces
one aggregate 32 GiB service, no swap and two Lean threads. A separate live
policy check verifies those settings; it is not a concurrent sample of that
audit. Reused dependency builds and these observations are not fixed-schedule
scaling, AB/BA or speedup evidence. Completed failures and the operator-stopped
initial dependency-fetch attempt are retained with their actual outcomes.

## Compiled-reader failure

`PacketQuoteRuntime` separately compiles the closed application of the same
parameterized reader. Pinned Lean `v4.35.0-rc3` reports
`unknown join point 'block_0'` and an `ExplicitBoxing` panic. Disabling closed
extraction or recursive specialization/inlining in the retained scoped attempts
does not repair it. The generic parameterized reader compiles, but the closed
quotation wrapper is currently `noncomputable`; the successful proof audit is
not evidence of a successful compiled run. Compiler and kernel checks remain
enabled. The runtime module is an expected failing reproducer, not a passing
regression.

The record includes the exact client sources and local package configuration.
Restore the `.lean.txt` files as `.lean` in a scratch package, point its local Hex
requirement at the source checkpoint, use the existing dependency cache and run
`run-bounded.sh env LAKE_NO_CACHE=true lake build PacketQuoteAudit`.
Build `PacketQuoteRuntime` separately to reproduce the compiler failure.

## Remaining scope

The full extension still requires generic source/provider/predecessor history
assembly, the general handler and accepted completeness, remaining realization
and source conversion, and the required conformance and manual coverage.
Strict compiled whole-reader missing-record rejection and native inverse/xgcd
stress remain unverified. This prototype does not close
[#10358](https://github.com/kim-em/hex-dev/issues/10358).

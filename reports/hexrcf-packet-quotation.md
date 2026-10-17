# Quoting an algebraic root table

This example quotes the existing checked root-table reader for
`X² − α`, where `α` is the selected positive root of `X² − 2`, and proves
`∃ x : ℝ, x² = Real.sqrt 2 ∧ 1 < x ∧ x < 2`. It tests the complete table
boundary beyond individual scalar and polynomial readers. The source checkpoint
is `250c4bbb5b2c6bfab8cac140bd64a782c7496be8`; all client modules, diagnostics,
logs and artifact digests are retained in the [record](data/hexrcf-packet-quotation/context.json).
The prototype record preserves the initial standalone clients. The current
repository also wires `conformance/HexRCF/RootTableQuote/` into `HexConformance`
and documents its checked example in the existing manual. Current validation
is retained separately in the [integrated record](data/hexrcf-packet-quotation/integrated/context.json).
This is direct API evidence, not a general tactic result.

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
34, 1,827 and 121,995 proof nodes respectively. The fresh importing audit checks
71 actual theorem bodies and 14 definitions, including private auxiliaries and
the final real witness. Its complete transitive axiom closure is exactly
`propext`, `Classical.choice`, `Quot.sound`. Kernel reduction diagnostics reject
native coefficient producers, and the dependency inventory excludes the old
source-polynomial computation and scalar-packet builders.

The original prototype audit passes 11,030 jobs in 40.499 seconds, CPU
38.298 seconds and peak 3.1 GiB/no swap. The integrated 14,336-job
library/runtime/audit/manual selection passes in 4 min 0.898 s, CPU
4 min 57.909 s, peak 3.4 GiB/no swap. After final exact-instance and module-export
hardening, the affected 11,191-job integration passes in 2 min 3.370 s, CPU
3 min 28.160 s, peak 3 GiB/no swap. It checks 71 root-table theorem bodies and
14 definitions, the 47/14 callback/module audit, and compiled original-reader
and reconstructed-root controls. Earlier 70/14 and polynomial-budget records
remain bound to their recorded sources.
The final 14,327-job manual render passes in 3 min 31.495 s, CPU
4 min 9.292 s, peak 3.1 GiB/no swap at source
`94665d0ea7224f4f56d663ddd0bd14104d69d8dd`. The source commit includes the
final input-budget wording. All six final desktop/narrow captures were
opened; seven changed-section targets fit1440px and390px. The browser run
takes10.808s with a5.1GiB peak/no swap. Metadata and relative-link checks pass.
The retained wrapper enforces
one aggregate 32 GiB service, no swap and two Lean threads. A separate live
policy check verifies those settings; it is not a concurrent sample of that
audit. Reused dependency builds and these observations are not fixed-schedule
scaling, AB/BA or speedup evidence. Completed failures and the operator-stopped
initial dependency-fetch attempt are retained with their actual outcomes.

## Compiling emitted data

A quoted data expression retained as a definition needs both `addDecl` and
`compileDecl` before compiled clients consume it. The current polynomial and
table clients perform both operations. Compiled controls evaluate the exact
original reader successfully, confirm three stored polynomial coefficients
and two reconstructed roots, and reject an empty scalar-decoding fact list.
The latter checks missing serialized-scalar evidence; it is not a universal
strictness theorem for arbitrary omitted arithmetic facts.

The initial clients omitted compilation of the generated polynomial definition.
Compiling a closed consumer, even just `input.size`, then failed in pinned
Lean `v4.35.0-rc3` with `unknown join point 'block_0'` and an `ExplicitBoxing`
panic. Scoped optimizer changes did not repair those clients. Explicitly
compiling an identical emitted definition repairs both the minimal input test
and the complete root-table call. The current default conformance uses
computable reader/data definitions and keeps compiler and kernel checks enabled.
The failed original sources and logs remain in the prototype record, with the
successful compilation-isolation clients in the integrated record. An attempted
`noinline` attribute on an imported definition was rejected, so that attempt
does not test the effect of an eligible local `noinline` annotation.

The original record includes exact standalone client/package sources. Restore
its `.lean.txt` files as `.lean` in a scratch package, point its local Hex
requirement at its recorded source checkpoint, use the existing dependency
cache, and run `run-bounded.sh env LAKE_NO_CACHE=true lake build PacketQuoteAudit`.
Its original runtime module reproduces the missing-compilation failure.
For the corrected repository path, build `+HexRCF.RootTableQuote.Runtime` and
`+HexRCF.RootTableQuote.Conformance` at the integrated source checkpoint.

## Remaining scope

The full extension still requires generic source/provider/predecessor history
assembly, the general handler and accepted completeness, remaining realization
and source conversion, and the required conformance and manual coverage.
Strict compiled whole-reader missing-record rejection and native inverse/xgcd
stress remain unverified. This prototype does not close
[#10358](https://github.com/kim-em/hex-dev/issues/10358).

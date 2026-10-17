# Quoting an algebraic root table

The current example quotes the checked complete table for `X² − α`, where
`α` is the selected positive root of `X² − 2`, and proves an ordinary real
fourth-root witness. The interpreted list is strictly increasing, has length
two, has no duplicates, and contains exactly every real solution of
`y² = Real.sqrt 2`. Both original reader equations are retained.

The current code/render source is `a8f13c8c119fc41bfe2ca5632f272dbbcd552a58`;
its [review record](data/hexrcf-packet-quotation/review/context.json) binds the
source hashes, actual inventories, all completed failed/passing attempts,
commands and final captures. The original standalone prototype at
`250c4bbb5b2c6bfab8cac140bd64a782c7496be8` stays in its
[prototype record](data/hexrcf-packet-quotation/context.json), and the earlier
default-conformance snapshot stays in the
[pre-review integrated record](data/hexrcf-packet-quotation/integrated/context.json).
These are direct API results, not a general tactic result.

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
The `solutions` regression additionally uses both directions of the supplied-table
coverage theorem: the interpreted list has length two, has no duplicates, and
contains exactly every real solution of `y² = Real.sqrt 2`, in strict increasing
order through the owner’s `Result.ordered` theorem. `checked_witness`
retains both original reader equations alongside the witness. The witness
itself uses the certified reconstructed data; its bounds follow from the
squared equation and the selected coefficient's checked bounds.

Quotation of the actual `readTable [] input` reader returns structured invalid
provider evidence with the exact provider key/version and restores the entire
saved declaration/metavariable state. This exercises the real reader's failure,
separately from the small structured-error shape probe.

## Proof and resource evidence

The successful structured reader, polynomial and table requests account for
34, 1,827 and 121,995 proof nodes respectively. The fresh importing audit checks
74 actual theorem bodies and 14 definitions, including private auxiliaries and
the final real witness and complete solution-set theorem. Audit copies are
checked in temporary kernel environments, then discarded; an assertion requires
that no copied declaration survives in the module. Its complete transitive axiom closure is exactly
`propext`, `Classical.choice`, `Quot.sound`. Kernel reduction diagnostics reject
native coefficient producers, and the dependency inventory excludes the old
source-polynomial computation and scalar-packet builders.

The original prototype audit passes 11,030 jobs in 40.499 seconds, CPU
38.298 seconds and peak 3.1 GiB/no swap. The integrated 14,336-job
library/runtime/audit/manual selection passes in 4 min 0.898 s, CPU
4 min 57.909 s, peak 3.4 GiB/no swap. After final exact-instance and module-export
hardening, the affected 11,191-job integration passes in 2 min 3.370 s, CPU
3 min 28.160 s, peak 3 GiB/no swap. At that source it checks 71 root-table theorem bodies and
14 definitions, the 47/14 callback/module audit, and compiled original-reader
and reconstructed-root controls. Earlier 70/14 and polynomial-budget records
remain bound to their recorded sources.
The pre-review 14,327-job manual render passes in 3 min 31.495 s, CPU
4 min 9.292 s, peak 3.1 GiB/no swap at source
`94665d0ea7224f4f56d663ddd0bd14104d69d8dd`. The source commit includes the
final input-budget wording. All six pre-review desktop/narrow captures were opened; eight changed-section
targets fit 1440 px and 390 px. That browser run takes 10.808 s with a
5.1 GiB peak/no swap. Its source checks and report relative-link checks pass.
The retained wrapper enforces
one aggregate 32 GiB service, no swap and two Lean threads. A separate live
policy check verifies those settings; it is not a concurrent sample of that
audit. Reused dependency builds and these observations are not fixed-schedule
scaling, AB/BA or speedup evidence. Completed failures and the operator-stopped
initial dependency-fetch attempt are retained with their actual outcomes.

The strengthened source `6f648bbd468e683517ddf0ab7a05225c83adbbf9` states
the exact polynomial and table reader equations in `checked_witness`. Its
74/14 body audit passes with both completeness directions and no retained
audit copies. The affected manual/audit selection passes 11,770 jobs in
7.265 s, CPU 9.274 s, peak 1 GiB/no swap, including reused dependencies.
The fresh audit itself also passed in the preceding invocation; that whole
invocation failed on a manual namespace spelling, which the passing selection
corrects. The prior 11,771-job runtime/audit/manual selection passes in
31.974 s, CPU 38.052 s, peak 2.1 GiB/no swap at source `3e5d19e113`.

The final 14,327-job full manual render passes in 2 min 32.958 s,
CPU 2 min 40.649 s, peak 2.2 GiB/no swap. The absolute manual-source report
link is suitable for the rendered HTML. Earlier timings are source-labelled;
the manual points to the report instead of attaching an older source timing
to the new theorem inventory. Failed namespace, proof-rewrite and narrow-layout
checks remain retained alongside successful results.

At source `a8f13c8c119fc41bfe2ca5632f272dbbcd552a58`, the final selected
11,783-job runtime/audit/manual validation passes in 2 min 18.333 s,
CPU 3 min 45.941 s, peak 4 GiB/no swap. It checks the 74/14 root-table audit,
the inherited 56/14 callback audit, strict real ordering, full coverage,
both exact reader equations and the actual terminal reader-failure control.
The final full 14,327-job render passes in 3 min 15.228 s,
CPU 3 min 53.476 s, peak 3 GiB/no swap. All eight final desktop/narrow captures
were opened; all nine changed-section targets fit 1440 px and 390 px with
zero measured overflow. The browser takes 11.092 s, CPU 49.679 s,
peak 8.3 GiB/no swap. The two failed layouts and all their captures remain
retained: 39 px overflow at source3e5d, then14 px at source6f648. Their old
inspection files were stale after early failure and were excluded explicitly.
The final code uses a local list binding to keep the same table-specific
statement readable on narrow displays. Source checks and report/manual
relative-link checks pass. These are cached build observations, not scaling
or matched performance measurements.

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

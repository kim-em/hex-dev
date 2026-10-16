# Current OrderedFn executable identity

The build at `9b1915c218366c781c43da00143a5d8ea41976ee` incorporates the merged
#10960/#10962 owner milestones and the computational acceptance checks. Its
5,172 source/configuration inputs and sixteen clean pins remain unchanged across
the native build. `list` and `verify` pass. No timing measurements are collected.

The executable is byte-identical to the measured integrated candidate:
`19a7750209804b74ea3ea0d480b6aebedfe1b4bd4c6eb7d3b4dcdc90f1592c8f`.
Its compiler/Lake binaries, sixteen pinned requirements, complete 89-file native
import closure and both captured generated-C artifacts also match that candidate.
The eleven compressed build/input/code/validation records retain the existing
source-freezing script unchanged. The executable itself is not committed.

The global Lake file differs only by added RealClosure test/semantic and
provider-history experiment globs from #10962. The original complete-comparison
`replay.py --current` correctly refuses this Lake-file difference; its strict
rule is unchanged. This separate source/build check reconciles that difference
without weakening replay, changing old records or collecting another sample:

```sh
python3 reports/ordered-fn-declaration-review/core-runtime/check.py
```

The checker validates every retained binding, both independently captured input
inventories, all current source/configuration bytes, new tracked source inputs,
current clean pinned requirements and measured executable/SDK/code identity.
It does not execute binaries or infer phase acceptance from a smoke verdict.
The [complete comparison](../../bench-results/ordered-fn-final-comparison/README.md)
remains the separately retained computational evidence.

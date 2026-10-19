# Current OrderedFn executable identity

The build at `9b1915c218366c781c43da00143a5d8ea41976ee` incorporates the merged
#10960/#10962 owner milestones and the computational acceptance checks. Its
source is retained by the non-release tag
`audit/issue-10575-orderedfn-core-acceptance-input-v1`. Its 5,172 source/configuration inputs and sixteen clean pins remain unchanged across
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

The default mode validates every retained binding, both independently captured
input inventories, measured source-record bindings, the seventeen `list`/`verify`
results and measured executable/SDK/code identity. It remains usable after later
source changes. An optional strict check also compares all current source inputs,
new tracked sources and clean pinned requirements:

```sh
python3 reports/ordered-fn-declaration-review/core-runtime/check.py --current
```

This mode matches the build at `9b1915c` and its source-identical evidence commit
`b407d48`. Later changes, including subsequent lint-only checks, intentionally
refuse rather than refreshing the frozen records. The native source, SDK and
executable identities established by that build remain separately scoped.
It does not execute binaries or infer phase acceptance from a correctness-only verification verdict.
Tamper controls check standalone archive verification without a source checkout,
changed executable/source identities, an unauthenticated copied measurement
record, an empty generated-code inventory, mismatched configuration bindings and
corrupted verification output:

```sh
python3 reports/ordered-fn-declaration-review/core-runtime/test_check.py
```

The [complete comparison](../../bench-results/ordered-fn-final-comparison/README.md)
remains the separately retained computational evidence.

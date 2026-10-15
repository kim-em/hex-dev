# Sturm proof, API and manual acceptance

HexSturm and HexSturmTheory satisfy Phases 5–7. This is local library
acceptance, not publication eligibility or acceptance of the whole
real-closure family. The owner Phase-4 attestation is merged in
[#10860](https://github.com/kim-em/hex-dev/pull/10860); its
[readiness matrix](real-closure-prerequisites.md) and
[performance report](hex-sturm-performance.md) retain evidence and limits.

## Individual API assessment

The [declaration review](sturm-declaration-review/README.md) assesses all
48 handwritten computational declarations in four production modules and
96 companion declarations. Every computational module still matches its
`reviewed_sha256` byte for byte. The review covers prepared-domain
reconstruction/projections, whole-`Option` producer agreement, reduced
queries, literal certificate bindings, cached/plain checker equality and
certificate transport. Characterizing lemmas expose these contracts without
forcing clients to unfold private representations. The public umbrella
imports all four modules.

The [individual computational assessments](sturm-declaration-review/computational.md),
[zero-reference dispositions](sturm-declaration-review/zero-references.md) and
[helper paths](sturm-declaration-review/helper-paths.json) distinguish
intentional public API from dead declarations. Each retained public
characterization has an individual contract and disposition; production
reference counts alone do not decide usefulness. The private computational
helper `modImpl_eq_mod` reaches the public reduced-query characterization.
PreparedDomain's private constructor supports checked reconstruction.
No declaration is accepted solely because it compiled or passed a linter.

The compiler inventory is historical, preserved at
`audit/issue-10575-sturm-companion-phase7-complete` before the Theory rename.
It is not a freshly generated reference graph for current main. Unchanged
core source permits reuse of the individual API decisions and helper paths;
current public imports, lints, kernel tests and manual examples are checked
separately. The historical manifest and compiler capture remain unchanged.
The [current reconciliation](bench-results/sturm-phase6-comparison/cap-complete-v3/current-source.json)
also checks all seven companion modules (96 declarations): normalizing only
the recorded Mathlib-to-Theory names makes the historical reviewed bytes
identical to the current files. This checks the rename without presenting
the historical reference graph as a new capture.

## Native regression comparison

The [complete comparison](bench-results/sturm-phase6-comparison/cap-complete-v3/README.md)
passes all 58 declared timing families and all 246 parameter comparisons under
the pinned 10-percent rule. All four balanced AB/BA blocks completed: 464
parent exports, 1,968 measurement points and 58 successful native guards.
The largest median increase is 5.156 percent. There is no integrity failure,
inconclusive rerun, or omitted family/parameter. This checks computational
regression against the most recent committed benchmark baseline; it is not
a new complexity attestation or theorem timing pass.

The producer is `8e5b3e40a69117c84bb6f0c19aaad93a26049ab8`, against baseline
`75fbfa04550ae0f76df074176f44bf0f2533334a`. The
[current reconciliation](bench-results/sturm-phase6-comparison/cap-complete-v3/current-source.json)
covers the benchmark's complete 62-file resolved import cone. Its only two
changes from recorded candidate files are documentation edits in
`bench/HexSturm/Bench.lean` and `HexRealRoots/Chain.lean`. The computational
code and registrations are unchanged. The original capture records the exact CLI pin,
but not individual hashes for three CLI source files. The current CLI checkout
is clean at that pin; the reconciliation distinguishes this check from an
attestation of unrecorded original file bytes. Executable
digests and exact harness pins remain in the archived context. Comment changes
do not warrant new measurements.

Sturm computes natively in Lean without calling the test oracles at runtime;
its native import cone excludes Mathlib and Tau Ceti. It exposes no
irreducibility or field-construction claim. HexSturmTheory is proof-only:
its SPEC uses representative kernel examples and axiom audits, not a compiled
benchmark baseline. Those inapplicable criteria do not create timing work.

## Build, conformance and trust checks

The full monorepo build passes all 14,725 jobs on
`leanprover/lean4:v4.35.0-rc3`, at source commit
`3a9c721289b10bfc826887dc5aab3e2bc32bdfe1`. Focused acceptance passes
11,647 jobs and uses ordinary public imports:

```sh
lake build HexSturm HexSturmTheory HexSturmTheoryTests HexQuerySemantics \
  +HexSturm.Conformance hexsturm_emit_fixtures HexManual.Chapters.HexSturm
python3 scripts/check_dag.py
python3 scripts/ci/check_benches_mathlib_free.py
python3 scripts/ci/check_named_admissions.py
python3 scripts/check_phase7.py
```

The tests include environment lints (including public/theorem docstrings) on
both production roots and ordinary-kernel
replay checks. Semantic replay in `HexQuerySemantics` retains explicit axiom
guards allowing only `propext`, `Classical.choice` and `Quot.sound`. The named
admission check scans the relevant production cones. A separate comment/string-aware
scan covers both Sturm umbrellas, both library directories, companion adapters
and computational conformance. No completed claim uses a sorry, new axiom or
`native_decide`.

Conformance checks ordinary/prepared queries and counts, cached/plain replay,
endpoint retargeting and positive certificate transport. Controls include
zero/constant/repeated heads, invalid domains, noncanonical storage, changed
literal bindings and corrupted evidence. The
[direct independent oracle](sturm-direct-conformance/README.md) passes all
192 serialized frontend cases with python-flint 0.9.0 / FLINT 3.6.0 and nine
refusal-control tests. Fresh native emission is byte-identical to the retained
fixtures. Integer/field differential controls supplement exact qqbar sign
answers; examples and oracles do not replace arbitrary-certificate soundness
or producer-totality proofs.

Reproduce the fresh emission and independent oracle checks using the existing
corpus and pinned Python dependency:

```sh
.lake/build/bin/hexsturm_emit_fixtures > /tmp/sturm.jsonl
cmp /tmp/sturm.jsonl conformance-fixtures/HexSturm/sturm.jsonl
uv run --with python-flint==0.9.0 python scripts/oracle/sturm_flint.py --check
uv run --with python-flint==0.9.0 python scripts/oracle/test_sturm_flint.py
```

The separate source scan and reviewed-core identity check are reproducible
without rewriting any historical binding:

```sh
python3 - <<'PY'
import hashlib, json
from pathlib import Path
from scripts.ci.check_named_admissions import ADMISSION, code_only
paths = [Path('HexSturm.lean'), Path('HexSturmTheory.lean')]
for directory in ('HexSturm', 'HexSturmTheory',
                  'adapters/HexSturmTheory', 'conformance/HexSturm'):
    paths.extend(sorted(Path(directory).rglob('*.lean')))
for path in paths:
    assert not ADMISSION.search(code_only(path.read_text())), path
manifest = json.loads(Path('reports/sturm-declaration-review/manifest.json').read_text())
modules = [m for m in manifest['modules'] if m['path'].startswith('HexSturm/')]
for module in modules:
    actual = hashlib.sha256(Path(module['path']).read_bytes()).hexdigest()
    assert actual == module['reviewed_sha256'], module['path']
print(len(paths), 'scanned files;', sum(len(m['handwritten_declarations'])
      for m in modules), 'unchanged reviewed core declarations')
PY
```

## User documentation and boundary

The [Verso chapter](../HexManual/Chapters/HexSturm.lean) explains the success
domain, counts versus sign sums, preparation, reduced queries, endpoint
retargeting, literal replay, transport and mathematical correspondence.
Its live examples build. The complete manual rendered successfully at the
same `3a9c721289b10bfc826887dc5aab3e2bc32bdfe1` source. All seven Sturm
sections, navigation, mathematical text, declaration cards and example code
were visually inspected at 1,440 and 390 pixels, with no document overflow.
There are no tables in this chapter. No tutorial is anchored to Sturm. The
[README](../HexSturm/README.md) states the computational/proof boundary and
unreleased status; its two quickstart guards are already exercised in
`conformance/HexSturm/Conformance.lean`.

The [publication plan](real-closure-publication.md) retains dependency pins,
candidate consumer checks and external distribution requirements. This
acceptance changes only HexSturm's remaining local phase counter. It does not
promote transitive dependencies, add released manifest entries or accept
unfinished tower/tactic owner contracts.

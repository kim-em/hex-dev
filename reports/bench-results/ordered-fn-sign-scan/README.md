# Infinitesimal sign and coefficient scan

Native infinitesimal signs use normalized numerator storage to detect formal
zero. Their coefficient scan first recognizes a shared zero object and otherwise
uses the original coefficient equality. Both kernel-facing reference bodies are
unchanged and marked noncomputable. Whole-function compiler equalities preserve
all results for arbitrary coefficients and predecessor sign procedures; no order,
provider or sharing hypothesis is added to their statements.

## Declaration assessment

| Declaration | Proof/API decision |
| --- | --- |
| `Infinitesimal.lowestIndex` | Preserve the public type and original coefficient scan as the kernel reference. Existing semantic consumers retain that definition. |
| `Infinitesimal.lowestIndexImpl` | Native implementation twin required by compiler registration. Pointer equality is a shortcut; distinct objects always use the original decidable equality. The result remains the array size when every coefficient is zero. |
| `Infinitesimal.lowestIndex_eq_impl` | Proves whole-function equality for arbitrary `Zero` and `DecidableEq` instances, including empty arrays and unshared equal coefficients. |
| `Infinitesimal.sign` | Preserve the numerator-zero guard and both coefficient signs in the kernel reference. Monic denominators can still have negative lowest coefficients. |
| `Infinitesimal.signImpl` | Native implementation uses canonical polynomial storage for the zero guard; both remaining coefficient scans use the registered twin. No real-extension trial or approximation code changes. |
| `Infinitesimal.sign_eq_impl` | Proves whole-function equality for every predecessor sign, independently of semantic order laws. The normalized storage invariant discharges the changed guard. |

Every new helper is used by its actual native caller or compiler registration.
The computational imports remain Mathlib- and Tau-Ceti-free. Both new equalities
have exactly `propext` and `Quot.sound`, guarded in the core tests. The
3,194-job proof/lint/test build also checks all 298 companion constants across ten
modules against the standard kernel axioms. Conformance and native emitters build.
All 80 freshly emitted infinitesimal fixtures and 122 real fixtures are
byte-identical and pass the pinned Z3/exact-Fraction and FLINT/Z3/exact-Fraction
oracles. The infinitesimal fixtures include successive extensions, zero,
non-monic definitions, denominator signs and the paper comparisons.

The generated native scan contains a direct pointer comparison followed by the
ordinary structural equality on the unequal-address branch. Its caller uses
`DensePoly.isZero` before scanning. The third-level benchmark specializes preparation and the scan in the same
module. Its generated scan uses the same closed zero object as the monomial's
padding, avoiding repeated equality of nested rational functions in this fixture.
The generic library path obtains its comparison zero by calling the coefficient
instance; the ordinary rational-function zero constructor allocates a fresh
object there, so that path takes structural equality instead. Arithmetic zeros
also need not share the comparison object. None of the six selected cases is a
separate fallback-performance workload. The complete historical comparison
still includes comparison/subtraction and the remaining families.

The 98% third-level result therefore concerns this specialized, shared-padding
fixture. It is not an allocation count or a universal caller speedup. Unboxed
scalar coefficient representations may also incur boxing for core pointer
inspection; that cost is not measured by these Rat/RationalFn cases.

The implementation calls the pinned core `withPtrEq` API with its required proof
that the shortcut agrees with equality. Core supplies that API's existing native
pointer implementation; the ordinary kernel sees its mathematical definition.
The Hex compiler registrations are both proved equalities. This change introduces
no `@[implemented_by]` registration, unsafe declaration or axiom in Hex; an axiom
report alone does not describe core's native implementation.

Both arms' generated `Infinitesimal.c` and `Bench.c` are retained under
`capture/code-reconstruction/`, with source inventories, pinned SDK executable
hashes and generated-code hashes. These separately captured builds reproduce
both measured executables byte-for-byte; the candidate's C also reproduces the
originally captured C exactly. The parent uses its original structural scan and
polynomial equality guard. This is code-provenance evidence, without new timing
observations or a claim to recover unrecorded build inputs.

## Bounded comparison

The question is whether the combined implementation resolves the selected height
and third-level sign costs without a neighbor regression. The source is
`b4e1e1522a81b09205ff792f8b1d0dc650a63e37`, retained by
`audit/issue-10575-orderedfn-sign-scan-input-v1`; the unmodified parent is
`10dd31805fb871a21ef9235a72e3e8f455a65224`. Both use Lean 4.35.0-rc3 with identical
clean dependency pins. The separate parent build reproduces the merged
positive-quotient executable byte-for-byte. These observations compare the
combined change with that parent; they do not isolate each component's effect.

The recorded criterion requires strictly more than 10% improvement at
`height@128`, `height@2048` and `third@1024`, with no greater-than-10% regression
at the three neighboring cases. All six cases use three trial-major adjacent
AB/BA/AB source pairs on one automatically leased CPU, a one-second batching
target and `LEAN_NUM_THREADS=4`. Host activity is recorded without a quiet-core
condition or rejected samples.

| Workload | Parameter | Parent median ns/call | Candidate median ns/call | Change |
| --- | ---: | ---: | ---: | ---: |
| height | 128 | 69.689273 | 57.182903 | −17.945904% |
| height | 1024 | 69.872771 | 57.489332 | −17.722839% |
| height | 2048 | 70.128218 | 57.087533 | −18.595489% |
| third | 512 | 31,342.259857 | 708.162093 | −97.740552% |
| third | 1024 | 61,989.860413 | 1,142.395996 | −98.157124% |
| third | 2048 | 124,625.738647 | 2,031.706413 | −98.369754% |

All 36 arms complete, with matching per-case hashes and unchanged source/tool
inputs. All 72 original raw streams are retained. Each per-arm median uses three
observations. These host-specific results meet the bounded expansion criterion.
Small result hashes are consistency controls; they are not mathematical oracles.

Each arm binds 5,164 source/configuration inputs, 89 native import files and
sixteen clean package pins. Only `Infinitesimal.lean` changes in the native import
paths; the broader inventory also changes `Tests.lean`. Separately captured
before/after build snapshots agree. The parent executable SHA-256 is
`e8634bce8b34b35651fc5f73d249d7f2385370df0a53fa5d9b9b087d0b5d1662`; the candidate is
`19a7750209804b74ea3ea0d480b6aebedfe1b4bd4c6eb7d3b4dcdc90f1592c8f`.
Child Git fields describe the invocation checkout; the source manifests identify
each executable's producer separately.

This implementation combines the bodies of the two retained storage-test and
pointer-scan variants. Their composition addresses the interaction exposed by
the [retained zero-storage result](https://github.com/kim-em/hex-dev/blob/audit/issue-10575-orderedfn-zero-investigation-v2/reports/bench-results/ordered-fn-zero-investigation/README.md).
The storage-test variant improved height but slowed the third-level case by
6.7%, failing its criterion; its measurements and recording defect remain retained.
The new combined binary meets its own declared rule. These data do not isolate
the pointer-only variant's effect. This comparison does not retry that earlier
binary or replace any failed experiment. Neither this result nor the independent
[positive-quotient diagnostic](../ordered-fn-positive-quotient/README.md) establishes
the required complete historical-baseline comparison. That comparison and
reconciliation of every remaining finding still precede core Phase-6 acceptance.
No Phase-4 scaling claim, phase counter or publication configuration changes.

## Offline evidence replay

The manifest binds the compressed and original files, including the complete
terminal context, raw observations, proposal/decision, producer scripts, independent
build inventories, generated native code, fixture bytes and validation logs.
Native executables are not committed. Replay collects no timings:

```sh
python3 reports/bench-results/ordered-fn-sign-scan/replay.py
```

It verifies archive hashes, original proposal agreement, the recorded criterion,
complete adjacent-arm schedule, commands, compiler identity, raw observations,
matching hashes, source/binary/script bindings, separately captured build
inventories, validation-log results, generated-code/source/SDK bindings, the
recorded thread/CPU selection and all six median calculations. The hash-bound measurement script checks live
source inputs again on exit; replay does not recover that host's final filesystem
or rebuild the executables. CPU affinity and the thread setting were applied by
the hash-bound producer; the capture records the selected CPU and the original
affinity, without a post-change or child-affinity observation.

Also check all current native import files, the axiom tests and three build
configuration files against the measured candidate:

```sh
python3 reports/bench-results/ordered-fn-sign-scan/replay.py --current
```

This requires the recorded dependency checkouts and intentionally refuses changes
to those inputs. Neither replay mode establishes a current-source performance pass.

# Sturm extension and nested-evidence observations

The Sturm SPEC requires extension-depth and nested-evidence sweeps. The
existing consumers instantiate its coefficient operations and supply those
observations. This audit reuses their retained evidence; it does not infer
performance from correctness fixtures or require the consumers' issues to
close before the prerequisite can be attested.

| Required axis | Actual retained sweep | Relation to Sturm and limits |
| --- | --- | --- |
| Extension-depth coefficient signs | [Corrected nested-sign collection](sign-det-nested-signs.md#corrected-declaration-measurements): depths 2/4/6/8/10/12, six fixed trial-major rounds, all 36 observations; source `92056cad4a`, consistent constructor-recurrence model | The actual ordered-field sign operation supplied to shared queries. It measures sign plus nested numeral construction, not whole-query time. The original incorrect leaf-sign model and all 36 failed characterizations remain retained. |
| Actual query/replay work in nested fields and growing evidence | [Nested tables](sign-det-nested-tables.md): fixed depths one/two, query counts 128/256/512/1024/2048, six rounds, all 120 observations; source `219e2232cf`, four consistent models | `NestedTables` prepares a `Sturm.PreparedDomain`; BKR production constructs 4s−1 moment chains and replay checks 4s−1 moment certificates plus their domains. Tree nodes, query reductions and moment slots grow with s. Production/checking overlap and include consumer matrix/list work; these are not isolated Sturm-stage timings. The field-level coefficients are simple 0/1 at depth two. |
| Interacting extension coefficients | [Operand work and denominator-one correction](sign-det-operand-work.md): depths one/two paired callbacks, all 24 observations, and current four-depth exact conformance | Real reduced/direct/reference production and replay on P=X²−g² with g involving multiple infinitesimals. Corrects repeated recursive gcd/division; retained paired medians favour the fix by 3.86/19.41. Higher-depth conformance is correctness/process context, not a scientific complexity ladder. |
| Nested supplied coefficient evidence | [Ordinary-kernel nested replay](sign-det-nested-kernel.md#recorded-costs): accepted/rejected polynomial and fraction evidence at depths one/two/three, six rotated adjacent control/proof rounds, source `6d3801053` | Actual existing arithmetic/checker reduction and standard-kernel proof builds; wall time and RSS include elaboration/import/process overhead. Depth-three acceptance costs about 108 seconds and 17.5 GiB on that source. It remains a manual target. This is consumer evidence, not a new theorem-only Sturm companion performance obligation or a general cross-level sharing claim. |

The [nested-wide archive](data/sign-det-nested-wide/219e2232cf/archive.json)
retains raw exports, source reconstruction, all 303 source hashes, executable
and harness bindings, host activity, complete schedules and original verdicts.
Its archived validator rechecks the points, medians and source reconstruction:

```sh
python3 -m scripts.bench.sign_det_nested_wide_archive \
  reports/data/sign-det-nested-wide/219e2232cf --reconstruct-source
```

The sign and kernel archives retain their own source reconstructions, hashes
and raw schedules. These observations keep their source scope: they are not
assigned to every future field dictionary or presented as current absolute
times. The newer denominator-one correction has its own controlled pairs;
no historical failed run is discarded or retrospectively passed.

The core ring-operation bound excludes coefficient-oracle costs. These
consumer measurements show why that exclusion matters, and fulfill the
integration size-axis coverage with actual executions rather than duplicate
root or field arithmetic. Full BKR algorithms, general nested-field costs,
certificate sharing, tower arithmetic and tower8 isolation retain their own
requirements under #10377/#10378. Their unfinished concerns are not attributed
to this library's generic query implementation or silently marked complete.

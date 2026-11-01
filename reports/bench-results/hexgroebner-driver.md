# Standalone finite-field F4 candidate driver

`hexgroebner_compute` reads explicit prime, variable/order and polynomial JSON,
then emits a complete reduced **unchecked candidate**, cumulative statistics,
advanced random state and candidate duration. Errors distinguish invalid input,
representation limits, exhaustion and internal matrix failures; failed responses
contain no candidate basis. Polynomial, byte, pair, round and matrix allowances
remain absolute parent budgets. Parsing and file IO are outside those allowances.
The library API retains resumable states; this driver does not serialize them.

The driver never elaborates Lean source. It uses the SDK's
`libinitialize_minimal.a`, when available, under that restriction. An SDK without
that archive falls back to ordinary initialization. `hexgroebner_compute_full`
uses ordinary initialization and the same parsing/computation/output code, giving
a reference executable for conformance and measurement. No initializer is
intercepted in either production target. Both targets build in the existing CI
job and independently pass all 567 complete corpus outputs and counters, plus
malformed input, order, zero/unit ideal, ordinary characteristic-two and resource
boundary checks.

Measured source fingerprint `e0b1cbd73ebf`, commit
`f8a9f9eddfd683062f4a110e7856f5979edb7c01`, contains the packed comparison
implementation `802ae51122d7` and adds these driver targets without changing F4.
The frozen SDK initialization archive SHA256 is
`31e5026b3d16824f7d5c5c30ce41843bf167d262a236978264d4021d1d8538a5`.
The final default and reference executable hashes, linker response files, all
input files and Git source blobs accompany the samples.

Each campaign retains 64 processes: 16 development inputs from seven families,
primes 32003 and 2147483647, adjacent AB then BA, one algorithm thread on an
automatically leased CPU. All 32 paired complete reduced bases agree in every
campaign; default/reference non-timing responses agree too. All completed
samples, failures and outliers are retained. No unchanged repeat is used.
GNU time wraps both arms identically and supplies post-exec peak RSS. Process
time includes that wrapper, launch, initialization, parsing, computation and
complete output. Certificate generation, independent final certification and
kernel checking are excluded. This is a development suite, not held-out evidence
or the fastest-open-source acceptance suite.

On CPU42, default/reference process B/A is 0.4133 (median 0.3314, range
0.1894–0.9689), or 0.4153 after equal family weighting. Peak observed child RSS
is 42512 KiB for the default and 92584 KiB for the reference. These are separate
whole-process observations; reduced startup does not imply faster F4 arithmetic.

Current msolve source is `3672113ee2c696a2ac9c637636e0f7214f500ba1`, built with
Clang 23.1.3, `-O3 -march=native`, GMP 6.3.0, MPFR 4.2.2 and FLINT 3.6.0.
The CLI and actual `libneogb` engine hashes, source archive, compiler flags and
linkage are retained. Both msolve modes request full reduced grevlex output,
one thread, matched time/address-space caps and identical input systems.
Mode 2 is exact; mode 42 uses probabilistic elimination. Its reported seeds
are retained in raw stderr; they are uncontrolled and not synchronized with Hex.
An independent polynomial parser compares complete canonical outputs.

| Family-balanced process Hex/msolve | Exact, CPU57 | Probabilistic, CPU58 |
| --- | ---: | ---: |
| All seven families | 1.2250 | 1.2422 |
| cyclic | 0.9416 | 1.0071 |
| katsura | 0.6234 | 0.7215 |
| eco | 5.2312 | 6.3882 |
| noon | 0.7519 | 0.6558 |
| reimer | 4.4011 | 4.7094 |
| minrank | 0.6092 | 0.4874 |
| dense quadratic | 0.6687 | 0.6531 |

The all-pair geometric means are 1.1853 and 1.2100, with medians 0.7600 and
0.7497 and ranges 0.2845–5.3060 and 0.4133–7.8948. Peak observed RSS is
42512/42516 KiB for Hex and 13396 KiB for msolve. Eco and Reimer remain large
performance gaps. These observations establish neither leadership nor general
coverage: wider fields, extensions, held-out inputs, parallel scaling and the
other required comparators remain outstanding.

A small JSON parse/print reproduction isolates initialization. On the pinned
Lean 4.35.0-rc3 toolchain, 24 alternating adjacent full/minimal SDK comparisons
observe a geometric mean ratio 8.2405 (20.7714 versus 2.5206 ms). The unchanged
reproduction on Lean 4.37.0-nightly-2026-10-30 observes 8.5911 (20.8497 versus
2.4269 ms), in its own 24 comparisons. These toolchains are not pooled.
`EmitC.emitInitFn` selects broad `lean_initialize` for a module using the Lean
package; narrowing JSON imports alone does not remove that initialization.
The existing SDK workaround already avoids most of this cost for a tool that
never elaborates Lean source. A reproduction and measured costs are recorded on
[Lean's initialization/linking issue](https://github.com/leanprover/lean4/issues/16082#issuecomment-6558865563).
There is no established requirement for a language change to reach F4 leadership.

The reproduction archive also retains an unsupported runtime-only initializer
interception used solely for diagnosis, never production. Its original
`wait4.ru_maxrss` values inherit a large Python-parent floor and are invalid as
child memory estimates; they remain unchanged and explicitly marked. A separate
GNU-time memory supplement and the final driver campaigns avoid that problem.
An earlier configuration experiment reused a cached Lake configuration and did
not actually produce a full-init reference. Its correction, logs and binary
hashes are retained; only the two separate final targets underlie the driver
measurements above.

Raw artifacts, each with SHA256:

- [cli-msolve-l2-production-records-e0b1cbd73ebf.tar.gz](raw/cli-msolve-l2-production-records-e0b1cbd73ebf.tar.gz):
  `e3bb337c7a8f5c09d696c1891d89f550d0a75c91be418f8e1881d9b7a718d19c`.

- [cli-msolve-l42-production-records-e0b1cbd73ebf.tar.gz](raw/cli-msolve-l42-production-records-e0b1cbd73ebf.tar.gz):
  `61565ab8707bafc182d4c4b8f07bc5fc608848a8455d5e7221c5cb7f6f95dab0`.

- [cli-production-records-e0b1cbd73ebf.tar.gz](raw/cli-production-records-e0b1cbd73ebf.tar.gz):
  `a65d57cc64763b87bc630420f06d344078c6cf8e92e49603f532f6031490e211`.

- [cli-validation-e0b1cbd73ebf.tar.gz](raw/cli-validation-e0b1cbd73ebf.tar.gz):
  `828c69090cd41c2c80efc92c4a53d2ace8e56fd787e95277baf4a026ccb21414`.

- [cli-initialization-reproduction.tar.gz](raw/cli-initialization-reproduction.tar.gz):
  `1ac1594828c6426d6a359b5c603a49afdedcc82f0ca842bda2dceaf1c5050991`.

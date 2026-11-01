# Standalone finite-field F4 candidate driver

`hexgroebner_compute` reads explicit prime, variable/order and polynomial JSON,
then emits a complete reduced **unchecked candidate**, cumulative statistics,
unchanged deterministic random state zero and candidate duration. Invalid input,
representation limits, exhaustion and internal matrix failures are distinct;
failed responses contain no candidate basis. Parent allowances cover computation;
parsing and file IO are outside them. The library API retains resumable states.

This bench-tree driver never elaborates Lean source or invokes its interpreter.
It uses the SDK's internal minimal-initialization archive only for compiler
revision `470d5ce1400764999581fd26d5d72b00d990b0f4`, when present. Other revisions
and missing archives use ordinary initialization. Its import closure must also
initialize modules reachable through extern/export calls. The full reference
uses identical parsing/computation/output code with ordinary initialization.
CI checks the linked initializer, complete non-timing response equality and
independent corpus outputs. No production initializer is intercepted.

Current source fingerprint `1bc68da7b1c1` and its archived source manifest identify
this implementation and measurement runner. The computational F4 sources remain
those of packed-comparison fingerprint `802ae51122d7`. Both driver executables
are byte-identical to those of `b42ce333603b`; the runner changes how msolve is
launched and strengthens provenance/input checks. Source blobs, executable
hashes, helper hashes, linker responses, compiler flags and child environment
settings are retained. Source and binary hashes are checked before and after
measurement. The SDK archive SHA256 is
`31e5026b3d16824f7d5c5c30ce41843bf167d262a236978264d4021d1d8538a5`.

Each full campaign retains 64 processes: 16 development inputs from seven
families, primes 32003 and 2147483647, adjacent AB then BA, one algorithm thread
on an automatically leased CPU. Every campaign jointly solves 32/32 pairs,
with 64/64 successful process exits, zero timeouts/failures and all 32 complete
reduced bases agreeing. Full/default non-timing responses agree too. No unchanged
repeat is used. All completed samples and outliers remain included.

GNU time wraps both arms identically, supplying post-exec peak RSS. Process
time includes that wrapper, launch, initialization, parsing, computation and
complete output. Certificate generation, independent final certification and
kernel checking are excluded. This is a development suite, with no held-out or
fastest-open-source acceptance claim. The shared host is an AMD EPYC 9455;
Hex dispatches exact AVX2 kernels with portable fallbacks. Generated C uses the
pinned Lean SDK; FFI uses Clang 23.1.3. ISA availability and toolchain context are
retained, without filtering host activity.

On CPU95, default/full process B/A is 0.4145 (A full, B default; below one favors
default), median 0.3338, range 0.2096–0.9646, or 0.4167 with equal family weights.
Peak observed RSS is 42348 KiB default and 92652 KiB full. Reduced initialization
cost does not imply faster F4 arithmetic.

msolve source is `3672113ee2c696a2ac9c637636e0f7214f500ba1`, built with Clang
23.1.3, `-O3 -march=native`, GMP 6.3.0, MPFR 4.2.2 and FLINT 3.6.0. Both modes
execute `.libs/msolve` directly, with its neogb library directory explicitly
recorded in `LD_LIBRARY_PATH`. The ELF and actual engine hashes are retained.
Mode 2 is exact; mode 42 uses probabilistic elimination, with uncontrolled seeds
retained in stderr. Both request full reduced grevlex output, one thread and
matched time/address-space caps. The runner independently checks characteristic,
variable order and canonical input generators across JSON and msolve files,
requires grevlex, and parses every complete output.

| Unadjusted process Hex/msolve | Exact, CPU9 | Probabilistic, CPU10 |
| --- | ---: | ---: |
| Equal-family geometric mean | 2.1093 | 2.4298 |
| cyclic | 1.8649 | 2.2553 |
| katsura | 1.3733 | 1.4997 |
| eco | 5.5003 | 7.1041 |
| noon | 1.2549 | 1.2618 |
| reimer | 8.1418 | 8.5310 |
| minrank | 0.9477 | 1.0360 |
| dense quadratic | 1.3619 | 1.8658 |

All-pair geometric means are 2.0771 and 2.4072; medians 1.5315 and 1.6441;
ranges 0.4646–8.5504 and 0.7406–9.1065. Peak RSS is 42288/42348 KiB for Hex and
13392 KiB for msolve. Eco and Reimer remain substantial gaps. Wider fields,
extensions, parallel scaling, held-out inputs and the other required comparators
remain outstanding. These measurements do not establish leadership.

A separate diagnostic uses the one-variable system `[x0]` at both primes, with
adjacent AB then BA on CPU92: eight successful processes, four agreeing pairs,
no failures. Hex process time ranges 3.2521–5.3046 ms (geometric mean 4.4413),
msolve 3.9604–11.1440 ms (5.3172). Every sample, including the 11.1440 ms
observation, is retained. This quantifies substantial fixed costs in small
cases. All reported ratios remain unadjusted; small-case process ratios are not
interpreted as arithmetic speed ratios. This is a one-off diagnostic, with no
per-change null-control requirement or sample-filtering rule.

Earlier snapshots `e0b1cbd73ebf` and `b42ce333603b` retain separate complete
campaigns and source manifests. Their msolve arms executed a libtool shell
wrapper that added overhead only to msolve, biasing Hex/msolve ratios in favor
of Hex. Their equal-family ratios 1.2250/1.2422 and 1.2526/1.2807 are retained
historical observations and are superseded by the direct-ELF table above.
They are not pooled or used as evidence of a smaller comparator gap. Their
initialization-only default/full observations, 0.4133 and 0.4293 respectively,
remain separate from the current 0.4145. The older protocol arm labels were
inherited from an exact-comparator suite; the current runner records each mode
and both named-manifest and executed-arm hashes explicitly.

A JSON parse/print reproduction isolates initialization. Twenty-four alternating
adjacent full/minimal comparisons on pinned Lean 4.35.0-rc3 observe a geometric
mean ratio 8.2405 (20.7714/2.5206 ms). The unchanged reproduction on Lean
4.37.0-nightly-2026-10-30 observes 8.5911 (20.8497/2.4269 ms), in its own
24 comparisons. These toolchains are not pooled; the nightly is diagnostic.
The pinned compiler's broad `lean_initialize` choice and existing internal SDK
workaround are recorded on
[Lean's initialization/linking issue](https://github.com/leanprover/lean4/issues/16082#issuecomment-6558865563).
No requirement for a language change to reach F4 leadership is established.

The reproduction retains an unsupported initializer interception used solely for
diagnosis, never production. Original reproduction `wait4.ru_maxrss` readings
inherit a Python-parent floor and are invalid child-memory estimates; they are
retained and marked. A separate GNU-time supplement and the driver campaigns
avoid that problem. An earlier cached Lake configuration did not actually select
full initialization; its correction and logs are retained. All driver timing
campaigns above use the two separate final targets.

[`groebner_cli_measure.py`](../../scripts/bench/groebner_cli_measure.py) retains
all inputs/results and rejects stale sources, changed executables, failures or
mismatches. Both final drivers pass the 567-case corpus, ten default fixture
counters, batch metadata and three serial-batch counters, plus boundary/error
response agreement. The oracle runner builds both itself. A deliberate
full-init/default swap is rejected by the committed initializer checker.

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

- [cli-reviewed-msolve-l2-production-records-b42ce333603b.tar.gz](raw/cli-reviewed-msolve-l2-production-records-b42ce333603b.tar.gz):
  `ccea5488e66bdb4482d6907ecc40ea87bf6b90e823995d2a0b6a0b2569691d1f`.

- [cli-reviewed-msolve-l42-production-records-b42ce333603b.tar.gz](raw/cli-reviewed-msolve-l42-production-records-b42ce333603b.tar.gz):
  `5347ebd171a9853f93d9b6e2e751e3a328be34c69c88abffb05d8ba61a4bf4ad`.

- [cli-reviewed-production-records-b42ce333603b.tar.gz](raw/cli-reviewed-production-records-b42ce333603b.tar.gz):
  `764f8799df9b24aec9b991ac76628aa98e3880ef45427f8441e5f72d8e90b87e`.

- [cli-reviewed-validation-b42ce333603b.tar.gz](raw/cli-reviewed-validation-b42ce333603b.tar.gz):
  `c852f999c2966e632d8106047dfaa63fc94d5765fd4e8bf95e63f1a1731571db`.

- [cli-direct-msolve-l2-production-records-1bc68da7b1c1.tar.gz](raw/cli-direct-msolve-l2-production-records-1bc68da7b1c1.tar.gz):
  `ec6205e7cac3ef4aaae3f0785b509cc6705c2bd40643ba5cfebd22ea27ffcb9f`.

- [cli-direct-msolve-l42-production-records-1bc68da7b1c1.tar.gz](raw/cli-direct-msolve-l42-production-records-1bc68da7b1c1.tar.gz):
  `124ca42f7840263d81e8ee9cf724b91bcab2d6ddb6c643b14ca3643dd42fa3cc`.

- [cli-direct-production-records-1bc68da7b1c1.tar.gz](raw/cli-direct-production-records-1bc68da7b1c1.tar.gz):
  `8a498a15c0ab4661d84752dd23f1a17ff975c60bccc82cbb91a4db5f65f25fb3`.

- [cli-startup-diagnostic-records-1bc68da7b1c1.tar.gz](raw/cli-startup-diagnostic-records-1bc68da7b1c1.tar.gz):
  `cd47a9dffaa68272ad4d2c7315452b2044a161e8009dab1e92f4568c03d8fce3`.

- [cli-direct-validation-1bc68da7b1c1.tar.gz](raw/cli-direct-validation-1bc68da7b1c1.tar.gz):
  `c8f279f26d5855917b2a95cbd5a7eabbd3ed48322e03e4754cef0f7b6e2799fe`.

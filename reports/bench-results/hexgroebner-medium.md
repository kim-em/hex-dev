# Finite-field F4 medium development comparisons

Hex remains slower than several comparators on this medium development suite.
The measurements identify remaining work; they do not meet the SPEC's
fastest-open-source milestone or establish a compiler/runtime impossibility.

The suite fixes 14 grevlex systems: cyclic7, Katsura8, Eco11, Noon5, Reimer6,
MinRank and dense quadratic6 at primes 32003 and 2147483647. Structured inputs
come from public GamBa source `f18c2db3a288f20f63f752b44e0171cf1cb86163`;
variable names are normalized and coefficients reduced in the explicit field.
The dense inputs use seed 10987 and the same signed integer coefficients in
both fields. Builders, canonical input JSON, comparator input text, source
excerpts and their GPLv3 license are retained. This fixed balanced development
corpus is not held out and is not the SPEC's acceptance suite.

Hex scheduling source `0cb80bf73a4a` and earlier oracle source `6ede9cb261a4`
have byte-identical frozen default executables, SHA256
`2ece3bf2646f90393331ce349043b8a19adb02d236ee1bf300337ceaf9e9bd67`.
They use default total-degree scheduling and produce complete monic reduced
bases. Their manifests and exact Git source blobs are retained separately in
all capsules; no timings from different executable sources are pooled.

Each comparator observation uses adjacent AB then BA per case, one requested
algorithm thread and one automatically leased CPU on the shared EPYC 9455
host. CPUs are 34/33 for msolve modes 2/42, 88 for GamBa, 7 for Giac and 22
for Julia. Placement is not isolation; observations may overlap on distinct
leased CPUs. Each has one initial campaign, no unchanged repeat. Every
completed sample, failure, timeout, raw full output, diagnostic and host-load
context is retained. The protocol allows 60 seconds, 16 GiB address space
and 64 MiB output per process. All 140 complete basis pairs agree with zero
failures or timeouts; every observation has 56 successful measured processes.
Julia's additional first-call bases agree too.

Whole-process comparisons use identical GNU-time wrappers and include launch,
initialization, parsing, complete reduced-basis output and diagnostics. Child
peak RSS is measured after exec. Candidate production, certificate generation,
independent final certification and kernel checking are distinct; these data
exclude the latter three stages. No production route wraps another F4 engine.

| Whole process, Hex/comparator | Equal-family mean | Median | Range | Peak RSS Hex/comparator KiB |
| --- | ---: | ---: | --- | ---: |
| msolve mode 2 | 2.5112 | 2.7627 | 0.7687–6.5250 | 97920/20312 |
| msolve mode 42 | 2.6749 | 2.7018 | 0.7720–7.1439 | 97732/20312 |
| GamBa v0.3 AVX512 | 1.3017 | 0.9875 | 0.1571–7.6095 | 97376/34348 |
| Giac 2.0.0-19 | 1.3021 | 1.5550 | 0.3137–2.1734 | 91036/90516 |

msolve is source `3672113ee2c696a2ac9c637636e0f7214f500ba1`, built with
Clang 23.1.3, `-O3 -march=native`, effective `znver5` recorded in its engine
ELF, GMP 6.3.0, MPFR 4.2.2 and FLINT 3.6.0. The build explicitly sets
`NIX_ENFORCE_NO_NATIVE=0`; the direct `.libs/msolve` ELF uses its retained
neogb library path. Configure cannot find `omp.h`; both arms request one
algorithm thread. Modes 2 and 42 request full reduced grevlex output; mode-42
uncontrolled seeds and all diagnostics remain in the observation. Public
source, build scripts, flags, ELF compile-command evidence and hashes are
retained. Historical libtool-wrapper timings and stripped native flags are
not used here.

GamBa is the official Linux AVX512 v0.3.0 release with seed 42 and one thread.
The release archive digest is
`fec73f3f800fe1f39d87e545ccf055c2cb9a45422c2f33448a501531adfa2174`.
Release metadata and measured executable hashes are retained. Its README
states that parts remain closed source and a source build is unavailable;
this comparator is not classified as fully open source. No executable is
redistributed. The process ratio is below one on four of seven families and
the median is 0.9875. Fixed startup can dominate these smaller cases; no
per-family algorithmic superiority is inferred from this single campaign.

Giac is the packaged 2.0.0-19 binary, with binary and engine hashes retained.
Upstream currency, build flags and native tuning are not established. The
helper calls `threads(1)`, checks the subsequent `threads()` response as one,
and requests `gbasis` over the explicit modular domain with `revlex` order.
Complete output is checked. No unsupported claim about deterministic or
probabilistic internal elimination is made.

Groebner.jl is version 0.10.12, source
`751c90b0dd9415bab2b56980b0b34b59497ff856`, running Julia 1.13.2 with
Nemo 0.57.1 and AbstractAlgebra 0.51.3. The complete package manifest, public
source archive and driver are retained. Each Julia process computes the same
input twice using deterministic linear algebra, `tasks=1`, seed 42 and reduced
grevlex output. Both first-call and second-call timings and complete bases
are retained. Julia and BLAS thread counts are one.

The Julia ratio compares Hex's internal candidate interval with Julia's
second call, including file reading and Nemo polynomial construction through
F4/interreduction. Hex's interval starts after JSON parsing and includes
canonical packing. These boundaries differ: Julia includes text parsing and BigInt-based term
construction while Hex excludes JSON parsing, biasing this ratio in Hex's
favour. Julia's first call also includes JIT work. Its process duration includes both computations plus JIT, so no
matched whole-process ratio is claimed. Peak Julia RSS includes compilation.

The Hex candidate/Julia second-call mean is 5.3322,
median 4.8317, range 1.2631–42.3179. Peak RSS is
92972/742660 KiB. This is an informative development comparison,
not an acceptance ranking across equivalent timing boundaries.

| Family | msolve 2 process | msolve 42 process | GamBa process | Giac process | Julia second call, distinct boundary |
| --- | ---: | ---: | ---: | ---: | ---: |
| cyclic | 4.8141 | 5.2457 | 3.7245 | 1.9907 | 4.8338 |
| kat | 2.8491 | 3.0782 | 0.8448 | 1.3466 | 5.8518 |
| eco | 2.8029 | 4.3713 | 6.5843 | 1.5553 | 2.3872 |
| noon | 1.9067 | 1.9451 | 0.7373 | 1.1903 | 12.3977 |
| reimer | 4.0639 | 4.4354 | 3.7873 | 1.3735 | 4.4745 |
| minrank | 1.1529 | 1.0398 | 0.3725 | 0.7781 | 3.5574 |
| dense-quadratic | 1.8335 | 1.5474 | 0.2939 | 1.1967 | 9.1971 |

An explanatory cyclic7 profile on CPU 7 samples eight Hex calls at 1999 Hz, with 6421
user-cycle samples and zero lost samples. All eight complete outputs and
non-timing counters agree. Flat shares include native M31 row scanning 15.23%,
monomial combination 10.17%, reference decrement 9.50%, object free 9.14%,
allocation 7.29%, allocator free 3.47%, monomial preparation 3.62%, packed
64-bit reading 2.49% and symbolic preprocessing 2.15%. Raw perf data and
symbols are retained. Its source is bound by an archived fallback manifest
identical to the GamBa capsule's manifest and measured Hex binary. CPU 7 also
served the Giac observation; placement does not establish non-overlap, and no
isolation or causal attribution is inferred. These whole-process samples include profiler overhead;
they motivate algorithm, allocation and representation work without assigning
a causal timing cost or proving a compiler limit.

Remaining acceptance work includes matched parallel sweeps, a current tuned
Giac comparison, Singular timing, other faster open-source contenders,
additional field widths and extension fields, hard/held-out suites, solved
coverage and family-balanced acceptance, plus separate certificate/native
verification/kernel-checking measurements. The issue remains open.

- [medium-msolve-l2-6ede9cb261a4.tar.gz](raw/medium-msolve-l2-6ede9cb261a4.tar.gz): `9ba11c64067d0b36ede2fc0b6a1ff16942c1345451ea6f93942197178b404756`.
- [medium-msolve-l42-6ede9cb261a4.tar.gz](raw/medium-msolve-l42-6ede9cb261a4.tar.gz): `fb0ad820894376fbd3fc48bcd72c7122dbfab5d7c92eec2c8af7399c0dd40841`.
- [medium-gamba-v03-avx512-first.tar.gz](raw/medium-gamba-v03-avx512-first.tar.gz): `29681a004fc6381cd0c0f710a7dd41d0b731af9cee69dba9c8588b70a6c1c0cd`.
- [medium-groebner-jl-v01012-deterministic-first.tar.gz](raw/medium-groebner-jl-v01012-deterministic-first.tar.gz): `ca13b8d03e7fa7f73eee2ce957599a7e53d31e1f4021f5d1f6f1a664afefce34`.
- [medium-giac-v20019-first.tar.gz](raw/medium-giac-v20019-first.tar.gz): `6e52e571490b7f5949db9d8006a86b9369e960fd5eab7f65d73f32860df61e91`.
- [medium-profile-cyclic7-degree.tar.gz](raw/medium-profile-cyclic7-degree.tar.gz): `ca04092e2464a40d3161516213ecafa836e832dbc3a12ac56103920c1124ddb0`.

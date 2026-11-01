# Packed reducer lookup and sparse-first F4 targets

The implementation combines bounded packed reducer lookup with stable
sparse-first ordering of joint Macaulay target rows. It preserves sugar pair
selection, known reducer pivots and original order among equal-sized targets.
Independent normal forms retain input order. Traced production moves every
source derivation root with its polynomial. Sorting work and packed-index
preparation charge their parent allowances before performing the work.

Read-only native trie calls admit at most 2048 nodes and 2047 edges, arity 4096,
and 4095 charged node/edge visits. The portable packed model and original node
traversal check exact results and exhausted prefixes. Larger or incompatible
indices and insufficient preparation allowances retain ordinary traversal.
This operation changes representation and lookup cost; target ordering changes
the algebraic work performed. Neither operation changes the mathematical output
contract. Completed checked results still require independent certification.

Source fingerprint `a00d1a3e57a9`, commit
`6093fec33797f41da5631db115b4e0cf49a6aacb`, identifies the measured combined
implementation and runner. A fresh detached 188-job build freezes both CLI
targets and checks their actual initialization linkage. The measured baseline is
standalone-driver fingerprint `17aa8e10ff23`, executable SHA256
`604abe19262994f76561ccc9e1479a9028ef072d8e18c8844724ec033141c17f`.
The new executable SHA256 is
`45f484e74ab091f80595314642bcea2afd487d151a79bef8987425c26114a33b`.
Each source manifest, exact Git blob, executable/helper hash and input is retained.
The before/after mode checks the baseline against its separate frozen manifest,
requires complete reduced bases and all computation metadata to agree, and
allows algorithm statistics to differ. A negative hash probe rejects a modified
baseline manifest before any measured process is launched.

Each campaign uses 16 development inputs from seven families at primes 32003
and 2147483647, one algorithm thread and an automatically leased CPU. Arms are
adjacent AB then BA. The first observation and single permitted unchanged repeat
are both retained: before/after CPU89/42, exact msolve CPU90/39, probabilistic
msolve CPU91/41. The three campaign types run concurrently on distinct leased
CPUs of the shared AMD EPYC 9455 host; this is placement, not isolation. No
host-activity or outlier filter is applied. No further unchanged repeat is used.
Every one of the six campaigns solves all 32 pairs with full reduced bases
agreeing, 64/64 successful processes, zero failures and zero timeouts.

Candidate time includes canonicalization, F4 and final interreduction. Whole
process time also includes launch, initialization, parsing, complete output and
identical GNU-time wrappers; RSS is measured after exec. Certificate generation,
independent final certification and kernel checking are excluded from timings.
The corpus, field widths and held-out coverage do not establish the SPEC's
fastest-open-source milestone. Wider fields, extensions, parallel scaling,
remaining comparators and deterministic producer proofs remain outstanding.

| Before/after observation | Candidate B/A | Whole process B/A |
| --- | ---: | ---: |
| CPU89 | 0.8340 | 0.9175 |
| CPU42 | 0.8572 | 0.9236 |
| Pooled 64 pairs | 0.8455 | 0.9205 |
| Pooled median | 0.9439 | 0.9688 |
| Pooled range | 0.4233–1.3629 | 0.4253–1.8254 |

Equal-family process ratio is 0.9180. Arithmetic improvements do not imply a
uniform process-time gain: Katsura and dense-quadratic process observations
regress despite lower candidate means. Every such sample remains included.
Peak before/after post-exec RSS is 42236/42208 KiB. Exact/probabilistic
comparator sweeps peak at 42208/42212 KiB Hex and 13360 KiB msolve.
Exact per-input durations are retained in each capsule.

| Family | Candidate B/A | Whole process B/A | Hex/msolve exact | Hex/msolve probabilistic |
| --- | ---: | ---: | ---: | ---: |
| cyclic | 0.9344 | 0.9381 | 2.6388 | 2.7498 |
| kat | 0.9486 | 1.2723 | 2.8706 | 2.8696 |
| eco | 0.8055 | 0.8133 | 4.9434 | 6.1495 |
| noon | 0.8289 | 0.9641 | 1.2429 | 1.1436 |
| reimer | 0.5050 | 0.5785 | 5.7694 | 4.6460 |
| minrank | 0.9622 | 0.9884 | 2.2173 | 1.9243 |
| dense-quadratic | 0.9722 | 1.0271 | 2.5613 | 2.5647 |

Current msolve is source `3672113ee2c696a2ac9c637636e0f7214f500ba1`,
Clang 23.1.3 with effective `-O3 -march=native` recorded in the engine ELF.
Its configure probe lacks `omp.h`; both arms request one algorithm thread.
The direct `.libs/msolve` ELF uses the recorded neogb library path. Modes 2/42
request full reduced grevlex output; `-v 2` diagnostics and uncontrolled mode-42
seeds remain in stderr and process time. Engine hashes and build inputs are
checked before/after. GMP, MPFR and FLINT versions are 6.3.0, 4.2.2 and 3.6.0.
These are the same native-tuned engine files as the preceding driver campaigns.

| Comparator observation | Exact Hex/msolve | Probabilistic Hex/msolve |
| --- | ---: | ---: |
| First equal-family mean | 2.7111 | 2.8377 |
| Repeat equal-family mean | 2.9947 | 2.7168 |
| Pooled equal-family mean | 2.8494 | 2.7766 |
| Pooled all-pair mean | 2.8221 | 2.7733 |
| Pooled median | 2.8109 | 2.7870 |
| Pooled range | 0.8369–6.9892 | 0.6893–7.9471 |

The earlier driver's 2.1939/2.3790 observations are separate snapshots and host
contexts, not an adjacent comparison with this implementation. They are not
pooled with these campaigns. The direct before/after measurements above supply
the implementation comparison. A change in ratios across distinct comparator
campaigns cannot be attributed entirely to code. Small-case durations are
substantial fixed costs; the complete raw durations and variation remain
available. The current comparator gaps remain large and do not demonstrate
leadership or an impossibility requiring compiler changes.

At the large prime, Reimer matrix entries fall 960252→435489 and rounds 26→19;
Eco entries fall 3268590→2939286. The sparse-first component alone has separate
128-process and 240-point fixed-case evidence, with Reimer fixed ratio 0.5361.
The original component prototype reordered independent normal forms too and
failed its first complete-basis comparison; its two completed processes and
exact source are retained separately in the component capsule. It is never
pooled with corrected measurements. Earlier packed-trie observations and guard
checks remain in [their own report](hexgroebner-trie.md).

The combined implementation passes all 1956 relevant conformance/theory targets,
both 567-case CLI output/counter comparisons, 175 independent matrix cases,
567 complete SymPy/Singular bases and 1288 division cases. Four Clang and four
GCC ASan/UBSan variants pass, including maximum read-only guard-page probes.
Native counts include 2246 trie calls, two deliberate malformed-arena declines
and 484 F4 calls without decline. A dedicated 78-pair system checks actual
batching above 64; improved Reimer now has largest batch 61 and identical
statistics with caps 64 and 1024. A distinct regression checks positional
independent normal forms. Dependency, phase, release-manifest, copyright,
file-size and 32-check benchmark-verification gates pass.

An explanatory Eco31 profile retains eight complete runs whose bases and
counters all agree with the campaign. It records 8493 samples at 1999 Hz with
zero lost samples. Flat sampled shares include Mersenne row scanning 17.42%,
monomial combination and its loop 6.09%, geometry checks 3.02%, matrix validation
2.37%, symbolic row translation 1.87% and native reducer lookup 1.72%.
Reference-count release, small-object allocation and free together account for
10.71%. These whole-process shares include profiler overhead; they are not
uninstrumented timing estimates. Kernel symbols are unresolved and some unwind
chains are unreliable, so only flat leaf-IP symbols are interpreted. Every raw
sample and full output is retained. This motivates investigating matrix and
representation overhead alongside arithmetic; it does not establish a compiler
limitation or replace the matched measurements.

- [combined-before-after-a00d1a3e57a9.tar.gz](raw/combined-before-after-a00d1a3e57a9.tar.gz): `db6d788f85ad37e0d0e3967143fddb023b1df57c1c1353924f32a0fa0e5c6701`.
- [combined-before-after-repeat-a00d1a3e57a9.tar.gz](raw/combined-before-after-repeat-a00d1a3e57a9.tar.gz): `8e766493dd6b4a7072ea776ad6383c1a3aede9ea1b3a0218f76cac53886172a0`.
- [combined-msolve-l2-a00d1a3e57a9.tar.gz](raw/combined-msolve-l2-a00d1a3e57a9.tar.gz): `30a7dd7c89e30dc82c803de1a4e5e613fbe0336c5ab521884b9ae11f15b8c8f5`.
- [combined-msolve-l2-repeat-a00d1a3e57a9.tar.gz](raw/combined-msolve-l2-repeat-a00d1a3e57a9.tar.gz): `820888332743072a12043881b37141ac5c44ff1bd425d2ded2e71d7f620d4e54`.
- [combined-msolve-l42-a00d1a3e57a9.tar.gz](raw/combined-msolve-l42-a00d1a3e57a9.tar.gz): `fa16764e07f30a21d9653ddb4c08cf19bd99376913f834b040049ab37df57ece`.
- [combined-msolve-l42-repeat-a00d1a3e57a9.tar.gz](raw/combined-msolve-l42-repeat-a00d1a3e57a9.tar.gz): `3598fc8b32bd8f5617a6dcb08384f2e0cf7ae0ce2f1d55843da4b255ccacd569`.
- [combined-validation-a00d1a3e57a9.tar.gz](raw/combined-validation-a00d1a3e57a9.tar.gz): `68ae47af6f8f03089d13ea80cd5cd65c360e11b8570dee7a11f02f9cb8089f26`.
- [combined-profile-eco-a00d1a3e57a9.tar.gz](raw/combined-profile-eco-a00d1a3e57a9.tar.gz): `9e847c241e255248b0cceb720721b2a6cbc99b9e417d8e6dd251dcc40419866d`.

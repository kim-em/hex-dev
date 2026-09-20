# Certificate language comparison

Hex retains its certificate representation and adds `primality? using expression`.
The expression is a closed Lean producer of `Hex.Nat.PrimeCert`; evaluation and
macros are untrusted, and the output is the existing literal checked by
`prime_of_checkPrimeAt`. The design decision, correspondence limits, extension
soundness, and compatibility policy are in the
[primality SPEC](../HexPrimality/SPEC/hex-primality.md#certificate-language-and-extension-policy).
No generated certificate migration is required.

## Prototypes and imports

The Hex prototype in `conformance/HexPrimality/CertificateProducer.lean` defines
an imported Fermat candidate producer and registers ordinary Lean macros for
Fermat candidates and a positive-exponent Pocklington form. The construction
conformance module invokes them explicitly through `using`. It also supplies
Curve25519 using named intermediate certificates. The macros are examples, not
new core syntax commitments; an implicit producer registry is unnecessary for
this extension model.

The same conformance module pins exact `Try this:` output, malformed-result
errors, and print/parse/elaborate/print stability. The original Curve25519
suggestion and the supplied route have the same 795-byte text, including the
indentation retained in the guard. `Curve25519Replay.lean` pastes that suggestion
and the 17 and 197 examples with only `import HexPrimality.Cert`. It also proves
100003 with a short Pocklington subtree, where `.small 100003` is rejected.
The companion has its own guarded suggestion using `natPrime_of_checkPrimeAt`.

The PrimeCert prototypes target upstream commit
`0803c2f6bd289c09704c7d352bb8fcf770cbb9b2`, Lean 4.33.0, with its pinned Mathlib;
Hex uses Lean 4.34.0. Their sources are under
`scripts/bench/certificate_language/` and their validation record is
[`hex-primality-language-prototypes.json`](bench-results/hex-primality-language-prototypes.json).
They establish:

- An externally registered method can supply a proved `Nat.Prime 17` through
  `prime_cert%`; it need not produce any Hex data.
- Repeated factors and zero exponents are legal PrimeCert Pocklington source.
  Hex's canonical form instead combines the four factors of 2 into exponent
  four (stored as three) and omits the zero power.
- Dictionary entries reuse intermediate primality proofs. Hex can name the
  same intermediate data with ordinary lets; literal reification expands it.
- The divisor-sieve proof for 197 with `F = 4` works through PrimeCert's theorem
  API. Its pinned `pock3` grammar requires an odd-factor tail, so this case
  cannot use that grammar directly.
- PrimeCert accepts the supplied bound 65 at 9223372036904058881; Hex rejects
  bounds above 64. This prime already has a Hex certificate with bound four:
  the difference is accepted witnesses, not an unprovable primality statement.
- PrimeCert's built-in sieve proves 100003 directly. Hex's table stops below
  100000, so its corresponding standalone data uses the Pocklington subtree.
- The malformed proof of 15 is rejected by a kernel application-type error.
  Its metaprogram initially returns an expression, so a tactic-level
  `fail_if_success` is not the right way to test this rejection.

PrimeCert's language needs Mathlib and Qq. Its method-specific theorem
applications remain in the proof and must be imported on replay. `small` and
`pock` work with `PrimeCert`; the measured Curve25519 ladder additionally imports
`PrimeCert.SieveBase` and `PrimeCert.Meta.SieveLookup`. The Hex elaboration route
imports `HexPrimality.Elab`, including construction code and Lean's metaprogramming
API, but its suggested literal needs only the Mathlib-free checker module.

## Measurements

All 40 fresh-module samples, 40 corresponding direct-kernel samples, eight
native samples, sources, toolchains, output sizes, and host-load observations
are retained in
[`hex-primality-language.json`](bench-results/hex-primality-language.json).
The runner is `scripts/bench/primality_language.py`. Four trial-major blocks
reverse adjacent arms in alternate blocks, on automatically selected CPU 21.
No completed sample was discarded or repeated. The first blocks overlapped a
large monorepo build; recorded one-minute host load ranged from 72 to 249.
These are observations on this host, not stable absolute costs or a claim of
an elaboration speedup. Separate Lean versions further limit cross-system
comparisons.

Fresh time is a Lake build of a fresh proof module, including imports and
elaboration. Kernel time is a separate warm `Lean.Kernel.check` of the complete
local proof against its declared type, recursively expanding local definitions
and auxiliary proofs. Imported library proofs remain dependencies. Negative
controls change the goal, the subject, and (for Hex) a witness base; all must
be rejected. Instrumentation and controls are excluded from the kernel timer
and are absent from the fresh-build measurement. All PrimeCert timing arms use
the common sieve-enabled import bundle, even for the smaller examples; those
fresh times do not measure their minimum possible import cost.

| Case / source route | Fresh build median (s) | Kernel median (ms) | Proof source (bytes) | Module olean (bytes) |
|---|---:|---:|---:|---:|
| Curve25519, `primality?` search | 4.061 | 9.445 | 13 | 4096 |
| Curve25519, existing literal | 2.815 | 12.164 | 773 | 4096 |
| Curve25519, `using` named data | 2.586 | 9.830 | 490 | 4096 |
| Curve25519, PrimeCert ladder | 4.885 | 28.092 | 410 | 5536 |
| 17, existing literal | 2.994 | 0.556 | 101 | 4040 |
| 17, `using` named data | 2.767 | 0.413 | 89 | 4040 |
| 17, PrimeCert ladder | 3.912 | 0.246 | 42 | 4160 |
| 197, existing literal | 1.917 | 0.900 | 116 | 4040 |
| 197, `using` named data | 3.044 | 1.062 | 100 | 4040 |
| 197, PrimeCert theorem | 4.034 | 0.424 | 65 | 4160 |

Source bytes count the proof expression, including its formatting, but exclude
the theorem header and imports. The 13-byte search invocation contains no
certificate. Olean sizes are whole-module artifacts, not serialized proof or
certificate sizes. Within each Hex case the supplied data is the same data as
the literal arm; search also finds that exact Curve25519 certificate. Different
source routes produce equivalent checker obligations, and no checker algorithm
or representation changed. Noise accounts for variation in the identical
Curve25519 obligations; in particular, these results do not establish a kernel
speedup from adding `using`.

The native executable uses an IO reference around the input and result to keep
the compiler from removing measured calls. Construction includes search and
its final self-check; supplied-data timing retrieves the precompiled literal
and runs its checker. It excludes parsing, process startup, printing, and the
elaborator's reification. It does not measure allocating a new certificate
from a serialized stream. Both arms return exactly the same certificate.

| Native Curve25519 operation | Samples (ms) | Median (ms) |
|---|---|---:|
| Existing bounded construction | 1064.583, 445.577, 417.849, 417.692 | 431.713 |
| Retrieve and check supplied data | 1.054, 0.604, 0.551, 0.552 | 0.578 |

This quantifies the work avoided by providing already constructed data. The
ordinary construction algorithm has not become faster. The result supports an
explicit producer route and unchanged replay representation; it supplies no
reason to replace the checker with an extensible interpreter or adopt a DAG.
Large shared proof graphs remain a separate workload, not a claimed performance
result of these three cases.

## Reproduction

Build `hexprimality_policy_probe` with Lake in Hex. In a separate PrimeCert
checkout at the pinned commit, build `PrimeCert` and install the prototype files:

```bash
mkdir -p /path/to/PrimeCert/PrimeCert/Comparator
cp scripts/bench/certificate_language/Extension.lean /path/to/PrimeCert/PrimeCert/Comparator/LanguageExtension.lean
cp scripts/bench/certificate_language/Cases.lean /path/to/PrimeCert/PrimeCert/Comparator/LanguageCases.lean
cp scripts/bench/certificate_language/Curve25519.lean /path/to/PrimeCert/PrimeCert/Comparator/LanguageCurve.lean
cp scripts/bench/certificate_language/Rejected.lean /path/to/PrimeCert/PrimeCert/Comparator/LanguageRejected.lean
```

In that checkout, `lake build +PrimeCert.Comparator.LanguageCases
+PrimeCert.Comparator.LanguageCurve` must succeed; the separate
`lake build +PrimeCert.Comparator.LanguageRejected` must fail with the recorded
kernel diagnostic. From Hex, run:

```bash
lake build hexprimality_policy_probe
python3 scripts/bench/primality_language.py --primecert-checkout /path/to/PrimeCert --output /tmp/language.json
lake build HexPrimality.ConstructionConformance HexPrimalityMathlib.Conformance
```

The runner refuses to overwrite its output or an existing measurement module.
Use isolated dependency checkouts when other worktrees may change package pins.

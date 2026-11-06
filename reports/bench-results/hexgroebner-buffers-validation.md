# Sparse matrix buffers: verification

The source snapshot below verifies the current benchmark and selftests while retaining the system measurements in [the measured snapshot](hexgroebner-buffers.md). Both computation drivers have the exact recorded producer hashes; the benchmark now throws on invalid results and checks wide native/reference agreement and rejection propagation during initialization. Its changed executable has no comparative timing claim.

Source commit: `f89fefb5acc7b12b50574b311d894468df00e911`. Runtime fingerprint: `5f0f9c0db129`. Verification-source SHA-256: `8d8cb87646738e47e57405ee8551a03d93063c00d5b7e8b8dedd3a7543cc2f16`.

All nine project checks and 36 strict Clang/GCC sanitizer configurations pass. Each compiler executes 327,680 index-load boundary cases in each explicitly labelled native and bytewise mode, calling the production helper with unaligned loads ending at heap allocation boundaries. All 85 frozen benchmark verifications pass. The capsule retains every source, generated profile, receipt and compiler wrapper/configuration input needed for these checks.

A separate fresh build of the measured producer snapshot, with both external compiler inputs retained, reproduces all three recorded executable hashes. The current producer configuration and executable hashes agree with that snapshot. These are recorded build results, distinct from the kernel replay and axiom audits exercised by the project checks.

[Verification capsule](raw/f4-buffer-validation-5f0f9c0db129.tar.xz) SHA-256: `247fec58ff7f16797b82f7c4323318a195b30f85a643c212b70ea8aca000722e` (1,072,268 bytes).

Run the source-bound verification manually from a checkout matching this snapshot:

```sh
python3 scripts/bench/groebner_buffers_report.py \
  --archive reports/bench-results/raw/f4-sparse-buffers-45745225e6b0.tar.xz \
  --heldout reports/bench-results/raw/f4-buffer-heldout-45745225e6b0.parts.json \
  --validation reports/bench-results/raw/f4-buffer-validation-5f0f9c0db129.tar.xz \
  --report reports/bench-results/hexgroebner-buffers.md --check --current
```

The command prints the validation capsule digest and requires both runtime and verification sources to match. Subsequent runtime, test or build-configuration changes require new verification evidence for this command. CI replays the historical measurements without pinning future unrelated changes to this source snapshot.

Candidate production, certificate generation, independent certification and kernel checking remain separate. No fastest-open-source, empirical complexity or language/runtime limitation claim follows from these verification results.

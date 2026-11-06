# Wide-prime verification capsule

The measured runtime `8b78fab53166` is unchanged. Verification source `3cc51cbe291b` adds protected-page cases with mixed corrected/uncorrected lanes and sums exactly equal to p². All nine project gates and 36 strict Clang/GCC ASan/UBSan configurations pass. The README states the independent default-on delayed AVX-512F policy; the existing sixteen-lane sparse scan remains opt-in. Historical report replay runs in the existing oracle job.

[Validation capsule](raw/f4-wide-validation-8b78fab53166-3cc51cbe291b.tar.xz): SHA-256 `75bc9b5a1e9cf45aa633a505c12fde0010a246197723ad4813311aac05edf100`, 1,077,404 bytes. It retains the identical measured producer manifest, source and compiler inputs, current verification sources, complete logs, generated strict-profile drivers and receipts. Earlier failed local verification logs are retained as separate payloads. This capsule supplies no new scientific timings.

Replay the historical measurements and current verification with:

```sh
python3 scripts/bench/groebner_scatter_report.py \
  --archive reports/bench-results/raw/f4-wide-production-8b78fab53166.parts.json \
  --heldout reports/bench-results/raw/f4-wide-heldout-8b78fab53166.parts.json \
  --validation reports/bench-results/raw/f4-wide-validation-8b78fab53166-3cc51cbe291b.tar.xz \
  --report reports/bench-results/hexgroebner-wide-prime.md --check --current
```

The command requires the exact recorded runtime and verification source listings. CI replays the historical report with `--check`; current-source binding is a separate manual verification. Candidate production, certificate generation, independent certification and kernel checking remain separate costs. No fastest-open-source or language/runtime limitation claim follows from these data.

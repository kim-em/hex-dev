# Sparse matrix buffers: functional checkpoint

Current runtime source `8dd7b08ebf35` reproduces all three executables from measured source `45745225e6b0` byte for byte. Their source differences are a checked benchmark cost-model comment and the exact pinned upstream Lake registrations for unrelated HexRCF targets. The computation and full-initialization drivers also match the preceding independently checked snapshot; the benchmark executable includes the new sparse kernels.

Both exact driver executables passed all 1,134 corpus and resource/input-boundary cases. The complete Eco-14 basis, metadata and all logical counters agree with the retained reference output. All 85 frozen benchmark verifications pass. Four Clang/GCC ASan/UBSan index-load checks each cover 327,680 aligned/unaligned boundary cases, including the bytewise fallback.

This capsule records functional evidence only. It contains no comparative timing or final 36-configuration/nine-gate receipt claim. Candidate production remains separate from certificate generation, independent certification and kernel checking. The fastest-open-source milestone and remaining issue #10987 obligations are not established.

Capsule SHA-256: `c08492f62a6f06728106980b7cafc88acc93466acd33192b21beb925674dcc14`. Source blobs, compiler and executable identities, complete outputs and functional records are replayed independently. Only this exact capsule is accepted as a functional checkpoint.

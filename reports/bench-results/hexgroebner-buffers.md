# Sparse matrix buffers: functional checkpoint

Frozen runtime `45745225e6b0` produces unchecked finite-field F4 candidates. Its computation and full-initialization drivers are byte-identical to the independently checked preceding snapshot; the benchmark executable includes the new sparse kernels.

Both exact driver executables passed all 1,134 corpus and resource/input-boundary cases. The complete Eco-14 basis, metadata and all logical counters agree with the retained reference output. All 85 frozen benchmark verifications pass. Four Clang/GCC ASan/UBSan index-load checks each cover 327,680 aligned/unaligned boundary cases, including the bytewise fallback.

This capsule records functional evidence only. It contains no comparative timing or final 36-configuration/nine-gate receipt claim. Candidate production remains separate from certificate generation, independent certification and kernel checking. The fastest-open-source milestone and remaining issue #10987 obligations are not established.

Capsule SHA-256: `5511cb5c3fc2dda7e4174963137756189528c4ef5f40c9c6dfff128fdcb75707`. Source blobs, compiler and executable identities, complete outputs and functional records are replayed independently. Only this exact capsule is accepted as a functional checkpoint.

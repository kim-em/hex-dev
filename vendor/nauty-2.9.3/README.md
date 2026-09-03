# Vendored nauty 2.9.3

The minimal subset of Brendan McKay and Adolfo Piperno's nauty 2.9.3
needed to build the `nauty-ffi` Lean package and the conformance oracle
shim: the dense-nauty core (`nauty.c`, `nautil.c`,
`naugraph.c`, `schreier.c`, `naurng.c`) with its headers, plus the
upstream `COPYRIGHT` and `LICENSE-2.0.txt` (Apache 2.0).

Provenance: `https://users.cecs.anu.edu.au/~bdm/nauty/nauty2_9_3.tar.gz`,
SHA-256
`9fc4edae04f88a0f5883985be3b39cf7f898fd6cc96e96b9ee25452743cc1b5b`,
the release pinned by
[SPEC/Libraries/hex-graph-iso.md](../../SPEC/Libraries/hex-graph-iso.md).
All files are unmodified copies from that archive. `nauty.h` and
`naututil.h` are the `configure`-generated headers from an LP64
Linux/glibc run of the archive's `./configure` (the `*-h.in` templates are
included for comparison). The generated architecture hints affect only
popcount selection: unsupported hosts, including macOS arm64, take nauty's
portable software fallback with identical results.

This directory is published verbatim into `leanprover/nauty-ffi`. It is not
part of any released Hex library, and `nauty-ffi` is not a dependency of the
shipped `hex-graph-iso` library.

## File hashes (SHA-256)

| file | sha256 |
| --- | --- |
| `COPYRIGHT` | `e7e1cb03b4962e46e38084f24ef134dd7582a7f9e19e9cd81145ed6c71bea51c` |
| `LICENSE-2.0.txt` | `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30` |
| `naugraph.c` | `256a04bfdf554f43ca25fef50c1d339c6dd7223e274c0e811383c9c644f8434f` |
| `naurng.c` | `47238eeecc8139e889c48d016a5d708b709db80b1d049ecccb50fecf45ff1948` |
| `naurng.h` | `fe5bd6d039cf10e5aa5a449c4720b12f3c55d30a5b336d4de7a7a2b9625b4d8d` |
| `nausparse.h` | `5d02bb5a7640f08348a1a71bf31faedc032cc4c6fd55afdc1ace62e983612d65` |
| `nautil.c` | `92262d9b5c2597965a3dcf60e5351d101336b8d6cdfd62d6f724089508c721ec` |
| `naututil-h.in` | `046eef8a9b13ad4a52d02300680e4abdbabd26897c9ab2be5fc9ea1a958b95b8` |
| `naututil.h` | `08213056ee6b78dc0e5d3fa4a36df8f5a29c1f8b625d51d557354e2837fa4b03` |
| `nauty-h.in` | `e5430f5e02e115606a347b6c0e280aa2debc565936c8a3fbb4b56e84cf2681d3` |
| `nauty.c` | `d4ca7e89c5500e8a242c7a088c882ac1d11cd5738b51fd718f381f67be35dd04` |
| `nauty.h` | `3843db09a5a659c7fb20251abdc722cd055e541fd233268c9a5be9fd86161982` |
| `schreier.c` | `ddfed8d79e641b4509e94398b36f11e21bf3372bb8fa7f872de140f6c900c594` |
| `schreier.h` | `a3b1d9a53bf905c4e3fcb33754b306a69d02939ac1925b1a717fb10652d95f3e` |
| `sorttemplates.c` | `f5a5ac90adfd400ddd43499b5a06d98f45ea6aa03a0eafa95dab1f89b923a64d` |

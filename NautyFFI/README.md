# nauty-ffi

Lean 4 FFI bindings to the dense canonical-labelling surface of
[nauty](https://users.cecs.anu.edu.au/~bdm/nauty/) 2.9.3.

# Quickstart

Add the package to `lakefile.toml`:

```toml
[[require]]
name = "NautyFFI"
git = "https://github.com/leanprover/nauty-ffi.git"
rev = "main"
```

Then import the package and build normally:

```lean
import NautyFFI
```

```sh
lake build
```

The package builds its vendored C sources directly and needs only a C11
compiler in addition to the Lean toolchain. Linux and macOS are supported.

# Functionality

The public API is intentionally small:

- `NautyFFI.canonicalize` accepts a vertex-coloured undirected simple graph
  and returns nauty's canonical labelling together with its canonical form.
  The form consists of the ordered colour-cell sizes and the canonical
  adjacency upper triangle in row-major order.
- `NautyFFI.findIso` compares two canonical forms and, when they agree,
  returns the forward vertex transporter obtained from the two labellings.
- `NautyFFI.isIso` is the corresponding Boolean isomorphism test.

Inputs are validated for square symmetric loopless adjacency, in-range
colours, and nonempty ordered colour cells before the native call.

The binding uses dense nauty with the option set pinned by `hex-graph-iso`.
Sparse nauty, Traces, digraphs, and automorphism-group output are out of scope.
Coverage expands in lockstep with `hex-graph-iso`; this package does not run
ahead of the verified library's surface.

# Verification

This is an unverified convenience package around native code. It does not
provide proof-producing results. Users who need the verified surface should
use [`hex-graph-iso`](https://github.com/leanprover/hex-graph-iso) instead.

The test executable checks canonical forms and labellings in process against
the committed `hex-graph-iso` conformance fixtures:

```sh
lake build nautyffi_tests
lake exe nautyffi_tests
```

`nauty-ffi` is not, and must not become, a dependency of the shipped
`hex-graph-iso` library. The latter remains pure Lean. The `hex-dev` monorepo
uses this package only in its conformance and benchmark tooling, complementing
the separate Python-driven nauty shim oracle.

## Vendored nauty

`vendor/nauty-2.9.3` contains the minimal unmodified source subset from
`https://users.cecs.anu.edu.au/~bdm/nauty/nauty2_9_3.tar.gz`. The archive's
SHA-256 is
`9fc4edae04f88a0f5883985be3b39cf7f898fd6cc96e96b9ee25452743cc1b5b`.
The two generated configuration headers are the output of running the
archive's `configure` script; the vendored directory records that provenance
and a SHA-256 for every file.

nauty releases 2.6r3 and later, including 2.9.3, are Apache License 2.0. The
upstream `COPYRIGHT` notice and `LICENSE-2.0.txt` from the pinned archive are
included verbatim in the vendored directory. This package's Lean and bridge
code is also Apache-2.0 under the repository's root `LICENSE`.

# Contributing

This repository is a published mirror. Develop changes in
[`leanprover/hex-dev`](https://github.com/kim-em/hex-dev), which is the source
of truth, and use its release sync to publish them here.

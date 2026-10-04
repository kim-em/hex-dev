# hex-ecpp

Part of [hex](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4. The project aims for fast executable code, fully verified,
built with spec-driven development.

Elliptic curve primality proving (ECPP) proves an integer prime using a point
of sufficiently large prime order on an elliptic curve. `HexECPP` stores and
checks the mathematical data for this argument, searches for certificates,
and imports certificates supplied by PARI/GP. Its search partially factors
proposed curve orders and recursively proves their auxiliary primes.

This package provides computation without Mathlib. Import the
[HexECPPMathlib companion](https://github.com/kim-em/hex-dev/tree/main/HexECPPMathlib)
to turn accepted certificates into Lean proofs of `Nat.Prime n` using the
proved Hasse bound. See the
[manual](https://kim-em.github.io/hex-dev/HexECPP___-bounded-elliptic-curve-certificates/Introduction/)
for the mathematical argument and proof workflows.

# Quickstart

```toml
[[require]]
name = "hex-ecpp"
git = "https://github.com/leanprover/hex-ecpp.git"
rev = "main"
```

```lean
import HexECPP
open Hex.ECPP

def certificate : Cert := .base (.small 17)
#guard checkAt 17 certificate
#guard !checkAt 19 certificate
#guard (produce 17 0).result.toOption.any (checkAt 17)
#guard (convertText defaultImportBudget "17" (.small 17)).isOk
#guard match (produce 17 0 { maxBits := 4 }).result with
  | .error e => e.resource == .inputBits
  | _ => false
```

# Functionality

- `check` verifies the curves, point multiplications, modular inverses and
  auxiliary prime certificates. `checkAt n` also requires that the certificate
  is for the integer `n`.
- `parsePari`, `preflight`, `convert`, `convertText`, and `convertCounted`
  enforce explicit parsing, integer, row, scalar, inverse and endpoint allocations.
- `proposeScalar` generates checked affine inverse transcripts.
- `CM.sqrt?`, `CM.norm?`, and `CM.curves` supply bounded CM proposals.
  The 512-bit policy adds 33 fixed linear or quadratic class polynomials to
  the original nine discriminants; proposed roots and certificates are checked.
  Fifteen non-fundamental entries overlap existing group orders and supply
  additional curve/factoring proposals within the shared allocation.
- `produce` uses deterministic seeds and shared allocations across backtracking.
  It returns a checked certificate or a resource diagnostic; exhaustion does
  not establish compositeness. The default policy admits 256 bits;
  `native512Budget` admits 512 bits, and `public512Budget` additionally enforces
  the public replay row and node ceilings. Production above 512 bits is unsupported.

# Integer-factorization integration

`HexIntFactor.Mixed` is an explicit downstream consumer of subject-bound ECPP
evidence. It combines ECPP and legacy certificates without changing `PrimeCert`
or introducing a dependency cycle. Its native completion uses `public256Budget`
or `public512Budget`; the new public 256-bit policy bounds depth at 21, rows at
20 and constructor nodes at 32 while preserving the existing Native 256-bit API.
`HexECPP.Policy` and `HexECPP.ElabData` provide shared Mathlib-free replay bounds,
constructor-data auditing and reification. Unconditional mixed primality remains
owned by the mathematical companions.

# Verification

The checker arithmetic and its check of the intended integer are proved in Lean. `convert_ok`
and `produce_ok` establish that successful conversion and production pass
this checker. The checker never searches for inverses or calls an oracle.
Supplied-certificate replay has separate 512-bit conformance evidence.

An accepted ECPP step's unconditional primality implication requires the
curve and Hasse correspondence owned by `HexECPPMathlib`. Importing this
package alone does not provide that theorem. PARI is an independent testing
oracle and optional input source, rather than a runtime dependency.

# Contributing

Development happens in the [hex-dev monorepo](https://github.com/kim-em/hex-dev),
rather than this published mirror. Contributions are welcome as pull requests
to the `SPEC/` directory: describe the behaviour you want and leave the
implementation to the maintainer.

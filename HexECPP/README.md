# hex-ecpp

Part of [hex](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4. The project aims for fast executable code, fully verified,
built with spec-driven development.

`HexECPP` provides arithmetic checking of elliptic-curve primality
certificates, bounded PARI certificate conversion, and opt-in native CM
production through 256 bits. It depends on `HexArith` and `HexPrimality`.
The [HexECPPMathlib companion](https://github.com/kim-em/hex-dev/tree/main/HexECPPMathlib)
owns curve semantics, the Hasse bound, and the unconditional primality implication.

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

- `check` replays supplied inverse witnesses and the exact integer size bound.
  `checkAt` also binds the certificate to its requested subject.
- `parsePari`, `preflight`, `convert`, `convertText`, and `convertCounted`
  enforce explicit parsing, integer, row, scalar, inverse and endpoint allocations.
- `proposeScalar` generates checked affine inverse transcripts.
- `CM.sqrt?`, `CM.norm?`, and `CM.curves` supply bounded CM proposals.
- `produce` uses deterministic seeds and shared allocations across backtracking.
  It returns a checked certificate or a resource diagnostic; exhaustion does
  not establish compositeness. Native production above 256 bits is unsupported.

# Verification

Arithmetic invariants and subject binding are proved in Lean. `convert_ok`
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

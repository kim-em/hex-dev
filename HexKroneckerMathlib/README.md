# HexKroneckerMathlib

Soundness of the integer Kronecker checks in any commutative ring, with the
explicitly invoked `kronecker` tactic and `kronecker%` term form.

```lean
import HexKroneckerMathlib

example {R : Type*} [CommRing R] (x y : R) :
    (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  kronecker

example {R : Type*} [CommRing R] (x y : R) :
    (x + y)^2 = x^2 + 2*x*y + y^2 :=
  kronecker% ((x + y)^2 = x^2 + 2*x*y + y^2)
```

The tactic uses a shared atom assignment for both sides, preserves their
expression trees, checks the dense-box budget, and submits an integer equality
certificate to the kernel. It requires no characteristic hypothesis. It uses
no local hypotheses or relations between independent atoms, and participates
in no default tactic chain.

Tighten the limits with, for example,
`kronecker (config := { maxDenseDigits := 4096, maxPackedBits := 1048576 })`.
Inputs outside either limit decline before packing and report the required size.

Programmatic callers can apply the six `Hex.Kronecker.check..._sound` theorems.
The `Mod_sound` theorems accept an explicit integer quotient witness and map the
result to any ring of the stated characteristic. Import
`HexKroneckerMathlib.Residue` for the bridge from hex-reflect's machine residue
coefficients to their canonical integer lifts.

See the [SPEC](SPEC/hex-kronecker-mathlib.md) for denotations, the reflection
boundary, and the performance requirements.

## Development verification

From the monorepo root, build the matched modules with
`lake build HexKroneckerMathlibProofProbe`. Collect the six paired trials and
the separate kernel-only profiles with:

```sh
python3 scripts/bench/kronecker_sweep.py reports/data/hex-kronecker-mathlib/local-sweep.json
python3 scripts/bench/kronecker_kernel_profile.py reports/data/hex-kronecker-mathlib/local-kernel.json
```

Both runners lease one CPU automatically and record source hashes and host
activity. The sweep accepts `--resume` after interruption and retains completed
samples. `scripts/bench/kronecker_report.py` renders a completed sweep with the
required `--kernel-profiles` input; both JSON inputs may be gzip-compressed.

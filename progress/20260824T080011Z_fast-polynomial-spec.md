# Fast polynomial arithmetic SPEC

## Accomplished

- Added `SPEC/Libraries/hex-poly-fast.md`, specifying explicit lawful
  multiplication plans, Karatsuba/clipped products, Newton division,
  half-gcd, product/remainder trees, multipoint evaluation/interpolation,
  Padé approximation, multipoint Kronecker, redundant-residue NTTs, and both
  finite-field and integer CRT-NTT multiplication.
- Assigned coefficient-specific work to hex-mod-arith, hex-modular,
  hex-poly-fp, and hex-poly-z and amended each owning SPEC.
- Added benchmark-gated adoption requirements to the Hensel, Berlekamp,
  Berlekamp-Zassenhaus, and GFq-ring consumer SPECs.
- Indexed the new planned library, removed its sketch from future work, and
  limited the Harvey prior-art discussion to the three selected papers.
- Left `libraries.yml`, `scripts/release/released.yml`, and Lake configuration
  unchanged; this session specifies future implementation rather than
  registering it.
- Passed `scripts/check_dag.py`, `scripts/check_phase4.py`, `git diff --check`,
  and relative-link/code-fence validation over every changed Markdown file.

## Current frontier

The specification family is decision-complete. The first executable work is
blocked by the planned hex-truncated-series and hex-modular prerequisites;
their SPECs now include the required Karatsuba `mulUpToImpl` and balanced
batch CRT work.

## Next step

Implement and activate the prerequisite milestones, then scaffold
`HexPolyFast` with `MulPlan`, schoolbook agreement, and the measured Karatsuba
full/square/slice kernels before starting Newton division.

## Blockers

No documentation blocker. Implementation ordering must preserve the DAG:
hex-truncated-series and hex-modular precede hex-poly-fast, and coefficient
library dependency changes land only after hex-poly-fast is active.

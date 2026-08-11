# Sparse-valued matrix multiplication timing

**Accomplished**

- Measured Hex dense `Int` matrix multiplication on deterministic sparse-valued
  square inputs at 1%, 5%, and 10% density, with nonzero coefficients in
  `{-3, -2, -1, 1, 2, 3}`.
- Used the canonical `lean-bench` harness on `chungus2`, pinned to CPU 24, with
  three outer trials for `n = 64, 128, 256, 512, 1024`.
- Compared ordinary `*` with `mulStrassen strassenDefault` at 5% density.
- Removed the temporary local registrations and rebuilt `hexmatrix_bench`
  successfully, leaving its tracked source unchanged.

**Current frontier**

- Ordinary `*` medians were effectively independent of the tested density:
  about 0.80 ms, 5.2 ms, 38 ms, 282 ms, and 2.16--2.20 s across the five sizes.
- At 5% density, Strassen medians were about 0.90 ms, 7.74 ms, 60.1 ms,
  443 ms, and 3.29 s, so the ordinary dense kernel was faster throughout.
- The result reflects sparse-valued dense storage: Hex currently executes the
  full dense dot-product schedule and does not skip zero entries.

**Next step**

- If sparse multiplication becomes a supported performance surface, design a
  sparse representation/kernel and add a permanent benchmark family that
  varies both dimension and density.

**Blockers**

- None.

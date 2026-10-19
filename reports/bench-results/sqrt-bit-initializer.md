# Bit-length square-root initializer: factorization scope

`HexArith.Nat.floorSqrt` starts Newton iteration at
`min n (2 ^ ((n.log2 + 2) / 2))`. The ordinary kernel proves that this start is
positive and at most `n` for positive inputs, and lies above the square-root
floor. The public `floorSqrt_eq` proves equality with Lean core's `Nat.sqrt`.
Conformance checks small integers and exact squares and their neighbours at
64, 257 and 4096 bits. The completed claims use only the three standard logical
axioms.

The initializer is used transitively by the compiled Hex factorization service.
The [selective sweep](hexbz-factor-sweep-sqrt-bit-initializer-16cff198bb.json)
therefore refreshes only `hex-factor`; all external comparator observations are
retained. It covers all 392 inputs of corpus SHA-256
`619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
The service solved 383 inputs in 118.1 seconds. All nine unsuccessful results
remain in the export. The 10-second cutoff is an operational safeguard.
There is no unchanged rerun, load exclusion or early termination.

The clean measured source is `16cff198bb2f2230b3553fb11766768b379081e5`.
The native service SHA-256 is
`bcba83c1ab9e0796bb4aad8c713be043738e25f38179cbfd5045ff4be41032a2`.
Measurement used automatically leased CPU 34 on `chungus2`; start load averages
were 6.53, 22.41 and 29.86, and end averages 10.23, 18.12 and 27.35.
The report's source fingerprint and committed manifest bind its relevant call
graph. Regenerate the factorization charts with `scripts/plots/hexbz-cactus.py`;
its newest-per-system merge reuses the external records.

This selective refresh does not establish four-library Phase-4 readiness or
change the attestation of any transitive library. It also does not remove the
remaining canonical real-algebraic construction and isolation concerns.

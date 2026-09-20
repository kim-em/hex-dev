# Polynomial determinant certificates

`Hex.PolyDet.polyDetWitness` runs row-pivoted fraction-free elimination on a polynomial matrix and retains its transform or a polynomial left kernel vector. The generic witness and list checker belong to `HexBareiss`; this library supplies `MvPoly` arithmetic and `Hex.exactDiv`.

`polyDetWitness?` returns a witness only after the compiled canonical-list check succeeds. `polyDet` computes the determinant with the existing Bareiss implementation. The Mathlib companion proves soundness of the list check and implements symbolic `det`.

Supported executable coefficient domains include integers, rationals, and prime residues through the existing lawful exact-division instances. Kernel certificates use canonical integer or reduced-Nat residue lists.

`checkDetPolyPacked` checks the same witness with bounded Kronecker products. `checkDetPolyPackedMod` additionally checks integer quotient rows proving divisibility by the characteristic. Structural checks, canonicality, and nonzero tests remain polynomial checks in the kernel. `Packed.select` preflights every product against the digit and bit limits and selects one checker for the entire witness. Unmeasured crossover keys and unavailable residue quotients select term lists.

The 30 conformance records in `conformance-fixtures/HexPolyDet/det.jsonl` are checked against SymPy's Berkowitz determinant. `lake build hexpolydet_bench` builds the Mathlib-free producer/checker benchmark ladder. Its preparation holds a precomputed certificate, and its checker measurements exclude conversion and production.

`lake build hex_poly_det_packed` builds the compiled preflight and phase-timing driver used by `scripts/bench/det_packed_sweep.py`.

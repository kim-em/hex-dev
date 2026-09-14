# Polynomial determinant certificates

`Hex.PolyDet.polyDetWitness` runs row-pivoted fraction-free elimination on a polynomial matrix and retains its transform or a polynomial left kernel vector. The generic witness and list checker belong to `HexBareiss`; this library supplies `MvPoly` arithmetic and `Hex.exactDiv`.

`polyDetWitness?` returns a witness only after the compiled canonical-list check succeeds. `polyDet` computes the determinant with the existing Bareiss implementation. The Mathlib companion proves soundness of the list check and implements symbolic `det`.

Supported executable coefficient domains include integers, rationals, and prime residues through the existing lawful exact-division instances. Kernel certificates use integer lists; reduced-Nat residue quotation awaits #10257.

The 30 conformance records in `conformance-fixtures/HexPolyDet/det.jsonl` are checked against SymPy's Berkowitz determinant. `lake build hexpolydet_bench` builds the Mathlib-free producer/checker benchmark ladder. Its preparation holds a precomputed certificate, and its checker measurements exclude conversion and production.

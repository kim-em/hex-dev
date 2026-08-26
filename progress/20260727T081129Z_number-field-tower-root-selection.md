# Accomplished

- Added recursive exact evaluation of mixed-radix tower elements at the stored absolute generators.
- Added tower-aware value majorants and certified ball evaluation using the finite `evalDisambiguationPrec` boundary.
- Added integer-polynomial lifting and unique multiplicity-one factor selection for a requested `AlgebraicRoot`.
- Added a conjugate-impostor regression over `Q(sqrt(2))` that retains `X - sqrt(2)` and rejects the other linear factor.
- Activated `HexNumberFieldTower.Split` in the umbrella and rebuilt it successfully.

# Current frontier

Fixed-embedding factor selection is complete. Creating the selected nonlinear extension now requires replacing the structural-only tower constructor boundary with one that carries meaningful irreducibility and embedding certificates.

# Next step

Land factor selection as a focused milestone, then implement the validated extension constructor and the public `adjoin?` identity/nonlinear cases.

# Blockers

None.

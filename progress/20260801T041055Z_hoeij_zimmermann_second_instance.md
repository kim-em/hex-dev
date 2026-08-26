# Hoeij–Zimmermann second-instance investigation

## Accomplished

- Reproduced the current Hoeij–Zimmermann coverage split: Hex answers only
  `hoeij_M12_f132`; NTL answers every row except `hoeij_S9`.
- Traced Hex's classical tier on the family. `hoeij_F190` selects `p = 13`
  with 38 degree-five local factors, exhausts 74,519 head-forced candidates,
  and then sends the unchanged degree-190 problem to the lattice tier.
- Factored `hoeij_F190` independently to identify its integer factor degrees
  as 10, 90, and 90. The degree-10 factor is supported by only two local
  factors, but the head-forced order misses it because the fixed head belongs
  to one of the 18-element supports.
- Ran NTL 11.6.0 with verbose phase timing. It finds the degree-10 factor in
  its unforced cardinality-two sweep, then reduces three incremental trace
  lattices; total LLL time was about 9.4 ms and total factorization time about
  35 ms.
- Profiled Hex's `factorLattice` on `hoeij_F190`. The current all-coefficients
  construction produces a 228-by-228 lattice and did not finish in 90 seconds.
  A temporary experiment routing the same basis through the certified fpLLL
  seam still exceeded 60 seconds, showing that changing the reducer alone is
  insufficient. The temporary source changes were reverted and
  `lake build hexbz_factor_service` is green.
- Measured certificate-replay feasibility on the three known `F190` factors:
  the current classical tier certified them in 0.023 s, 4.715 s, and 0.671 s.

## Current frontier

`hoeij_F190` is the best candidate for a second answered family row. A
general unforced cardinality-one-to-three sweep should expose its degree-10
factor cheaply. The remaining 90/90 support split needs a small incremental
CLD/trace lattice or another support-proposal mechanism; the existing
all-coefficients lattice is too large even with fpLLL.

The lowest-proof-cost design is to treat the incremental lattice as a candidate
generator, check the proposed product exactly, and certify each smaller piece
with the already-proved classical factorizer. This avoids placing the adaptive
lattice heuristic in the trust boundary while retaining complete irreducible
output.

## Next step

Prototype an `r`-dimensional incremental CLD proposal lattice on the residual
36 local factors, adding one or a few coefficient columns per reduction. Record
the dimensions, precisions, partition after each reduction, proposal time, and
classical replay time. In parallel with that prototype, replace the initial
head-forced low-cardinality levels by an unforced, degree-pruned sweep and make
bounded decline retain partial factors and the residual modular support.

## Blockers

No external blocker. The main uncertainty is empirical: how many direct CLD
columns are needed to recover the 18/18 residual partition with Hex's current
coefficient construction, and whether native certified reduction of those
small matrices stays inside the roughly four-second budget left after classical
certificate replay.

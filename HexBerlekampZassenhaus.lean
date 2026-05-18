import HexBerlekampZassenhaus.Basic
import HexBerlekampZassenhaus.Conformance
import HexBerlekampZassenhaus.CrossCheck
import HexBerlekampZassenhaus.SmallModSingleton

/-!
The `HexBerlekampZassenhaus` library exposes the executable integer
Berlekamp-Zassenhaus factorization pipeline: normalization, good-prime
selection, Hensel-lift packaging, LLL-based recombination, bounded/default
factor entry points, and the integer irreducibility certificate checker.

The library root also imports `HexBerlekampZassenhaus.Conformance` for
Phase 3 core checks and `HexBerlekampZassenhaus.CrossCheck`, the
SPEC-sanctioned LLL-vs-exhaustive recombination cross-check.
-/

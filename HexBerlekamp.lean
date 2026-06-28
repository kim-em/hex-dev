import HexBerlekamp.Basic
import HexBerlekamp.DistinctDegree
import HexBerlekamp.Factor
import HexBerlekamp.Irreducibility
import HexBerlekamp.RabinSoundness

/-!
`HexBerlekamp` exposes the executable Berlekamp-matrix surface for factoring
over `F_p`, centered on the Frobenius matrix `Q_f`, its fixed-space kernel, and
the first irreducibility-facing, split-step factoring, and distinct-degree
factorization tests built from that data.
-/

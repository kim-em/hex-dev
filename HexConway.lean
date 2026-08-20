/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexConway.Rebuild
import HexConway.Table
import HexConway.Certificates
import HexConway.Api
import HexConway.Compatibility
import HexConway.Primitivity
import HexConway.EntrySource

/-!
`HexConway` provides the Tier 1 imported-lookup API for the Conway-polynomial
database: 38 committed table entries, for `p` in `2, 3, 5, 7, 11, 13`, running
to degree `6` for the odd primes and to degree `8` for `p = 2`, each carrying a
Lean-checked irreducibility certificate, and the divisor-compatibility half of
Tier 2 in `HexConway.Compatibility`: for every committed pair whose degrees
divide, the norm of the generator down to the smaller subfield is a root of the
smaller Conway polynomial, and `HexConway.Primitivity`, which checks that each
committed entry's generator has multiplicative order exactly `p^n - 1`. Tier 3
(on-demand search) is specified but not yet implemented.

`HexConway.Rebuild` supplies the `rebuild_luebeckConwayPolynomial?` command that
regenerates the committed coefficient table from the cached Lübeck slice. The
invocation sits commented out above the table in `HexConway.Table`, so a build
never reads the cache; uncommenting it offers the regenerated definition as a
`Try this:` replacement. The module is imported here so that the command stays
compiled and its rendering stays covered by the conformance checks, rather than
rotting until the next time someone widens the table.

`HexConway.EntrySource` covers the rest of a widening. The coefficient table is
only the data; each entry also needs a polynomial literal, its monic and degree
facts, a table-hit lemma, and a Rabin certificate. All of those are mechanical
except the certificate, which has to be computed, so `#conway_entry_source`
computes it and renders the whole block. It is imported here for the same reason
as the command, and for the same reason it costs a build nothing: neither runs
unless invoked.
-/

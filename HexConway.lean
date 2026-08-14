/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexConway.Table
import HexConway.Certificates
import HexConway.Api

/-!
`HexConway` provides the Tier 1 imported-lookup API for the Conway-polynomial
database: 36 committed table entries, for `p` in `2, 3, 5, 7, 11, 13` and `n`
in `1` to `6`, each carrying a Lean-checked irreducibility certificate. Tier 2
(primitivity and compatibility across the subfield lattice) and Tier 3
(on-demand search) are specified but not yet implemented.
-/

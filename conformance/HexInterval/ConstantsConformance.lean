/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval

/-!
# Named-constant certificate conformance

Oracle: independent Python Fraction series and a second Machin identity in
`scripts/oracle/interval_constants.py`; the checks here need no external tool.
Mode: always.
Covered operations:
- bounded generation, the deterministic order schedule and literal replay;
- exact factorial/arctangent recurrences and source/precision authentication.
Covered properties:
- accepted finite cuts, actual requested width and successful replay;
- rejection of mutated subjects, orders, witnesses, cuts and exhausted budgets.
Covered edge cases:
- zero precision, inadequate order, billion-bit requests and zero resource caps;
- precisions from 0 through 1000, including the SPEC's π acceptance target.
-/

namespace Hex.Interval.ConstantsConformance

open Constants

private def accepted (source : Source) (bits : Nat) : Bool :=
  match enclose (limitsFor bits) source bits with
  | .error _ => false
  | .ok certificate =>
      match check (limitsFor bits) source bits certificate with
      | .error _ => false
      | .ok interval =>
          interval.view == .bounds (.finite certificate.lower false)
            (.finite certificate.upper false) &&
          certificate.upper.toRat - certificate.lower.toRat ≤ mkRat 1 (2 ^ bits)

#guard [.piMachinV1, .expOneTaylorV1].all fun source =>
  [0, 1, 8, 32, 128, 256, 1000].all (accepted source)

-- Closed-form first terms, independent of the recurrence implementation.
#guard (arctanState 5 2).1 == mkRat 74 375
#guard (arctanState 5 2).2 == 3125
#guard arctanRadius 5 3125 == mkRat 1 3000
#guard expState 4 == (64, 24)
#guard (approximate .expOneTaylorV1 4) == ⟨mkRat 8 3, mkRat 5 96⟩

private def refused (result : Except Error α) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

#guard match generate (limitsFor 32) .expOneTaylorV1 32 1 with
  | .error .width => true
  | _ => false
#guard match generate (limitsFor 32) .piMachinV1 32 0 with
  | .error .order => true
  | _ => false
#guard match enclose (limitsFor 32) .piMachinV1 1000000000 with
  | .error .order => true
  | _ => false

private def adversarial (source : Source) : Bool :=
  let limits := limitsFor 32
  match enclose limits source 32 with
  | .error _ => false
  | .ok c =>
      let other := if source == .piMachinV1 then Source.expOneTaylorV1 else .piMachinV1
      refused (check limits other 32 c) &&
      refused (check limits source 31 c) &&
      refused (check limits source 32 { c with order := 0 }) &&
      refused (check limits source 32 { c with approximation.radius := 0 }) &&
      refused (check limits source 32 { c with approximation.center := 0 }) &&
      refused (check limits source 32 { c with lower := c.upper }) &&
      refused (check limits source 32 { c with upper := c.lower }) &&
      refused (check limits source 32 { c with lower := .ofIntWithPrec 1 1000000000 }) &&
      (match check { limits with maxReplayWork := 0 } source 32 c with
       | .error .replay => true
       | _ => false)

#guard [.piMachinV1, .expOneTaylorV1].all adversarial

-- Unchecked formula helpers do not make negative radii acceptable at the
-- finishing boundary, and computed witnesses must obey the bit charge.
#guard match finish (limitsFor 8) .piMachinV1 8 12 ⟨3, -1⟩ with
  | .error .endpoints => true
  | _ => false
#guard match finish (limitsFor 0) .piMachinV1 0 0 ⟨(2 : Rat) ^ 300, 0⟩ with
  | .error .integerBits => true
  | _ => false

#guard match enclose { limitsFor 8 with maxIntegerBits := 0 } .piMachinV1 8 with
  | .error .integerBits => true
  | _ => false
#guard match enclose { limitsFor 8 with maxIntegerWork := 0 } .piMachinV1 8 with
  | .error .integerWork => true
  | _ => false
#guard match enclose { limitsFor 8 with maxAllocation := 0 } .piMachinV1 8 with
  | .error .allocation => true
  | _ => false
#guard refused (enclose { limitsFor 8 with arithmetic.maxTemporaryBits := 0 } .piMachinV1 8)
#guard refused (enclose { limitsFor 8 with arithmetic.endpoint.maxEndpointHeight := 0 }
  .expOneTaylorV1 8)
#guard refused (enclose { limitsFor 8 with arithmetic.maxPrecisionMagnitude := 0 }
  .expOneTaylorV1 8)

-- The default integer/replay caps are exact charges, so one unit less must
-- refuse before approximation; the equality case is exercised by accepted.
#guard match enclose
    { limitsFor 8 with maxIntegerBits := (limitsFor 8).maxIntegerBits - 1 }
    .piMachinV1 8 with
  | .error .integerBits => true
  | _ => false
#guard match enclose
    { limitsFor 8 with maxIntegerWork := (limitsFor 8).maxIntegerWork - 1 }
    .piMachinV1 8 with
  | .error .integerWork => true
  | _ => false
#guard match enclose
    { limitsFor 8 with maxAllocation := (limitsFor 8).maxAllocation - 1 }
    .expOneTaylorV1 8 with
  | .error .allocation => true
  | _ => false
#guard match enclose (limitsFor 8) .expOneTaylorV1 8 with
  | .error _ => false
  | .ok c => match check
      { limitsFor 8 with maxReplayWork := (limitsFor 8).maxReplayWork - 1 }
      .expOneTaylorV1 8 c with
    | .error .replay => true
    | _ => false

end Hex.Interval.ConstantsConformance

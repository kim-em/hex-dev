/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Membership
import HexGroebner.NormalForm
import HexGroebner.Division
import HexGroebnerTheory.DivisionExample

namespace HexGroebnerTheory.DivisionExample
open Hex.Groebner

def receipt : CheckedBasis := CheckedBasis.ofCertificate context generators generators basis (by decide +kernel)

#guard match memberWith receipt {} target with
  | .nonmember _ _ => true
  | _ => false
#guard match memberWith receipt {} generators[0]! with
  | .member division _ _ => division.value.quotients == #[[([0], 1)]]
  | _ => false
#guard match memberWith receipt { work := 0 } target with
  | .exhausted .work _ => true
  | _ => false

private def finishBoundary : Bool := Id.run do
  let .success _ usage := normalFormWith receipt {} target | return false
  let .exhausted .work state := memberWith receipt { work := usage.work } target | return false
  if !state.stage.isRight then return false
  match resumeMemberWith {} state with
  | .nonmember _ final => return final.work > usage.work
  | _ => return false

#guard finishBoundary

end HexGroebnerTheory.DivisionExample

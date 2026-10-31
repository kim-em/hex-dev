/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateContainment
public import HexGroebner.CertificateReduction

@[expose] public section

namespace Hex.Groebner
namespace Certificate

/-- Both ideal containments and a bounded cofactor representation for each
ordered final S-pair. Pair arrays use the proposed basis indices, including
diagonal zero pairs. This initial exact checker deliberately checks all pairs.
This dense witness type is provisional; it is not a stable interchange format.
Sparse/shared pair witnesses remain required for large computations. -/
structure Basis where
  forward : Containment
  backward : Containment
  pairs : Array (Array (Array Polynomial))
  deriving Repr, Inhabited

/-- Monic, nonzero, reduced and sorted basis shape. Every divisibility test uses
exact exponents; a term may be divisible only by its own leading monomial. -/
def checkShape (order : TermOrder) (basis : Array Polynomial) : Bool :=
  let heads := basis.map (leading order)
  (List.finRange basis.size).all fun i =>
    match heads[i.val]'(by simp [heads]) with
    | none => false
    | some a => a.2 == 1 && (List.finRange basis.size).all fun j =>
      match heads[j.val]'(by simp [heads]) with
      | none => false
      | some b =>
        (if i.val < j.val then compare order a.1 b.1 == .gt else true) &&
        basis[i].all fun term =>
          !divides b.1 term.1 || (i.val == j.val && term.1 == a.1)

end Certificate

/-- Independent complete basis replay. Both containment directions, all final
S-pair degree bounds, canonical coefficients, reducedness and decreasing leading
order are checked from literal data. This function does not rerun F4 and gives
no special trust to the candidate producer or a native success flag. -/
def checkBasis (context : Context) (generators basis : Array Certificate.Polynomial)
    (certificate : Certificate.Basis) : Bool :=
  let p := context.field.modulus.toNat
  let n := context.variables
  Certificate.checkContainment p n generators basis certificate.forward &&
    Certificate.checkContainment p n basis generators certificate.backward &&
    Certificate.checkShape context.order basis &&
    Certificate.checkPairs p n context.order basis certificate.pairs

end Hex.Groebner

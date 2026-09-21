import Algebraic
open Hex Algebraic
namespace Nested

abbrev Base := Element reducible
def alpha : Base := pack reducible (DensePoly.monomial 1 1)
def defining : DensePoly Base := DensePoly.ofCoeffs #[-alpha,0,1]

/-- For this particular irreducible quadratic over Q(sqrt(2)), remainder zero
is exact. This is not a replacement for general tower root determination. -/
def zero (q : DensePoly Base) : Bool := (DensePoly.divMod q defining).2.isZero
abbrev Elem := Option {q : DensePoly Base // zero q = false}
instance : Zero Elem := ⟨none⟩
instance : DecidableEq Elem := inferInstanceAs (DecidableEq (Option {q : DensePoly Base // zero q = false}))
def pack (q : DensePoly Base) : Elem := if h : zero q = false then some ⟨q,h⟩ else none
def raw : Elem → DensePoly Base | none => 0 | some q => q.val
instance : One Elem := ⟨pack 1⟩
instance : NatCast Elem := ⟨fun n => pack (DensePoly.C (n : Base))⟩
instance : Add Elem := ⟨fun a b => pack (raw a+raw b)⟩
instance : Sub Elem := ⟨fun a b => pack (raw a-raw b)⟩
instance : Mul Elem := ⟨fun a b => pack (raw a*raw b)⟩
instance : Neg Elem := ⟨fun a => pack (-raw a)⟩
instance : Inv Elem := ⟨fun a =>
  if raw a == 0 then 0 else
    let eg := DensePoly.xgcd (raw a) defining
    pack (DensePoly.scale eg.gcd.leadingCoeff⁻¹ eg.left)⟩
instance : Div Elem := ⟨fun a b => a*b⁻¹⟩
def beta : Elem := pack (DensePoly.monomial 1 1)

/-- Runtime regression over genuine nested coefficients; no fake Field instance.
The fourth-root interpretation still needs a companion proof. -/
def checks : Bool := Id.run do
  let a := pack (DensePoly.C alpha)
  if beta*beta-a != 0 then return false
  if beta*beta*beta*beta-((2 : Nat) : Elem) != 0 then return false
  if beta*beta⁻¹-1 != 0 then return false
  let alternative := pack (DensePoly.monomial 1 1+defining)
  if beta == alternative || beta-alternative != 0 then return false
  let p := DensePoly.ofCoeffs #[beta,1]
  let q := DensePoly.ofCoeffs #[a,1]
  let (quot,rem) := DensePoly.divMod (p*q) q
  return rem.isZero && (quot-p).isZero
end Nested

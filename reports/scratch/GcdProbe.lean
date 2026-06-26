module

public import HexBerlekampZassenhaus.Basic

public section

open Hex

private def zp (cs : Array Int) : ZPoly := DensePoly.ofCoeffs cs

private def splitProduct (n : Nat) : ZPoly := Id.run do
  let mut acc : ZPoly := 1
  for i in [1:n+1] do
    acc := acc * (zp #[-(Int.ofNat i), 1])
  return acc

private instance b13 : ZMod64.Bounds 13 := ⟨by decide, by decide⟩

@[expose]
def main : IO Unit := do
  let f := splitProduct 11
  let fModP := @ZPoly.modP 13 b13 f
  let fp' := DensePoly.derivative fModP
  let g := DensePoly.gcd fModP fp'
  let toNat (x : ZMod64 13) : Nat := x.toNat
  IO.println s!"f mod 13 size={fModP.toArray.size}, vals={fModP.toArray.toList.map toNat}"
  IO.println s!"f' mod 13 size={fp'.toArray.size}, vals={fp'.toArray.toList.map toNat}"
  IO.println s!"gcd size={g.toArray.size}, vals={g.toArray.toList.map toNat}"
  IO.println s!"gcd == 1? {g == 1}"
  let one : DensePoly (ZMod64 13) := 1
  IO.println s!"(1 : Fp13Poly).toArray vals = {one.toArray.toList.map toNat}"
  IO.println s!"isGoodPrime f 13 = {@Hex.isGoodPrime f 13 b13}"
  IO.println s!"f mod 13 leading {toNat (DensePoly.leadingCoeff fModP)}"

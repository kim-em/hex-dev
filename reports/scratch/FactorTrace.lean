import HexBerlekampZassenhaus.Basic

open Hex

private def zp (cs : Array Int) : ZPoly := DensePoly.ofCoeffs cs

private def splitProduct (n : Nat) : ZPoly := Id.run do
  let mut acc : ZPoly := 1
  for i in [1:n+1] do
    acc := acc * (zp #[-(Int.ofNat i), 1])
  return acc

private def encodeInts (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

/-- Force evaluation of a Factorization by hashing every coefficient. -/
private def fingerprint (φ : Factorization) : UInt64 :=
  let h0 : UInt64 := hash φ.scalar
  φ.factors.foldl (init := h0) fun acc (g, m) =>
    let gh := g.toArray.foldl (init := (0 : UInt64)) (fun a c => mixHash a (hash c))
    mixHash (mixHash acc gh) (hash m)

private def report (label : String) (f : ZPoly) : IO Unit := do
  let prime := Hex.choosePrime f
  let data? := Hex.choosePrimeData? f
  let dataPrime :=
    match data? with
    | some data => toString data.p
    | none => "none"
  let primeOk := data?.isSome
  let coeffBound := ZPoly.defaultFactorCoeffBound f
  IO.println s!"--- {label} (deg {f.degree?.getD 0}, choosePrime={prime}, dataPrime={dataPrime}, dataOk={primeOk}, B={coeffBound})"

  -- Time factorFastWithBound at the default bound used by factor combinator
  let mut chk : UInt64 := 0
  let tA ← IO.monoNanosNow
  let mFastB := Hex.factorFast f
  chk := chk ^^^ (fingerprint (mFastB.getD ({ scalar := 0, factors := #[] } : Factorization)))
  let tB ← IO.monoNanosNow
  let fastBms := Float.ofInt (Int.ofNat (tB - tA)) / 1e6
  match mFastB with
  | none => IO.println s!"  factorFast (at fastCap): none  ({fastBms} ms, chk={chk})"
  | some φ =>
      let degs := φ.factors.toList.map (fun e => e.1.degree?.getD 0)
      IO.println s!"  factorFast (at fastCap): {φ.factors.size} factors degrees={degs}  ({fastBms} ms, chk={chk})"

  -- Time the public combinator
  let tC ← IO.monoNanosNow
  let φFull := Hex.factor f
  chk := chk ^^^ (fingerprint φFull)
  let tD ← IO.monoNanosNow
  let fullMs := Float.ofInt (Int.ofNat (tD - tC)) / 1e6
  let degs := φFull.factors.toList.map (fun e => e.1.degree?.getD 0)
  IO.println s!"  factor   (combinator): {φFull.factors.size} factors degrees={degs}  ({fullMs} ms, chk={chk})"

def main : IO Unit := do
  for n in [3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24] do
    report s!"(x-1)..(x-{n})" (splitProduct n)

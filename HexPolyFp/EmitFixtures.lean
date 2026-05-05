import Hex.Conformance.Emit
import HexPolyFp

/-!
JSONL emit driver for the `hex-poly-fp` oracle.

`lake exe hexpolyfp_emit_fixtures` writes JSONL records covering
`F_p[x]` arithmetic at primes `p ∈ {5, 11, 31}`, the Frobenius image
`f^p mod g` over the same primes, and Yun-style square-free
decomposition over `F_5`.  The companion driver
`scripts/oracle/polyfp_flint.py` re-runs each operation through
python-flint's `nmod_poly` and compares.

Coefficients are rendered as their canonical `[0, p)` representatives.
For `gcd` we monic-normalise the Lean output before emission so the
result coincides with python-flint's monic gcd.  For square-free
decomposition we hoist constant factors and leading coefficients into
the unit, then sort the remaining monic factors so the comparison is
order-independent.
-/

namespace Hex.PolyFpEmit

open Hex.Conformance.Emit
open Hex.FpPoly

private def lib : String := "HexPolyFp"

private instance instBoundsFive  : ZMod64.Bounds 5  := ⟨by decide, by decide⟩
private instance instBoundsEleven : ZMod64.Bounds 11 := ⟨by decide, by decide⟩
private instance instBoundsThirtyOne : ZMod64.Bounds 31 := ⟨by decide, by decide⟩

/-- Manual primality witness for `5`, mirroring the existing
`HexPolyFp/Conformance.lean` proof.  Required by
`squareFreeDecomposition`. -/
private theorem primeFive : Hex.Nat.Prime 5 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simp at hm
  · exact Or.inl rfl
  · simp at hm
  · simp at hm
  · simp at hm
  · exact Or.inr rfl

/-! ## Coefficient generation -/

/-- Deterministic `(seed, i) → ZMod64 p` mixing function.  The integer
constants are large odd primes so distinct seeds give visibly different
sequences without a true PRNG. -/
private def coeffOf (p : Nat) [ZMod64.Bounds p] (seed i : Nat) : ZMod64 p :=
  ZMod64.ofNat p ((seed * 73856093 + i * 19349663 + 83492791) % 2147483647)

/-- Generate a polynomial with `deg + 1` coefficients drawn from `coeffOf`.
The actual `degree?` may be smaller if a randomly-generated leading
coefficient happens to be zero (`ofCoeffs` trims trailing zeros). -/
private def randomPoly (p : Nat) [ZMod64.Bounds p] (seed deg : Nat) : FpPoly p :=
  ofCoeffs (Array.ofFn (n := deg + 1) fun i => coeffOf p seed i.val)

/-! ## Monic polynomial construction (for Frobenius modulus)

We build the array as `(coefficients of degree 0..deg-1).push 1` so the
leading coefficient is provably `1` after `ofCoeffs` trims trailing
zeros (it cannot trim the final `1`). -/

/-- `(deg coefficients of degrees 0..deg-1).push 1`. -/
private def monicArray (p : Nat) [ZMod64.Bounds p] (seed deg : Nat) :
    Array (ZMod64 p) :=
  (Array.ofFn (n := deg) fun i => coeffOf p seed i.val).push (1 : ZMod64 p)

private theorem monicArray_back?
    (p : Nat) [ZMod64.Bounds p] (seed deg : Nat) :
    (monicArray p seed deg).back? = some (1 : ZMod64 p) := by
  simp [monicArray]

/-- Required nondegeneracy for `monicArray` to survive `ofCoeffs`'s trim. -/
private theorem one_ne_zero_zmod (p : Nat) [ZMod64.Bounds p] (h : 2 ≤ p) :
    (1 : ZMod64 p) ≠ 0 := by
  intro hzero
  have hcast : ((1 : Nat) : ZMod64 p) = ((0 : Nat) : ZMod64 p) := by
    simpa using hzero
  have hmod := (ZMod64.natCast_eq_natCast_iff (p := p) 1 0).mp hcast
  -- `1 % p = 0 % p` — but `p ≥ 2` makes `1 % p = 1` and `0 % p = 0`.
  have : (1 : Nat) % p = 1 := Nat.mod_eq_of_lt (by omega)
  have hzero_mod : (0 : Nat) % p = 0 := Nat.zero_mod _
  rw [this, hzero_mod] at hmod
  exact Nat.one_ne_zero hmod

/-- Build a monic polynomial of exact degree `deg` whose lower
coefficients are pseudo-random.  Requires `2 ≤ p` so `1 ≠ 0`. -/
private def randomMonicPoly (p : Nat) [ZMod64.Bounds p] (h : 2 ≤ p)
    (seed deg : Nat) : FpPoly p :=
  { coeffs := monicArray p seed deg
    normalized := by
      right
      intro hback
      have h1 : (monicArray p seed deg).back? = some (1 : ZMod64 p) :=
        monicArray_back? p seed deg
      rw [hback] at h1
      have heq : (0 : ZMod64 p) = (1 : ZMod64 p) := Option.some.inj h1
      exact (one_ne_zero_zmod p h) heq.symm }

private theorem randomMonicPoly_monic
    (p : Nat) [ZMod64.Bounds p] (h : 2 ≤ p) (seed deg : Nat) :
    DensePoly.Monic (randomMonicPoly p h seed deg) := by
  unfold DensePoly.Monic DensePoly.leadingCoeff randomMonicPoly
  simp [monicArray_back?]
  rfl

/-! ## Coefficient ↔ Int conversion -/

private def coeffInts {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : List Int :=
  f.toArray.toList.map (fun c => (c.toNat : Int))

/-! ## gcd output normalisation -/

/-- Scale a non-zero polynomial so its leading coefficient becomes `1`.
Returns `f` unchanged when `f.isZero`. -/
private def monicNormalize {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : FpPoly p :=
  if f.isZero then f
  else DensePoly.scale (ZMod64.inv (DensePoly.leadingCoeff f)) f

/-! ## Square-free output normalisation -/

/-- Lexicographic compare on `List Int`. -/
private def lexLessInts : List Int → List Int → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a < b then true
    else if a == b then lexLessInts as bs
    else false

/-- Total order on factor records, by coefficient list then multiplicity. -/
private def factorLess (x y : List Int × Nat) : Bool :=
  if lexLessInts x.1 y.1 then true
  else if decide (x.1 = y.1) then x.2 < y.2
  else false

/-- Canonical form `(unit, sortedFactors)` for a square-free
decomposition.  Constant factors and leading coefficients are hoisted
into `unit`; the remaining monic factors are sorted by `factorLess`. -/
private def normalizeSqFree {p : Nat} [ZMod64.Bounds p]
    (decomp : SquareFreeDecomposition p) : ZMod64 p × List (List Int × Nat) :=
  let go : (ZMod64 p × List (List Int × Nat)) →
      SquareFreeFactor p →
      (ZMod64 p × List (List Int × Nat)) :=
    fun (state : ZMod64 p × List (List Int × Nat)) sf =>
      let (unit, factors) := state
      let f := sf.factor
      let m := sf.multiplicity
      if f.size ≤ 1 then
        let c := f.coeff 0
        (unit * c ^ m, factors)
      else
        let lead := DensePoly.leadingCoeff f
        let monic := DensePoly.scale (ZMod64.inv lead) f
        (unit * lead ^ m, (coeffInts monic, m) :: factors)
  let (unit, rawFactors) := decomp.factors.foldl go (decomp.unit, [])
  (unit, rawFactors.toArray.qsort factorLess |>.toList)

/-! ## JSON value builders for square-free output -/

private def jsonNat (n : Nat) : String := toString n
private def jsonInt (n : Int) : String := toString n

private def jsonIntList (xs : List Int) : String := Id.run do
  let mut out := "["
  let mut first := true
  for x in xs do
    if first then first := false else out := out.push ','
    out := out ++ jsonInt x
  return out.push ']'

private def jsonFactor (factor : List Int × Nat) : String :=
  "[" ++ jsonIntList factor.1 ++ "," ++ jsonNat factor.2 ++ "]"

private def jsonFactorList (xs : List (List Int × Nat)) : String := Id.run do
  let mut out := "["
  let mut first := true
  for f in xs do
    if first then first := false else out := out.push ','
    out := out ++ jsonFactor f
  return out.push ']'

/-- A square-free result value: `[unit, [[factor, mult], ...]]`. -/
private def sqFreeValue (unit : Int) (factors : List (List Int × Nat)) : String :=
  "[" ++ jsonInt unit ++ "," ++ jsonFactorList factors ++ "]"

/-! ## Per-fixture emission helpers -/

private def caseName (op : String) (p deg : Nat) : String :=
  op ++ "/p" ++ toString p ++ "/deg" ++ toString deg

/-- Emit a `mul` fixture: two random factors and their product. -/
private def emitMul (p : Nat) [ZMod64.Bounds p] (deg : Nat) : IO Unit := do
  let case := caseName "mul" p deg
  let a := randomPoly p (deg * 17 + 1) deg
  let b := randomPoly p (deg * 17 + 2) deg
  emitPolyFixture lib (case ++ "/left")  (coeffInts a) (some (p : Int))
  emitPolyFixture lib (case ++ "/right") (coeffInts b) (some (p : Int))
  emitResult lib case "mul" (polyValue (coeffInts (a * b)))

/-- Emit a `gcd` fixture: two random polynomials and their monic gcd. -/
private def emitGcd (p : Nat) [ZMod64.Bounds p] (deg : Nat) : IO Unit := do
  let case := caseName "gcd" p deg
  let a := randomPoly p (deg * 23 + 1) deg
  let b := randomPoly p (deg * 23 + 2) deg
  let g := monicNormalize (DensePoly.gcd a b)
  emitPolyFixture lib (case ++ "/left")  (coeffInts a) (some (p : Int))
  emitPolyFixture lib (case ++ "/right") (coeffInts b) (some (p : Int))
  emitResult lib case "gcd" (polyValue (coeffInts g))

/-- Emit a `divrem` fixture: dividend, divisor, and `(quot, rem)`. -/
private def emitDivRem (p : Nat) [ZMod64.Bounds p] (deg : Nat) : IO Unit := do
  let case := caseName "divrem" p deg
  let a := randomPoly p (deg * 31 + 1) deg
  let b := randomPoly p (deg * 31 + 2) (deg / 2 + 1)
  let q := DensePoly.div a b
  let r := DensePoly.mod a b
  emitPolyFixture lib (case ++ "/dividend") (coeffInts a) (some (p : Int))
  emitPolyFixture lib (case ++ "/divisor")  (coeffInts b) (some (p : Int))
  emitResult lib case "divrem" (divModValue (coeffInts q) (coeffInts r))

/-- Emit a `frobenius` fixture: base polynomial, monic modulus, and
`base^p mod modulus`. -/
private def emitFrobenius (p : Nat) [ZMod64.Bounds p] (h : 2 ≤ p) (deg : Nat) :
    IO Unit := do
  let case := caseName "frobenius" p deg
  let modulus := randomMonicPoly p h (deg * 41 + 1) deg
  let base := randomPoly p (deg * 41 + 2) (deg - 1)
  let r := powModMonic base modulus (randomMonicPoly_monic p h _ _) p
  emitPolyFixture lib (case ++ "/base") (coeffInts base) (some (p : Int))
  emitPolyFixture lib (case ++ "/mod")  (coeffInts modulus) (some (p : Int))
  emitResult lib case "frobenius" (polyValue (coeffInts r))

/-- Emit a `squarefree` fixture (currently `p = 5` only): input polynomial
plus its canonicalised square-free decomposition. -/
private def emitSquareFreeFive (deg : Nat) : IO Unit := do
  let case := caseName "squarefree" 5 deg
  let f := randomPoly 5 (deg * 53 + 1) deg
  let decomp := squareFreeDecomposition primeFive f
  let (unit, factors) := normalizeSqFree decomp
  emitPolyFixture lib (case ++ "/poly") (coeffInts f) (some (5 : Int))
  emitResult lib case "squarefree"
    (sqFreeValue (unit.toNat : Int) factors)

end Hex.PolyFpEmit

open Hex.PolyFpEmit

private def arithDegrees : List Nat := [8, 16, 32]
private def frobeniusDegrees : List Nat := [6, 10]
private def squareFreeDegrees : List Nat := [8, 12]

def main : IO Unit := do
  -- mul / gcd / divrem at p ∈ {5, 11, 31}
  for d in arithDegrees do emitMul (p := 5)  d
  for d in arithDegrees do emitMul (p := 11) d
  for d in arithDegrees do emitMul (p := 31) d
  for d in arithDegrees do emitGcd (p := 5)  d
  for d in arithDegrees do emitGcd (p := 11) d
  for d in arithDegrees do emitGcd (p := 31) d
  for d in arithDegrees do emitDivRem (p := 5)  d
  for d in arithDegrees do emitDivRem (p := 11) d
  for d in arithDegrees do emitDivRem (p := 31) d
  -- Frobenius `f^p mod g` at degrees 6, 10 over the same primes
  for d in frobeniusDegrees do emitFrobenius (p := 5)  (by decide) d
  for d in frobeniusDegrees do emitFrobenius (p := 11) (by decide) d
  for d in frobeniusDegrees do emitFrobenius (p := 31) (by decide) d
  -- Square-free decomposition over F_5 at degrees 8, 12
  for d in squareFreeDegrees do emitSquareFreeFive d

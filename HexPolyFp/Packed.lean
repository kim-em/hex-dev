module

public import HexPolyFp.Basic

public section

/-!
Packed `Array UInt64` monic-division kernel for `FpPoly` and its
value-correspondence with the reference `FpPoly.modByMonic`.

`FpPoly p = DensePoly (ZMod64 p)` stores coefficients as `Array (ZMod64 p)`,
which boxes every element (`lean_ctor` per coefficient) and allocates per
operation. The packed kernel below mirrors the reference array long-division
loop (`HexPoly/Euclid.lean`) over a bare `Array UInt64`, eliminating the boxing
on the monic-division / Frobenius hot path.

The arithmetic stays overflow-safe: `ZMod64.Bounds p` only gives `p ≤ 2^64`, so
`p` may exceed `2^32` and naive `UInt64` `(a*b) % p` would wrap mod `2^64`. The
word helpers `ZMod64.mulWord` / `ZMod64.subWord` reconstruct residues and reuse
the multi-branch `ZMod64.mul` / `ZMod64.sub` (the former extern-backed by a
`__uint128_t` widening multiply), so the packed kernel equals the reference for
*every* `Bounds p`.

`modByMonicPacked_eq` is the value-correspondence theorem; a later `@[csimp]`
swap of `FpPoly.modByMonic` for `modByMonicPacked` is therefore
behaviour-preserving.
-/

namespace Hex

namespace ZMod64

variable {p : Nat} [Bounds p]

/-- Overflow-safe modular product of two raw words, reconstructing residues and
delegating to the (extern-backed) `ZMod64.mul`. Defined so that
`mulWord p x.val y.val = (x * y).val`. -/
@[expose]
def mulWord (p : Nat) [Bounds p] (a b : UInt64) : UInt64 :=
  (mul (ofNat p a.toNat) (ofNat p b.toNat)).val

/-- Overflow-safe modular difference of two raw words, reconstructing residues
and delegating to `ZMod64.sub`. Defined so that
`subWord p x.val y.val = (x - y).val`. -/
@[expose]
def subWord (p : Nat) [Bounds p] (a b : UInt64) : UInt64 :=
  (sub (ofNat p a.toNat) (ofNat p b.toNat)).val

/-- The backing word of the zero residue is the zero word. -/
@[simp] theorem val_zero : (Zero.zero : ZMod64 p).val = 0 := by
  apply UInt64.toNat_inj.mp
  show (ofNat p 0).val.toNat = (0 : UInt64).toNat
  rw [val_toNat_ofNat]
  simp

/-- A residue's backing word is zero exactly when the residue is zero. -/
theorem val_eq_zero_iff (x : ZMod64 p) : x.val = 0 ↔ x = (Zero.zero : ZMod64 p) := by
  constructor
  · intro h
    apply ZMod64.ext
    rw [h, val_zero]
  · intro h
    rw [h, val_zero]

/-- The word multiply agrees with the residue product read off in words. -/
theorem mulWord_val (x y : ZMod64 p) : mulWord p x.val y.val = (x * y).val := by
  unfold mulWord
  have hx : ofNat p x.val.toNat = x := by
    rw [← ZMod64.toNat_eq_val]; exact ZMod64.ofNat_toNat x
  have hy : ofNat p y.val.toNat = y := by
    rw [← ZMod64.toNat_eq_val]; exact ZMod64.ofNat_toNat y
  rw [hx, hy]
  rfl

/-- The word subtract agrees with the residue difference read off in words. -/
theorem subWord_val (x y : ZMod64 p) : subWord p x.val y.val = (x - y).val := by
  unfold subWord
  have hx : ofNat p x.val.toNat = x := by
    rw [← ZMod64.toNat_eq_val]; exact ZMod64.ofNat_toNat x
  have hy : ofNat p y.val.toNat = y := by
    rw [← ZMod64.toNat_eq_val]; exact ZMod64.ofNat_toNat y
  rw [hx, hy]
  rfl

end ZMod64

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- Pack a residue coefficient array into its backing words. -/
@[expose]
def toWords (a : Array (ZMod64 p)) : Array UInt64 :=
  a.map (fun x => x.val)

/-- Reconstruct a residue coefficient array from raw words. -/
@[expose]
def ofWords (p : Nat) [ZMod64.Bounds p] (a : Array UInt64) : Array (ZMod64 p) :=
  a.map (fun w => ZMod64.ofNat p w.toNat)

@[simp] theorem toWords_size (a : Array (ZMod64 p)) : (toWords a).size = a.size := by
  simp [toWords]

/-- Reading a packed word with default `0` is the residue coefficient read with
default `0`, packed. -/
theorem toWords_getD (a : Array (ZMod64 p)) (i : Nat) :
    (toWords a).getD i (0 : UInt64) = (a.getD i (Zero.zero : ZMod64 p)).val := by
  unfold toWords
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[i]? with
  | none => simp [ZMod64.val_zero]
  | some v => simp

/-- Writing a residue then packing equals packing then writing the word. -/
theorem toWords_set! (a : Array (ZMod64 p)) (i : Nat) (v : ZMod64 p) :
    (toWords a).set! i v.val = toWords (a.set! i v) := by
  simp [toWords, Array.set!_eq_setIfInBounds, Array.map_setIfInBounds]

/-- Packing a zero-filled array gives a zero-word-filled array. -/
theorem toWords_replicate (n : Nat) :
    toWords (Array.replicate n (Zero.zero : ZMod64 p)) = Array.replicate n (0 : UInt64) := by
  simp [toWords, Array.map_replicate, ZMod64.val_zero]

/-- Reconstructing the words of a residue array recovers the original array. -/
theorem ofWords_toWords (a : Array (ZMod64 p)) : ofWords p (toWords a) = a := by
  unfold ofWords toWords
  rw [Array.map_map]
  have hid : ((fun w => ZMod64.ofNat p w.toNat) ∘ (fun x : ZMod64 p => x.val)) = id := by
    funext x
    show ZMod64.ofNat p x.val.toNat = x
    rw [← ZMod64.toNat_eq_val]
    exact ZMod64.ofNat_toNat x
  rw [hid, Array.map_id]

/-- Packed downward degree scan: the highest index below `fuel` with a nonzero
word, mirroring `DensePoly.arrayDegreeAux`. -/
@[expose]
def arrayDegreeAuxPacked (coeffs : Array UInt64) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
      if coeffs.getD fuel 0 = 0 then
        arrayDegreeAuxPacked coeffs fuel
      else
        some fuel

/-- Packed degree: the highest index of a nonzero word, mirroring
`DensePoly.arrayDegree?`. -/
@[expose]
def arrayDegreePacked? (coeffs : Array UInt64) : Option Nat :=
  arrayDegreeAuxPacked coeffs coeffs.size

/-- One packed elimination coefficient write, mirroring
`DensePoly.subtractScaledShiftStep` with overflow-safe word arithmetic. -/
@[expose]
def subtractScaledShiftStepPacked (p : Nat) [ZMod64.Bounds p]
    (q : Array UInt64) (shift : Nat) (coeff : UInt64) (next : Array UInt64) (j : Nat) :
    Array UInt64 :=
  next.set! (shift + j)
    (ZMod64.subWord p (next.getD (shift + j) 0) (ZMod64.mulWord p coeff (q.getD j 0)))

/-- One full packed elimination step `rem - coeff * xˢʰⁱᶠᵗ * q`, mirroring
`DensePoly.subtractScaledShift`. -/
@[expose]
def subtractScaledShiftPacked (p : Nat) [ZMod64.Bounds p]
    (rem q : Array UInt64) (shift : Nat) (coeff : UInt64) : Array UInt64 :=
  (List.range q.size).foldl (subtractScaledShiftStepPacked p q shift coeff) rem

/-- The packed fuel-bounded long-division loop, mirroring
`DensePoly.divModArrayAux`. -/
@[expose]
def divModArrayAuxPacked (p : Nat) [ZMod64.Bounds p]
    (q : Array UInt64) (qDegree : Nat) (scaleLead : UInt64 → UInt64)
    (fuel : Nat) (quot rem : Array UInt64) : Array UInt64 × Array UInt64 :=
  match fuel with
  | 0 => (quot, rem)
  | fuel + 1 =>
      match arrayDegreePacked? rem with
      | none => (quot, rem)
      | some rd =>
          if _hdeg : rd < qDegree then
            (quot, rem)
          else
            let shift := rd - qDegree
            let coeff := scaleLead (rem.getD rd 0)
            let quot := quot.set! shift coeff
            let rem := subtractScaledShiftPacked p rem q shift coeff
            divModArrayAuxPacked p q qDegree scaleLead fuel quot rem

/-- Packed monic division remainder, identical in signature to
`FpPoly.modByMonic` (csimp requirement). Packs both operand arrays, runs the
packed loop with `scaleLead = id` (the divisor is monic), and reconstructs the
remainder. -/
@[expose]
def modByMonicPacked (f g : FpPoly p) (_hmonic : DensePoly.Monic f) : FpPoly p :=
  if f.isZero then
    g
  else
    let qDegree := f.size - 1
    let quotientSize := g.size - qDegree
    let quot := Array.replicate quotientSize (0 : UInt64)
    let qr := divModArrayAuxPacked p (toWords f.toArray) qDegree id g.size quot (toWords g.toArray)
    DensePoly.ofCoeffs (ofWords p qr.2)

/-- Packed degree scan agrees with the reference scan on packed input. -/
theorem arrayDegreeAuxPacked_eq (a : Array (ZMod64 p)) (ceil : Nat) :
    arrayDegreeAuxPacked (toWords a) ceil = DensePoly.arrayDegreeAux a ceil := by
  induction ceil with
  | zero => rfl
  | succ ceil ih =>
      simp only [arrayDegreeAuxPacked, DensePoly.arrayDegreeAux]
      by_cases h : a.getD ceil (Zero.zero : ZMod64 p) = (Zero.zero : ZMod64 p)
      · have hp : (toWords a).getD ceil (0 : UInt64) = 0 := by
          rw [toWords_getD, h, ZMod64.val_zero]
        rw [if_pos hp, if_pos h, ih]
      · have hp : ¬ (toWords a).getD ceil (0 : UInt64) = 0 := by
          rw [toWords_getD]
          intro hc
          exact h ((ZMod64.val_eq_zero_iff _).mp hc)
        rw [if_neg hp, if_neg h]

/-- Packed degree agrees with the reference degree on packed input. -/
theorem arrayDegreePacked?_eq (a : Array (ZMod64 p)) :
    arrayDegreePacked? (toWords a) = DensePoly.arrayDegree? a := by
  unfold arrayDegreePacked? DensePoly.arrayDegree?
  rw [toWords_size]
  exact arrayDegreeAuxPacked_eq a a.size

/-- One packed elimination coefficient write corresponds to the reference write. -/
theorem subtractScaledShiftStepPacked_eq (q : Array (ZMod64 p)) (shift : Nat)
    (coeff : ZMod64 p) (rem : Array (ZMod64 p)) (j : Nat) :
    subtractScaledShiftStepPacked p (toWords q) shift coeff.val (toWords rem) j
      = toWords (DensePoly.subtractScaledShiftStep q shift coeff rem j) := by
  unfold subtractScaledShiftStepPacked DensePoly.subtractScaledShiftStep
  rw [← toWords_set!, toWords_getD, toWords_getD, ZMod64.mulWord_val, ZMod64.subWord_val]

/-- Folding the packed step over any index list corresponds to folding the
reference step. -/
theorem foldl_subtractScaledShiftStepPacked (q : Array (ZMod64 p)) (shift : Nat)
    (coeff : ZMod64 p) (xs : List Nat) (rem : Array (ZMod64 p)) :
    xs.foldl (subtractScaledShiftStepPacked p (toWords q) shift coeff.val) (toWords rem)
      = toWords (xs.foldl (DensePoly.subtractScaledShiftStep q shift coeff) rem) := by
  induction xs generalizing rem with
  | nil => rfl
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [subtractScaledShiftStepPacked_eq]
      exact ih (DensePoly.subtractScaledShiftStep q shift coeff rem j)

/-- A full packed elimination step corresponds to the reference step. -/
theorem subtractScaledShiftPacked_eq (rem q : Array (ZMod64 p)) (shift : Nat)
    (coeff : ZMod64 p) :
    subtractScaledShiftPacked p (toWords rem) (toWords q) shift coeff.val
      = toWords (DensePoly.subtractScaledShift rem q shift coeff) := by
  unfold subtractScaledShiftPacked DensePoly.subtractScaledShift
  rw [toWords_size]
  exact foldl_subtractScaledShiftStepPacked q shift coeff (List.range q.size) rem

/-- The packed long-division loop corresponds, coordinatewise, to the reference
loop with `scaleLead = id`. -/
theorem divModArrayAuxPacked_eq (q : Array (ZMod64 p)) (qDegree : Nat) (fuel : Nat)
    (quot rem : Array (ZMod64 p)) :
    divModArrayAuxPacked p (toWords q) qDegree id fuel (toWords quot) (toWords rem)
      = (toWords (DensePoly.divModArrayAux q qDegree id fuel quot rem).1,
         toWords (DensePoly.divModArrayAux q qDegree id fuel quot rem).2) := by
  induction fuel generalizing quot rem with
  | zero => rfl
  | succ fuel ih =>
      simp only [divModArrayAuxPacked, DensePoly.divModArrayAux, id_eq, arrayDegreePacked?_eq]
      cases h : DensePoly.arrayDegree? rem with
      | none => rfl
      | some rd =>
          by_cases hlt : rd < qDegree
          · simp only [dif_pos hlt]
          · simp only [dif_neg hlt, toWords_getD, toWords_set!, subtractScaledShiftPacked_eq]
            exact ih (quot.set! (rd - qDegree) (rem.getD rd (Zero.zero : ZMod64 p)))
              (DensePoly.subtractScaledShift rem q (rd - qDegree)
                (rem.getD rd (Zero.zero : ZMod64 p)))

/-- **Value correspondence.** The packed monic-division remainder equals the
reference `FpPoly.modByMonic` for every modulus `p` (every `Bounds p`). -/
theorem modByMonicPacked_eq (f g : FpPoly p) (hmonic : DensePoly.Monic f) :
    FpPoly.modByMonic f g hmonic = modByMonicPacked f g hmonic := by
  rw [FpPoly.modByMonic, DensePoly.modByMonic, DensePoly.divModMonic, DensePoly.divModArray]
  unfold modByMonicPacked
  by_cases hz : f.isZero
  · simp [hz]
  · rw [if_neg hz, if_neg hz]
    dsimp only
    rw [← toWords_replicate (p := p) (g.size - (f.size - 1))]
    simp only [divModArrayAuxPacked_eq, ofWords_toWords]

end FpPoly

end Hex

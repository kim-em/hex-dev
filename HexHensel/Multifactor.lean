import HexHensel.Linear

/-!
Executable multifactor Hensel lifting surface.

This module exposes the ordered product convention used by downstream
factorization code and implements a sequential multifactor lift by repeatedly
reducing the problem to the binary Hensel lift.
-/

namespace Array

/-- Ordered product of integer polynomial factors, using left-fold order. -/
def polyProduct (factors : Array Hex.ZPoly) : Hex.ZPoly :=
  factors.foldl (· * ·) 1

end Array

namespace Hex

namespace ZPoly

/--
Extended gcd witnesses scaled so their Bezout combination is monic when the
raw Euclidean gcd is a nonzero constant unit.
-/
def normalizedXGCD
    (p : Nat) [ZMod64.Bounds p]
    (g h : ZPoly) : DensePoly.XGCDResult (ZMod64 p) :=
  let raw := DensePoly.xgcd (modP p g) (modP p h)
  let unitInv := (DensePoly.leadingCoeff raw.gcd)⁻¹
  { gcd := DensePoly.scale unitInv raw.gcd
    left := DensePoly.scale unitInv raw.left
    right := DensePoly.scale unitInv raw.right }

private def multifactorLiftList
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) : List ZPoly → Array ZPoly
  | [] => #[]
  | [_g] => #[reduceModPow f p k]
  | g :: rest =>
      let restFactors := rest.toArray
      let h := Array.polyProduct restFactors
      let xgcd := normalizedXGCD p g h
      let lifted := henselLift p k f g h xgcd.left xgcd.right
      #[lifted.g] ++ multifactorLiftList p k lifted.h rest

/--
Lift an ordered array of factors from congruence modulo `p` to congruence
modulo `p^k`.
-/
def multifactorLift
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly) : Array ZPoly :=
  multifactorLiftList p k f factors.toList

/--
Recursive preconditions required by the sequential multifactor lift.

Each nontrivial split must supply exactly the invariant package consumed by
`henselLift_spec`, and the recursive tail must satisfy the same contract for
the lifted complementary factor.
-/
def MultifactorLiftInvariant
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) : List ZPoly → Prop
  | [] => ZPoly.congr 1 f (p ^ k)
  | [_g] => True
  | g :: rest =>
      let h := Array.polyProduct rest.toArray
      let xgcd := normalizedXGCD p g h
      let lifted := henselLift p k f g h xgcd.left xgcd.right
      LinearLiftLoopInvariant p 1 f xgcd.left xgcd.right
        { g := reduceModPow g p 1
          h := reduceModPow h p 1 } ∧
        (∀ (n : Nat) (state : LinearLiftResult),
          1 ≤ n →
          LinearLiftLoopInvariant p n f xgcd.left xgcd.right state →
          LinearLiftStepDegreeInvariant p n f xgcd.left xgcd.right state) ∧
        (∀ (n : Nat) (state : LinearLiftResult),
          1 ≤ n →
          LinearLiftLoopInvariant p n f xgcd.left xgcd.right state →
          let next := linearHenselStep p n f state.g state.h xgcd.left xgcd.right
          ZPoly.congr
            (FpPoly.liftToZ
              (xgcd.left * ZPoly.modP p next.g + xgcd.right * ZPoly.modP p next.h))
            1 p) ∧
        MultifactorLiftInvariant p k lifted.h rest

/-- Left identity for `ZPoly` multiplication, used to reason about
`Array.polyProduct` as a left fold from `1`. Shared by the linear and
quadratic multifactor proofs. -/
theorem one_mul_zpoly (g : ZPoly) :
    (1 : ZPoly) * g = g := by
  rw [DensePoly.mul_comm_poly (S := Int), DensePoly.mul_one_right_poly]

/-- `Array.polyProduct` of a singleton array is just the element. -/
theorem polyProduct_singleton (g : ZPoly) :
    Array.polyProduct #[g] = g := by
  simpa [Array.polyProduct] using one_mul_zpoly g

/-- Folding `(· * ·)` over a `List ZPoly` with seed `g` factors out as
`g` times the same fold with seed `1`. The key step for splitting
`Array.polyProduct (#[g] ++ rest)`. -/
theorem list_foldl_mul_eq_mul_foldl_one (g : ZPoly) (xs : List ZPoly) :
    xs.foldl (fun acc factor => acc * factor) g =
      g * xs.foldl (fun acc factor => acc * factor) 1 := by
  induction xs generalizing g with
  | nil =>
      simpa using (DensePoly.mul_one_right_poly (S := Int) g).symm
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [one_mul_zpoly]
      calc
        xs.foldl (fun acc factor => acc * factor) (g * x) =
            (g * x) * xs.foldl (fun acc factor => acc * factor) 1 := ih (g * x)
        _ = g * (x * xs.foldl (fun acc factor => acc * factor) 1) := by
            rw [DensePoly.mul_assoc_poly (S := Int)]
        _ = g * xs.foldl (fun acc factor => acc * factor) x := by
            rw [ih x]

/-- Splitting `Array.polyProduct` across a singleton prepend: the head
factors out as a left multiplication. Used to relate the multifactor
recursion tree to the public ordered-product convention. -/
theorem polyProduct_singleton_append (g : ZPoly) (rest : Array ZPoly) :
    Array.polyProduct (#[g] ++ rest) = g * Array.polyProduct rest := by
  cases rest with
  | mk xs =>
      simpa [Array.polyProduct, one_mul_zpoly] using
        list_foldl_mul_eq_mul_foldl_one g xs

/-- `Array.polyProduct` of the empty array is the multiplicative unit. -/
theorem polyProduct_empty :
    Array.polyProduct (#[] : Array ZPoly) = 1 :=
  rfl

/-- `Array.polyProduct` splits as a product across array concatenation. -/
theorem polyProduct_append (xs ys : Array ZPoly) :
    Array.polyProduct (xs ++ ys) =
      Array.polyProduct xs * Array.polyProduct ys := by
  rw [Array.polyProduct, Array.foldl_append]
  cases ys with
  | mk ylist =>
      simpa [Array.polyProduct] using list_foldl_mul_eq_mul_foldl_one
        (Array.foldl (fun acc factor => acc * factor) 1 xs) ylist

/-- `Array.polyProduct` over `(g :: rest).toArray` factors the head out as a
left multiplication. The `List`-flavoured analogue of
`polyProduct_singleton_append`. -/
theorem polyProduct_cons_toArray (g : ZPoly) (rest : List ZPoly) :
    Array.polyProduct (g :: rest).toArray =
      g * Array.polyProduct rest.toArray := by
  simpa [Array.polyProduct, one_mul_zpoly] using
    (list_foldl_mul_eq_mul_foldl_one g rest)

private theorem multifactorLiftList_spec
    (p k : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f : ZPoly) (factors : List ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : MultifactorLiftInvariant p k f factors) :
    ZPoly.congr (Array.polyProduct (multifactorLiftList p k f factors)) f (p ^ k) := by
  induction factors generalizing f with
  | nil =>
      simpa [multifactorLiftList, Array.polyProduct, MultifactorLiftInvariant] using hinv
  | cons g rest ih =>
      cases rest with
      | nil =>
          have hpow : 0 < p ^ k := Nat.pow_pos (Nat.zero_lt_of_lt hp)
          simpa [multifactorLiftList, polyProduct_singleton] using
            ZPoly.congr_reduceModPow f p k hpow
      | cons h tail =>
          let restFactors := (h :: tail).toArray
          let splitProduct := Array.polyProduct restFactors
          let xgcd := normalizedXGCD p g splitProduct
          let lifted := henselLift p k f g splitProduct xgcd.left xgcd.right
          rcases hinv with ⟨hstart, hstepDegree, hstepBezout, htail⟩
          have htailCongr :
              ZPoly.congr
                (Array.polyProduct (multifactorLiftList p k lifted.h (h :: tail)))
                lifted.h
                (p ^ k) := by
            exact ih lifted.h htail
          have hsplit :
              ZPoly.congr (lifted.g * lifted.h) f (p ^ k) := by
            simpa [lifted, splitProduct, restFactors, xgcd] using
              henselLift_spec p k f g splitProduct xgcd.left xgcd.right
                hk hp hstart hstepDegree hstepBezout
          have hprod :
              ZPoly.congr
                (lifted.g *
                  Array.polyProduct (multifactorLiftList p k lifted.h (h :: tail)))
                (lifted.g * lifted.h)
                (p ^ k) := by
            exact ZPoly.congr_mul _ _ _ _ (p ^ k)
              (ZPoly.congr_refl lifted.g (p ^ k))
              htailCongr
          have hcombined :
              ZPoly.congr
                (lifted.g *
                  Array.polyProduct (multifactorLiftList p k lifted.h (h :: tail)))
                f
                (p ^ k) :=
            ZPoly.congr_trans _ _ _ (p ^ k) hprod hsplit
          simpa [multifactorLiftList, restFactors, splitProduct, xgcd, lifted,
            polyProduct_singleton_append] using hcombined

/--
The product of the lifted factors is congruent to `f` modulo `p^k`, provided
each recursive binary split supplies the linear Hensel invariant package.
-/
theorem multifactorLift_spec
    (p k : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f : ZPoly) (factors : Array ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : MultifactorLiftInvariant p k f factors.toList) :
    ZPoly.congr (Array.polyProduct (multifactorLift p k f factors)) f (p ^ k) := by
  simpa [multifactorLift] using
    multifactorLiftList_spec p k f factors.toList hk hp hinv

end ZPoly

end Hex

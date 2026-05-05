import HexHensel.Multifactor
import HexHensel.Quadratic

/-!
Quadratic multifactor Hensel lifting.

This module exposes `multifactorLiftQuadratic`, the production multifactor
Hensel lifter named on equal footing with `multifactorLift` in
`hex-hensel`. The implementation reuses the per-step quadratic primitive
`quadraticHenselStep` inside a sequential split tree that mirrors
`multifactorLift`. Iteration to the requested precision `p^k` is handled
by a doubling loop on the Bezout-witnessed `QuadraticLiftResult`.

The companion theorem states the ordered-product congruence contract for
the lifted array. The linear-vs-quadratic agreement obligation lives in
`hex-hensel-mathlib`.
-/

namespace Hex

namespace ZPoly

/-- Iterate `quadraticHenselStep` on a Bezout-witnessed factorisation,
doubling the modulus exponent each time. The first index is the current
modulus exponent; the second is the number of remaining doubling steps. -/
private def iterateQuadraticHensel
    (p : Nat) [ZMod64.Bounds p] (f : ZPoly) :
    Nat → Nat → QuadraticLiftResult → QuadraticLiftResult
  | _current, 0, acc => acc
  | current, fuel + 1, acc =>
      let m := p ^ current
      let next := quadraticHenselStep m f acc.g acc.h acc.s acc.t
      iterateQuadraticHensel p f (2 * current) fuel next

/-- Lift a Bezout-witnessed factorisation modulo `p` to one valid modulo
`p^k` by iterating `quadraticHenselStep`.

`k` doubling steps starting from modulus `p` reach modulus `p^(2^k)`,
which dominates `p^k` for all `k`; the final result is reduced modulo
`p^k` to expose the requested precision. -/
def henselLiftQuadratic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly) : QuadraticLiftResult :=
  let init : QuadraticLiftResult := { g, h, s, t }
  let lifted := iterateQuadraticHensel p f 1 k init
  { g := ZPoly.reduceModPow lifted.g p k
    h := ZPoly.reduceModPow lifted.h p k
    s := ZPoly.reduceModPow lifted.s p k
    t := ZPoly.reduceModPow lifted.t p k }

private def multifactorLiftQuadraticList
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) : List ZPoly → Array ZPoly
  | [] => #[]
  | [_g] => #[ZPoly.reduceModPow f p k]
  | g :: rest =>
      let restFactors := rest.toArray
      let h := Array.polyProduct restFactors
      let xgcd := ZPoly.normalizedXGCD p g h
      let s := FpPoly.liftToZ xgcd.left
      let t := FpPoly.liftToZ xgcd.right
      let lifted := henselLiftQuadratic p k f g h s t
      #[lifted.g] ++ multifactorLiftQuadraticList p k lifted.h rest

/--
Quadratic multifactor Hensel lift.

Lifts an ordered array of factors of `f` from congruence modulo `p` to
congruence modulo `p^k` using the doubling step `quadraticHenselStep`
inside the same sequential split tree as `multifactorLift`.
-/
def multifactorLiftQuadratic
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly) : Array ZPoly :=
  multifactorLiftQuadraticList p k f factors.toList

/-- The proof state carried by one quadratic Hensel loop modulus. -/
def QuadraticLiftLoopInvariant
    (m : Nat) (f : ZPoly) (acc : QuadraticLiftResult) : Prop :=
  ZPoly.congr (acc.g * acc.h) f m ∧
    ZPoly.congr (acc.s * acc.g + acc.t * acc.h) 1 m ∧
    DensePoly.Monic acc.g

/--
One quadratic step preserves the loop invariant while replacing `m` by `m*m`.

This is the local invariant-preservation surface consumed by the quadratic
doubling loop.
-/
theorem quadraticLiftLoopInvariant_step
    (m : Nat) (f : ZPoly) (acc : QuadraticLiftResult)
    (hm : 1 < m)
    (hinv : QuadraticLiftLoopInvariant m f acc) :
    let next := quadraticHenselStep m f acc.g acc.h acc.s acc.t
    QuadraticLiftLoopInvariant (m * m) f next := by
  rcases hinv with ⟨hprod, hbez, hmonic⟩
  intro next
  have hstep :
      ZPoly.congr (next.g * next.h) f (m * m) ∧
        ZPoly.congr (next.s * next.g + next.t * next.h) 1 (m * m) := by
    simpa [next] using
      quadraticHenselStep_spec m f acc.g acc.h acc.s acc.t hm hprod hbez hmonic
  exact
    ⟨hstep.1, hstep.2,
      by
        simpa [next] using
          quadraticHenselStep_monic m f acc.g acc.h acc.s acc.t hm hmonic⟩

private theorem congr_of_modulus_dvd
    (f g : ZPoly) {m n : Nat}
    (hmn : m ∣ n)
    (hfg : ZPoly.congr f g n) :
    ZPoly.congr f g m := by
  intro i
  have hmnInt : (m : Int) ∣ (n : Int) := by
    exact_mod_cast hmn
  exact Int.emod_eq_zero_of_dvd
    (Int.dvd_trans hmnInt (Int.dvd_of_emod_eq_zero (hfg i)))

private theorem congr_of_pow_le
    (p a b : Nat) (f g : ZPoly)
    (hab : a ≤ b)
    (hfg : ZPoly.congr f g (p ^ b)) :
    ZPoly.congr f g (p ^ a) :=
  congr_of_modulus_dvd f g (Nat.pow_dvd_pow p hab) hfg

private theorem le_two_pow_self (k : Nat) : k ≤ 2 ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.pow_succ]
      have hpow_pos : 1 ≤ 2 ^ k := by
        exact Nat.succ_le_of_lt (Nat.pow_pos (by omega : 0 < 2))
      omega

private theorem iterateQuadraticHensel_invariant
    (p : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (current fuel : Nat) (acc : QuadraticLiftResult)
    (hp : 1 < p)
    (hcurrent : 1 ≤ current)
    (hinv : QuadraticLiftLoopInvariant (p ^ current) f acc) :
    QuadraticLiftLoopInvariant (p ^ (current * 2 ^ fuel)) f
      (iterateQuadraticHensel p f current fuel acc) := by
  induction fuel generalizing current acc with
  | zero =>
      simpa [iterateQuadraticHensel] using hinv
  | succ fuel ih =>
      let m := p ^ current
      let next := quadraticHenselStep m f acc.g acc.h acc.s acc.t
      have hm : 1 < m := by
        exact Nat.one_lt_pow (Nat.ne_of_gt hcurrent) hp
      have hnext :
          QuadraticLiftLoopInvariant (p ^ (2 * current)) f next := by
        have hstep :
            QuadraticLiftLoopInvariant (m * m) f next := by
          simpa [m, next] using
            quadraticLiftLoopInvariant_step m f acc hm hinv
        have hpow : m * m = p ^ (2 * current) := by
          dsimp [m]
          rw [← Nat.pow_add]
          congr
          omega
        simpa [hpow] using hstep
      have htail :
          QuadraticLiftLoopInvariant (p ^ ((2 * current) * 2 ^ fuel)) f
            (iterateQuadraticHensel p f (2 * current) fuel next) :=
        ih (current := 2 * current) (acc := next) (by omega) hnext
      have hexp : (2 * current) * 2 ^ fuel = current * 2 ^ (fuel + 1) := by
        rw [Nat.pow_succ]
        calc
          2 * current * 2 ^ fuel = current * 2 * 2 ^ fuel := by
            rw [Nat.mul_comm 2 current]
          _ = current * (2 * 2 ^ fuel) := by
            rw [Nat.mul_assoc]
          _ = current * (2 ^ fuel * 2) := by
            rw [Nat.mul_comm 2 (2 ^ fuel)]
      have htail' :
          QuadraticLiftLoopInvariant (p ^ (current * 2 ^ (fuel + 1))) f
            (iterateQuadraticHensel p f (2 * current) fuel next) := by
        simpa [hexp] using htail
      simpa [iterateQuadraticHensel, m, next] using htail'

private theorem congr_mul_reduceModPow_pair
    (p k : Nat) [ZMod64.Bounds p] (g h : ZPoly) :
    ZPoly.congr
      (ZPoly.reduceModPow g p k * ZPoly.reduceModPow h p k)
      (g * h)
      (p ^ k) := by
  apply ZPoly.congr_mul
  · exact ZPoly.congr_reduceModPow g p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))
  · exact ZPoly.congr_reduceModPow h p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))

/-- The binary quadratic wrapper lifts a factorisation to congruence modulo `p^k`. -/
theorem henselLiftQuadratic_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (_hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    let lifted := henselLiftQuadratic p k f g h s t
    ZPoly.congr (lifted.g * lifted.h) f (p ^ k) := by
  let init : QuadraticLiftResult := { g, h, s, t }
  let looped := iterateQuadraticHensel p f 1 k init
  have hstart : QuadraticLiftLoopInvariant (p ^ 1) f init := by
    simpa [init] using hinv
  have hloop :
      QuadraticLiftLoopInvariant (p ^ (1 * 2 ^ k)) f looped := by
    simpa [looped] using
      iterateQuadraticHensel_invariant p f 1 k init hp (by omega) hstart
  have hprod_loop_k : ZPoly.congr (looped.g * looped.h) f (p ^ k) := by
    have hprod_loop :
        ZPoly.congr (looped.g * looped.h) f (p ^ (2 ^ k)) := by
      simpa using hloop.1
    exact congr_of_pow_le p k (2 ^ k) (looped.g * looped.h) f
      (le_two_pow_self k) hprod_loop
  have hred :
      ZPoly.congr
        (ZPoly.reduceModPow looped.g p k * ZPoly.reduceModPow looped.h p k)
        (looped.g * looped.h)
        (p ^ k) :=
    congr_mul_reduceModPow_pair p k looped.g looped.h
  exact
    ZPoly.congr_trans
      (ZPoly.reduceModPow looped.g p k * ZPoly.reduceModPow looped.h p k)
      (looped.g * looped.h)
      f
      (p ^ k)
      hred
      hprod_loop_k

/--
Recursive preconditions required by the sequential quadratic multifactor lift.

Each nontrivial split carries the initial quadratic loop invariant needed by
`henselLiftQuadratic`; the recursive tail carries the same contract for the
lifted complementary factor.
-/
def QuadraticMultifactorLiftInvariant
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) : List ZPoly → Prop
  | [] => ZPoly.congr 1 f (p ^ k)
  | [_g] => True
  | g :: rest =>
      let h := Array.polyProduct rest.toArray
      let xgcd := normalizedXGCD p g h
      let s := FpPoly.liftToZ xgcd.left
      let t := FpPoly.liftToZ xgcd.right
      let lifted := henselLiftQuadratic p k f g h s t
      QuadraticLiftLoopInvariant p f { g, h, s, t } ∧
        QuadraticMultifactorLiftInvariant p k lifted.h rest

private theorem one_mul_zpoly (g : ZPoly) :
    (1 : ZPoly) * g = g := by
  rw [DensePoly.mul_comm_poly (S := Int), DensePoly.mul_one_right_poly]

private theorem polyProduct_singleton (g : ZPoly) :
    Array.polyProduct #[g] = g := by
  simpa [Array.polyProduct] using one_mul_zpoly g

private theorem list_foldl_mul_eq_mul_foldl_one (g : ZPoly) (xs : List ZPoly) :
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

private theorem polyProduct_singleton_append (g : ZPoly) (rest : Array ZPoly) :
    Array.polyProduct (#[g] ++ rest) = g * Array.polyProduct rest := by
  cases rest with
  | mk xs =>
      simpa [Array.polyProduct, one_mul_zpoly] using
        list_foldl_mul_eq_mul_foldl_one g xs

private theorem multifactorLiftQuadraticList_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : List ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticMultifactorLiftInvariant p k f factors) :
    ZPoly.congr
      (Array.polyProduct (multifactorLiftQuadraticList p k f factors))
      f
      (p ^ k) := by
  induction factors generalizing f with
  | nil =>
      simpa [multifactorLiftQuadraticList, Array.polyProduct,
        QuadraticMultifactorLiftInvariant] using hinv
  | cons g rest ih =>
      cases rest with
      | nil =>
          have hpow : 0 < p ^ k := Nat.pow_pos (ZMod64.Bounds.pPos (p := p))
          simpa [multifactorLiftQuadraticList, polyProduct_singleton] using
            ZPoly.congr_reduceModPow f p k hpow
      | cons h tail =>
          let restFactors := (h :: tail).toArray
          let splitProduct := Array.polyProduct restFactors
          let xgcd := normalizedXGCD p g splitProduct
          let s := FpPoly.liftToZ xgcd.left
          let t := FpPoly.liftToZ xgcd.right
          let lifted := henselLiftQuadratic p k f g splitProduct s t
          rcases hinv with ⟨hstart, htail⟩
          have htailCongr :
              ZPoly.congr
                (Array.polyProduct
                  (multifactorLiftQuadraticList p k lifted.h (h :: tail)))
                lifted.h
                (p ^ k) := by
            exact ih lifted.h htail
          have hsplit :
              ZPoly.congr (lifted.g * lifted.h) f (p ^ k) := by
            simpa [lifted, splitProduct, restFactors, xgcd, s, t] using
              henselLiftQuadratic_spec p k f g splitProduct s t hk hp hstart
          have hprod :
              ZPoly.congr
                (lifted.g *
                  Array.polyProduct
                    (multifactorLiftQuadraticList p k lifted.h (h :: tail)))
                (lifted.g * lifted.h)
                (p ^ k) := by
            exact ZPoly.congr_mul _ _ _ _ (p ^ k)
              (ZPoly.congr_refl lifted.g (p ^ k))
              htailCongr
          have hcombined :
              ZPoly.congr
                (lifted.g *
                  Array.polyProduct
                    (multifactorLiftQuadraticList p k lifted.h (h :: tail)))
                f
                (p ^ k) :=
            ZPoly.congr_trans _ _ _ (p ^ k) hprod hsplit
          simpa [multifactorLiftQuadraticList, restFactors, splitProduct, xgcd,
            s, t, lifted, polyProduct_singleton_append] using hcombined

/--
The product of the lifted factors is congruent to `f` modulo `p^k`,
under the recursive precondition package consumed by the quadratic
multifactor lifting tree.

The lift-uniqueness companion (linear-vs-quadratic agreement after
canonicalisation) lives in `hex-hensel-mathlib`.
-/
theorem multifactorLiftQuadratic_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticMultifactorLiftInvariant p k f factors.toList) :
    ZPoly.congr (Array.polyProduct (multifactorLiftQuadratic p k f factors))
      f (p ^ k) := by
  simpa [multifactorLiftQuadratic] using
    multifactorLiftQuadraticList_spec p k f factors.toList hk hp hinv

end ZPoly

end Hex

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

/-- Number of quadratic-doubling steps needed to reach precision `p^k`
from data valid modulo `p`. -/
def quadraticDoublingSteps (k : Nat) : Nat :=
  if k ≤ 1 then 0 else (k - 1).log2 + 1

/-- Lift a Bezout-witnessed factorisation modulo `p` to one valid modulo
`p^k` by iterating `quadraticHenselStep`.

The wrapper performs only `ceil(log₂ k)` doubling steps, since after
`fuel` steps the loop has reached exponent `2^fuel`. The final result is
reduced modulo `p^k` to expose exactly the requested precision. -/
def henselLiftQuadratic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly) : QuadraticLiftResult :=
  let init : QuadraticLiftResult := { g, h, s, t }
  let lifted := iterateQuadraticHensel p f 1 (quadraticDoublingSteps k) init
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

/-- Constructor for the initial quadratic split invariant from the three
proof obligations supplied by factor-product, Bezout, and monicness facts. -/
theorem QuadraticLiftLoopInvariant.of_product_bezout_monic
    {m : Nat} {f g h s t : ZPoly}
    (hprod : ZPoly.congr (g * h) f m)
    (hbezout : ZPoly.congr (s * g + t * h) 1 m)
    (hg_monic : DensePoly.Monic g) :
    QuadraticLiftLoopInvariant m f { g, h, s, t } :=
  ⟨hprod, hbezout, hg_monic⟩

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

private theorem le_two_pow_quadraticDoublingSteps (k : Nat) :
    k ≤ 2 ^ quadraticDoublingSteps k := by
  by_cases hk : k ≤ 1
  · simp [quadraticDoublingSteps, hk]
  · have hpred_lt : k - 1 < 2 ^ ((k - 1).log2 + 1) :=
      Nat.lt_log2_self
    simp [quadraticDoublingSteps, hk]
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

/--
Throughout the quadratic doubling loop, the cofactor `acc.h` only changes by
quantities divisible by the current modulus. In particular, the final cofactor
is still congruent to the initial cofactor modulo the base prime `p`.
-/
private theorem iterateQuadraticHensel_h_congr_mod_base
    (p : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (current fuel : Nat) (acc : QuadraticLiftResult)
    (hp : 1 < p)
    (hcurrent : 1 ≤ current)
    (hinv : QuadraticLiftLoopInvariant (p ^ current) f acc) :
    ZPoly.congr (iterateQuadraticHensel p f current fuel acc).h acc.h p := by
  induction fuel generalizing current acc with
  | zero =>
      simpa [iterateQuadraticHensel] using ZPoly.congr_refl acc.h p
  | succ fuel ih =>
      let m := p ^ current
      let next := quadraticHenselStep m f acc.g acc.h acc.s acc.t
      have hm : 1 < m := Nat.one_lt_pow (Nat.ne_of_gt hcurrent) hp
      have hprod_m : ZPoly.congr (acc.g * acc.h) f m := hinv.1
      have hh_step_m : ZPoly.congr next.h acc.h m :=
        (ZPoly.quadraticHenselStep_factor_congr_mod_base m f acc.g acc.h acc.s acc.t
          hm hprod_m).2
      have hp_dvd_m : p ∣ m := by
        dsimp [m]
        have hdvd : p ^ 1 ∣ p ^ current := Nat.pow_dvd_pow p hcurrent
        simpa [Nat.pow_one] using hdvd
      have hh_step_p : ZPoly.congr next.h acc.h p :=
        congr_of_modulus_dvd next.h acc.h hp_dvd_m hh_step_m
      have hnext_inv : QuadraticLiftLoopInvariant (p ^ (2 * current)) f next := by
        have hstep : QuadraticLiftLoopInvariant (m * m) f next := by
          simpa [m, next] using
            quadraticLiftLoopInvariant_step m f acc hm hinv
        have hpow : m * m = p ^ (2 * current) := by
          dsimp [m]
          rw [← Nat.pow_add]
          congr 1
          omega
        simpa [hpow] using hstep
      have htail :
          ZPoly.congr
            (iterateQuadraticHensel p f (2 * current) fuel next).h next.h p :=
        ih (current := 2 * current) (acc := next) (by omega) hnext_inv
      have hresult :
          (iterateQuadraticHensel p f current (fuel + 1) acc) =
            iterateQuadraticHensel p f (2 * current) fuel next := by
        simp [iterateQuadraticHensel, m, next]
      rw [hresult]
      exact ZPoly.congr_trans _ _ _ p htail hh_step_p

/--
The cofactor produced by `henselLiftQuadratic` is congruent to the input
cofactor modulo `p`. The quadratic doubling loop only adjusts `h` by quantities
divisible by `p`, and the final `reduceModPow` cleanup is congruent to its
input modulo `p^k`, hence modulo `p`.

This is the surface used downstream by the multifactor `_of_factorsModP`
boundary theorem: it lets the recursive call on `lifted.h, rest` reuse the
same mod-`p` product hypothesis the caller supplies for the head split.
-/
theorem henselLiftQuadratic_h_congr_mod_base
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    ZPoly.congr (henselLiftQuadratic p k f g h s t).h h p := by
  let init : QuadraticLiftResult := { g, h, s, t }
  let fuel := quadraticDoublingSteps k
  let looped := iterateQuadraticHensel p f 1 fuel init
  have hstart : QuadraticLiftLoopInvariant (p ^ 1) f init := by
    simpa [init] using hinv
  have hloop_h : ZPoly.congr looped.h h p := by
    have hcongr :=
      iterateQuadraticHensel_h_congr_mod_base p f 1 fuel init hp (by omega) hstart
    simpa [init] using hcongr
  have hreduce_pk : ZPoly.congr (ZPoly.reduceModPow looped.h p k) looped.h (p ^ k) :=
    ZPoly.congr_reduceModPow looped.h p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))
  have hreduce_p : ZPoly.congr (ZPoly.reduceModPow looped.h p k) looped.h p := by
    have hpow_one : p ^ 1 = p := Nat.pow_one p
    have hcongr := congr_of_pow_le p 1 k _ _ hk hreduce_pk
    simpa [hpow_one] using hcongr
  have heq : (henselLiftQuadratic p k f g h s t).h = ZPoly.reduceModPow looped.h p k := by
    simp [henselLiftQuadratic, init, fuel, looped]
  rw [heq]
  exact ZPoly.congr_trans _ _ _ p hreduce_p hloop_h

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
  let fuel := quadraticDoublingSteps k
  let looped := iterateQuadraticHensel p f 1 fuel init
  have hstart : QuadraticLiftLoopInvariant (p ^ 1) f init := by
    simpa [init] using hinv
  have hloop :
      QuadraticLiftLoopInvariant (p ^ (1 * 2 ^ fuel)) f looped := by
    simpa [looped] using
      iterateQuadraticHensel_invariant p f 1 fuel init hp (by omega) hstart
  have hprod_loop_k : ZPoly.congr (looped.g * looped.h) f (p ^ k) := by
    have hprod_loop :
        ZPoly.congr (looped.g * looped.h) f (p ^ (2 ^ fuel)) := by
      simpa using hloop.1
    exact congr_of_pow_le p k (2 ^ fuel) (looped.g * looped.h) f
      (le_two_pow_quadraticDoublingSteps k) hprod_loop
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

private theorem int_eq_of_congr_of_bounds
    {a b : Int} {m : Nat}
    (hcongr : (a - b) % (m : Int) = 0)
    (ha_nonneg : 0 ≤ a) (ha_lt : a < (m : Int))
    (hb_nonneg : 0 ≤ b) (hb_lt : b < (m : Int)) :
    a = b := by
  have hmod_eq : a % (m : Int) = b % (m : Int) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hcongr
  rw [Int.emod_eq_of_lt ha_nonneg ha_lt, Int.emod_eq_of_lt hb_nonneg hb_lt] at hmod_eq
  exact hmod_eq

private theorem int_eq_zero_of_mod_zero_of_bounds
    {a : Int} {m : Nat}
    (hm : 1 < m)
    (hmod : a % (m : Int) = 0)
    (ha_nonneg : 0 ≤ a) (ha_lt : a < (m : Int)) :
    a = 0 := by
  exact int_eq_of_congr_of_bounds (by simpa using hmod)
    ha_nonneg ha_lt (by decide) (by exact_mod_cast (Nat.zero_lt_of_lt hm))

/--
If a bounded nonnegative cofactor `h` satisfies a coefficientwise congruence
`g * h ≡ f (mod m)` against monic `g` and `f`, then `h` is monic. The proof
compares the possible top coefficient of `g * h` with the top coefficient of
`f`; the coefficient bounds rule out wraparound modulo `m`.

Consumed by `monic_reduceModPow_of_congr_mul_monic_monic`, which specialises
this to the `reduceModPow`-canonicalised cofactor consumed by
`henselLiftQuadratic_h_monic`.
-/
theorem monic_of_congr_mul_monic_monic
    {g h f : Hex.ZPoly} {m : Nat}
    (hm : 1 < m)
    (hcongr : Hex.ZPoly.congr (g * h) f m)
    (hg_monic : Hex.DensePoly.Monic g)
    (hf_monic : Hex.DensePoly.Monic f)
    (hh_bound_lt : ∀ i, h.coeff i < Int.ofNat m)
    (hh_bound_nonneg : ∀ i, 0 ≤ h.coeff i)
    (hh_ne_zero : h ≠ 0) :
    Hex.DensePoly.Monic h := by
  have hg_ne_zero : g ≠ 0 := by
    intro hg_zero
    have hlead : Hex.DensePoly.leadingCoeff g = (0 : Int) := by
      rw [hg_zero]
      rfl
    rw [hg_monic] at hlead
    omega
  have hf_ne_zero : f ≠ 0 := by
    intro hf_zero
    have hlead : Hex.DensePoly.leadingCoeff f = (0 : Int) := by
      rw [hf_zero]
      rfl
    rw [hf_monic] at hlead
    omega
  have hg_pos : 0 < g.size := Hex.ZPoly.size_pos_of_ne_zero g hg_ne_zero
  have hh_pos : 0 < h.size := Hex.ZPoly.size_pos_of_ne_zero h hh_ne_zero
  have hf_pos : 0 < f.size := Hex.ZPoly.size_pos_of_ne_zero f hf_ne_zero
  let gTop := g.size - 1
  let hTop := h.size - 1
  let fTop := f.size - 1
  have hg_top : g.coeff gTop = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last g hg_pos]
    exact hg_monic
  have hf_top : f.coeff fTop = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last f hf_pos]
    exact hf_monic
  have hprod_size :
      (g * h).size = g.size + h.size - 1 :=
    Hex.ZPoly.mul_size_eq_top_succ_of_nonzero g h hg_pos hh_pos
  have hsum_not_gt : ¬ fTop < gTop + hTop := by
    intro hlt
    have hf_zero : f.coeff (gTop + hTop) = 0 := by
      apply Hex.DensePoly.coeff_eq_zero_of_size_le f
      unfold fTop at hlt
      omega
    have hprod_top :
        (g * h).coeff (gTop + hTop) = h.coeff hTop := by
      have htop := Hex.ZPoly.coeff_mul_top g h hg_pos hh_pos
      unfold gTop hTop
      rw [htop]
      rw [hg_top]
      omega
    have hmod : h.coeff hTop % (m : Int) = 0 := by
      have hc := hcongr (gTop + hTop)
      rw [hprod_top, hf_zero] at hc
      simpa using hc
    have hlead_zero : h.coeff hTop = 0 :=
      int_eq_zero_of_mod_zero_of_bounds hm hmod
        (hh_bound_nonneg hTop) (hh_bound_lt hTop)
    have hlead_ne : h.coeff hTop ≠ 0 := by
      unfold hTop
      exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size h hh_pos
    exact hlead_ne hlead_zero
  have hsum_not_lt : ¬ gTop + hTop < fTop := by
    intro hlt
    have hprod_zero : (g * h).coeff fTop = 0 := by
      apply Hex.DensePoly.coeff_eq_zero_of_size_le (g * h)
      rw [hprod_size]
      unfold gTop hTop fTop at hlt
      omega
    have hbad : (0 : Int) = 1 := by
      have hc := hcongr fTop
      rw [hprod_zero, hf_top] at hc
      exact int_eq_of_congr_of_bounds hc
        (by decide) (by exact_mod_cast (Nat.zero_lt_of_lt hm))
        (by decide) (by exact_mod_cast hm)
    omega
  have hsum_eq : gTop + hTop = fTop := by omega
  have hprod_top_at_f :
      (g * h).coeff fTop = h.coeff hTop := by
    rw [← hsum_eq]
    change (g * h).coeff (g.size - 1 + (h.size - 1)) = h.coeff (h.size - 1)
    rw [Hex.ZPoly.coeff_mul_top g h hg_pos hh_pos]
    have hg_top' : g.coeff (g.size - 1) = (1 : Int) := by
      simpa [gTop] using hg_top
    rw [hg_top']
    omega
  have hlead_one : h.coeff hTop = (1 : Int) := by
    have hc := hcongr fTop
    rw [hprod_top_at_f, hf_top] at hc
    exact int_eq_of_congr_of_bounds hc
      (hh_bound_nonneg hTop) (hh_bound_lt hTop)
      (by decide) (by exact_mod_cast hm)
  rw [Hex.DensePoly.Monic]
  rw [Hex.DensePoly.leadingCoeff_eq_coeff_last h hh_pos]
  unfold hTop at hlead_one
  exact hlead_one

/--
Specialisation of `monic_of_congr_mul_monic_monic` for cofactors already
canonicalised by `Hex.ZPoly.reduceModPow`; its coefficients automatically lie
in `[0, p^k)`.

Consumed by `henselLiftQuadratic_h_monic`, where the spec congruence
`(lifted.g * lifted.h) ≡ f (mod p^k)` already supplies a `reduceModPow`-form
cofactor.
-/
theorem monic_reduceModPow_of_congr_mul_monic_monic
    {g h f : Hex.ZPoly} {p k : Nat}
    (hm : 1 < p ^ k)
    (hcongr : Hex.ZPoly.congr (g * Hex.ZPoly.reduceModPow h p k) f (p ^ k))
    (hg_monic : Hex.DensePoly.Monic g)
    (hf_monic : Hex.DensePoly.Monic f)
    (hh_ne_zero : Hex.ZPoly.reduceModPow h p k ≠ 0) :
    Hex.DensePoly.Monic (Hex.ZPoly.reduceModPow h p k) := by
  have hpos : 0 < p ^ k := Nat.zero_lt_of_lt hm
  have hpos_int : (0 : Int) < (p ^ k : Int) := by
    exact_mod_cast hpos
  apply monic_of_congr_mul_monic_monic hm hcongr hg_monic hf_monic
  · intro i
    rw [Hex.ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hpos]
    exact Int.emod_lt_of_pos _ hpos_int
  · intro i
    rw [Hex.ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hpos]
    exact Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hpos))
  · exact hh_ne_zero

/-- The lifted monic factor `lifted.g` produced by `henselLiftQuadratic` is
monic. The quadratic doubling loop preserves `Monic acc.g` via
`quadraticHenselStep_monic`; the final `reduceModPow` cleanup preserves it via
`reduceModPow_monic_of_monic`.

Consumed (alongside `henselLiftQuadratic_h_monic`) by
`multifactorLiftQuadratic_each_monic` to discharge per-output monicness inside
the sequential split tree. -/
theorem henselLiftQuadratic_g_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    DensePoly.Monic (henselLiftQuadratic p k f g h s t).g := by
  let init : QuadraticLiftResult := { g, h, s, t }
  let fuel := quadraticDoublingSteps k
  let looped := iterateQuadraticHensel p f 1 fuel init
  have hstart : QuadraticLiftLoopInvariant (p ^ 1) f init := by
    simpa [init] using hinv
  have hloop :
      QuadraticLiftLoopInvariant (p ^ (1 * 2 ^ fuel)) f looped :=
    iterateQuadraticHensel_invariant p f 1 fuel init hp (by omega) hstart
  have hg_monic : DensePoly.Monic looped.g := hloop.2.2
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hreduce_monic :
      DensePoly.Monic (ZPoly.reduceModPow looped.g p (k' + 1)) :=
    reduceModPow_monic_of_monic p k' looped.g hp hg_monic
  simpa [henselLiftQuadratic, init, fuel, looped] using hreduce_monic

/-- The lifted cofactor `lifted.h` produced by `henselLiftQuadratic` is monic
when `f` is monic. Derived from the cofactor monic lemma
`monic_reduceModPow_of_congr_mul_monic_monic` applied to the spec congruence
`(lifted.g * lifted.h) ≡ f (mod p^k)` and `henselLiftQuadratic_g_monic`.

Consumed (alongside `henselLiftQuadratic_g_monic`) by
`multifactorLiftQuadratic_each_monic` to discharge per-output monicness inside
the sequential split tree. -/
theorem henselLiftQuadratic_h_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hf_monic : DensePoly.Monic f)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    DensePoly.Monic (henselLiftQuadratic p k f g h s t).h := by
  have hpk_gt_one : 1 < p ^ k := Nat.one_lt_pow (by omega : k ≠ 0) hp
  have hpk_pos : 0 < p ^ k := Nat.zero_lt_of_lt hpk_gt_one
  let init : QuadraticLiftResult := { g, h, s, t }
  let fuel := quadraticDoublingSteps k
  let looped := iterateQuadraticHensel p f 1 fuel init
  have hg_monic_lifted :
      DensePoly.Monic (henselLiftQuadratic p k f g h s t).g :=
    henselLiftQuadratic_g_monic p k f g h s t hk hp hinv
  have hspec_let := henselLiftQuadratic_spec p k f g h s t hk hp hinv
  have hspec :
      ZPoly.congr
        ((henselLiftQuadratic p k f g h s t).g *
          (henselLiftQuadratic p k f g h s t).h) f (p ^ k) := hspec_let
  have hh_eq :
      (henselLiftQuadratic p k f g h s t).h =
        ZPoly.reduceModPow looped.h p k := by
    simp [henselLiftQuadratic, init, fuel, looped]
  have hcongr_form :
      ZPoly.congr
        ((henselLiftQuadratic p k f g h s t).g *
          ZPoly.reduceModPow looped.h p k) f (p ^ k) := by
    rw [← hh_eq]; exact hspec
  have hh_ne_zero : (henselLiftQuadratic p k f g h s t).h ≠ 0 := by
    intro hzero
    have hf_ne_zero : f ≠ 0 := by
      intro hf_z
      have hlead : DensePoly.leadingCoeff f = (0 : Int) := by
        rw [hf_z]; rfl
      rw [hf_monic] at hlead
      omega
    have hf_pos : 0 < f.size := ZPoly.size_pos_of_ne_zero f hf_ne_zero
    have hf_top : f.coeff (f.size - 1) = (1 : Int) := by
      rw [← DensePoly.leadingCoeff_eq_coeff_last f hf_pos]
      exact hf_monic
    have hmul_zero :
        (henselLiftQuadratic p k f g h s t).g *
          (henselLiftQuadratic p k f g h s t).h = 0 := by
      rw [hzero, DensePoly.mul_comm_poly (S := Int)]
      exact DensePoly.zero_mul _
    have hspec_zero :
        ZPoly.congr (0 : ZPoly) f (p ^ k) := by
      rw [← hmul_zero]; exact hspec
    have hc := hspec_zero (f.size - 1)
    rw [DensePoly.coeff_zero, hf_top] at hc
    have hdvd : (p ^ k : Int) ∣ ((0 : Int) - 1) :=
      Int.dvd_of_emod_eq_zero hc
    have hdvd_one : (p ^ k : Int) ∣ (1 : Int) := by
      have : (p ^ k : Int) ∣ -(1 : Int) := by simpa using hdvd
      simpa using (Int.dvd_neg).mp this
    have hdvd_one_nat : p ^ k ∣ 1 := by
      have h := Int.ofNat_dvd.mp (by exact_mod_cast hdvd_one)
      exact h
    have : p ^ k = 1 := Nat.eq_one_of_dvd_one hdvd_one_nat
    omega
  have hh_red_ne_zero : ZPoly.reduceModPow looped.h p k ≠ 0 := by
    rw [← hh_eq]; exact hh_ne_zero
  have hmonic_reduce :
      DensePoly.Monic (ZPoly.reduceModPow looped.h p k) :=
    monic_reduceModPow_of_congr_mul_monic_monic
      (g := (henselLiftQuadratic p k f g h s t).g)
      (h := looped.h) (f := f) (p := p) (k := k)
      hpk_gt_one hcongr_form hg_monic_lifted hf_monic hh_red_ne_zero
  rw [hh_eq]; exact hmonic_reduce

private theorem multifactorLiftQuadraticList_each_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : List ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hf_monic : DensePoly.Monic f)
    (hinv : QuadraticMultifactorLiftInvariant p k f factors) :
    ∀ entry ∈ (multifactorLiftQuadraticList p k f factors).toList,
      DensePoly.Monic entry := by
  induction factors generalizing f with
  | nil =>
      simp [multifactorLiftQuadraticList]
  | cons g rest ih =>
      cases rest with
      | nil =>
          intro entry hmem
          have hentry_eq : entry = ZPoly.reduceModPow f p k := by
            simp [multifactorLiftQuadraticList] at hmem
            exact hmem
          rw [hentry_eq]
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          exact reduceModPow_monic_of_monic p k' f hp hf_monic
      | cons h tail =>
          intro entry hmem
          rcases hinv with ⟨hstart, htail⟩
          let restFactors := (h :: tail).toArray
          let splitProduct := Array.polyProduct restFactors
          let xgcd := normalizedXGCD p g splitProduct
          let s := FpPoly.liftToZ xgcd.left
          let t := FpPoly.liftToZ xgcd.right
          let lifted := henselLiftQuadratic p k f g splitProduct s t
          have hh_monic : DensePoly.Monic lifted.h := by
            simpa [lifted, splitProduct, restFactors, xgcd, s, t] using
              henselLiftQuadratic_h_monic p k f g splitProduct s t hk hp hf_monic
                (by simpa [restFactors, splitProduct, xgcd, s, t] using hstart)
          have hg_monic : DensePoly.Monic lifted.g := by
            simpa [lifted, splitProduct, restFactors, xgcd, s, t] using
              henselLiftQuadratic_g_monic p k f g splitProduct s t hk hp
                (by simpa [restFactors, splitProduct, xgcd, s, t] using hstart)
          have htail' :
              QuadraticMultifactorLiftInvariant p k lifted.h (h :: tail) := by
            simpa [lifted, splitProduct, restFactors, xgcd, s, t] using htail
          have hmem' :
              entry = lifted.g ∨
                entry ∈
                  (multifactorLiftQuadraticList p k lifted.h (h :: tail)).toList := by
            have hexpand :
                (multifactorLiftQuadraticList p k f (g :: h :: tail)).toList =
                  lifted.g ::
                    (multifactorLiftQuadraticList p k lifted.h (h :: tail)).toList := by
              simp [multifactorLiftQuadraticList, restFactors, splitProduct,
                xgcd, s, t, lifted]
            rw [hexpand] at hmem
            simpa using hmem
          rcases hmem' with hg_eq | hh_mem
          · rw [hg_eq]; exact hg_monic
          · exact ih lifted.h hh_monic htail' entry hh_mem

/-- Every output of `multifactorLiftQuadratic` is monic when the input
polynomial `f` is monic and the quadratic multifactor lift invariant package
holds.

Driven by `henselLiftQuadratic_g_monic` and `henselLiftQuadratic_h_monic`
applied at each sequential split node. Consumed by the Mathlib-facing umbrella
`HexBerlekampZassenhausMathlib.henselLiftData_liftedFactor_monic`. -/
theorem multifactorLiftQuadratic_each_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hf_monic : DensePoly.Monic f)
    (hinv : QuadraticMultifactorLiftInvariant p k f factors.toList) :
    ∀ i : Fin (multifactorLiftQuadratic p k f factors).size,
      DensePoly.Monic (multifactorLiftQuadratic p k f factors)[i] := by
  intro i
  have hmem :
      (multifactorLiftQuadratic p k f factors)[i] ∈
        (multifactorLiftQuadratic p k f factors).toList :=
    Array.getElem_mem_toList i.isLt
  exact multifactorLiftQuadraticList_each_monic p k f factors.toList hk hp
    hf_monic hinv _ hmem

end ZPoly

end Hex

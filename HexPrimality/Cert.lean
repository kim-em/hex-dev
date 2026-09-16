/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Cert3
public import HexPrimality.Order
public import HexPrimality.Table
public import HexArith.Montgomery.Context
-- For the `#guard` regression block only.
meta import HexPrimality.Table
meta import HexArith.Montgomery.Context

public section

/-!
The Pocklington primality certificate, its kernel-replayable checker, and
checker soundness.

`PrimeCert` is one inductive: a stored-table leaf, the square-root
Pocklington node, and the cube-root Brillhart-Lehmer-Selfridge node. Both
Pocklington arms check their arithmetic conditions and recursively replay
every child certificate. The prime of each factor entry is not stored; it is
read off as the child certificate's subject, which removes a redundancy an
attacker could otherwise exploit.

The checker-owned definitions are `@[expose]` and structurally recursive. The
replay closure runs through `HexArith.powModNat` (the kernel-facing
specification whose `@[csimp]` twin takes the Montgomery path at runtime),
core `Nat` arithmetic including `Nat.gcd`, `Nat.mod`, and `Nat.div`, and the
table's exposed lookup in its verified sieve bitset. The `decide +kernel` probes in
`HexBench.PrimalityKernel` confirm that accepted certificates in both
Pocklington forms replay by kernel reduction alone. `prime_of_checkPrime`
proves soundness of both arms; per the SPEC, no certificate-existence,
checker-completeness, or search-completeness claim accompanies it.
-/

namespace Hex

namespace Nat

/-- A primality certificate. One inductive rather than two mutually
recursive declarations, because a structure referring forward to `PrimeCert`
while `PrimeCert` refers back to it does not elaborate.

Each factor entry is a base `a`, an exponent `e` (stored off by one, so the
exponent `e + 1` is positive by construction), and the child certificate for
a prime `q`, read off as the child's subject. Factor lists in both Pocklington
constructors must be in strictly ascending child-subject order for the checker
to accept them. -/
inductive PrimeCert where
  /-- `n` is an entry of the stored table. -/
  | small (n : Nat)
  /-- Pocklington: `factors` partially factors `n - 1` past its square
  root. -/
  | pock (n : Nat) (factors : List (Nat × Nat × PrimeCert))
  /-- The cube-root Brillhart-Lehmer-Selfridge variant, with the cofactor
  decomposition `R = 2 F s + r` and the integer-square-root witness `w` for
  the discriminant test (`Nat.sqrt` is well-founded recursion and does not
  kernel-reduce, so the checker verifies `w` instead of computing a root). -/
  | pock3 (n r s w : Nat) (factors : List (Nat × Nat × PrimeCert))
  /-- Cube-root Pocklington with divisors `lF+1` excluded for `1 ≤ l < m`. -/
  | pock3Sieve (n r s w m : Nat) (factors : List (Nat × Nat × PrimeCert))
deriving Repr

/-- The number a certificate is about. -/
@[expose]
def PrimeCert.subject : PrimeCert → Nat
  | .small n | .pock n _ | .pock3 n _ _ _ _ | .pock3Sieve n _ _ _ _ _ => n

/-- `acc * q ^ e`, checking each nonzero multiplication by division before
constructing it. A zero accumulator or base returns zero immediately; otherwise
the computation aborts as soon as the next product would exceed `bound`, so an
attacker-chosen enormous power is never constructed. -/
@[expose]
def boundedPowMul.native (bound q : Nat) : Nat → Nat → Option Nat
  | acc, 0 => some acc
  | acc, e + 1 =>
      if acc = 0 then some 0
      else if q = 0 then some 0
      else if acc ≤ bound / q then boundedPowMul.native bound q (acc * q) e
      else none

/-- Kernel reduction uses raw recursors to avoid auxiliary match and
`Decidable` reductions at each bounded multiplication. -/
@[expose] noncomputable def boundedPowMul.go (bound q acc e : Nat) : Option Nat :=
  Nat.rec (fun acc => some acc)
    (fun _ rec acc =>
      (acc.beq 0).rec
        ((q.beq 0).rec
          ((acc.ble (bound.div q)).rec none (rec (acc.mul q)))
          (some 0))
        (some 0)) e acc

private theorem boundedPowMul.go_eq (bound q acc e : Nat) :
    boundedPowMul.go bound q acc e = boundedPowMul.native bound q acc e := by
  induction e generalizing acc with
  | zero => rfl
  | succ e ih =>
    change (acc.beq 0).rec
      ((q.beq 0).rec
        ((acc.ble (bound.div q)).rec none (boundedPowMul.go bound q (acc.mul q) e))
        (some 0)) (some 0) = boundedPowMul.native bound q acc (e + 1)
    simp only [Bool.rec_eq, Nat.beq_eq, Nat.ble_eq, ih, boundedPowMul.native]
    rfl

private theorem boundedPowMul.native.closed (bound q acc e : Nat) :
    boundedPowMul.native bound q acc e =
      if e = 0 ∨ acc * q ^ e ≤ bound then some (acc * q ^ e) else none := by
  induction e generalizing acc with
  | zero => simp [boundedPowMul.native]
  | succ e ih =>
      by_cases ha : acc = 0
      · simp [boundedPowMul.native, ha]
      by_cases hq : q = 0
      · simp [boundedPowMul.native, hq]
      have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      have hmul : (acc * q) * q ^ e = acc * q ^ (e + 1) := by
        simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have hle : acc * q ≤ acc * q ^ (e + 1) := by
        rw [← hmul]
        exact Nat.le_mul_of_pos_right _ (Nat.pow_pos hqpos)
      simp only [boundedPowMul.native, ha, hq, ite_false]
      by_cases hb : acc ≤ bound / q
      · rw [ite_eq_left hb, ih, hmul]
        have hab : acc * q ≤ bound := (Nat.le_div_iff_mul_le hqpos).mp hb
        by_cases he : e = 0
        · subst e; simp [hab]
        · simp [he]
      · rw [ite_eq_right hb]
        have hn : ¬ acc * q ^ (e + 1) ≤ bound := by
          intro h
          exact hb ((Nat.le_div_iff_mul_le hqpos).mpr (Nat.le_trans hle h))
        simp [hn]

/-- Powers of two use a checked shift: the right shift checks the final
product bound before the left shift constructs that product. Other bases use
bounded multiplication. Compiled evaluation retains the original loop. -/
@[expose]
noncomputable def boundedPowMul (bound q acc e : Nat) : Option Nat :=
  (e.beq 0).rec
    ((q.beq 2).rec
      (boundedPowMul.go bound q acc e)
      ((acc.ble (bound.shiftRight e)).rec none (some (acc.shiftLeft e))))
    (some acc)

private theorem boundedPowMul.eq_loop (bound q acc e : Nat) :
    boundedPowMul bound q acc e = boundedPowMul.native bound q acc e := by
  simp only [boundedPowMul, Bool.rec_eq, Nat.beq_eq, Nat.ble_eq]
  split
  next he => subst e; rfl
  next he =>
    split
    next hq =>
      subst q
      rw [boundedPowMul.native.closed]
      change (if acc ≤ bound >>> e then some (acc <<< e) else none) = _
      simp only [he, false_or, Nat.shiftLeft_eq,
        Nat.shiftRight_eq_div_pow,
        Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
    next => exact boundedPowMul.go_eq bound q acc e

/-- The compiler uses the verified runtime implementation. -/
@[csimp] theorem boundedPowMul_eq_native : @boundedPowMul = @boundedPowMul.native := by
  funext bound q acc e
  exact boundedPowMul.eq_loop bound q acc e

/-- Exponent zero preserves the accumulator, even when it exceeds the bound. -/
@[simp] theorem boundedPowMul_zero (bound q acc : Nat) :
    boundedPowMul bound q acc 0 = some acc := rfl

/-- One checked multiplication, as an equation for symbolic proofs. -/
theorem boundedPowMul_succ (bound q acc e : Nat) :
    boundedPowMul bound q acc (e + 1) =
      if acc = 0 then some 0
      else if q = 0 then some 0
      else if acc ≤ bound / q then boundedPowMul bound q (acc * q) e
      else none := by
  simp only [boundedPowMul.eq_loop, boundedPowMul.native]

/-- The factored part `F = ∏ qᵢ ^ (eᵢ + 1)` of a factor list, aborting as
soon as the running product exceeds `bound`. -/
@[expose]
def certProduct (bound : Nat) : List (Nat × Nat × PrimeCert) → Option Nat
  | [] => some 1
  | (_, e, c) :: rest =>
      match boundedPowMul bound c.subject 1 (e + 1) with
      | none => none
      | some pw =>
          match certProduct bound rest with
          | none => none
          | some f => boundedPowMul bound f pw 1

/-- Bounded product for positive factor subjects, with zero denoting failure.
The caller checks positivity. Exponent-one entries multiply and check the
result against the bound; larger exponents retain the bounded power routine.
A multiplication has at most the sum of its operands’ bit lengths. -/
@[expose] noncomputable def pockProduct (bound : Nat) :
    List (Nat × Nat × PrimeCert) → Nat :=
  List.rec 1 (fun x _ f => Nat.rec
    (let p := x.2.2.subject.mul f; (p.ble bound).rec 0 p)
    (fun e _ => Option.rec 0 id (boundedPowMul bound x.2.2.subject f e.succ.succ))
    x.2.1)

/-- Continue the canonical factor-subject check above a strict lower bound. -/
@[expose]
def subjectsAfter.native (lower : Nat) : List (Nat × Nat × PrimeCert) → Bool
  | [] => true
  | (_, _, c) :: rest =>
      decide (lower < c.subject) && subjectsAfter.native c.subject rest

/-- Primitive comparisons in a direct list fold for kernel replay. -/
@[expose]
noncomputable def subjectsAfter (lower : Nat) (fs : List (Nat × Nat × PrimeCert)) : Bool :=
  List.rec (fun _ => true)
    (fun x _ ih lower => (lower.blt x.2.2.subject).and (ih x.2.2.subject)) fs lower

private theorem subjectsAfter.eq_native (lower : Nat) (fs : List (Nat × Nat × PrimeCert)) :
    subjectsAfter lower fs = subjectsAfter.native lower fs := by
  induction fs generalizing lower with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a, e, c⟩
    change (lower.blt c.subject && subjectsAfter c.subject xs) = _
    rw [ih]
    apply Bool.eq_iff_iff.mpr
    simp [subjectsAfter.native, Nat.blt_eq]

/-- The compiler uses the verified runtime implementation. -/
@[csimp] theorem subjectsAfter_eq_native : @subjectsAfter = @subjectsAfter.native := by
  funext lower fs
  exact subjectsAfter.eq_native lower fs

/-- Structural check on the factor list: every claimed prime is at least
`2`, and the claimed primes are in strictly ascending order. The canonical
order implies pairwise distinctness with one lower-bound subject comparison
per entry. -/
@[expose]
def subjectsOk (factors : List (Nat × Nat × PrimeCert)) : Bool :=
  subjectsAfter 1 factors

/-- The per-entry witness conditions: Fermat at the base, and the gcd
condition at the reduced exponent. The gcd argument is written modularly:
the checker only holds the residue `x`, and `(x + n - 1) % n` is `x - 1`
modulo `n` at every residue, where the literal `x - 1` would truncate at
`x = 0`. -/
@[expose]
def checkWitness.native (n q a : Nat) : Bool :=
  HexArith.powModNat a (n - 1) n == 1 % n &&
    Nat.gcd ((HexArith.powModNat a ((n - 1) / q) n + n - 1) % n) n == 1

/-- The witness conditions with primitive Nat comparisons for kernel reduction. -/
@[expose]
noncomputable def checkWitness (n q a : Nat) : Bool :=
  let pred := n.sub 1
  let x := HexArith.powModNat a (pred.div q) n
  (HexArith.powModNat a pred n).beq ((1 : Nat).mod n) &&
    (Nat.gcd (((x.add n).sub 1).mod n) n).beq 1

private theorem checkWitness.eq_native (n q a : Nat) :
    checkWitness n q a = checkWitness.native n q a := by
  apply Bool.eq_iff_iff.mpr
  simp [checkWitness, checkWitness.native] <;> rfl

/-- The compiler uses the verified runtime implementation. -/
@[csimp] theorem checkWitness_eq_native : @checkWitness = @checkWitness.native := by
  funext n q a
  exact checkWitness.eq_native n q a

/-- The ordinary per-entry witness traversal used by compiled search. -/
@[expose]
def checkWitnesses.native (n : Nat) (fs : List (Nat × Nat × PrimeCert)) : Bool :=
  fs.all fun x => checkWitness n x.2.2.subject x.1

/-- Replay adjacent equal witness bases with one Fermat check. `seen` records
that the preceding base passed its Fermat check; the initial state is false. -/
@[expose] noncomputable def checkWitnesses.go (n : Nat)
    (fs : List (Nat × Nat × PrimeCert)) (prev : Nat) (seen : Bool) : Bool :=
  List.rec (motive := fun _ => Nat → Bool → Bool) (fun _ _ => true)
    (fun x _ ih prev seen =>
      ((seen.and (x.1.beq prev)).rec (motive := fun _ => Bool)
        ((HexArith.powModNat x.1 (n.sub 1) n).beq ((1 : Nat).mod n)) true).and
        (((Nat.gcd (((HexArith.powModNat x.1 ((n.sub 1).div x.2.2.subject) n).add n).sub 1
          |>.mod n) n).beq 1).and (ih x.1 true))) fs prev seen

/-- Check every witness, reusing the Fermat leg for adjacent equal bases. -/
@[expose]
noncomputable def checkWitnesses (n : Nat) (fs : List (Nat × Nat × PrimeCert)) : Bool :=
  checkWitnesses.go n fs 0 false

private theorem checkWitnesses.go_eq (n : Nat) (fs : List (Nat × Nat × PrimeCert))
    (prev : Nat) (seen : Bool)
    (hp : seen = true → (HexArith.powModNat prev (n.sub 1) n).beq ((1 : Nat).mod n) = true) :
    checkWitnesses.go n fs prev seen = checkWitnesses.native n fs := by
  induction fs generalizing prev seen with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a, e, c⟩
    let fermat := (HexArith.powModNat a (n.sub 1) n).beq ((1 : Nat).mod n)
    have hcache : ((seen.and (a.beq prev)).rec (motive := fun _ => Bool) fermat true) = fermat := by
      simp only [Bool.rec_eq, Bool.and_eq_true, Nat.beq_eq]
      split
      · next h =>
        obtain ⟨hs, ha⟩ := h
        subst prev
        exact (hp hs).symm
      · rfl
    change (((seen.and (a.beq prev)).rec (motive := fun _ => Bool) fermat true).and
      (((Nat.gcd (((HexArith.powModNat a ((n.sub 1).div c.subject) n).add n).sub 1
        |>.mod n) n).beq 1).and (checkWitnesses.go n xs a true))) = _
    rw [hcache]
    change _ = ((fermat &&
      (Nat.gcd (((HexArith.powModNat a ((n.sub 1).div c.subject) n).add n).sub 1
        |>.mod n) n).beq 1) && checkWitnesses.native n xs)
    cases hf : fermat with
    | false => rfl
    | true =>
      rw [ih a true (by intro _; exact hf)]
      rfl

private theorem checkWitnesses.eq_native (n : Nat) (fs : List (Nat × Nat × PrimeCert)) :
    checkWitnesses n fs = checkWitnesses.native n fs :=
  checkWitnesses.go_eq n fs 0 false (by intro h; cases h)

/-- The compiler uses the verified runtime implementation. -/
@[csimp] theorem checkWitnesses_eq_native : @checkWitnesses = @checkWitnesses.native := by
  funext n fs
  exact checkWitnesses.eq_native n fs

/-- The arithmetic side of the square-root Pocklington node: `n` odd and at
least `2`, canonical strictly ascending factor subjects, `F ∣ n - 1` with
`n < F * F`, and every per-entry witness condition. Child certificates are
checked separately by `checkPrime`. -/
@[expose]
def checkPockArith.native (n : Nat) (factors : List (Nat × Nat × PrimeCert)) : Bool :=
  decide (2 ≤ n) && n % 2 == 1 && subjectsOk factors &&
    match certProduct (n - 1) factors with
    | none => false
    | some F =>
        (n - 1) % F == 0 && decide (n < F * F) &&
          factors.all fun x => checkWitness n x.2.2.subject x.1

/-- Kernel comparisons use primitive Nat operations; compiled evaluation
retains the original arithmetic check. -/
@[expose]
noncomputable def checkPockArith (n : Nat) (factors : List (Nat × Nat × PrimeCert)) : Bool :=
  (2 : Nat).ble n && (n.mod 2).beq 1 && subjectsOk factors &&
    (let F := pockProduct (n.sub 1) factors
     ((n.sub 1).mod F).beq 0 && n.blt (F.mul F) &&
       checkWitnesses n factors)

/-- The arithmetic side of the cube-root node: everything the square-root
arm verifies except the `n < F * F` bound, which the
Brillhart-Lehmer-Selfridge conditions replace: `F` even, the cofactor
`R = (n - 1) / F` odd (the weaker form of the classical `gcd(F, R) = 1`
that the proof uses once `F` is even), the decomposition `R = 2Fs + r` with
`1 ≤ r < 2F`, the cube-root size bound, and the discriminant condition on
`r² - 8s`, with the stored witness `w` verifying non-squareness by two
multiplications. (When `r² ≤ 8s` the truncated subtraction makes the
witness clause `w * w < 0` unsatisfiable, so the disjunct is simply never
taken; the middle disjunct covers that region.) -/
@[expose]
def checkPock3Arith (n r s w : Nat)
    (factors : List (Nat × Nat × PrimeCert)) : Bool :=
  decide (2 ≤ n) && n % 2 == 1 && subjectsOk factors &&
    match certProduct (n - 1) factors with
    | none => false
    | some F =>
        (n - 1) % F == 0 && F % 2 == 0 && (n - 1) / F % 2 == 1 &&
          (n - 1) / F == 2 * F * s + r &&
          decide (1 ≤ r) && decide (r < 2 * F) &&
          decide (n < (F + 1) * (2 * F * F + (r - 1) * F + 1)) &&
          (s == 0 || decide (r * r < 8 * s) ||
            (decide (w * w < r * r - 8 * s) &&
              decide (r * r - 8 * s < (w + 1) * (w + 1)))) &&
          checkWitnesses n factors

/-- Check the first `k` possible divisors `lF+1`. -/
@[expose]
def checkDivisors (n F : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => checkDivisors n F k && n % ((k + 1) * F + 1) != 0

private theorem checkDivisors_spec (n F : Nat) : ∀ k,
    checkDivisors n F k = true → ∀ l, 1 ≤ l → l ≤ k → ¬ l * F + 1 ∣ n
  | 0, _, _, _, _ => by omega
  | k + 1, h, l, hl, hk => by
    simp only [checkDivisors, Bool.and_eq_true, bne_iff_ne] at h
    by_cases heq : l = k + 1
    · subst l
      exact fun hd => h.2 (Nat.mod_eq_zero_of_dvd hd)
    · exact checkDivisors_spec n F k h.1 l hl (by omega)

/-- The general cube-root arithmetic check; the legacy node retains its sieve-free path. -/
@[expose]
def checkPock3SieveArith (n r s w m : Nat)
    (factors : List (Nat × Nat × PrimeCert)) : Bool :=
  decide (2 ≤ n) && n % 2 == 1 && subjectsOk factors &&
    match certProduct (n - 1) factors with
    | none => false
    | some F =>
        (n - 1) % F == 0 && F % 2 == 0 && (n - 1) / F % 2 == 1 &&
          (n - 1) / F == 2 * F * s + r &&
          decide (1 ≤ r) && decide (r < 2 * F) && decide (1 ≤ m) &&
          checkDivisors n F (m - 1) &&
          decide (2 * s + m * m < (2 * F + r) * m + 2) &&
          (s == 0 || decide (r * r < 8 * s) ||
            (decide (w * w < r * r - 8 * s) &&
              decide (r * r - 8 * s < (w + 1) * (w + 1)))) &&
          checkWitnesses n factors

/-! Accumulator lemmas -/

/-- On success, the bounded accumulator computes the ordinary product. -/
theorem boundedPowMul_eq {bound q : Nat} :
    ∀ (e acc r : Nat), boundedPowMul bound q acc e = some r →
      r = acc * q ^ e := by
  simp only [boundedPowMul.eq_loop]
  intro e
  induction e with
  | zero =>
      intro acc r h
      unfold boundedPowMul.native at h
      injection h with h
      subst h
      simp
  | succ e ih =>
      intro acc r h
      unfold boundedPowMul.native at h
      by_cases ha : acc = 0
      · rw [ite_eq_left ha] at h
        injection h with h
        subst h
        simp [ha]
      · rw [ite_eq_right ha] at h
        by_cases hq : q = 0
        · rw [ite_eq_left hq] at h
          injection h with h
          subst h
          simp [hq]
        · rw [ite_eq_right hq] at h
          by_cases hb : acc ≤ bound / q
          · rw [ite_eq_left hb] at h
            rw [ih (acc * q) r h, Nat.pow_succ, Nat.mul_assoc,
              Nat.mul_comm q (q ^ e)]
          · rw [ite_eq_right hb] at h
            cases h

/-- A successful bounded multiplication preserves the accumulator bound. The
incoming bound is needed only for the zero-exponent case; every positive step
establishes it before constructing the next accumulator. -/
theorem boundedPowMul_le {bound q acc e r : Nat} (hacc : acc ≤ bound)
    (h : boundedPowMul bound q acc e = some r) : r ≤ bound := by
  rw [boundedPowMul.eq_loop] at h
  induction e generalizing acc r with
  | zero =>
      unfold boundedPowMul.native at h
      injection h with h
      simpa [h] using hacc
  | succ e ih =>
      unfold boundedPowMul.native at h
      by_cases ha : acc = 0
      · rw [ite_eq_left ha] at h
        injection h with h
        subst h
        exact Nat.zero_le _
      · rw [ite_eq_right ha] at h
        by_cases hq : q = 0
        · rw [ite_eq_left hq] at h
          injection h with h
          subst h
          exact Nat.zero_le _
        · rw [ite_eq_right hq] at h
          by_cases hb : acc ≤ bound / q
          · rw [ite_eq_left hb] at h
            exact ih ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hq)).mp hb) h
          · rw [ite_eq_right hb] at h
            cases h

/-- A successful certificate product is bounded when its initial accumulator
`1` is bounded. -/
theorem certProduct_le {bound : Nat} (hbound : 1 ≤ bound) :
    ∀ (l : List (Nat × Nat × PrimeCert)) (F : Nat),
      certProduct bound l = some F → F ≤ bound := by
  intro l F h
  cases l with
  | nil =>
      unfold certProduct at h
      injection h with h
      simpa [h] using hbound
  | cons a rest =>
      obtain ⟨a1, e, c⟩ := a
      unfold certProduct at h
      split at h
      · cases h
      next pw hpw =>
        split at h
        · cases h
        next f hcp =>
          exact boundedPowMul_le (boundedPowMul_le hbound hpw) h

/-- The unbounded product the accumulator computes when it does not abort. -/
private def certProd : List (Nat × Nat × PrimeCert) → Nat
  | [] => 1
  | (_, e, c) :: rest => c.subject ^ (e + 1) * certProd rest

private theorem certProduct_eq {bound : Nat} :
    ∀ (l : List (Nat × Nat × PrimeCert)) (F : Nat),
      certProduct bound l = some F → F = certProd l := by
  intro l
  induction l with
  | nil =>
      intro F h
      unfold certProduct at h
      injection h with h
      subst h
      rfl
  | cons a rest ih =>
      intro F h
      obtain ⟨a1, e, c⟩ := a
      unfold certProduct at h
      split at h
      · cases h
      next pw hpw =>
        split at h
        · cases h
        next f hcp =>
          have h1 := boundedPowMul_eq (e + 1) 1 pw hpw
          have h2 := ih f hcp
          have h3 := boundedPowMul_eq 1 pw F h
          simpa [certProd, h1, h2] using h3

private theorem certProd_pos {fs : List (Nat × Nat × PrimeCert)}
    (h : ∀ x ∈ fs, 0 < x.2.2.subject) : 0 < certProd fs := by
  induction fs with
  | nil => decide
  | cons x xs ih =>
    exact Nat.mul_pos (Nat.pow_pos (h x (by simp)))
      (ih (fun y hy => h y (by simp [hy])))

private theorem pockProduct.cons (bound a e : Nat) (c : PrimeCert)
    (xs : List (Nat × Nat × PrimeCert)) :
    pockProduct bound ((a, e, c) :: xs) =
      match e with
      | 0 => if c.subject * pockProduct bound xs ≤ bound then
          c.subject * pockProduct bound xs else 0
      | e + 1 => (boundedPowMul bound c.subject (pockProduct bound xs) (e + 2)).getD 0 := by
  cases e with
  | zero =>
    change ((c.subject.mul (pockProduct bound xs)).ble bound).rec (motive := fun _ => Nat)
      0 (c.subject.mul (pockProduct bound xs)) = _
    simp only [Bool.rec_eq, Nat.ble_eq, Nat.mul_eq]
  | succ e =>
    change Option.rec (motive := fun _ => Nat) 0 id
      (boundedPowMul bound c.subject (pockProduct bound xs) (e + 2)) =
      (boundedPowMul bound c.subject (pockProduct bound xs) (e + 2)).getD 0
    cases boundedPowMul bound c.subject (pockProduct bound xs) (e + 2) <;> rfl

private theorem pockProduct.eq_product (bound : Nat)
    (fs : List (Nat × Nat × PrimeCert)) (hs : ∀ x ∈ fs, 0 < x.2.2.subject) :
    pockProduct bound fs = (certProduct bound fs).getD 0 := by
  induction fs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a, e, c⟩
    have hq : 0 < c.subject := hs (a, e, c) (by simp)
    have ht : ∀ x ∈ xs, 0 < x.2.2.subject := fun x hx => hs x (by simp [hx])
    have hf := certProd_pos ht
    have ih := ih ht
    cases hp : certProduct bound xs with
    | none =>
      simp only [hp, Option.getD_none] at ih
      rw [pockProduct.cons, ih]
      cases e <;>
        simp [certProduct, hp, boundedPowMul.eq_loop, boundedPowMul.native.closed] <;>
        split <;> rfl
    | some f =>
      have hfp : 0 < f := (certProduct_eq xs f hp) ▸ hf
      simp only [hp, Option.getD_some] at ih
      have hle : c.subject ^ (e + 1) ≤ c.subject ^ (e + 1) * f :=
        Nat.le_mul_of_pos_right _ hfp
      rw [pockProduct.cons, ih]
      by_cases hw : c.subject ^ (e + 1) ≤ bound
      · by_cases hm : c.subject ^ (e + 1) * f ≤ bound <;>
          cases e <;>
          simp_all [certProduct, boundedPowMul.eq_loop, boundedPowMul.native.closed,
            Nat.mul_comm, Nat.add_assoc] <;> grind
      · have hm : ¬ c.subject ^ (e + 1) * f ≤ bound := fun h => hw (Nat.le_trans hle h)
        cases e <;>
          simp_all [certProduct, boundedPowMul.eq_loop, boundedPowMul.native.closed,
            Nat.mul_comm, Nat.add_assoc] <;> grind


private theorem subjectsAfter_spec :
    ∀ (lower : Nat) (l : List (Nat × Nat × PrimeCert)),
      subjectsAfter lower l = true →
        (∀ x ∈ l, lower < x.2.2.subject) ∧
          l.Pairwise (fun a b => a.2.2.subject < b.2.2.subject)
  | _, [], _ => ⟨by simp, List.Pairwise.nil⟩
  | lower, a :: rest, h => by
      obtain ⟨a1, e, c⟩ := a
      change (lower.blt c.subject && subjectsAfter c.subject rest) = true at h
      rw [Bool.and_eq_true, Nat.blt_eq] at h
      have ih := subjectsAfter_spec c.subject rest h.2
      refine ⟨?_, List.pairwise_cons.mpr ⟨ih.1, ih.2⟩⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact Nat.lt_trans h.1 (ih.1 x hx)

private theorem subjectsAfter_mono {lower upper : Nat} (hlu : lower ≤ upper) :
    ∀ (l : List (Nat × Nat × PrimeCert)), subjectsAfter upper l = true →
      subjectsAfter lower l = true
  | [], _ => by simp [subjectsAfter]
  | a :: rest, h => by
      obtain ⟨a1, e, c⟩ := a
      unfold subjectsAfter at h ⊢
      simp only [Bool.and_eq_true, Nat.blt_eq] at h ⊢
      exact ⟨Nat.lt_of_le_of_lt hlu h.1, h.2⟩

private theorem subjectsOk_cons {a : Nat × Nat × PrimeCert}
    {rest : List (Nat × Nat × PrimeCert)}
    (h : subjectsOk (a :: rest) = true) :
    2 ≤ a.2.2.subject ∧ (∀ x ∈ rest, x.2.2.subject ≠ a.2.2.subject) ∧
      subjectsOk rest = true := by
  obtain ⟨a1, e, c⟩ := a
  change ((1 : Nat).blt c.subject && subjectsAfter c.subject rest) = true at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  have htail := subjectsAfter_spec c.subject rest h.2
  refine ⟨?_, ?_, ?_⟩
  · change 2 ≤ c.subject
    omega
  · intro x hx
    exact Nat.ne_of_gt (htail.1 x hx)
  · unfold subjectsOk
    exact subjectsAfter_mono (by omega) rest h.2

private theorem subjectsOk_forall :
    ∀ {l : List (Nat × Nat × PrimeCert)}, subjectsOk l = true →
      ∀ x ∈ l, 2 ≤ x.2.2.subject := by
  intro l
  induction l with
  | nil =>
      intro _ x hx
      cases hx
  | cons a rest ih =>
      intro h x hx
      obtain ⟨ha2, _, hrest⟩ := subjectsOk_cons h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ha2
      · exact ih hrest x hx'

private theorem checkPockArith.eq_native (n : Nat) (factors : List (Nat × Nat × PrimeCert)) :
    checkPockArith n factors = checkPockArith.native n factors := by
  by_cases hs : subjectsOk factors = true
  · have hp : ∀ x ∈ factors, 0 < x.2.2.subject := by
      intro x hx
      have := subjectsOk_forall hs x hx
      omega
    simp only [checkPockArith, pockProduct.eq_product _ _ hp,
      checkWitnesses.eq_native, checkWitnesses.native]
    cases h : certProduct (n - 1) factors <;>
      apply Bool.eq_iff_iff.mpr <;>
      simp [checkPockArith.native, h, hs, Nat.blt_eq] <;> rfl
  · have hf : subjectsOk factors = false := Bool.eq_false_iff.mpr hs
    simp [checkPockArith, checkPockArith.native, hf]

/-- The compiler uses the verified arithmetic implementation. -/
@[csimp] theorem checkPockArith_eq_native : @checkPockArith = @checkPockArith.native := by
  funext n fs
  exact checkPockArith.eq_native n fs


mutual

/-- Accept or reject a primality certificate. Pocklington factor lists are
accepted only in strictly ascending child-subject order. This is the ordinary
compiled traversal; the public `checkPrime` supplies the kernel fold. -/
@[expose]
def checkPrime.native : PrimeCert → Bool
  | .small n => isTablePrime n
  | .pock n factors => checkPockArith n factors && checkChildren factors
  | .pock3 n r s w factors =>
      checkPock3Arith n r s w factors && checkChildren factors
  | .pock3Sieve n r s w m factors =>
      checkPock3SieveArith n r s w m factors && checkChildren factors

/-- Accept every child certificate of a factor list. -/
@[expose]
def checkChildren : List (Nat × Nat × PrimeCert) → Bool
  | [] => true
  | (_, _, c) :: rest => checkPrime.native c && checkChildren rest

end

/-- Direct structural fold for kernel replay. Compiled code retains the
ordinary mutually recursive traversal. -/
@[expose]
noncomputable def checkPrime : PrimeCert → Bool :=
  PrimeCert.rec (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool)
    (motive_3 := fun _ => Bool) (motive_4 := fun _ => Bool)
    isTablePrime (fun n fs ih => (checkPockArith n fs).and ih)
    (fun n r s w fs ih => (checkPock3Arith n r s w fs).and ih)
    (fun n r s w m fs ih => (checkPock3SieveArith n r s w m fs).and ih)
    true (fun _ _ head tail => head.and tail)
    (fun _ _ ih => ih) (fun _ _ ih => ih)

private theorem checkPrime.pock (n : Nat) (fs : List (Nat × Nat × PrimeCert)) :
    checkPrime (.pock n fs) = (checkPockArith n fs && fs.all (fun x => checkPrime x.2.2)) := by
  suffices h : _ = fs.all (fun x => checkPrime x.2.2) by
    exact congrArg (fun x => checkPockArith n fs && x) h
  induction fs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a, e, c⟩
    simpa only [checkPrime, List.all_cons, Bool.and] using congrArg (checkPrime c && ·) ih

private theorem checkPrime.pock3 (n r s w : Nat) (fs : List (Nat × Nat × PrimeCert)) :
    checkPrime (.pock3 n r s w fs) =
      (checkPock3Arith n r s w fs && fs.all (fun x => checkPrime x.2.2)) := by
  suffices h : _ = fs.all (fun x => checkPrime x.2.2) by
    exact congrArg (fun x => checkPock3Arith n r s w fs && x) h
  induction fs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a, e, c⟩
    simpa only [checkPrime, List.all_cons, Bool.and] using congrArg (checkPrime c && ·) ih

private theorem checkPrime.pock3Sieve (n r s w m : Nat) (fs : List (Nat × Nat × PrimeCert)) :
    checkPrime (.pock3Sieve n r s w m fs) =
      (checkPock3SieveArith n r s w m fs && fs.all (fun x => checkPrime x.2.2)) := by
  suffices h : _ = fs.all (fun x => checkPrime x.2.2) by
    exact congrArg (fun x => checkPock3SieveArith n r s w m fs && x) h
  induction fs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a, e, c⟩
    simpa only [checkPrime, List.all_cons, Bool.and] using congrArg (checkPrime c && ·) ih

mutual
private theorem checkPrime.eq_native : ∀ c, checkPrime c = checkPrime.native c
  | .small _ => rfl
  | .pock n fs => by rw [checkPrime.pock, checkChildren.eq_all]; rfl
  | .pock3 n r s w fs => by rw [checkPrime.pock3, checkChildren.eq_all]; rfl
  | .pock3Sieve n r s w m fs => by rw [checkPrime.pock3Sieve, checkChildren.eq_all]; rfl

private theorem checkChildren.eq_all : ∀ fs : List (Nat × Nat × PrimeCert),
    fs.all (fun x => checkPrime x.2.2) = checkChildren fs
  | [] => rfl
  | (_, _, c) :: rest => by
    change (checkPrime c && rest.all (fun x => checkPrime x.2.2)) =
      (checkPrime.native c && checkChildren rest)
    rw [checkPrime.eq_native c, checkChildren.eq_all rest]
end

/-- The compiler uses the verified recursive implementation. -/
@[csimp] theorem checkPrime_eq_native : @checkPrime = @checkPrime.native := by
  funext c
  exact checkPrime.eq_native c

private theorem dvd_pow_self'' (a : Nat) {k : Nat} (hk : k ≠ 0) : a ∣ a ^ k := by
  cases k with
  | zero => exact absurd rfl hk
  | succ k => exact ⟨a ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩

private theorem checkChildren_forall :
    ∀ {l : List (Nat × Nat × PrimeCert)}, checkChildren l = true →
      ∀ x ∈ l, checkPrime.native x.2.2 = true := by
  intro l
  induction l with
  | nil =>
      intro _ x hx
      cases hx
  | cons a rest ih =>
      intro h x hx
      obtain ⟨a1, e, c⟩ := a
      unfold checkChildren at h
      rw [Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h.1
      · exact ih h.2 x hx'

/-! Prime-power combination -/

private theorem prime_eq_of_dvd {p q : Nat} (hp : Prime p) (hq : Prime q)
    (h : p ∣ q) : p = q := by
  rcases hq.2 p h with h1 | h1
  · exact absurd h1 (by have := hp.two_le; omega)
  · exact h1

private theorem coprime_certProd {q : Nat} (hq : Prime q) :
    ∀ {l : List (Nat × Nat × PrimeCert)},
      (∀ x ∈ l, Prime x.2.2.subject) → (∀ x ∈ l, x.2.2.subject ≠ q) →
      Nat.Coprime q (certProd l) := by
  intro l
  induction l with
  | nil =>
      intro _ _
      exact Nat.coprime_one_right q
  | cons a rest ih =>
      intro hprime hne
      obtain ⟨a1, e, c⟩ := a
      have hqc : Nat.Coprime q c.subject := by
        refine hq.coprime_of_not_dvd ?_
        intro hdvd
        exact hne _ (List.mem_cons_self ..)
          (prime_eq_of_dvd hq (hprime _ (List.mem_cons_self ..)) hdvd).symm
      have htail : Nat.Coprime q (certProd rest) :=
        ih (fun x hx => hprime x (List.mem_cons_of_mem _ hx))
          (fun x hx => hne x (List.mem_cons_of_mem _ hx))
      simpa [certProd] using Nat.Coprime.mul_right (hqc.pow_right _) htail

private theorem certProd_mem_dvd :
    ∀ {l : List (Nat × Nat × PrimeCert)} {x : Nat × Nat × PrimeCert},
      x ∈ l → x.2.2.subject ^ (x.2.1 + 1) ∣ certProd l := by
  intro l
  induction l with
  | nil =>
      intro x hx
      cases hx
  | cons a rest ih =>
      intro x hx
      obtain ⟨a1, e, c⟩ := a
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.dvd_mul_right _ _
      · exact Nat.dvd_trans (ih hx') (Nat.dvd_mul_left _ _)

/-- A product of powers of distinct primes, each dividing `m`, divides
`m`. Stated over the same fold the checker computes, so no standalone
`List.prod` API is needed. -/
private theorem certProd_dvd :
    ∀ {l : List (Nat × Nat × PrimeCert)},
      (∀ x ∈ l, Prime x.2.2.subject) → subjectsOk l = true →
      ∀ {m : Nat}, (∀ x ∈ l, x.2.2.subject ^ (x.2.1 + 1) ∣ m) →
      certProd l ∣ m := by
  intro l
  induction l with
  | nil =>
      intro _ _ m _
      exact Nat.one_dvd m
  | cons a rest ih =>
      intro hprime hsub m hdvd
      obtain ⟨h2, hne, hrest⟩ := subjectsOk_cons hsub
      obtain ⟨a1, e, c⟩ := a
      have hqprime : Prime c.subject := hprime _ (List.mem_cons_self ..)
      have hcop : Nat.Coprime (c.subject ^ (e + 1)) (certProd rest) :=
        (coprime_certProd hqprime
          (fun x hx => hprime x (List.mem_cons_of_mem _ hx))
          (fun x hx => hne x hx)).pow_left _
      have hhead : c.subject ^ (e + 1) ∣ m := hdvd _ (List.mem_cons_self ..)
      have htail : certProd rest ∣ m :=
        ih (fun x hx => hprime x (List.mem_cons_of_mem _ hx)) hrest
          (fun x hx => hdvd x (List.mem_cons_of_mem _ hx))
      simpa [certProd] using
        Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hhead htail

/-! The gcd-to-noncongruence transport -/

private theorem mod_ne_one_of_gcd {p n x : Nat} (hp : 2 ≤ p) (hpn : p ∣ n)
    (hx : x < n) (hg : Nat.gcd ((x + n - 1) % n) n = 1) :
    x % p ≠ 1 % p := by
  intro heq
  have h1p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1p] at heq
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with rfl | h
    · rw [Nat.zero_mod] at heq
      omega
    · exact h
  have hpx : p ∣ x - 1 := by
    have := Nat.div_add_mod x p
    exact ⟨x / p, by omega⟩
  have hpxn : p ∣ x + n - 1 := by
    obtain ⟨u, hu⟩ := hpx
    obtain ⟨v, hv⟩ := hpn
    exact ⟨u + v, by rw [Nat.mul_add]; omega⟩
  have hpmod : p ∣ (x + n - 1) % n := by
    have h1 : p ∣ n * ((x + n - 1) / n) :=
      Nat.dvd_trans hpn (Nat.dvd_mul_right n _)
    have h2 : (x + n - 1) % n = (x + n - 1) - n * ((x + n - 1) / n) := by
      have := Nat.div_add_mod (x + n - 1) n
      omega
    rw [h2]
    exact Nat.dvd_sub hpxn h1
  have hdvd1 := Nat.dvd_gcd hpmod hpn
  rw [hg] at hdvd1
  exact absurd (Nat.dvd_one.mp hdvd1) (by omega)

/-! The Pocklington step and checker soundness -/

/-- The per-entry witness conditions give `F ∣ p - 1` for every prime
divisor `p` of `n`: each entry contributes its prime power to
`orderOf a_q p ∣ p - 1`, and the pairwise-coprime powers combine. Shared by
the square-root and cube-root soundness cases. -/
private theorem pock_divisor_step {n F : Nat}
    {factors : List (Nat × Nat × PrimeCert)} (h3 : 3 ≤ n)
    (hF : F ∣ n - 1)
    (hq : ∀ x ∈ factors, Prime x.2.2.subject)
    (hsub : subjectsOk factors = true)
    (hFprod : F = certProd factors)
    (hwit : ∀ x ∈ factors, checkWitness n x.2.2.subject x.1 = true) :
    ∀ p, Prime p → p ∣ n → F ∣ p - 1 := by
  intro p hpprime hpn
  have hp2 := hpprime.two_le
  have hnpos : 0 < n := by omega
  have hstep : ∀ x ∈ factors, x.2.2.subject ^ (x.2.1 + 1) ∣ p - 1 := by
    intro x hx
    have hw := hwit x hx
    rw [checkWitness.eq_native] at hw
    unfold checkWitness.native at hw
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hw
    obtain ⟨hferm, hgcd⟩ := hw
    rw [HexArith.powModNat_eq _ _ _ hnpos] at hferm hgcd
    -- Transport Fermat from mod n to mod p.
    have hferm_p : x.1 ^ (n - 1) % p = 1 % p := by
      calc x.1 ^ (n - 1) % p
          = x.1 ^ (n - 1) % n % p := (Nat.mod_mod_of_dvd _ hpn).symm
        _ = 1 % n % p := by rw [hferm]
        _ = 1 % p := Nat.mod_mod_of_dvd _ hpn
    -- The gcd condition transports to noncongruence mod p.
    have hne_p : x.1 ^ ((n - 1) / x.2.2.subject) % p ≠ 1 % p := by
      have hxlt : x.1 ^ ((n - 1) / x.2.2.subject) % n < n := Nat.mod_lt _ hnpos
      have := mod_ne_one_of_gcd hp2 hpn hxlt hgcd
      intro hcontra
      apply this
      calc x.1 ^ ((n - 1) / x.2.2.subject) % n % p
          = x.1 ^ ((n - 1) / x.2.2.subject) % p := Nat.mod_mod_of_dvd _ hpn
        _ = 1 % p := hcontra
    have hpow_dvd : x.2.2.subject ^ (x.2.1 + 1) ∣ n - 1 := by
      rw [hFprod] at hF
      exact Nat.dvd_trans (certProd_mem_dvd hx) hF
    have horder := prime_pow_dvd_orderOf (hq x hx) hpow_dvd
      hpprime.one_lt hferm_p hne_p
    have hcop : Nat.Coprime x.1 p :=
      coprime_of_pow_mod_eq_one hpprime.one_lt (by omega) hferm_p
    exact Nat.dvd_trans horder (orderOf_dvd_pred hpprime hcop)
  rw [hFprod]
  exact certProd_dvd hq hsub hstep

/-- The square-root Pocklington theorem, over the checker's own data: every
prime divisor `p` of `n` satisfies `F ∣ p - 1`, so `p ≥ F + 1 > √n` and
`n` has no prime divisor at most its square root. -/
private theorem pocklington {n F : Nat}
    {factors : List (Nat × Nat × PrimeCert)} (h2 : 2 ≤ n) (hodd : n % 2 = 1)
    (hF : F ∣ n - 1) (hFF : n < F * F)
    (hq : ∀ x ∈ factors, Prime x.2.2.subject)
    (hsub : subjectsOk factors = true)
    (hFprod : F = certProd factors)
    (hwit : ∀ x ∈ factors, checkWitness n x.2.2.subject x.1 = true) :
    Prime n := by
  have h3 : 3 ≤ n := by omega
  by_cases hp : Prime n
  · exact hp
  exfalso
  obtain ⟨p, hpprime, hpn, hpsq⟩ := exists_prime_le_sqrt (by omega) hp
  have hp2 := hpprime.two_le
  have hFp : F ∣ p - 1 :=
    pock_divisor_step h3 hF hq hsub hFprod hwit p hpprime hpn
  have hFle : F ≤ p - 1 := Nat.le_of_dvd (by omega) hFp
  have hsq : F * F ≤ (p - 1) * (p - 1) := Nat.mul_le_mul hFle hFle
  have hlt : (p - 1) * (p - 1) < p * p := by
    rcases p with _ | p'
    · omega
    · have e1 : p' + 1 - 1 = p' := by omega
      rw [e1]
      have hexp : (p' + 1) * (p' + 1) = p' * p' + 2 * p' + 1 := by
        rw [Nat.add_mul, Nat.mul_add]
        omega
      omega
  omega

private theorem checkPockArith_spec {n : Nat}
    {factors : List (Nat × Nat × PrimeCert)}
    (h : checkPockArith n factors = true) :
    2 ≤ n ∧ n % 2 = 1 ∧ subjectsOk factors = true ∧
      ∃ F, F = certProd factors ∧ F ∣ n - 1 ∧ n < F * F ∧
        ∀ x ∈ factors, checkWitness n x.2.2.subject x.1 = true := by
  rw [checkPockArith.eq_native] at h
  unfold checkPockArith.native at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h2, hodd⟩, hm⟩ := h
  rw [Bool.and_eq_true] at h2
  obtain ⟨h2', hodd'⟩ := h2
  split at hm
  · cases hm
  next F hprod =>
    rw [Bool.and_eq_true, Bool.and_eq_true] at hm
    obtain ⟨⟨hdvd, hlt⟩, hall⟩ := hm
    refine ⟨by simpa using h2', by simpa using hodd', hodd,
      F, certProduct_eq _ _ hprod,
      Nat.dvd_of_mod_eq_zero (by simpa using hdvd),
      by simpa using hlt, ?_⟩
    rw [List.all_eq_true] at hall
    intro x hx
    exact hall x hx

private theorem checkPock3Arith_spec {n r s w : Nat}
    {factors : List (Nat × Nat × PrimeCert)}
    (h : checkPock3Arith n r s w factors = true) :
    2 ≤ n ∧ n % 2 = 1 ∧ subjectsOk factors = true ∧
      ∃ F, F = certProd factors ∧ F ∣ n - 1 ∧ F % 2 = 0 ∧
        (n - 1) / F % 2 = 1 ∧ (n - 1) / F = 2 * F * s + r ∧
        1 ≤ r ∧ r < 2 * F ∧
        n < (F + 1) * (2 * F * F + (r - 1) * F + 1) ∧
        (s = 0 ∨ r * r < 8 * s ∨ ∀ t, t * t ≠ r * r - 8 * s) ∧
        ∀ x ∈ factors, checkWitness n x.2.2.subject x.1 = true := by
  unfold checkPock3Arith at h
  simp only [checkWitnesses.eq_native, checkWitnesses.native] at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h2, hodd⟩, hm⟩ := h
  rw [Bool.and_eq_true] at h2
  obtain ⟨h2', hodd'⟩ := h2
  split at hm
  · cases hm
  next F hprod =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff,
      beq_iff_eq, List.all_eq_true] at hm
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hdvd, heven⟩, hrodd⟩, hdec⟩, hr1⟩, hr2⟩, hbound⟩,
      hdisc⟩, hall⟩ := hm
    refine ⟨by simpa using h2', by simpa using hodd', hodd,
      F, certProduct_eq _ _ hprod, Nat.dvd_of_mod_eq_zero hdvd,
      heven, hrodd, hdec, hr1, hr2, hbound, ?_, hall⟩
    rcases hdisc with (hs0 | hlt) | ⟨hw1, hw2⟩
    · exact Or.inl hs0
    · exact Or.inr (Or.inl hlt)
    · exact Or.inr (Or.inr (not_square_of_sqrt_witness hw1 hw2))

private theorem checkPock3SieveArith_spec {n r s w m : Nat}
    {factors : List (Nat × Nat × PrimeCert)}
    (h : checkPock3SieveArith n r s w m factors = true) :
    2 ≤ n ∧ n % 2 = 1 ∧ subjectsOk factors = true ∧
      ∃ F, F = certProd factors ∧ F ∣ n - 1 ∧ F % 2 = 0 ∧
        (n - 1) / F % 2 = 1 ∧ (n - 1) / F = 2 * F * s + r ∧
        1 ≤ r ∧ r < 2 * F ∧
        1 ≤ m ∧ (∀ l, 1 ≤ l → l < m → ¬ l * F + 1 ∣ n) ∧
        2 * s + m * m < (2 * F + r) * m + 2 ∧
        (s = 0 ∨ r * r < 8 * s ∨ ∀ t, t * t ≠ r * r - 8 * s) ∧
        ∀ x ∈ factors, checkWitness n x.2.2.subject x.1 = true := by
  unfold checkPock3SieveArith at h
  simp only [checkWitnesses.eq_native, checkWitnesses.native] at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h2, hodd⟩, hm⟩ := h
  rw [Bool.and_eq_true] at h2
  obtain ⟨h2', hodd'⟩ := h2
  split at hm
  · cases hm
  next F hprod =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff,
      beq_iff_eq, List.all_eq_true] at hm
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdvd, heven⟩, hrodd⟩, hdec⟩, hr1⟩, hr2⟩, hm⟩, hdiv⟩, hbound⟩,
      hdisc⟩, hall⟩ := hm
    refine ⟨by simpa using h2', by simpa using hodd', hodd,
      F, certProduct_eq _ _ hprod, Nat.dvd_of_mod_eq_zero hdvd,
      heven, hrodd, hdec, hr1, hr2, hm,
      (fun l hl hb => checkDivisors_spec n F (m - 1) hdiv l hl (by omega)), hbound, ?_, hall⟩
    rcases hdisc with (hs0 | hlt) | ⟨hw1, hw2⟩
    · exact Or.inl hs0
    · exact Or.inr (Or.inl hlt)
    · exact Or.inr (Or.inr (not_square_of_sqrt_witness hw1 hw2))

/-- Pocklington replay with separately proved child primes. This permits a
certificate generator to share child proofs across many parent certificates.
Only each child's subject is used; `checkPockArith` validates the parent
arithmetic, factor ordering and witnesses. The `PrimeCert` payload is ignored
apart from its subject: a `.small q` here is not checked against the table.
The separate `hprimes` hypothesis must prove that `q` is prime. -/
theorem prime_of_pocklington {n : Nat}
    {factors : List (Nat × Nat × PrimeCert)}
    (hcheck : checkPockArith n factors = true)
    (hprimes : ∀ x ∈ factors, Prime x.2.2.subject) : Prime n := by
  obtain ⟨h2, hodd, hsub, F, hFprod, hFdvd, hFF, hwit⟩ :=
    checkPockArith_spec hcheck
  exact pocklington h2 hodd hFdvd hFF hprimes hsub hFprod hwit

private theorem prime_of_checkPrime_aux :
    ∀ N c, PrimeCert.subject c = N → checkPrime.native c = true → Prime N := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro c hsubj hcheck
    cases c with
    | small m =>
        have hm : m = N := hsubj
        subst hm
        unfold checkPrime.native at hcheck
        exact mem_primeTable_prime (isTablePrime_iff.mp hcheck)
    | pock m factors =>
        have hm : m = N := hsubj
        subst hm
        unfold checkPrime.native at hcheck
        rw [Bool.and_eq_true] at hcheck
        obtain ⟨harith, hchildren⟩ := hcheck
        obtain ⟨h2, hodd, hsub, F, hFprod, hFdvd, hFF, hwit⟩ :=
          checkPockArith_spec harith
        have hchildprime : ∀ x ∈ factors, Prime x.2.2.subject := by
          intro x hx
          have hcheckx := checkChildren_forall hchildren x hx
          have hq2 : 2 ≤ x.2.2.subject := subjectsOk_forall hsub x hx
          have hqltm : x.2.2.subject < m := by
            have hqdvd : x.2.2.subject ∣ m - 1 := by
              refine Nat.dvd_trans ?_ hFdvd
              rw [hFprod]
              exact Nat.dvd_trans (dvd_pow_self'' _ (by omega))
                (certProd_mem_dvd hx)
            have hm3 : 3 ≤ m := by omega
            have := Nat.le_of_dvd (by omega : 0 < m - 1) hqdvd
            omega
          exact ih x.2.2.subject hqltm x.2.2 rfl hcheckx
        exact pocklington h2 hodd hFdvd hFF hchildprime hsub hFprod hwit
    | pock3 m r s w factors =>
        have hm : m = N := hsubj
        subst hm
        unfold checkPrime.native at hcheck
        rw [Bool.and_eq_true] at hcheck
        obtain ⟨harith, hchildren⟩ := hcheck
        obtain ⟨h2, hodd, hsub, F, hFprod, hFdvd, hFeven, hRodd, hdec, hr1,
          hr2, hbound, hdisc, hwit⟩ := checkPock3Arith_spec harith
        have hF0 : 0 < F := by
          rcases Nat.eq_zero_or_pos F with h0 | h
          · subst h0
            have := Nat.eq_zero_of_zero_dvd hFdvd
            omega
          · exact h
        have hchildprime : ∀ x ∈ factors, Prime x.2.2.subject := by
          intro x hx
          have hcheckx := checkChildren_forall hchildren x hx
          have hq2 : 2 ≤ x.2.2.subject := subjectsOk_forall hsub x hx
          have hqltm : x.2.2.subject < m := by
            have hqdvd : x.2.2.subject ∣ m - 1 := by
              refine Nat.dvd_trans ?_ hFdvd
              rw [hFprod]
              exact Nat.dvd_trans (dvd_pow_self'' _ (by omega))
                (certProd_mem_dvd hx)
            have hm3 : 3 ≤ m := by omega
            have := Nat.le_of_dvd (by omega : 0 < m - 1) hqdvd
            omega
          exact ih x.2.2.subject hqltm x.2.2 rfl hcheckx
        exact pocklington3 (by omega) hFdvd hFeven hF0 hRodd hdec hr1 hr2
          hbound hdisc
          (pock_divisor_step (by omega) hFdvd hchildprime hsub hFprod hwit)
    | pock3Sieve m r s w k factors =>
        have hm : m = N := hsubj
        subst hm
        unfold checkPrime.native at hcheck
        rw [Bool.and_eq_true] at hcheck
        obtain ⟨harith, hchildren⟩ := hcheck
        obtain ⟨h2, hodd, hsub, F, hFprod, hFdvd, hFeven, hRodd, hdec, hr1,
          hr2, hk, hdiv, hbound, hdisc, hwit⟩ := checkPock3SieveArith_spec harith
        have hF0 : 0 < F := by
          rcases Nat.eq_zero_or_pos F with h0 | h
          · subst h0
            have := Nat.eq_zero_of_zero_dvd hFdvd
            omega
          · exact h
        have hchildprime : ∀ x ∈ factors, Prime x.2.2.subject := by
          intro x hx
          have hcheckx := checkChildren_forall hchildren x hx
          have hq2 : 2 ≤ x.2.2.subject := subjectsOk_forall hsub x hx
          have hqltm : x.2.2.subject < m := by
            have hqdvd : x.2.2.subject ∣ m - 1 := by
              refine Nat.dvd_trans ?_ hFdvd
              rw [hFprod]
              exact Nat.dvd_trans (dvd_pow_self'' _ (by omega))
                (certProd_mem_dvd hx)
            have hm3 : 3 ≤ m := by omega
            have := Nat.le_of_dvd (by omega : 0 < m - 1) hqdvd
            omega
          exact ih x.2.2.subject hqltm x.2.2 rfl hcheckx
        exact pocklington3Sieve (by omega) hFdvd hFeven hF0 hRodd hdec hr1 hr2
          hk hdiv hbound hdisc
          (pock_divisor_step (by omega) hFdvd hchildprime hsub hFprod hwit)

/-- Checker soundness: an accepted certificate proves its subject prime.
The whole conclusion; no certificate-existence, checker-completeness, or
search-completeness claim accompanies it. -/
theorem prime_of_checkPrime {c : PrimeCert} (h : checkPrime c = true) :
    Prime c.subject :=
  prime_of_checkPrime_aux _ c rfl ((checkPrime.eq_native c) ▸ h)

/-- Single-Bool-slot wrapper for the tactic reifier: the kernel verifies the
subject match and the certificate replay in one reduction. -/
theorem prime_of_checkPrimeAt {n : Nat} {c : PrimeCert}
    (h : (c.subject == n && checkPrime c) = true) : Prime n := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1 ▸ prime_of_checkPrime h.2

/-- An accepted certificate tied to the number requested by its caller. The
subject equality is load-bearing: `checkPrime` proves primality of
`c.subject`, not of an unrelated input that happened to request `c`. -/
structure CheckedPrimeCert (n : Nat) where
  /-- The certificate itself. -/
  raw : PrimeCert
  /-- The certificate is about the requested number. -/
  subject_eq : raw.subject = n
  /-- The checker accepts. -/
  valid : checkPrime raw = true

/-- The primality of the requested subject. -/
theorem CheckedPrimeCert.prime {n : Nat} (c : CheckedPrimeCert n) : Prime n :=
  c.subject_eq ▸ prime_of_checkPrime c.valid

/-! Regression coverage: table leaves, accepted Pocklington nodes, explicit
zero and truncating-division boundaries for bounded multiplication, structural
preflight on long canonical lists and late malformed entries, and rejected
certificates covering the arithmetic clauses and adversarial products. The
checker's negative cases matter as much as its positive ones, and no oracle
produces them. -/

set_option maxRecDepth 100000   -- table walks in the guards below

/-- A long canonical factor list for the linear structural-preflight guards. -/
private def longFactors : List (Nat × Nat × PrimeCert) :=
  (List.range 2048).map fun i => (0, 0, .small (i + 2))

#guard subjectsOk longFactors = true
#guard subjectsOk (longFactors ++ [(0, 0, .small 2049)]) = false

#guard checkPrime (.small 97) = true
#guard checkPrime (.small 100) = false
#guard checkPrime (.small 100003) = false  -- prime, but above the table bound
#guard checkPrime (.pock 7 [(2, 0, .small 3)]) = true
#guard checkPrime (.pock 31 [(3, 0, .small 3), (3, 0, .small 5)]) = true
#guard checkPrime (.pock 31 [(3, 0, .small 5), (3, 0, .small 3)]) = false
  -- distinct but noncanonical subjects
#guard checkPrime (.pock 2027 [(2, 0, .small 1013)]) = true
#guard checkPrime (.pock 13 [(2, 0, .small 3)]) = false      -- F² ≤ n
#guard checkPrime (.pock 7 [(2, 0, .small 4)]) = false       -- composite factor
#guard checkPrime (.pock 7 [(6, 0, .small 3)]) = false       -- gcd witness fails
#guard checkPrime (.pock 11 [(2, 0, .small 7)]) = false      -- 7 ∤ 10
#guard boundedPowMul 0 0 1 1 = some 0                        -- zero base
#guard boundedPowMul 0 5 0 1048576 = some 0                  -- zero accumulator
#guard boundedPowMul 7 2 3 1 = some 6                        -- rounded bound accepts
#guard boundedPowMul 7 2 4 1 = none                          -- next product is 8
#guard checkPrime (.pock 7 [(2, 0, .small (2 ^ 4096))]) = false
  -- huge child subject is rejected by the first product bound check
#guard checkPrime (.pock 97 [(5, 1048576, .small 2)]) = false
  -- huge exponent aborts when its next bounded multiplication would cross 96
#guard checkPrime (.pock 31 [(3, 0, .small 5), (3, 0, .small 7)]) = false
  -- each factor fits under 30, but their next combined product would be 35
-- Cube-root arm: n = 199 with F = 6 sits squarely in the cube-root regime
-- (F² = 36 ≤ 199 < 847 = (F+1)(2F² + (r-1)F + 1), R = 33 = 2·6·2 + 9,
-- discriminant 9² - 8·2 = 65 with witness 8² < 65 < 9²).
#guard checkPrime (.pock3 199 9 2 8 [(3, 0, .small 2), (2, 0, .small 3)]) = true
#guard checkPrime (.pock3 199 9 2 7 [(3, 0, .small 2), (2, 0, .small 3)]) = false
  -- wrong square-root witness
#guard checkPrime (.pock3 199 33 0 0 [(3, 0, .small 2), (2, 0, .small 3)]) = false
  -- r out of range
#guard checkPrime (.pock3 199 9 2 8 [(2, 0, .small 3)]) = false
  -- F = 3 odd
#guard checkPrime (.pock 199 [(3, 0, .small 2), (2, 0, .small 3)]) = false
  -- the same data fails the square-root arm: F² ≤ n

end Nat

end Hex

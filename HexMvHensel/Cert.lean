/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvHensel.Seed

@[expose] public section

/-!
Executable validation and the small, modulus-independent lift certificate.
The checker deliberately does not call `valid`: the prime power is search
state, not part of what a successful decomposition means.
-/

namespace Hex.MvHensel

open Hex
open Hex.MvPoly

/-- The lifted factor tuple is the complete certificate payload. -/
structure Cert (n : Nat)
    (cmp : Mono (n + 1) → Mono (n + 1) → Ordering)
    [IsMonomialOrder cmp] where
  /-- Reconstructed multivariate factors in image-factor order. -/
  factors : List (MvPoly (n + 1) Int cmp)
  deriving BEq, DecidableEq

variable {n : Nat}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp] [IsMonomialOrder cmp']

/-! # Ordered validation helpers -/

def imagesPositive : List ZPoly → Bool
  | [] => true
  | F :: Fs =>
      (match F.degree? with
       | some degree => 0 < degree
       | none => false) && imagesPositive Fs

def firstLeadingImage? (point : Fin n → Int) :
    Nat → List ZPoly → List (MvPoly n Int cmp') → Option Nat
  | _, [], [] => none
  | j, F :: Fs, L :: Ls =>
      if MvPoly.eval point L != F.leadingCoeff then some j
      else firstLeadingImage? point (j + 1) Fs Ls
  | j, _, _ => some j

def firstPrimeDivisor? (p : Nat) : Nat → List ZPoly → Option Nat
  | _, [] => none
  | j, F :: Fs =>
      if F.leadingCoeff % (p : Int) = 0 then some j
      else firstPrimeDivisor? p (j + 1) Fs

def firstWitnessDegree? : Nat → List ZPoly → List ZPoly → Option Nat
  | _, [], [] => none
  | j, F :: Fs, sigma :: sigmas =>
      let bad : Bool := match sigma.degree?, F.degree? with
        | some ds, some dF => decide (dF ≤ ds)
        | _, _ => false
      if bad then some j else firstWitnessDegree? (j + 1) Fs sigmas
  | j, _, _ => some j

/-- The first failed V1--V6 condition, in the diagnostic order fixed by the
SPEC. -/
def failure? (inp : Input n cmp cmp') : Option Failure :=
  let i := inp.setup.main
  let point := inp.setup.point
  let image := imageAt i cmp' point inp.target
  let mainDegree := MvPoly.degreeOf i inp.target
  if inp.images.length != inp.leading.length ||
      inp.images.length != inp.witness.length || inp.images.isEmpty ||
      inp.setup.exponent = 0 || mainDegree = 0 ||
      !imagesPositive inp.images then
    some .arity
  else if image.degree?.getD 0 != mainDegree then
    some .degreeDrop
  else if uniProduct inp.images != image then
    some .imageProduct
  else if mvProduct inp.leading != lcIn i cmp' inp.target then
    some .leadingProduct
  else match firstLeadingImage? point 0 inp.images inp.leading with
    | some j => some (.leadingImage j)
    | none =>
        match firstPrimeDivisor? inp.setup.prime.m 0 inp.images with
        | some j => some (.primeDividesLc j)
        | none =>
            if !coeffsDivisible inp.setup.modulus
                (zSub (uniCombination inp.witness
                  (complements inp.images)) 1) then
              some .notCoprime
            else match firstWitnessDegree? 0 inp.images inp.witness with
              | some j => some (.witnessDegree j)
              | none => none

/-- Boolean form of the V1--V6 input contract. -/
def valid (inp : Input n cmp cmp') : Bool :=
  (failure? inp).isNone

/-! # Certificate checker -/

/-- What a checked certificate witnesses. -/
def IsLiftOf (inp : Input n cmp cmp')
    (fs : List (MvPoly (n + 1) Int cmp)) : Prop :=
  fs.length = inp.images.length ∧
  mvProduct fs = inp.target ∧
  (∀ j, j < inp.images.length →
    imageAt inp.setup.main cmp' inp.setup.point (fs.getD j 0) =
      inp.images.getD j 0) ∧
  (∀ j, j < inp.images.length →
    lcIn inp.setup.main cmp' (fs.getD j 0) = inp.leading.getD j 0)

/-- Replay the exact product, image, and leading-coefficient conditions. -/
def check (inp : Input n cmp cmp') (cert : Cert n cmp) : Bool :=
  cert.factors.length == inp.images.length &&
    mvProduct cert.factors == inp.target &&
    (List.range inp.images.length).all (fun j =>
      imageAt inp.setup.main cmp' inp.setup.point
          (cert.factors.getD j 0) == inp.images.getD j 0) &&
    (List.range inp.images.length).all (fun j =>
      lcIn inp.setup.main cmp' (cert.factors.getD j 0) ==
        inp.leading.getD j 0)

/-- The executable checker implies the semantic certificate predicate. -/
theorem check_sound {inp : Input n cmp cmp'} {cert : Cert n cmp}
    (h : check inp cert = true) : IsLiftOf inp cert.factors := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  rcases h with ⟨⟨⟨hlen, hproduct⟩, himages⟩, hleading⟩
  exact ⟨hlen, hproduct, himages, hleading⟩

end Hex.MvHensel

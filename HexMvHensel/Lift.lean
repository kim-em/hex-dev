/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvHensel.Cert

@[expose] public section

/-!
The stagewise EEZ lift.  Computation takes place after shifting the evaluation
point to zero.  Every stage first installs the prescribed leading coefficient
through the new variable, then corrects each power of that variable using the
multivariate diophantine solver at the fixed coefficient modulus.
-/

namespace Hex.MvHensel

open Hex
open Hex.MvPoly

variable {n : Nat}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp] [IsMonomialOrder cmp']

/-! # Stage helpers -/

/-- Multivariate complementary products, in tuple order. -/
def mvComplements {k : Nat} {order : Mono k → Mono k → Ordering}
    [IsMonomialOrder order] :
    List (MvPoly k Int order) → List (MvPoly k Int order) :=
  complementProducts (· * ·) 1

/-- Install one prefix of the prescribed shifted leading coefficients. -/
def installLeading? (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (count : Nat) :
    List (MvPoly (n + 1) Int cmp) → List (MvPoly n Int cmp') →
      Option (List (MvPoly (n + 1) Int cmp))
  | [], [] => some []
  | f :: fs, L :: Ls => do
      let tail ← installLeading? i cmp' count fs Ls
      some (setLc i cmp' (prefixVars count L) f :: tail)
  | _, _ => none

/-- Add one reduced, box-truncated correction at a selected variable power. -/
def applyCorrections? (q : Nat) (i : Fin (n + 1))
    (d : Fin n → Nat) (selected : Fin (n + 1)) (power : Nat) :
    List (MvPoly (n + 1) Int cmp) →
      List (MvPoly (n + 1) Int cmp) →
        Option (List (MvPoly (n + 1) Int cmp))
  | [], [] => some []
  | f :: fs, delta :: deltas => do
      let tail ← applyCorrections? q i d selected power fs deltas
      let correction := embedPower selected power
        (reduceMod q (truncate i d delta))
      some ((f + correction) :: tail)
  | _, _ => none

/-- Lift through every power of one non-main variable. -/
def liftStage (q : Nat) (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (d : Fin n → Nat) (images witness : List ZPoly)
    (shiftedTarget : MvPoly (n + 1) Int cmp)
    (shiftedLeading : List (MvPoly n Int cmp'))
    (y : Fin n) (factors : List (MvPoly (n + 1) Int cmp)) :
    Option (List (MvPoly (n + 1) Int cmp)) := do
  let installed ← installLeading? i cmp' (y.val + 1) factors shiftedLeading
  let selected := remainingVar i y
  let bases := mvComplements (installed.map (sliceVar selected 0))
  let stageTarget := prefixNonMain i (y.val + 1) shiftedTarget
  (List.range (d y)).foldlM
    (fun current k => do
      let error := reduceMod q
        (truncate i d (stageTarget - mvProduct current))
      let rhs := sliceVar selected (k + 1) error
      let deltas ←
        diophantinePrefix q i cmp' y.val d bases images witness rhs
      applyCorrections? q i d selected (k + 1) current deltas)
    installed

/-- Run all non-main-variable stages in coordinate order. -/
def liftStages (q : Nat) (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (d : Fin n → Nat) (images witness : List ZPoly)
    (shiftedTarget : MvPoly (n + 1) Int cmp)
    (shiftedLeading : List (MvPoly n Int cmp'))
    (initial : List (MvPoly (n + 1) Int cmp)) :
    Option (List (MvPoly (n + 1) Int cmp)) :=
  (List.finRange n).foldlM
    (fun factors y =>
      liftStage q i cmp' d images witness shiftedTarget shiftedLeading y factors)
    initial

/-- Build the shifted factors through full box precision. -/
def liftShifted? (inp : Input n cmp cmp') :
    Option (List (MvPoly (n + 1) Int cmp)) := do
  let i := inp.setup.main
  let point := inp.setup.point
  let shiftedTarget := shift i point inp.target
  let shiftedLeading := inp.leading.map (shiftAll point)
  let initial ← seedTuple? i cmp' inp.images shiftedLeading
  let d : Fin n → Nat := fun j =>
    MvPoly.degreeOf (remainingVar i j) shiftedTarget
  liftStages inp.setup.modulus i cmp' d inp.images inp.witness
    shiftedTarget shiftedLeading initial

/-- Return from shifted coordinates to the caller's coordinates. -/
def reconstruct (i : Fin (n + 1)) (point : Fin n → Int)
    (fs : List (MvPoly (n + 1) Int cmp)) :
    List (MvPoly (n + 1) Int cmp) :=
  fs.map (unshift i point)

/-! # Public lift and retries -/

/-- Perform one checked lift at the exponent stored in `inp.setup`. -/
def lift (inp : Input n cmp cmp') : Except Failure (Cert n cmp) :=
  match failure? inp with
  | some failure => .error failure
  | none =>
      match liftShifted? inp with
      | none => .error (.reconstruct inp.setup.modulus)
      | some shifted =>
          let cert : Cert n cmp :=
            { factors := reconstruct inp.setup.main inp.setup.point shifted }
          if check inp cert then .ok cert
          else .error (.reconstruct inp.setup.modulus)

/-- Rebuild an input at a new exponent and derive the corresponding witness. -/
def raiseExponent? (inp : Input n cmp cmp') : Option (Input n cmp cmp') := do
  let setup : Setup n :=
    { main := inp.setup.main
      point := inp.setup.point
      prime := inp.setup.prime
      exponent := 2 * inp.setup.exponent }
  let witness ← witnessOf? setup inp.images
  some
    { setup := setup
      target := inp.target
      images := inp.images
      leading := inp.leading
      witness := witness }

/-- Retry reconstruction by repeatedly doubling the exponent. -/
def liftWithAux : Nat → Input n cmp cmp' → Except Failure (Cert n cmp)
  | 0, inp => lift inp
  | fuel + 1, inp =>
      match lift inp with
      | .ok cert => .ok cert
      | .error failure@(.reconstruct _) =>
          match raiseExponent? inp with
          | none => .error failure
          | some next => liftWithAux fuel next
      | .error failure => .error failure

/-- Lift with the configured number of exponent doublings. -/
def liftWith (cfg : Config) (inp : Input n cmp cmp') :
    Except Failure (Cert n cmp) :=
  liftWithAux cfg.doublings inp

/-! # Phase-1 correctness API -/

/-- Every certificate returned by `lift` passes the independent checker. -/
theorem lift_checks {inp : Input n cmp cmp'} {cert : Cert n cmp}
    (h : lift inp = .ok cert) : check inp cert = true := by
  sorry

/-- Once V1--V6 hold, reconstruction is the only possible failure. -/
theorem lift_progress {inp : Input n cmp cmp'} (h : valid inp = true) :
    (∃ cert, lift inp = .ok cert) ∨
      (∃ modulus, lift inp = .error (.reconstruct modulus)) := by
  sorry

end Hex.MvHensel

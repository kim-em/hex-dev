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

/-- Two shifted factors have the same image, selected-variable leading
coefficient, and selected-variable degree. -/
def SameFrame (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (f g : MvPoly (n + 1) Int cmp) : Prop :=
  imageAt i cmp' (fun _ => 0) g = imageAt i cmp' (fun _ => 0) f ∧
  lcIn i cmp' g = lcIn i cmp' f ∧
  MvPoly.degreeOf i g = MvPoly.degreeOf i f

/-- A positive power in a non-main variable and a lower-main-degree
correction preserve every factor's shifted image, leading coefficient, and
main-variable degree. This is the exact preservation fact used by the stage
loop after truncation and symmetric reduction. -/
theorem applyCorrections_frame {q : Nat} {i : Fin (n + 1)}
    {d : Fin n → Nat} {selected : Fin (n + 1)} {power : Nat}
    {factors deltas updated : List (MvPoly (n + 1) Int cmp)}
    (hselected : ∃ y : Fin n, selected = remainingVar i y)
    (hpower : 0 < power)
    (hlength : factors.length = deltas.length)
    (hdegree : ∀ j, j < factors.length →
      MvPoly.degreeOf i (deltas.getD j 0) <
        MvPoly.degreeOf i (factors.getD j 0))
    (happly : applyCorrections? q i d selected power factors deltas =
      some updated) :
    updated.length = factors.length ∧
      ∀ j, j < factors.length →
        SameFrame i cmp' (factors.getD j 0) (updated.getD j 0) := by
  sorry

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

/-! # Stage invariant -/

/-- The state carried between EEZ stages. It records exactly the facts used
at the next `diophantinePrefix` call: fixed image and main degree, installed
leading prefix, absence of future variables, and the product equation through
the completed prefix. -/
def IsStage (inp : Input n cmp cmp') (count : Nat)
    (factors : List (MvPoly (n + 1) Int cmp)) : Prop :=
  let i := inp.setup.main
  let shiftedTarget := shift i inp.setup.point inp.target
  let shiftedLeading := inp.leading.map (shiftAll inp.setup.point)
  let d : Fin n → Nat := fun j =>
    MvPoly.degreeOf (remainingVar i j) shiftedTarget
  factors.length = inp.images.length ∧
  (∀ j, j < inp.images.length →
    imageAt i cmp' (fun _ => 0) (factors.getD j 0) =
      inp.images.getD j 0) ∧
  (∀ j, j < inp.images.length →
    lcIn i cmp' (factors.getD j 0) =
      prefixVars count (shiftedLeading.getD j 0)) ∧
  (∀ j, j < inp.images.length →
    MvPoly.degreeOf i (factors.getD j 0) =
      (inp.images.getD j 0).degree?.getD 0) ∧
  (∀ j, j < inp.images.length →
    prefixNonMain i count (factors.getD j 0) = factors.getD j 0) ∧
  BoxCongr i d inp.setup.modulus (mvProduct factors)
    (prefixNonMain i count shiftedTarget)

/-- Valid seeds establish the stage-zero invariant. -/
theorem seedTuple_stage {inp : Input n cmp cmp'} (h : valid inp = true) :
    ∃ initial,
      seedTuple? inp.setup.main cmp' inp.images
          (inp.leading.map (shiftAll inp.setup.point)) = some initial ∧
        IsStage inp 0 initial := by
  sorry

/-- The stage invariant makes every internal diophantine solve reachable and
is preserved while one more non-main variable is introduced. -/
theorem liftStage_spec {inp : Input n cmp cmp'} (h : valid inp = true)
    (y : Fin n) {factors : List (MvPoly (n + 1) Int cmp)}
    (hstage : IsStage inp y.val factors) :
    let i := inp.setup.main
    let shiftedTarget := shift i inp.setup.point inp.target
    let shiftedLeading := inp.leading.map (shiftAll inp.setup.point)
    let d : Fin n → Nat := fun j =>
      MvPoly.degreeOf (remainingVar i j) shiftedTarget
    ∃ next,
      liftStage inp.setup.modulus i cmp' d inp.images inp.witness
          shiftedTarget shiftedLeading y factors = some next ∧
        IsStage inp (y.val + 1) next := by
  sorry

/-- Consequently a valid input cannot take the partial `none` branch while
building shifted factors. -/
theorem liftShifted_some {inp : Input n cmp cmp'} (h : valid inp = true) :
    ∃ shifted, liftShifted? inp = some shifted ∧ IsStage inp n shifted := by
  sorry

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

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyDet.Packed

@[expose] public section

namespace Hex.PolyDet.Packed

open Hex.Matrix Hex.MvPoly.Kernel Hex.Kronecker

/-- One product determined entirely by the original determinant witness. -/
structure Product (R : Type) where
  row : Nat
  inner : Nat
  width : Nat
  left : List R
  right : List (List R)
  result : List R
  deriving Repr

/-- The same prefix products consumed by the kernel checker. -/
def products (ops : DetOps R) (n : Nat) (a : List (List R)) :
    DetWitness R → List (Product R)
  | .triangular swaps ts d =>
      (ts.zipIdx).map fun (t, i) =>
        { row := i, inner := i + 1, width := i + 1, left := t
          right := leading (i + 1) (DetWitness.permute swaps a)
          result := List.replicate i ops.zero ++ [next ops swaps d i (ts.drop (i + 1))] }
  | .singular v =>
      [{ row := 0, inner := n, width := n, left := v, right := a,
         result := List.replicate n ops.zero }]

def Product.map (f : R → S) (a : Product R) : Product S :=
  { a with left := a.left.map f, right := a.right.map (List.map f), result := a.result.map f }

/-- Exact crossover coordinates; uncovered products always use term lists. -/
structure Key where
  packedBits : Nat
  leftSupport : Nat
  /-- List support or retained tree nodes, according to the selected table. -/
  rightSize : Nat
  resultSupport : Nat
  inner : Nat
  deriving Repr, BEq, Inhabited

def support (a : List (PolyList C)) : Nat := a.foldl (fun s p => s + p.length) 0

def Product.key (a : Product (PolyList Int)) (s : SizeBound) : Key :=
  ⟨s.packedBits, support a.left, support a.right.flatten, support a.result, a.inner⟩

/-- Product keys from six paired comparisons with a smaller packed median.
The retained measurements and selection rule are in `reports/bench-results/hex-det-packed/`.
Uncovered witnesses continue to use term lists. -/
def crossover : List Key := [
  ⟨6, 1, 1, 1, 1⟩,
  ⟨12, 2, 4, 2, 2⟩,
  ⟨24, 2, 5, 2, 3⟩,
  ⟨34, 1, 4, 4, 1⟩,
  ⟨35, 1, 1, 1, 1⟩,
  ⟨41, 1, 4, 4, 1⟩,
  ⟨45, 4, 8, 4, 4⟩,
  ⟨62, 1, 4, 4, 1⟩,
  ⟨83, 1, 4, 4, 1⟩,
  ⟨98, 8, 16, 8, 2⟩,
  ⟨104, 1, 4, 4, 1⟩,
  ⟨111, 1, 4, 4, 1⟩,
  ⟨118, 1, 4, 4, 1⟩,
  ⟨139, 1, 4, 4, 1⟩,
  ⟨175, 8, 16, 11, 2⟩,
  ⟨186, 8, 16, 11, 2⟩,
  ⟨188, 1, 4, 4, 1⟩,
  ⟨208, 25, 36, 12, 3⟩,
  ⟨340, 49, 64, 16, 4⟩,
  ⟨362, 8, 16, 12, 2⟩,
  ⟨400, 36, 36, 21, 3⟩,
  ⟨485, 2, 4, 1, 2⟩,
  ⟨527, 8, 16, 13, 2⟩,
  ⟨538, 8, 16, 15, 2⟩,
  ⟨576, 33, 36, 22, 3⟩,
  ⟨660, 87, 64, 30, 4⟩,
  ⟨784, 41, 36, 34, 3⟩,
  ⟨791, 8, 16, 15, 2⟩,
  ⟨890, 8, 16, 10, 2⟩,
  ⟨1187, 8, 16, 13, 2⟩,
  ⟨1280, 86, 64, 36, 4⟩,
  ⟨1300, 135, 64, 54, 4⟩,
  ⟨1408, 42, 36, 41, 3⟩,
  ⟨1451, 8, 16, 15, 2⟩,
  ⟨1529, 3, 9, 1, 3⟩,
  ⟨1546, 1, 4, 4, 1⟩,
  ⟨1979, 8, 16, 15, 2⟩,
  ⟨2000, 39, 36, 35, 3⟩,
  ⟨3179, 4, 16, 1, 4⟩,
  ⟨3600, 151, 64, 88, 4⟩,
  ⟨3840, 45, 36, 50, 3⟩,
  ⟨4096, 30, 36, 20, 3⟩,
  ⟨5040, 126, 64, 66, 4⟩,
  ⟨5488, 39, 36, 38, 3⟩,
  ⟨5760, 43, 36, 45, 3⟩,
  ⟨7655, 8, 16, 15, 2⟩,
  ⟨11960, 184, 64, 130, 4⟩,
  ⟨12096, 45, 36, 51, 3⟩,
  ⟨12500, 80, 64, 35, 4⟩,
  ⟨12500, 200, 64, 140, 4⟩,
  ⟨14080, 134, 64, 79, 4⟩,
  ⟨19840, 43, 36, 47, 3⟩,
  ⟨47940, 188, 64, 143, 4⟩,
  ⟨48020, 204, 64, 160, 4⟩
]

/-- Tree-entry keys are fitted independently from forced tree proof timings. -/
def treeCrossover : List Key := [
  ⟨5, 1, 1, 1, 1⟩,
  ⟨7, 1, 3, 2, 1⟩,
  ⟨7, 1, 6, 1, 1⟩,
  ⟨11, 1, 4, 1, 2⟩,
  ⟨11, 1, 7, 1, 1⟩,
  ⟨11, 2, 4, 2, 2⟩,
  ⟨14, 3, 12, 2, 2⟩,
  ⟨15, 2, 9, 2, 3⟩,
  ⟨15, 4, 9, 2, 3⟩,
  ⟨15, 4, 27, 2, 3⟩,
  ⟨17, 1, 9, 1, 3⟩,
  ⟨17, 2, 23, 1, 2⟩,
  ⟨17, 5, 48, 2, 4⟩,
  ⟨19, 1, 7, 1, 1⟩,
  ⟨20, 2, 24, 1, 2⟩,
  ⟨23, 2, 9, 2, 3⟩,
  ⟨23, 2, 23, 1, 2⟩,
  ⟨24, 6, 16, 3, 4⟩,
  ⟨27, 2, 24, 1, 2⟩,
  ⟨29, 2, 27, 1, 2⟩,
  ⟨29, 4, 16, 3, 4⟩,
  ⟨34, 1, 21, 4, 1⟩,
  ⟨34, 2, 28, 1, 2⟩,
  ⟨35, 1, 7, 1, 1⟩,
  ⟨35, 2, 16, 2, 4⟩,
  ⟨35, 3, 25, 3, 5⟩,
  ⟨36, 3, 49, 1, 3⟩,
  ⟨39, 3, 51, 1, 3⟩,
  ⟨41, 1, 19, 4, 1⟩,
  ⟨44, 4, 16, 4, 4⟩,
  ⟨48, 6, 36, 4, 6⟩,
  ⟨53, 2, 27, 1, 2⟩,
  ⟨54, 3, 49, 1, 3⟩,
  ⟨55, 4, 49, 4, 7⟩,
  ⟨55, 4, 88, 1, 4⟩,
  ⟨55, 4, 90, 1, 4⟩,
  ⟨59, 3, 51, 1, 3⟩,
  ⟨62, 1, 21, 4, 1⟩,
  ⟨62, 2, 28, 1, 2⟩,
  ⟨63, 3, 58, 1, 3⟩,
  ⟨67, 1, 7, 1, 1⟩,
  ⟨69, 3, 60, 1, 3⟩,
  ⟨72, 3, 49, 1, 3⟩,
  ⟨79, 3, 51, 1, 3⟩,
  ⟨80, 8, 64, 5, 8⟩,
  ⟨83, 1, 19, 4, 1⟩,
  ⟨88, 2, 91, 0, 4⟩,
  ⟨96, 5, 136, 1, 5⟩,
  ⟨98, 8, 81, 8, 2⟩,
  ⟨99, 4, 88, 1, 4⟩,
  ⟨99, 4, 90, 1, 4⟩,
  ⟨99, 4, 104, 1, 4⟩,
  ⟨99, 4, 106, 1, 4⟩,
  ⟨99, 8, 82, 8, 2⟩,
  ⟨101, 2, 27, 1, 2⟩,
  ⟨104, 1, 23, 4, 1⟩,
  ⟨111, 1, 18, 4, 1⟩,
  ⟨117, 3, 58, 1, 3⟩,
  ⟨118, 1, 21, 4, 1⟩,
  ⟨118, 2, 28, 1, 2⟩,
  ⟨129, 3, 60, 1, 3⟩,
  ⟨132, 6, 200, 1, 6⟩,
  ⟨135, 3, 58, 1, 3⟩,
  ⟨139, 1, 19, 4, 1⟩,
  ⟨149, 2, 27, 1, 2⟩,
  ⟨149, 3, 60, 1, 3⟩,
  ⟨152, 1, 80, 16, 1⟩,
  ⟨174, 2, 28, 1, 2⟩,
  ⟨175, 8, 75, 11, 2⟩,
  ⟨176, 4, 88, 1, 4⟩,
  ⟨176, 4, 90, 1, 4⟩,
  ⟨176, 5, 161, 1, 5⟩,
  ⟨176, 7, 271, 1, 7⟩,
  ⟨186, 8, 83, 11, 2⟩,
  ⟨187, 4, 104, 1, 4⟩,
  ⟨187, 4, 106, 1, 4⟩,
  ⟨188, 1, 20, 4, 1⟩,
  ⟨192, 5, 136, 1, 5⟩,
  ⟨197, 2, 27, 1, 2⟩,
  ⟨207, 25, 178, 12, 3⟩,
  ⟨208, 25, 180, 12, 3⟩,
  ⟨225, 3, 58, 1, 3⟩,
  ⟨230, 2, 28, 1, 2⟩,
  ⟨234, 8, 352, 1, 8⟩,
  ⟨243, 3, 58, 1, 3⟩,
  ⟨246, 6, 236, 1, 6⟩,
  ⟨249, 3, 60, 1, 3⟩,
  ⟨251, 1, 19, 4, 1⟩,
  ⟨269, 3, 60, 1, 3⟩,
  ⟨275, 4, 104, 1, 4⟩,
  ⟨275, 4, 106, 1, 4⟩,
  ⟨303, 6, 200, 1, 6⟩,
  ⟨330, 7, 320, 1, 7⟩,
  ⟨336, 5, 161, 1, 5⟩,
  ⟨340, 49, 316, 16, 4⟩,
  ⟨340, 49, 318, 16, 4⟩,
  ⟨362, 8, 83, 12, 2⟩,
  ⟨363, 4, 104, 1, 4⟩,
  ⟨363, 4, 106, 1, 4⟩,
  ⟨384, 5, 136, 1, 5⟩,
  ⟨400, 36, 183, 21, 3⟩,
  ⟨405, 3, 58, 1, 3⟩,
  ⟨440, 7, 271, 1, 7⟩,
  ⟨441, 3, 58, 1, 3⟩,
  ⟨442, 8, 416, 1, 8⟩,
  ⟨449, 3, 60, 1, 3⟩,
  ⟨474, 6, 236, 1, 6⟩,
  ⟨475, 1, 19, 4, 1⟩,
  ⟨485, 2, 27, 1, 2⟩,
  ⟨489, 3, 60, 1, 3⟩,
  ⟨494, 32, 319, 33, 2⟩,
  ⟨495, 4, 104, 1, 4⟩,
  ⟨495, 4, 106, 1, 4⟩,
  ⟨527, 8, 75, 13, 2⟩,
  ⟨538, 8, 85, 15, 2⟩,
  ⟨560, 5, 161, 1, 5⟩,
  ⟨566, 2, 28, 1, 2⟩,
  ⟨567, 77, 496, 19, 5⟩,
  ⟨576, 2, 352, 0, 8⟩,
  ⟨576, 33, 171, 22, 3⟩,
  ⟨576, 33, 177, 22, 3⟩,
  ⟨638, 7, 320, 1, 7⟩,
  ⟨650, 8, 352, 1, 8⟩,
  ⟨656, 5, 161, 1, 5⟩,
  ⟨660, 87, 322, 30, 4⟩,
  ⟨683, 6, 200, 1, 6⟩,
  ⟨715, 4, 104, 1, 4⟩,
  ⟨715, 4, 106, 1, 4⟩,
  ⟨784, 41, 186, 34, 3⟩,
  ⟨791, 8, 75, 15, 2⟩,
  ⟨799, 116, 716, 23, 6⟩,
  ⟨858, 8, 416, 1, 8⟩,
  ⟨890, 8, 71, 10, 2⟩,
  ⟨891, 4, 104, 1, 4⟩,
  ⟨891, 4, 106, 1, 4⟩,
  ⟨930, 6, 236, 1, 6⟩,
  ⟨1078, 99, 717, 49, 3⟩,
  ⟨1101, 163, 971, 27, 7⟩,
  ⟨1125, 3, 58, 1, 3⟩,
  ⟨1187, 8, 75, 13, 2⟩,
  ⟨1188, 7, 271, 1, 7⟩,
  ⟨1200, 5, 161, 1, 5⟩,
  ⟨1249, 3, 60, 1, 3⟩,
  ⟨1254, 7, 320, 1, 7⟩,
  ⟨1280, 86, 306, 36, 4⟩,
  ⟨1280, 86, 322, 36, 4⟩,
  ⟨1296, 5, 161, 1, 5⟩,
  ⟨1300, 135, 330, 54, 4⟩,
  ⟨1377, 3, 58, 1, 3⟩,
  ⟨1386, 7, 320, 1, 7⟩,
  ⟨1408, 42, 192, 41, 3⟩,
  ⟨1419, 218, 1264, 31, 8⟩,
  ⟨1451, 8, 85, 15, 2⟩,
  ⟨1529, 3, 60, 1, 3⟩,
  ⟨1546, 1, 23, 4, 1⟩,
  ⟨1690, 8, 416, 1, 8⟩,
  ⟨1733, 2, 27, 1, 2⟩,
  ⟨1842, 6, 236, 1, 6⟩,
  ⟨1872, 5, 161, 1, 5⟩,
  ⟨1885, 196, 1274, 65, 4⟩,
  ⟨1979, 8, 75, 15, 2⟩,
  ⟨2000, 39, 168, 35, 3⟩,
  ⟨2022, 2, 28, 1, 2⟩,
  ⟨2106, 8, 352, 1, 8⟩,
  ⟨2106, 8, 416, 1, 8⟩,
  ⟨2160, 5, 161, 1, 5⟩,
  ⟨2374, 6, 236, 1, 6⟩,
  ⟨2475, 4, 104, 1, 4⟩,
  ⟨2475, 4, 106, 1, 4⟩,
  ⟨2486, 7, 320, 1, 7⟩,
  ⟨3179, 4, 104, 1, 4⟩,
  ⟨3179, 4, 106, 1, 4⟩,
  ⟨3210, 6, 236, 1, 6⟩,
  ⟨3299, 8, 75, 13, 2⟩,
  ⟨3354, 8, 416, 1, 8⟩,
  ⟨3600, 151, 334, 88, 4⟩,
  ⟨3840, 45, 168, 50, 3⟩,
  ⟨3850, 7, 320, 1, 7⟩,
  ⟨4096, 30, 159, 20, 3⟩,
  ⟨4274, 6, 236, 1, 6⟩,
  ⟨4862, 7, 320, 1, 7⟩,
  ⟨5040, 126, 298, 66, 4⟩,
  ⟨5049, 3, 58, 1, 3⟩,
  ⟨5488, 39, 168, 38, 3⟩,
  ⟨5609, 3, 60, 1, 3⟩,
  ⟨5760, 43, 186, 45, 3⟩,
  ⟨5939, 8, 75, 15, 2⟩,
  ⟨6370, 8, 416, 1, 8⟩,
  ⟨6480, 5, 161, 1, 5⟩,
  ⟨6561, 3, 58, 1, 3⟩,
  ⟨6800, 5, 161, 1, 5⟩,
  ⟨6875, 4, 104, 1, 4⟩,
  ⟨6875, 4, 106, 1, 4⟩,
  ⟨7289, 3, 60, 1, 3⟩,
  ⟨7514, 8, 416, 1, 8⟩,
  ⟨7655, 8, 91, 15, 2⟩,
  ⟨8250, 7, 320, 1, 7⟩,
  ⟨10691, 8, 75, 13, 2⟩,
  ⟨11874, 6, 236, 1, 6⟩,
  ⟨11960, 184, 338, 130, 4⟩,
  ⟨11979, 4, 104, 1, 4⟩,
  ⟨11979, 4, 106, 1, 4⟩,
  ⟨12096, 45, 168, 51, 3⟩,
  ⟨12500, 80, 282, 35, 4⟩,
  ⟨12500, 200, 298, 140, 4⟩,
  ⟨13850, 6, 236, 1, 6⟩,
  ⟨14080, 134, 298, 79, 4⟩,
  ⟨15147, 4, 104, 1, 4⟩,
  ⟨15147, 4, 106, 1, 4⟩,
  ⟨16250, 8, 416, 1, 8⟩,
  ⟨18000, 5, 161, 1, 5⟩,
  ⟨18150, 7, 320, 1, 7⟩,
  ⟨19840, 43, 204, 47, 3⟩,
  ⟨21296, 39, 168, 38, 3⟩,
  ⟨23166, 7, 320, 1, 7⟩,
  ⟨25872, 5, 161, 1, 5⟩,
  ⟨28314, 8, 416, 1, 8⟩,
  ⟨38474, 6, 236, 1, 6⟩,
  ⟨39546, 8, 416, 1, 8⟩,
  ⟨41616, 5, 161, 1, 5⟩,
  ⟨45618, 6, 236, 1, 6⟩,
  ⟨47940, 188, 362, 143, 4⟩,
  ⟨48020, 204, 298, 160, 4⟩,
  ⟨49129, 3, 60, 1, 3⟩,
  ⟨52800, 45, 168, 51, 3⟩,
  ⟨54720, 134, 298, 79, 4⟩,
  ⟨70070, 7, 320, 1, 7⟩,
  ⟨72171, 4, 106, 1, 4⟩,
  ⟨80190, 7, 320, 1, 7⟩,
  ⟨93346, 6, 236, 1, 6⟩,
  ⟨104907, 4, 106, 1, 4⟩,
  ⟨109744, 39, 168, 38, 3⟩,
  ⟨109850, 8, 416, 1, 8⟩,
  ⟨158950, 7, 320, 1, 7⟩,
  ⟨170586, 8, 416, 1, 8⟩,
  ⟨276250, 8, 416, 1, 8⟩,
  ⟨280000, 134, 298, 79, 4⟩,
  ⟨292820, 204, 298, 160, 4⟩
]

/-- Syntax size of a retained entry, independent of polynomial expansion. -/
def treeNodes : Hex.Kronecker.Expr → Nat
  | .int _ | .atom _ => 1
  | .neg a | .pow a _ => 1 + treeNodes a
  | .add a b | .sub a b | .mul a b => 1 + treeNodes a + treeNodes b

def Product.treeKey (a : Product (PolyList Int)) (s : SizeBound)
    (b : TreeMatrix) : Key :=
  ⟨s.packedBits, support a.left,
    b.foldl (fun n row => row.foldl (fun n e => n + treeNodes e) n) 0,
    support a.result, a.inner⟩

/-- Explicit comparison overrides do not waive either hard packing limit. -/
inductive Arm where
  | automatic
  | lists
  | packed
  | signedPacked
  deriving Repr, BEq, Inhabited

structure Report where
  row : Nat
  size : SizeBound
  key : Key
  deriving Repr

structure Selection where
  mode : MulMode := .plain
  packed : Bool := false
  reports : List Report := []
  reason : Option String := none
  quotientSupport : Nat := 0
  deriving Repr

/-- Kernel width hints for signed packing, already admitted by preflight. -/
def Selection.widths (s : Selection) : List (Nat × Nat) :=
  s.reports.map fun r => (r.size.innerBits, r.size.outerSlotBits?.getD 0)

def Selection.route (s : Selection) : String :=
  if !s.packed then "term-list" else
    match s.mode with | .plain => "packed/plain" | .signedPacked => "packed/signedPacked"

def limitText (n limit : Nat) : String :=
  if n > limit then s!"at least {limit + 1}" else toString n

def declineMessage (budget : Budget) (r : Report) : String :=
  s!"det: packed certificate declined: dense box requires {limitText r.size.digits budget.maxDenseDigits} digits and {limitText r.size.packedBits budget.maxPackedBits} packed bits (limits {budget.maxDenseDigits} digits, {budget.maxPackedBits} bits); using term lists; product row {r.row}, per-atom degrees {r.size.degrees}, limitingStage {reprStr r.size.limitingStage}"

/-- One arm and one multiplication mode for the entire witness. -/
def select (budget : Budget) (arm : Arm) (k : Nat)
    (ps : List (Product (PolyList Int))) (modulus : Option Nat := none)
    (quotients : Option (List (List (PolyList Int))) := none)
    (table : List Key := crossover) : Except String Selection := do
  let mode := if arm == .signedPacked then MulMode.signedPacked else .plain
  let mut reports := []
  for a in ps do
    -- Without a quotient payload these are preliminary integer-product bounds.
    -- They can reject packing, but never establish modular packing eligibility.
    let sized := match modulus, quotients with
      | some p, some qs => sizeMulTermsMod budget mode k 1 a.inner a.width p
          [a.left] a.right [a.result] [qs.getD a.row []]
      | _, _ => sizeMulTerms budget mode k 1 a.inner a.width [a.left] a.right [a.result]
    let s ← sized.mapError (fun e => s!"malformed packed product at row {a.row}: {reprStr e}")
    reports := reports ++ [⟨a.row, s, a.key s⟩]
  let base : Selection := { mode, reports, quotientSupport := quotients.map (support ∘ List.flatten) |>.getD 0 }
  if let some r := reports.find? (fun r => !r.size.accepts budget) then
    return { base with reason := some (declineMessage budget r) }
  if arm == .lists then return { base with reason := some "forced term lists" }
  if modulus.isSome && quotients.isNone then
    return { base with reason := some "residue quotient payload unavailable" }
  if arm == .automatic && !reports.all (fun r => table.contains r.key) then
    return { base with reason := some "no measured packed regime" }
  return { base with packed := true }

/-- Optional quotient work is bounded by the existing certificate and producer limits. -/
structure QuotientBudget where
  terms : Nat := 100000
  coefficientBits : Nat := 4096
  certificateTerms : Nat := 65536
  deriving Repr

inductive QuotientError where
  | invalidModulus
  | unavailable
  | indivisible (row column : Nat)
  deriving Repr, BEq

def coefficientBits (a : PolyList Int) : Nat :=
  a.foldl (fun b (_, c) => max b (c.natAbs.log2 + 1)) 0

def within (budget : QuotientBudget) (a : PolyList Int) : Bool :=
  a.length ≤ budget.terms && coefficientBits a ≤ budget.coefficientBits

/-- Compute each integer quotient coefficient exactly in compiled code. -/
def prepareQuotients (budget : QuotientBudget) (p : Nat)
    (ps : List (Product (PolyList Int))) : Except QuotientError (List (List (PolyList Int))) := do
  if p == 0 then throw .invalidModulus
  let mut qs := []
  let mut count := 0
  for a in ps do
    let mut row := []
    for j in [:a.width] do
      let mut acc : PolyList Int := []
      for t in [:a.inner] do
        let l := a.left.getD t []
        let r := (a.right.getD t []).getD j []
        -- Reject unaffordable products before allocating their term cross product.
        if l.length * r.length + acc.length > budget.terms ||
            coefficientBits l + coefficientBits r + (l.length * r.length).log2 + 1 > budget.coefficientBits then
          throw .unavailable
        acc := add acc (mul l r)
        unless within budget acc do throw .unavailable
      let c := a.result.getD j []
      if acc.length + c.length > budget.terms then throw .unavailable
      acc := sub acc c
      unless within budget acc do throw .unavailable
      unless acc.all (fun (_, z) => z % (p : Int) == 0) do throw (.indivisible a.row j)
      let q := acc.map fun (e,z) => (e, z / (p : Int))
      count := count + q.length
      if count > budget.certificateTerms then throw .unavailable
      row := row ++ [q]
    qs := qs ++ [row]
  return qs

end Hex.PolyDet.Packed

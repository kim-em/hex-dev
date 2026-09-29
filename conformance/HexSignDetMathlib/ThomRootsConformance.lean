/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ThomRoots
public import HexSignDetMathlib.RootListConformance
public import HexSignDetMathlib.ReencodingConformance
public import HexSignDet.Infinitesimal
public meta import HexSignDetMathlib.RootListConformance
public meta import HexSignDet.Infinitesimal
public meta import HexSignDet

public section

/-! Universal root-list success/order and infinitesimal root separation.
Computational conformance owner: `HexSignDet`. -/
namespace Hex.SignDetMathlib.ThomRootsConformance

open Hex Hex.SignDet HexPolyMathlib.Interpret HexRealRootsMathlib

/-- Enumerate 0 and ε without searching for a rational separator. Both roots
are in (−1,1); their derivative words determine their strict order. -/
def infinitesimalPasses : Bool :=
  let x : DensePoly Hex.SignDet.Infinitesimal.First := Hex.SignDet.Infinitesimal.x
  let epsilon := Hex.SignDet.Infinitesimal.epsilon
  let p := x * (x - DensePoly.C epsilon)
  match Descriptor.buildRoots Hex.SignDet.Infinitesimal.firstSign 7 p
      (.finite (-1)) (.finite 1) with
  | .ok (some roots) =>
    roots.map (fun d => d.raw.signs) == [[-1, 1], [1, 1]] &&
      roots.map (fun d => d.signAt x) == [0, 1] &&
      roots.map (fun d => d.signAt (x - DensePoly.C epsilon)) == [-1, 0] &&
      roots.all (fun d => d.raw.head == p && d.raw.indices == [1, 2] &&
        d.raw.check Hex.SignDet.Infinitesimal.firstSign 7 d.evidence &&
        !d.raw.check Hex.SignDet.Infinitesimal.firstSign 8 d.evidence) &&
      decide (roots.Pairwise (fun d e => d.fullOrder e = some .lt))
  | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard infinitesimalPasses

namespace Noncanonical

open Hex.SignDetMathlib.ReencodingConformance.Noncanonical
open HexPoly.InterpretTests

/-- Instantiate the actual universal producer theorem with noninjective
coefficient storage, including complete coverage and strict mathematical order. -/
theorem roots (p : DensePoly Rep) (a b : Endpoint Rep)
    (hdom : HexSturmMathlib.Domain realValue zero p a b) :
    ∃ out, Descriptor.buildRoots Hex.TarskiTests.Noncanonical.sign 7 p a b = .ok (some out) ∧
      (∀ x, x ∈ Tarski.rootsIn (interpret realValue zero p) (a.map realValue) (b.map realValue) ↔
        x ∈ out.map (fun d => d.root realValue zero one add sub mul natCast sign)) ∧
      (out.map (fun d => d.root realValue zero one add sub mul natCast sign)).Nodup ∧
      (out.map (fun d => d.root realValue zero one add sub mul natCast sign)).Pairwise (· < ·) := by
  exact Descriptor.buildRoots_roots realValue zero one add sub mul natCast sign neg inv
    7 p a b hdom

end Noncanonical

/-- info: 'Hex.SignDet.Thom.insert_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Thom.insert_success
/-- info: 'Hex.SignDet.Descriptor.rootsFromTable_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.rootsFromTable_nil
/-- info: 'Hex.SignDet.Descriptor.rootsFromTable_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.rootsFromTable_cons
/-- info: 'Hex.SignDet.Descriptor.buildRoots_ofTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildRoots_ofTable
/-- info: 'Hex.SignDet.Descriptor.fullOrder_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.fullOrder_strict
/-- info: 'Hex.SignDet.Descriptor.rootsFromTable_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.rootsFromTable_success
/-- info: 'Hex.SignDet.Descriptor.buildRoots_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildRoots_success
/-- info: 'Hex.SignDet.Descriptor.buildRoots_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildRoots_ordered
/-- info: 'Hex.SignDet.Descriptor.buildRoots_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildRoots_roots
/-- info: 'Hex.SignDetMathlib.ThomRootsConformance.Noncanonical.roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDetMathlib.ThomRootsConformance.Noncanonical.roots

end Hex.SignDetMathlib.ThomRootsConformance

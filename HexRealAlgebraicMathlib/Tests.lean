/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealAlgebraicMathlib.RealClosed
public import HexRealAlgebraicMathlib.Laws
public import HexRealAlgebraicMathlib.IntegerRoots
public import HexRealAlgebraicMathlib.Repr
public import HexRealAlgebraicMathlib.Rounding
public import HexRealAlgebraicMathlib.Norm
public section

/-! Ordinary-kernel axiom guards for the implemented comparison, root,
recognition, rounding, approximation and square-root correspondence theorems.
These are correctness checks; they do not measure executable performance. -/

/-- info: 'Hex.RealAlgebraicNumber.compare_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicNumber.compare_eq

/-- info: 'Hex.RealAlgebraicPoly.contains_roots_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicPoly.contains_roots_iff

/-- info: 'Hex.RealAlgebraicPoly.roots_all_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicPoly.roots_all_iff

/-- info: 'Hex.RealAlgebraicPoly.roots_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicPoly.roots_multiplicity

/-- info: 'Hex.RealAlgebraicPoly.roots_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicPoly.roots_sorted

/-- info: 'Hex.RealAlgebraicPoly.roots_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicPoly.roots_positive

/-- info: 'Hex.RealAlgebraicPoly.roots_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicPoly.roots_spec

/-- info: 'Hex.ZPoly.mem_realAlgebraicRoots_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.ZPoly.mem_realAlgebraicRoots_iff

/-- info: 'Hex.RealAlgebraicNumber.toRat?_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicNumber.toRat?_eq_some

/-- info: 'Hex.RealAlgebraicNumber.floor_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicNumber.floor_bounds

/-- info: 'Hex.RealAlgebraicNumber.ceil_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicNumber.ceil_bounds

/-- info: 'Hex.RealAlgebraicNumber.approx_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicNumber.approx_error

/-- info: 'Hex.RealAlgebraicNumber.sqrtRoot?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicNumber.sqrtRoot?_isSome

/-- info: 'Hex.RealAlgebraicNumber.sqrt?_eq_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicNumber.sqrt?_eq_none

/-- info: 'Hex.RealAlgebraicNumber.sqrt_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicNumber.sqrt_sq

/-- info: 'Hex.RealAlgebraicNumber.repr_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicNumber.repr_isSome

/-- info: 'Hex.RealAlgebraicNumber.repr_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicNumber.repr_roundtrip

/-- info: 'Hex.RealAlgebraicNumber.ceil_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicNumber.ceil_eq

/-- info: 'Hex.RealAlgebraicNumber.sqrt?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealAlgebraicNumber.sqrt?_isSome

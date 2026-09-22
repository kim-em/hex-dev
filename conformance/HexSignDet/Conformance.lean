/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet
public import HexRank.Int
public import HexRowReduce.Inverse
public import HexSturm.Fixtures

public meta import HexSignDet.Replay
public meta import HexSignDet.Matrix
public meta import HexSignDet.Support
public meta import HexRank.Cert
public meta import HexSturm.Basic

public section

open Hex Hex.SignDet
open scoped Hex

/-! Recursive replay regressions. Fixture generation uses independently supplied
rational roots to populate counts; it is test code, not a sign-table producer.
The final literal probe runs solely through the ordinary kernel. -/
namespace Hex.SignDet.Conformance

def sign : Rat → Int := Sturm.orderSign

def p : DensePoly Rat := DensePoly.ofCoeffs #[-1, 0, 1]
def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]

/-- Test-only certificate assembly, using the existing rational inverse and
integer rank producers. Counts come from a supplied list of exact roots. -/
def makeNode (d : Sturm.PreparedDomain Rat) (qs : List (DensePoly Rat))
    (rows : List (List Nat)) (columns : List (List Int)) (roots : List Rat) :
    Option (Node Rat Nat) := do
  if rows.length != columns.length then none else do
    let r := columns.length
    let cols : Vector (List Int) r := Vector.ofFn fun i => columns[i.val]!
    let es : Vector (List Nat) r := Vector.ofFn fun i => rows[i.val]!
    let m : Matrix Rat r r := Matrix.ofFn fun i j => (entry es[i] cols[j] : Rat)
    let inv ← Matrix.inverse? m
    let den := ((List.finRange r).flatMap fun i =>
      (List.finRange r).map fun j => inv[(i, j)].den).foldl (· * ·) 1
    let moments := Vector.ofFn fun i => Sturm.certifyPrepared 7 d (moment qs es[i])
    let s : System r := {
      rows := es, columns := cols
      counts := Vector.ofFn fun i => (roots.countP fun a =>
        decide (qs.map (fun q => sign (q.eval a)) = cols[i]) : Nat)
      values := moments.map (·.value)
      inverse := Matrix.ofFn fun i j => inv[(i, j)].num * (den / inv[(i, j)].den : Nat)
      denominator := den }
    return {
      context := 7, head := d.head, lower := d.lower, upper := d.upper, queries := qs
      size := r, system := s, moments
      basis := Matrix.rankCert s.retainedMatrix }

/-- Finite fixture assembly. Failure is a test failure, not an API result. -/
def build (d : Sturm.PreparedDomain Rat) (roots : List Rat) :
    Nat → List (DensePoly Rat) → Option (Replay Rat Nat)
  | 0, _ => none
  | fuel + 1, qs => do
    if qs.length ≤ 1 then
      return .leaf (← makeNode d qs (leafRows qs.length) (leafColumns qs.length) roots)
    else
      let l ← build d roots fuel (qs.take (qs.length / 2))
      let r ← build d roots fuel (qs.drop (qs.length / 2))
      let n ← makeNode d qs (product l.node.rows r.node.rows)
        (product l.node.system.support r.node.system.support) roots
      return .split n l r

def fixture (head : DensePoly Rat) (roots : List Rat) (qs : List (DensePoly Rat))
    (a : Endpoint Rat := .negInf) (b : Endpoint Rat := .posInf) : Option (Replay Rat Nat) := do
  let d ← Sturm.prepare sign head a b
  build d roots (qs.length + 1) qs

def accepts (qs : List (DensePoly Rat)) (t : Replay Rat Nat) : Bool :=
  t.check sign 7 p .negInf .posInf qs

def good (head : DensePoly Rat) (roots : List Rat) (qs : List (DensePoly Rat)) : Bool :=
  match fixture head roots qs with
  | none => false
  | some t => t.check sign 7 head .negInf .posInf qs

#guard good p [-1, 1] [x, x - 1]
#guard good p [-1, 1] [x, x, 0, 1, x - 1]
#guard good p [-1, 1] []
#guard good x [0] [x, 0]
#guard good 1 [] []
#guard good 1 [] [x, 0]
#guard good (x * x + 1) [] [x, x, 0]
#guard (fixture 0 [] []).isNone
#guard (fixture (x * x) [0] []).isNone
#guard (fixture p [-1, 1] [] (.finite (-1)) .posInf).isNone
#guard (fixture p [-1, 1] [] (.finite 2) (.finite 2)).isNone
#guard (fixture p [-1, 1] [] (.finite 2) (.finite (-2))).isNone

def mapNode (f : Node Rat Nat → Node Rat Nat) : Replay Rat Nat → Replay Rat Nat
  | .leaf n => .leaf (f n)
  | .split n l r => .split (f n) l r

def replaceSystem (n : Node Rat Nat) (s : System n.size) : Node Rat Nat :=
  {n with system := s, basis := Matrix.rankCert s.retainedMatrix}

def mutate (f : Replay Rat Nat → Replay Rat Nat) : Bool :=
  match fixture p [-1, 1] [x, x - 1] with
  | none => false
  | some t => !accepts [x, x - 1] (f t)

#guard mutate (mapNode fun n => {n with context := 8})
#guard mutate (mapNode fun n => {n with queries := n.queries.reverse})
#guard mutate (mapNode fun n => {n with lower := .finite 0})
#guard mutate (mapNode fun n => {n with system := {n.system with denominator := 0}})
#guard mutate (mapNode fun n => {n with system := {n.system with inverse := 0}})
#guard mutate (mapNode fun n => replaceSystem n {n.system with counts := n.system.counts.map (· + 1)})
#guard mutate (mapNode fun n => replaceSystem n {n.system with counts := n.system.counts.map (fun _ => -1)})
#guard mutate (mapNode fun n => {n with system := {n.system with rows := n.system.rows.map (fun _ => [3, 0])}})
#guard mutate (mapNode fun n => {n with system := {n.system with columns := n.system.columns.map (fun _ => [-1, -1])}})
#guard mutate (mapNode fun n => {n with basis := {n.basis with denom := 0}})
#guard mutate (mapNode fun n => {n with moments := n.moments.map (fun c => {c with context := 8})})
#guard mutate (mapNode fun n => {n with moments := n.moments.map (fun c => {c with value := c.value + 1})})
#guard mutate (fun t => match t with | .leaf n => .leaf n | .split n l _ => .split n l l)
#guard mutate (fun t => match t with | .leaf n => .leaf n | .split n l r => .split n r l)
#guard mutate (fun t => match t with
  | .leaf n => .leaf n
  | .split n l r => .split n (mapNode (fun c => {c with context := 8}) l) r)
#guard mutate (fun t => .leaf t.node)
#guard mutate (mapNode fun n => {n with basis := {n.basis with
  rows := n.basis.rows.map (fun i => ⟨0, Nat.zero_lt_of_lt i.isLt⟩)}})
#guard mutate (mapNode fun n => {n with basis := {n.basis with
  cols := n.basis.cols.map (fun i => ⟨0, Nat.zero_lt_of_lt i.isLt⟩)}})

example : entry [0, 0] [0, 0] = 1 := by decide +kernel
example : momentMatrix #v[[0], [1], [2]] #v[[-1], [0], [1]] =
    Matrix.ofRows #v[#v[1, 1, 1], #v[-1, 0, 1], #v[1, 0, 1]] := by decide +kernel

/-- The SPEC's forged support satisfies both matrix identities and has the
correct total count. It still lacks the required full singleton leaf support. -/
@[expose] def forged : System 1 where
  rows := #v[[0]]
  columns := #v[[1]]
  counts := #v[2]
  values := #v[2]
  inverse := Matrix.identity 1
  denominator := 1

example : forged.check 1 = true := by decide +kernel
example : forged.columns.toList ≠ leafColumns 1 := by decide +kernel

/-- Fully literal query-one replay on (-2,2), including its rank witness. -/
@[expose] def literalSystem : System 1 where
  rows := #v[[]]
  columns := #v[[]]
  counts := #v[2]
  values := #v[2]
  inverse := Matrix.identity 1
  denominator := 1

@[expose] def literalNode : Node Rat Nat where
  context := 7
  head := Sturm.Fixtures.p
  lower := .finite (-2)
  upper := .finite 2
  queries := []
  size := 1
  system := literalSystem
  moments := #v[Sturm.Fixtures.literal]
  basis := {
    rank := 1
    rows := #v[0]
    cols := #v[⟨0, by decide +kernel⟩]
    denom := 1
    adj := Matrix.identity 1 }

set_option maxRecDepth 8192 in
/-- Ordinary-kernel acceptance of literal evidence, without any producer. -/
theorem literal_accepts : (Replay.leaf literalNode).check Sturm.orderSign 7
    Sturm.Fixtures.p (.finite (-2)) (.finite 2) [] = true := by
  simp only [Replay.check, Node.check, Sturm.check, TarskiCertificate.check,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

@[expose] def forgedNode : Node Rat Nat :=
  {literalNode with queries := [Sturm.Fixtures.x], system := forged}

set_option maxRecDepth 8192 in
/-- Local query/matrix evidence really passes for the omitted-support forgery. -/
theorem forged_local : forgedNode.check Sturm.orderSign 7 Sturm.Fixtures.p
    (.finite (-2)) (.finite 2) [Sturm.Fixtures.x] = true := by
  simp only [Node.check, Sturm.check, TarskiCertificate.check,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- The recursive boundary rejects the same forgery before trusting its solve. -/
theorem forged_rejected : (Replay.leaf forgedNode).check Sturm.orderSign 7
    Sturm.Fixtures.p (.finite (-2)) (.finite 2) [Sturm.Fixtures.x] = false := by
  decide +kernel

@[expose] def emptySystem : System 0 where
  rows := #v[]
  columns := #v[]
  counts := #v[]
  values := #v[]
  inverse := Matrix.identity 0
  denominator := 1

example : emptySystem.check 0 = true := by decide +kernel

@[expose] def emptyNode : Node Rat Nat where
  context := 7
  head := Sturm.Fixtures.p
  lower := .finite (-2)
  upper := .finite 2
  queries := []
  size := 0
  system := emptySystem
  moments := #v[]
  basis := ⟨0, #v[], #v[], 1, Matrix.identity 0⟩

/-- Vacuous zero-dimensional equations cannot certify a root-free domain. -/
theorem empty_rejected : (Replay.leaf emptyNode).check Sturm.orderSign 7
    Sturm.Fixtures.p (.finite (-2)) (.finite 2) [] = false := by decide +kernel

/-- info: 'Hex.SignDet.Conformance.literal_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_accepts
/-- info: 'Hex.SignDet.System.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms System.unique
/-- info: 'Hex.SignDet.System.mem_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms System.mem_support

end Hex.SignDet.Conformance

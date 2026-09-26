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
public import HexRealRoots.TarskiTests

public meta import HexSignDet.Replay
public meta import HexSignDet.Matrix
public meta import HexSignDet.Support
public meta import HexSignDet.Produce
public meta import HexSignDet.Reference
public meta import HexRank.Cert
public meta import HexSturm.Basic
public meta import HexSignDet.Reduction
public meta import HexSignDet.Table
public meta import HexSignDet.TableProducer
public meta import HexSignDet.Thom
public meta import HexSignDet.Descriptor
public meta import HexSignDet.Complete
public meta import HexSignDet.SelectedSigns
public meta import HexSignDet.RootList
public meta import HexSignDet.Compare
public meta import HexSignDet.Reencode
public meta import HexSignDet.CommonProduct
public meta import HexRealRoots.TarskiTests

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

/-- Compare observable sparse integer counts without hiding zero pruning. -/
def entries {r : Nat} (s : System r) : List (List Int × Int) :=
  s.positive.map fun i => (s.columns[i], s.counts[i])

/-- Counts are computed solely from Tarski queries; the expected table is
supplied independently by each regression. -/
def produced (head : DensePoly Rat) (qs : List (DensePoly Rat))
    (expected : List (List Int × Int))
    (a : Endpoint Rat := .negInf) (b : Endpoint Rat := .posInf) : Bool :=
  match Sturm.prepare sign head a b with
  | none => false
  | some d => match buildPrepared 7 d qs with
    | .error _ => false
    | .ok t => entries t.val.node.system == expected

#guard produced p [x, x - 1] [([-1, -1], 1), ([1, 0], 1)]
#guard produced (-p) [x] [([-1], 1), ([1], 1)]
#guard produced p [] [([], 2)]
#guard produced p [0, 1, x, x] [([0, 1, -1, -1], 1), ([0, 1, 1, 1], 1)]
#guard produced x [x, 0] [([0, 0], 1)]
#guard produced 1 [] []
#guard produced 1 [x, x, 0] []
#guard produced (x * x + 1) [] []
#guard produced (x * x + 1) [x, x, 0] []
#guard produced (x * x - 2) [x, x * x - 2, x * x - 3, x - 1]
  [([-1, 0, -1, -1], 1), ([1, 0, -1, 1], 1)]
#guard produced (x * x * x - x) [x] [([-1], 1), ([0], 1), ([1], 1)]
#guard produced (x * x * x - x) [x] [([0], 1)] (.finite (-1 / 2)) (.finite (1 / 2))
#guard produced p (List.replicate 12 x)
  [(List.replicate 12 (-1), 1), (List.replicate 12 1, 1)]

/-- Sparse natural lookup is checked at present, omitted and malformed
conditions; zero-root domains retain no explicit zero rows. -/
def sparseCounts (head : DensePoly Rat) (qs : List (DensePoly Rat))
    (expected : List (List Int × Nat)) (absent : List (List Int)) : Bool :=
  match Sturm.prepare sign head .negInf .posInf with
  | none => false
  | some d => match buildTablePrepared 7 d qs with
    | .error _ => false
    | .ok t => t.rows.toList == expected &&
      expected.all (fun (s, n) => t.count s == n) && absent.all (fun s => t.count s == 0)

#guard sparseCounts p [x, x - 1] [([-1, -1], 1), ([1, 0], 1)]
  [[-1, 0], [0, 0], [1, 1], [], [2, 0]]
#guard sparseCounts p [] [([], 2)] [[0], [-1]]
#guard sparseCounts (x * x + 1) [x] [] [[-1], [0], [1], []]
#guard sparseCounts 1 [] [] [[], [0]]

def descriptor (indices : List Nat) (signs : List Int) : RawDescriptor Rat Nat :=
  ⟨7, p, .negInf, .posInf, indices, signs⟩

def descriptorAccepts (raw : RawDescriptor Rat Nat) : Bool :=
  match Sturm.prepare sign raw.head raw.lower raw.upper with
  | none => false
  | some d => match buildPrepared raw.context d raw.queries with
    | .error _ => false
    | .ok t => raw.check sign raw.context t.val

#guard descriptorAccepts (descriptor [1] [-1])
#guard descriptorAccepts (descriptor [1] [1])
#guard descriptorAccepts (descriptor [1, 2] [-1, 1])
#guard descriptorAccepts (descriptor [2, 1] [1, -1])
#guard descriptorAccepts {descriptor [1, 2] [1, -1] with head := -p}
#guard !descriptorAccepts (descriptor [] [])
#guard descriptorAccepts {descriptor [] [] with lower := .finite 0}
#guard !descriptorAccepts (descriptor [1] [0])
#guard !descriptorAccepts (descriptor [2] [1])
#guard !descriptorAccepts (descriptor [1, 2] [-1, -1])
#guard !descriptorAccepts (descriptor [1, 1] [-1, -1])
#guard !descriptorAccepts (descriptor [0] [0])
#guard !descriptorAccepts (descriptor [3] [0])
#guard !descriptorAccepts (descriptor [1, 2] [-1])
#guard !descriptorAccepts (descriptor [1] [2])
#guard !descriptorAccepts {descriptor [] [] with head := 1}

def descriptorBuilt (raw : RawDescriptor Rat Nat) : Bool :=
  match Descriptor.build sign 7 raw with
  | .ok (.ok d) => d.raw.check sign 7 d.evidence && d.raw.indices == raw.indices &&
    d.raw.signs == raw.signs && d.raw.head == raw.head &&
    d.raw.lower == raw.lower && d.raw.upper == raw.upper
  | _ => false

def descriptorFailure (raw : RawDescriptor Rat Nat) (expected : DescriptorError) : Bool :=
  match Descriptor.build sign 7 raw with
  | .ok (.error reason) => reason == expected
  | _ => false

#guard descriptorBuilt (descriptor [1] [-1])
#guard descriptorBuilt (descriptor [1, 2] [1, 1])
#guard descriptorBuilt {descriptor [] [] with lower := .finite 0}
#guard descriptorFailure (descriptor [1] [0]) .absent
#guard descriptorFailure (descriptor [] []) .ambiguous
#guard descriptorFailure (descriptor [2] [1]) .ambiguous
#guard descriptorFailure (descriptor [0] [0]) .malformed
#guard descriptorFailure (descriptor [1, 1] [-1, -1]) .malformed
#guard descriptorFailure {descriptor [1] [1] with lower := .finite 1} .domain
#guard descriptorFailure {descriptor [1] [1] with context := 8} .context
#guard descriptorFailure {descriptor [] [] with head := 0} .domain

#guard (Descriptor.validate sign 7 (descriptor [1] [-1])).isSome
#guard (Descriptor.validate sign 7 (descriptor [1] [0])).isNone
#guard (Descriptor.validate sign 7 (descriptor [] [])).isNone
#guard (Descriptor.validate sign 7 (descriptor [0] [0])).isNone
#guard (Descriptor.validate sign 7
  {descriptor [1] [1] with lower := .finite 1}).isNone
#guard (Descriptor.validate sign 7
  {descriptor [1] [1] with context := 8}).isNone

/-- Public insertion rejects unrelated heads and partial derivative slots,
even when their raw sign words would produce a strict comparison. -/
def insertionRejected (left right : RawDescriptor Rat Nat) : Bool :=
  match Descriptor.build sign 7 left, Descriptor.build sign 7 right with
  | .ok (.ok l), .ok (.ok r) => match Thom.insert l [r] with
    | .error .system => true
    | _ => false
  | _, _ => false

#guard insertionRejected (descriptor [1, 2] [1, 1])
  {descriptor [1, 2] [-1, 1] with head := (x - 2) * (x - 4)}
#guard insertionRejected {descriptor [1, 3] [-1, 1] with head := x * x * x - x}
  {descriptor [2, 3] [1, 1] with head := x * x * x - x}

/- A sign-equivalent query is still not the declared formal derivative;
changing context also cannot recycle the original query tree. -/
#guard match Sturm.prepare sign p .negInf .posInf with
  | none => false
  | some d => match buildPrepared 7 d [x], buildPrepared 7 d (descriptor [1] [-1]).queries with
    | .ok wrong, .ok right =>
      !(descriptor [1] [-1]).check sign 7 wrong.val &&
      !({descriptor [1] [-1] with context := 8}).check sign 8 right.val
    | _, _ => false

/-- Completion and selected signs run the actual BKR producers. Expected
values here are independent direct evaluations at the selected roots. -/
def completed (raw : RawDescriptor Rat Nat) (expected : List Int) : Bool :=
  match Descriptor.build sign 7 raw with
  | .ok (.ok d) => match d.buildCompletion with
    | .ok c => c.descriptor.raw.signs == expected &&
      d.raw.completes c.descriptor.raw &&
      c.descriptor.raw.check sign 7 c.descriptor.evidence
    | _ => false
  | _ => false

def selected (raw : RawDescriptor Rat Nat) (qs : List (DensePoly Rat))
    (expected : List Int) : Bool :=
  match Descriptor.build sign 7 raw with
  | .ok (.ok d) => match d.buildSigns qs with
    | .ok s => s.values.toList == expected && d.checkSigns qs s.values s.evidence
    | _ => false
  | _ => false

#guard completed (descriptor [1] [-1]) [-1, 1]
#guard completed (descriptor [2, 1] [1, -1]) [-1, 1]
#guard completed {descriptor [] [] with lower := .finite 0} [1, 1]
#guard completed {descriptor [1] [1] with head := -p} [1, -1]
#guard completed {descriptor [2] [-1] with head := x * x * x - x} [1, -1, 1]
#guard completed {descriptor [1] [-1] with head := x * x * x - x} [-1, 0, 1]
#guard completed {descriptor [2] [1] with head := x * x * x - x} [1, 1, 1]
#guard completed {descriptor [2] [1] with head := -(x * x * x - x)} [-1, 1, -1]
#guard completed {descriptor [1] [1] with head := x * x - 2} [1, 1]

#guard selected (descriptor [1] [-1]) [x, p, x + 1, x - 1, 0, 7] [-1, 0, 0, -1, 0, 1]
#guard selected (descriptor [1] [1]) [x, p, x + 1, x - 1, 0, 7] [1, 0, 1, 0, 0, 1]
#guard selected (descriptor [1] [-1]) [] []
#guard selected {descriptor [] [] with lower := .finite 0} [x, -x] [1, -1]
#guard selected {descriptor [1] [1] with head := x * x - 2}
  [x * x - 2, x * x - 3, x, x - 1] [0, -1, 1, 1]

/- A complete table can be reused for the same bound domain and query list,
but cannot justify a wrong selected sign or a different query/context. -/
#guard match Descriptor.build sign 7 (descriptor [1] [-1]) with
  | .ok (.ok d) => match d.buildSigns [x] with
    | .ok s => s.value == -1 &&
      !d.checkSigns [x] #v[1] s.evidence &&
      !d.checkSigns [2 * x] s.values s.evidence &&
      (match Descriptor.build sign 8 {descriptor [1] [-1] with context := 8} with
       | .ok (.ok other) => !other.checkSigns [x] s.values s.evidence
       | _ => false)
    | _ => false
  | _ => false

def compared (left right : RawDescriptor Rat Nat) (expected : Ordering) : Bool :=
  match Descriptor.build sign 7 left, Descriptor.build sign 7 right with
  | .ok (.ok l), .ok (.ok r) => match l.buildComparison r with
    | .ok c => c.order == expected && c.common.check 7 left.head right.head &&
      l.checkReencoding c.leftEncoding.target c.common.head .negInf .posInf c.leftEncoding.evidence &&
      r.checkReencoding c.rightEncoding.target c.common.head .negInf .posInf c.rightEncoding.evidence
    | _ => false
  | _, _ => false

def reencoded (source : RawDescriptor Rat Nat) (head : DensePoly Rat) (a b : Endpoint Rat)
    (expected : Option (List Int)) : Bool :=
  match Descriptor.build sign 7 source with
  | .ok (.ok d) => match d.buildReencoding head a b, expected with
    | .ok none, none => true
    | .ok (some r), some signs => r.target.raw.signs == signs &&
      d.checkReencoding r.target head a b r.evidence
    | _, _ => false
  | _ => false

#guard compared {descriptor [1] [1] with head := x - 1}
  {descriptor [1] [1] with head := x - 2} .lt
#guard compared (descriptor [1] [-1]) (descriptor [2, 1] [1, -1]) .eq
#guard compared {descriptor [1] [1] with head := x * x - 2}
  {descriptor [1] [-1] with head := (x * x - 2) * (x - 3)} .eq
#guard compared {descriptor [1] [-1] with head := x * x - 2}
  {descriptor [1] [-1] with head := (x * x - 2) * (x - 3)} .lt
#guard compared (descriptor [1] [1]) {descriptor [1] [-1] with head := -p} .eq
#guard compared (descriptor [1] [1]) {descriptor [1] [1] with head := 2 * p} .eq
#guard compared {descriptor [1] [1] with head := x - 1, lower := .finite 0, upper := .finite 2}
  {descriptor [1] [1] with head := x - 2, lower := .finite 1, upper := .finite 3} .lt
#guard compared {descriptor [] [] with lower := .finite (-2), upper := .finite 0}
  {descriptor [] [] with lower := .finite 0, upper := .finite 2} .lt
#guard reencoded {descriptor [1] [1] with head := x * x - 2}
  ((x * x - 2) * (x - 3)) .negInf .posInf (some [-1, 1, 1])
#guard reencoded (descriptor [1] [-1]) p (.finite 0) .posInf none
#guard reencoded (descriptor [1] [1]) (x - 3) .negInf .posInf none
#guard reencoded (descriptor [1] [1]) p (.finite 1) .posInf none
#guard reencoded {descriptor [] [] with head := x - 1, lower := .finite 0, upper := .finite 2}
  (x * (x - 1) * (x - 2)) .negInf .posInf (some [-1, 0, 1])

/- The product with an unremoved common factor satisfies the root-union
identities but fails the independent squarefree-domain guard. -/
#guard
  let q := p * (x - 3)
  let c : CommonProduct Rat Nat := ⟨7, p, q, p * q, 1, q, p⟩
  c.check 7 p q && (Sturm.prepare sign c.head .negInf .posInf).isNone &&
    !({c with context := 8}).check 7 p q &&
    !({c with leftQuotient := 1}).check 7 p q &&
    !({c with factor := 2}).check 7 p q

/- Distinct stored coefficients with equal values must select equal roots.
No Field instance exists on this representation carrier. -/
#guard
  let sign := Hex.TarskiTests.Noncanonical.sign
  let head := Hex.TarskiTests.Noncanonical.head
  let x := HexPoly.InterpretTests.x
  let left : RawDescriptor HexPoly.InterpretTests.Rep Nat := ⟨7, head, .negInf, .posInf, [1], [1]⟩
  let right := {left with head := x * x - 1}
  decide (left.head ≠ right.head) &&
    match Descriptor.build sign 7 left, Descriptor.build sign 7 right with
    | .ok (.ok l), .ok (.ok r) => match l.buildComparison r with
      | .ok result => result.order == .eq
      | _ => false
    | _, _ => false

example : Thom.select [2, 1] [-1, 1] = some [1, -1] ∧
    Thom.select [0] [0] = none ∧ Thom.select [2] [0] = none := by decide +kernel

example : (descriptor [1] [-1]).completes (descriptor [1, 2] [-1, 1]) = true ∧
    (descriptor [1] [-1]).completes (descriptor [1, 2] [1, 1]) = false ∧
    (descriptor [1] [-1]).completes (descriptor [1] [-1]) = false ∧
    (descriptor [1] [-1]).completes
      {descriptor [1, 2] [-1, 1] with context := 8} = false ∧
    (descriptor [1] [-1]).completes
      {descriptor [1, 2] [-1, 1] with head := x * x - 2} = false := by decide +kernel

/-- For x³-x, ordinary lexicographic sorting puts the middle root first.
The Thom rule uses the largest differing index and also handles -p. -/
example : Thom.compareSigns [1, -1, 1] [-1, 0, 1] = some .lt ∧
    Thom.compareSigns [-1, 0, 1] [1, 1, 1] = some .lt ∧
    Thom.compareSigns [-1, 1, -1] [1, 0, -1] = some .lt ∧
    Thom.compareSigns [1, 0, -1] [-1, -1, -1] = some .lt := by decide +kernel

example : Thom.compareSigns [-1, 1] [-1, 1] = some .eq ∧
    Thom.compareSigns [1, 1] [-1, 1] = some .gt ∧
    Thom.compareSigns [1] [-1] = none ∧
    Thom.compareSigns [1, 0, 1] [-1, 0, 1] = none ∧
    Thom.compareSigns [1] [1, 1] = none ∧
    Thom.compareSigns [2, 1] [1, 1] = none ∧
    Thom.compareSigns [] [] = none := by decide +kernel

/-- The exponential reference and reduced producer must agree on small lists.
Both also have to pass the ordinary checker for their literal moments. -/
def agrees (head : DensePoly Rat) (qs : List (DensePoly Rat)) : Bool :=
  match Sturm.prepare sign head .negInf .posInf with
  | none => false
  | some d => match buildPrepared 7 d qs, referencePrepared 7 d qs with
    | .ok t, .ok n => n.check sign 7 head .negInf .posInf qs &&
      entries t.val.node.system == entries n.system
    | _, _ => false

#guard [p, x, (1 : DensePoly Rat), x * x + 1, x * x - 2, x * x * x - x].all fun h =>
  [[], [x], [x, x - 1], [x, 0, x]].all (agrees h)

/-- Compare the two actual recursive constructors, not only the reference
solver. The high-degree queries exercise reduction before Tarski production. -/
def momentModes (head : DensePoly Rat) (qs : List (DensePoly Rat)) : Bool :=
  match Sturm.prepare sign head .negInf .posInf with
  | none => false
  | some d => match buildPrepared 7 d qs true, buildPrepared 7 d qs false with
    | .ok reduced, .ok direct =>
      entries reduced.val.node.system == entries direct.val.node.system &&
      reduced.val.node.system.rows.toList == direct.val.node.system.rows.toList &&
      reduced.val.node.system.values.toList == direct.val.node.system.values.toList
    | _, _ => false

#guard [p, -p, x, (1 : DensePoly Rat), x * x + 1, x * x - 2,
    DensePoly.ofCoeffs #[-1, 0, 2], DensePoly.ofCoeffs #[1, 0, -2],
    DensePoly.ofCoeffs #[2, -3], DensePoly.ofCoeffs #[1, -2, 0, 3]].all fun h =>
  [[], [x], [x, x - 1], [x, 0, x], [x.natPow 7 + 1, x.natPow 6 - 1]].all (momentModes h)

#guard [p, -p, x].all fun h =>
  [([], []), ([x], [0]), ([x], [1]), ([x], [2]), ([x, x + 1], [2, 2]),
    ([0, x], [1, 2]), ([p, x], [2, 1])].all fun (qs, es) =>
      (Reduction.build sign h qs es).check sign h qs es

#guard !(Reduction.build sign p [x] [3]).check sign p [x] [3]
#guard !(Reduction.build sign p [x] []).check sign p [x] []
#guard !(Reduction.build sign 1 [x] [1]).check sign 1 [x] [1]
#guard !(Reduction.build sign 0 [x] [1]).check sign 0 [x] [1]

/- Reject malformed indices before constructing a repeated-factor list. -/
#guard match Sturm.prepare sign p .negInf .posInf with
  | none => false
  | some d => match buildNode 7 d [x] [[100000000]] [[1]] with
    | .error .system => true
    | _ => false

/-- Mutate every independently checked component of a supplied chain. -/
def corruptReduction : Bool :=
  let qs := [x, x + 1]
  let es := [1, 2]
  let r := Reduction.build sign p qs es
  let badSteps : List (ReductionStep Rat → ReductionStep Rat) := [
    fun s => {s with index := s.index + 1},
    fun s => {s with next := s.next + 1},
    fun s => {s with witness := {s.witness with quotient := s.witness.quotient + 1}},
    fun s => {s with witness := {s.witness with leftScale := 0}},
    fun s => {s with witness := {s.witness with leftScale := -1}},
    fun s => {s with witness := {s.witness with rightScale := 0}},
    fun s => {s with witness := {s.witness with rightScale := -1}}]
  r.check sign p qs es &&
    badSteps.all (fun change => !({r with steps := r.steps.map change}.check sign p qs es)) &&
    !({r with steps := r.steps.reverse}.check sign p qs es) &&
    !({r with steps := r.steps.drop 1}.check sign p qs es) &&
    !({r with steps := r.steps ++ r.steps}.check sign p qs es) &&
    !({r with result := r.result + 1}.check sign p qs es) &&
    !r.check sign p qs [2, 1] && !r.check sign p qs.reverse es

#guard corruptReduction

/- These forged identities hold exactly; only positivity prevents their
false sign claims. The first flips a nonzero sign, the second invents zero,
and the third invents a nonzero sign for a product divisible by the head. -/
#guard
  let step : ReductionStep Rat := ⟨0, -x, ⟨1, 0, -1⟩⟩
  SignedRemainderChain.subIsZero (1 * x) (0 * p + DensePoly.scale (-1) (-x)) &&
    !({steps := [step], result := -x} : Reduction Rat).check sign p [x] [1]
#guard
  let step : ReductionStep Rat := ⟨0, 0, ⟨0, 0, 1⟩⟩
  SignedRemainderChain.subIsZero (DensePoly.scale 0 (1 * x)) (0 * p + 0) &&
    !({steps := [step], result := 0} : Reduction Rat).check sign p [x] [1]
#guard
  let first : ReductionStep Rat := ⟨0, x - 1, ⟨1, 0, 1⟩⟩
  let last : ReductionStep Rat := ⟨1, 1, ⟨1, 1, 0⟩⟩
  SignedRemainderChain.subIsZero ((x - 1) * (x + 1)) (1 * p + DensePoly.scale 0 1) &&
    !({steps := [first, last], result := 1} : Reduction Rat).check sign p [x - 1, x + 1] [1, 1]

/- End-to-end replay binds the reduced query, exponent vector and context.
The certificate for a correct reduced polynomial cannot justify an altered
reduction, or stand in for the full product's literal query binding. -/
#guard match Sturm.prepare sign p .negInf .posInf with
  | none => false
  | some d =>
    let qs := [x.natPow 7, x + 1]
    let es := [2, 1]
    let r := Reduction.build sign p qs es
    let cert := Sturm.certifyPrepared (7 : Nat) d r.result
    checkMoment sign 7 p .negInf .posInf qs es cert.value cert (some r) &&
    !checkMoment sign 8 p .negInf .posInf qs es cert.value cert (some r) &&
    !checkMoment sign 7 p .negInf .posInf qs [1, 1] cert.value cert (some r) &&
    !checkMoment sign 7 p .negInf .posInf qs es cert.value cert
      (some {r with result := r.result + 1}) &&
    !checkMoment sign 7 p .negInf .posInf qs es cert.value cert none &&
    r.steps.all (fun s => s.next.isZero || decide (s.next.natDegree < p.natDegree)) &&
    decide (r.result.natDegree < p.natDegree) && decide (14 < (moment qs es).natDegree)

/- Zero differences accept semantically equal final representatives while
the Tarski certificate still binds the exact representative supplied to it. -/
#guard
  let head := Hex.TarskiTests.Noncanonical.head
  let sign := Hex.TarskiTests.Noncanonical.sign
  let q := DensePoly.C HexPoly.InterpretTests.root
  let r := Reduction.build sign head [q] [1]
  let r' := {r with result := (1 : HexPoly.InterpretTests.Poly)}
  r'.check sign head [q] [1] &&
    match Sturm.prepare sign head .negInf .posInf with
    | none => false
    | some d =>
      let cert := Sturm.certifyPrepared (7 : Nat) d q
      checkMoment sign 7 head .negInf .posInf [q] [1] cert.value cert
        (some {r with result := q}) &&
      !checkMoment sign 7 head .negInf .posInf [q] [1] cert.value cert (some r')

#guard match Sturm.prepare Hex.TarskiTests.Noncanonical.sign
    Hex.TarskiTests.Noncanonical.head .negInf .posInf with
  | none => false
  | some d => match buildPrepared 7 d [HexPoly.InterpretTests.x,
      HexPoly.InterpretTests.x - DensePoly.C HexPoly.InterpretTests.root] with
    | .error _ => false
    | .ok t => entries t.val.node.system == [([-1, -1], 1), ([1, 0], 1)]

/-- Malformed moment right-hand sides exercise exact conversion diagnostics. -/
def solveError (values : Vector Int 3) (expected : BuildError) : Bool :=
  match solveSystem 1 #v[[0], [1], [2]] #v[[-1], [0], [1]] values with
  | .error e => e == expected
  | .ok _ => false

#guard solveError #v[0, 1, 0] .nonintegral
#guard solveError #v[0, 2, 0] .negative
#guard match solveScaled 1 #v[[0]] #v[[1]] #v[2] (-3) (Matrix.ofRows #v[#v[-3]]) with
  | .ok s => s.counts == #v[2] && s.check 1
  | _ => false
#guard match solveScaled 1 #v[[0]] #v[[1]] #v[1] 2 (Matrix.ofRows #v[#v[1]]) with
  | .error .nonintegral => true
  | _ => false
#guard match solveScaled 1 #v[[0]] #v[[1]] #v[-1] 1 (Matrix.ofRows #v[#v[1]]) with
  | .error .negative => true
  | _ => false
#guard match solveScaled 1 #v[[0]] #v[[1]] #v[2] 0 (Matrix.ofRows #v[#v[1]]) with
  | .error .singular => true
  | _ => false
#guard match solveScaled 1 #v[[0]] #v[[1]] #v[2] 1 (Matrix.ofRows #v[#v[2]]) with
  | .error .system => true
  | _ => false
#guard match solveSystem 1 #v[[0], [1]] #v[[1], [1]] #v[1, 1] with
  | .error .singular => true
  | _ => false
#guard match solveSystem 1 #v[[3]] #v[[1]] #v[1] with
  | .error .system => true
  | _ => false
#guard match Sturm.prepare sign p .negInf .posInf with
  | some d => match buildNode 7 d [] [] [[]] with
    | .error .dimensions => true
    | _ => false
  | none => false

example : words [-1, 0, 1] 0 = leafColumns 0 := by decide +kernel
example : words [-1, 0, 1] 1 = leafColumns 1 := by decide +kernel
example : words [0, 1, 2] 0 = leafRows 0 := by decide +kernel
example : words [0, 1, 2] 1 = leafRows 1 := by decide +kernel

/-- Literal finite systems keep the downstream moment-contract probe small;
the query and rank certificates are independently produced for replay testing. -/
@[expose] def observedLeaf (cs vs : Vector Int 3) : System 3 where
  rows := #v[[0], [1], [2]]
  columns := #v[[-1], [0], [1]]
  counts := cs
  values := vs
  inverse := Matrix.ofRows #v[#v[0, -1, 1], #v[2, 0, -2], #v[0, 1, 1]]
  denominator := 2

@[expose] def observedParent : System 4 where
  rows := #v[[0, 0], [0, 1], [1, 0], [1, 1]]
  columns := #v[[-1, -1], [-1, 0], [1, -1], [1, 0]]
  counts := #v[1, 0, 0, 1]
  values := #v[2, -1, 0, 1]
  inverse := Matrix.ofRows #v[#v[0, -1, 0, 1], #v[1, 1, -1, -1],
    #v[0, -1, 0, -1], #v[1, 1, 1, 1]]
  denominator := 2

@[expose] def observedNode {r : Nat} (d : Sturm.PreparedDomain Rat)
    (qs : List (DensePoly Rat)) (s : System r) : Node Rat Nat where
  context := 7
  head := d.head
  lower := d.lower
  upper := d.upper
  queries := qs
  size := r
  system := s
  moments := s.rows.map fun e => Sturm.certifyPrepared 7 d (moment qs e)
  basis := Matrix.rankCert s.retainedMatrix

@[expose] def observedTree (d : Sturm.PreparedDomain Rat) : Replay Rat Nat :=
  .split (observedNode d [x, x - 1] observedParent)
    (.leaf (observedNode d [x] (observedLeaf #v[1, 0, 1] #v[2, 0, 2])))
    (.leaf (observedNode d [x - 1] (observedLeaf #v[1, 1, 0] #v[2, -1, 1])))

/-- This downstream ordinary-kernel proof pins both observation restrictions
and all node moments. It also detects hidden bodies at the module boundary. -/
theorem observed_interprets (d : Sturm.PreparedDomain Rat) :
    (observedTree d).Interprets 2 [[-1, -1], [1, 0]] := by
  simp only [observedTree, Replay.Interprets, observedNode, observedLeaf, observedParent]
  simp only [moments, ← Hex.Vector.ofFn'_eq_ofFn]
  decide +kernel

example (d : Sturm.PreparedDomain Rat)
    (h : (observedTree d).check sign 7 d.head d.lower d.upper [x, x - 1] = true)
    (σ : List Int) : σ ∈ (observedTree d).node.system.support ↔ σ ∈ [[-1, -1], [1, 0]] :=
  Replay.support_iff h (by simp [Observations]) (observed_interprets d) σ

#guard match Sturm.prepare sign p .negInf .posInf with
  | some d => (observedTree d).check sign 7 p .negInf .posInf [x, x - 1]
  | none => false

/- The recursive theorem has no semantic root-sum axiom hidden in its proof. -/
/-- info: 'Hex.SignDet.Replay.support_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Replay.support_complete

/-- info: 'Hex.SignDet.Replay.support_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Replay.support_iff

/-- info: 'Hex.SignDet.count_moments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms count_moments

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

/-- Mutate the actual constructor's output as well as independent fixtures. -/
def rejectsProduced (f : Replay Rat Nat → Replay Rat Nat) : Bool :=
  match Sturm.prepare sign p .negInf .posInf with
  | none => false
  | some d => match buildPrepared 7 d [x, x - 1] with
    | .error _ => false
    | .ok t => !accepts [x, x - 1] (f t.val)

#guard rejectsProduced (mapNode fun n => {n with context := 8})
#guard rejectsProduced (mapNode fun n => {n with preparation := n.preparation.map fun r =>
  {r with steps := r.steps.reverse}})
#guard rejectsProduced (mapNode fun n => {n with preparation := n.preparation.map fun r =>
  {r with steps := []}})
#guard rejectsProduced (mapNode fun n => {n with preparation := n.preparation.map fun r =>
  {r with steps := r.steps.map fun s => {s with index := s.index + 1}}})
#guard rejectsProduced (mapNode fun n => {n with preparation := n.preparation.map fun r =>
  {r with steps := r.steps.map fun s => {s with next := s.next + 1}}})
#guard rejectsProduced (mapNode fun n => {n with preparation := n.preparation.map fun r =>
  {r with steps := r.steps.map fun s =>
    {s with witness := {s.witness with leftScale := -s.witness.leftScale}}}})
#guard rejectsProduced (fun t => match t with
  | .leaf n => .leaf n
  | .split n l r => .split {n with preparation := l.node.preparation} l r)
#guard rejectsProduced (mapNode fun n => replaceSystem n {n.system with counts := n.system.counts.map (· + 1)})
#guard rejectsProduced (fun t => match t with | .leaf n => .leaf n | .split n l r => .split n r l)
#guard rejectsProduced (mapNode fun n => {n with reductions := n.reductions.map (fun r =>
  r.map fun r => {r with result := r.result + 1})})
#guard rejectsProduced (mapNode fun n => {n with reductions := n.reductions.map (fun r =>
  r.map fun r => {r with steps := r.steps.map fun s => {s with index := s.index + 1}})})
#guard rejectsProduced (fun t => match t with
  | .leaf n => .leaf n
  | .split n l r => .split n (mapNode (fun c => {c with reductions := c.reductions.map (fun r =>
      r.map fun r => {r with steps := []})}) l) r)
#guard mutate (mapNode fun n => {n with basis := {n.basis with
  rows := n.basis.rows.map (fun i => ⟨0, Nat.zero_lt_of_lt i.isLt⟩)}})
#guard mutate (mapNode fun n => {n with basis := {n.basis with
  cols := n.basis.cols.map (fun i => ⟨0, Nat.zero_lt_of_lt i.isLt⟩)}})

example : entry [0, 0] [0, 0] = 1 := by decide +kernel
example : momentMatrix #v[[0], [1], [2]] #v[[-1], [0], [1]] =
    Matrix.ofRows #v[#v[1, 1, 1], #v[-1, 0, 1], #v[1, 0, 1]] := by decide +kernel

/-- A parent forgery omitting the realized condition (-1,-1). Three genuine
moments permit the false counts (1,1,0) on (-1,0), (1,-1), (1,0). Both complete
children remain intact; recursive replay must reject the parent support. -/
def internalForgery : Option (Replay Rat Nat) := do
  let .split _ l r ← fixture p [-1, 1] [x, x - 1] | none
  let d ← Sturm.prepare sign p .negInf .posInf
  let n ← makeNode d [x, x - 1] [[0, 0], [0, 1], [1, 0]]
    [[-1, 0], [1, -1], [1, 0]] []
  let n := replaceSystem n {n.system with
    counts := Vector.ofFn fun i => if i.val < 2 then 1 else 0}
  return .split n l r

#guard match internalForgery with
  | some (.split n l r) =>
    n.check sign 7 p .negInf .posInf [x, x - 1] &&
    l.check sign 7 p .negInf .posInf [x] &&
    r.check sign 7 p .negInf .posInf [x - 1] &&
    !accepts [x, x - 1] (.split n l r)
  | _ => false

/-- Preserve the local equations while reversing candidate-column order. -/
def reverseColumns (n : Node Rat Nat) : Node Rat Nat :=
  replaceSystem n {n.system with
    columns := Vector.ofFn fun i => n.system.columns[i.rev]
    counts := Vector.ofFn fun i => n.system.counts[i.rev]
    inverse := Matrix.ofFn fun i j => n.system.inverse[(i.rev, j)]}

/-- Preserve local equations and query evidence while reversing moment rows. -/
def reverseRows (n : Node Rat Nat) : Node Rat Nat :=
  let s := {n.system with
    rows := Vector.ofFn fun i => n.system.rows[i.rev]
    values := Vector.ofFn fun i => n.system.values[i.rev]
    inverse := Matrix.ofFn fun i j => n.system.inverse[(i, j.rev)]}
  {n with
    system := s
    basis := Matrix.rankCert s.retainedMatrix
    moments := Vector.ofFn fun i => n.moments[i.rev]}

/-- Length-only product comparisons would accept these valid local systems.
The full checker must enforce the exact child-product orders. -/
def rejectsOrder (f : Node Rat Nat → Node Rat Nat) : Bool :=
  match fixture p [-1, 1] [x, x - 1] with
  | some (.split n l r) =>
    let changed := f n
    changed.check sign 7 p .negInf .posInf [x, x - 1] &&
    l.check sign 7 p .negInf .posInf [x] &&
    r.check sign 7 p .negInf .posInf [x - 1] &&
    decide (changed.system.columns.toList.length =
      (product l.node.system.support r.node.system.support).length) &&
    decide (changed.system.rows.toList.length = (product l.node.rows r.node.rows).length) &&
    !accepts [x, x - 1] (.split changed l r)
  | _ => false

#guard rejectsOrder reverseColumns
#guard rejectsOrder reverseRows

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
  reductions := #v[none]
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
  simp only [Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Restrict the literal root-count certificate to the positive root. -/
@[expose] def singletonQuery : TarskiCertificate Rat Rat Nat :=
  {Sturm.Fixtures.literal with
    lower := .finite 0
    lowerSigns := #[-1, 0, 1]
    lowerVariations := 1
    value := 1}

@[expose] def singletonNode : Node Rat Nat :=
  {literalNode with
    lower := .finite 0
    system := {literalSystem with counts := #v[1], values := #v[1]}
    moments := #v[singletonQuery]}

@[expose] def singletonRaw : RawDescriptor Rat Nat :=
  ⟨7, Sturm.Fixtures.p, .finite 0, .finite 2, [], []⟩

@[expose] def selectedNode : Node Rat Nat where
  context := 7
  head := Sturm.Fixtures.p
  lower := .finite 0
  upper := .finite 2
  queries := [1]
  size := 3
  system := {
    rows := #v[[0], [1], [2]]
    columns := #v[[-1], [0], [1]]
    counts := #v[0, 0, 1]
    values := #v[1, 1, 1]
    denominator := 2
    inverse := Matrix.ofRows #v[#v[0, -1, 1], #v[2, 0, -2], #v[0, 1, 1]] }
  moments := #v[singletonQuery, singletonQuery, singletonQuery]
  basis := {
    rank := 1
    rows := #v[0]
    cols := #v[⟨0, by decide +kernel⟩]
    denom := 1
    adj := Matrix.identity 1}

set_option maxRecDepth 16384 in
/-- Ordinary-kernel count-one descriptor and selected-query replay. The
literals contain no prepared-domain construction or opaque table extraction. -/
theorem selected_kernel :
    singletonRaw.check Sturm.orderSign 7 (.leaf singletonNode) = true ∧
    singletonRaw.checkSigns Sturm.orderSign 7 [1] #v[1] (.leaf selectedNode) = true ∧
    singletonRaw.checkSigns Sturm.orderSign 7 [1] #v[0] (.leaf selectedNode) = false ∧
    singletonRaw.checkSigns Sturm.orderSign 8 [1] #v[1] (.leaf selectedNode) = false := by
  simp only [RawDescriptor.check, RawDescriptor.checkSigns, Replay.check, Node.check_eq,
    checkMoment_eq, queryPoly, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Literal certificates for the positive constant derivative and its square.
Only the initial multiplier changes in the signed remainder chain. -/
@[expose] def constantQuery (c : Rat) : TarskiCertificate Rat Rat Nat :=
  {singletonQuery with
    queryPoly := DensePoly.C c
    remainders := {Sturm.Fixtures.literalChain with initial := ⟨1, 0, 2 * c⟩}}

@[expose] def derivativeNode : Node Rat Nat :=
  {selectedNode with
    queries := [DensePoly.C 2]
    moments := #v[singletonQuery, constantQuery 2, constantQuery 4]}

@[expose] def derivativeRaw : RawDescriptor Rat Nat :=
  {singletonRaw with indices := [2], signs := [1]}

set_option maxRecDepth 16384 in
/-- Kernel replay forces both formal derivative iterations. A copied tree
for the sign-equivalent constant one is rejected by literal query binding. -/
theorem derivative_kernel :
    derivativeRaw.check Sturm.orderSign 7 (.leaf derivativeNode) = true ∧
    derivativeRaw.check Sturm.orderSign 7 (.leaf selectedNode) = false := by
  simp only [RawDescriptor.check, Replay.check, Node.check_eq, checkMoment_eq, queryPoly,
    Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Literal first-derivative query: 4X² = 4(X²-1) + 4. -/
@[expose] def firstQuery : TarskiCertificate Rat Rat Nat :=
  {singletonQuery with
    queryPoly := 2 * Sturm.Fixtures.x
    remainders := {
      chain := #[Sturm.Fixtures.p, 1]
      degrees := #[2, 0]
      initial := ⟨1, 4, 4⟩
      steps := #[]
      terminal := some (1, Sturm.Fixtures.p)}
    lowerSigns := #[-1, 1]
    upperSigns := #[1, 1]}

/-- Literal square query: 8X³ = 8X(X²-1) + 8X. -/
@[expose] def firstSquare : TarskiCertificate Rat Rat Nat :=
  {singletonQuery with
    queryPoly := 4 * Sturm.Fixtures.x * Sturm.Fixtures.x
    remainders := {Sturm.Fixtures.literalChain with initial := ⟨1, 8 * Sturm.Fixtures.x, 8⟩}}

@[expose] def firstNode : Node Rat Nat :=
  {selectedNode with
    queries := [2 * Sturm.Fixtures.x]
    moments := #v[singletonQuery, firstQuery, firstSquare]}

@[expose] def fullNode : Node Rat Nat :=
  {singletonNode with
    queries := [2 * Sturm.Fixtures.x, DensePoly.C 2]
    system := {literalSystem with
      rows := #v[[0, 0]], columns := #v[[1, 1]], counts := #v[1], values := #v[1]}}

@[expose] def fullReplay : Replay Rat Nat :=
  .split fullNode (.leaf firstNode) (.leaf derivativeNode)

set_option maxRecDepth 32768 in
/-- A full two-derivative tree replays in the ordinary kernel, including both
leaf supports and the exact Cartesian parent. No producer is evaluated. -/
theorem full_kernel : fullReplay.check Sturm.orderSign 7 singletonRaw.head
    singletonRaw.lower singletonRaw.upper (singletonRaw.full []).queries = true := by
  simp only [fullReplay, Replay.check, Node.check_eq, checkMoment_eq, queryPoly,
    Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Extract the unique full row using the shared literal replay proof. -/
def sharedDescriptor : Descriptor Rat Nat Sturm.orderSign 7 :=
  Descriptor.ofFullRow singletonRaw fullReplay (by decide +kernel) rfl full_kernel ([1, 1], 1)
    (by rw [Replay.table_rows]; decide +kernel) rfl

theorem shared_descriptor :
    sharedDescriptor.raw.check Sturm.orderSign 7 sharedDescriptor.evidence = true :=
  sharedDescriptor.accepted

@[expose] def forgedNode : Node Rat Nat :=
  {literalNode with queries := [Sturm.Fixtures.x], system := forged}

/-- Finite interpretation plus kernel replay determines every lookup,
including absent conditions, without trusting compiled table values. -/
theorem literal_table_count (c : List Int) :
    ((Replay.leaf literalNode).table literal_accepts).count c =
      if c = [] then 2 else 0 := by
  have ho : Observations 0 [[], []] := by simp [Observations]
  have hm : (Replay.leaf literalNode).Interprets 0 [[], []] := by
    simp only [Replay.Interprets, literalNode, literalSystem, moments, ← Hex.Vector.ofFn'_eq_ofFn]
    decide +kernel
  have he := Replay.table_count (Replay.leaf literalNode) literal_accepts ho hm c
  by_cases hc : c = [] <;> simp_all

set_option maxRecDepth 8192 in
/-- Local query/matrix evidence really passes for the omitted-support forgery. -/
theorem forged_local : forgedNode.check Sturm.orderSign 7 Sturm.Fixtures.p
    (.finite (-2)) (.finite 2) [Sturm.Fixtures.x] = true := by
  simp only [Node.check_eq, checkMoment_eq, queryPoly, Sturm.check, TarskiCertificate.check_eq,
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

/-- info: 'Hex.SignDet.Replay.query_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Replay.query_evidence
/-- info: 'Hex.SignDet.Replay.table_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Replay.table_count
/-- info: 'Hex.SignDet.Conformance.literal_table_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_table_count
/-- info: 'Hex.SignDet.RawDescriptor.check_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RawDescriptor.check_count
/-- info: 'Hex.SignDet.Conformance.selected_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selected_kernel
/-- info: 'Hex.SignDet.Conformance.derivative_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms derivative_kernel
/-- info: 'Hex.SignDet.Conformance.full_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms full_kernel
/-- info: 'Hex.SignDet.Conformance.shared_descriptor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shared_descriptor
/-- info: 'Hex.SignDet.Reencoding.count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Reencoding.count
/-- info: 'Hex.SignDet.SelectedSigns.signs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SelectedSigns.signs_eq
/-- info: 'Hex.SignDet.Descriptor.rootsFrom_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.rootsFrom_perm
/-- info: 'Hex.SignDet.Descriptor.rootsFrom_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.rootsFrom_sorted
/-- info: 'Hex.SignDet.Descriptor.rootsFromTable_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.rootsFromTable_eq
/-- info: 'Hex.SignDet.Descriptor.rootsFromTable_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.rootsFromTable_perm
/-- info: 'Hex.SignDet.Descriptor.rootsFromTable_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.rootsFromTable_sorted
/-- info: 'Hex.SignDet.SelectedSigns.count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SelectedSigns.count
/-- info: 'Hex.SignDet.SelectedSigns.ternary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SelectedSigns.ternary
/-- info: 'Hex.SignDet.Thom.compareSigns_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Thom.compareSigns_eq
/-- info: 'Hex.SignDet.Replay.check_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Replay.check_children

/-- info: 'Hex.SignDet.Node.check_bindings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Node.check_bindings
/-- info: 'Hex.SignDet.mem_product' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_product
/-- info: 'Hex.SignDet.Conformance.forged_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forged_local
/-- info: 'Hex.SignDet.Conformance.forged_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forged_rejected
/-- info: 'Hex.SignDet.Conformance.empty_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms empty_rejected

/-- info: 'Hex.SignDet.Descriptor.buildRoots_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.buildRoots_spec
/-- info: 'Hex.SignDet.Descriptor.buildRoots_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.buildRoots_perm
/-- info: 'Hex.SignDet.Descriptor.buildRoots_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.buildRoots_sorted

/-- info: 'Hex.SignDet.Descriptor.rootsFrom_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.rootsFrom_raw
/-- info: 'Hex.SignDet.Descriptor.buildRoots_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.buildRoots_raw
/-- info: 'Hex.SignDet.Descriptor.buildRoots_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.buildRoots_constant

/-- info: 'Hex.SignDet.Thom.compareFrom_cons_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Thom.compareFrom_cons_lt
/-- info: 'Hex.SignDet.Thom.compareFrom_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Thom.compareFrom_trans
/-- info: 'Hex.SignDet.Thom.compareFrom_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Thom.compareFrom_swap
/-- info: 'Hex.SignDet.Thom.compareSigns_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Thom.compareSigns_trans
/-- info: 'Hex.SignDet.Thom.compareSigns_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Thom.compareSigns_swap
/-- info: 'Hex.SignDet.Descriptor.fullOrder_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.fullOrder_trans
/-- info: 'Hex.SignDet.Descriptor.fullOrder_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.fullOrder_reverse

end Hex.SignDet.Conformance

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet
import HexSignDet.Convert
import HexSignDet.Codec
import HexSignDet.DagSelectedSigns
import HexSignDet.DagEncode
import HexSignDet.CommonField
import HexSignDet.CrossCheck
import HexSignDet.Infinitesimal
import HexRealRoots.TarskiTests

/-! Compiled sign-determination checks over genuine number fields.

Every public sign-determination operation (descriptor validation and selected
signs, completion, query handles, root lists, tables, comparison, re-encoding,
refinement, Thom re-encoding to a new defining polynomial, conversion, and
supplied graph signs) runs here over `ℚ(∛2)` in its real embedding, with
coefficient signs computed from the canonical real algebraic value of each
coordinate. A common quartic field for two independent quadratic
irrationalities, a noninjective rational coefficient carrier and nested
infinitesimal fields exercise the cases those carriers distinguish.
The driver is Mathlib-free; the semantic theorems instantiated at the cubic
field live in `conformance/HexSignDetMathlib/FieldConformance.lean`. -/
namespace Hex.SignDet.FieldChecks

open Hex Hex.SignDet

/-! ## The cubic field `ℚ(∛2)` -/

/-- The real cube root of two. Irreducible so that elaboration never
evaluates root isolation. -/
@[irreducible] def generator : AlgebraicNumber := ZPoly.rootNear #p[-2, 0, 0, 1] 1.26

abbrev CubicField := QAdjoin generator

def alpha : CubicField := generator.toQAdjoin

/-- Coordinate signs use the generator's selected real embedding. -/
def fieldSign (a : CubicField) : Int := CommonField.sign a

def xPoly : DensePoly CubicField := DensePoly.ofList [0, 1]

/-- The two real roots ±∛2. -/
def head : DensePoly CubicField :=
  (xPoly - DensePoly.C alpha) * (xPoly + DensePoly.C alpha)

def queries : List (DensePoly CubicField) :=
  [xPoly - 1, xPoly - DensePoly.C 2, xPoly.natPow 3 - DensePoly.C 2, xPoly - 1]

/-- The same queries with the first two exchanged. -/
def reordered : List (DensePoly CubicField) :=
  [xPoly - DensePoly.C 2, xPoly - 1, xPoly.natPow 3 - DensePoly.C 2, xPoly - 1]

/-- A propositional length equation, so that the kernel never compares the
two query lists by unfolding cubic-field arithmetic. -/
theorem reordered_length : reordered.length = queries.length := by
  simp only [reordered, queries, List.length_cons, List.length_nil]

/-- The first derivative sign selects +∛2. -/
def raw : RawDescriptor CubicField Nat :=
  ⟨7, head, .negInf, .posInf, [1], [1]⟩

/-- Three roots −∛2, 0, ∛2. -/
def cubicHead : DensePoly CubicField := head * xPoly

/-! ## Selected signs -/

/-- The derivative word selects +∛2 rather than −∛2. Query order and
repetitions are retained, a nonzero cubic query vanishes at the root, and
evidence is rejected after any change of context, head, word or values. -/
def selectedPasses : Bool :=
  generator.p.natDegree == 3 &&
  match Descriptor.build fieldSign 7 raw with
  | .ok (.ok d) =>
    match d.buildSigns queries, d.buildSigns [] with
    | .ok s, .ok empty =>
      s.values.toList == [1, -1, 0, 1] && empty.values.toList == [] &&
        d.checkSigns queries s.values s.evidence &&
        !d.checkSigns queries #v[-1, -1, 0, 1] s.evidence &&
        !d.checkSigns reordered (s.values.cast reordered_length.symm) s.evidence &&
        !({raw with context := 8}).checkSigns fieldSign 8 queries s.values s.evidence &&
        !({raw with head := head + 1}).checkSigns fieldSign 7 queries s.values s.evidence &&
        !({raw with indices := [2]}).checkSigns fieldSign 7 queries s.values s.evidence &&
        !({raw with signs := [-1]}).checkSigns fieldSign 7 queries s.values s.evidence &&
        !({raw with context := 8}).check fieldSign 8 d.evidence &&
        !({raw with head := head + 1}).check fieldSign 7 d.evidence
    | _, _ => false
  | _ => false

/-- The total one-query operation, including the zero polynomial. -/
def totalSignsPasses : Bool :=
  match Descriptor.validate fieldSign 7 raw with
  | some d =>
    d.signAt (xPoly - 1) == 1 && d.signAt (xPoly - DensePoly.C 2) == -1 &&
      d.signAt (xPoly.natPow 3 - DensePoly.C 2) == 0 && d.signAt 0 == 0
  | none => false

/-! ## Completion -/

/-- The second derivative sign of the three-root cubic selects +∛2. -/
def positive : RawDescriptor CubicField Nat :=
  ⟨7, cubicHead, .negInf, .posInf, [2], [1]⟩

/-- Compare every stored field, without quotienting coefficient representations. -/
def sameRaw (a b : RawDescriptor CubicField Nat) : Bool :=
  decide (a.context = b.context) && decide (a.head = b.head) &&
    decide (a.lower = b.lower) && decide (a.upper = b.upper) &&
    decide (a.indices = b.indices) && decide (a.signs = b.signs)

/-- The total accessor agrees with checked construction and the literal full
descriptor; the completed result fails every changed source binding. -/
def completesAs (raw : RawDescriptor CubicField Nat) (word : List Int) : Bool :=
  match Descriptor.validate fieldSign 7 raw with
  | none => false
  | some d =>
    match d.buildCompletion with
    | .error _ => false
    | .ok c =>
      let out := d.complete
      sameRaw out.raw (raw.full word) && sameRaw out.raw c.descriptor.raw &&
        raw.completes out.raw &&
        !({raw with context := 8}).completes out.raw &&
        !({raw with head := raw.head + 1}).completes out.raw &&
        !({raw with lower := .finite 0}).completes out.raw &&
        (raw.signs.isEmpty ||
          !({raw with signs := raw.signs.map (fun s => if s = 0 then 1 else -s)}).completes out.raw) &&
        !({raw with indices := [0]}).completes out.raw

/-! ## Query handles -/

/-- Joint and singleton calls through a prepared handle agree with the
expected signs; fresh descriptors reject evidence copied from this one. -/
def preparedPasses : Bool :=
  let qs := queries
  let expected := [1, -1, 0, 1]
  let targets : List (RawDescriptor CubicField Nat) :=
    [{raw with indices := [1, 2], signs := [1, 1]}, {raw with context := 8},
      {raw with signs := [-1]}, {raw with lower := .finite 1, upper := .finite 2}]
  match Descriptor.validate fieldSign 7 raw with
  | none => false
  | some d =>
    match d.prepareQueries with
    | none => false
    | some h =>
      match h.buildSigns qs, h.buildSigns [] with
      | .ok s, .ok empty =>
        s.values.toList == expected && empty.values.toList == [] &&
          h.checkSigns qs s.values s.evidence &&
          !h.checkSigns qs (s.values.map fun value => value + 1) s.evidence &&
          !s.evidence.check fieldSign 7 raw.head raw.lower raw.upper
            (d.raw.queries ++ qs.reverse) &&
          (qs.zip expected).all (fun (q, value) => h.signAt q == value) &&
          (match h.buildSigns [0] with
            | .ok single => single.value == 0 && h.signAt 0 == 0
            | .error _ => false) &&
          targets.all (fun target =>
            match Descriptor.validate fieldSign target.context target with
            | none => false
            | some other => match other.prepareQueries with
              | none => false
              | some otherHandle => !otherHandle.checkSigns qs s.values s.evidence)
      | _, _ => false

/-! ## Root lists -/

/-- Successful enumeration with full words, literal bindings, context-bound
evidence and strictly increasing Thom order. -/
def rootsAs {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E]
    [Mul E] [NatCast E] [Neg E] [Inv E]
    (sign : E → Int) (p : DensePoly E) (a b : Endpoint E)
    (words : List (List Int)) : Bool :=
  match Descriptor.buildRoots sign 7 p a b with
  | .ok (some roots) =>
    roots.map (fun d => d.raw.signs) == words &&
      roots.all (fun d => d.raw.context == 7 && d.raw.head == p &&
        d.raw.lower == a && d.raw.upper == b &&
        d.raw.indices == List.range' 1 p.natDegree &&
        d.raw.check sign 7 d.evidence &&
        !d.raw.check sign 8 d.evidence) &&
      decide (roots.Pairwise (fun d e => d.fullOrder e = some .lt))
  | _ => false

/-- An invalid domain is reported as such, not as an empty root list. -/
def invalidDomain (p : DensePoly CubicField) (a b : Endpoint CubicField) : Bool :=
  match Descriptor.buildRoots fieldSign 7 p a b with
  | .ok none => true
  | _ => false

/-- Enumerate 0 and ε without a rational separator; their derivative words
determine their strict order. -/
def infinitesimalRootsPasses : Bool :=
  let x : DensePoly Infinitesimal.First := Infinitesimal.x
  let epsilon := Infinitesimal.epsilon
  let p := x * (x - DensePoly.C epsilon)
  match Descriptor.buildRoots Infinitesimal.firstSign 7 p (.finite (-1)) (.finite 1) with
  | .ok (some roots) =>
    roots.map (fun d => d.raw.signs) == [[-1, 1], [1, 1]] &&
      roots.map (fun d => d.signAt x) == [0, 1] &&
      roots.map (fun d => d.signAt (x - DensePoly.C epsilon)) == [-1, 0] &&
      roots.all (fun d => d.raw.check Infinitesimal.firstSign 7 d.evidence &&
        !d.raw.check Infinitesimal.firstSign 8 d.evidence) &&
      decide (roots.Pairwise (fun d e => d.fullOrder e = some .lt))
  | _ => false

/-! ## Tables -/

/-- The checked, total and prepared table paths agree; one nonzero query
vanishes at a head root, and absent words count zero. -/
def tablePasses : Bool :=
  let qs := [xPoly - DensePoly.C alpha, xPoly - 1, xPoly - DensePoly.C 2]
  let rows := [([-1, -1, -1], 1), ([0, 1, -1], 1)]
  let zeros : List (List Int) := [[1, 1, -1], [0, 0, 0]]
  match Sturm.prepare fieldSign head .negInf .posInf with
  | none => false
  | some domain =>
    match buildTablePrepared 7 domain qs true, determine fieldSign 7 head .negInf .posInf qs true with
    | .ok checked, some actual =>
      let prepared := determinePrepared 7 domain qs true
      checked.rows.toList == rows && actual.rows.toList == rows &&
        prepared.rows.toList == rows &&
        zeros.all (fun word => checked.count word == 0 &&
          actual.count word == 0 && prepared.count word == 0)
    | _, _ => false

/-! ## Common number field of two quadratic irrationalities -/

def commonInputs : Array AlgebraicNumber := #[
  ZPoly.rootNear #p[-2, 0, 1] 1.4,
  ZPoly.rootNear #p[-3, 0, 1] 1.7]

/-- At a=√2 and b=√3 in their quartic common field, the root rows of
(x−a)(x−b) have signs (0,−,−) and (+,0,−). Enumeration, comparison and
re-encoding use those coordinates; equal roots of different heads compare
equal, and copied or stale evidence rejects. -/
def commonFieldPasses : Bool := Id.run do
  let common := QAdjoin.common commonInputs
  if common.entries.map (·.toAlgebraicNumber) != commonInputs then return false
  if common.generator.p.natDegree != 4 then return false
  if !common.generator.isReal then return false
  let sign := @CommonField.sign common.generator
  let some a := common.entries[0]? | return false
  let some b := common.entries[1]? | return false
  let x : DensePoly (QAdjoin common.generator) := DensePoly.ofList [0, 1]
  let qa := x - DensePoly.C a
  let qb := x - DensePoly.C b
  let head := qa * qb
  let queries := [qa, qb, DensePoly.C (a - b)]
  let some table := determine sign 7 head .negInf .posInf queries | return false
  if table.rows.toList != [([0, -1, -1], 1), ([1, 0, -1], 1)] then return false
  if table.count [0, 0, -1] != 0 then return false
  let .ok (some roots) := Descriptor.buildRoots sign 7 head .negInf .posInf | return false
  if roots.map (fun d => d.raw.signs) != [[-1, 1], [1, 1]] then return false
  if roots.map (fun d => d.signAt qa) != [0, 1] then return false
  if roots.map (fun d => d.signAt qb) != [-1, 0] then return false
  let rawA : RawDescriptor (QAdjoin common.generator) Nat :=
    ⟨7, head, .negInf, .posInf, [1], [-1]⟩
  let rawB : RawDescriptor (QAdjoin common.generator) Nat :=
    ⟨7, qb, .negInf, .posInf, [1], [1]⟩
  let some left := Descriptor.validate sign 7 rawA | return false
  let some right := Descriptor.validate sign 7 rawB | return false
  if left.compare right != .lt || right.compare left != .gt then return false
  let .ok (some same) := left.buildReencoding qa .negInf .posInf | return false
  let square := x * x - DensePoly.C (a * a)
  let some squareRoot := Descriptor.validate sign 7
    (⟨7, square, .negInf, .posInf, [1], [1]⟩ :
      RawDescriptor (QAdjoin common.generator) Nat) | return false
  return left.compare same.target == .eq &&
    same.target.compare squareRoot == .eq &&
    squareRoot.compare same.target == .eq &&
    same.target.signAt qa == 0 && same.target.signAt qb == -1 &&
    left.checkReencoding same.target qa .negInf .posInf same.evidence &&
    !same.target.raw.check sign 7 left.evidence &&
    !same.target.raw.check sign 8 same.target.evidence

/-- A nonreal common generator is rejected before coefficient signs are used. -/
def rejectsNonreal : Bool :=
  match (CommonField.fixture #[AlgebraicNumber.I, commonInputs[0]!]).getObjValAs?
      String "error" with
  | .ok message => message == "nonreal generator"
  | .error _ => false

/-! ## Re-encoding and absence -/

/-- An absence result requires successful source validation, rather than an
internal error being mistaken for absence of the selected root. -/
def absentAs (source : RawDescriptor CubicField Nat) (target : DensePoly CubicField)
    (a b : Endpoint CubicField) (prepared : Bool := true) : Bool :=
  match Descriptor.validate fieldSign 7 source with
  | none => false
  | some d =>
    ((Sturm.prepare fieldSign target a b).isSome == prepared) &&
    match d.buildReencoding target a b with
    | .ok none => true
    | _ => false

/-- A target containing the source root succeeds. -/
def presentPasses : Bool :=
  match Descriptor.validate fieldSign 7 raw with
  | none => false
  | some d =>
    let target := xPoly - DensePoly.C alpha
    match d.buildReencoding target .negInf .posInf with
    | .ok (some r) =>
      d.checkReencoding r.target target .negInf .posInf r.evidence &&
        r.target.raw.head == target
    | _ => false

/-- Refinement to a smaller interval: new interval, complete word, fresh
evidence; the old evidence is rejected for the new interval. -/
def refinementPasses : Bool :=
  let a : Endpoint CubicField := .finite 1
  let b : Endpoint CubicField := .finite 2
  match Descriptor.validate fieldSign 7 raw with
  | none => false
  | some d =>
    match d.buildReencoding raw.head a b with
    | .ok (some r) =>
      r.target.raw.lower == a && r.target.raw.upper == b &&
        r.target.raw.head == raw.head && r.target.raw.context == 7 &&
        r.target.raw.indices == [1, 2] && r.target.raw.signs == [1, 1] &&
        r.target.signAt (xPoly.natPow 3 - DensePoly.C 2) == 0 &&
        r.target.raw.check fieldSign 7 r.target.evidence &&
        !r.target.raw.check fieldSign 7 d.evidence &&
        !({raw with lower := a, upper := b}).check fieldSign 7 d.evidence &&
        d.checkReencoding r.target raw.head a b r.evidence &&
        !r.evidence.check fieldSign 7 raw.head raw.lower raw.upper
          (r.target.raw.queries ++ d.raw.constraints)
    | _ => false

/-- Re-encode a root selected by an empty word on (0,2) to a different defining
polynomial on the whole line. Both evidence layers retain the target head. -/
def thomReencoded (target : DensePoly CubicField) (signs : List Int)
    (differentHead : Bool := true) : Bool :=
  let source : RawDescriptor CubicField Nat :=
    {raw with lower := .finite 0, upper := .finite 2, indices := [], signs := []}
  match Descriptor.validate fieldSign 7 source with
  | none => false
  | some d =>
    match d.buildReencoding target .negInf .posInf with
    | .ok (some r) =>
      r.target.raw.head == target && r.target.raw.lower == .negInf &&
        r.target.raw.upper == .posInf && r.target.raw.signs == signs &&
        r.target.signAt (xPoly - DensePoly.C alpha) == 0 &&
        r.target.raw.check fieldSign 7 r.target.evidence &&
        (decide (target ≠ source.head) == differentHead) &&
        (if differentHead then
          !r.target.evidence.check fieldSign 7 source.head .negInf .posInf r.target.raw.queries
         else true) &&
        !r.target.evidence.check fieldSign 7 target source.lower source.upper r.target.raw.queries &&
        d.checkReencoding r.target target .negInf .posInf r.evidence
    | _ => false

/-- Refine an infinitesimal-width interval at the second nested level: no
positive rational lies inside it. -/
def infinitesimalRefinementPasses : Bool :=
  let head := Infinitesimal.nested
  let delta := Infinitesimal.delta
  let sign := Infinitesimal.secondSign
  let source : RawDescriptor Infinitesimal.Second Nat :=
    ⟨7, head, .finite 0, .finite (2 * delta), [], []⟩
  match Descriptor.validate sign 7 source with
  | none => false
  | some d =>
    match d.buildReencoding head (.finite (delta / 2)) (.finite (3 * delta / 2)) with
    | .ok (some r) =>
      r.target.raw.signs == [1, -1, 1] &&
        r.target.signAt (Infinitesimal.x - DensePoly.C delta) == 0 &&
        r.target.raw.check sign 7 r.target.evidence &&
        !r.target.raw.check sign 7 d.evidence &&
        !({source with lower := .finite (delta / 2), upper := .finite (3 * delta / 2)}).check
          sign 7 d.evidence
    | _ => false

/-! ## Noninjective coefficient storage -/

/-- The same polynomial rebuilt with different nonzero stored coefficients.
A zero difference permits re-encoding, while copied evidence still fails the
exact defining-polynomial binding on the same interval. -/
def changedHeadPasses : Bool :=
  let root := HexPoly.InterpretTests.root
  let source : RawDescriptor HexPoly.InterpretTests.Rep Nat :=
    ⟨7, DensePoly.ofCoeffs #[-root, 0, 1], .finite 0,
      .finite ((2 : Nat) : HexPoly.InterpretTests.Rep), [], []⟩
  let target : DensePoly HexPoly.InterpretTests.Rep := DensePoly.ofCoeffs #[-1, 0, root]
  let sign := Hex.TarskiTests.Noncanonical.sign
  match Descriptor.validate sign 7 source with
  | none => false
  | some d =>
    source.check sign 7 d.evidence &&
      decide (target ≠ source.head) && (target - source.head).isZero &&
      !({source with head := target}).check sign 7 d.evidence &&
      match d.buildReencoding target source.lower source.upper with
      | .ok (some r) =>
        r.target.raw.head == target && r.target.raw.signs == [1, 1] &&
          r.target.signAt (HexPoly.InterpretTests.x - DensePoly.C 1) == 0 &&
          r.target.raw.check sign 7 r.target.evidence &&
          !r.target.evidence.check sign 7 source.head source.lower source.upper
            r.target.raw.queries &&
          d.checkReencoding r.target target source.lower source.upper r.evidence
      | _ => false

/-! ## Comparison -/

/-- Every stage succeeds; both literal bindings and joint replays are checked,
and the total operation is exercised in both argument orders. -/
def compares (left right : RawDescriptor CubicField Nat) (expected : Ordering) : Bool :=
  match Descriptor.validate fieldSign 7 left, Descriptor.validate fieldSign 7 right with
  | some l, some r =>
    match l.buildComparison r with
    | .ok c =>
      c.order == expected && (l.buildOrder r).toOption == some expected &&
        (r.buildOrder l).toOption == some expected.swap &&
        l.compare r == expected && r.compare l == expected.swap &&
        c.common.check 7 left.head right.head &&
        !c.common.check 8 left.head right.head &&
        c.common.left == left.head && c.common.right == right.head &&
        l.checkReencoding c.leftEncoding.target c.common.head .negInf .posInf
          c.leftEncoding.evidence &&
        r.checkReencoding c.rightEncoding.target c.common.head .negInf .posInf
          c.rightEncoding.evidence
    | _ => false
  | _, _ => false

/-- +∛2 selected by an empty word on (0,2). -/
def cubicPositive : RawDescriptor CubicField Nat :=
  {raw with lower := .finite 0, upper := .finite 2, indices := [], signs := []}

/-- Zero and constant inputs use the total division kernel; a shared factor
is removed rather than squared. -/
def commonProductPasses : Bool :=
  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  let passes (p q : DensePoly Rat) (degree : Nat) (zero : Bool) : Bool :=
    match CommonProduct.build 7 p q with
    | .ok c => c.val.check 7 p q && c.val.head.natDegree == degree &&
      c.val.head.isZero == zero && !c.val.check 8 p q
    | _ => false
  passes 0 0 0 true && passes 0 (x - 1) 0 true && passes 2 3 0 false &&
    passes (x * x - 1) (x - 1) 2 false

/-! ## Supplied graph signs -/

open Hex.SignDet.Conformance Hex.SignDet.CrossCheck in
/-- One validated graph memo supplies two singleton queries and their joint
query; wrong values, slots and bindings reject. -/
def graphMemoPasses : Bool :=
  let partialRaw := {singletonRaw with indices := [1], signs := [1]}
  match Descriptor.ofReplay? Sturm.orderSign 7 singletonRaw (.leaf singletonNode),
      Descriptor.ofReplay? Sturm.orderSign 7 partialRaw (.leaf firstNode) with
  | some source, some prefixed =>
    match full.validate? Sturm.orderSign 7 source.raw.head source.raw.lower source.raw.upper with
    | none => false
    | some memo =>
      (SelectedSigns.ofMemo? source firstNode.queries #v[1] memo 0).isSome &&
      (SelectedSigns.ofMemo? source derivativeNode.queries #v[1] memo 1).isSome &&
      (SelectedSigns.ofMemo? source fullNode.queries #v[1, 1] memo 2).isSome &&
      (SelectedSigns.ofMemo? source firstNode.queries #v[-1] memo 0).isNone &&
      (SelectedSigns.ofMemo? source derivativeNode.queries #v[1] memo 0).isNone &&
      (SelectedSigns.ofMemo? source firstNode.queries #v[1] memo 3).isNone &&
      (SelectedSigns.readMemo? prefixed [DensePoly.C 2] #v[1] memo 2).isSome &&
      (SelectedSigns.readMemo? prefixed [DensePoly.C 2] #v[-1] memo 2).isNone &&
      (Dag.bindDomain? Sturm.orderSign 7 memo source.raw.head .negInf source.raw.upper).isNone
  | _, _ => false

/-- Compare literal trees through their injective shared encoding. -/
def sameEvidence (left right : Replay Rat Nat) : Bool :=
  let l := Dag.encode left
  let r := Dag.encode right
  l.entries == r.entries && l.root == r.root

open Hex.SignDet.Conformance Hex.SignDet.CrossCheck in
/-- Byte decoding retains supplied signs and literal replay; wrong values and
truncated bytes fail without rerunning a producer. -/
def graphBytesPasses : Bool :=
  match Descriptor.ofReplay? Sturm.orderSign 7 singletonRaw (.leaf singletonNode) with
  | none => false
  | some source =>
    let bytes := full.encodeBytes ValueCodec.rat ValueCodec.nat
    match full.selectedSigns? source fullNode.queries #v[1, 1],
        Dag.decodeSigns ValueCodec.rat ValueCodec.nat source fullNode.queries #v[1, 1] bytes with
    | some expected, .ok actual =>
      actual.values == #v[1, 1] && sameEvidence actual.evidence expected.evidence &&
        (Dag.decodeSigns ValueCodec.rat ValueCodec.nat source fullNode.queries
          #v[0, 1] bytes).toOption.isNone &&
        (Dag.decodeSigns ValueCodec.rat ValueCodec.nat source fullNode.queries #v[1, 1]
          (bytes.extract 0 (bytes.size - 2))).toOption.isNone
    | _, _ => false

open Hex.SignDet.Conformance in
/-- Replay of the producer's own encoded graph agrees with the producer,
including zero signs. -/
def graphProducedPasses : Bool :=
  let qs := [Sturm.Fixtures.x, Sturm.Fixtures.p, 0, 1, -1]
  match Descriptor.ofReplay? Sturm.orderSign 7 singletonRaw (.leaf singletonNode) with
  | none => false
  | some source =>
    match source.buildSigns qs with
    | .error _ => false
    | .ok original =>
      let graph := Dag.encode original.evidence
      match graph.selectedSigns? source qs original.values with
      | none => false
      | some replayed => replayed.values.toList == [1, 0, 0, 1, -1] &&
        sameEvidence replayed.evidence original.evidence

/-! ## Conversion -/

/-- A context-only conversion over the cubic field rebuilds child queries even
though head, bounds and word are identical; stale children reject. -/
def cubicContextPasses : Bool :=
  let raw := {raw with indices := [1, 2], signs := [1, 1]}
  match Descriptor.validate fieldSign 7 raw with
  | none => false
  | some source =>
    match source.convert id (fun _ => Iff.rfl) fieldSign 8 with
    | .ok (.ok target) =>
      let staleChildRejected := match source.evidence, target.evidence with
        | .split _ oldLeft _, .split node _ freshRight =>
          !target.raw.check fieldSign 8 (.split node oldLeft freshRight)
        | _, _ => false
      staleChildRejected &&
      target.raw.context == 8 && target.raw.head == source.raw.head &&
      target.raw.signs == source.raw.signs &&
      target.raw.check fieldSign 8 target.evidence &&
      !target.raw.check fieldSign 8 source.evidence &&
      !({source.raw with context := 8}).check fieldSign 8 source.evidence &&
      target.signAt (xPoly.natPow 3 - DensePoly.C 2) == 0 &&
      target.signAt (xPoly - 1) == 1
    | _ => false

/-- The rational constant embedding into the cubic field reflects zero. -/
theorem ofRat_eq_zero (q : Rat) : (PolyQuot.ofRat q : CubicField) = 0 ↔ q = 0 := by
  have hpos : 0 < (ZPoly.toRatPoly generator.p).natDegree := by
    simpa [DensePoly.natDegree, DensePoly.degree?, ZPoly.size_toRatPoly] using generator.x.posDegree
  have hdeg : (DensePoly.scale q (1 : DensePoly Rat)).natDegree = 0 := by
    have hs : (DensePoly.scale q (1 : DensePoly Rat)).size ≤ 1 := by
      rw [DensePoly.scale_eq_scaleImpl]
      exact Nat.le_trans (DensePoly.size_scaleImpl_le _ _) (DensePoly.size_C_le_one _)
    simp only [DensePoly.natDegree, DensePoly.degree?]
    split
    · rfl
    · simp only [Option.getD_some]; omega
  have hcoeffs : (PolyQuot.ofRat q : CubicField).coeffs = DensePoly.scale q 1 := by
    change PolyQuot.reduceCoeffs _ (DensePoly.scale q (1 : DensePoly Rat)) = _
    apply DensePoly.mod_eq_self_of_degree_lt
    omega
  constructor
  · intro h
    have h0 := congrArg (fun a : CubicField => a.coeffs.coeff 0) h
    simp only [hcoeffs] at h0
    rw [DensePoly.coeff_scale _ _ _ (Rat.mul_zero q)] at h0
    change q * (DensePoly.C (1 : Rat)).coeff 0 = (0 : DensePoly Rat).coeff 0 at h0
    rw [DensePoly.coeff_C] at h0
    simpa using h0
  · rintro rfl
    apply PolyQuot.ext
    rw [hcoeffs]
    exact DensePoly.scale_zero_left_semiring _

/-- A rational root descriptor (√2) moved into the cubic field compares with ∛2
by an ordinary selected sign. -/
def intoCubicPasses : Bool :=
  let raw : RawDescriptor Rat Nat :=
    ⟨7, DensePoly.ofList [-2, 0, 1], .finite 0, .posInf, [], []⟩
  match Descriptor.validate Sturm.orderSign 7 raw with
  | none => false
  | some source =>
    match source.convert PolyQuot.ofRat ofRat_eq_zero fieldSign 8 with
    | .ok (.ok target) =>
      target.raw.context == 8 && target.raw.signs.isEmpty &&
      target.raw.lower == .finite 0 && target.raw.upper == .posInf &&
      target.signAt (xPoly - DensePoly.C alpha) == 1 &&
      target.signAt (xPoly.natPow 2 - DensePoly.C 2) == 0
    | _ => false

/-- Rational negation reflects zero. -/
theorem neg_eq_zero (q : Rat) : -q = 0 ↔ q = 0 := by
  constructor
  · intro h
    simpa using congrArg Neg.neg h
  · intro h
    simp [h]

/-- A converter need not preserve order; reversed converted bounds are an
ordinary domain error. -/
def badConversionPasses : Bool :=
  let raw : RawDescriptor Rat Nat :=
    ⟨7, DensePoly.ofList [-2, 0, 1], .finite 1, .finite 2, [], []⟩
  match Descriptor.validate Sturm.orderSign 7 raw with
  | none => false
  | some source =>
    match source.convert (fun q => -q) neg_eq_zero Sturm.orderSign 8 with
    | .ok (.error .domain) => true
    | _ => false

/-- Rationalization merges different stored representations of one value,
keeps the partial word and builds fresh evidence in the new context. -/
def rationalizesPasses : Bool :=
  let x := HexPoly.InterpretTests.x
  let source : RawDescriptor HexPoly.InterpretTests.Rep Nat :=
    ⟨7, x * x - DensePoly.C HexPoly.InterpretTests.root, .negInf, .posInf, [1], [-1]⟩
  HexPoly.InterpretTests.root != (1 : HexPoly.InterpretTests.Rep) &&
  match Descriptor.validate Hex.TarskiTests.Noncanonical.sign 7 source with
  | none => false
  | some d =>
    match d.convert HexPoly.InterpretTests.value HexPoly.InterpretTests.value_eq_zero
        Sturm.orderSign 8 with
    | .ok (.ok target) =>
      target.raw.context == 8 &&
      target.raw.head == DensePoly.Interpret.map HexPoly.InterpretTests.value
        HexPoly.InterpretTests.value_eq_zero source.head &&
      target.raw.signs == source.signs &&
      target.raw.check Sturm.orderSign 8 target.evidence &&
      !({target.raw with context := 7}).check Sturm.orderSign 7 target.evidence &&
      target.signAt (DensePoly.ofList [-1, 1]) == -1 &&
      target.signAt (DensePoly.ofList [-1, 0, 1]) == 0
    | _ => false

/-! ## Driver -/

def checks : List (String × (Unit → Bool)) := [
  ("selected signs: derivative word, query order, stale bindings", fun _ => selectedPasses),
  ("selected signs: total signAt", fun _ => totalSignsPasses),
  ("completion: negative leading coefficient",
    fun _ => completesAs {positive with head := -positive.head, signs := [-1]} [-1, -1, -1]),
  ("completion: zero derivative sign",
    fun _ => completesAs {positive with indices := [1], signs := [-1]} [-1, 0, 1]),
  ("completion: empty partial word",
    fun _ => completesAs ⟨7, head, .finite 1, .finite 2, [], []⟩ [1, 1]),
  ("query handle: prepared signs and stale evidence", fun _ => preparedPasses),
  ("root list: three roots with zero derivative sign",
    fun _ => rootsAs fieldSign cubicHead .negInf .posInf [[1, -1, 1], [-1, 0, 1], [1, 1, 1]]),
  ("root list: nonzero constant has no roots",
    fun _ => rootsAs fieldSign (DensePoly.C (2 : CubicField)) .negInf .posInf []),
  ("root list: reversed bounds are an invalid domain",
    fun _ => invalidDomain head (.finite 2) (.finite 1)),
  ("root list: infinitesimal roots without rational separator",
    fun _ => infinitesimalRootsPasses),
  ("table: shared root query and absent words", fun _ => tablePasses),
  ("common field: table, roots, comparison, re-encoding", fun _ => commonFieldPasses),
  ("common field: nonreal generator rejected", fun _ => rejectsNonreal),
  ("re-encoding: target has only the other root",
    fun _ => absentAs raw (xPoly + DensePoly.C alpha) .negInf .posInf),
  ("re-encoding: restricted interval excludes the root",
    fun _ => absentAs raw head (.finite (-2)) (.finite 0)),
  ("re-encoding: non-squarefree target is absent",
    fun _ => absentAs raw ((xPoly - DensePoly.C alpha).natPow 2) .negInf .posInf false),
  ("re-encoding: failed source validation is not absence",
    fun _ => !absentAs {raw with signs := [0]} (DensePoly.C 2) .negInf .posInf),
  ("re-encoding: present target succeeds", fun _ => presentPasses),
  ("refinement: smaller interval with fresh evidence", fun _ => refinementPasses),
  ("refinement: infinitesimal-width interval", fun _ => infinitesimalRefinementPasses),
  ("thom: extra target root rejected only by source equation",
    fun _ => thomReencoded ((xPoly - DensePoly.C alpha) * (xPoly - 1)) [1, 1]),
  ("thom: other source root rejected only by old interval",
    fun _ => thomReencoded head [1, 1] false),
  ("noninjective storage: changed head re-encoding", fun _ => changedHeadPasses),
  ("comparison: shared root of different heads",
    fun _ => compares cubicPositive ⟨7, xPoly - DensePoly.C alpha, .negInf, .posInf, [1], [1]⟩ .eq),
  ("comparison: root at the other descriptor's endpoint",
    fun _ => compares cubicPositive
      ⟨7, (xPoly - DensePoly.C alpha) * (xPoly - DensePoly.C 2), .finite (3/2), .finite 3, [], []⟩ .lt),
  ("comparison: common product of zero, constant and shared factors",
    fun _ => commonProductPasses),
  ("graph signs: memo slots and rejections", fun _ => graphMemoPasses),
  ("graph signs: byte decoding and truncation", fun _ => graphBytesPasses),
  ("graph signs: replay agrees with producer", fun _ => graphProducedPasses),
  ("conversion: context change with stale child", fun _ => cubicContextPasses),
  ("conversion: rational descriptor into the cubic field", fun _ => intoCubicPasses),
  ("conversion: order-reversing converter reports domain error", fun _ => badConversionPasses),
  ("conversion: rationalize noninjective storage", fun _ => rationalizesPasses)]

end Hex.SignDet.FieldChecks

def main : IO UInt32 := do
  let checks := Hex.SignDet.FieldChecks.checks
  let mut failed := 0
  for (name, check) in checks do
    unless check () do
      IO.println s!"FAIL: {name}"
      failed := failed + 1
  IO.println s!"HexSignDet field checks: {checks.length - failed}/{checks.length} passed"
  return if failed == 0 then 0 else 1

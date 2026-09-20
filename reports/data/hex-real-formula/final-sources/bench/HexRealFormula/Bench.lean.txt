/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealFormula
import LeanBench

/-!
Compiled structural and exact-rational operations. Prepared inputs keep syntax,
monomial count, arity, coefficient bits and exponent ladders separate. Result
checksums traverse the entire output, at no higher order than each measured
operation. The harness consumes results through Hashable, outside operation-only
profile regions. All registrations use two-sided family-specific cost models.
-/

namespace Hex.RealFormula.Bench

private def hashCmp : Cmp → UInt64
  | .eq => 1 | .ne => 2 | .lt => 3 | .le => 4 | .gt => 5 | .ge => 6
private def hashPoly (p : Poly n) : UInt64 :=
  p.termsList.foldl (fun h t => mixHash h (mixHash (hash t.1.toList) (hash t.2))) 0
private def hashBody : Kernel.Body → UInt64
  | .atom p c => mixHash (hash p) (hashCmp c)
  | .tt => 11 | .ff => 12
  | .not p => mixHash 13 (hashBody p)
  | .and p q => mixHash 14 (mixHash (hashBody p) (hashBody q))
  | .or p q => mixHash 15 (mixHash (hashBody p) (hashBody q))
private def hashQF : QF n → UInt64
  | .atom a => mixHash (hashPoly a.p) (hashCmp a.cmp)
  | .tt => 11 | .ff => 12
  | .not p => mixHash 13 (hashQF p)
  | .and p q => mixHash 14 (mixHash (hashQF p) (hashQF q))
  | .or p q => mixHash 15 (mixHash (hashQF p) (hashQF q))
private def hashPrenex : Prenex n → UInt64
  | .matrix p => hashQF p
  | .quant q p => mixHash (if q == .existsReal then 16 else 17) (hashPrenex p)

instance : Hashable (Poly n) where hash := hashPoly
instance : Hashable (QF n) where hash := hashQF
instance : Hashable (Prenex n) where hash := hashPrenex
private def hashPrefix (qs : List Quantifier) : UInt64 :=
  hash (qs.map fun q => if q == .existsReal then (0 : Nat) else 1)
instance : Hashable (Prenex.View n) where
  hash p := mixHash (hashPrefix p.prefix) (hashQF p.matrix)
instance : Hashable Kernel.QF where
  hash p := mixHash (mixHash (hash p.version) (hash p.arity)) (hashBody p.body)
instance : Hashable Kernel.Prenex where
  hash p := mixHash (mixHash (hash p.freeArity) (hashPrefix p.prefix)) (hash p.matrix)
instance : Hashable Kernel.Dag where hash p := hash (reprStr p)

private def atom : QF 2 := .atom ⟨MvPoly.X 0 ^ 2 + MvPoly.X 1 + MvPoly.C 1, .gt⟩
def prepTree : Nat → QF 2
  | 0 => .tt
  | n + 1 => .and atom (.not (.not (prepTree n)))
private def point (i : Fin 2) : Rat := if i == 0 then 1/2 else 1/3

def nodes (p : QF 2) := p.nodeCount
def polys (p : QF 2) := p.polys
def support (p : QF 2) := p.support
def degree (p : QF 2) := p.degree 0
def nnf (p : QF 2) := p.nnf
def rename (p : QF 2) := p.rename fun i => if i == 0 then (1 : Fin 2) else 0
def lift (p : QF 2) := p.lift
def prepDrop (n : Nat) : QF 3 := (prepTree n).lift
def drop (p : QF 3) := p.drop? 2
def move (p : QF 2) := p.moveLast 0
def encode (p : QF 2) := p.toKernel
def prepKernel (n : Nat) := (prepTree n).toKernel
def decode (p : Kernel.QF) := (QF.ofKernel? p : Option (QF 2))
def evaluate (p : QF 2) := p.evalRat point
def evaluateKernel (p : Kernel.QF) := p.body.evalRat [1/2, 1/3]
def implication (p : QF 2) := p.imp p
def biconditional (p : QF 2) := p.iff p
private def negations : Nat → QF 0 → QF 0
  | 0, p => p
  | n + 1, p => .not (negations n p)
def prepEquality (n : Nat) := (negations n .tt, negations n .ff)
def equality (p : QF 0 × QF 0) := p.1 == p.2

def validate (p : Kernel.QF) := p.validate.isSome
private def prefixBool : (k n : Nat) → Bool → Prenex n
  | 0, _, b => .matrix (if b then .tt else .ff)
  | k + 1, n, b => .quant .existsReal (prefixBool k (n + 1) b)
def prepPrefixEquality (n : Nat) := (prefixBool n 1 true, prefixBool n 1 false)
def prefixEquality (p : Prenex 1 × Prenex 1) := p.1 == p.2

private def makePrefix : (k n : Nat) → Prenex n
  | 0, _ => .matrix (.atom ⟨MvPoly.C 1, .gt⟩)
  | k + 1, n => .quant .existsReal (makePrefix k (n + 1))
def prepPrefix (n : Nat) := makePrefix n 1
def prefixNodes (p : Prenex 1) := p.nodeCount
def view (p : Prenex 1) :=
  p.toView
def prepView (n : Nat) := (prepPrefix n).toView
def ofView (p : Prenex.View 1) := Prenex.ofView p
def prefixRename (p : Prenex 1) := p.rename fun _ => (1 : Fin 2)
def swap (p : Prenex 1) := p.swap? 0
def prefixEncode (p : Prenex 1) :=
  p.toKernel
def prepPrefixKernel (n : Nat) := (prepPrefix n).toKernel
def prefixDecode (p : Kernel.Prenex) := (Prenex.ofKernel? p : Option (Prenex 1))

def prepTerms (n : Nat) : QF 2 := .atom ⟨MvPoly.ofTerms ((List.range n).map fun i =>
  (⟨#[i % 32, i / 32], by rfl⟩, (1 : Int))), .gt⟩
def evalTerms (p : QF 2) := p.evalRat (fun _ => 1)
def renameTerms (p : QF 2) := p.rename fun i => if i == 0 then (1 : Fin 2) else 0
def prepRawTerms (n : Nat) : Kernel.QF :=
  ⟨1, 2, .atom ((List.range n).map fun i => ([i / 64, i % 64], (1 : Int))) .gt⟩
def decodeTerms (p : Kernel.QF) := decode p

structure ArityInput where
  n : Nat
  formula : QF n

instance : Hashable ArityInput where
  hash p := mixHash (hash p.n) (hashQF p.formula)

def prepArity (n : Nat) : ArityInput :=
  ⟨n, .atom ⟨MvPoly.monomial (Vector.replicate n 1) 3, .gt⟩⟩
def evalArity (p : ArityInput) := p.formula.evalRat (fun _ => 1)
def supportArity (p : ArityInput) := p.formula.support.map (·.val)
def renameArity (p : ArityInput) := p.formula.rename (fun _ => (0 : Fin 1))

def prepBits (n : Nat) : QF 1 := .atom ⟨MvPoly.C (Int.ofNat (2 ^ n + 1)) * MvPoly.X 0, .gt⟩
def evalBits (p : QF 1) := p.evalRat (fun _ => 3/2)
def prepExponent (n : Nat) : QF 1 := .atom ⟨MvPoly.monomial (Vector.replicate 1 n) 3, .gt⟩
def evalExponent (p : QF 1) := p.evalRat (fun _ => 1)

def prepDag (n : Nat) : Kernel.Dag :=
  ⟨1, 0, #[.tt] ++ (Array.range n).map (fun i => .and 0 i), n⟩
def dag (p : Kernel.Dag) := (p.decode #[]).map QF.toKernel

/- There are 4*n+1 syntax nodes and fixed-size atom polynomials. Traversal and the complete result checksum are linear in n; Boolean evaluation visits every conjunct. -/
setup_benchmark nodes n => n with prep := prepTree
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are 4*n+1 syntax nodes and fixed-size atom polynomials. Traversal and the complete result checksum are linear in n; Boolean evaluation visits every conjunct. -/
setup_benchmark polys n => n with prep := prepTree
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are 4*n+1 syntax nodes and fixed-size atom polynomials. Traversal and the complete result checksum are linear in n; Boolean evaluation visits every conjunct. -/
setup_benchmark support n => n with prep := prepTree
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are 4*n+1 syntax nodes and fixed-size atom polynomials. Traversal and the complete result checksum are linear in n; Boolean evaluation visits every conjunct. -/
setup_benchmark degree n => n with prep := prepTree
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are 4*n+1 syntax nodes and fixed-size atom polynomials. Traversal and the complete result checksum are linear in n; Boolean evaluation visits every conjunct. -/
setup_benchmark nnf n => n with prep := prepTree
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are 4*n+1 syntax nodes and fixed-size atom polynomials. Traversal and the complete result checksum are linear in n; Boolean evaluation visits every conjunct. -/
setup_benchmark rename n => n with prep := prepTree
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are 4*n+1 syntax nodes and fixed-size atom polynomials. Traversal and the complete result checksum are linear in n; Boolean evaluation visits every conjunct. -/
setup_benchmark lift n => n with prep := prepTree
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are 4*n+1 syntax nodes and fixed-size atom polynomials. Traversal and the complete result checksum are linear in n; Boolean evaluation visits every conjunct. -/
setup_benchmark move n => n with prep := prepTree
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are 4*n+1 syntax nodes and fixed-size atom polynomials. Traversal and the complete result checksum are linear in n; Boolean evaluation visits every conjunct. -/
setup_benchmark encode n => n with prep := prepTree
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are 4*n+1 syntax nodes and fixed-size atom polynomials. Traversal and the complete result checksum are linear in n; Boolean evaluation visits every conjunct. -/
setup_benchmark evaluate n => n with prep := prepTree
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are 4*n+1 syntax nodes and fixed-size atom polynomials. Traversal and the complete result checksum are linear in n; Boolean evaluation visits every conjunct. -/
setup_benchmark implication n => n with prep := prepTree
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are 4*n+1 syntax nodes and fixed-size atom polynomials. Traversal and the complete result checksum are linear in n; Boolean evaluation visits every conjunct. -/
setup_benchmark biconditional n => n with prep := prepTree
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- Each of n syntax steps has constant arity and bounded polynomial work. Equality differs at the deepest leaf; checked decode visits all nodes. Result consumption adds at most one linear traversal. -/
setup_benchmark drop n => n with prep := prepDrop
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- Each of n syntax steps has constant arity and bounded polynomial work. Equality differs at the deepest leaf; checked decode visits all nodes. Result consumption adds at most one linear traversal. -/
setup_benchmark decode n => n with prep := prepKernel
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- Each of n syntax steps has constant arity and bounded polynomial work. Equality differs at the deepest leaf; checked decode visits all nodes. Result consumption adds at most one linear traversal. -/
setup_benchmark evaluateKernel n => n with prep := prepKernel
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- Each of n syntax steps has constant arity and bounded polynomial work. Equality differs at the deepest leaf; checked decode visits all nodes. Result consumption adds at most one linear traversal. -/
setup_benchmark equality n => n with prep := prepEquality
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are n quantifiers and one constant atom whose exponent vector has length n+1. Prefix traversal, coordinate transport and complete result hashing take linear work. -/
setup_benchmark prefixNodes n => n with prep := prepPrefix
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are n quantifiers and one constant atom whose exponent vector has length n+1. Prefix traversal, coordinate transport and complete result hashing take linear work. -/
setup_benchmark view n => n with prep := prepPrefix
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are n quantifiers and one constant atom whose exponent vector has length n+1. Prefix traversal, coordinate transport and complete result hashing take linear work. -/
setup_benchmark ofView n => n with prep := prepView
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are n quantifiers and one constant atom whose exponent vector has length n+1. Prefix traversal, coordinate transport and complete result hashing take linear work. -/
setup_benchmark prefixRename n => n with prep := prepPrefix
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are n quantifiers and one constant atom whose exponent vector has length n+1. Prefix traversal, coordinate transport and complete result hashing take linear work. -/
setup_benchmark swap n => n with prep := prepPrefix
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are n quantifiers and one constant atom whose exponent vector has length n+1. Prefix traversal, coordinate transport and complete result hashing take linear work. -/
setup_benchmark prefixEncode n => n with prep := prepPrefix
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- There are n quantifiers and one constant atom whose exponent vector has length n+1. Prefix traversal, coordinate transport and complete result hashing take linear work. -/
setup_benchmark prefixDecode n => n with prep := prepPrefixKernel
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- The atom contains n distinct terms in a fixed two-coordinate grid. Exponents are bounded by 31, and evaluation at (1,1) keeps every intermediate integer within one word. Thus evaluation visits n bounded-cost terms. -/
setup_benchmark evalTerms n => n with prep := prepTerms
  where {
    paramSchedule := .custom #[32, 64, 128, 256, 512, 1024]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- A coordinate permutation preserves n distinct terms of bounded exponent and coefficient size. Each term is inserted into a balanced map in logarithmic time; hashing the output is linear. -/
setup_benchmark renameTerms n => n * Nat.log2 (n + 1) with prep := prepTerms
  where {
    paramSchedule := .custom #[32, 64, 128, 256, 512, 1024]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- The raw grid has bounded exponents (at most 127) and fixed coefficients. Ascending raw terms force insertion normalization to traverse every existing suffix. This is quadratic in n; subsequent balanced-tree reconstruction and output hashing cost O(n log n) and O(n). -/
setup_benchmark decodeTerms n => n * n with prep := prepRawTerms
  where {
    paramSchedule := .custom #[256, 512, 1024, 2048, 4096, 8192]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- One monomial has n coordinates of exponent one. At the all-one valuation, rational intermediates have bounded size and the monomial product visits every coordinate. -/
setup_benchmark evalArity n => n with prep := prepArity
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- The single-term atom has every coordinate present. Each degree query reads one vector entry; producing and hashing the n-element support takes linear work. -/
setup_benchmark supportArity n => n with prep := prepArity
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- All n source coordinates map to one target coordinate. Accumulating n unit exponents is linear and normalization inserts just one term. The result checksum is constant-size. -/
setup_benchmark renameArity n => n with prep := prepArity
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- A single n-bit odd coefficient is multiplied by the fixed rational 3/2. Small-integer multiplication and denominator handling traverse a linear number of limbs; comparison does not require a growing result checksum. -/
setup_benchmark evalBits n => n with prep := prepBits
  where {
    paramSchedule := .custom #[65536, 131072, 262144, 524288, 1048576, 2097152]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- Binary powering at the exact rational point 1 performs logarithmically many constant-size rational multiplications. This isolates exponent traversal; the coefficient-bit ladder separately tests growing arithmetic operands. -/
setup_benchmark evalExponent n => Nat.log2 (n + 1) with prep := prepExponent
  where {
    paramSchedule := .custom #[256, 65536, 16777216, 4294967296, 1099511627776, 281474976710656]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- The DAG has n+1 nodes, and its expanded tree has 2*n+1 nodes. Decode checks every reference and constructs one syntax node per DAG node; complete expanded-tree hashing remains linear. -/
setup_benchmark dag n => n with prep := prepDag
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- Every raw syntax node and exponent-vector length is checked, including
unused branches. The fixed-arity, fixed-term family makes this linear. -/
setup_benchmark validate n => n with prep := prepKernel
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

/- Two prefixes differ only at the final matrix truth value, forcing all n
binder comparisons. The output is one Boolean. -/
setup_benchmark prefixEquality n => n with prep := prepPrefixEquality
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 4
    maxSecondsPerCall := 4.0
  }

end Hex.RealFormula.Bench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args

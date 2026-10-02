/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Structural
public import HexMvPoly.Recursive
public import HexMvPoly.Query
public import Init.GrindInstances.Ring.Rat

@[expose] public section

/-! Polynomial comparisons and formulas with explicit finite coordinate sets. -/

namespace Hex.RealFormula

/-- Integer polynomials in the fixed lexicographic monomial order. -/
abbrev Poly (n : Nat) := MvPoly n Int Mono.lex

/-- Comparison with zero. -/
inductive Cmp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, BEq, Repr

/-- Logical complement, including the boundary point. -/
def Cmp.complement : Cmp → Cmp
  | .eq => .ne | .ne => .eq | .lt => .ge
  | .le => .gt | .gt => .le | .ge => .lt

/-- An exact rational comparison. -/
def Cmp.evalRat (c : Cmp) (x : Rat) : Bool :=
  match c with
  | .eq => x == 0 | .ne => x != 0
  | .lt => x < 0 | .le => x ≤ 0 | .gt => x > 0 | .ge => x ≥ 0

/-- An atom compares its normalized polynomial with zero. -/
structure Atom (n : Nat) where
  p : Poly n
  cmp : Cmp
  deriving DecidableEq, BEq

/-- Quantifier-free Boolean syntax. Negation is permitted at every node. -/
inductive QF (n : Nat) where
  | atom (a : Atom n)
  | tt | ff
  | not (p : QF n)
  | and (p q : QF n)
  | or (p q : QF n)
  deriving DecidableEq, BEq

namespace QF

/-- Number of nodes in the expanded syntax tree. -/
def nodeCount : QF n → Nat
  | .atom _ | .tt | .ff => 1
  | .not p => 1 + p.nodeCount
  | .and p q | .or p q => 1 + p.nodeCount + q.nodeCount

/-- Transform every polynomial, preserving Boolean structure. -/
def map (f : Poly n → Poly m) : QF n → QF m
  | .atom a => .atom ⟨f a.p, a.cmp⟩
  | .tt => .tt | .ff => .ff
  | .not p => .not (map f p)
  | .and p q => .and (map f p) (map f q)
  | .or p q => .or (map f p) (map f q)

/-- Polynomials in left-to-right atom order, retaining repeated atoms. -/
def polys (p : QF n) : List (Poly n) := go p [] where
  go : QF n → List (Poly n) → List (Poly n)
    | .atom a, tail => a.p :: tail
    | .tt, tail | .ff, tail => tail
    | .not p, tail => go p tail
    | .and p q, tail | .or p q, tail => go p (go q tail)

/-- Maximum normalized exponent of the selected coordinate. -/
def degree (i : Fin n) : QF n → Nat
  | .atom a => a.p.degreeOf i
  | .tt | .ff => 0
  | .not p => p.degree i
  | .and p q | .or p q => max (p.degree i) (q.degree i)

/-- Coordinates occurring in a normalized atom, in coordinate order. -/
def support (p : QF n) : List (Fin n) :=
  (List.finRange n).filter fun i => p.degree i != 0

/-- Coordinate substitution. Colliding coordinates combine exponents and terms. -/
def rename (σ : Fin n → Fin m) : QF n → QF m :=
  map (MvPoly.rename Mono.lex σ)

/-- Exchange two valid coordinates, fixing every other coordinate. -/
def exchange (i j k : Fin n) : Fin n :=
  if k = i then j else if k = j then i else k

theorem exchange_involutive (i j k : Fin n) : exchange i j (exchange i j k) = k := by
  by_cases hi : k = i
  · subst k; by_cases hij : i = j <;> simp [exchange, hij, eq_comm]
  · by_cases hj : k = j
    · subst k; simp [exchange, hi]
    · simp [exchange, hi, hj]

/-- Move the selected coordinate to the last slot by a checked transposition. -/
def moveLast (i : Fin (n + 1)) : QF (n + 1) → QF (n + 1) :=
  rename (exchange i ⟨n, Nat.lt_succ_self n⟩)

/-- External coordinate selection rejects out-of-range identifiers. -/
def moveLast? (i : Nat) (p : QF (n + 1)) : Option (QF (n + 1)) :=
  if h : i < n + 1 then some (p.moveLast ⟨i, h⟩) else none

/-- Append an unused last coordinate. -/
def lift : QF n → QF (n + 1) := rename Fin.castSucc

/-- Remove a coordinate known absent from every normalized atom. -/
def drop (i : Fin (n + 1)) (p : QF (n + 1)) (_h : p.degree i = 0) : QF n :=
  p.map fun a => MvPoly.ofTerms
    (a.termsList.map fun (m, c) => (MvPoly.removeVar i m, c))

/-- Checked coordinate removal. -/
def drop? (i : Fin (n + 1)) (p : QF (n + 1)) : Option (QF n) :=
  if h : p.degree i = 0 then some (p.drop i h) else none

/-- Push a polarity through Boolean syntax, complementing atom comparisons. -/
def nnfWith (neg : Bool) : QF n → QF n
  | .atom a => .atom ⟨a.p, if neg then a.cmp.complement else a.cmp⟩
  | .tt => if neg then .ff else .tt
  | .ff => if neg then .tt else .ff
  | .not p => nnfWith (!neg) p
  | .and p q => if neg then .or (nnfWith neg p) (nnfWith neg q)
      else .and (nnfWith neg p) (nnfWith neg q)
  | .or p q => if neg then .and (nnfWith neg p) (nnfWith neg q)
      else .or (nnfWith neg p) (nnfWith neg q)

/-- Negation normal form, with no negation nodes. -/
def nnf (p : QF n) : QF n := nnfWith false p

/-- Expand implication before polarity normalization. -/
def imp (p q : QF n) : QF n := .or (.not p) q

/-- Expand biconditional into Boolean connectives. -/
def iff (p q : QF n) : QF n := .and (p.imp q) (q.imp p)

/-- Exact rational evaluation, without quantifying over rationals. -/
def evalRat (p : QF n) (ρ : Fin n → Rat) : Bool :=
  match p with
  | .atom a => a.cmp.evalRat (MvPoly.eval₂ (fun (z : Int) => (z : Rat)) ρ a.p)
  | .tt => true | .ff => false
  | .not p => !p.evalRat ρ
  | .and p q => p.evalRat ρ && q.evalRat ρ
  | .or p q => p.evalRat ρ || q.evalRat ρ

end QF

/-- Real quantifier kinds. -/
inductive Quantifier where
  | existsReal | forallReal
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- A prefix extends the free valuation one last coordinate at a time. -/
inductive Prenex : Nat → Type where
  | matrix (p : QF n) : Prenex n
  | quant (q : Quantifier) (p : Prenex (n + 1)) : Prenex n
  deriving DecidableEq, BEq

/-- A formula with no free parameters. -/
abbrev Sentence := Prenex 0

/-- Number of quantifier and matrix nodes. -/
def Prenex.nodeCount : Prenex n → Nat
  | .matrix p => p.nodeCount
  | .quant _ p => 1 + p.nodeCount

/-- Extend a source-to-target map, fixing the newly appended binder. -/
def extend (σ : Fin n → Fin m) (i : Fin (n + 1)) : Fin (m + 1) :=
  if h : i.val < n then (σ ⟨i.val, h⟩).castSucc else ⟨m, Nat.lt_succ_self m⟩

/-- Rename free coordinates without changing the order or identity of binders. -/
def Prenex.rename (σ : Fin n → Fin m) : Prenex n → Prenex m
  | .matrix p => .matrix (p.rename σ)
  | .quant q p => .quant q (p.rename (extend σ))

/-- A finite coordinate map with constant-time lookup and checked range. -/
structure IndexMap (n m : Nat) where
  indices : Array Nat
  size : indices.size = n
  bounds : ∀ i (h : i < indices.size), indices[i] < m

def IndexMap.get (σ : IndexMap n m) (i : Fin n) : Fin m :=
  ⟨σ.indices[i.val]'(by rw [σ.size]; exact i.isLt),
    σ.bounds i.val (by rw [σ.size]; exact i.isLt)⟩

def IndexMap.push (σ : IndexMap n m) : IndexMap (n + 1) (m + 1) :=
  { indices := σ.indices.push m
    size := by simp [σ.size]
    bounds := by
      intro i hi
      by_cases h : i < σ.indices.size
      · simpa [Array.getElem_push_lt h] using Nat.lt_succ_of_lt (σ.bounds i h)
      · have he : i = σ.indices.size := by simp only [Array.size_push] at hi; omega
        subst i
        simp }

theorem IndexMap.get_push (σ : IndexMap n m) : σ.push.get = extend σ.get := by
  funext i
  have hs := σ.size
  apply Fin.ext
  simp only [IndexMap.get, IndexMap.push, extend]
  split
  next h => simp [Array.getElem_push_lt (show i.val < σ.indices.size by omega)]
  next h =>
    have hi : i.val = σ.indices.size := by omega
    simp [hi]

def IndexMap.ofFn (σ : Fin n → Fin m) : IndexMap n m :=
  { indices := Array.ofFn fun i => (σ i).val
    size := by simp
    bounds := by intro i hi; simp only [Array.getElem_ofFn]; exact (σ ⟨i, by simpa using hi⟩).isLt }

theorem IndexMap.get_ofFn (σ : Fin n → Fin m) : (IndexMap.ofFn σ).get = σ := by
  funext i
  apply Fin.ext
  simp [IndexMap.ofFn, IndexMap.get]

/-- Compile prefix renaming using a table extended once at each binder. -/
def Prenex.renameFast (σ : Fin n → Fin m) (p : Prenex n) : Prenex m :=
  go (IndexMap.ofFn σ) p
where
  go {n m : Nat} (σ : IndexMap n m) : Prenex n → Prenex m
    | .matrix p => .matrix (p.rename σ.get)
    | .quant q p => .quant q (go σ.push p)

theorem Prenex.renameFast.go_correct (σ : IndexMap n m) (p : Prenex n) :
    renameFast.go σ p = p.rename σ.get := by
  induction p generalizing m with
  | matrix p => rfl
  | quant q p ih => simp only [renameFast.go, rename, ih, IndexMap.get_push]

@[csimp] theorem Prenex.rename_eq_fast : @Prenex.rename = @Prenex.renameFast := by
  funext n m σ p
  simp only [renameFast, renameFast.go_correct, IndexMap.get_ofFn]

end Hex.RealFormula

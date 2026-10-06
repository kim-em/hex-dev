/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly

@[expose] public section

/-! Canonical sorted-list proxy used by the native orientation comparator. -/

namespace Hex.MvPolyBench
open Hex Hex.MvPoly

namespace Sorted

/-- Native-comparator canonical sorted-list representation. Operations below
are the only constructors used by the comparator, and maintain increasing
comparator order while removing zero coefficients. -/
structure Poly (n : Nat) (R : Type)
    (cmp : Mono n → Mono n → Ordering := Mono.lex) where
  terms : List (Mono n × R)
  deriving BEq

variable {cmp : Mono n → Mono n → Ordering}

/-- Merge two increasing canonical term lists, combining equal monomials.

The worker is structurally recursive on fuel rather than using a generated
well-founded recursion theorem. The public entry point supplies exactly the
sum of the input lengths, so the exhausted-fuel branch is unreachable for
canonical calls.
-/
def merge [Zero R] [Add R] [DecidableEq R]
    (cmp : Mono n → Mono n → Ordering := Mono.lex)
    (left right : List (Mono n × R)) : List (Mono n × R) :=
  go (left.length + right.length) left right
where
  go : Nat → List (Mono n × R) → List (Mono n × R) → List (Mono n × R)
    | _, [], ys => ys
    | _, xs, [] => xs
    | 0, xs, ys => xs ++ ys
    | fuel + 1, x :: xs, y :: ys =>
        match cmp x.1 y.1 with
        | .lt => x :: go fuel xs (y :: ys)
        | .gt => y :: go fuel (x :: xs) ys
        | .eq =>
            let coefficient := x.2 + y.2
            if coefficient = 0 then go fuel xs ys
            else (x.1, coefficient) :: go fuel xs ys

/-- Insert one term through the same merge path used by addition. -/
def insert [Zero R] [Add R] [DecidableEq R]
    (cmp : Mono n → Mono n → Ordering := Mono.lex)
    (terms : List (Mono n × R)) (term : Mono n × R) :
    List (Mono n × R) :=
  if term.2 = 0 then terms else merge cmp terms [term]

/-- Canonicalize an arbitrary term stream by repeated insertion. -/
def ofTerms [Zero R] [Add R] [DecidableEq R]
    (terms : List (Mono n × R))
    (cmp : Mono n → Mono n → Ordering := Mono.lex) : Poly n R cmp :=
  ⟨terms.foldl (insert cmp) []⟩

/-- Whether a term stream has strictly increasing, hence distinct, keys. -/
def strictlyOrdered
    (cmp : Mono n → Mono n → Ordering := Mono.lex) :
    List (Mono n × R) → Bool
  | [] | [_] => true
  | first :: second :: rest =>
      cmp first.1 second.1 == .lt &&
        strictlyOrdered cmp (second :: rest)

/-- Use the linear construction path for an already sorted term stream.

Zero coefficients are discarded first. A checked fallback through `ofTerms`
keeps the proxy canonical if a benchmark corpus ever violates its advertised
strict-order precondition. -/
def ofSortedTerms [Zero R] [Add R] [DecidableEq R]
    (terms : List (Mono n × R))
    (cmp : Mono n → Mono n → Ordering := Mono.lex) : Poly n R cmp :=
  let filtered := terms.filter fun term => term.2 != 0
  if strictlyOrdered cmp filtered then
    ⟨filtered⟩
  else
    ofTerms filtered cmp

instance [Zero R] : Zero (Poly n R cmp) where
  zero := ⟨[]⟩

/-- Single-pass canonical sparse addition. -/
def add [Zero R] [Add R] [DecidableEq R]
    (p q : Poly n R cmp) : Poly n R cmp :=
  ⟨merge cmp p.terms q.terms⟩

instance [Zero R] [Add R] [DecidableEq R] : Add (Poly n R cmp) where
  add := add

/-- Negate coefficients without changing the ordered support. -/
def neg [Neg R] (p : Poly n R cmp) : Poly n R cmp :=
  ⟨p.terms.map fun term => (term.1, -term.2)⟩

instance [Neg R] : Neg (Poly n R cmp) where
  neg := neg

/-- Sparse subtraction through merge addition. -/
def sub [Zero R] [Add R] [Neg R] [DecidableEq R]
    (p q : Poly n R cmp) : Poly n R cmp :=
  add p (neg q)

instance [Zero R] [Add R] [Neg R] [DecidableEq R] :
    Sub (Poly n R cmp) where
  sub := sub

/-- Merge adjacent translated rows once. -/
def mergeRound [Zero R] [Add R] [DecidableEq R]
    (cmp : Mono n → Mono n → Ordering := Mono.lex) :
    List (List (Mono n × R)) → List (List (Mono n × R))
  | [] => []
  | [row] => [row]
  | first :: second :: rest =>
      merge cmp first second :: mergeRound cmp rest

/-- Repeated balanced merge rounds. The fuel is initialized to the row count;
each nontrivial round at least halves that count. -/
def mergeRows [Zero R] [Add R] [DecidableEq R]
    (cmp : Mono n → Mono n → Ordering := Mono.lex) :
    Nat → List (List (Mono n × R)) → List (Mono n × R)
  | _, [] => []
  | _, [row] => row
  | 0, rows => rows.foldl (merge cmp) []
  | fuel + 1, rows => mergeRows cmp fuel (mergeRound cmp rows)

/-- Produce sorted translated rows and combine them in balanced merge rounds.
Translation preserves row order because `cmp` is a monomial order. -/
def mul [Zero R] [Add R] [Mul R] [DecidableEq R] [IsMonomialOrder cmp]
    (p q : Poly n R cmp) : Poly n R cmp :=
  let rows :=
    p.terms.map fun left =>
      q.terms.map fun right =>
        (Mono.mul left.1 right.1, left.2 * right.2)
  ⟨mergeRows cmp rows.length rows⟩

instance [Zero R] [Add R] [Mul R] [DecidableEq R] [IsMonomialOrder cmp] :
    Mul (Poly n R cmp) where
  mul := mul

/-- Rename variables, canonicalizing collisions. -/
def rename [Zero R] [Add R] [DecidableEq R]
    (f : Fin n → Fin k) (p : Poly n R cmp)
    (targetCmp : Mono k → Mono k → Ordering := Mono.lex) : Poly k R targetCmp :=
  ofTerms (p.terms.map fun term => (Mono.rename f term.1, term.2)) targetCmp

end Sorted

end Hex.MvPolyBench

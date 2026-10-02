/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Evidence

public section

namespace Hex.SignDet.Codec
open Lean

/-- Row, column and count order is serialized literally. Integer matrix
identities remain the independent checker's responsibility. -/
def system (s : System n) : Json :=
  .arr #[toJson s.rows.toArray, toJson s.columns.toArray, toJson s.counts.toArray,
    toJson s.values.toArray, encodeMatrix s.inverse, toJson s.denominator]

def readSystem (n arity : Nat) (j : Json) : Except String (System n) := do
  let a ← tuple 6 j
  let rows ← vector n (fun j => Vector.toList <$> vector arity (fromJson? (α := Nat)) j) a[0]
  let columns ← vector n (fun j => Vector.toList <$> vector arity (fromJson? (α := Int)) j) a[1]
  return ⟨rows, columns, ← vector n fromJson? a[2], ← vector n fromJson? a[3],
    ← matrix n n a[4], ← fromJson? a[5]⟩

def basis (b : Matrix.RankCert Int n m) : Json :=
  .arr #[toJson b.rank, toJson (b.rows.toArray.map Fin.val), toJson (b.cols.toArray.map Fin.val),
    toJson b.denom, encodeMatrix b.adj]

/-- Selected indices are checked against the decoded matrix dimensions before
constructing `Fin` values. No rank or nonsingularity claim is assumed. -/
def readBasis (n m : Nat) (j : Json) : Except String (Matrix.RankCert Int n m) := do
  let a ← tuple 5 j
  let rank ← fromJson? (α := Nat) a[0]
  if rank > n || rank > m then throw "rank exceeds matrix dimensions"
  return ⟨rank, ← vector rank (index n) a[1], ← vector rank (index m) a[2],
    ← fromJson? a[3], ← matrix rank rank a[4]⟩

variable {E Ctx : Type} [Zero E] [DecidableEq E]

def node (value : ValueCodec E) (context : ValueCodec Ctx) (n : Node E Ctx) : Json :=
  .arr #[context.encode n.context, poly value n.head, endpoint value n.lower,
    endpoint value n.upper, list (poly value) n.queries, toJson n.size, system n.system,
    array (tarski value context) n.moments.toArray,
    array (option (reduction value)) n.reductions.toArray,
    option (preparation value) n.preparation, basis n.basis]

/-- Decode all size-indexed fields against the same declared size. The rank
column dimension is computed from the literal integer counts, not supplied
as a separate unbound claim. -/
def readNode (value : ValueCodec E) (context : ValueCodec Ctx) (j : Json) :
    Except String (Node E Ctx) := do
  let a ← tuple 11 j
  let ctx ← context.decode a[0]
  let head ← readPoly value a[1]
  let lower ← readEndpoint value a[2]
  let upper ← readEndpoint value a[3]
  let queries ← readList (readPoly value) a[4]
  let size ← fromJson? (α := Nat) a[5]
  let system ← readSystem size queries.length a[6]
  return ⟨ctx, head, lower, upper, queries, size, system,
    ← vector size (readTarski value context) a[7],
    ← vector size (readOption (readReduction value queries.length)) a[8],
    ← readOption (readPreparation value queries.length) a[9],
    ← readBasis size system.positive.length a[10]⟩

/-- Both node and child query certificates retain the caller's full literal
context and root domain. Equal meanings or context hashes are insufficient. -/
def bindings [DecidableEq Ctx] (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (n : Node E Ctx) : Bool :=
  decide (n.context = context ∧ n.head = p ∧ n.lower = a ∧ n.upper = b) &&
    n.moments.toList.all fun c =>
      decide (c.context = context ∧ c.head = p ∧ c.lower = a ∧ c.upper = b)

end Hex.SignDet.Codec

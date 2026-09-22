/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Support
public import HexSignDet.MomentReplay
public import HexSignDet.QueryReduction

public section

/-! Finite recursive BKR replay with direct or reduced moments. Every recursion edge
checks the exact query positions, domain and full caller-supplied context.
This checker does not produce certificates or assert root-sum semantics. -/
namespace Hex.SignDet

open scoped Hex

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]

/-- One node's literal system, query replays and retained row basis. Sizes and
indices are intrinsic; a serialization reader must validate them on decoding. -/
structure Node (E : Type u) (Ctx : Type v) [Zero E] [DecidableEq E] where
  context : Ctx
  head : DensePoly E
  lower : Endpoint E
  upper : Endpoint E
  queries : List (DensePoly E)
  size : Nat
  system : System size
  moments : Vector (TarskiCertificate E E Ctx) size
  reductions : Vector (Option (Reduction E)) size := Vector.replicate size none
  preparation : Option (QueryReduction E) := none
  basis : Matrix.RankCert Int size system.positive.length

/-- Compare literal context and ordinary fields before computing support
lengths. Natural-number decisions then align dependent rank witnesses while
keeping the complete equality decision reducible in the ordinary kernel. -/
instance [DecidableEq Ctx] : DecidableEq (Node E Ctx) := by
  intro a b
  cases a with
  | mk ca pa la ua qa na sa ma ra da ba =>
    cases b with
    | mk cb pb lb ub qb nb sb mb rb db bb =>
      by_cases h : na = nb
      · subst nb
        by_cases hf : ca = cb ∧ pa = pb ∧ la = lb ∧ ua = ub ∧ qa = qb ∧
            sa = sb ∧ ma = mb ∧ ra = rb ∧ da = db
        · by_cases hl : sa.positive.length = sb.positive.length
          · let basis : Matrix.RankCert Int na sb.positive.length := hl ▸ ba
            exact decidable_of_iff (basis = bb) (by
              constructor
              · intro hb
                rcases hf with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                simpa [basis, Node.mk.injEq, heq_eq_eq] using hb
              · intro he
                cases he
                simp [basis])
          · exact isFalse fun he => hl (by cases he; rfl)
        · exact isFalse fun he => hf (by cases he; simp)

      · exact isFalse fun he => h (by cases he; rfl)

/-- Retained independent rows in the order certified by HexRank. -/
@[expose] def Node.rows (n : Node E Ctx) : List (List Nat) :=
  n.basis.rows.toList.map fun i => n.system.rows[i]

/-- A finite tree. There is no constructor for omitted or unproved children. -/
inductive Replay (E : Type u) (Ctx : Type v) [Zero E] [DecidableEq E] where
  | leaf (node : Node E Ctx)
  | split (node : Node E Ctx) (left right : Replay E Ctx)

@[expose] def Replay.node : Replay E Ctx → Node E Ctx
  | .leaf n | .split n _ _ => n

variable [One E] [Add E] [Sub E] [Mul E] [NatCast E]

/-- Prefer a matching graph domain. Otherwise validate the node's own first
domain only when several moments can reuse it. A single moment uses full
replay directly instead of constructing a cache for one use. -/
@[expose] def Node.cache [DecidableEq Ctx] (sign : E → Int)
    (context : Ctx) (p : DensePoly E) (a b : Endpoint E) (n : Node E Ctx)
    (shared : Option (TarskiCertificate.Domain.Checked (Ctx := Ctx) sign
      (EndpointSigns.ofSign sign))) :
    Option (TarskiCertificate.Domain.Checked (Ctx := Ctx) sign (EndpointSigns.ofSign sign)) :=
  n.moments.toArray[0]?.bind fun cert =>
    match shared.filter (fun d => d.data.binds context p a b cert.squarefree) with
    | some d => some d
    | none => if n.size ≤ 1 then none else
        TarskiCertificate.Domain.replay? sign (EndpointSigns.ofSign sign) cert.domain

/-- Check all local facts without query production, gcd search or row search.
The rank certificate's columns must preserve the retained support order.
Its full HexRank check is retained unchanged; the additional direct left-inverse
check avoids assuming an inverse-format or permutation adapter. -/
@[expose] def Node.check [DecidableEq Ctx] (sign : E → Int)
    (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (n : Node E Ctx)
    (shared : Option (TarskiCertificate.Domain.Checked (Ctx := Ctx) sign
      (EndpointSigns.ofSign sign)) := none) : Bool :=
  let k := n.system.positive.length
  decide (n.context = context ∧ n.head = p ∧ n.lower = a ∧ n.upper = b ∧ n.queries = qs) &&
  n.system.check qs.length &&
  decide (n.basis.rank = k) &&
  decide (n.basis.cols.toList.map Fin.val = List.range k) &&
  (let retained := n.system.retainedMatrix
   Matrix.checkRank retained n.basis &&
   decide (n.basis.adj * Matrix.selectedSubmatrix retained n.basis.rows n.basis.cols =
     Matrix.scale n.basis.denom (Matrix.identity n.basis.rank)) &&
   (match n.preparation with | none => true | some r => r.check sign p qs) &&
   (let cache := n.cache sign context p a b shared
    (List.finRange n.size).all (fun i =>
     checkMoment sign context p a b (QueryReduction.operands qs n.preparation)
       n.system.rows[i] n.system.values[i]
       n.moments[i] n.reductions[i] cache)))

/-- Sharing a validated domain leaves the result unchanged
for all supplied nodes, including empty systems and differing valid witnesses. -/
theorem Node.check_eq [DecidableEq Ctx] (sign : E → Int)
    (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (n : Node E Ctx)
    (shared : Option (TarskiCertificate.Domain.Checked (Ctx := Ctx) sign
      (EndpointSigns.ofSign sign))) :
    n.check sign context p a b qs shared = (
  let k := n.system.positive.length
  decide (n.context = context ∧ n.head = p ∧ n.lower = a ∧ n.upper = b ∧ n.queries = qs) &&
  n.system.check qs.length &&
  decide (n.basis.rank = k) &&
  decide (n.basis.cols.toList.map Fin.val = List.range k) &&
  (let retained := n.system.retainedMatrix
   Matrix.checkRank retained n.basis &&
   decide (n.basis.adj * Matrix.selectedSubmatrix retained n.basis.rows n.basis.cols =
     Matrix.scale n.basis.denom (Matrix.identity n.basis.rank)) &&
   (match n.preparation with | none => true | some r => r.check sign p qs) &&
   (List.finRange n.size).all (fun i =>
     checkMoment sign context p a b (QueryReduction.operands qs n.preparation)
       n.system.rows[i] n.system.values[i]
       n.moments[i] n.reductions[i]))) := by
  simp only [Node.check, checkMoment_eq]

/-- Passing a previously validated domain changes only replay work, never a
node's acceptance or the tree evidence that its result can justify. -/
theorem Node.check_cache [DecidableEq Ctx] (sign : E → Int)
    (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (n : Node E Ctx)
    (shared : Option (TarskiCertificate.Domain.Checked (Ctx := Ctx) sign
      (EndpointSigns.ofSign sign))) :
    n.check sign context p a b qs shared = n.check sign context p a b qs := by
  simp only [Node.check_eq]

/-- Empty and singleton lists have complete fixed supports. Larger leaves
are rejected, so this is not an exponential full-table fallback. -/
@[expose] def leafColumns (arity : Nat) : List (List Int) :=
  if arity = 0 then [[]] else [[-1], [0], [1]]

@[expose] def leafRows (arity : Nat) : List (List Nat) :=
  if arity = 0 then [[]] else [[0], [1], [2]]

/-- Literal recursive replay. Leaves include the root-count moment even for
an empty query list. At internal nodes both children are checked before the
parent solve, including when their product is empty. Thus a vacuous zero-size
system never stands alone as evidence of zero roots. -/
@[expose] def Replay.check [DecidableEq Ctx] (sign : E → Int)
    (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) : Replay E Ctx → Bool
  | .leaf n =>
    decide (qs.length ≤ 1) &&
    decide (n.system.columns.toList = leafColumns qs.length) &&
    decide (n.system.rows.toList = leafRows qs.length) &&
    n.check sign context p a b qs
  | .split n l r =>
    decide (1 < qs.length) &&
    l.check sign context p a b (qs.take (qs.length / 2)) &&
    r.check sign context p a b (qs.drop (qs.length / 2)) &&
    decide (n.system.columns.toList = product l.node.system.support r.node.system.support) &&
    decide (n.system.rows.toList = product l.node.rows r.node.rows) &&
    n.check sign context p a b qs

/-- Every accepted tree includes a checked local system at its root. -/
theorem Replay.check_node [DecidableEq Ctx] {sign : E → Int}
    {context : Ctx} {p : DensePoly E} {a b : Endpoint E}
    {qs : List (DensePoly E)} {t : Replay E Ctx}
    (h : t.check sign context p a b qs = true) :
    t.node.check sign context p a b qs = true := by
  cases t <;> simp only [Replay.check, Bool.and_eq_true] at h <;> exact h.2

/-- The complete children and exact Cartesian product are mandatory parts of
acceptance. Matrix invertibility cannot replace either child check. -/
theorem Replay.check_children [DecidableEq Ctx] {sign : E → Int}
    {context : Ctx} {p : DensePoly E} {a b : Endpoint E}
    {qs : List (DensePoly E)} {n : Node E Ctx} {l r : Replay E Ctx}
    (h : (Replay.split n l r).check sign context p a b qs = true) :
    l.check sign context p a b (qs.take (qs.length / 2)) = true ∧
    r.check sign context p a b (qs.drop (qs.length / 2)) = true ∧
    n.system.columns.toList = product l.node.system.support r.node.system.support := by
  simp only [Replay.check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩

/-- A checked node binds all operands literally and checks its integer system. -/
theorem Node.check_bindings [DecidableEq Ctx] {sign : E → Int}
    {context : Ctx} {p : DensePoly E} {a b : Endpoint E}
    {qs : List (DensePoly E)} {n : Node E Ctx}
    (h : n.check sign context p a b qs = true) :
    (n.context = context ∧ n.head = p ∧ n.lower = a ∧ n.upper = b ∧ n.queries = qs) ∧
    n.system.check qs.length = true := by
  simp only [Node.check_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

/-- Every accepted row has moment evidence for its exact exponent positions,
context, head, endpoints and integer right-hand side. -/
theorem Node.check_moment [DecidableEq Ctx] {sign : E → Int}
    {context : Ctx} {p : DensePoly E} {a b : Endpoint E}
    {qs : List (DensePoly E)} {n : Node E Ctx}
    (h : n.check sign context p a b qs = true) (i : Fin n.size) :
    checkMoment sign context p a b (QueryReduction.operands qs n.preparation) n.system.rows[i]
      n.system.values[i] n.moments[i] n.reductions[i] = true := by
  simp only [Node.check_eq, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2.2 i (List.mem_finRange i)

/-- Shared query reductions are checked against the exact original ordered
query list before any moment uses them. -/
theorem Node.check_preparation [DecidableEq Ctx] {sign : E → Int}
    {context : Ctx} {p : DensePoly E} {a b : Endpoint E}
    {qs : List (DensePoly E)} {n : Node E Ctx}
    (h : n.check sign context p a b qs = true) :
    (match n.preparation with | none => true | some r => r.check sign p qs) = true := by
  simp only [Node.check_eq, Bool.and_eq_true] at h
  exact h.2.1.2

/-- Even an empty root system reaches a checked Tarski query at a leaf.
Hence empty matrix identities can never bypass the shared domain guards. -/
theorem Replay.query_evidence [DecidableEq Ctx] {sign : E → Int}
    {context : Ctx} {p : DensePoly E} {a b : Endpoint E}
    {qs : List (DensePoly E)} {t : Replay E Ctx}
    (h : t.check sign context p a b qs = true) :
    ∃ f value cert, Sturm.check sign context p f a b value cert = true := by
  induction t generalizing qs with
  | leaf n =>
    have hn := Replay.check_node h
    simp only [Replay.check, Bool.and_eq_true, decide_eq_true_eq] at h
    have hs := congrArg List.length h.1.1.2
    have hp : 0 < n.size := by
      by_cases he : qs.length = 0 <;> simp [leafColumns, he] at hs <;> omega
    exact ⟨_, _, _, checkMoment_query (Node.check_moment hn ⟨0, hp⟩)⟩
  | split n l r ihl _ =>
    exact ihl (Replay.check_children h).1

end Hex.SignDet

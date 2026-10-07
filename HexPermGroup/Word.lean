/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Perm.Fast
public import HexPermGroup.Generated

public section

namespace Hex.PermGroup

/-- A word in signed original-generator indices. `true` denotes an inverse. -/
abbrev Word (S : Array (Perm n)) := List (Fin S.size × Bool)

namespace Word

@[expose] def letter (S : Array (Perm n)) (a : Fin S.size × Bool) : Perm n :=
  if a.2 then S[a.1.val].inv else S[a.1.val]

/-- Words use left-action composition: the rightmost letter acts first. -/
@[expose] def eval (S : Array (Perm n)) : Word S → Perm n
  | [] => Perm.id n
  | a :: w => (letter S a).comp (eval S w)

@[simp] theorem eval_nil (S : Array (Perm n)) : eval S [] = Perm.id n := rfl

@[simp] theorem eval_cons (S : Array (Perm n)) (a) (w : Word S) :
    eval S (a :: w) = (letter S a).comp (eval S w) := rfl

theorem eval_append (S : Array (Perm n)) (u v : Word S) :
    eval S (u ++ v) = (eval S u).comp (eval S v) := by
  induction u with
  | nil => simp [eval]
  | cons a u ih => simp [eval, ih, Perm.comp_assoc]

/-- Invert a word by reversing its letters and changing their signs. -/
@[expose] def inv {S : Array (Perm n)} (w : Word S) : Word S :=
  w.reverse.map fun a => (a.1, !a.2)

@[simp] theorem letter_inv (S : Array (Perm n)) (a : Fin S.size × Bool) :
    letter S (a.1, !a.2) = (letter S a).inv := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [letter]

theorem eval_inv (S : Array (Perm n)) (w : Word S) :
    eval S w.inv = (eval S w).inv := by
  induction w with
  | nil => simp [inv, eval]
  | cons a w ih =>
    simp only [inv, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      eval_append, eval_cons, eval_nil, Perm.comp_id, letter_inv, Perm.inv_comp]
    exact congrArg (fun p => p.comp (letter S a).inv) ih

theorem eval_generated (S : Array (Perm n)) (w : Word S) : Generated S (eval S w) := by
  induction w with
  | nil => exact .id
  | cons a w ih =>
    apply Generated.comp _ ih
    rcases a with ⟨i, b⟩
    cases b
    · exact .generator (Array.getElem_mem i.isLt)
    · exact .inv (.generator (Array.getElem_mem i.isLt))

/-- Prepend one letter, cancelling it against the first letter of `w` when that
letter is its inverse. -/
@[expose] def push {S : Array (Perm n)} (a : Fin S.size × Bool) : Word S → Word S
  | [] => [a]
  | b :: w => if b.1 = a.1 ∧ b.2 = !a.2 then w else a :: b :: w

theorem eval_push (S : Array (Perm n)) (a : Fin S.size × Bool) (w : Word S) :
    eval S (push a w) = (letter S a).comp (eval S w) := by
  cases w with
  | nil => rfl
  | cons b w =>
    rcases a with ⟨i, c⟩
    rcases b with ⟨j, d⟩
    simp only [push]
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      cases c <;> simp [letter, ← Perm.comp_assoc]
    · rfl

/-- Free reduction: cancel adjacent letters `(i, b)` and `(i, !b)` until none
remain. The result has no such adjacent pair. -/
@[expose] def reduce {S : Array (Perm n)} : Word S → Word S
  | [] => []
  | a :: w => push a (reduce w)

/-- `reduce` in constant stack space: push the letters from the right end. -/
@[expose] def reduceTR {S : Array (Perm n)} (w : Word S) : Word S :=
  w.reverse.foldl (fun acc a => push a acc) []

@[csimp] theorem reduce_eq_reduceTR : @reduce = @reduceTR := by
  funext n S w
  rw [reduceTR, List.foldl_reverse]
  induction w with
  | nil => rfl
  | cons a w ih => simp only [reduce, List.foldr_cons, ih]

@[simp] theorem eval_reduce (S : Array (Perm n)) (w : Word S) :
    eval S (reduce w) = eval S w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [reduce, eval_push, ih, eval_cons]

/-- Display a word as a product of generator names, such as `g0 * g1⁻¹`, with
`g i` naming `S[i]`. The empty word is displayed as `1`. -/
@[expose] def toString {S : Array (Perm n)} (w : Word S) : String :=
  if w.isEmpty then "1"
  else " * ".intercalate (w.map fun a => "g" ++ Nat.repr a.1.val ++ if a.2 then "⁻¹" else "")

end Word

/-- The closure predicate is exactly evaluation of finite signed words. -/
theorem generated_iff_word {S : Array (Perm n)} {p : Perm n} :
    Generated S p ↔ ∃ w : Word S, Word.eval S w = p := by
  constructor
  · intro h
    induction h with
    | id => exact ⟨[], rfl⟩
    | generator h =>
      rcases Array.mem_iff_getElem.mp h with ⟨i, hi, hp⟩
      exact ⟨[(⟨i, hi⟩, false)], by simp [Word.eval, Word.letter, hp]⟩
    | comp _ _ hp hq =>
      rcases hp with ⟨u, hu⟩
      rcases hq with ⟨v, hv⟩
      exact ⟨u ++ v, by rw [Word.eval_append, hu, hv]⟩
    | inv _ hp =>
      rcases hp with ⟨w, hw⟩
      exact ⟨w.inv, by rw [Word.eval_inv, hw]⟩
  · rintro ⟨w, rfl⟩
    exact Word.eval_generated S w

/-- One node in a straight-line program. References address earlier nodes only. -/
inductive Node where
  | id
  | generator (index : Nat)
  | inv (index : Nat)
  | comp (left right : Nat)
  deriving DecidableEq, Repr

/-- Raw program data. Evaluation rejects an invalid node, even if unreachable
from the root, and rejects an out-of-range root. -/
structure Program where
  nodes : Array Node
  root : Nat
  deriving DecidableEq, Repr

namespace Program

/-- Evaluate one node against the already evaluated values. Its result carries
provenance, which is erased by compilation. -/
@[expose] def evalNode (S : Array (Perm n))
    (values : Array {p : Perm n // Generated S p}) :
    Node → Option {p : Perm n // Generated S p}
  | .id => some ⟨Perm.id n, .id⟩
  | .generator i =>
    if h : i < S.size then some ⟨S[i], .generator (Array.getElem_mem h)⟩ else none
  | .inv i => do
    let p ← values[i]?
    return ⟨p.val.inv, .inv p.property⟩
  | .comp i j => do
    let p ← values[i]?
    let q ← values[j]?
    return ⟨p.val.comp q.val, .comp p.property q.property⟩

/-- Check every node in order, using only the values for references. -/
@[expose] def evalNodes (S : Array (Perm n)) :
    List Node → Array {p : Perm n // Generated S p} →
      Option (Array {p : Perm n // Generated S p})
  | [], values => some values
  | node :: rest, values => do
    let p ← evalNode S values node
    evalNodes S rest (values.push p)

/-- Evaluate the root of a fully checked program. -/
@[expose] def evalCertified (S : Array (Perm n)) (program : Program) :
    Option {p : Perm n // Generated S p} := do
  let values ← evalNodes S program.nodes.toList #[]
  values[program.root]?

/-- The executable permutation denoted by a program, or failure for malformed
references or generator indices. -/
@[expose] def eval (S : Array (Perm n)) (program : Program) : Option (Perm n) :=
  (evalCertified S program).map Subtype.val

theorem eval_sound {S : Array (Perm n)} {program : Program} {p : Perm n}
    (h : eval S program = some p) : Generated S p := by
  unfold eval at h
  cases he : evalCertified S program with
  | none => simp [he] at h
  | some q =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    exact h ▸ q.property

/-- The word of one node, computed from the words of earlier nodes. Words are
deferred, so that only nodes reachable from the root are ever expanded, while
the checks on indices and references match `evalNode`. -/
@[expose] def wordNode (S : Array (Perm n)) (words : Array (Thunk (Word S))) :
    Node → Option (Thunk (Word S))
  | .id => some (Thunk.pure [])
  | .generator i =>
    if h : i < S.size then some (Thunk.pure [(⟨i, h⟩, false)]) else none
  | .inv i => do
    let u ← words[i]?
    return Thunk.mk fun _ => u.get.inv
  | .comp i j => do
    let u ← words[i]?
    let v ← words[j]?
    return Thunk.mk fun _ => Word.reduce (u.get ++ v.get)

/-- Check every node in order, as `evalNodes` does, recording deferred words. -/
@[expose] def wordNodes (S : Array (Perm n)) :
    List Node → Array (Thunk (Word S)) → Option (Array (Thunk (Word S)))
  | [], words => some words
  | node :: rest, words => do
    let w ← wordNode S words node
    wordNodes S rest (words.push w)

/-- The freely reduced word in the original generators obtained by expanding
the nodes reachable from the root. It is `none` exactly when `eval S program`
is `none`. Expansion does not share subexpressions, so the word can be
exponentially longer than the program. Use it to display short programs, not
as a certificate. -/
@[expose] def toWord? (S : Array (Perm n)) (program : Program) : Option (Word S) := do
  let words ← wordNodes S program.nodes.toList #[]
  let w ← words[program.root]?
  return w.get

/-- The nodes the root depends on. References point to earlier nodes, so one
pass from the root downwards marks them all. -/
@[expose] def reachable (program : Program) : Array Bool :=
  (List.range program.nodes.size).reverse.foldl (init :=
      (Array.replicate program.nodes.size false).setIfInBounds program.root true)
    fun marks i =>
      if marks[i]?.getD false then
        match program.nodes[i]? with
        | some (Node.inv j) => marks.setIfInBounds j true
        | some (Node.comp j k) => (marks.setIfInBounds j true).setIfInBounds k true
        | _ => marks
      else marks

/-- `toWord?` for compiled code: before reading the root, force the deferred
words of the reachable nodes in increasing order, so that each finds its
operands already computed and expansion never recurses through the program's
depth. Unreachable nodes are still never expanded. -/
@[expose] def toWordImpl (S : Array (Perm n)) (program : Program) : Option (Word S) := do
  let words ← wordNodes S program.nodes.toList #[]
  let marks := reachable program
  let forced := words.mapIdx fun i t => if marks[i]?.getD false then Thunk.pure t.get else t
  let w ← forced[program.root]?
  return w.get

@[csimp] theorem toWord?_eq_toWordImpl : @toWord? = @toWordImpl := by
  funext n S program
  simp only [toWord?, toWordImpl]
  cases wordNodes S program.nodes.toList #[] with
  | none => rfl
  | some words =>
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    by_cases hr : program.root < words.size
    · rw [getElem?_pos words program.root hr,
        getElem?_pos _ program.root (by simpa using hr)]
      simp only [Option.bind_some, Array.getElem_mapIdx]
      split <;> rfl
    · rw [getElem?_neg words program.root hr,
        getElem?_neg _ program.root (by simpa using hr)]

private def Agree (S : Array (Perm n)) (words : Array (Thunk (Word S)))
    (values : Array {p : Perm n // Generated S p}) : Prop :=
  words.size = values.size ∧
    ∀ (k : Nat) (hw : k < words.size) (hv : k < values.size),
      Word.eval S words[k].get = values[k].val

private theorem wordNode_rel (S : Array (Perm n)) {words : Array (Thunk (Word S))}
    {values : Array {p : Perm n // Generated S p}} (h : Agree S words values) (node : Node) :
    Option.Rel (fun t p => Word.eval S t.get = p.val)
      (wordNode S words node) (evalNode S values node) := by
  obtain ⟨hs, he⟩ := h
  cases node with
  | id => exact .some rfl
  | generator i =>
    simp only [wordNode, evalNode]
    split
    · exact .some (by simp [Thunk.get, Thunk.pure, Word.eval, Word.letter])
    · exact .none
  | inv i =>
    simp only [wordNode, evalNode]
    by_cases hi : i < values.size
    · have hw : i < words.size := hs ▸ hi
      simp only [getElem?_pos words i hw, getElem?_pos values i hi]
      exact .some (by simp [Thunk.get, Word.eval_inv, ← he i hw hi])
    · have hw : ¬ i < words.size := hs ▸ hi
      simp only [getElem?_neg words i hw, getElem?_neg values i hi]
      exact .none
  | comp i j =>
    simp only [wordNode, evalNode]
    by_cases hi : i < values.size
    · have hwi : i < words.size := hs ▸ hi
      simp only [getElem?_pos words i hwi, getElem?_pos values i hi]
      by_cases hj : j < values.size
      · have hwj : j < words.size := hs ▸ hj
        simp only [getElem?_pos words j hwj, getElem?_pos values j hj]
        exact .some (by simp [Thunk.get, Word.eval_append, ← he i hwi hi, ← he j hwj hj])
      · have hwj : ¬ j < words.size := hs ▸ hj
        simp only [getElem?_neg words j hwj, getElem?_neg values j hj]
        exact .none
    · have hw : ¬ i < words.size := hs ▸ hi
      simp only [getElem?_neg words i hw, getElem?_neg values i hi]
      exact .none

private theorem wordNodes_rel (S : Array (Perm n)) (nodes : List Node) :
    ∀ {words : Array (Thunk (Word S))} {values : Array {p : Perm n // Generated S p}},
      Agree S words values →
        Option.Rel (Agree S) (wordNodes S nodes words) (evalNodes S nodes values) := by
  induction nodes with
  | nil => intro _ _ h; exact .some h
  | cons node rest ih =>
    intro words values h
    simp only [wordNodes, evalNodes]
    have hn := wordNode_rel S h node
    cases ha : wordNode S words node <;>
      cases hb : evalNode S values node <;> rw [ha, hb] at hn <;> cases hn
    case none.none => exact .none
    case some.some hab =>
      apply ih
      obtain ⟨hs, he⟩ := h
      refine ⟨by simp [hs], fun k hw hv => ?_⟩
      simp only [Array.getElem_push]
      by_cases hk : k < words.size
      · simp only [hk, dite_true, hs ▸ hk]
        exact he k hk (hs ▸ hk)
      · simp only [hk, dite_false, hs ▸ hk]
        exact hab

private theorem toWord?_rel (S : Array (Perm n)) (program : Program) :
    Option.Rel (fun w p => Word.eval S w = p) (toWord? S program) (eval S program) := by
  have h := wordNodes_rel S program.nodes.toList (words := #[]) (values := #[])
    ⟨rfl, fun k hw => absurd hw (by simp)⟩
  simp only [toWord?, eval, evalCertified]
  cases ha : wordNodes S program.nodes.toList #[] <;>
    cases hb : evalNodes S program.nodes.toList #[] <;> rw [ha, hb] at h <;> cases h
  case none.none => exact .none
  case some.some words values hab =>
    obtain ⟨hs, he⟩ := hab
    by_cases hr : program.root < values.size
    · have hw : program.root < words.size := hs ▸ hr
      simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some,
        getElem?_pos words program.root hw, getElem?_pos values program.root hr, Option.map_some]
      exact .some (he _ hw hr)
    · have hw : ¬ program.root < words.size := hs ▸ hr
      simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some,
        getElem?_neg words program.root hw, getElem?_neg values program.root hr,
        Option.bind_none, Option.map_none]
      exact .none

/-- A word obtained from a program evaluates to the program's value. -/
theorem eval_of_toWord? {S : Array (Perm n)} {program : Program} {w : Word S}
    (h : toWord? S program = some w) : eval S program = some (Word.eval S w) := by
  have hr := toWord?_rel S program
  rw [h] at hr
  cases hp : eval S program <;> rw [hp] at hr <;> cases hr
  case some.some hw => rw [hw]

/-- Flattening fails exactly when evaluation fails. -/
theorem isSome_toWord? (S : Array (Perm n)) (program : Program) :
    (toWord? S program).isSome = (eval S program).isSome := by
  have h := toWord?_rel S program
  revert h
  generalize toWord? S program = a
  generalize eval S program = b
  intro h
  cases h <;> rfl

/-- For each node, the length of the word `toWord?` expands it to before free
reduction, computed with `Nat` arithmetic and without expanding. A reference to
a missing node counts as length zero. -/
@[expose] def lengths (program : Program) : Array Nat :=
  program.nodes.foldl (init := #[]) fun ls node =>
    ls.push <| match node with
      | .id => 0
      | .generator _ => 1
      | .inv i => ls[i]?.getD 0
      | .comp i j => ls[i]?.getD 0 + ls[j]?.getD 0

/-- The length of the root's word before free reduction, an upper bound on the
length of the word `toWord?` returns. -/
@[expose] def expandedLength (program : Program) : Nat :=
  (lengths program)[program.root]?.getD 0

/-- Why `toWordCapped` returned no word. -/
inductive WordError where
  /-- The program does not evaluate. -/
  | invalid
  /-- The word before free reduction would have this many letters, more than
  the cap. -/
  | tooLong (length : Nat)
  deriving DecidableEq, Repr

/-- `toWord?` with a cap on the word's length before free reduction. The length
is computed from the program first, so a word over the cap is never expanded;
this check precedes the validity check. -/
@[expose] def toWordCapped (cap : Nat) (S : Array (Perm n)) (program : Program) :
    Except WordError (Word S) :=
  if cap < program.expandedLength then .error (.tooLong program.expandedLength)
  else match toWord? S program with
    | some w => .ok w
    | none => .error .invalid

theorem toWordCapped_ok {cap : Nat} {S : Array (Perm n)} {program : Program} {w : Word S}
    (h : toWordCapped cap S program = .ok w) : eval S program = some (Word.eval S w) := by
  unfold toWordCapped at h
  split at h
  · cases h
  · split at h
    · rename_i hw
      cases h
      exact eval_of_toWord? hw
    · cases h

theorem toWordCapped_tooLong {cap : Nat} {S : Array (Perm n)} {program : Program}
    {length : Nat} (h : toWordCapped cap S program = .error (.tooLong length)) :
    length = program.expandedLength ∧ cap < length := by
  unfold toWordCapped at h
  split at h
  · cases h
    exact ⟨rfl, by assumption⟩
  · split at h <;> cases h

theorem toWordCapped_invalid {cap : Nat} {S : Array (Perm n)} {program : Program}
    (h : toWordCapped cap S program = .error .invalid) : eval S program = none := by
  unfold toWordCapped at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hw
      have := isSome_toWord? S program
      rw [hw] at this
      cases he : eval S program
      · rfl
      · rw [he] at this; cases this

end Program

/-- Check that a program in the original generators denotes the claimed element. -/
@[expose] def checkWord (S : Array (Perm n)) (p : Perm n) (program : Program) : Bool :=
  decide (program.eval S = some p)

theorem checkWord_sound {S : Array (Perm n)} {p : Perm n} {program : Program}
    (h : checkWord S p program = true) : Generated S p :=
  Program.eval_sound (of_decide_eq_true h)

end Hex.PermGroup

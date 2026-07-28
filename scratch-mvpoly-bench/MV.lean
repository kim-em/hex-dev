import Std
open Std

abbrev Mono := Array Nat

def monoCmp (a b : Mono) : Ordering := compare a b

def monoCmpOld (a b : Mono) : Ordering := Id.run do
  for i in [0:a.size] do
    let x := a[i]!; let y := b[i]!
    if x < y then return .lt
    if y < x then return .gt
  return .eq

def monoAdd (a b : Mono) : Mono := a.zipWith (· + ·) b

/-! ## Rep A: ExtTreeMap-backed -/
abbrev PA := ExtTreeMap Mono Int compare

def PA.addTerm (p : PA) (m : Mono) (c : Int) : PA :=
  p.alter m fun
    | none => if c == 0 then none else some c
    | some d => if d + c == 0 then none else some (d + c)

def PA.add (p q : PA) : PA := q.foldl (fun acc m c => acc.addTerm m c) p
def PA.mul (p q : PA) : PA :=
  p.foldl (fun acc m c => q.foldl (fun acc m' c' => acc.addTerm (monoAdd m m') (c * c')) acc) ∅

/-! ## Rep B: sorted-list backed (Karatarakis / WuProver shape) -/
abbrev PB := List (Mono × Int)

def PB.addTerm : PB → Mono → Int → PB
  | [], m, c => if c == 0 then [] else [(m, c)]
  | (m', c') :: t, m, c =>
    match compare m m' with
    | .lt => (m', c') :: PB.addTerm t m c
    | .gt => if c == 0 then (m', c') :: t else (m, c) :: (m', c') :: t
    | .eq => if c' + c == 0 then t else (m', c' + c) :: t

def PB.add (p q : PB) : PB := q.foldl (fun acc (m, c) => PB.addTerm acc m c) p
def PB.mul (p q : PB) : PB :=
  p.foldl (fun acc (m, c) => q.foldl (fun acc (m', c') => PB.addTerm acc (monoAdd m m') (c * c')) acc) []

/-! ## Workload: (1 + x0 + ... + x_{n-1})^k, two ways -/
def genA (n : Nat) : PA :=
  (List.range n).foldl (fun p i => p.addTerm (Array.ofFn (fun j : Fin n => if j.val = i then 1 else 0)) 1)
    (PA.addTerm ∅ (Array.replicate n 0) 1)
def genB (n : Nat) : PB :=
  (List.range n).foldl (fun p i => PB.addTerm p (Array.ofFn (fun j : Fin n => if j.val = i then 1 else 0)) 1)
    (PB.addTerm [] (Array.replicate n 0) 1)

def powA (p : PA) : Nat → PA
  | 0 => PA.addTerm ∅ (Array.replicate 3 0) 1
  | k+1 => PA.mul p (powA p k)
def powB (p : PB) : Nat → PB
  | 0 => PB.addTerm [] (Array.replicate 3 0) 1
  | k+1 => PB.mul p (powB p k)

def sizeA (n k : Nat) : Nat := (powA (genA n) k).toList.length
def sizeB (n k : Nat) : Nat := (powB (genB n) k).length

#eval (sizeA 3 5, sizeB 3 5)
#eval (sizeA 3 8, sizeB 3 8)

def PA.toListX (p : PA) : List (Mono × Int) := p.toList
def PB.toListX (p : PB) : List (Mono × Int) := p

from pathlib import Path
p=Path('HexMvPoly/Kernel.lean');s=Path('/tmp/issue-10320-kernel/Kernel.recursors').read_text();old=Path('/tmp/issue-10320-kernel/Kernel.before').read_text()
for name,end in [('expBeq','/-- Lexicographic'),('expCmp','/-- Pointwise'),('addExp','/-- Insert')]:
 a=old.index('def '+name+' :');b=old.index(end,a)
 impl=old[a:b].replace(name,name+'Impl')
 start='def '+name+' ('
 s=s.replace(start, '/-- Equation implementation used by compiled callers. -/\n'+impl+'noncomputable '+start,1)
insert=s.index('/-- Insert one term')
helpers='''@[simp] theorem expBeq_nil (b : List Nat) :
    expBeq [] b = (match b with | [] => true | _ :: _ => false) := rfl
@[simp] theorem expBeq_cons_nil (x : Nat) (xs : List Nat) : expBeq (x :: xs) [] = false := rfl
@[simp] theorem expBeq_cons_cons (x y : Nat) (xs ys : List Nat) :
    expBeq (x :: xs) (y :: ys) = (Nat.beq x y && expBeq xs ys) := rfl

@[simp] theorem expCmp_nil (b : List Nat) :
    expCmp [] b = (match b with | [] => .eq | _ :: _ => .lt) := rfl
@[simp] theorem expCmp_cons_nil (x : Nat) (xs : List Nat) : expCmp (x :: xs) [] = .gt := rfl
@[simp] theorem expCmp_cons_cons (x y : Nat) (xs ys : List Nat) :
    expCmp (x :: xs) (y :: ys) =
      (if Nat.blt x y then .lt else if Nat.blt y x then .gt else expCmp xs ys) := rfl

@[simp] theorem addExp_nil (b : List Nat) : addExp [] b = b := rfl
@[simp] theorem addExp_cons_nil (x : Nat) (xs : List Nat) : addExp (x :: xs) [] = x :: xs := rfl
@[simp] theorem addExp_cons_cons (x y : Nat) (xs ys : List Nat) :
    addExp (x :: xs) (y :: ys) = Nat.add x y :: addExp xs ys := rfl

@[csimp] theorem expBeq_eq_impl : expBeq = expBeqImpl := by
  funext a b
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih => cases b <;> simp [expBeqImpl, ih]

@[csimp] theorem expCmp_eq_impl : expCmp = expCmpImpl := by
  funext a b
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih => cases b <;> simp [expCmpImpl, ih]

@[csimp] theorem addExp_eq_impl : addExp = addExpImpl := by
  funext a b
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih => cases b <;> simp [addExpImpl, ih]

'''
s=s[:insert]+helpers+s[insert:]
s=s.replace('simp [expBeq, ih]','simp [ih]').replace('simp [expCmp, ','simp [').replace('simp [expCmp]','simp')
s=s.replace('simp only [addExp, List.length_cons]','simp only [addExp_cons_cons, List.length_cons]').replace('simp only [addExp, List.getD_cons_succ]','simp only [addExp_cons_cons, List.getD_cons_succ]')
p.write_text(s)

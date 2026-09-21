from pathlib import Path
p=Path('HexMvPoly/Kernel.lean');s=p.read_text()
a=s.index('def mulTerm [');b=s.index('/-- Sum rows',a)
old=s[a:b].replace('mulTerm','mulTermImpl')
new='''/-- Kernel row multiplication; compilation uses the equation implementation. -/
noncomputable def mulTerm [Zero κ] [Add κ] [Mul κ] [DecidableEq κ]
    (t : Term κ) (p : PolyList κ) : PolyList κ :=
  List.rec (motive := fun _ => PolyList κ) []
    (fun u _ next => insert (addExp t.1 u.1, t.2 * u.2) next) p

@[simp] theorem mulTerm_nil [Zero κ] [Add κ] [Mul κ] [DecidableEq κ] (t : Term κ) :
    mulTerm t [] = [] := rfl
@[simp] theorem mulTerm_cons [Zero κ] [Add κ] [Mul κ] [DecidableEq κ]
    (t u : Term κ) (us : PolyList κ) :
    mulTerm t (u :: us) = insert (addExp t.1 u.1, t.2 * u.2) (mulTerm t us) := rfl

@[csimp] theorem mulTerm_eq_impl [Zero κ] [Add κ] [Mul κ] [DecidableEq κ] :
    @mulTerm κ _ _ _ _ = @mulTermImpl κ _ _ _ _ := by
  funext t p
  induction p with
  | nil => rfl
  | cons u us ih => simp [mulTermImpl, ih]

'''
s=s[:a]+old+new+s[b:]
a=s.index('def beq [');b=s.index('/-- Linear-time exponentiation',a)
old=s[a:b].replace('beq','beqImpl')
new='''/-- Kernel list equality; compilation uses the equation implementation. -/
noncomputable def beq [DecidableEq κ] (p q : PolyList κ) : Bool :=
  List.rec (motive := fun _ => PolyList κ → Bool)
    (fun q => match q with | [] => true | _ :: _ => false)
    (fun t _ next q => match q with
      | [] => false
      | u :: us => expBeq t.1 u.1 && decide (t.2 = u.2) && next us) p q

@[simp] theorem beq_nil [DecidableEq κ] (q : PolyList κ) :
    beq [] q = (match q with | [] => true | _ :: _ => false) := rfl
@[simp] theorem beq_cons_nil [DecidableEq κ] (t : Term κ) (ts : PolyList κ) :
    beq (t :: ts) [] = false := rfl
@[simp] theorem beq_cons_cons [DecidableEq κ] (t u : Term κ) (ts us : PolyList κ) :
    beq (t :: ts) (u :: us) = (expBeq t.1 u.1 && decide (t.2 = u.2) && beq ts us) := rfl

@[csimp] theorem beq_eq_impl [DecidableEq κ] : @beq κ _ = @beqImpl κ _ := by
  funext p q
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons t ts ih => cases q <;> simp [beqImpl, ih]

'''
s=s[:a]+old+new+s[b:]
s=s.replace('rw [mulTerm]','rw [mulTerm_cons]').replace('simp only [mulTerm, denote]','simp only [mulTerm_nil, denote]').replace('rw [mulTerm, denote_insert','rw [mulTerm_cons, denote_insert')
s=s.replace('simp only [beq, Bool.and_eq_true','simp only [beq_cons_cons, Bool.and_eq_true')
p.write_text(s)

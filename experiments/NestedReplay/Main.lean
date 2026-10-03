/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRealClosure.SignFacts
import HexSignDet.DagEncode

open Hex Hex.RealClosure.Algebraic Hex.SignDet

/-! Native-only diagnostic experiment. Local unsafe wrappers observe ordinary
packing and reuse correctly typed facts produced by that same computation.
They are not kernel proof methods or changes to library arithmetic. A missing
fact exits before running a replacement sign search; no fabricated value or
proof is returned. The compiler may eliminate redundant pure calls, so counts
measure executed wrapper calls, not a formal arithmetic complexity bound. -/

inductive Mode where
  | collect | ordinary | replay
  deriving BEq

structure Counts where
  calls : Nat := 0
  signs : Nat := 0
  nonconstantSigns : Nat := 0
  hits : Nat := 0
  deriving Repr

variable {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Neg E]
  [Mul E] [Inv E] [Div E] [NatCast E]
  {sign : E → Int} {parent : Nat}

structure Store (context : Context E Nat sign parent) where
  level : Nat
  mode : IO.Ref Mode
  facts : IO.Ref (List (SignFact context))
  used : IO.Ref (List (DensePoly E))
  counts : IO.Ref Counts

unsafe def Store.create (context : Context E Nat sign parent) (level : Nat)
    (mode : IO.Ref Mode) : IO (Store context) := do
  return ⟨level, mode, ← IO.mkRef [], ← IO.mkRef [], ← IO.mkRef {}⟩

@[noinline] unsafe def pack (context : Context E Nat sign parent)
    (store : Store context) (p : DensePoly E) : Element context :=
  match unsafeIO (do
    let kept := context.reduce p
    store.counts.modify fun c => {c with calls := c.calls + 1}
    let mode ← store.mode.get
    if mode != .collect then
      store.used.modify fun ps => if kept ∈ ps then ps else kept :: ps
    if mode == .replay then
      match SignFact.find (← store.facts.get) kept with
      | some f =>
        store.counts.modify fun c => {c with hits := c.hits + 1}
        if hn : f.val = 0 then return 0
        else return Element.restore kept f.val f.property hn
      | none =>
        IO.eprintln s!"MISSING level={store.level}; no replacement sign evaluation"
        IO.eprintln s!"counts={reprStr (← store.counts.get)}"
        IO.Process.exit 17
    else
      store.counts.modify fun c => {c with
        signs := c.signs + 1
        nonconstantSigns := c.nonconstantSigns + (if 1 < kept.size then 1 else 0)}
      let s := context.signPoly kept
      if mode == .collect then
        let fact : SignFact context := ⟨kept, s, rfl⟩
        store.facts.modify fun fs =>
          if (SignFact.find fs kept).isSome then fs else fact :: fs
      if hn : s = 0 then return 0
      else return Element.restore kept s rfl hn) with
  | .ok value => value
  | .error e =>
    letI : Inhabited (Element context) := ⟨0⟩
    panic! s!"prototype IO failure: {e}"

@[instance_reducible] unsafe def one (c : Context E Nat sign parent) (s : Store c) : One (Element c) :=
  ⟨pack c s 1⟩
@[instance_reducible] unsafe def add (c : Context E Nat sign parent) (s : Store c) : Add (Element c) :=
  ⟨fun a b => pack c s (a.polynomial + b.polynomial)⟩
@[instance_reducible] unsafe def sub (c : Context E Nat sign parent) (s : Store c) : Sub (Element c) :=
  ⟨fun a b => pack c s (a.polynomial - b.polynomial)⟩
@[instance_reducible] unsafe def mul (c : Context E Nat sign parent) (s : Store c) : Mul (Element c) :=
  ⟨fun a b => pack c s (a.polynomial * b.polynomial)⟩
@[instance_reducible] unsafe def neg (c : Context E Nat sign parent) (s : Store c) : Neg (Element c) :=
  ⟨fun a => pack c s (0 - a.polynomial)⟩
@[instance_reducible] unsafe def natCast (c : Context E Nat sign parent) (s : Store c) : NatCast (Element c) :=
  ⟨fun n => pack c s (DensePoly.C n)⟩

/-- Inversion is outside this experiment's replay vocabulary. Reject it rather
than silently entering ordinary packing through an uninstrumented operation. -/
@[noinline] unsafe def inverse (c : Context E Nat sign parent) (s : Store c)
    (a : Element c) : Element c :=
  match unsafeIO (do
    if (← s.mode.get) == .replay then
      IO.eprintln s!"UNSUPPORTED inverse level={s.level}"
      IO.Process.exit 18
    return Element.inv a) with
  | .ok value => value
  | .error e =>
    letI : Inhabited (Element c) := ⟨0⟩
    panic! s!"prototype IO failure: {e}"

@[instance_reducible] unsafe def inv (c : Context E Nat sign parent) (s : Store c) : Inv (Element c) :=
  ⟨inverse c s⟩
@[instance_reducible] unsafe def div (c : Context E Nat sign parent) (s : Store c) : Div (Element c) :=
  ⟨fun a b => pack c s (a.polynomial * (inverse c s b).polynomial)⟩

def root (s : E → Int) (id : Nat) (p : DensePoly E) (a b : E) :
    IO (Descriptor E Nat s id) := do
  match Descriptor.build s id ⟨id, p, .finite a, .finite b, [], []⟩ with
  | .ok (.ok d) => return d
  | _ => throw (IO.userError "selected-root construction failed")

unsafe def report {context : Context E Nat sign parent} (s : Store context) : IO Unit := do
  IO.println s!"level={s.level} facts={(← s.facts.get).length} used={(← s.used.get).length} {reprStr (← s.counts.get)}"

unsafe def reset {context : Context E Nat sign parent} (s : Store context) : IO Unit := do
  s.counts.set {}
  s.used.set []

unsafe def removeFact {context : Context E Nat sign parent} (s : Store context) : IO Unit := do
  let some victim := (← s.used.get).find? (fun p => 1 < p.size)
    | throw (IO.userError "no nonconstant replay fact to remove")
  s.facts.modify fun fs => fs.filter (fun f => f.polynomial != victim)
  IO.println s!"removed one actually used nonconstant level={s.level} fact"

/-- A changing nonce prevents the native compiler from sharing the entire
Boolean replay result across mode changes. Every positive nonce checks the
identical graph and caller inputs. -/
@[noinline] def checkGraph (nonce : Nat) (g : Dag E Nat) (s : E → Int) (id : Nat)
    (p : DensePoly E) (a b : Endpoint E) (qs : List (DensePoly E)) : Bool :=
  nonce != 0 && g.check s id p a b qs

unsafe def main (args : List String) : IO UInt32 := do
  let mode ← IO.mkRef Mode.collect
  let d1 ← root Sturm.orderSign 7 (DensePoly.ofCoeffs #[-2, 0, 1] : DensePoly Rat) 1 2
  let c1 := Context.adjoin d1 (fun _ => true)
  let s1 ← Store.create c1 1 mode
  letI := one c1 s1
  letI := add c1 s1
  letI := sub c1 s1
  letI := mul c1 s1
  letI := neg c1 s1
  letI := natCast c1 s1
  letI := inv c1 s1
  letI := div c1 s1
  letI : Hashable (Element c1) := ⟨fun _ => 0⟩
  do
    let a := pack c1 s1 (DensePoly.ofCoeffs #[0, 1])
    let d2 ← root Element.sign 8 (DensePoly.ofCoeffs #[-(a + (2 : Element c1)), 0, 1]) (1 : Element c1) 3
    let c2 := Context.adjoin d2 (fun _ => true)
    let s2 ← Store.create c2 2 mode
    letI := one c2 s2
    letI := add c2 s2
    letI := sub c2 s2
    letI := mul c2 s2
    letI := neg c2 s2
    letI := natCast c2 s2
    letI := inv c2 s2
    letI := div c2 s2
    letI : Hashable (Element c2) := ⟨fun _ => 0⟩
    do
      let b := pack c2 s2 (DensePoly.ofCoeffs #[0, 1])
      let constructionStarted ← IO.monoNanosNow
      let d3 ← root Element.sign 9 (DensePoly.ofCoeffs #[-(b + (2 : Element c2)), 0, 1]) (1 : Element c2) 3
      let q : DensePoly (Element c2) := DensePoly.ofCoeffs #[-b, 1]
      let queries := [q, q]
      let productionStarted ← IO.monoNanosNow
      let signs ← match d3.buildSigns queries with
        | .ok signs => pure signs
        | .error _ => throw (IO.userError "sign producer failed")
      if signs.values.toList != [1, 1] then
        throw (IO.userError "unexpected selected signs")
      let graph := Dag.encode signs.evidence
      IO.println s!"productionNanos={(← IO.monoNanosNow) - productionStarted}"
      IO.println s!"thirdRootAndProductionNanos={(← IO.monoNanosNow) - constructionStarted}"
      let check := fun (nonce : Nat) => checkGraph nonce graph Element.sign 9 d3.raw.head
        d3.raw.lower d3.raw.upper (d3.raw.queries ++ queries)
      IO.println s!"graphNodes={graph.entries.size} selectedSigns={signs.values.toList}"
      IO.println "factsAfterProduction"
      report s1
      report s2
      if args.contains "--collect-replay" then
        let started ← IO.monoNanosNow
        if !check 1 then throw (IO.userError "collection replay rejected")
        let elapsed := (← IO.monoNanosNow) - started
        IO.println s!"collectReplayNanos={elapsed}"
      report s1
      report s2
      reset s1
      reset s2
      mode.set .replay
      let started ← IO.monoNanosNow
      if !check 2 then throw (IO.userError "cached replay rejected")
      let elapsed := (← IO.monoNanosNow) - started
      IO.println s!"cachedReplayNanos={elapsed}"
      if (← s1.counts.get).calls == 0 || (← s2.counts.get).calls == 0 then
        throw (IO.userError "compiler eliminated replay instrumentation")
      if (← s1.counts.get).signs != 0 || (← s2.counts.get).signs != 0 then
        throw (IO.userError "replay performed a replacement sign evaluation")
      report s1
      report s2
      let cachedCounts1 ← s1.counts.get
      let cachedCounts2 ← s2.counts.get
      if args.contains "--omit" || args.contains "--omit-level-one" then
        if args.contains "--omit-level-one" then removeFact s1 else removeFact s2
        reset s1
        reset s2
        if check 3 then throw (IO.userError "omitted fact was accepted")
        return 1
      -- Both timed arms record the same used-key list and wrapper counters.
      -- Each changing nonce forces a new native check rather than reusing a Bool.
      let repetitions := 200
      let arms := if args.contains "--ordinary-first" then
        [Mode.ordinary, Mode.replay] else [Mode.replay, Mode.ordinary]
      for arm in arms do
        reset s1
        reset s2
        mode.set arm
        let started ← IO.monoNanosNow
        for i in [:repetitions] do
          if !check (10 + i) then throw (IO.userError "timed replay rejected")
        let elapsed := (← IO.monoNanosNow) - started
        let label := if arm == .replay then "cached" else "ordinary"
        IO.println s!"arm={label} repetitions={repetitions} nanos={elapsed}"
        let counts1 ← s1.counts.get
        let counts2 ← s2.counts.get
        if counts1.calls == 0 || counts2.calls == 0 then
          throw (IO.userError "compiler eliminated timed replay instrumentation")
        if arm == .replay then
          if counts1.signs != 0 || counts2.signs != 0 then
            throw (IO.userError "timed replay performed replacement signs")
          if counts1.calls != cachedCounts1.calls * repetitions ||
              counts2.calls != cachedCounts2.calls * repetitions then
            throw (IO.userError "native compiler shared a timed replay result")
        report s1
        report s2
      return 0

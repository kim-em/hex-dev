/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRealClosure.SignCodec
import HexSignDet.Codec
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
  inverses : Nat := 0
  deriving Repr

variable {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Neg E]
  [Mul E] [Inv E] [Div E] [NatCast E]
  {sign : E → Int} {parent : Nat}

structure Store (context : Context E Nat sign parent) where
  level : Nat
  mode : IO.Ref Mode
  facts : IO.Ref (List (SignFact context))
  used : IO.Ref (List (DensePoly E))
  literals : IO.Ref (List (DensePoly E))
  track : IO.Ref Bool
  counts : IO.Ref Counts

unsafe def Store.create (context : Context E Nat sign parent) (level : Nat)
    (mode : IO.Ref Mode) : IO (Store context) := do
  return ⟨level, mode, ← IO.mkRef [], ← IO.mkRef [], ← IO.mkRef [], ← IO.mkRef true, ← IO.mkRef {}⟩

@[noinline] unsafe def pack (context : Context E Nat sign parent)
    (store : Store context) (p : DensePoly E) : Element context :=
  match unsafeIO (do
    let kept := context.reduce p
    store.counts.modify fun c => {c with calls := c.calls + 1}
    let mode ← store.mode.get
    if mode != .collect && (← store.track.get) then
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
    panic! s!"prototype IO failure (runner aborts on panic): {e}"

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
    s.counts.modify fun counts => {counts with inverses := counts.inverses + 1}
    if a == 0 then return 0
    return pack c s a.inverseCandidate) with
  | .ok value => value
  | .error e =>
    letI : Inhabited (Element c) := ⟨0⟩
    panic! s!"prototype IO failure (runner aborts on panic): {e}"

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

/-- Read every nonzero literal through the existing strict recursive codec.
This still trusts in-memory producer facts, not independently replayed children. -/
@[noinline] unsafe def literalCodec (c : Context E Nat sign parent) (s : Store c)
    (base : ValueCodec E) (nonce : Nat := 1) : ValueCodec (Element c) where
  encode := (Element.codec base).encode
  decode j := match unsafeIO (do
    if nonce == 0 then IO.Process.exit 19
    match (Element.signCodec base (← s.facts.get)).decode j with
    | .error error =>
      IO.eprintln s!"LITERAL_REJECTED level={s.level}: {error}; no replacement sign evaluation"
      IO.Process.exit 17
    | .ok a =>
      if a != 0 then
        s.literals.modify fun ps => if a.polynomial ∈ ps then ps else a.polynomial :: ps
      return Except.ok a) with
    | .ok result => result
    | .error e => .error s!"prototype IO error: {e}"

private def demand (result : Except String α) : IO α :=
  match result with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

unsafe def removeFact {context : Context E Nat sign parent} (s : Store context) (literal := false) : IO Unit := do
  let keys ← if literal then s.literals.get else s.used.get
  let some victim := keys.find? (fun p => 1 < p.size)
    | throw (IO.userError "no nonconstant replay fact to remove")
  s.facts.modify fun fs => fs.filter (fun f => f.polynomial != victim)
  IO.println s!"removed one actually used nonconstant level={s.level} fact"

/-- A changing nonce prevents the native compiler from sharing the entire
Boolean replay result across mode changes. Every positive nonce checks the
identical graph and caller inputs. -/
@[noinline] def checkGraph (nonce : Nat) (g : Dag E Nat) (s : E → Int) (id : Nat)
    (p : DensePoly E) (a b : Endpoint E) (qs : List (DensePoly E)) : Bool :=
  nonce != 0 && g.check s id p a b qs

/-- A separate tower using the unmodified library instances, with no IO counters. -/
def plain : IO (Nat → Bool) := do
  let d1 ← root Sturm.orderSign 7 (DensePoly.ofCoeffs #[-2, 0, 1] : DensePoly Rat) 1 2
  let c1 := Context.adjoin d1 (fun _ => true)
  letI : Hashable (Element c1) := ⟨fun _ => 0⟩
  do
    let a := Element.ofPoly (context := c1) (DensePoly.ofCoeffs #[0, 1])
    let d2 ← root Element.sign 8 (DensePoly.ofCoeffs #[-(a + (2 : Element c1)), 0, 1]) (1 : Element c1) 3
    let c2 := Context.adjoin d2 (fun _ => true)
    letI : Hashable (Element c2) := ⟨fun _ => 0⟩
    do
      let b := Element.ofPoly (context := c2) (DensePoly.ofCoeffs #[0, 1])
      let d3 ← root Element.sign 9 (DensePoly.ofCoeffs #[-(b + (2 : Element c2)), 0, 1]) (1 : Element c2) 3
      let q : DensePoly (Element c2) := DensePoly.ofCoeffs #[-b, 1]
      let signs ← match d3.buildSigns [q, q] with
        | .ok result => pure result
        | .error _ => throw (IO.userError "plain producer failed")
      if signs.values.toList != [1, 1] then throw (IO.userError "plain signs differ")
      let graph := Dag.encode signs.evidence
      return fun nonce => checkGraph nonce graph Element.sign 9 d3.raw.head
        d3.raw.lower d3.raw.upper (d3.raw.queries ++ [q, q])

/-- Different representatives and conjugate contexts must not share literals. -/
unsafe def keyProbes : IO Unit := do
  let mode ← IO.mkRef Mode.collect
  let head : DensePoly Rat := DensePoly.ofCoeffs #[-4, 0, 2]
  let positive ← root Sturm.orderSign 7 head 1 2
  let negative ← root Sturm.orderSign 7 head (-2) (-1)
  let cp := Context.adjoin positive (fun _ => true)
  let cn := Context.adjoin negative (fun _ => true)
  if cp.canReduce || cn.canReduce then throw (IO.userError "nonmonic reduction was enabled")
  let sp ← Store.create cp 1 mode
  let sn ← Store.create cn 1 mode
  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  let a := pack cp sp x
  let b := pack cn sn x
  let alias := Element.ofPoly (context := cp) (x + head)
  if a.sign != 1 || b.sign != -1 || alias.sign != 1 || alias.polynomial == a.polynomial then
    throw (IO.userError "key-probe setup failed")
  let vp := Element.signCodec ValueCodec.rat (← sp.facts.get)
  let vn := Element.signCodec ValueCodec.rat (← sn.facts.get)
  if (vp.decode (vp.encode alias)).isOk then
    throw (IO.userError "a semantically equal absent literal was accepted")
  if (vn.decode (vp.encode a)).isOk then
    throw (IO.userError "a conjugate context accepted the opposite cached sign")
  IO.println "noncanonicalAliasRejected=true conjugateLiteralRejected=true"

unsafe def main (args : List String) : IO UInt32 := do
  if args.contains "--keys-only" then
    keyProbes
    return 0
  let plainCheck ← plain
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
      let nativeCodec := Element.codec (context := c2) (Element.codec (context := c1) ValueCodec.rat)
      let graphBytes := graph.encodeBytes nativeCodec ValueCodec.nat
      IO.println "factsAfterProduction"
      report s1
      report s2
      mode.set .replay
      let codec1 := literalCodec c1 s1 ValueCodec.rat
      let codec2 := literalCodec c2 s2 codec1
      -- Validate immutable context inputs and the prebuilt One values as well.
      let _ ← demand (Codec.readPoly codec1 (Codec.poly codec1 d2.raw.head))
      let _ ← demand (Codec.readEndpoint codec1 (Codec.endpoint codec1 d2.raw.lower))
      let _ ← demand (Codec.readEndpoint codec1 (Codec.endpoint codec1 d2.raw.upper))
      let _ ← demand (codec1.decode (codec1.encode (1 : Element c1)))
      let _ ← demand (codec2.decode (codec2.encode (1 : Element c2)))
      let readInputs : Nat → IO (Dag (Element c2) Nat × DensePoly (Element c2) ×
          Endpoint (Element c2) × Endpoint (Element c2) × List (DensePoly (Element c2))) :=
          fun nonce => do
        let codec1 := literalCodec c1 s1 ValueCodec.rat nonce
        let codec2 := literalCodec c2 s2 codec1 nonce
        let head ← demand (Codec.readPoly codec2 (Codec.poly nativeCodec d3.raw.head))
        let lower ← demand (Codec.readEndpoint codec2 (Codec.endpoint nativeCodec d3.raw.lower))
        let upper ← demand (Codec.readEndpoint codec2 (Codec.endpoint nativeCodec d3.raw.upper))
        let qs ← demand (Codec.readList (Codec.readPoly codec2)
          (Codec.list (Codec.poly nativeCodec) (d3.raw.queries ++ queries)))
        let decoded ← demand (Codec.decodeGraph codec2 ValueCodec.nat 9 head lower upper graphBytes)
        if decoded.encodeBytes nativeCodec ValueCodec.nat != graphBytes then
          throw (IO.userError "strict decoding changed a literal")
        return (decoded, head, lower, upper, qs)
      let (decoded, head, lower, upper, qs) ← readInputs 1
      IO.println s!"nonconstantFacts1={(← s1.facts.get).countP (fun f => 1 < f.polynomial.size)} nonconstantFacts2={(← s2.facts.get).countP (fun f => 1 < f.polynomial.size)}"
      IO.println s!"literalKeys1={(← s1.literals.get).length} literalKeys2={(← s2.literals.get).length}"
      if args.contains "--omit-literal" then
        removeFact s2 true
        let _ ← readInputs 2
        throw (IO.userError "missing literal fact was accepted")
      let check := fun (nonce : Nat) => checkGraph nonce decoded (Element.sign (context := c2)) 9 head lower upper qs
      IO.println s!"graphNodes={graph.entries.size} selectedSigns={signs.values.toList}"
      if args.contains "--collect-replay" then
        mode.set .collect
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
      reset s1
      reset s2
      mode.set .ordinary
      if !check 4 then throw (IO.userError "ordinary preflight rejected")
      let ordinaryCounts1 ← s1.counts.get
      let ordinaryCounts2 ← s2.counts.get
      s1.track.set false
      s2.track.set false
      let repetitions := 200
      let arms := if args.contains "--ordinary-first" then
        ["plain", "ordinary", "cached"] else ["cached", "ordinary", "plain"]
      for label in arms do
        reset s1
        reset s2
        mode.set (if label == "cached" then .replay else .ordinary)
        let started ← IO.monoNanosNow
        for i in [:repetitions] do
          let accepted := if label == "plain" then plainCheck (10 + i) else check (10 + i)
          if !accepted then throw (IO.userError "timed replay rejected")
        let elapsed := (← IO.monoNanosNow) - started
        IO.println s!"arm={label} repetitions={repetitions} nanos={elapsed}"
        let counts1 ← s1.counts.get
        let counts2 ← s2.counts.get
        if label != "plain" then
          let expected1 := if label == "cached" then cachedCounts1 else ordinaryCounts1
          let expected2 := if label == "cached" then cachedCounts2 else ordinaryCounts2
          if counts1.calls != expected1.calls * repetitions ||
              counts2.calls != expected2.calls * repetitions then
            throw (IO.userError "native compiler shared a timed replay result")
        if label == "cached" && (counts1.signs != 0 || counts2.signs != 0) then
          throw (IO.userError "timed replay performed replacement signs")
        report s1
        report s2
      return 0

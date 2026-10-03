/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Soundness
public import HexRealRootsMathlib.RealClosed
public import HexRCF.RealCoefficients.IntervalSign

public section

/-! Exact interval bounds and rational Tarski queries for a selected literal real root. -/

namespace Hex.RCF.RealCoefficients.LiteralSign

open Hex HexRealRootsMathlib HexPolyMathlib.Interpret

/-- Interpret a rational dense polynomial as a real polynomial. -/
@[expose] noncomputable def realPoly (p : DensePoly Rat) : Polynomial ℝ :=
  interpret (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero) p

/-- A count-one rational interval and an accepted query determine the sign at
the selected root. The root may have been named by a separate literal square;
only its equation and membership in this interval are used here. -/
theorem checked_one (p q : DensePoly Rat) (lower upper : Rat)
    (x : ℝ) (hx : (realPoly p).IsRoot x)
    (hl : (lower : ℝ) < x) (hu : x < (upper : ℝ))
    (count query : TarskiCertificate Rat Rat Unit) (value : Int)
    (hc : Sturm.check Sturm.orderSign () p 1 (.finite lower) (.finite upper)
      1 count = true)
    (hq : Sturm.check Sturm.orderSign () p q (.finite lower) (.finite upper)
      value query = true) :
    value = (SignType.sign ((realPoly q).eval x) : Int) := by
  classical
  let f : Rat → ℝ := fun r => (r : ℝ)
  have hz : ∀ a : Rat, f a = 0 ↔ a = 0 := fun _ => Rat.cast_eq_zero
  have h1 : f 1 = 1 := by norm_num [f]
  have ha : ∀ a b : Rat, f (a + b) = f a + f b := fun _ _ => Rat.cast_add _ _
  have hs : ∀ a b : Rat, f (a - b) = f a - f b := fun _ _ => Rat.cast_sub _ _
  have hm : ∀ a b : Rat, f (a * b) = f a * f b := fun _ _ => Rat.cast_mul _ _
  have hn : ∀ n : Nat, f (n : Rat) = (n : ℝ) := by intro n; norm_num [f]
  have hsign : ∀ a : Rat, Sturm.orderSign a = (SignType.sign (f a) : Int) := by
    intro a
    rw [HexSturmMathlib.orderSign_eq]
    rcases lt_trichotomy a 0 with hneg | hzero | hpos
    · have hr : (a : ℝ) < 0 := by exact_mod_cast hneg
      simp [sign_neg hneg, sign_neg hr, f]
    · subst a
      simp [f]
    · have hr : (0 : ℝ) < a := by exact_mod_cast hpos
      simp [sign_pos hpos, sign_pos hr, f]
  have countSound := HexSturmMathlib.check_sound f hz h1 ha hs hm hn
    Sturm.orderSign hsign () p 1 (.finite lower) (.finite upper) 1 count hc
  have countSpec := countSound.2
  change (1 : Int) = Tarski.rootSum (realPoly p) (realPoly 1)
    (.finite (lower : ℝ)) (.finite (upper : ℝ)) at countSpec
  rw [show realPoly (1 : DensePoly Rat) = 1 by
      exact interpret_one f hz h1, Tarski.rootSum_one] at countSpec
  have hne : realPoly p ≠ 0 := countSound.1.1
  have hmem : x ∈ Tarski.rootsIn (realPoly p)
      (.finite (lower : ℝ)) (.finite (upper : ℝ)) :=
    (Tarski.mem_rootsIn_iff (realPoly p) hne _ _ x).mpr
      ⟨hx.eq_zero, (Tarski.inInterval_finite _ _ _).mpr ⟨hl, hu⟩⟩
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (by exact_mod_cast countSpec.symm)
  have hxr : x = r := by simpa only [hr, Finset.mem_singleton] using hmem
  have querySpec := (HexSturmMathlib.check_sound f hz h1 ha hs hm hn
    Sturm.orderSign hsign () p q (.finite lower) (.finite upper) value query hq).2
  change value = Tarski.rootSum (realPoly p) (realPoly q)
    (.finite (lower : ℝ)) (.finite (upper : ℝ)) at querySpec
  rw [Tarski.rootSum_singleton _ _ _ _ r hr, ← hxr] at querySpec
  exact querySpec

/-- A literal sign for one value of a fixed real number field. Coordinates
come from the key. Absent query evidence selects exact interval evaluation;
present query evidence must pass its own binding and replay checks. -/
structure Entry (D : Type u) where
  key : D
  value : Int
  evidence : Option (TarskiCertificate Rat Rat Unit)

namespace Entry

/-- Replay interval entries with exact Horner arithmetic on the authenticated
generator enclosure; query entries retain their full rational certificate. -/
@[expose] def check {D : Type u} (entry : Entry D) (head : DensePoly Rat)
    (lower upper : Rat) (query : D → DensePoly Rat) : Bool :=
  match entry.evidence with
  | none => decide (IntervalSign.sign? (query entry.key) lower upper = some entry.value)
  | some evidence => Sturm.check Sturm.orderSign () head (query entry.key)
      (.finite lower) (.finite upper) entry.value evidence

/-- Both evidence branches identify the same real sign. A malformed query
certificate is rejected rather than replaced with interval evidence. -/
theorem check_spec {D : Type u} (entry : Entry D) (head : DensePoly Rat)
    (lower upper : Rat) (query : D → DensePoly Rat) (x : ℝ)
    (hx : (realPoly head).IsRoot x)
    (hl : (lower : ℝ) < x) (hu : x < (upper : ℝ))
    (count : TarskiCertificate Rat Rat Unit)
    (hc : Sturm.check Sturm.orderSign () head 1 (.finite lower) (.finite upper)
      1 count = true) (accepted : entry.check head lower upper query = true) :
    entry.value = (SignType.sign ((realPoly (query entry.key)).eval x) : Int) := by
  unfold check at accepted
  cases evidence : entry.evidence with
  | none =>
      rw [evidence] at accepted
      exact IntervalSign.sign_spec (query entry.key) lower upper x hl.le hu.le
        entry.value (of_decide_eq_true accepted)
  | some certificate =>
      rw [evidence] at accepted
      exact checked_one head (query entry.key) lower upper x hx hl hu
        count certificate entry.value hc accepted

/-- Prefer an exact enclosure sign, including singleton zero; otherwise retain the complete
rational Sturm query. Inconclusive intervals never assert equality to zero. -/
@[expose] def build {D : Type u} (domain : Sturm.PreparedDomain Rat)
    (lower upper : Rat) (key : D) (query : D → DensePoly Rat) : Entry D :=
  match IntervalSign.sign? (query key) lower upper with
  | some value => ⟨key, value, none⟩
  | none =>
      let evidence := Sturm.certifyPrepared () domain (query key)
      ⟨key, evidence.value, some evidence⟩

@[simp] theorem build_key {D : Type u} (domain : Sturm.PreparedDomain Rat)
    (lower upper : Rat) (key : D) (query : D → DensePoly Rat) :
    (build domain lower upper key query).key = key := by
  unfold build
  cases IntervalSign.sign? (query key) lower upper <;> rfl

theorem build_checked {D : Type u} (domain : Sturm.PreparedDomain Rat)
    (head : DensePoly Rat) (lower upper : Rat) (key : D) (query : D → DensePoly Rat)
    (accepted : Sturm.check Sturm.orderSign () head (query key)
      (.finite lower) (.finite upper) (Sturm.certifyPrepared () domain (query key)).value
      (Sturm.certifyPrepared () domain (query key)) = true) :
    (build domain lower upper key query).check head lower upper query = true := by
  cases sign : IntervalSign.sign? (query key) lower upper with
  | none => simpa only [build, sign, check] using accepted
  | some value => simp only [build, sign, check, decide_true]

end Entry

/-- Interpret a checked rational count-one interval through the shared Sturm
soundness theorem. No isolation or approximation is evaluated by this law. -/
private theorem checked_count (p : DensePoly Rat) (lower upper : Rat)
    (count : TarskiCertificate Rat Rat Unit)
    (accepted : Sturm.check Sturm.orderSign () p 1 (.finite lower) (.finite upper)
      1 count = true) :
    realPoly p ≠ 0 ∧
      (Tarski.rootsIn (realPoly p) (.finite (lower : ℝ)) (.finite (upper : ℝ))).card = 1 := by
  let f : Rat → ℝ := fun r => (r : ℝ)
  have hz : ∀ a : Rat, f a = 0 ↔ a = 0 := fun _ => Rat.cast_eq_zero
  have h1 : f 1 = 1 := by norm_num [f]
  have ha : ∀ a b : Rat, f (a + b) = f a + f b := Rat.cast_add
  have hs : ∀ a b : Rat, f (a - b) = f a - f b := Rat.cast_sub
  have hm : ∀ a b : Rat, f (a * b) = f a * f b := Rat.cast_mul
  have hn : ∀ n : Nat, f (n : Rat) = (n : ℝ) := by intro n; norm_num [f]
  have hsign : ∀ a : Rat, Sturm.orderSign a = (SignType.sign (f a) : Int) := by
    intro a
    rw [HexSturmMathlib.orderSign_eq]
    rcases lt_trichotomy a 0 with hneg | hzero | hpos
    · have hr : (a : ℝ) < 0 := by exact_mod_cast hneg
      simp [sign_neg hneg, sign_neg hr, f]
    · subst a; simp [f]
    · have hr : (0 : ℝ) < a := by exact_mod_cast hpos
      simp [sign_pos hpos, sign_pos hr, f]
  have sound := HexSturmMathlib.check_sound f hz h1 ha hs hm hn
    Sturm.orderSign hsign () p 1 (.finite lower) (.finite upper) 1 count accepted
  have meaning := sound.2
  change (1 : Int) = Tarski.rootSum (realPoly p) (realPoly 1)
    (.finite (lower : ℝ)) (.finite (upper : ℝ)) at meaning
  rw [show realPoly (1 : DensePoly Rat) = 1 from interpret_one f hz h1,
    Tarski.rootSum_one] at meaning
  exact ⟨sound.1.1, by exact_mod_cast meaning.symm⟩

/-- A frozen inner generator interval with its count-one certificate. It is
trusted only after checking containment in the original count-one interval. -/
structure Window where
  lower : Rat
  upper : Rat
  count : TarskiCertificate Rat Rat Unit

namespace Window

/-- Check the nested domain and the actual root count; the original generator
identity remains in the table's outer interval. -/
@[expose] def check (window : Window) (head : DensePoly Rat) (lower upper : Rat) : Bool :=
  decide (lower ≤ window.lower) && decide (window.upper ≤ upper) &&
    Sturm.check Sturm.orderSign () head 1 (.finite window.lower) (.finite window.upper)
      1 window.count

/-- Both checked count-one domains select the same real root. The tighter
bounds are a checked conclusion, not supplied containment of the selected root. -/
theorem bounds (window : Window) (head : DensePoly Rat) (lower upper : Rat)
    (count : TarskiCertificate Rat Rat Unit) (x : ℝ)
    (hx : (realPoly head).IsRoot x)
    (hl : (lower : ℝ) < x) (hu : x < (upper : ℝ))
    (outer : Sturm.check Sturm.orderSign () head 1 (.finite lower) (.finite upper)
      1 count = true) (accepted : window.check head lower upper = true) :
    (window.lower : ℝ) < x ∧ x < (window.upper : ℝ) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have hlo : (lower : ℝ) ≤ (window.lower : ℝ) := by exact_mod_cast accepted.1.1
  have hhi : (window.upper : ℝ) ≤ (upper : ℝ) := by exact_mod_cast accepted.1.2
  obtain ⟨nonzero, outerCard⟩ := checked_count head lower upper count outer
  obtain ⟨_, innerCard⟩ := checked_count head window.lower window.upper window.count accepted.2
  obtain ⟨root, roots⟩ := Finset.card_eq_one.mp outerCard
  have original : x ∈ Tarski.rootsIn (realPoly head)
      (.finite (lower : ℝ)) (.finite (upper : ℝ)) :=
    (Tarski.mem_rootsIn_iff _ nonzero _ _ x).mpr
      ⟨hx.eq_zero, (Tarski.inInterval_finite _ _ _).mpr ⟨hl, hu⟩⟩
  have originalRoot : x = root := by simpa only [roots, Finset.mem_singleton] using original
  obtain ⟨inner, innerRoots⟩ := Finset.card_eq_one.mp innerCard
  have member : inner ∈ Tarski.rootsIn (realPoly head)
      (.finite (window.lower : ℝ)) (.finite (window.upper : ℝ)) := by
    rw [innerRoots]; exact Finset.mem_singleton_self inner
  obtain ⟨zero, interval⟩ := (Tarski.mem_rootsIn_iff _ nonzero _ _ inner).mp member
  have contained := (Tarski.inInterval_finite _ _ _).mp interval
  have outerMember : inner ∈ Tarski.rootsIn (realPoly head)
      (.finite (lower : ℝ)) (.finite (upper : ℝ)) :=
    (Tarski.mem_rootsIn_iff _ nonzero _ _ inner).mpr ⟨zero,
      (Tarski.inInterval_finite _ _ _).mpr
        ⟨hlo.trans_lt contained.1, contained.2.trans_le hhi⟩⟩
  have innerRoot : inner = root := by simpa only [roots, Finset.mem_singleton] using outerMember
  rwa [originalRoot, ← innerRoot]

end Window

/-- Exact interval signs or rational queries for finitely many field values.
The same authenticated count-one interval is used for every entry. -/
structure Table (D : Type u) where
  head : DensePoly Rat
  lower : Rat
  upper : Rat
  count : TarskiCertificate Rat Rat Unit
  entries : List (Entry D)
  refinement : Option Window := none

namespace Table

variable {D : Type u} [DecidableEq D]

/-- The interval used by recorded signs. Original context bindings remain on
`head`/`lower`/`upper`, even when the sign evidence uses a checked inner window. -/
@[expose] def interval (table : Table D) : Window :=
  match table.refinement with
  | none => ⟨table.lower, table.upper, table.count⟩
  | some window => window

/-- Check the original root count, any frozen refinement and every sign. -/
@[expose] def check (table : Table D) (query : D → DensePoly Rat) : Bool :=
  let outer := Sturm.check Sturm.orderSign () table.head 1
    (.finite table.lower) (.finite table.upper) 1 table.count
  match table.refinement with
  | none => outer &&
      table.entries.all fun entry => entry.check table.head table.lower table.upper query
  | some window => outer && window.check table.head table.lower table.upper &&
      table.entries.all fun entry => entry.check table.head window.lower window.upper query

/-- Look up a sign only when the finite table records this key. -/
@[expose] def lookup? (table : Table D) (a : D) : Option Int :=
  (table.entries.find? (fun entry => decide (entry.key = a))).map Entry.value

/-- The semantic fallback supplies a total mathematical sign; executable
consumers can use `lookup?` to require a recorded finite hit. -/
@[expose] noncomputable def sign (table : Table D) (eval : D → ℝ) (a : D) : Int :=
  match table.lookup? a with
  | some value => value
  | none => (SignType.sign (eval a) : Int)

/-- Every stored entry of an accepted table has the sign at the original
selected root, including when its evidence uses a checked tighter window. -/
theorem entry_spec (table : Table D) (query : D → DensePoly Rat)
    (entry : Entry D) (member : entry ∈ table.entries) (x : ℝ)
    (hx : (realPoly table.head).IsRoot x)
    (hl : (table.lower : ℝ) < x) (hu : x < (table.upper : ℝ))
    (h : table.check query = true) :
    entry.value = (SignType.sign ((realPoly (query entry.key)).eval x) : Int) := by
  let interval := table.interval
  have checks : Sturm.check Sturm.orderSign () table.head 1
      (.finite interval.lower) (.finite interval.upper) 1 interval.count = true ∧
      (interval.lower : ℝ) < x ∧ x < (interval.upper : ℝ) ∧
      table.entries.all (fun entry => entry.check table.head interval.lower interval.upper query) = true := by
    cases refined : table.refinement with
    | none =>
        simp only [check, refined, Bool.and_eq_true] at h
        simpa only [interval, Table.interval, refined] using And.intro h.1
          (And.intro hl (And.intro hu h.2))
    | some window =>
        simp only [check, refined, Bool.and_eq_true] at h
        have bounds := window.bounds table.head table.lower table.upper table.count x
          hx hl hu h.1.1 h.1.2
        have count : Sturm.check Sturm.orderSign () table.head 1
            (.finite window.lower) (.finite window.upper) 1 window.count = true := by
          simp only [Window.check, Bool.and_eq_true] at h
          exact h.1.2.2
        simpa only [interval, Table.interval, refined] using And.intro count
          (And.intro bounds.1 (And.intro bounds.2 h.2))
  have checked := List.all_eq_true.mp checks.2.2.2 entry member
  exact entry.check_spec table.head interval.lower interval.upper query
    x hx checks.2.1 checks.2.2.1 interval.count checks.1 checked

/-- An accepted table agrees with the real sign for every field element,
including elements absent from the finite table. -/
theorem sign_spec (table : Table D) (query : D → DensePoly Rat)
    (eval : D → ℝ) (x : ℝ)
    (hx : (realPoly table.head).IsRoot x)
    (hl : (table.lower : ℝ) < x) (hu : x < (table.upper : ℝ))
    (heval : ∀ a, eval a = (realPoly (query a)).eval x)
    (h : table.check query = true) (a : D) :
    table.sign eval a = (SignType.sign (eval a) : Int) := by
  unfold sign lookup?
  cases hfind : table.entries.find? (fun entry => decide (entry.key = a)) with
  | some entry =>
      simp only [Option.map_some]
      have hm : entry ∈ table.entries := List.mem_of_find?_eq_some hfind
      have heq : entry.key = a := of_decide_eq_true
        (List.find?_some (p := fun row : Entry D => decide (row.key = a)) hfind)
      have hs := table.entry_spec query entry hm x hx hl hu h
      rw [heq, ← heval] at hs
      exact hs
  | none => simp only [Option.map_none]

/-- A checked finite hit has the actual sign; missing keys remain explicit. -/
theorem lookup_spec (table : Table D) (query : D → DensePoly Rat)
    (eval : D → ℝ) (x : ℝ)
    (hx : (realPoly table.head).IsRoot x)
    (hl : (table.lower : ℝ) < x) (hu : x < (table.upper : ℝ))
    (heval : ∀ a, eval a = (realPoly (query a)).eval x)
    (h : table.check query = true) (a : D) (value : Int)
    (hit : table.lookup? a = some value) :
    value = (SignType.sign (eval a) : Int) := by
  have hs := table.sign_spec query eval x hx hl hu heval h a
  unfold sign at hs
  rw [hit] at hs
  exact hs

/-- Prefer exact Horner signs on one prepared rational root interval and
retain a Sturm query when an enclosure is inconclusive. The result is
returned only after the complete literal table checker accepts it. -/
@[expose] def build (head : DensePoly Rat) (lower upper : Rat)
    (keys : List D) (query : D → DensePoly Rat) : Option (Table D) :=
  match Sturm.prepare Sturm.orderSign head (.finite lower) (.finite upper) with
  | none => none
  | some domain =>
      let count : TarskiCertificate Rat Rat Unit :=
        Sturm.certifyPrepared () domain (1 : DensePoly Rat)
      let entries : List (Entry D) := keys.map (Entry.build domain lower upper · query)
      let table : Table D := ⟨head, lower, upper, count, entries, none⟩
      if table.check query then some table else none

omit [DecidableEq D] in
/-- The producer does not bypass any query or binding checks. -/
theorem build_checked (head : DensePoly Rat) (lower upper : Rat)
    (keys : List D) (query : D → DensePoly Rat) (table : Table D)
    (h : build head lower upper keys query = some table) :
    table.check query = true := by
  unfold build at h
  split at h
  · simp at h
  · next domain hdomain =>
      dsimp only at h
      split at h
      · next hc =>
          cases Option.some.inj h
          exact hc
      · simp at h

omit [DecidableEq D] in
/-- The returned table retains the producer's original rational domain. -/
theorem build_bindings (head : DensePoly Rat) (lower upper : Rat)
    (keys : List D) (query : D → DensePoly Rat) (table : Table D)
    (produced : build head lower upper keys query = some table) :
    table.head = head ∧ table.lower = lower ∧ table.upper = upper := by
  unfold build at produced
  split at produced
  · contradiction
  · dsimp only at produced
    split at produced
    · cases Option.some.inj produced
      exact ⟨rfl, rfl, rfl⟩
    · contradiction

/-- Every requested key has a literal finite hit, including repeated keys. -/
theorem build_lookup (head : DensePoly Rat) (lower upper : Rat)
    (keys : List D) (query : D → DensePoly Rat) (table : Table D)
    (produced : build head lower upper keys query = some table)
    (key : D) (requested : key ∈ keys) : ∃ value, table.lookup? key = some value := by
  unfold build at produced
  split at produced
  · contradiction
  · rename_i domain prepared
    dsimp only at produced
    split at produced
    · cases Option.some.inj produced
      let entries := keys.map (Entry.build domain lower upper · query)
      have present : Entry.build domain lower upper key query ∈ entries :=
        List.mem_map.mpr ⟨key, requested, rfl⟩
      change ∃ value, (entries.find? (fun row => decide (row.key = key))).map Entry.value = some value
      cases found : entries.find? (fun row => decide (row.key = key)) with
      | none =>
        have missing := List.find?_eq_none.mp found _ present
        simp only [Entry.build_key, decide_true] at missing
        exact False.elim (missing trivial)
      | some row => exact ⟨row.value, rfl⟩
    · contradiction

omit [DecidableEq D] in
/-- Every rational count-one domain yields a checked table for every finite key list. -/
theorem build_success (head : DensePoly Rat) (lower upper : Rat)
    (keys : List D) (query : D → DensePoly Rat)
    (valid : HexSturmMathlib.Domain (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) head (.finite lower) (.finite upper))
    (card : (Tarski.rootsIn (realPoly head)
      (.finite (lower : ℝ)) (.finite (upper : ℝ))).card = 1) :
    ∃ table, build head lower upper keys query = some table := by
  classical
  let f : Rat → ℝ := fun r => (r : ℝ)
  have hz : ∀ a : Rat, f a = 0 ↔ a = 0 := fun _ => Rat.cast_eq_zero
  have h1 : f 1 = 1 := by norm_num [f]
  have ha : ∀ a b : Rat, f (a + b) = f a + f b := fun _ _ => Rat.cast_add _ _
  have hs : ∀ a b : Rat, f (a - b) = f a - f b := fun _ _ => Rat.cast_sub _ _
  have hm : ∀ a b : Rat, f (a * b) = f a * f b := fun _ _ => Rat.cast_mul _ _
  have hn : ∀ a : Rat, f (-a) = -f a := Rat.cast_neg
  have hi : ∀ a : Rat, f a⁻¹ = (f a)⁻¹ := Rat.cast_inv
  have hnat : ∀ n : Nat, f (n : Rat) = (n : ℝ) := by intro n; norm_num [f]
  have hsign : ∀ a : Rat, Sturm.orderSign a = (SignType.sign (f a) : Int) := by
    intro a
    rw [HexSturmMathlib.orderSign_eq]
    rcases lt_trichotomy a 0 with hneg | hzero | hpos
    · have hr : (a : ℝ) < 0 := by exact_mod_cast hneg
      simp [sign_neg hneg, sign_neg hr, f]
    · subst a; simp [f]
    · have hr : (0 : ℝ) < a := by exact_mod_cast hpos
      simp [sign_pos hpos, sign_pos hr, f]
  have signs := HexSturmMathlib.sign_spec f Sturm.orderSign hsign
  have available := (HexSturmMathlib.prepare_isSome f hz ha hs hm
    Sturm.orderSign (fun a => (signs a).2.1) (fun a => (signs a).2.2.1)
    h1 hn hi hnat (fun a => (signs a).1) head (.finite lower) (.finite upper)).mpr valid
  cases prepared : Sturm.prepare Sturm.orderSign head (.finite lower) (.finite upper) with
  | none => simp [prepared] at available
  | some domain =>
    obtain ⟨signEq, headEq, loEq, upperEq⟩ := Sturm.prepare_eq_some _ _ _ _ domain prepared
    have accepted (q : DensePoly Rat) := HexSturmMathlib.certifyPrepared_checks f hz ha hs hm
      Sturm.orderSign (fun a => (signs a).2.1) h1 hn hi (fun a => (signs a).1)
      (fun a => (signs a).2.2.2) () domain signEq q
    have bound (q : DensePoly Rat) : Sturm.check Sturm.orderSign () head q
        (.finite lower) (.finite upper) (Sturm.certifyPrepared () domain q).value
        (Sturm.certifyPrepared () domain q) = true := by
      simpa only [headEq, loEq, upperEq] using accepted q
    let count := Sturm.certifyPrepared () domain (1 : DensePoly Rat)
    have countValue : count.value = 1 := by
      have meaning := (HexSturmMathlib.check_sound f hz h1 ha hs hm hnat
        Sturm.orderSign hsign () head 1 (.finite lower) (.finite upper) count.value count (bound 1)).2
      change count.value = Tarski.rootSum (realPoly head) (realPoly 1)
        (.finite (lower : ℝ)) (.finite (upper : ℝ)) at meaning
      rw [show realPoly (1 : DensePoly Rat) = 1 from interpret_one f hz h1,
        Tarski.rootSum_one, card] at meaning
      exact meaning
    let entries : List (Entry D) := keys.map (Entry.build domain lower upper · query)
    let table : Table D := ⟨head, lower, upper, count, entries, none⟩
    have checked : table.check query = true := by
      simp only [table, Table.check, Bool.and_eq_true]
      refine ⟨?_, List.all_eq_true.mpr ?_⟩
      · rw [← countValue]; exact bound 1
      · intro entry mem
        obtain ⟨key, _, same⟩ := List.mem_map.mp mem
        subst entry
        exact Entry.build_checked domain head lower upper key query (bound (query key))
    refine ⟨table, ?_⟩
    unfold build
    rw [prepared]
    change (if table.check query then some table else none) = some table
    simp only [checked, ite_eq_left]

/-- Rebuild signs on one proposed contained window. The original root interval
and count remain unchanged. A malformed window or query rejects; replay does
not run the preparation or certificate producer. -/
@[expose] def refine (table : Table D) (lower upper : Rat)
    (query : D → DensePoly Rat) : Option (Table D) :=
  match Sturm.prepare Sturm.orderSign table.head (.finite lower) (.finite upper) with
  | none => none
  | some domain =>
      let window : Window := ⟨lower, upper, Sturm.certifyPrepared () domain 1⟩
      let entries := table.entries.map fun entry => Entry.build domain lower upper entry.key query
      let result := {table with entries, refinement := some window}
      if result.check query then some result else none

/-- Successful refinement passes the same independent table checker. -/
theorem refine_checked (table : Table D) (lower upper : Rat)
    (query : D → DensePoly Rat) (result : Table D)
    (h : table.refine lower upper query = some result) : result.check query = true := by
  unfold refine at h
  cases prepared : Sturm.prepare Sturm.orderSign table.head (.finite lower) (.finite upper) with
  | none => rw [prepared] at h; contradiction
  | some domain =>
      rw [prepared] at h
      dsimp only at h
      split at h
      · cases Option.some.inj h
        assumption
      · contradiction

/-- Refinement preserves the original selected-domain binding and every key in
its exact entry order; only the sign evidence window is replaced. -/
theorem refine_bindings (table : Table D) (lower upper : Rat)
    (query : D → DensePoly Rat) (result : Table D)
    (h : table.refine lower upper query = some result) :
    result.head = table.head ∧ result.lower = table.lower ∧ result.upper = table.upper ∧
      result.count = table.count ∧ result.entries.map Entry.key = table.entries.map Entry.key := by
  unfold refine at h
  cases prepared : Sturm.prepare Sturm.orderSign table.head (.finite lower) (.finite upper) with
  | none => rw [prepared] at h; contradiction
  | some domain =>
      rw [prepared] at h
      dsimp only at h
      split at h
      · cases Option.some.inj h
        refine ⟨rfl, rfl, rfl, rfl, ?_⟩
        simp only [List.map_map, Function.comp_def, Entry.build_key]
      · contradiction

end Table

end Hex.RCF.RealCoefficients.LiteralSign

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Soundness
public import HexRealRootsMathlib.RealClosed

public section

/-! Rational Tarski queries for signs at a selected literal real root. -/

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

/-- A literal sign for one value of a fixed real number field. The query
polynomial is determined by the key's rational coordinates, not copied from
the certificate. -/
structure Entry (D : Type u) where
  key : D
  value : Int
  evidence : TarskiCertificate Rat Rat Unit

/-- Exact rational queries supporting finitely many field signs. The same
count-one interval is used for every entry. -/
structure Table (D : Type u) where
  head : DensePoly Rat
  lower : Rat
  upper : Rat
  count : TarskiCertificate Rat Rat Unit
  entries : List (Entry D)

namespace Table

variable {D : Type u} [DecidableEq D]

/-- Check the root count and every sign in the literal table. -/
@[expose] def check (table : Table D) (query : D → DensePoly Rat) : Bool :=
  Sturm.check Sturm.orderSign () table.head 1
    (.finite table.lower) (.finite table.upper) 1 table.count &&
  table.entries.all fun entry =>
    Sturm.check Sturm.orderSign () table.head (query entry.key)
      (.finite table.lower) (.finite table.upper) entry.value entry.evidence

/-- Look up a sign only when the finite table records this key. -/
@[expose] def lookup? (table : Table D) (a : D) : Option Int :=
  (table.entries.find? (fun entry => decide (entry.key = a))).map Entry.value

/-- The semantic fallback supplies a total mathematical sign; executable
consumers can use `lookup?` to require a recorded finite hit. -/
@[expose] noncomputable def sign (table : Table D) (eval : D → ℝ) (a : D) : Int :=
  match table.lookup? a with
  | some value => value
  | none => (SignType.sign (eval a) : Int)

/-- An accepted table agrees with the real sign for every field element,
including elements absent from the finite table. -/
theorem sign_spec (table : Table D) (query : D → DensePoly Rat)
    (eval : D → ℝ) (x : ℝ)
    (hx : (realPoly table.head).IsRoot x)
    (hl : (table.lower : ℝ) < x) (hu : x < (table.upper : ℝ))
    (heval : ∀ a, eval a = (realPoly (query a)).eval x)
    (h : table.check query = true) (a : D) :
    table.sign eval a = (SignType.sign (eval a) : Int) := by
  simp only [check, Bool.and_eq_true] at h
  unfold sign lookup?
  cases hfind : table.entries.find? (fun entry => decide (entry.key = a)) with
  | some entry =>
      simp only [hfind, Option.map_some]
      have hm : entry ∈ table.entries := List.mem_of_find?_eq_some hfind
      have heq : entry.key = a := of_decide_eq_true
        (List.find?_some (p := fun row : Entry D => decide (row.key = a)) hfind)
      have hquery := List.all_eq_true.mp h.2 entry hm
      have hs := checked_one table.head (query entry.key) table.lower table.upper
        x hx hl hu table.count entry.evidence entry.value h.1 hquery
      rw [heq, ← heval] at hs
      exact hs
  | none => simp only [hfind, Option.map_none]

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

/-- Reuse one prepared rational root interval for all requested field signs.
The result is returned only after the exact table checker accepts it. -/
@[expose] def build (head : DensePoly Rat) (lower upper : Rat)
    (keys : List D) (query : D → DensePoly Rat) : Option (Table D) :=
  match Sturm.prepare Sturm.orderSign head (.finite lower) (.finite upper) with
  | none => none
  | some domain =>
      let count : TarskiCertificate Rat Rat Unit :=
        Sturm.certifyPrepared () domain (1 : DensePoly Rat)
      let entries : List (Entry D) := keys.map fun key =>
        let evidence : TarskiCertificate Rat Rat Unit :=
          Sturm.certifyPrepared () domain (query key)
        (⟨key, evidence.value, evidence⟩ : Entry D)
      let table : Table D := ⟨head, lower, upper, count, entries⟩
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
      let evidence := Sturm.certifyPrepared () domain (query key)
      let entry : Entry D := ⟨key, evidence.value, evidence⟩
      have present : entry ∈ keys.map (fun key =>
          let evidence := Sturm.certifyPrepared () domain (query key)
          (⟨key, evidence.value, evidence⟩ : Entry D)) := List.mem_map.mpr ⟨key, requested, rfl⟩
      unfold lookup?
      cases found : (keys.map (fun key =>
          let evidence := Sturm.certifyPrepared () domain (query key)
          (⟨key, evidence.value, evidence⟩ : Entry D))).find?
            (fun row => decide (row.key = key)) with
      | none =>
        have missing := List.find?_eq_none.mp found entry present
        simp [entry] at missing
      | some row => exact ⟨row.value, by simp only [Option.map_some]⟩
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
    let entries : List (Entry D) := keys.map fun key =>
      let evidence := Sturm.certifyPrepared () domain (query key)
      ⟨key, evidence.value, evidence⟩
    let table : Table D := ⟨head, lower, upper, count, entries⟩
    have checked : table.check query = true := by
      simp only [Table.check, Bool.and_eq_true]
      refine ⟨?_, List.all_eq_true.mpr ?_⟩
      · change Sturm.check Sturm.orderSign () head 1 (.finite lower) (.finite upper) 1 count = true
        rw [← countValue]; exact bound 1
      · intro entry mem
        obtain ⟨key, _, same⟩ := List.mem_map.mp mem
        subst entry
        exact bound (query key)
    refine ⟨table, ?_⟩
    unfold build
    rw [prepared]
    change (if table.check query then some table else none) = some table
    simp only [checked, ite_eq_left]

end Table

end Hex.RCF.RealCoefficients.LiteralSign

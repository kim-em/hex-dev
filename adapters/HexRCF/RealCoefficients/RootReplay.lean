/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.RootTable

public section
namespace Hex.RCF.RealCoefficients.RootReplay
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- The exact head and domain to which a frozen root table is bound. Full
derivative queries come from the head, never from a supplied query vector. -/
@[expose] def subject (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value) :
    RawDescriptor parent.Value Signature := ⟨parent.signature, p, lower, upper, [], []⟩

/-- Accepted finite extraction from a single supplied replay. The stored
equation is the owner's literal extraction boundary, not native production.
It deliberately makes no unproved coverage or mathematical-order assertion. -/
structure Result (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value) where
  replay : SignDet.Replay parent.Value Signature
  checked : replay.check parent.sign parent.signature p lower upper
    ((subject p lower upper).full []).queries = true
  roots : List (Descriptor parent.Value Signature parent.sign parent.signature)
  extracted : Descriptor.rootsFrom parent.sign parent.signature (subject p lower upper)
    replay (replay.table checked).rows.toList = .ok roots

/-- Restore the canonical result fields without repeating graph validation. -/
@[expose] def fromTable (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (result : RootTable.Result parent.sign parent.signature p lower upper) : Result p lower upper :=
  ⟨result.tree, result.checked, result.roots, result.extracted⟩

/-- Extract the accepted full table using the shared operation-parametric core. -/
@[expose] def extract (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (replay : SignDet.Replay parent.Value Signature)
    (checked : replay.check parent.sign parent.signature p lower upper
      ((subject p lower upper).full []).queries = true) :=
  RootTable.extract parent.sign parent.signature p lower upper replay checked

theorem extract_eq (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (replay : SignDet.Replay parent.Value Signature)
    (checked : replay.check parent.sign parent.signature p lower upper
      ((subject p lower upper).full []).queries = true) :
    extract p lower upper replay checked =
      Descriptor.rootsFrom parent.sign parent.signature (subject p lower upper)
        replay (replay.table checked).rows.toList :=
  RootTable.extract_eq _ _ _ _ _ _ _

/-- Preflight original supplied guards and restore one frozen full root table.
Predecessor codecs/arithmetic require checked finite assembly for quotation. -/
@[expose] def read (value : ValueCodec parent.Value) (guards : List parent.Value)
    (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (graph : Codec.Json) : Except Replay.Error (Result p lower upper) :=
  (RootTable.read value Signature.codec parent.sign parent.signature guards p lower upper graph).map
    (fromTable p lower upper)

/-- Five equal supplied operations avoid native predecessor arithmetic during
finite replay and full derivative extraction. Literal data and all failures
are preserved when transporting the checked result back to canonical indices. -/
@[expose] def readWith (value : ValueCodec parent.Value) (guards : List parent.Value)
    (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (pOne : One parent.Value) (pAdd : Add parent.Value) (pSub : Sub parent.Value)
    (pMul : Mul parent.Value) (pNat : NatCast parent.Value)
    (ho : pOne = Tower.instOneValue parent) (ha : pAdd = Tower.instAddValue parent)
    (hs : pSub = Tower.instSubValue parent) (hm : pMul = Tower.instMulValue parent)
    (hn : pNat = Tower.instNatCastValue parent) (graph : Codec.Json) :
    Except Replay.Error (Result p lower upper) :=
  (@RootTable.readWith parent.Value Signature (Tower.instZeroValue parent)
    (Tower.instDecidableEqValue parent) inferInstance (Tower.instOneValue parent)
    (Tower.instAddValue parent) (Tower.instSubValue parent) (Tower.instMulValue parent)
    (Tower.instNatCastValue parent) value Signature.codec pOne pAdd pSub pMul pNat ho ha hs hm hn
    parent.sign parent.signature guards p lower upper graph).map (fromTable p lower upper)

theorem readWith_eq (value : ValueCodec parent.Value) (guards : List parent.Value)
    (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (pOne : One parent.Value) (pAdd : Add parent.Value) (pSub : Sub parent.Value)
    (pMul : Mul parent.Value) (pNat : NatCast parent.Value)
    (ho : pOne = Tower.instOneValue parent) (ha : pAdd = Tower.instAddValue parent)
    (hs : pSub = Tower.instSubValue parent) (hm : pMul = Tower.instMulValue parent)
    (hn : pNat = Tower.instNatCastValue parent) (graph : Codec.Json) :
    readWith value guards p lower upper pOne pAdd pSub pMul pNat ho ha hs hm hn graph =
      read value guards p lower upper graph := by
  unfold readWith read
  rw [@RootTable.readWith_eq parent.Value Signature (Tower.instZeroValue parent)
    (Tower.instDecidableEqValue parent) inferInstance (Tower.instOneValue parent)
    (Tower.instAddValue parent) (Tower.instSubValue parent) (Tower.instMulValue parent)
    (Tower.instNatCastValue parent) value Signature.codec pOne pAdd pSub pMul pNat
    ho ha hs hm hn parent.sign parent.signature guards p lower upper graph]

theorem read_guards (value : ValueCodec parent.Value) (guards : List parent.Value)
    (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (graph : Codec.Json) (result : Result p lower upper)
    (accepted : read value guards p lower upper graph = .ok result) :
    guards.all (fun d => Decidable.decide (d ≠ 0)) = true := by
  cases valid : guards.all (fun d => Decidable.decide (d ≠ 0))
  · simp only [read, RootTable.read, valid, Bool.false_eq_true, ite_false, bind, Except.bind, Except.map] at accepted
    contradiction
  · rfl

theorem read_domains (original : Model parent ℝ) (value : ValueCodec parent.Value)
    (guards : List parent.Value) (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (graph : Codec.Json) (result : Result p lower upper)
    (accepted : read value guards p lower upper graph = .ok result) :
    ∀ d ∈ guards, original.value d ≠ 0 := by
  intro d member zero
  have valid := read_guards value guards p lower upper graph result accepted
  exact (of_decide_eq_true (List.all_eq_true.mp valid d member))
    ((original.zero_iff d).mp zero)

theorem read_zero (value : ValueCodec parent.Value) (guards : List parent.Value)
    (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (graph : Codec.Json) (d : parent.Value) (member : d ∈ guards) (zero : d = 0) :
    read value guards p lower upper graph = .error .divisor := by
  have bad : guards.all (fun d => Decidable.decide (d ≠ 0)) = false := by
    apply Bool.eq_false_iff.mpr
    intro valid
    exact (of_decide_eq_true (List.all_eq_true.mp valid d member)) zero
  simp only [read, RootTable.read, bad, Bool.false_eq_true, ite_false, bind, Except.bind, Except.map]
  rfl

/-- The checked extraction retains every table word, including difficult rows. -/
theorem Result.words {p : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (result : Result p lower upper) :
    (result.roots.map fun d => d.raw.signs).Perm
      ((result.replay.table result.checked).rows.toList.map Prod.fst) :=
  Descriptor.rootsFrom_perm _ _ _ _ result.extracted

/-- No full derivative word occurs twice in the extracted list. This is a
finite table invariant, separate from interpreted-root Nodup. -/
theorem Result.unique_words {p : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (result : Result p lower upper) : (result.roots.map fun d => d.raw.signs).Nodup :=
  result.words.nodup_iff.mpr (result.replay.table result.checked).distinct

/-- Every descriptor retains the entire original domain and full derivative slots. -/
theorem Result.fields {p : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (result : Result p lower upper) :
    ∀ d ∈ result.roots, ∃ word, d.raw = (subject p lower upper).full word :=
  Descriptor.rootsFrom_raw _ _ _ _ result.extracted

/-- Finite comparator order is checked; this alone is not mathematical ordering. -/
theorem Result.sorted {p : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (result : Result p lower upper) :
    result.roots.Pairwise (fun a b => a.fullOrder b = some .lt) :=
  Descriptor.rootsFrom_sorted _ _ _ _ result.extracted

open HexPolyMathlib.Interpret HexRealRootsMathlib in
/-- The supplied replay proves the original open query domain, even for an
empty table. It does not remove half-open source-domain guard atoms. -/
theorem Result.domain {p : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (result : Result p lower upper) (original : Model parent ℝ) :
    HexSturmMathlib.Domain original.value original.zero_iff p lower upper :=
  result.replay.check_domain original.value original.zero_iff original.one original.add
    original.sub original.mul original.nat parent.sign original.sign parent.signature
    p lower upper _ result.checked

open HexPolyMathlib.Interpret HexRealRootsMathlib in
/-- Every emitted descriptor denotes an actual root of the bound polynomial
in the bound interval. Completeness and Nodup need the owner's supplied-replay
coverage export; no native producer equation is assumed here. -/
theorem Result.root_spec {p : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (result : Result p lower upper) (original : Model parent ℝ)
    (d : Descriptor parent.Value Signature parent.sign parent.signature)
    (member : d ∈ result.roots) :
    d.root original.value original.zero_iff original.one original.add original.sub
      original.mul original.nat original.sign ∈
        Tarski.rootsIn (interpret original.value original.zero_iff p)
          (lower.map original.value) (upper.map original.value) := by
  obtain ⟨word, same⟩ := result.fields d member
  have literal : d.raw.head = p ∧ d.raw.lower = lower ∧ d.raw.upper = upper := by
    rw [same]
    exact ⟨rfl, rfl, rfl⟩
  simpa only [literal.1, literal.2.1, literal.2.2] using
    (d.root_spec original.value original.zero_iff original.one original.add original.sub
      original.mul original.nat original.sign).1

end Hex.RCF.RealCoefficients.RootReplay

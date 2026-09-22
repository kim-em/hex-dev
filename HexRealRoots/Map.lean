/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.Tarski
public import HexPoly.Interpret

public section
namespace Hex

variable {D : Type u} {E : Type v} [Zero D] [DecidableEq D] [Zero E] [DecidableEq E]
variable (f : D → E) (hz : ∀ x, f x = 0 ↔ x = 0)

/-- Apply a zero-reflecting coefficient map to the supplied scales and quotient. -/
@[expose] def RemainderStep.map (s : RemainderStep D) : RemainderStep E :=
  ⟨f s.leftScale, DensePoly.Interpret.map f hz s.quotient, f s.rightScale⟩

/-- Map the supplied remainder evidence without repeating polynomial division.
Stored degrees are retained; zero reflection preserves every polynomial degree. -/
@[expose] def SignedRemainderChain.map (cert : SignedRemainderChain D) : SignedRemainderChain E where
  chain := Hex.Array.map' (DensePoly.Interpret.map f hz) cert.chain
  degrees := cert.degrees
  initial := cert.initial.map f hz
  steps := Hex.Array.map' (RemainderStep.map f hz) cert.steps
  terminal := cert.terminal.map fun (a, q) => (f a, DensePoly.Interpret.map f hz q)

namespace SignedRemainderChain
open DensePoly.Interpret

private theorem map_entry (cert : SignedRemainderChain D) (i : Nat) :
    (cert.map f hz).chain.getD i 0 = DensePoly.Interpret.map f hz (cert.chain.getD i 0) := by
  by_cases hi : i < cert.chain.size
  · have hi' : i < (cert.map f hz).chain.size := by simpa only [map, Hex.Array.size_map'] using hi
    rw [← Array.getElem_eq_getD (h := hi') 0, ← Array.getElem_eq_getD (h := hi) 0]
    simp only [map, Hex.Array.getElem_map']
  · have hi' : ¬ i < (cert.map f hz).chain.size := by simpa only [map, Hex.Array.size_map'] using hi
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    exact (map_zero_poly f hz).symm

variable [Add D] [Add E] [Sub D] [Sub E] [Mul D] [Mul E]
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b) (hm : ∀ a b, f (a * b) = f a * f b)
variable (sign : D → Int) (sign' : E → Int) (hsgn : ∀ a, sign' (f a) = sign a)

omit [Add D] [Add E] [Mul D] [Mul E] in
include hs in
private theorem map_subIsZero (p q : DensePoly D) :
    subIsZero (DensePoly.Interpret.map f hz p) (DensePoly.Interpret.map f hz q) = subIsZero p q := by
  rw [subIsZero, ← map_sub f hz hs, map_isZero]
  rfl

include ha hs hm hsgn in
/-- Scalar operation and sign preservation transport each checked recurrence. -/
theorem map_checkStep (a b c : DensePoly D) (s : RemainderStep D) :
    checkStep sign' (DensePoly.Interpret.map f hz a) (DensePoly.Interpret.map f hz b)
      (DensePoly.Interpret.map f hz c) (s.map f hz) = checkStep sign a b c s := by
  simp only [checkStep, RemainderStep.map, hsgn, ← map_scale f hz hm, ← map_mul f hz ha hm,
    ← map_sub f hz hs, map_subIsZero f hz hs]

variable [NatCast D] [NatCast E] (hn : ∀ n : Nat, f (n : D) = (n : E))

include ha hs hm hn hsgn in
/-- An accepted literal chain remains accepted after a zero-reflecting map
preserving scalar operations and signs. The map need not be injective. -/
theorem map_checks (p g : DensePoly D) (cert : SignedRemainderChain D)
    (h : check sign p g cert = true) :
    check sign' (DensePoly.Interpret.map f hz p) (DensePoly.Interpret.map f hz g)
      (cert.map f hz) = true := by
  have hsize : (cert.map f hz).chain.size = cert.chain.size := by simp only [map, Hex.Array.size_map']
  have hsrc := h
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hsrc
  obtain ⟨hp, hnz, hb, hh, hdeg, hnonzero, hdesc, hl, hr, hi, ht⟩ := hsrc
  simp only [check, hsize, map_size, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨?_, hnz, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [map_isZero] using hp
  · simp only [map, Hex.Array.map'_eq_map, Array.getElem?_map, hh, Option.map_some]
  · simpa only [map, Hex.Array.map'_eq_map, Array.map_map, Function.comp_def, map_degree] using hdeg
  · rw [← hsize]
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro q hq
    simp only [map, Hex.Array.map'_eq_map, Array.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    simpa only [map_isZero] using Array.all_eq_true_iff_forall_mem.mp hnonzero r hr
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro i hi
    simpa only [map_entry, map_size] using Array.all_eq_true_iff_forall_mem.mp hdesc i hi
  · simpa only [map, RemainderStep.map, hsgn] using hl
  · simpa only [map, RemainderStep.map, hsgn] using hr
  · rw [map_entry]
    simpa only [map, RemainderStep.map, ← map_scale f hz hm,
      ← map_derivative f hz hn hm, ← map_mul f hz ha hm, ← map_add f hz ha,
      map_subIsZero f hz hs] using hi
  · by_cases hsingle : cert.chain.size = 1
    · simp only [hsingle, ↓reduceIte, Bool.and_eq_true] at ht ⊢
      constructor
      · simpa only [map, Array.isEmpty, Hex.Array.size_map'] using ht.1
      · simpa only [map, Option.isNone_map] using ht.2
    · simp only [hsingle, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at ht ⊢
      refine ⟨?_, ?_, ?_⟩
      · simpa only [map, Hex.Array.size_map'] using ht.1
      · apply Array.all_eq_true_iff_forall_mem.mpr
        intro i hi
        have hidx : i < cert.steps.size := by simpa only [map, Hex.Array.size_map'] using Array.mem_range.mp hi
        have hidx' : i < (cert.map f hz).steps.size := by simpa only [map, Hex.Array.size_map'] using hidx
        have hh := Array.all_eq_true_iff_forall_mem.mp ht.2.1 i (Array.mem_range.mpr hidx)
        rw [map_entry, map_entry, map_entry, ← Array.getElem_eq_getD (h := hidx') ⟨0, 0, 0⟩]
        simpa only [map, Hex.Array.getElem_map', map_checkStep f hz ha hs hm sign sign' hsgn,
          ← Array.getElem_eq_getD (h := hidx) ⟨0, 0, 0⟩] using hh
      · cases he : cert.terminal with
        | none => simp only [he, Bool.false_eq_true] at ht; exact ht.2.2.elim
        | some pair =>
          obtain ⟨a, q⟩ := pair
          rw [show (cert.map f hz).terminal = some (f a, DensePoly.Interpret.map f hz q) by
            simp only [map, he, Option.map_some]]
          change (decide (sign' (f a) = 1) && subIsZero
            (DensePoly.scale (f a) ((cert.map f hz).chain.getD (cert.chain.size - 2) 0))
            (DensePoly.Interpret.map f hz q * (cert.map f hz).chain.getD (cert.chain.size - 1) 0)) = true
          rw [map_entry, map_entry]
          simpa only [he, hsgn, ← map_scale f hz hm,
            ← map_mul f hz ha hm, map_subIsZero f hz hs] using ht.2.2

end SignedRemainderChain

/-- Map finite endpoint values, retaining the two infinities. -/
@[expose] def Endpoint.map {A : Type w} {B : Type w'} (k : A → B) : Endpoint A → Endpoint B
  | .negInf => .negInf
  | .finite a => .finite (k a)
  | .posInf => .posInf

/-- Transport all literal polynomial and endpoint data in a certificate.
The context, signs, variations, and query value are retained exactly. -/
@[expose] def TarskiCertificate.map {A : Type w} {B : Type w'} {Ctx : Type w''}
    (k : A → B) (cert : TarskiCertificate D A Ctx) : TarskiCertificate E B Ctx where
  context := cert.context
  head := DensePoly.Interpret.map f hz cert.head
  queryPoly := DensePoly.Interpret.map f hz cert.queryPoly
  lower := cert.lower.map k
  upper := cert.upper.map k
  squarefree := cert.squarefree.map f hz
  remainders := cert.remainders.map f hz
  lowerSigns := cert.lowerSigns
  upperSigns := cert.upperSigns
  lowerVariations := cert.lowerVariations
  upperVariations := cert.upperVariations
  value := cert.value

namespace TarskiCertificate
open DensePoly.Interpret

variable {A : Type w} {B : Type w'} (k : A → B)
variable (sign : D → Int) (sign' : E → Int) (hsgn : ∀ a, sign' (f a) = sign a)
variable (ends : EndpointSigns D A) (ends' : EndpointSigns E B)
variable (hcmp : ∀ a b, ends'.compare (k a) (k b) = ends.compare a b)
variable (heval : ∀ p a, ends'.evalSign (DensePoly.Interpret.map f hz p) (k a) = ends.evalSign p a)

include hsgn heval in
theorem map_signAt (p : DensePoly D) (a : Endpoint A) :
    (a.map k).signAt sign' ends' (DensePoly.Interpret.map f hz p) = a.signAt sign ends p := by
  cases a <;> simp only [Endpoint.map, Endpoint.signAt, map_leading, map_degree, hsgn, heval]

include hcmp heval in
private theorem map_checkEndpoints (p : DensePoly D) (a b : Endpoint A) :
    checkEndpoints ends' (DensePoly.Interpret.map f hz p) (a.map k) (b.map k) =
      checkEndpoints ends p a b := by
  cases a <;> cases b <;>
    simp only [checkEndpoints, Endpoint.map, Endpoint.lt, Endpoint.nonvanishing, map_isZero, hcmp, heval]

include hsgn heval in
theorem map_signs (chain : Array (DensePoly D)) (a : Endpoint A) :
    signs sign' ends' (Hex.Array.map' (DensePoly.Interpret.map f hz) chain) (a.map k) =
      signs sign ends chain a := by
  simp only [signs, Hex.Array.map'_eq_map, Array.map_map, Function.comp_def,
    map_signAt f hz k sign sign' hsgn ends ends' heval]

private theorem map_lastIsConstant (cert : SignedRemainderChain D) :
    SignedRemainderChain.lastIsConstant (cert.map f hz) = SignedRemainderChain.lastIsConstant cert := by
  simp only [SignedRemainderChain.lastIsConstant, show (cert.map f hz).chain.size = cert.chain.size by
    simp only [SignedRemainderChain.map, Hex.Array.size_map'], SignedRemainderChain.map_entry, map_size]

variable [One D] [One E] [Add D] [Add E] [Sub D] [Sub E] [Mul D] [Mul E] [NatCast D] [NatCast E]
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b) (hm : ∀ a b, f (a * b) = f a * f b)
variable (h1 : f 1 = 1) (hn : ∀ n : Nat, f (n : D) = (n : E))

include ha hs hm h1 hn hsgn hcmp heval in
/-- Transport acceptance, including all literal bindings, through coefficient
and endpoint maps. No injectivity or producer provenance is required. -/
theorem map_checks {Ctx : Type w''} [DecidableEq Ctx] [DecidableEq A] [DecidableEq B]
    (context : Ctx) (p g : DensePoly D) (a b : Endpoint A) (value : Int)
    (cert : TarskiCertificate D A Ctx) (h : check sign ends context p g a b value cert = true) :
    check sign' ends' context (DensePoly.Interpret.map f hz p) (DensePoly.Interpret.map f hz g)
      (a.map k) (b.map k) value (cert.map f hz k) = true := by
  simp only [check_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hctx, hp, hg, hl, hu, hv, hends, hsf, hc, hr, hls, hus, hbl, hbu, hvl, hvu, hval⟩ := h
  have hsf' := SignedRemainderChain.map_checks f hz ha hs hm sign sign' hsgn hn p 1 cert.squarefree hsf
  rw [map_one f hz h1] at hsf'
  have hr' := SignedRemainderChain.map_checks f hz ha hs hm sign sign' hsgn hn p g cert.remainders hr
  simp only [check_eq, map, hp, hg, hl, hu, hctx, hv, map_checkEndpoints f hz k ends ends' hcmp heval,
    hends, hsf', hr', map_lastIsConstant, hc, decide_true, Bool.true_and]
  simp only [SignedRemainderChain.map, map_signs f hz k sign sign' hsgn ends ends' heval,
    hls, hus, hvl, hvu, Bool.and_eq_true, decide_eq_true_eq, and_assoc, true_and]
  exact ⟨by simpa only [hls] using hbl, by simpa only [hus] using hbu,
    by simpa only [hvl, hls, hvu, hus] using hval⟩

end TarskiCertificate
end Hex

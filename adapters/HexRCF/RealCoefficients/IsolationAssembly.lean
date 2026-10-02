/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Isolations
public import HexRCF.RealCoefficients.IsolationCheck
public section
namespace Hex.RCF.RealCoefficients.IsolationReplay
open HexPolyMathlib.Interpret
variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
  [Neg E] [Inv E] [NatCast E]
variable (f : E → ℝ) (hz : ∀ a, f a = 0 ↔ a = 0)
  (h1 : f 1 = 1) (ha : ∀ a b, f (a+b) = f a + f b)
  (hs : ∀ a b, f (a-b) = f a - f b) (hm : ∀ a b, f (a*b) = f a * f b)
  (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
  (hnat : ∀ n : Nat, f (n : E) = (n : ℝ))
  (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
  (point : Dyadic → E)
include h1 ha hs hm hn hi hnat hsign
private theorem countRetarget {Ctx : Type v} [DecidableEq Ctx]
    (context : Ctx) (domain : Sturm.PreparedDomain E)
    (binding : domain.sign = sign)
    (lower upper : Endpoint E)
    (valid : HexSturmMathlib.Domain f hz domain.head lower upper) :
    Sturm.check sign context domain.head 1 lower upper
      (TarskiCertificate.fromChains sign
        (EndpointSigns.ofSign sign) context domain.head 1 lower upper
        domain.squarefree domain.squarefree).value
      (TarskiCertificate.fromChains sign
        (EndpointSigns.ofSign sign) context domain.head 1 lower upper
        domain.squarefree domain.squarefree) = true := by
  have signs := HexSturmMathlib.sign_spec f sign hsign
  have available := (HexSturmMathlib.withEndpoints_isSome f hz
    ha hs hm
    sign (fun a => (signs a).2.1) (fun a => (signs a).2.2.1)
    h1 hn hi
    hnat (fun a => (signs a).1) domain binding lower upper).mpr valid
  cases retargeted : domain.withEndpoints? lower upper with
  | none => simp [retargeted] at available
  | some next =>
    obtain ⟨nextSign, head, chain, lo, upperEq⟩ :=
      Sturm.PreparedDomain.withEndpoints_bindings domain next lower upper retargeted
    have accepted := HexSturmMathlib.certifyCountPrepared_checks f hz
      ha hs hm
      sign (fun a => (signs a).2.1) h1
      hn hi (fun a => (signs a).1)
      (fun a => (signs a).2.2.2) context next (nextSign.trans binding)
    simpa only [Sturm.countPrepared, Sturm.certifyCountPrepared, nextSign, binding,
      head, chain, lo, upperEq, TarskiCertificate.fromChains] using accepted

private theorem countValue {Ctx : Type v} [DecidableEq Ctx]
    (context : Ctx) (domain : Sturm.PreparedDomain E)
    (binding : domain.sign = sign)
    (lower upper : Endpoint E)
    (valid : HexSturmMathlib.Domain f hz domain.head lower upper) :
    (TarskiCertificate.fromChains sign
      (EndpointSigns.ofSign sign) context domain.head 1 lower upper
      domain.squarefree domain.squarefree).value =
      (HexRealRootsMathlib.Tarski.rootsIn (interpret f hz domain.head)
        (lower.map f) (upper.map f)).card := by
  have checked := countRetarget f hz h1 ha hs hm hn hi hnat sign hsign context domain binding lower upper valid
  have meaning := (HexSturmMathlib.check_sound f hz
    h1 ha
    hs hm hnat
    sign hsign context domain.head 1 lower upper _ _ checked).2
  simpa only [interpret_one f hz h1,
    HexRealRootsMathlib.Tarski.rootSum_one] using meaning

/-- Valid whole-line and interval domains, separation and exact root counts
make the actual shared-chain isolation producer succeed. -/
theorem build_success {Ctx : Type v} [DecidableEq Ctx]
    (context : Ctx) (head : DensePoly E) (isolations : IsolationCert)
    (whole : HexSturmMathlib.Domain f hz head .negInf .posInf)
    (gaps : isolations.checkGaps = true)
    (totalCard : (HexRealRootsMathlib.Tarski.rootsIn (interpret f hz head)
      .negInf .posInf).card = isolations.intervals.size)
    (intervalDomain : ∀ i : Fin isolations.intervals.size,
      HexSturmMathlib.Domain f hz head
        (.finite (point isolations.intervals[i].lower))
        (.finite (point isolations.intervals[i].upper)))
    (intervalCard : ∀ i : Fin isolations.intervals.size,
      (HexRealRootsMathlib.Tarski.rootsIn (interpret f hz head)
        ((Endpoint.finite (point isolations.intervals[i].lower)).map f)
        ((Endpoint.finite (point isolations.intervals[i].upper)).map f)).card = 1) :
    ∃ cert, IsolationReplay.build sign point context head isolations = some cert := by
  have signs := HexSturmMathlib.sign_spec f sign hsign
  have available := (HexSturmMathlib.prepare_isSome f hz
    ha hs hm
    sign (fun a => (signs a).2.1) (fun a => (signs a).2.2.1)
    h1 hn hi
    hnat (fun a => (signs a).1) head .negInf .posInf).mpr whole
  cases prepared : Sturm.prepare sign head .negInf .posInf with
  | none => simp [prepared] at available
  | some domain =>
    obtain ⟨signEq, headEq, lower, upper⟩ := Sturm.prepare_eq_some _ _ _ _ domain prepared
    let total := Sturm.certifyPrepared context domain 1
    have totalEq : total = TarskiCertificate.fromChains sign
        (EndpointSigns.ofSign sign) context head 1 .negInf .posInf
        domain.squarefree domain.squarefree := by
      calc
        total = Sturm.certifyCountPrepared context domain :=
          (Sturm.certifyCountPrepared_eq context domain).symm
        _ = _ := by simp only [Sturm.certifyCountPrepared, signEq, headEq, lower, upper]
    have totalSquarefree : total.squarefree = domain.squarefree := by rw [totalEq]; rfl
    have totalRemainders : total.remainders = domain.squarefree := by rw [totalEq]; rfl
    have totalValue : total.value = isolations.intervals.size := by
      rw [totalEq]
      have value := countValue f hz h1 ha hs hm hn hi hnat sign hsign context domain signEq .negInf .posInf
        (by simpa only [headEq] using whole)
      simpa only [headEq, Endpoint.map, totalCard] using value
    have totalChecked := HexSturmMathlib.certifyPrepared_checks f hz
      ha hs hm
      sign (fun a => (signs a).2.1) h1
      hn hi (fun a => (signs a).1)
      (fun a => (signs a).2.2.2) context domain signEq 1
    rw [headEq, lower, upper] at totalChecked
    change Sturm.check sign context head 1 .negInf .posInf total.value total = true at totalChecked
    rw [totalValue] at totalChecked
    let counts := Vector.ofFn fun i : Fin isolations.intervals.size =>
      TarskiCertificate.fromChains sign (EndpointSigns.ofSign sign)
        context head 1 (.finite (point isolations.intervals[i].lower))
        (.finite (point isolations.intervals[i].upper)) total.squarefree total.remainders
    let cert : IsolationReplay E Ctx := ⟨isolations, total, counts⟩
    have each (i : Fin isolations.intervals.size) :
        Sturm.check sign context head 1
          (.finite (point isolations.intervals[i].lower))
          (.finite (point isolations.intervals[i].upper)) 1 counts[i] = true := by
      have valid : HexSturmMathlib.Domain f hz domain.head
          (.finite (point isolations.intervals[i].lower))
          (.finite (point isolations.intervals[i].upper)) := by
        simpa only [headEq] using intervalDomain i
      have accepted := countRetarget f hz h1 ha hs hm hn hi hnat sign hsign context domain signEq _ _ valid
      have value := countValue f hz h1 ha hs hm hn hi hnat sign hsign context domain signEq _ _ valid
      rw [headEq, intervalCard i] at value
      rw [headEq, value] at accepted
      have countEq : counts[i] = TarskiCertificate.fromChains sign
          (EndpointSigns.ofSign sign) context head 1
          (.finite (point isolations.intervals[i].lower))
          (.finite (point isolations.intervals[i].upper)) domain.squarefree domain.squarefree := by
        change (Vector.ofFn fun j : Fin isolations.intervals.size =>
          TarskiCertificate.fromChains sign
            (EndpointSigns.ofSign sign) context head 1
            (.finite (point isolations.intervals[j].lower))
            (.finite (point isolations.intervals[j].upper)) total.squarefree total.remainders)[i.val] = _
        simp only [Vector.getElem_ofFn, totalSquarefree, totalRemainders]
      exact (congrArg (fun evidence => Sturm.check sign context head 1
        (.finite (point isolations.intervals[i].lower))
        (.finite (point isolations.intervals[i].upper)) 1 evidence) countEq).trans accepted
    have checked : cert.check sign point context head = true := by
      simp only [IsolationReplay.check, cert, Bool.and_eq_true]
      exact ⟨⟨gaps, totalChecked⟩, List.all_eq_true.mpr (fun i _ => each i)⟩
    refine ⟨cert, ?_⟩
    unfold IsolationReplay.build
    rw [prepared]
    change (if cert.check sign point context head then some cert else none) = some cert
    simp only [checked, ite_eq_left]

omit h1 ha hs hm hn hi hnat hsign in
private theorem rootOutside (isolations : IsolationCert) (gaps : isolations.checkGaps = true)
    (root : Fin isolations.intervals.size → ℝ)
    (bounds : ∀ i, HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].lower < root i ∧
      root i < HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].upper)
    (i j : Fin isolations.intervals.size) (different : j ≠ i) :
    root j < HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].lower ∨
      HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].upper < root j := by
  rcases lt_or_gt_of_ne different with before | after
  · left
    exact (bounds j).2.trans (HexRealRootsMathlib.toReal_lt_toReal
      (IsolationCert.gaps_of_check gaps j i before))
  · right
    exact (HexRealRootsMathlib.toReal_lt_toReal
      (IsolationCert.gaps_of_check gaps i j after)).trans (bounds j).1

omit h1 ha hs hm hn hi hnat hsign in
private theorem isolationCards (polynomial : Polynomial ℝ) (nonzero : polynomial ≠ 0)
    (isolations : IsolationCert) (gaps : isolations.checkGaps = true)
    (root : Fin isolations.intervals.size → ℝ)
    (bounds : ∀ i, HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].lower < root i ∧
      root i < HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].upper)
    (complete : ∀ x, polynomial.IsRoot x ↔ ∃ i, root i = x) :
    (HexRealRootsMathlib.Tarski.rootsIn polynomial .negInf .posInf).card = isolations.intervals.size ∧
      ∀ i : Fin isolations.intervals.size, (polynomial.eval (HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].lower) ≠ 0 ∧
        polynomial.eval (HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].upper) ≠ 0) ∧
        (HexRealRootsMathlib.Tarski.rootsIn polynomial
          (.finite (HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].lower))
          (.finite (HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].upper))).card = 1 := by
  classical
  have mono : StrictMono root := fun _ _ ordered => IsolationCert.roots_lt_of_check gaps ordered
    ⟨(bounds _).1, (bounds _).2.le⟩ ⟨(bounds _).1, (bounds _).2.le⟩
  have total : HexRealRootsMathlib.Tarski.rootsIn polynomial .negInf .posInf =
      Finset.image root Finset.univ := by
    ext x
    simp only [HexRealRootsMathlib.Tarski.mem_rootsIn_iff polynomial nonzero,
      HexRealRootsMathlib.Tarski.inInterval_univ, and_true, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact complete x
  constructor
  · rw [total, Finset.card_image_of_injective _ mono.injective, Finset.card_univ, Fintype.card_fin]
  · intro i
    have lower : polynomial.eval (HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].lower) ≠ 0 := by
      intro zero
      obtain ⟨j, equals⟩ := (complete _).mp zero
      by_cases same : j = i
      · subst j; linarith [(bounds i).1]
      · rcases rootOutside isolations gaps root bounds i j same with before | after
        · linarith
        · linarith [(bounds i).1, (bounds i).2]
    have upper : polynomial.eval (HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].upper) ≠ 0 := by
      intro zero
      obtain ⟨j, equals⟩ := (complete _).mp zero
      by_cases same : j = i
      · subst j; linarith [(bounds i).2]
      · rcases rootOutside isolations gaps root bounds i j same with before | after
        · linarith [(bounds i).1, (bounds i).2]
        · linarith
    refine ⟨⟨lower, upper⟩, Finset.card_eq_one.mpr ⟨root i, ?_⟩⟩
    ext x
    rw [HexRealRootsMathlib.Tarski.mem_rootsIn_iff polynomial nonzero]
    simp only [HexRealRootsMathlib.Tarski.inInterval_finite, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxlo, hxhi⟩
      obtain ⟨j, equals⟩ := (complete x).mp hx
      by_cases same : j = i
      · subst j; exact equals.symm
      · rcases rootOutside isolations gaps root bounds i j same with before | after <;> linarith
    · rintro rfl
      exact ⟨(complete _).mpr ⟨i, rfl⟩, (bounds i).1, (bounds i).2⟩



/-- Complete roots enclosed by strictly separated intervals establish every
root-count and endpoint obligation of the actual isolation producer. The
squarefree hypothesis is explicit; this theorem does not manufacture a
squarefree reduction. -/
theorem build_fromRoots (hpoint : ∀ d, f (point d) = HexRealRootsMathlib.Dyadic.toReal d)
    {Ctx : Type v} [DecidableEq Ctx] (context : Ctx) (head : DensePoly E)
    (nonzero : interpret f hz head ≠ 0) (squarefree : Squarefree (interpret f hz head))
    (isolations : IsolationCert) (gaps : isolations.checkGaps = true)
    (root : Fin isolations.intervals.size → ℝ)
    (bounds : ∀ i, HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].lower < root i ∧
      root i < HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].upper)
    (complete : ∀ x, (interpret f hz head).IsRoot x ↔ ∃ i, root i = x) :
    ∃ cert, IsolationReplay.build sign point context head isolations = some cert := by
  obtain ⟨totalCard, each⟩ := isolationCards (interpret f hz head) nonzero isolations gaps root bounds complete
  have whole : HexSturmMathlib.Domain f hz head .negInf .posInf :=
    ⟨nonzero, squarefree, trivial, trivial, trivial⟩
  apply build_success f hz h1 ha hs hm hn hi hnat sign hsign point context head isolations whole gaps totalCard
  · intro i
    refine ⟨nonzero, squarefree, ?_, ?_, ?_⟩
    · change f (point isolations.intervals[i].lower) < f (point isolations.intervals[i].upper)
      rw [hpoint, hpoint]
      exact (bounds i).1.trans (bounds i).2
    · change (interpret f hz head).eval (f (point isolations.intervals[i].lower)) ≠ 0
      rw [hpoint]; exact (each i).1.1
    · change (interpret f hz head).eval (f (point isolations.intervals[i].upper)) ≠ 0
      rw [hpoint]; exact (each i).1.2
  · intro i
    simpa only [Endpoint.map, hpoint] using (each i).2

include hz h1 ha hs hm hn hi hnat hsign in
/-- Every atom query on produced isolation evidence passes the literal
checker. Domain validity comes from the accepted per-interval count; the
shared squarefree chain remains bound to the original head. -/
theorem queryAt_checked {Ctx : Type v} [DecidableEq Ctx]
    (context : Ctx) (head query : DensePoly E) (cert : IsolationReplay E Ctx)
    (checked : cert.check sign point context head = true)
    (chain : cert.total.squarefree = SignedRemainderChain.build sign (Sturm.normalize sign) head 1)
    (i : Fin cert.isolations.intervals.size) :
    Sturm.check sign context head query
      (.finite (point cert.isolations.intervals[i].lower))
      (.finite (point cert.isolations.intervals[i].upper))
      (cert.queryAt sign point context head query i).value
      (cert.queryAt sign point context head query i) = true := by
  let lower := Endpoint.finite (point cert.isolations.intervals[i].lower)
  let upper := Endpoint.finite (point cert.isolations.intervals[i].upper)
  have signs := HexSturmMathlib.sign_spec f sign hsign
  have valid := HexSturmMathlib.check_domain f hz ha hs hm sign
    (fun a => (signs a).2.1) (fun a => (signs a).2.2.1) h1 hnat
    (fun a => (signs a).1) context head 1 lower upper 1 cert.counts[i]
    (cert.count_checked sign point context head checked i)
  have available := (HexSturmMathlib.prepare_isSome f hz ha hs hm sign
    (fun a => (signs a).2.1) (fun a => (signs a).2.2.1) h1 hn hi hnat
    (fun a => (signs a).1) head lower upper).mpr valid
  cases prepared : Sturm.prepare sign head lower upper with
  | none => simp [prepared] at available
  | some domain =>
    obtain ⟨binding, headEq, lo, up⟩ := Sturm.prepare_eq_some _ _ _ _ domain prepared
    have accepted := HexSturmMathlib.certifyPrepared_checks f hz ha hs hm sign
      (fun a => (signs a).2.1) h1 hn hi (fun a => (signs a).1)
      (fun a => (signs a).2.2.2) context domain binding query
    have chainEq : domain.squarefree = cert.total.squarefree := by
      rw [domain.produced, binding, headEq, chain]
    simpa only [Sturm.certifyPrepared, binding, headEq, lo, up, chainEq,
      IsolationReplay.queryAt, lower, upper] using accepted

end Hex.RCF.RealCoefficients.IsolationReplay

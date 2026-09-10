/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Bounded
public import HexPermGroup.Search.BoundedFirst
public import HexPermGroup.Search.Centralizer
public import HexPermGroup.Search.Intersection
public import HexPermGroup.Search.Normalizer
public import HexPermGroup.Search.Sets
public import HexPermGroup.Search.SetTransporter

public section

namespace Hex.PermGroup.Search

/-- Both directions of the generator-conjugation test use the shared sift
allowance. The second direction is skipped after a failed forward test. -/
@[expose] def Tester.normalizer {budget : Budget} (H : Group n) : Tester (Predicate.normalizer H) budget :=
  fun p m =>
    match m.allSifts H H.generators.size
        (fun i : Fin H.generators.size => p.conj (H.generators[i.val]'i.isLt)) (3 * n) with
    | .exhausted failure => .exhausted failure
    | .ok forward meter =>
      if hf : forward.val = true then
        match meter.allSifts H H.generators.size
            (fun i : Fin H.generators.size => p.inv.conj (H.generators[i.val]'i.isLt)) (4 * n) with
        | .exhausted failure => .exhausted failure
        | .ok backward meter => .ok ⟨backward.val, by
            have he := forward.property.symm.trans hf
            simpa only [Predicate.normalizer, Normalizer.test, he, Bool.true_and] using backward.property⟩ meter
      else .ok ⟨false, by
        have he := forward.property.symm.trans (Bool.eq_false_iff.mpr hf)
        simp only [Predicate.normalizer, Normalizer.test, he, Bool.false_and]⟩ meter

end Hex.PermGroup.Search

namespace Hex.PermGroup.Group

@[expose] def intersectionWith (budget : Search.Budget) (G H : Group n) :
    Search.Outcome (Search.Intersection.constraint G H) budget :=
  Search.solveWith budget (Search.Intersection.constraint G H) (Search.Tester.subgroup H)

@[expose] def centralizerWith (budget : Search.Budget) (G H : Group n) :
    Search.Outcome (Search.Centralizer.constraint G H) budget :=
  Search.solveWith budget (Search.Centralizer.constraint G H) (Search.Tester.pure (Search.Predicate.centralizer H))

@[expose] def centerWith (budget : Search.Budget) (G : Group n) :
    Search.Outcome (Search.Centralizer.constraint G G) budget := G.centralizerWith budget G

@[expose] def centralizerPermWith (budget : Search.Budget) (G : Group n) (p : Perm n) :
    Search.Outcome (Search.Centralizer.constraint G (ofGenerators #[p])) budget :=
  G.centralizerWith budget (ofGenerators #[p])

@[expose] def normalizerWith (budget : Search.Budget) (G H : Group n) :
    Search.Outcome (Search.Normalizer.constraint G H) budget :=
  Search.solveWith budget (Search.Normalizer.constraint G H) (Search.Tester.normalizer H)

@[expose] def setStabilizerWith (budget : Search.Budget) (G : Group n) (A : Vector Bool n) :
    Search.Outcome (Search.Sets.constraint G A) budget :=
  Search.solveWith budget (Search.Sets.constraint G A) (Search.Tester.pure (Search.Predicate.setStabilizer A))

/-- The budget includes the original-generator witness program for a positive
answer. Exhaustion has a separate constructor and cannot mean nonexistence. -/
@[expose] def setTransporterWith (budget : Search.Budget) (G : Group n) (A B : Vector Bool n) :
    Search.AnswerOutcome (Search.Sets.transporter G A B) budget :=
  Search.firstWith budget (Search.Sets.transporter G A B) (Search.Evaluator.pure (Search.Sets.test A B))

end Hex.PermGroup.Group

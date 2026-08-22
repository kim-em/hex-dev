# TowerMathlib: the three SPEC-declared missing items

## Accomplished

- Proved the public Extension.embed surface under
  Extension.PreservesEmbedding: embed_injective, embed_add, embed_mul,
  embed_ofRat, embed_smul, and the packaged
  embedAlgHom : T.toField ->a[Q] E.tower.toField with its simp apply
  lemma and injectivity (Arithmetic.lean; the formerly-private Split
  copies are deleted and their call site repointed).
- Installed the scoped Lean.Grind.Field (Elem T) law package by
  delegating to Mathlib's Field.toGrindField in the same scope as the
  field instance, with an operational grind check in review.
- Proved dim_eq_finrank : T.dim = finrank Q T.toField via a scoped
  CharZero instance (through the injective complex embedding), the
  rational-cast bridges, and coordEquiv : Elem T =l[Q] (Fin T.dim -> Q)
  from the mixed-radix coordinates; toField abbreviates Elem T.
- All named theorems check with axioms exactly
  [propext, Classical.choice, Quot.sound]; build green (9325 jobs).
- Clarified the SPEC's two finrank spellings to the toField form and
  made the PreservesEmbedding hypothesis explicit in the
  every-embed sentence, matching what is proved.

## Current frontier

- The TowerMathlib Phase-1 surface is now SPEC-complete; the cluster
  attestations (wave task C14) can cite this.

## Next step

- C14 Phase 1+2 attestations for the NumberField cluster once the BZ
  bump lands on main.

## Blockers

- None.

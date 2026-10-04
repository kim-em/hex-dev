/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Sorted
public import HexMvPolyCorpus

public meta import HexMvPolyCorpus

public meta import HexMvPoly.Sorted

public section

open Hex Hex.MvPoly Hex.MvPolyBench Hex.MvPolyBench.Corpus

/- The native comparator requires increasing streams for its linear
construction path. Check the largest registered rungs of each stream. -/
#guard Sorted.strictlyOrdered Mono.lex (intTerms 4096 3 (axisMono (0 : Fin 4)))
#guard Sorted.strictlyOrdered Mono.lex
  (intTerms 4096 5 (fun i => axisMono (0 : Fin 4) (4096 + i)))
#guard Sorted.strictlyOrdered Mono.grlex (intTerms 128 19 (axisMono (6 : Fin 8)))
#guard Sorted.strictlyOrdered Mono.grlex (intTerms 128 23 (axisMono (7 : Fin 8)))
#guard Sorted.strictlyOrdered Mono.lex
  (intTerms 256 37 (fun i => axisMono (0 : Fin 4) (i + 1)))
#guard Sorted.strictlyOrdered Mono.lex
  (intTerms 256 41 (fun i => axisMono (1 : Fin 4) (i + 1)))
#guard Sorted.strictlyOrdered Mono.grlex (intTerms 1024 53 (collisionMono 1024))
#guard Sorted.strictlyOrdered Mono.grevlex (intTerms 512 59 (patternedMono 512 · 3))
#guard Sorted.strictlyOrdered Mono.grevlex (intTerms 512 61 (patternedMono 512 · 7))
#guard Sorted.strictlyOrdered Mono.grevlex (intTerms 512 67 (patternedMono 512 · 11))

/- Compare canonical outputs across the two representations, including
cancellation and collisions after renaming. -/
#guard
  let left := intTerms 8 37 (fun i => axisMono (0 : Fin 4) (i + 1))
  let right := intTerms 8 41 (fun i => axisMono (1 : Fin 4) (i + 1))
  let p : MvPoly 4 Int Mono.lex := ofTerms left
  let q : MvPoly 4 Int Mono.lex := ofTerms right
  let s := Sorted.ofSortedTerms left
  let t := Sorted.ofSortedTerms right
  toList ((p + q) * (p + q) - (p * p + q * q)) ==
    ((s + t) * (s + t) - (s * s + t * t)).terms

#guard
  let terms := intTerms 16 53 (collisionMono 16)
  let p : MvPoly 4 Int Mono.grlex := ofTerms terms
  let s := Sorted.ofSortedTerms terms Mono.grlex
  let f := fun i : Fin 4 => if i.val % 2 = 0 then (0 : Fin 2) else (1 : Fin 2)
  toList (rename Mono.grevlex f p) == (Sorted.rename f s Mono.grevlex).terms

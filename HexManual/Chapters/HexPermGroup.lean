/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexPermGroupMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "HexPermGroup: checked finite permutation groups" =>
%%%
tag := "hex-perm-group"
%%%

# The Mathlib correspondence

`HexPermGroupMathlib` identifies the checked array representation with
`Equiv.Perm (Fin n)` and transports membership, order, stabilizers, and finite
actions to Mathlib. All producers and certificate checkers remain in the
Mathlib-free `HexPermGroup` library.

# Explicit actions and stabilizer chains

`Perm n` stores all `n` images, including fixed points. Composition is the
left-action convention `(p.comp q) x = p (q x)`. `Group.ofGenerators` builds a
complete checked stabilizer chain; order and negative membership become
mathematical facts only after that check succeeds.

```lean
open Hex Hex.PermGroup

namespace HexPermGroupChapter

def rotation : Perm 4 := ⟨#v[1, 2, 3, 0], by decide, by decide⟩
def reflection : Perm 4 := ⟨#v[0, 3, 2, 1], by decide, by decide⟩
def polygon : Group 4 := Group.ofGenerators #[rotation, reflection]

#guard polygon.order = 8
#guard (polygon.orbit 0).size = 4
#guard (polygon.stabilizer 0).order = 2
#guard (polygon.word? (rotation.comp reflection)).isSome
```

The returned membership program is expressed in the original presentation and
is accepted by `checkWord`. Different presentations can be compared as
subgroups rather than by generator-array equality. Left cosets are used
throughout; for a nonnormal subgroup they must not be interchanged with right
cosets.

```lean
def cyclicA : Group 4 := Group.ofGenerators #[rotation]
def cyclicB : Group 4 := Group.ofGenerators #[rotation.inv]
#guard cyclicA.sameGroup cyclicB

def swap3 : Perm 3 := ⟨#v[1, 0, 2], by decide, by decide⟩
def cycle3 : Perm 3 := ⟨#v[1, 2, 0], by decide, by decide⟩
def symmetric3 : Group 3 := Group.ofGenerators #[swap3, cycle3]
def pointFixer : Group 3 := symmetric3.stabilizer 2

example : pointFixer.IsSubgroup symmetric3 := by
  intro p hp
  exact (symmetric3.mem_stabilizer 2 p).mp hp |>.1

#guard (symmetric3.leftCosetsWith 3 pointFixer (by
  intro p hp
  exact (symmetric3.mem_stabilizer 2 p).mp hp |>.1)).isOk
```

# Actions, transporters, blocks, and element access

Finite actions retain their domain ordering. Images record the induced
generator permutations; kernels are accepted only after checking the complete
domain and every generator action. This is the kernel-checking boundary: a
generator map alone does not prove an action law or a final kernel.

```lean
def opposite := polygon.blocks [(0, 2)]
#guard opposite.blockSize 0 = 2

def oppositeAction := polygon.blockAction opposite
  (polygon.blocks_invariant [(0, 2)]) 2
#guard oppositeAction.isOk

def source : Vector Bool 4 := #v[true, true, false, false]
def target : Vector Bool 4 := #v[false, true, true, false]
#guard (polygon.setTransporter? source target).isSome

def rankRoundTrip : Bool :=
  match polygon.unrank? 5 with
  | none => false
  | some p => (polygon.rank p).val == 5

#guard rankRoundTrip
```

# Normal structure and products

The complete derived-series result retains and checks every derived subgroup.
The four-point imprimitive `C₂ wr C₂` action exposes both factor embeddings and
has order eight.

```lean
def symmetric4 : Group 4 := Group.ofGenerators
  #[⟨#v[1, 0, 2, 3], by decide, by decide⟩, rotation]
#guard symmetric4.derivedSeries.certificate.orders symmetric4 = [24, 12, 4, 1]

def c2 : Group 2 := Group.ofGenerators #[⟨#v[1, 0], by decide, by decide⟩]
def c2wr2 := c2.wreathProduct c2 (by decide)
#guard c2wr2.order = 8
#guard c2wr2.generators.size = 3

end HexPermGroupChapter
```

# Incomplete results

Construction, enumeration, actions, search, normal structure, and products
have bounded entry points. A limit is checked before the corresponding work.
An exhausted search can retain a proved subgroup lower bound, and a term-capped
derived series can retain a checked prefix. Neither result supplies a negative
answer. Producer meters and replay limits are separate so certificate checking
never consumes or inherits a producer's unused allowance.

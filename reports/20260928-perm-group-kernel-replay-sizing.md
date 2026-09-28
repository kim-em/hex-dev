# Kernel replay of permutation-group certificates: sizing

Measurements behind the [Kernel certificates](../HexPermGroup/SPEC/hex-perm-group.md#kernel-certificates)
section of the `hex-perm-group` SPEC. Host `chungus2` (96 cores, 125 GB,
shared with other work), Lean v4.34.1, hex-dev at `20f6c424`. Every run
was a single `lake env lean` process under a `systemd-run --user --scope -p
MemoryMax=… -p MemorySwapMax=0` limit, one at a time. "Kernel" is the
profiler's type-checking time; "peak" is the cgroup's `memory.peak`.

## Inputs

ATLAS permutation generators from GAP 4.15.1 with AtlasRep; chains built by
`Group.ofGenerators`, whose orders agree with GAP's in every case.

| group | degree | order | nontrivial levels (orbit sizes) | Schreier generators sifted |
|---|---|---|---|---|
| M11 | 11 | 7920 | 11, 10, 9, 8 | 177 |
| M11, classical generators | 11 | 7920 | 11, 10, 9, 8 | 170 |
| M12 | 12 | 95040 | 12, 11, 10, 9, 8 | 215 |
| M22 | 22 | 443520 | 22, 21, 20, 16, 3 | 295 |
| M23 | 23 | 10200960 | 23, 22, 21, 20, 3, 16 | 440 |
| M24 | 24 | 244823040 | 24, 23, 22, 21, 20, 16, 3 | 558 |
| J2 | 100 | 604800 | 100, 63, 24, 4 | 656 |
| HS | 100 | 44352000 | 100, 77, 60, 32, 3 | 1102 |
| McL | 275 | 898128000 | 275, 112, 81, 36, 5, 2 | 1803 |
| Co3 | 276 | 495766656000 | 276, 275, 162, 56, 45, 16 | 3763 |

The classical generators of M11 are the 11-cycle and (3 7 11 8)(4 10 5 6).

## Replay of `checkChain`

`theorem : checkChain S c = true := by decide +kernel` on the literal chain.

| group | kernel | peak |
|---|---|---|
| M11 | 20 s | 6.0 GB |
| M11, classical generators | 28.3 s | 5.8 GB |
| M12 | 62 s on a loaded host | not recorded |
| M22 | did not finish | above 24 GB after 61 s |
| M23, M24 | did not finish | above 30 GB after 80 s |
| J2, HS | did not finish | tens of GB |

Kernel construction (`(Group.ofGenerators S).order = 7920 := by decide
+kernel`) does not reduce: `Build.build` is defined by well-founded recursion.

In isolation for M11, `Chain.Normalized`, `Working`, `Fixed` and `checkWords`
each take under 60 ms, the top `Orbit.Valid` 0.3 s, and one sift 0.16 s, so
the time is the Schreier sifts. Each sift visits all `n` levels of the fixed
base and recomputes `Perm.inv` and `Perm.comp` at each. Single operations:
compose, inverse and compose take 53 ms at degree 11, 3.5 s at degree 100 and
4.2 s at degree 276. Comparing two degree-276 permutations with
`DecidableEq` takes 23 s, and the `decide +kernel` proofs of one degree-276
literal's `nodup` and `complete` fields about 2 s. Degree-275 literals need
`maxRecDepth 100000` and `maxHeartbeats 0` to elaborate.

Running nine of these replays at once exhausted memory and swap on the host.

## Packed certificates

A prototype checker over raw `Nat` data, with no soundness proof: levels only
at nontrivial base points, packed permutations with `W` bits per image, stored
inverse transversals, full Schreier-family sifting. Variants differ in how the
transversal is read and how arithmetic is written:

- A: `List Nat` transversals read by `List.getD`; operators `&&&`, `>>>`, `|||`;
  compose by structural recursion.
- B: as A with compose as one `Nat.rec` step per image.
- C: as B with each transversal packed into one `Nat`, read by shift and mask.
- D: as B with raw `Nat.land`, `Nat.shiftRight`, `Nat.shiftLeft`, `Nat.lor`,
  `Nat.mul` spellings.
- E: as B with `Lean.RArray` transversals and orbits.
- F: as D with `Lean.RArray` transversals and orbits.

Single declaration:

| group | A | B | C | D | E | F |
|---|---|---|---|---|---|---|
| M11 | 0.45 s, 0.33 GB | | | | | |
| M11, classical generators | | | | | | 0.14 s, 0.28 GB |
| M12 | 0.72 s, 0.39 GB | | | | | |
| M22 | 2.1 s, 0.66 GB | | | | | |
| M23 | 3.8 s, 0.96 GB | | | | | |
| M24 | 6.0 s, 1.3 GB | 4.7 s, 0.98 GB | 4.6 s, 0.92 GB | | | 1.8 s, 0.52 GB |
| J2 | 21 s, 4.3 GB | | | | | |
| HS | 38 s, 7.5 GB | 30.9 s, 5.4 GB | 28.2 s, 5.1 GB | 13.9 s, 2.1 GB | 53.7 s, 5.1 GB | 10.2 s, 1.9 GB |
| McL | timeout at 107 s, 19.7 GB | | | | | |
| Co3 | timeout at 107 s, 19.8 GB | | | | | |

The HS columns B to F were run back to back; other cells were run at
different times on the shared host and vary by up to about 20%.

Split into declarations (one per level for the non-sifting checks, and one
per 256 consecutive Schreier generators), total kernel time, largest
declaration, and peak:

| group | A | B | C | D | F |
|---|---|---|---|---|---|
| HS | 41 s total, 2.4 GB | | | | |
| McL | 269 s, 42 s, 8.5 GB | | | | |
| Co3 | 554 s, 42 s, 10.1 GB | 400 s, 30 s, 7.9 GB | 493 s, 41 s, 7.4 GB | 173 s, 24 s, 5.3 GB | 114 s, 8.6 s, 5.0 GB |

The default heartbeat limit ended the single-declaration McL and Co3 checks
at 107 s, so a certificate of this size must be split. Peak memory is roughly
proportional to the kernel work in one declaration.

Compiling a 276-entry `List Nat` literal hits `maximum recursion depth`; the
same literal in a `noncomputable def` elaborates and checks.

## Observations

- For the `M11` example of the manual, variant F takes 0.14 s and 0.28 GB
  against 28.3 s and 5.8 GB for `checkChain` replay. Most of the 0.28 GB is
  the Lean process itself.

- Packing permutations into `Nat` and dropping singleton levels is the large
  change: M24 goes from over 30 GB unfinished to seconds.
- Raw `Nat` spellings halve the time again (HS 30.9 s to 13.9 s).
- A transversal packed into one `Nat` is no better than a list at degree 100
  and worse at degree 276, since each read shifts the whole number.
- `RArray` transversals help together with raw spellings: HS 13.9 s to
  10.2 s, and Co3 173 s to 114 s, with its largest declaration (the level
  whose orbit has 276 points) 24 s to 8.6 s. With operator spellings they
  were slower than lists (HS 53.7 s against 30.9 s); the cause was not
  investigated.
- With all of these, Co3 checks in about two minutes of kernel time in
  declarations of under ten seconds each.

## Appendix: prototype checker (variant F)

No soundness proof. Certificates were generated from `Group.ofGenerators`
chains by a Python script that packs permutations, builds balanced `RArray`
literals and records Schreier-tree parents and next-level indices.

```lean
/-! Packed-Nat stabilizer-chain checker (sizing prototype, no soundness proof).

A permutation of degree `n` is one `Nat` with `W` bits per image. Orbit lookup
tables are packed the same way (orbit index + 1, with 0 meaning absent). -/

structure Level where
  base : Nat
  gens : List Nat
  orbit : List Nat
  lookup : Nat
  reps : List Nat
  repInvs : List Nat
  parent : List (Nat × Nat)
  orbitR : Lean.RArray Nat
  repsR : Lean.RArray Nat
  repInvsR : Lean.RArray Nat

instance : Inhabited Level := ⟨⟨0, [], [], 0, [], [], [], .leaf 0, .leaf 0, .leaf 0⟩⟩

namespace Packed

def mask (W : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 W) 1

def pget (W p i : Nat) : Nat := Nat.land (Nat.shiftRight p (Nat.mul i W)) (mask W)

/-- `(p * q)(i) = p(q(i))`, built from the top image down. -/
-- Raw `Nat` spellings with the mask passed in: no typeclass instance is unfolded per image.
def compM (W m p q : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.shiftRight p (Nat.mul (Nat.land (Nat.shiftRight q (Nat.mul i W)) m) W)) m)
      (Nat.mul i W))) n

def comp (n W p q : Nat) : Nat := compM W (mask W) p q n

def ident (n W : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => acc ||| (i <<< (i * W))) n

/-- Sift `h` through the suffix chain, left-multiplying by stored inverses. -/
def sift (n W : Nat) (e : Nat) : List Level → Nat → Bool
  | [], h => h == e
  | L :: rest, h =>
    let j := pget W L.lookup (pget W h L.base)
    if j == 0 then false else sift n W e rest (comp n W (L.repInvsR.get (j - 1)) h)

/-- All `(i, j)` pairs, generator index and orbit index. -/
def allPairs (g o : Nat) : List (Nat × Nat) :=
  (List.range g).flatMap fun i => (List.range o).map fun j => (i, j)

def checkLevel (n W : Nat) (e : Nat) (fixed : List Nat) (L : Level) (rest : List Level) : Bool :=
  let g := L.gens.length
  let o := L.orbit.length
  -- generators fix all earlier base points and the set is closed under inverses
  L.gens.all (fun s => fixed.all fun b => pget W s b == b) &&
  L.gens.all (fun s => L.gens.any fun t => comp n W s t == e) &&
  -- orbit and lookup agree; the orbit starts at the base point with the identity
  L.orbitR.get 0 == L.base && L.repsR.get 0 == e &&
  L.reps.length == o && L.repInvs.length == o && L.parent.length == o &&
  (List.range o).all (fun j => pget W L.lookup (L.orbitR.get j) == j + 1) &&
  -- the orbit is closed under the generators
  (allPairs g o).all (fun (i, j) =>
    let x := pget W (L.gens.getD i 0) (L.orbitR.get j)
    let k := pget W L.lookup x
    k != 0 && L.orbitR.get (k - 1) == x) &&
  -- transversal provenance through the Schreier tree, and stored inverses
  (List.range o).all (fun j => j == 0 ||
    (let (i, pj) := L.parent.getD j (0, 0)
     pj < j && pget W (L.gens.getD i 0) (L.orbitR.get pj) == L.orbitR.get j &&
     L.repsR.get j == comp n W (L.gens.getD i 0) (L.repsR.get pj))) &&
  (List.range o).all (fun j => comp n W (L.repInvsR.get j) (L.repsR.get j) == e) &&
  -- every Schreier generator sifts to the identity through the suffix
  (allPairs g o).all (fun (i, j) =>
    let s := L.gens.getD i 0
    let x := pget W s (L.orbitR.get j)
    let k := pget W L.lookup x
    sift n W e rest (comp n W (L.repInvsR.get (k - 1)) (comp n W s (L.repsR.get j)))) &&
  -- next-level generators lie in the stabilizer: each is a Schreier generator of this level
  (match rest with
   | [] => true
   | next :: _ => next.gens.all fun t => (allPairs g o).any fun (i, j) =>
      let s := L.gens.getD i 0
      let x := pget W s (L.orbitR.get j)
      let k := pget W L.lookup x
      comp n W (L.repInvsR.get (k - 1)) (comp n W s (L.repsR.get j)) == t)

def checkChainAux (n W e : Nat) : List Nat → List Level → Bool
  | _, [] => true
  | fixed, L :: rest => checkLevel n W e fixed L rest && checkChainAux n W e (L.base :: fixed) rest

/-- Input generators are exactly (up to inverses and order) the first level's generators. -/
def checkInputs (n W e : Nat) (inputs : List Nat) (levels : List Level) : Bool :=
  match levels with
  | [] => inputs.all (· == e)
  | L :: _ => inputs.all (fun s => L.gens.contains s) &&
      L.gens.all (fun s => inputs.contains s || inputs.any fun t => comp n W s t == e)

def checkChain (n W : Nat) (inputs : List Nat) (levels : List Level) : Bool :=
  let e := ident n W
  checkInputs n W e inputs levels && checkChainAux n W e [] levels

def orderOf (levels : List Level) : Nat := levels.foldl (fun acc L => acc * L.orbit.length) 1

end Packed

/-! Split variant: the same checks, but the Schreier family in explicit chunks so that each
kernel declaration does a bounded amount of work. Next-level generators come with a
recorded `(i, j)` index into the family instead of a search. -/

namespace Packed

def schreierGen (n W : Nat) (L : Level) (i j : Nat) : Nat :=
  let s := L.gens.getD i 0
  let x := pget W s (L.orbitR.get j)
  let k := pget W L.lookup x
  comp n W (L.repInvsR.get (k - 1)) (comp n W s (L.repsR.get j))

/-- Everything in `checkLevel` except the Schreier sifts and next-level provenance. -/
def checkLevelBasic (n W : Nat) (e : Nat) (fixed : List Nat) (L : Level) : Bool :=
  let g := L.gens.length
  let o := L.orbit.length
  L.gens.all (fun s => fixed.all fun b => pget W s b == b) &&
  L.gens.all (fun s => L.gens.any fun t => comp n W s t == e) &&
  L.orbitR.get 0 == L.base && L.repsR.get 0 == e &&
  L.reps.length == o && L.repInvs.length == o && L.parent.length == o &&
  (List.range o).all (fun j => pget W L.lookup (L.orbitR.get j) == j + 1) &&
  (allPairs g o).all (fun (i, j) =>
    let x := pget W (L.gens.getD i 0) (L.orbitR.get j)
    let k := pget W L.lookup x
    k != 0 && L.orbitR.get (k - 1) == x) &&
  (List.range o).all (fun j => j == 0 ||
    (let (i, pj) := L.parent.getD j (0, 0)
     pj < j && pget W (L.gens.getD i 0) (L.orbitR.get pj) == L.orbitR.get j &&
     L.repsR.get j == comp n W (L.gens.getD i 0) (L.repsR.get pj))) &&
  (List.range o).all (fun j => comp n W (L.repInvsR.get j) (L.repsR.get j) == e)

/-- Sift the Schreier generators with indices in `[lo, hi)` of the row-major family. -/
def checkSchreierRange (n W e : Nat) (L : Level) (rest : List Level) (lo hi : Nat) : Bool :=
  let o := L.orbit.length
  (List.range (hi - lo)).all fun t =>
    let p := lo + t
    sift n W e rest (schreierGen n W L (p / o) (p % o))

/-- Each next-level generator is the recorded Schreier generator. -/
def checkNextGens (n W : Nat) (L next : Level) (idx : List (Nat × Nat)) : Bool :=
  idx.length == next.gens.length &&
  (List.range idx.length).all fun t =>
    let (i, j) := idx.getD t (0, 0)
    schreierGen n W L i j == next.gens.getD t 0

end Packed
```

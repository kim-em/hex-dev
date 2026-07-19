/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexRealRootsMathlib.Isolations
public import HexRealRootsMathlib.Separation
public import HexRealRootsMathlib.ChainCorrespond
public meta import HexRealRoots.Refine
public meta import HexRealRoots.Isolate
public import HexPolyZMathlib.Basic
public import Lean
-- Stage-1 permits `import all` shortcuts so this module's OWN sanity `decide`s
-- reduce.  The downstream user-side test file uses a plain
-- `import HexRealRootsMathlib.IsolateRootsProto` (no `import all`), which is how
-- the exposure gaps are surfaced.
import all Init.Data.Array.DecidableEq
import all HexRealRootsMathlib.Separation
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var
import all HexRealRoots.Prec
import all HexRealRoots.Refine

public section
set_option backward.proofsInPublic true

/-!
# Stage-1 feasibility prototype: the `isolate_roots` term elaborator

Intentionally NOT added to the `HexRealRootsMathlib` umbrella; it answers the
feasibility questions for the later polished stages: the `Hex.IsolatedRealRoots`
structure (aeval form, `Vector (ℚ × ℚ) n`); the glue lemmas
(`aeval_toPolynomial`, `IsolatedRealRoots.of`, `IsolatedRealRoots.congrRoots`);
two term elaborators, `isolate_roots` (per-field `decide`, the
`RealRootsX4Minus2` shape) and `isolate_roots_replay` (single reified Sturm
chain + cheap replay checks) for the A/B kernel-cost experiment; and the width
path. Every `sorry` is listed in the Stage-1 report.
-/

open Polynomial

namespace Hex

/-! ## The user-facing structure -/

/-- A complete, certified real-root isolation of `P : Polynomial R` over `ℝ`:
`n` rational intervals, each holding exactly one real root, together covering
every real root. Props are in `aeval` form so the same structure serves
`R = ℤ` (a `ZPoly` via `toPolynomial`), `R = ℚ`, and `R = ℝ`. -/
structure IsolatedRealRoots {R : Type*} [CommRing R] [Algebra R ℝ]
    (P : Polynomial R) (n : ℕ) where
  /-- The `n` isolating intervals `(lower, upper]`, as pairs of rationals. -/
  intervals : Vector (ℚ × ℚ) n
  /-- Each interval holds exactly one real root of `P`. -/
  unique_root : ∀ i : Fin n, ∃! x : ℝ,
      aeval x P = 0 ∧ (intervals[i].1 : ℝ) < x ∧ x ≤ (intervals[i].2 : ℝ)
  /-- Every real root of `P` lies in one of the intervals. -/
  covers : ∀ x : ℝ, aeval x P = 0 →
      ∃ i : Fin n, (intervals[i].1 : ℝ) < x ∧ x ≤ (intervals[i].2 : ℝ)

/-- Transport an isolation along a pointwise root equivalence. One lemma, used
twice by the elaborator: the squarefree-core step and the user-polynomial
step. Heterogeneous in the coefficient ring, since the structure only sees `P`
through `aeval x P = 0`. -/
noncomputable def IsolatedRealRoots.congrRoots {R S : Type*} [CommRing R] [Algebra R ℝ]
    [CommRing S] [Algebra S ℝ] {P : Polynomial R} {Q : Polynomial S} {n : ℕ}
    (h : ∀ x : ℝ, aeval x P = 0 ↔ aeval x Q = 0) :
    IsolatedRealRoots P n → IsolatedRealRoots Q n := fun H =>
  { intervals := H.intervals
    unique_root := fun i => by
      obtain ⟨x, ⟨hx0, hlo, hhi⟩, huniq⟩ := H.unique_root i
      exact ⟨x, ⟨(h x).mp hx0, hlo, hhi⟩,
        fun y hy => huniq y ⟨(h y).mpr hy.1, hy.2.1, hy.2.2⟩⟩
    covers := fun x hx => H.covers x ((h x).mpr hx) }

end Hex

namespace HexRealRootsMathlib

open Hex

/-! ## Glue lemmas -/

/-- `aeval` of the integer cast at a real point equals the real-cast
polynomial's `eval`. Bridges the `RealRootIsolation` API (stated for
`(toPolyℝ p).IsRoot`) to the structure's `aeval` form. -/
theorem aeval_toPolynomial (p : Hex.ZPoly) (x : ℝ) :
    aeval x (HexPolyZMathlib.toPolynomial p) = (toPolyℝ p).eval x := by
  rw [aeval_def, HexPolyMathlib.eval₂_toPolynomial, eval_toPolyℝ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  norm_num

/-- `IsRoot` of the real cast is the structure's `aeval = 0` form. -/
theorem isRoot_toPolyℝ_iff (p : Hex.ZPoly) (x : ℝ) :
    (toPolyℝ p).IsRoot x ↔ aeval x (HexPolyZMathlib.toPolynomial p) = 0 := by
  rw [Polynomial.IsRoot, aeval_toPolynomial]

/-- A `ZPoly` with nonzero stored size is nonzero. Emitted `p ≠ 0` proofs go
through this (a `Nat` `decide` on `p.size`), never through structural
`DensePoly` equality (the core `Array.instDecidableEqImpl` module bug). -/
theorem ne_zero_of_size_ne_zero {p : Hex.ZPoly} (h : p.size ≠ 0) : p ≠ 0 :=
  fun he => h (by rw [he]; exact Hex.DensePoly.size_zero)

/-- **The from-`RealRootIsolations` constructor (`IsolatedRealRoots.of`).**
Assemble the user structure from a complete Sturm-certified run, via
`exists_unique_root` + `isolates` + the `aeval` bridge. -/
noncomputable def IsolatedRealRoots.of (p : Hex.ZPoly) (hp0 : p ≠ 0)
    (hsf : Hex.ZPoly.SquareFreeRat p) (out : Hex.RealRootIsolations p) :
    Hex.IsolatedRealRoots (HexPolyZMathlib.toPolynomial p) out.isolations.size where
  intervals := Vector.ofFn fun i =>
    (out.isolations[i].interval.lower.toRat, out.isolations[i].interval.upper.toRat)
  unique_root := by
    intro i
    have h := (out.isolations[i]).exists_unique_root hsf
    obtain ⟨r, ⟨hr0, hlo, hhi⟩, huniq⟩ := h
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    refine ⟨r, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (isRoot_toPolyℝ_iff p r).mp hr0
    · exact hlo
    · exact hhi
    · intro y hy
      exact huniq y ⟨(isRoot_toPolyℝ_iff p y).mpr hy.1, hy.2.1, hy.2.2⟩
  covers := by
    intro x hx
    have hroot : (toPolyℝ p).IsRoot x := (isRoot_toPolyℝ_iff p x).mpr hx
    obtain ⟨iso, ⟨hmem, hlo, hhi⟩, _⟩ := out.isolates hp0 hsf x hroot
    rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hmem
    obtain ⟨j, hj, hjeq⟩ := hmem
    refine ⟨⟨j, hj⟩, ?_, ?_⟩ <;> simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    · rw [hjeq]; exact hlo
    · rw [hjeq]; exact hhi

/-! ## Replay lemmas for the A/B experiment (path (b))

These tie a *reified literal* Sturm chain to `sturmCount`/`rootCount` on the
polynomial, so `count_one`/`complete` can be discharged by cheap `decide`s on
literal sign-variation gaps rather than by rebuilding `sturmChain p` inside
each field. In the prototype they carry a `sorry`: a real proof needs the
`chain = sturmChain p` identification (blocked from a plain-`decide` route by
the core `Array` DecidableEq module bug — see the Stage-1 report). The
squarefree certificate is still discharged by a real `decide` in BOTH paths, so
path (b) still pays exactly one honest chain build. -/

/-- Path-(b) surrogate for `count_one`: a literal-chain sign-variation gap of
`1` gives a Sturm count of `1`. Sorry stands in for the `chain = sturmChain p`
identification (stage 3a). -/
theorem sturmCount_ofChain (p : Hex.ZPoly) (chain : Array Hex.ZPoly)
    (I : Hex.DyadicInterval)
    (_h : (Hex.sturmVarAt chain I.lower : Int) - Hex.sturmVarAt chain I.upper = 1) :
    Hex.sturmCount p I = 1 := by
  sorry

/-- Path-(b) surrogate for `complete`: a literal-chain `−∞/+∞` sign-variation
gap of `n` gives `rootCount p = n`. Sorry as above. -/
theorem rootCount_ofChain (p : Hex.ZPoly) (chain : Array Hex.ZPoly) (n : ℕ)
    (_h : Hex.sturmVarNegInf chain - Hex.sturmVarPosInf chain = n) :
    Hex.rootCount p = n := by
  sorry

namespace IsolateProto

open Lean Elab Meta Term

/-! ## The elaborator -/

/-- Evaluate a closed `Hex.ZPoly` expression at elaboration time (compiled
evaluation, IrreducibleCert pattern). -/
private meta unsafe def evalZPolyUnsafe (e : Expr) : MetaM (Except String Hex.ZPoly) :=
  try return .ok (← evalExpr Hex.ZPoly (mkConst ``Hex.ZPoly) e)
  catch ex => return .error (← ex.toMessageData.toString)

@[implemented_by evalZPolyUnsafe]
private meta opaque evalZPolyCore (e : Expr) : MetaM (Except String Hex.ZPoly)

meta def evalZPoly (e : Expr) : MetaM Hex.ZPoly := do
  match ← evalZPolyCore e with
  | .ok f => return f
  | .error msg => throwError "isolate_roots: failed to evaluate the ZPoly{indentExpr e}\n{msg}"

/-- Evaluate a closed `Rat` (width) expression at elaboration time. `Rat` is
computable, so `2^(-20)`, `1/1000`, `10^(-2)` all reduce. -/
private meta unsafe def evalRatUnsafe (e : Expr) : MetaM (Except String Rat) :=
  try return .ok (← evalExpr Rat (mkConst ``Rat) e)
  catch ex => return .error (← ex.toMessageData.toString)

@[implemented_by evalRatUnsafe]
private meta opaque evalRatCore (e : Expr) : MetaM (Except String Rat)

meta def evalRat (e : Expr) : MetaM Rat := do
  match ← evalRatCore e with
  | .ok q => return q
  | .error msg => throwError "isolate_roots: failed to evaluate the width{indentExpr e}\n{msg}"

/-- Term syntax for an `Int` literal. -/
meta def intStx (c : Int) : MetaM (TSyntax `term) := do
  let numLit := Syntax.mkNumLit (toString c.natAbs)
  if c < 0 then `((-$numLit : Int)) else `(($numLit : Int))

/-- Term syntax for a `Nat` literal. -/
meta def natStx (n : Nat) : TSyntax `term := Syntax.mkNumLit (toString n)

/-- Term syntax for a reified `Hex.ZPoly` as `Hex.DensePoly.ofCoeffs #[…]`. -/
meta def zpolyStx (f : Hex.ZPoly) : MetaM (TSyntax `term) := do
  let elems ← f.toArray.mapM intStx
  `(Hex.DensePoly.ofCoeffs #[$elems,*])

/-- Term syntax for a `Dyadic` endpoint as `Dyadic.ofInt m` or
`Dyadic.ofInt m >>> (s : Int)`. -/
meta def dyadicStx (d : Dyadic) : MetaM (TSyntax `term) := do
  let q := d.toRat
  let mStx ← intStx q.num
  if q.den == 1 then
    `(Dyadic.ofInt $mStx)
  else
    let s := q.den.log2   -- den is a power of two
    let sStx ← intStx (Int.ofNat s)
    `(Dyadic.ofInt $mStx >>> ($sStx : Int))

/-- Extract a `Nat` literal from an `Expr` (numerals and raw literals). -/
meta def getNat (e : Expr) : MetaM Nat := do
  match ← getNatValue? e with
  | some n => return n
  | none =>
    match (← whnfR e).getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) =>
      match ← getNatValue? n with
      | some k => return k
      | none => throwError "isolate_roots: not a Nat literal{indentExpr e}"
    | _ => throwError "isolate_roots: not a Nat literal{indentExpr e}"

/-- Interpret an integer scalar leaf (`OfNat`, `Neg`, `C`-free numerals). -/
meta partial def evalIntLit (e : Expr) : MetaM Int := do
  match (← whnfR e).getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => return Int.ofNat (← getNat n)
  | (``Neg.neg, #[_, _, a]) => return - (← evalIntLit a)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return (← evalIntLit a) * (← evalIntLit b)
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return (← evalIntLit a) + (← evalIntLit b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return (← evalIntLit a) - (← evalIntLit b)
  | (``Int.ofNat, #[n]) => return Int.ofNat (← getNat n)
  | _ =>
    match ← getIntValue? e with
    | some z => return z
    | none => throwError "isolate_roots: non-integer coefficient{indentExpr e}"

/-- Recursive interpreter: a `Polynomial R` expression over
`X / C / numerals / + / - / * / ^ / neg` to a `Hex.ZPoly` value. -/
meta partial def parsePoly (e : Expr) : MetaM Hex.ZPoly := do
  match (← whnfR e).getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return (← parsePoly a) + (← parsePoly b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return (← parsePoly a) - (← parsePoly b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return (← parsePoly a) * (← parsePoly b)
  | (``Neg.neg, #[_, _, a]) => return - (← parsePoly a)
  | (``HPow.hPow, #[_, _, _, _, a, n]) => do
      let base ← parsePoly a
      let k ← getNat n
      let mut acc : Hex.ZPoly := Hex.DensePoly.C 1
      for _ in [0:k] do acc := acc * base
      return acc
  | (``Polynomial.X, _) => return Hex.DensePoly.ofCoeffs #[(0 : Int), 1]
  | (``Polynomial.C, #[_, _, c]) => return Hex.DensePoly.C (← evalIntLit c)
  | (``OfNat.ofNat, #[_, n, _]) => return Hex.DensePoly.C (Int.ofNat (← getNat n))
  | _ => throwError "isolate_roots: unsupported polynomial syntax{indentExpr e}"

/-- Compute the refinement target `k` (bits) from a positive rational width
`q`: the least `k` with `2^(-k) ≤ q`. -/
meta def widthBits (q : Rat) : Int := Id.run do
  if q ≤ 0 then return 0
  let inv := q⁻¹
  let mut k : Nat := 0
  while (2 : Rat) ^ k < inv && k < 4096 do
    k := k + 1
  return Int.ofNat k

/-- The certified isolation data extracted at elaboration time: the reified
polynomial, per-root dyadic endpoints, and the Sturm chain (for path (b)). A
nondependent DTO. -/
structure IsoData where
  poly     : Hex.ZPoly
  endpoints : Array (Dyadic × Dyadic)
  chain    : Array Hex.ZPoly

/-- Run the compiled backend: `isolate?`, optionally `refineTo`, and read off a
nondependent DTO. -/
meta def runBackend (f : Hex.ZPoly) (widthK : Option Int) : MetaM IsoData := do
  if f.size == 0 then throwError "isolate_roots: the zero polynomial (every real is a root)"
  unless Hex.ZPoly.hasSquarefreeSturmChain f do
    throwError "isolate_roots: non-squarefree input (prototype limitation)"
  let some out := Hex.isolate? f
    | throwError "isolate_roots: backend isolate? returned none"
  let isos := out.isolations
  let refined := match widthK with
    | some k => isos.map (fun iso : Hex.RealRootIsolation f => iso.refineTo k)
    | none => isos
  let endpoints := refined.map
    (fun iso : Hex.RealRootIsolation f => (iso.interval.lower, iso.interval.upper))
  return { poly := f, endpoints, chain := Hex.ZPoly.sturmChain f }

/-- Emit path (a): per-field `by decide` (the `RealRootsX4Minus2` shape). -/
meta def emitPathA (d : IsoData) : MetaM (TSyntax `term) := do
  let fStx ← zpolyStx d.poly
  let isoStxs ← d.endpoints.mapM fun (lo, hi) => do
    let loStx ← dyadicStx lo
    let hiStx ← dyadicStx hi
    `(term| (⟨⟨$loStx, $hiStx, by decide⟩, by decide⟩ : Hex.RealRootIsolation $fStx))
  `(HexRealRootsMathlib.IsolatedRealRoots.of $fStx
      (HexRealRootsMathlib.ne_zero_of_size_ne_zero (by decide))
      (HexRealRootsMathlib.squareFreeRat_of_hasSquarefreeSturmChain $fStx (by decide))
      { isolations := #[$isoStxs,*], ordered := by decide, complete := by decide })

/-- Emit path (b): one reified Sturm chain, cheap literal sign-variation
`decide`s via the replay lemmas, one honest squarefree `decide`. -/
meta def emitPathB (d : IsoData) : MetaM (TSyntax `term) := do
  let fStx ← zpolyStx d.poly
  let chainStxs ← d.chain.mapM zpolyStx
  let chainStx ← `((#[$chainStxs,*] : Array Hex.ZPoly))
  let n := natStx d.endpoints.size
  let isoStxs ← d.endpoints.mapM fun (lo, hi) => do
    let loStx ← dyadicStx lo
    let hiStx ← dyadicStx hi
    `(term| (⟨⟨$loStx, $hiStx, by decide⟩,
        HexRealRootsMathlib.sturmCount_ofChain $fStx $chainStx _ (by decide)⟩ :
          Hex.RealRootIsolation $fStx))
  `(HexRealRootsMathlib.IsolatedRealRoots.of $fStx
      (HexRealRootsMathlib.ne_zero_of_size_ne_zero (by decide))
      (HexRealRootsMathlib.squareFreeRat_of_hasSquarefreeSturmChain $fStx (by decide))
      { isolations := #[$isoStxs,*], ordered := by decide,
        complete := (HexRealRootsMathlib.rootCount_ofChain $fStx $chainStx $n (by decide)).symm ▸
          (by rfl : (#[$isoStxs,*] : Array (Hex.RealRootIsolation $fStx)).size = $n) })

/-- Bridge tactic macro closing `aeval x (toPolynomial pZ) = 0 ↔ aeval x P = 0`
for reflected literals (best-effort in the prototype). -/
macro "isolate_roots_bridge" : tactic =>
  `(tactic| (intro x
             simp only [HexRealRootsMathlib.aeval_toPolynomial, HexRealRootsMathlib.eval_toPolyℝ,
      Hex.DensePoly.coeff_ofCoeffs, Finset.sum_range_succ, Finset.sum_range_zero, map_ofNat,
      Polynomial.aeval_X, Polynomial.aeval_C, map_sub, map_pow, map_add, map_mul, map_neg]
             push_cast
             ring_nf))

/-- Shared driver for both elaborators. -/
meta def elabIsolate (mode : Bool) (widthStx : Option (TSyntax `term)) (pStx : TSyntax `term)
    (expectedType? : Option Expr) : TermElabM Expr := do
  -- width
  let widthK ← match widthStx with
    | none => pure none
    | some w => do
      let wE ← elabTermEnsuringType w (some (mkConst ``Rat))
      let wE ← instantiateMVars wE
      if wE.hasFVar || wE.hasExprMVar then
        throwError "isolate_roots: the width must be a closed rational{indentExpr wE}"
      let q ← evalRat wE
      if q ≤ 0 then throwError "isolate_roots: the width must be strictly positive"
      pure (some (widthBits q))
  -- polynomial: dispatch on type
  let pE ← elabTerm pStx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let pE ← instantiateMVars pE
  if pE.hasFVar || pE.hasExprMVar then
    throwError "isolate_roots: the polynomial must be closed{indentExpr pE}"
  let ty ← whnfR (← inferType pE)
  let tyFn := ty.getAppFn
  let tyArgs := ty.getAppArgs
  let isZPoly := tyFn.isConstOf ``Hex.DensePoly
  let isPoly := tyFn.isConstOf ``Polynomial
  let f ←
    if isZPoly then
      if tyArgs.size ≥ 1 && tyArgs[0]!.isConstOf ``Int then evalZPoly pE
      else throwError "isolate_roots: only Hex.ZPoly (DensePoly Int) supported{indentExpr ty}"
    else if isPoly then parsePoly pE
    else throwError "isolate_roots: expected a Hex.ZPoly or Polynomial term{indentExpr ty}"
  let d ← runBackend f widthK
  let core ← if mode then emitPathA d else emitPathB d
  -- If the user gave a Polynomial input, transport onto their polynomial.
  let term ← match ty.getAppFnArgs with
    | (``Polynomial, _) =>
        -- Splice the reflected polynomial and its (post-trim) size into the
        -- bridge so the coefficient sum expands; the residual iff is between two
        -- copies of the same real polynomial equation.
        let fStx ← zpolyStx d.poly
        let szStx := natStx d.poly.size
        `(Hex.IsolatedRealRoots.congrRoots
            (by intro x
                rw [HexRealRootsMathlib.aeval_toPolynomial, HexRealRootsMathlib.eval_toPolyℝ,
                    show ($fStx).size = $szStx from rfl]
                simp only [Hex.DensePoly.coeff_ofCoeffs, Finset.sum_range_succ,
                  Finset.sum_range_zero, Polynomial.aeval_X, Polynomial.aeval_C, map_sub, map_add,
                  map_mul, map_pow, map_neg, map_ofNat, map_one]
                norm_num
                constructor <;> intro h <;> linarith)
            $core)
    | _ => pure core
  Term.elabTermEnsuringType term expectedType?

/-- Syntax for the width-annotated / bare term elaborators. The `atomic`
lookahead lets the optional `(width := …)` group backtrack, so a bare term
argument that itself begins with `(` (e.g. `(X^4 - 2 : Polynomial ℝ)`) is not
misparsed as the width group. -/
syntax (name := isolateRootsStx) "isolate_roots"
  (atomic("(" "width" ":=") term ")")? term : term
syntax (name := isolateRootsReplayStx) "isolate_roots_replay"
  (atomic("(" "width" ":=") term ")")? term : term

@[term_elab isolateRootsStx]
meta def elabIsolateRoots : TermElab := fun stx expectedType? => do
  match stx with
  | `(isolate_roots (width := $wt:term) $p:term) => elabIsolate true (some wt) p expectedType?
  | `(isolate_roots $p:term) => elabIsolate true none p expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab isolateRootsReplayStx]
meta def elabIsolateRootsReplay : TermElab := fun stx expectedType? => do
  match stx with
  | `(isolate_roots_replay (width := $wt:term) $p:term) => elabIsolate false (some wt) p expectedType?
  | `(isolate_roots_replay $p:term) => elabIsolate false none p expectedType?
  | _ => throwUnsupportedSyntax

end IsolateProto

end HexRealRootsMathlib

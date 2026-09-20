# Symbolic determinants

Import this unpublished companion to enable symbolic `det` and `det%`:

```lean
import HexPolyDetMathlib

example {R : Type} [CommRing R] (x : R) :
    Matrix.det !![x, 1; 1, x] = x ^ 2 - 1 := by det

example (x : Int) :
    Matrix.det !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x] =
      x ^ 4 - 3 * x ^ 2 + 1 := by det

example (x : Int) : Matrix.det !![x, 1; 1, x] = (det% !![x, 1; 1, x]).value :=
  (det% !![x, 1; 1, x]).proof
```

Dimensions up to three use closed determinant formulas followed by `ring`. Larger symbolic literals use a checked polynomial certificate; rational inputs first undergo proved denominator clearing. Both orientations are supported. The target may be any commutative ring; it need not be a domain or have characteristic zero.

`Hex.normPolyDet` is an opt-in simproc. The published `Hex.norm_det` retains the numeric certificate and Mathlib fallback, and does not import this companion. On a symbolic decline, `det` tries Mathlib directly without repeating the symbolic work. Consequently success through the composed tactic can also come from a closed formula or fallback.

The polynomial certificate treats atoms independently: it does not use a hypothesis `x = 0` or an algebraic relation such as `α ^ 2 = 2`. A target that adds atoms or requires such a relation may decline. Prime-characteristic domains use the shared canonical Nat residue lists and modular operations. Coefficients are reduced modulo the prime; exponents remain formal, so `X ^ 3 - X` over `ZMod 3` is not the zero polynomial. When the residue provider declines its capability conditions, including composite characteristic or a missing domain instance, the universal integer certificate remains available. Denominator clearing currently recognizes rational expressions over `Rat`; division in another carrier can still be treated as an atom.

The fresh-module runner is `scripts/bench/det_symbolic_sweep.py`. It retains all six trials and timeouts, compares identical targets against unmodified `norm_det`, and includes separate 3×3 closed-form probes. The symbolic simproc remains outside the default chain pending measurements establishing an eligible size regime.

Larger certificates select canonical term lists or bounded Kronecker packing using the measured crossover table. The packed soundness proofs discharge the shared witness identities; they do not replay the term-list checker. Residue packing carries exact integer quotient polynomials, and rational row clearing uses the integer checker on the scaled matrix.

`set_option trace.HexMatrix.certificate true` reports the selected route (`term-list`, `packed/plain`, or `packed/signedPacked`), encoding, product bounds, quotient support, and any packing decline. The comparison options `hex.det.checker` (`0` automatic, `1` lists, `2` plain packing, `3` signed packing) and `hex.det.quotients` exercise both arms and missing-payload fallback. Forced packing still obeys the hard size limits. `scripts/bench/det_packed_sweep.py` runs the preregistered forced comparison followed by fixed-table dispatch against Mathlib.

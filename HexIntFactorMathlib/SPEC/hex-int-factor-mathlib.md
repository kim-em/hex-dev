# hex-int-factor-mathlib (depends on hex-int-factor + hex-primality-mathlib + Mathlib)

## Correspondence-only classification

This library is a `correspondence-only-layer`.

Computational conformance owner: `HexIntFactor`
Computational performance owner: `HexIntFactor`

The companion proves that checked `HexIntFactor` data agrees with Mathlib's
factorization, divisor, squarefree, totient, and multiplicative-order APIs. It
does not search for factors or orders, replay a certificate, reify syntax, run
a tactic, or install a decision procedure. All transported values are computed
by `HexIntFactor`; this layer supplies proofs that identify those values with
their Mathlib counterparts.

## Headline correctness theorem

The bridge's headline correctness theorem is
`Hex.Nat.CheckedFactorization.factorization_eq`:

```lean
theorem Hex.Nat.CheckedFactorization.factorization_eq {n : Nat}
    (F : CheckedFactorization n) (p : Nat) :
    n.factorization p =
      (F.raw.factors.find? fun e => e.prime == p).elim 0 (·.exponent)
```

It is the end-to-end correspondence for the checked factorization API: every
multiplicity computed from the certificate's canonical prime-power list is
exactly Mathlib's `Nat.factorization` value for the certified subject. The
divisor, arithmetic-function, square-decomposition, and order transports
below build on this checked correspondence and the core correctness theorems.

## Factorization correspondences

`HexIntFactorMathlib.Factorization` transports the core checker facts and
arithmetic operations:

- `factorization_entry`, `factorization_eq`, and
  `CheckedFactorization.factorization_eq` identify checked multiplicities with
  `Nat.factorization`;
- `factorization_absent` pins zero multiplicity outside the listed prime
  support;
- `factors_eq` and `CheckedFactorization.primeFactorsList_eq` identify the
  canonical expanded prime list;
- `divisors_eq`, `divisors_list_eq`, and `numDivisors_eq_card` identify the
  checked divisor enumeration and count;
- `totient_eq`, `sigma_eq`, `primeFactors_eq`, and `radical_eq` transport the
  corresponding arithmetic functions; and
- `isSquarefree_iff_squarefree`, `squarefreePart_mathlib`, and
  `squareDivisor_mathlib` transport the square-decomposition facts.

Their computational coverage lives in
`conformance/HexIntFactor/Conformance.lean`: complete-certificate acceptance
and rejection, canonical factor support and multiplicity, divisor enumeration,
generalized divisor sums, totient, radical, and squarefree decomposition all
have typical, edge, and adversarial checks. The required PARI/python-flint
oracle independently recomputes factorization and the transported arithmetic
values from the original inputs.

The private expanded-list helpers occur only in theorem statements and proofs.
They are normal forms for correspondence, not a separately advertised runtime
surface.

## Order correspondences

`HexIntFactorMathlib.Order` proves:

- `orderOf_unitOfCoprime`, relating the core natural-number order to Mathlib's
  order of the corresponding unit;
- `orderOf_natCast`, including the nonunit case; and
- `orderOf_eq`, specializing the correspondence to an accepted `OrderCert`.

The transported `Hex.Nat.orderOf` computation is covered by the
`HexPrimality` conformance suite. `HexIntFactor` conformance separately covers
accepted, malformed, and nonminimal order certificates, primitive-root
testing and bounded search, and Carmichael values and laws. This companion
contains no bridge-local executable operation to test independently.

## Boundary

The public umbrella imports only the two correspondence modules. The library
owns no conformance source, compiled benchmark, proof-probe root, oracle
wrapper, executable checker, reifier, tactic, or global instance. It therefore
has no ordinary Phase-3 conformance target and no separate Phase-4 runtime
surface.

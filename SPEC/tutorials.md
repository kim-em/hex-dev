# Tutorials

This document specifies the project's user-facing tutorial deliverables.
The goal is not to restate the library APIs, but to show that the
libraries support recognizable, end-to-end mathematical and engineering
workflows.

Tutorials are a **release artifact**, not a prerequisite for early
scaffolding. They should be written once the corresponding computational
and proof layers are stable enough that the examples are unlikely to be
rewritten immediately.

## Delivery format

Tutorials are delivered as a small **Verso** documentation site built
inside this project and published to **GitHub Pages**.

The site should:

- contain executable Lean code snippets where feasible;
- mix concrete computation with short mathematical explanation;
- emphasize user stories and applications rather than internal library
  architecture;
- be reproducible from the repository without relying on external CAS
  services at page-build time.

The published artifact is part of the project's release surface, alongside
Lean libraries, executable examples, and benchmark reports.

## Tutorial design principles

- Lead with an application that a reader already cares about.
- Show real computations, not just type signatures or constructors.
- Use examples small enough to run comfortably in CI and on GitHub Pages.
- Make the proof/computation boundary explicit: what is being computed,
  what is being certified, and which claims are Lean-checked.
- Prefer a memorable narrative arc over comprehensive API coverage.

## Required tutorial set

The initial tutorial site should include the following capstone pages.

### 1. AES byte arithmetic in `GF(2^8)`

Purpose: demonstrate finite-field construction and arithmetic through a
familiar cryptographic example.

This tutorial should:

- represent AES bytes as polynomials over `F_2`;
- construct `GF(2^8)` using the AES modulus
  `x^8 + x^4 + x^3 + x + 1`;
- show addition, multiplication, inversion, and exponentiation in that
  field;
- connect the computations to AES operations such as `XTIMES()` and the
  multiplicative-inverse step behind the S-box;
- verify a small number of known concrete byte computations.

Primary libraries:

- `hex-gf2`
- `hex-gfq-ring`
- `hex-gfq-field`
- optionally `hex-gfq` if the convenience layer is mature enough

### 2. Why the AES modulus works

Purpose: show a concrete irreducibility argument with a real downstream
consequence.

This tutorial should:

- explain why quotienting by the AES modulus only yields a field if the
  modulus is irreducible over `F_2`;
- use the project's irreducibility machinery to certify that
  `x^8 + x^4 + x^3 + x + 1` is irreducible;
- explicitly connect that certificate to the validity of the AES field
  construction from Tutorial 1;
- avoid drifting into a general-purpose survey of irreducibility testing.

Primary libraries:

- `hex-gf2`
- `hex-poly-fp`
- `hex-berlekamp`
- `hex-berlekamp-mathlib` if needed for the final correctness statement

### 3. Prime splitting via Kummer-Dedekind

Purpose: show that polynomial factorization over finite fields feeds into
serious computational algebraic number theory, not just toy examples.

This tutorial should:

- start from a concrete number field presented by an irreducible integer
  polynomial;
- choose a prime `p` and factor the defining polynomial modulo `p`;
- use Mathlib's Kummer-Dedekind theorem to interpret that factorization as
  splitting data for the ideal `(p)` in the corresponding ring of
  integers;
- make clear which parts come from this project's computational algebra
  libraries and which parts come from Mathlib's number-theory layer.

This page is intended to be **application-first**. It should read as
"what factoring tells us about arithmetic in a number field", not as an
exposition of the Berlekamp-Zassenhaus pipeline.

Primary libraries:

- `hex-poly-z`
- `hex-berlekamp-zassenhaus`
- Mathlib's `NumberTheory.KummerDedekind`

### 4. LLL in cryptanalysis: a toy Coppersmith attack

Purpose: show that lattice reduction supports a recognizable security
application rather than existing only as a subroutine in integer
polynomial factorization.

This tutorial should:

- present a deliberately weak toy RSA-style instance with a hidden small
  root;
- encode the attack as a modular polynomial problem;
- build the corresponding lattice and run LLL;
- recover the hidden value from the reduced basis;
- explain the boundary between the pedagogical toy setup and real-world
  cryptanalytic attacks.

This page is not required to formalize the full Coppersmith theorem.
The requirement is a concrete, honest demonstration that the project's
LLL layer can support the core computational step of such an attack.

Primary libraries:

- `hex-matrix`
- `hex-gram-schmidt`
- `hex-lll`

### 5. The Rubik's cube group

Purpose: show kernel-checked permutation-group computation on a group large
enough that enumeration is out of the question.

This tutorial should:

- write the six face turns as permutations of the 54 stickers and prove the
  order of the group they generate with `perm_group`;
- prove that a single twisted corner, a single flipped edge and an exchange of
  two edges are not in the group;
- prove that adding those three moves gives the group of all reassemblies,
  which contains the cube group with index 12;
- compute the orbits of the stickers and the stabilizer of a corner sticker,
  stating that these values are computed rather than proved.

It does not solve the cube, sample random positions or produce move
sequences: the words `Group.word?` returns are far longer than useful solutions.

Primary libraries:

- `hex-perm-group`
- `hex-perm-group-mathlib`

## Release policy

Tutorials should be published only when the underlying examples are stable
enough to serve as documentation rather than moving targets.

Minimum release bar for any tutorial page:

- the corresponding libraries build in CI;
- the code snippets in the page are checked as part of the docs build or
  an equivalent verification path;
- the example runs natively in Lean;
- the page states clearly whether each key claim is computational,
  proof-producing, or imported from Mathlib.

## Non-goals

- The tutorial site is not a substitute for per-library API reference.
- The tutorial site does not need to cover every library in the DAG.
- Early project milestones are not blocked on tutorial prose.
- The first release of the site need not include styling or content beyond
  what Verso and GitHub Pages require for clear presentation.

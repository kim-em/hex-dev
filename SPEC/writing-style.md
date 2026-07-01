# Writing style

Rules for all prose in this repository: docstrings, SPEC files, and the
manual (`HexManual/`). The audience is a working mathematician who reads
Lean. Write for them: plain, literal, and accurate. When a sentence is
awkward, the fix is almost always to say the ordinary thing directly, not
to reach for a fancier word.

The test for every sentence: read each verb with its object. If the pair
is not something an ordinary English speaker would say about that kind of
thing, rewrite it.

## Banned words

Do not use these as nouns or verbs for a thing in the repository:

- **stack** ("the row-reduction stack") — name the library or the
  operation.
- **core** ("the matrix core", "documented with the matrix core") — name
  the library (`HexMatrix`) or the type (`Hex.Matrix`).
- **bridge** ("the Mathlib bridge") — name the library
  (`HexMatrixMathlib`) and say what it does (relates the executable
  types to Mathlib's).
- **reader** for an accessor or query function ("the linear-algebra
  readers a caller wants") — name the functions, or call them the span
  and nullspace *operations* / *queries*.
- **smoke** ("smoke test") — say "fast check" or name the check.
- **gate** ("gates the merge") — say "required check".

This list grows. When a review rejects a word as jargon, add it here.

## No em-dashes

Do not use em-dashes (`—`). Rewrite as two sentences, a colon, or
parentheses.

## No run-on sentences joined by a semicolon

A semicolon does not license welding two only-loosely-related statements
into one sentence. If the two halves are independent thoughts, write two
sentences.

- Bad: "Each has a determinant law, proved in HexDeterminant;
  HexRowReduce uses them for Gauss-Jordan reduction over a field."
- Good: "Each has a determinant law, proved in HexDeterminant.
  HexRowReduce uses them for Gauss-Jordan reduction over a field."

A semicolon is fine inside a genuine list whose items themselves contain
commas.

## Every verb-object pair must be literal

No metaphorical or anthropomorphic verb applied to an abstract object.
The reader should never have to decode a figure of speech.

- Bad: "This chapter walks the echelon certificate." You cannot walk a
  certificate.
- Bad: "tying the executable answer back to the matrix." You do not tie
  an answer to a matrix.
- Bad: "the linear-algebra readers sit on top of the reduced form."
- Good: name the real action. "This chapter describes the echelon
  certificate." "a soundness theorem proving the computed coefficients
  reconstruct the vector." "From the reduced form we compute the span and
  nullspace."

## Do not invent noun phrases

If a phrase would make a reader stop and ask "what is that?", it is
wrong. "Linear-algebra reader" is not a thing anyone says. Name the
actual function, type, or library.

## Match categories

Identify or relate a concrete object with its concrete counterpart, not
with a field of study or a body of theory.

- Bad: "identifies the executable rank, span, and nullspace with
  Mathlib's linear algebra." Rank is not identified with a subject.
- Good: "identifies the executable rank, span, and nullspace with their
  Mathlib analogues `Matrix.rank`, `Submodule.span`, and `LinearMap.ker`"
  (or "with Mathlib's noncomputable versions").

## Punctuation-separated noun phrases are not a list

Comma-separated noun phrases followed by a trailing verb read as one
clause with a subject and objects, not as a list. Written that way, the
sentence can assert a relationship you did not mean.

- Bad: "The squared norm of a vector, the Gram matrix of the rows, and
  the leading principal submatrices the Bareiss recurrence uses:" reads
  as a claim that the squared norm uses the Gram matrix.
- Good, when you mean a heading for what follows: a noun phrase with no
  trailing verb, introduced by a colon, like "The zero and identity
  matrices:".

## Keep build and verification notes out of the reading flow

A reader in the middle of the mathematics should not be told how the
manual is checked. Do not mix "checked when the chapter builds" or
"closes with a worked example verified at build time" into exposition.
If the fact matters, put it in its own note.

## Be accurate about what exists and what is cited

- Do not call an existing library "forthcoming". Tense and
  cross-references must match reality.
- A docstring or lemma cited for a claim must actually be about that
  claim. "The identity is a left and right unit" is `identity_mul` and
  `mul_identity`, not `identity_mulVec` (which is the left unit on
  vectors).

## Manual examples that cross into Mathlib

A recipe that shows how to prove a *Mathlib* fact by running the
executable is written for someone who already has a Mathlib goal. The
definitions and the theorem statement must therefore be stated in Mathlib
types alone. The translation into `Hex.Matrix` belongs entirely in the
proof body (through `matrixEquiv` and the correspondence theorems).

Antipattern: defining the example matrix as a `Hex.Matrix` and stating
the theorem about `matrixEquiv M`. That presumes the reader started on
the Hex side, which is exactly backwards for a "prove a Mathlib fact"
recipe, and it hides the boundary crossing the recipe is meant to teach.

- Bad: `def M : Hex.Matrix Rat 2 3 := ...` then
  `theorem _ : Matrix.rank (matrixEquiv M) = 1`.
- Good: `def A : Matrix (Fin 2) (Fin 3) Rat := ...` then
  `theorem _ : A.rank = 1`, with the proof introducing the Hex matrix and
  rewriting through the correspondence theorem.

## Naming (cross-reference)

Short verb-noun names, qualifiers in namespaces. See the naming section
of `.claude/CLAUDE.md`. A name whose qualifier list reads like a sentence
belongs in the docstring, not the name.

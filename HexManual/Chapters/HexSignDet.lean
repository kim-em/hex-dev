/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexSignDet
import HexSignDetMathlib.TableProducer
import HexSignDetMathlib.ThomRoots
import HexSignDetMathlib.Naturality
import HexRealRootsMathlib.RealClosed

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "HexSignDet: sign tables and Thom encodings" =>
%%%
tag := "hex-sign-det"
%%%

# Sign determination

A Sturm–Tarski query gives a signed sum. Sign determination gives the
complete distribution: how many distinct roots realize each ordered list
of query signs. `HexSignDet` implements the Ben-Or–Kozen–Reif method
using the shared {ref "hex-sturm"}[Sturm–Tarski query] and checked integer
linear algebra. It also supplies Thom encodings for selected roots,
comparisons of full encodings and signs at a selected root.

The computational import is `HexSignDet`; it is Mathlib-free. The
`HexSignDetMathlib` umbrella exports the finite algebraic correspondence.
The root interpretation, producer and conversion theorems used below additionally
require `HexSignDetMathlib.TableProducer` and
`HexSignDetMathlib.ThomRoots`, together with
`HexSignDetMathlib.Naturality` for conversion. These are development modules in the `HexQuerySemantics` Lake target under
`adapters/`, built in `hex-dev`; their presence does not make them
available in a published companion package. Both libraries are unreleased.
Tau Ceti is a dependency of the Mathlib proofs, never of the computation.

# Sparse tables with exact counts

For query polynomials `Q₁, …, Qₙ`, a sign condition is a list of `n`
integers from `-1`, `0`, `1`. Order matters, and repeated or zero queries
keep their positions. Each count is a natural number of distinct roots;
it is not a multiplicity or a signed sum.

{docstring Hex.SignDet.SignTable +hideFields}

Only positive counts are stored in {name}`Hex.SignDet.SignTable.rows`.
{name}`Hex.SignDet.SignTable.count` returns zero for an omitted condition,
including malformed conditions. Structural well-formedness of a table
does not itself prove that its rows describe polynomial roots.

{docstring Hex.SignDet.determine}

The domain is the same as for Sturm: a nonzero squarefree head and an
open interval with strictly ordered, root-free endpoints. Here the head
is `X²-1`, and the queries are `X` and `X-1`. The root `-1` contributes
`[-1, -1]`; the root `1` contributes `[1, 0]`.

```lean
open Hex Hex.SignDet
namespace SignTables

def x : DensePoly Rat :=
  DensePoly.ofCoeffs #[0, 1]
def p : DensePoly Rat :=
  DensePoly.ofCoeffs #[-1, 0, 1]

def table := determine Sturm.orderSign 7
  p .negInf .posInf [x, x - 1]

#guard table.map (fun t => t.rows.toList) =
  some [([-1, -1], 1), ([1, 0], 1)]
#guard table.map (fun t => t.count [0, 0]) =
  some 0
```

An empty query list has one possible sign condition, `[]`. Its count is
the total root count. A valid domain without roots has an empty sparse
table. Neither case is an invalid domain:

```lean
#guard (determine Sturm.orderSign 7 p
  .negInf .posInf []).map
  (fun t => t.rows.toList) = some [([], 2)]
#guard (determine Sturm.orderSign 7
  (1 : DensePoly Rat) .negInf .posInf []).map
  (fun t => t.rows.toList) = some []
#guard (determine Sturm.orderSign 7
  (0 : DensePoly Rat) .negInf .posInf []).isNone

end SignTables
```

For several queries on one head and interval, call
{name}`Hex.Sturm.prepare` once and pass its result to
{name}`Hex.SignDet.buildTablePrepared` or
{name}`Hex.SignDet.determinePrepared`. Preparation binds the coefficient
sign function as well as the head and endpoints. It does not authorize
reuse in another coefficient context.

`buildTablePrepared` exposes internal construction diagnostics for
arbitrary supplied coefficient operations. `determinePrepared` has a
diagnostic panic branch with an empty-table fallback. The companion's
{name}`Hex.SignDet.determinePrepared_success` proves that this branch is
unreachable under a lawful interpretation and the prepared sign binding.
An arbitrary provider's successful output is insufficient to establish
those hypotheses.

# Moments, rank and literal replay

The method recursively splits the ordered queries. Tarski queries of
products give moments of their sign conditions. The integer system uses
a checked rank certificate and a nonzero scaled left inverse to recover
counts. Zero counts are pruned; retained columns and rows keep their
order. The producer and checker share these exact finite structures.

{docstring Hex.SignDet.Replay.check}

The checker accepts supplied evidence: it checks children, literal query
bindings, Tarski certificates, rank data and moment equations. It does
not accept an integer system merely because that system has a unique
solution. {name}`Hex.SignDet.System.unique` proves uniqueness of an accepted finite
system. Under a lawful coefficient interpretation,
{name}`Hex.SignDet.Replay.count_roots` proves that any accepted replay
has exactly the actual root counts, including omitted sign conditions.

Coefficient storage need not carry a Mathlib field instance or have an
injective representation. Computation uses explicit operations and a
total sign function. Its mathematical interpretation must preserve the
operations used and reflect zero: only the stored zero may have value zero.
Nonzero values may have several representatives. This distinction permits
canonical
fields and noncanonical representatives to use the same polynomial API.

# Selecting a root with derivatives

A Thom encoding records signs of formal derivatives of the original
head. Derivatives retain their original scaling: a sign-changing
normalization would change the encoding. Derivative indices start at
one, are distinct and lie within the head's degree.

{docstring Hex.SignDet.RawDescriptor +hideFields}

A raw descriptor is a claim. {name}`Hex.SignDet.Descriptor` contains
accepted count-one evidence for that exact context, head, interval and
ordered derivative list. A partial list of derivatives can select a root
when its sign condition has count one; well-formedness alone is insufficient.

The first derivative of `X²-1` is `2X`. Its negative and positive signs
select the two roots even on the whole line, without rational separators.
The empty derivative word on that same interval is ambiguous.

```lean
namespace ThomRoots
open SignTables

def raw (signs : List Int) :
    RawDescriptor Rat Nat :=
  ⟨7, p, .negInf, .posInf, [1], signs⟩

def accepted (r : RawDescriptor Rat Nat) :
    Bool :=
  match Descriptor.build
      Sturm.orderSign 7 r with
  | .ok (.ok _) => true
  | _ => false

#guard accepted (raw [-1])
#guard accepted (raw [1])
#guard !accepted (raw [0])
#guard !accepted {raw [1] with context := 8}
#guard !accepted
  {raw [] with indices := [], signs := []}

end ThomRoots
```

{name}`Hex.SignDet.Descriptor.buildRoots` constructs the complete root
list from full derivative words. The mathematical producer theorem below
proves success, complete coverage, absence of duplicates and strict order.
Multiplicity handling and adjoining the selected algebraic root belong
to the real-closure library.

For full encodings of the same head, the Thom comparison rule inspects
the highest differing derivative slot. The shared sign in the immediately
next higher derivative slot must be
nonzero and determines its direction. A zero or missing next slot returns
`none`:

```lean
#guard Thom.compareSigns [-1, 1] [1, 1] =
  some .lt
#guard Thom.compareSigns [1] [-1] = none
```

{name}`Hex.SignDet.Thom.compareSigns` checks a finite word rule. It does
not establish root realization or compare roots of different heads.
Use {name}`Hex.SignDet.Descriptor.fullOrder` on validated full descriptors
with their literal head and context checks. Reencoding to a different
head and cross-field comparison require the corresponding checked
conversion and embedding laws.

# Signs at a selected root and shared evidence

{name}`Hex.SignDet.SelectedSigns` combines the descriptor's derivative
queries with the caller's exact ordered query list. Its checker requires
a complete joint table whose descriptor prefix has exactly one extending
row of count one. Counting one matching row without excluding other
matching observations would not justify the selected signs.

{docstring Hex.SignDet.RawDescriptor.checkSigns}

The DAG interfaces share repeated evidence. Encode a tree with
{name}`Hex.SignDet.Dag.encode`, validate the graph once with
{name}`Hex.SignDet.Dag.validate?`, then use its memo for several selections.
The memo binds the full head, endpoints, context and ordered queries.
Forward references, missing entries and invalid unreachable entries reject:
validation checks every stored entry, not only entries reachable from the root.

{name}`Hex.SignDet.Replay.signOperands` and
{name}`Hex.SignDet.Dag.signOperands` expose finite coefficient-sign
dependencies. Their congruence lemmas transfer the exact checker result
when a replacement sign function agrees on every required operand.
These inventories may contain repetitions and are not execution traces.
Cross-level context reconstruction and automatic arithmetic evidence
remain distinct from these finite congruence laws.

# Printing and reading a selected-root subject

The `HexSignDet` umbrella includes
{name}`Hex.SignDet.Codec.descriptor` and
{name}`Hex.SignDet.Codec.readDescriptor`. They encode and read all six
fields of a raw descriptor: context, head, lower endpoint, upper endpoint,
derivative indices and derivative signs. The derivative lists retain their
order. The reader rejects malformed records, but a parsed record is still
an unchecked root claim.

Use {name}`Hex.SignDet.Codec.readDescriptorBinding` when a packet must
refer to a particular caller-supplied descriptor. It compares the complete
parsed subject with that descriptor, including the indices and signs that
distinguish roots of the same head on the same interval. Successful binding
gives the following literal equality through the existing public theorem:

```lean
namespace RootPackets
open Codec

variable (raw : RawDescriptor Rat Nat)
variable (packet : Json)
variable
  (accepted : readDescriptorBinding
    ValueCodec.rat ValueCodec.nat
    raw packet = .ok ())

example : readDescriptor
    ValueCodec.rat ValueCodec.nat
    packet = .ok raw :=
  readDescriptorBinding_checked
    ValueCodec.rat ValueCodec.nat
    raw packet accepted

end RootPackets
```

This theorem establishes subject binding. Root validity requires a
{name}`Hex.SignDet.Descriptor` carrying accepted count-one evidence;
{name}`Hex.SignDet.Descriptor.ofReplay?` is one way to obtain it.
The owning `DescriptorCodec` conformance module checks changed contexts,
heads, the lower endpoint, indices and signs, as well as malformed field counts and
coefficient records.

{name}`Hex.SignDet.Codec.read_descriptor_of` proves that printing and
reading the subject preserves it literally. Its hypotheses require the
coefficient reader to cover the stored head and finite endpoints, and the
context reader to cover this actual context. A partial coefficient reader
need not satisfy a roundtrip law for every possible coefficient.

For full replay graphs, {name}`Hex.SignDet.Dag.encodeBytes` prints the
literal graph and {name}`Hex.SignDet.Codec.decodeGraph` parses it after
the byte syntax and resource checks. Parsing checks references, context and domain
bindings; {name}`Hex.SignDet.Dag.decodeBytes` additionally runs replay
against the caller's sign operation and ordered query list.
{name}`Hex.SignDet.Dag.decode_replays` identifies the returned checked
tree with the parsed graph's actual replay result.

{name}`Hex.SignDet.Codec.decode_graph_covered` proves the byte roundtrip
for partial readers covering every stored graph coefficient and context.
It also requires a valid root index, the node shape, context and domain bindings
for every entry, earlier-only child references, and acceptance by the
byte syntax and resource checks. Subject coverage alone does not establish
these graph conditions.

For the separate tree-to-graph encoder, {name}`Hex.SignDet.Dag.check_encode_eq`
preserves the complete checker result, including rejection.
Encoding an invalid tree or structurally expanding a graph with
{name}`Hex.SignDet.Dag.expand?` does not validate its mathematical claims.

{name}`Hex.SignDet.Dag.decodeDescriptor` checks graph bytes against the
caller's full raw descriptor and returns a validated count-one descriptor.
{name}`Hex.SignDet.Dag.decodeSigns` checks supplied query signs against an
already validated descriptor, using the supplied graph's joint-table evidence.
Neither reader calls the selected-sign producer to replace missing evidence.
{name}`Hex.SignDet.Dag.decodeDescriptor_raw` preserves the exact requested
subject; {name}`Hex.SignDet.Dag.decodeSigns_evidence` preserves the caller's
claimed signs exactly and identifies the checked replay used for them.

# Converting coefficients and contexts

To move a selected root to another coefficient representation, use
{name}`Hex.SignDet.Descriptor.convert`. This operation maps the literal
subject and builds fresh checked evidence with the target sign operation
and context. Its result distinguishes an internal {name}`Hex.SignDet.BuildError`
from an input diagnostic for the mapped subject, such as an invalid domain
or an absent or ambiguous sign condition. Merely changing a context tag does not authorize
reuse of the original certificate.

The correspondence uses source and target interpretations in one ordered
real-closed field. Value preservation means `g (convert a) = f a` for every
coefficient `a`, with source interpretation `f` and target interpretation `g`.
The conversion must also reflect zero. Each law states the arithmetic and
sign hypotheses it uses. Conversion success uses target negation and inverse
laws; root preservation needs neither interpretation's negation or inverse
laws. Selected-root sign and comparison laws additionally use source negation
and inverse; comparison also uses division. With its stated hypotheses,
{name}`Hex.SignDet.Descriptor.convert_success` proves actual conversion
success, and {name}`Hex.SignDet.Descriptor.convert_root` proves preservation
of the selected root. The checked returned descriptors also satisfy:

* {name}`Hex.SignDet.Descriptor.convert_signAt` preserves the total sign
  at that root for the converted query polynomial.
* {name}`Hex.SignDet.Descriptor.convert_compare` preserves all three
  comparison results after both descriptors convert successfully, even
  when they have different defining polynomials.

For tables and root lists, run the existing producers on the mapped head,
endpoints and ordered queries, using the same `reduced` flag for the table
calls. The following laws compare those actual
source and target runs; they do not convert an already returned table or
convert each descriptor in an existing root list:

* {name}`Hex.SignDet.determine_convert_isSome` preserves the table API's
  success domain. {name}`Hex.SignDet.determine_convert_counts` equates
  every count in actual returned tables, including omitted sign words.
* {name}`Hex.SignDet.Descriptor.buildRoots_convert_isSome` preserves
  root-list success. {name}`Hex.SignDet.Descriptor.buildRoots_convert_roots`
  identifies the interpreted, ordered returned root lists, including empty
  lists.

These are value-preserving conversion laws with explicit semantic
hypotheses. They do not construct a common coefficient field or an
ordinary-real realization of a nested tower. The owning `FieldChecks`
conversion cases exercise {name}`Hex.SignDet.Descriptor.convert` and
{name}`Hex.SignDet.Descriptor.signAt`; its root-list cases use unconverted
inputs. The producer-run conversion laws above have ordinary-kernel
axiom checks in the owning `RootSemantics` diagnostic module.

# The Mathlib correspondence

The interpretation targets an ordered real-closed field, which may be
non-Archimedean. Sign tables and Thom encodings therefore apply to
infinitesimal coefficients without rational separating intervals.
The laws relate the supplied coefficient operations and sign function
to that model; they do not construct a joint ordinary-real realization
of an arbitrary nested tower.

{docstring Hex.SignDet.determine_correct}

This theorem characterizes every returned count, including omitted words.
{name}`Hex.SignDet.buildTablePrepared_success` establishes actual producer
success, while {name}`Hex.SignDet.determine_isSome` characterizes the domain.
These producer obligations are separate from the arbitrary-certificate
soundness proved by {name}`Hex.SignDet.Replay.count_roots`.

{docstring Hex.SignDet.Descriptor.buildRoots_roots}

The following specialization reuses the same complete-producer theorem
as the downstream sign consumer. Given a mathematical root in a valid
domain, it obtains a descriptor from the actual returned list without
assuming that production succeeded.

```lean
open HexPolyMathlib.Interpret
open HexRealRootsMathlib
open scoped Classical
namespace RootCoverage
noncomputable section

def value (d : Descriptor ℝ Nat
    Sturm.orderSign 7) : ℝ :=
  d.root id (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    HexSturmMathlib.orderSign_eq

variable (p : DensePoly ℝ)
variable (a b : Endpoint ℝ)
variable
  (domain : HexSturmMathlib.Domain
    id (fun _ => Iff.rfl) p a b)
variable (x : ℝ)

example (member : x ∈ Tarski.rootsIn
    (interpret id (fun _ => Iff.rfl) p)
    (a.map id) (b.map id)) :
    ∃ out,
      Descriptor.buildRoots
        Sturm.orderSign 7 p a b =
          .ok (some out) ∧
      ∃ d ∈ out, value d = x := by
  obtain ⟨out, produced, coverage, _, _⟩ :=
    Descriptor.buildRoots_roots id
      (fun _ => Iff.rfl) rfl
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      HexSturmMathlib.orderSign_eq
      (fun _ => rfl) (fun _ => rfl)
      7 p a b domain
  refine ⟨out, produced, ?_⟩
  exact List.mem_map.mp
    ((coverage x).mp member)

end
end RootCoverage
```

The owning conformance suites separately guard ordinary-kernel axioms
and check the table, descriptor, selected-sign, replay and codec contracts.
Exact Z3 and python-flint oracles check emitted fixtures. The retained
BKR/Thom performance reports distinguish computation, replay and witness
growth; neither the examples here nor theorem-application timings supply
computational performance evidence.

# Joint re-encoding inputs

For odd n at least three, use the source heads `X^n-1` and `X^n+1`, whose
unique real roots are 1 and -1. The shared gcd producer returns the literal constant -2, so the actual
common head is `-(X^(2n)-1)/2`, with exactly those two real roots. The fixture
retains that scaling and its reversed target derivative signs; it does not
substitute a monic normalization. The fixture in `bench/HexSignDet/Joint.lean`
constructs actual partial descriptors using the highest derivative's positive
sign, completes both through `Descriptor.buildCompletion`, and invokes the
actual cross-polynomial `Descriptor.buildComparison`. It checks the common
head literally and requires the result `gt`.

The implementation constructs two separate re-encoding tables. Each query list
contains the 2n target derivatives, the source defining equation, and its n
source derivatives, in exactly that order. Thus each has `s=3n+1` queries;
this is neither a combined list of both sources nor just the common head's
derivatives. The total query degree is `D=n(5n-1)/2`. The two source derivative
polynomial lists agree, but their defining equations and selected-root sign
vectors differ. They must retain separate bindings.

The reduced tables come directly from the two re-encoding evidence trees
returned by the comparison producer. The unreduced producer receives precisely
the same prepared domain and ordered query list. Both complete tables must
match direct rational evaluation at the known roots -1 and 1, each with count
one. The target descriptor words are checked at their selected roots. The
fixture checks actual graph replay and byte-decoded replay in both modes.
A full ternary reference would have `3^(3n+1)` columns and is not enumerated;
small-input reduced/full agreement has its separate existing evidence.

The independent Python validator reconstructs every literal polynomial,
source slot/sign vector and both complete tables using integer factorials
and evaluation, including the actual negative half-scale of the common head. It computes candidate dimensions recursively from the two
known-root restrictions before solving: leaf dimensions are three, and each
parent dimension is the product of the distinct child supports. Each query
polynomial is distinct, so exact DAG encoding cannot identify two nodes with
different query lists. It checks all tree/graph dimensions and edge counts.
The matrix inverse/denominator bits, query-witness bits and certificate bytes
are recorded positive integers without a claimed closed formula. Witness
bits scan stored query/reduction certificates, including quotient and scaling
fields; they are not peak intermediate values, allocated bytes or live memory.

`inspect-joint` selects degrees 3, 7, 15, 31 and 63; `inspect-joint N` selects
one development input. This is an untimed correctness and input inventory.
No timing registration, cost-model verdict or performance gate follows from
it. Separate completion, comparison/re-encoding, reduced/direct construction
and checking measurements, intermediate coefficient observations and allocation
coverage remain required before the joint-encoding Phase-4 gate can pass.

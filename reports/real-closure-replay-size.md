# Real-closure selected-sign graph sizes

The driver constructs `alpha_1 = sqrt(2)` and `alpha_2 = sqrt(alpha_1)`, each
selected in `(1,2)`. At each level it produces one joint selected-sign
certificate for `n` queries, for `n = 1,2,4,8,16,32`. One family repeats
`X-1`; the other uses the distinct queries `X-i`, for `0 <= i < n`. Both
families run the production `Descriptor.buildSigns`, encode its actual replay
with `Dag.encode`, and check the resulting bytes with `Dag.decodeSigns`.

The [retained analysis](bench-results/real-closure-replay-size/analysis.json)
contains all 24 rows. The [manifest](bench-results/real-closure-replay-size/manifest.json)
binds the driver, independent oracle, fixture, analysis and native binary by
SHA-256. Rebuild with `lake build hexrealclosure_replay_size`; run the native
command and analysis command in the manifest. CI reproduces the entire native
fixture, runs the oracle and tests changed inputs and graph/count mutations.
The FLINT oracle checks the exact defining and query coefficients in
`Q(gamma)` with `gamma^(2^depth)=2`. Both selected positive roots lie strictly
between 1 and 2, which gives the query signs independently of Hex. Its graph
checks authenticate shape, bindings and child query slices; the mathematical
certificate replay is performed by the native Lean checker.

## Nodes, edges and occurrences

An edge is one child-reference slot. Two slots referencing the same child
count as two edges. An occurrence is one node in the expanded replay tree,
including each repeated visit to a shared child. All encoded entries are
reachable from the root in these fixtures.

| Queries n | Repeated: nodes | Repeated: edges | Distinct: nodes | Distinct: edges | Tree occurrences, both families |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 0 | 1 | 0 | 1 |
| 2 | 2 | 2 | 3 | 2 | 3 |
| 4 | 3 | 4 | 7 | 6 | 7 |
| 8 | 4 | 6 | 15 | 14 | 15 |
| 16 | 5 | 8 | 31 | 30 | 31 |
| 32 | 6 | 10 | 63 | 62 | 63 |

The counts agree at both depths. The balanced producer gives the occurrence
recurrence `T(1)=1`, `T(2m)=1+2*T(m)`, hence `T(n)=2*n-1` for these inputs.
For the repeated family, identical left and right subtrees are shared:
`D(1)=1`, `D(2m)=1+D(m)`. This gives `D(n)=1+log2(n)` and
`E(n)=2*log2(n)` at the measured powers of two. The distinct queries prevent
sharing between disjoint query slices in this family; its node and edge counts
are `2*n-1` and `2*n-2`. These recurrences describe these literal inputs and
the current balanced producer.

## Operand and evidence sizes

All input queries have outer degree one. The defining polynomials have degree
two. The analysis counts rational leaves and numerator/denominator bits in the
literal input coefficients, including stored algebraic representatives at
depth two. It separately reports graph bytes and node payload bytes, with
compact UTF-8 JSON delimiters and no transport whitespace. The unique payload
sum counts each stored node once; the unshared payload sum follows every tree
occurrence. These payload sums include node-local context frames and integer
certificates, and exclude child-reference indices and graph delimiters.

For a node with local payload size `b_i`, expanded occurrences and payload
bytes follow `t_i=1+t_left+t_right` and
`u_i=b_i+u_left+u_right`; leaves have `t_i=1`, `u_i=b_i`. The oracle computes
these recurrences in the actual postorder graph, retaining multiplicity when
both children have the same index. Unique bytes are `sum_i b_i`.

| Depth | Family | n | Compact graph bytes | Unique node payload bytes | Unshared node payload bytes |
| ---: | --- | ---: | ---: | ---: | ---: |
| 1 | Repeated | 32 | 8,598 | 8,530 | 81,133 |
| 2 | Repeated | 32 | 12,769 | 12,701 | 120,267 |
| 1 | Distinct | 32 | 83,067 | 82,474 | 82,474 |
| 2 | Distinct | 32 | 123,107 | 122,514 | 122,514 |

Graph node count alone omits query-array width, integer certificate sizes and
nested coefficient/context payloads. These exact size observations do not
bound replay elapsed time or the cost of coefficient signs, producer arithmetic
or kernel quotation. `Dag.encode` visits the supplied tree occurrences before
sharing entries. General interleaved towers, deeper coefficient growth and
elapsed replay scaling require their own evidence.

# Public graph encoding equations and reader reduction

`Hex.SignDet.Codec.readGraph` and the existing readers it calls expose their
definitions across ordinary module imports. A consumer can reduce a concrete
graph read in an ordinary kernel proof using `import HexSignDet`, including
through the optional `import HexRCF.RealCoefficients`. A private `import all`
is unnecessary for this structured graph-reader path.

This is raw decoding. A successful read checks shape, dimensions, child indices,
canonical rational and polynomial encodings, and literal context/domain bindings;
it does not check the certificate's arithmetic identities,
support completeness or selected-root claim. Independent replay and the existing
semantic theorems remain necessary. The conformance fixtures deliberately contain
raw arithmetic witnesses without claiming they pass replay.

## Reader API decisions

These are existing public operations with unchanged bodies and types. Exposing
their definitions makes the existing computation available to the kernel in an
importing module. It introduces no algorithm, codec, mathematical hypothesis or
new trusted primitive.

| Reader | Reason to expose its existing definition |
| --- | --- |
| `readGraph` | Reduce the version, root index, entry traversal and graph result |
| `readEntry` | Reduce each node and its literal caller bindings |
| `readChildren` | Check both references against the earlier-entry prefix |
| `readNode` | Decode every dependent-size node field |
| `readSystem` | Decode ordered rows, columns, counts, values and inverse |
| `readBasis` | Check rank dimensions and bounded selected indices |
| `vector` | Construct the length-indexed fields after checking literal length |
| `matrix` | Read each row against both dimensions |
| `index` | Construct an index only after its bound check |
| `readOption` | Traverse absence or exactly one present record |
| `readRemainder` | Read all literal scales and quotient coefficients |
| `readTerminal` | Read an optional terminal scale and polynomial |
| `readChain` | Traverse initial witness, steps, degrees and terminal |
| `readTarski` | Traverse the complete moment certificate |
| `readReductionStep` | Check the original query index before reading a step |
| `readReduction` | Read ordered reduction steps and their result |
| `readPreparation` | Read the original-query preprocessing steps |

The already exposed coefficient, endpoint, JSON and binding helpers remain
unchanged. This reader audit concerns `readGraph`; it does not claim kernel reduction
coverage of every byte parser, producer or independent replay operation.

## Encoding equations

`Codec.graph_eq`, `entry_eq` and `node_eq` expose the literal graph, entry and
node record shapes without exposing the encoder bodies. The `entry_fn` equation
rewrites the encoder as a function, including inside `Codec.array` maps.
`option_none` and `option_some` retain both optional payload shapes;
`system_eq`, `basis_eq` and `encodeMatrix_eq` identify the stored integer fields.
`tarski_eq`, `chain_eq`, `remainder_eq`, `terminal_eq`, `reductionStep_eq`,
`reduction_eq` and `preparation_eq` identify all nested witness fields. These
are equations for arbitrary raw records, without structural or arithmetic
acceptance premises. The reference encoder bodies remain hidden across imports;
consumers use the public equations rather than private imports. Function forms
`tarski_fn`, `remainder_fn`, `reductionStep_fn` and `reduction_fn` also rewrite
partially applied encoders beneath arbitrary arrays, lists and optional payloads.
The `moments_encode` and `reductions_encode` public-import consumers check this
without fixing lengths or entries. `moments_encode` additionally requires that
reflexivity alone cannot open the hidden Tarski encoder.

The ordinary-import `PublicCodec` consumer composes these equations to identify
both a size-zero graph and a size-one numerical graph with all nested evidence
present. `graph_nested_literal` binds the raw records to the exact JSON packet
already exercised by `graph_nested`, including both chains, their initial and
nonempty subsequent remainder witnesses, a present terminal, optional reduction,
query preparation and a 1×1 system. The deliberately zero scales and system
denominator are literal data, not a claim of arithmetic acceptance. Its basis
has rank zero; the existing conformance retains positive-rank coverage.

The nested equation and general array-consumer guards require exactly
`propext`; the composed numerical graph proof requires exactly `propext`,
`Classical.choice` and `Quot.sound`. The reference equations are proved by
reflexivity, and no global simplification attributes or executable bodies change.

This removes the nested structured-encoder equation gap. It does not identify
an arbitrary numerical tower frame: the actual coefficient/context codecs and
stored history still need their own exact bindings. `ValueCodec.Lawful` states
only `decode (encode value) = .ok value`; it supplies no converse identifying
an arbitrary accepted literal with an encoding. Arithmetic replay, strict
rejection of missing reached records and general joint ordinary-real export
remain separate owner obligations.

## Verification

[`PublicCodec.lean`](../conformance/HexSignDet/PublicCodec.lean) imports only the
ordinary computational umbrella. Its ten `decide +kernel` proofs cover an empty
malformed graph, a complete size-zero node, a nonempty nested moment/reduction/
preparation graph, wrong literal context, a forward child reference and a wrong
version, a valid earlier-child pair, an invalid right child, and changed caller
polynomial/endpoints. The nested fixture traverses all seventeen readers above, including
the present optional terminal and reduction branches. The nonempty system and its
1×1 inverse exercise vector/matrix reading; the zero-rank basis reads empty index
vectors. Arbitrary positive-rank evidence still has the existing
conformance coverage rather than a new kernel-reduction claim here.

[`PublicGraphCodec.lean`](../conformance/HexRCF/PublicGraphCodec.lean) imports
only the optional public umbrella and checks the reported empty-input reduction
and a complete nonempty node directly. Every named proof has a CI-built exact axiom guard within the standard
allowlist `propext`, `Classical.choice` and `Quot.sound`; some encoding
equations use only `propext` or no axioms. There is no private
import, admission, `native_decide` or external runtime oracle in these proofs.

Both modules extend the existing conformance library. Reproduce from the root:

```sh
lake build HexSignDet +HexSignDet.PublicCodec +HexRCF.PublicGraphCodec \
  +HexSignDet.Conformance +HexSignDet.FastCheck +HexSignDet.DescriptorCodec
```

The small fixtures establish reduction and selected refusal behavior, without a
claim about practical kernel cost on large graphs. They supplement the existing
compiled codec conformance and the kernel-replay examples.

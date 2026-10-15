# Public graph-reader reduction

`Hex.SignDet.Codec.readGraph` and the existing readers it calls expose their
definitions across ordinary module imports. A consumer can reduce a concrete
graph read in an ordinary kernel proof using `import HexSignDet`, including
through the optional `import HexRCF.RealCoefficients`. A private `import all`
is unnecessary for this structured graph-reader path.

This is raw decoding. A successful read checks shape, dimensions, child indices
and literal context/domain bindings; it does not prove any arithmetic identity,
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
unchanged. This audit concerns `readGraph`; it does not claim kernel reduction
coverage of every byte parser, producer or independent replay operation.

## Verification

[`PublicCodec.lean`](../conformance/HexSignDet/PublicCodec.lean) imports only the
ordinary computational umbrella. Its eight `decide +kernel` proofs cover an empty
malformed graph, a complete size-zero node, a nonempty nested moment/reduction/
preparation graph, wrong literal context, a forward child reference and a wrong
version, a valid earlier-child pair and an invalid right child. The nested fixture traverses all seventeen readers above, including
the present optional terminal and reduction branches. A zero-rank basis exercises
the vector/matrix readers; arbitrary positive-rank evidence still has the existing
conformance coverage rather than a new kernel-reduction claim here.

[`PublicGraphCodec.lean`](../conformance/HexRCF/PublicGraphCodec.lean) imports
only the optional public umbrella and checks the reported empty-input reduction
directly. Every named proof has a CI-built axiom guard allowing exactly the three
standard axioms `propext`, `Classical.choice` and `Quot.sound`. There is no private
import, admission, `native_decide` or external runtime oracle in these proofs.

Both modules extend the existing conformance library. Reproduce from the root:

```sh
lake build HexSignDet +HexSignDet.PublicCodec +HexRCF.PublicGraphCodec \
  +HexSignDet.Conformance +HexSignDet.FastCheck +HexSignDet.DescriptorCodec
```

The mathematical declaration assessments remain applicable: stripping only the
new `@[expose]` attributes from the four owned production files gives their exact
previous source at `8572e4a1e5bc03c51438decb8ea796cfe118abad`. Existing review
archives retain their original source bindings. No native computation, fixture
bytes, package dependencies, phase counters or publication state change.

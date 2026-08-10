# Lean encoded locked-NAND semantic boundary

This milestone gives the locked-NAND construction one exact external bit
format and proves that the resulting bit-to-bit transformation has the
intended meaning. It follows the legacy Section 17 construction already
reconstructed in the typed Lean modules. If Lean exposes a contradiction in
that legacy route, the formal development must change rather than conceal the
failure.

## Plain-language result

The earlier milestones proved the important mathematical behavior of a
larger NAND circuit: a source circuit is satisfiable exactly when the best
equivalent implementation crosses a known size threshold. Until now, that
result lived behind Lean's strongly typed internal objects.

This step defines the actual zeros and ones used to represent:

- a source NAND circuit;
- every gate and wire source;
- the complete locked-NAND candidate, including every exposed output; and
- the exact source-derived threshold.

Lean proves that encoding and then decoding these objects returns the same
objects. It also proves that malformed input is rejected, not silently
reinterpreted. Most importantly, for every input bitstring, the source bytes
describe a satisfiable circuit exactly when the transformed bytes describe a
locked-NAND instance above its encoded threshold.

That is a necessary interface on the route to a real reduction. It prevents a
future machine from proving that it runs quickly while emitting a different
or incomplete object.

## Technical result

The new modules are:

- `PNP.Concrete.LockedNANDEncoding`, which defines the strict grammar,
  normalization, intrinsic elaboration, reification, and codecs; and
- `PNP.Concrete.LockedNANDReduction`, which defines the concrete source and
  target languages and the pure semantic transformation.

The four-bit version-zero alphabet has twelve assigned codes:

| Code | Token |
| --- | --- |
| `0000` | version zero |
| `0001` | unary unit |
| `0010` | natural-number terminator |
| `0011` | input source |
| `0100` | false constant |
| `0101` | true constant |
| `0110` | gate source |
| `0111` | gate terminator |
| `1000` | program terminator |
| `1001` | output-list terminator |
| `1010` | threshold marker |
| `1011` | instance terminator |

The four spare codes `1100` through `1111`, incomplete four-bit groups,
incorrect counts, invalid source indices, trailing tokens, and malformed
terminators all fail closed.

### Legacy output normalization

The boundary accepts a circuit whose selected output is an input, a constant,
or an existing gate. Before elaboration it applies the legacy normalization:

- an existing gate output is unchanged;
- an input output gains two NAND gates implementing double negation;
- false gains one `NAND(true, true)` gate; and
- true gains one `NAND(false, false)` gate.

`RawCircuit.normalize_eval` proves directly, over the untyped boundary
semantics, that every branch preserves the output Boolean function.
`RawCircuit.normalize_idempotent` proves that the operation cannot keep
adding gates.

### Complete target bytes

Successful source decoding constructs
`LockedNANDGlobalCandidates.fullCandidate circuit`, not a descriptor for
that candidate and not a caller-supplied certificate. The target encoding
contains the candidate's actual gate list, complete output word, and
`lockedBaselineCount circuit.program`.

`EncodedLockedNANDThreshold` decodes and intrinsically validates those bytes,
then evaluates the existing exhaustive `referenceMinimum` on the decoded
candidate. The empty word and every failed decode are outside the language.

The principal all-bitstring theorem is:

```lean
theorem buildLockedNANDInstance_correct (bits : BitString) :
    EncodedNANDSAT bits ↔
      EncodedLockedNANDThreshold (buildLockedNANDInstance bits)
```

On a valid source, `buildLockedNANDInstance` returns the exact complete
locked instance. On malformed input it returns the empty word, which is
proved not to be a valid target instance.

## Kernel and regression evidence

`lean-audit/PNPConcreteLockedNANDSemanticReductionAxiomAudit.lean` audits all
36 theorem declarations and twelve executable interfaces. Of those 48
audited declarations:

- four have empty axiom closure;
- 37 use only `propext`; and
- seven use only `propext` and `Quot.sound`.

None reaches `Classical.choice`, `sorryAx`, a project axiom, host-side
schedule lookup, a caller certificate, `native_decide`, or a SAT shortcut.

The Lean regression covers reserved and incomplete tokens, input and both
constant normalization branches, direct normalization semantics, all codec
round trips, complete candidate bytes, satisfiable and unsatisfiable source
circuits, the exact valid builder branch, malformed input, empty-target
rejection, and the universal correctness theorem. The hostile JavaScript
audit rejects grammar changes, dropped theorem or transcript lines, altered
candidate measurement, nonempty malformed output, hidden assumptions,
shortcuts, and reduction overclaims.

## Mechanically generated publication evidence

Inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-08-11-123` records 26,624 declarations,
13,928 theorems, 7,165 assumption-free theorems, 14,939 excluded private
declarations, 241 source-closure modules, and 2,498 reviewed milestone
candidates. The canonical inventory is 17,275,021 bytes with SHA-256
`231781715e011ebf8b583ce3c26f9896622d6962faaf8fcebd68f36e511ea003`.
The reviewed Lean source-closure SHA-256 is
`e30716e5e6ec0ad0f7c084a66d9ff28c1a8cf5a7008b5fc8caff81205e51eb15`.

Publication map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-11-124` contains 102 milestones: 99
earned and two deliberately unearned. It pins eleven theorem types for
`concrete-locked-nand-encoded-semantic-boundary`; the complete pin inventory
contains 2,498 theorem types. The map is 809,177 bytes with SHA-256
`96e4a8b21a717e2190b5eed64ed50f27402b7690b7b80a52bb98782984f54258`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-124` records the semantic
boundary fields as true while retaining all four project assumptions, all six
blockers, unset activation fingerprints, an absent `PNP.Main.p_eq_np`, and a
false concrete publication gate. The status is 2,034,357 bytes with SHA-256
`0f3e05664980c80d3c8a9fb5cceb4cb10cefaa05a96ea2d0f523c2663956fbc3`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-11-124` has a
211,420-byte TeX source with SHA-256
`b81fbdd17af61400d2883493ee90417affddd37f5d23567ede3d808bb417b0e2`
and an 82-page, 449,511-byte PDF with SHA-256
`e998779d189f762ffcbcdb82b51de8a15bd0c7c8e4be6d463d5c833323ae45ef`.

## Exact boundary and strategic next step

`buildLockedNANDInstance` is a pure Lean specification. It is not a
`PolynomialReduction`, not a `RawRefinement`, and not a finite work machine.
This milestone proves no parser runtime, emitter runtime, output-size
polynomial, CNFSAT-in-P theorem, NP-hardness transport, abstract
`PNP.LockedNANDThreshold` discharge, or P = NP.

The following milestones now supply both the executable parser/validator
machine and the exact target emitter for this version-zero grammar. Their
strict composition is bounded and connected through recursive
`RawRefinement`, and the successor polynomial-reduction milestone packages
that exact function with this encoded language equivalence.

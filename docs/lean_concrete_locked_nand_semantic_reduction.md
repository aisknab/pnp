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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-12-129` records 27,573 declarations,
14,360 theorems, 7,314 assumption-free theorems, 15,002 excluded private
declarations, 247 source-closure modules, and 2,557 reviewed milestone
candidates. The canonical inventory is 17,787,380 bytes with SHA-256
`859ef0595f1eeea872518b0f399a788225e3a2ed9fefe987c6ae5bd6b3783aaf`.
The reviewed Lean source-closure SHA-256 is
`4608b17afe6e8d0be3f7f6e0fae526025c0050f64dca9670e71ae89f9f27aa7c`.

Publication map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-12-130` contains 108 milestones: 106
earned and two deliberately unearned. It pins eleven theorem types for
`concrete-locked-nand-encoded-semantic-boundary`; the complete pin inventory
contains 2,557 theorem types. The map is 829,327 bytes with SHA-256
`f076b8f813c2877d7a03b7090151d4c9db9f4793a5c4f40fbdc5125c82808ed8`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-12-130` records the semantic
boundary fields as true while retaining all four project assumptions, all five
blockers, unset activation fingerprints, an absent `PNP.Main.p_eq_np`, and a
false concrete publication gate. The status is 2,084,476 bytes with SHA-256
`1a4609a63dd44da92cfc4558d1cef0db60430b26942cc6b3e2d199eb35d66ed9`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-12-130` has a
218,897-byte TeX source with SHA-256
`2f3aeaa0801283edbcb713f74567d133ea4598e3b5eb04541ac083d31fbf7546`
and an 85-page, 455,853-byte PDF with SHA-256
`fedbffc7877c0cf4da70f6eea77395f7ee413e48917a80ee3ea5f24d9c325fec`.

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

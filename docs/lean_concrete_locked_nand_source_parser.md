# Concrete strict-v0 locked-NAND source parser

## Plain-language boundary

The previous locked-NAND milestone fixed the exact zeros and ones used to
describe a source circuit. This milestone turns that format into a small,
literal machine rather than asking Lean's built-in decoder to do the work.

In everyday terms, the machine reads a circuit description from left to
right. It checks that the document has the right version, that all counts end
where they should, that each gate has two usable inputs, that references point
to things already declared, and that the document ends at the exact required
place. Its transition table is finite and can be inspected one rule at a time.

The intended successful result is deliberately boring: return the exact
source bytes that were supplied. The intended failure result is equally
strict: erase the source workspace and return no output bytes. This prevents a
malformed document from being silently repaired, reinterpreted, or partly
accepted.

Lean now connects **every** input shape to one of those two results under one
unconditional runtime theorem. Valid descriptions accept and preserve their
bytes; malformed grammar and invalid references reject and expose the empty
output. The compiled machine reaches that verdict without timing out at the
stated cubic bound. This is the earned parser/validator milestone. Its
successors now emit the locked-NAND target and package the composed function
as the concrete polynomial reduction.

## Exact technical architecture

The source-parser implementation is split into small reviewable layers:

- `LockedNANDSourceParserSpec` fixes the accepted language and the
  byte-preserving-or-empty output function.
- `LockedNANDSourceParserSemantics` proves the constructive relationship
  between raw circuit well-formedness and intrinsic Lean elaboration.
- `LockedNANDSourceParserMachine` contains the literal work alphabet, states,
  rules, work machine, and six-for-one compiled machine.
- `LockedNANDSourceParserFailureShapes` gives exact normal forms for every
  token-framing and strict grammar failure.
- `LockedNANDSourceParserValidTrace` proves canonical layouts and exact
  transition components for successful paths.
- `LockedNANDSourceParserTotalTrace` proves exact generic cleanup runs and the
  restored accepting boundary.
- `LockedNANDSourceParserCorrectness` dispatches every raw bitstring through
  valid, malformed-grammar, or ill-formed-reference exact traces.
- `LockedNANDSourceParserCompiled` supplies the explicit external polynomial,
  raw-start blank-tape transport, exact compiled verdict/output theorems, and
  the polynomial-time machine/function/refinement interface.

### Strict version-zero grammar

The parser recognizes one circuit, with no optional or trailing material:

```text
version0
unary input count
unary gate count
exactly that many (left source, right source, gateEnd) records
programEnd
one output source
outputsEnd
instanceEnd
end of input
```

Each token occupies exactly four source bits and two packed work cells.
Natural numbers are unary runs of `unit` followed by `natEnd`. A source is an
input reference, Boolean constant, or earlier-gate reference. Input indices
must be strictly below the declared input count; gate indices must be strictly
below the number of gates already completed.

`TokenDecodeFailure` classifies the first reserved `11xx` token after a
canonical full-token prefix, or an exact one-, two-, or three-bit trailing
fragment. `NatTokenFailure`, `SourceTokenFailure`,
`NGatesTokenFailure`, and `CircuitTokenFailure` then classify every grammar
boundary, including missing or wrong version/count/source/gate terminators,
wrong program/output/instance terminators, and trailing tokens. Their
`decode... = none ↔ ...Failure` theorems are constructive and retain exact
input equalities for forward machine traces.

### Literal finite transition table

The work alphabet has nine symbols:

```text
blank, left guard, cursor mark, count mark,
00, 01, gate mark, 10, 11
```

There are exactly 228 control-state programs. Each program has one transition
for each of the nine work symbols, giving:

```text
228 × 9 = 2,052 literal work rules.
```

`rules_pairwise_query_distinct` proves that no two rules compete for the same
state-and-symbol query. The start, accept, and reject states are pairwise
separated.

The executable `statePrograms`, `rules`, `machine`, and `compiledMachine`
definitions do not call `decodeTokens`, `decodeCircuit`,
`decodeElaboratedCircuit`, or a well-formedness oracle. Decoder theorems are
used only outside the table to state and prove what the literal transitions
mean. There is no host-side schedule lookup or caller-supplied execution
certificate.

### Exact success and failure endpoints

On the successful route, count and gate marks occupy cells whose original
values are statically known. The exact trace components restore those cells
before acceptance. `acceptedTape_outputBits` proves that the canonical
accepting tape exposes precisely `encodeCircuit raw`, not a normalized,
shortened, or independently reconstructed substitute.

On a malformed route, control enters a leftward guard seek and then an
output-erasing rightward cleanup. The cleanup theorems cover both the usual
blank-extended tape and a materialized blank followed by arbitrary finite
suffix data. `cleanupRejectConfiguration_output_empty` proves that the
canonical rejecting endpoint exposes `[]`, and
`cleanupRejectConfiguration_isHalted` proves that endpoint is genuinely
rejecting.

`wellFormed_exact`, `malformed_exact`, and `illFormed_exact` assemble those
components for the three complete semantic cases. `allInput_exact` then
dispatches every bitstring without a caller-supplied execution certificate.
It produces a halted exact run within `validWorkBound`, proves that the final
state is accepting exactly when `ValidEncodedCircuit` holds, and proves that
the final output equals `validatedSourceBytes`. Thus valid inputs are
preserved byte-for-byte and every invalid input exposes `[]`.

### Conservative compiled bound

For source length `n`, the current work-transition envelope is

```text
validWorkBound(n) = 4096 × (n + 1)³.
```

The fixed work-machine compiler uses six raw transitions per work transition:

```text
validRawBound(n) = 6 × validWorkBound(n).
```

`validRawTimePolynomial` is a literal `NatPolynomial` with that evaluation,
and `compiledStart_blankEquivalent` relates the ordinary raw-input start to
the packed work-machine start over the same infinite blank-extended tape.
Every all-input exact trace is proved to fit the work bound. Consequently,
the compiled machine accepts exactly `ValidEncodedCircuit`, returns exactly
`validatedSourceBytes`, and cannot time out within
`6 × 4096 × (n + 1)³` raw transitions.

`polynomialTimeMachine` packages the language decision. The nonexpanding
`validatedSourceBytesPolynomialTimeFunction` packages the total validator
with identity output-size polynomial, and its output theorem recovers the
exact byte-preserving-or-empty specification.
`validatedSourceBytesRawRefinement` proves the function witness's leaf
program is already implemented by that exact raw machine.

## Kernel audit and verification

The axiom audit follows every current non-private declaration in source order,
including executable definitions, finite state types, the rule table,
failure classifiers, low-level exact traces, cleanup endpoints, and compiled
bound interfaces. Its current kernel closures are limited to the empty
closure, `propext`, and `Quot.sound`. It contains no project axiom,
`Classical.choice`, `sorry`, `admit`, `native_decide`, SAT shortcut, host
decoder, or caller certificate.

The regression covers empty circuit tokens, one-, two-, and three-bit framing
tails, a reserved `11xx` token, unterminated unary numbers, malformed source
and gate records, every program/output/instance delimiter failure, trailing
tokens, invalid input and gate references, canonical valid circuits, exact
all-input verdict/output behavior, compiled acceptance and non-timeout,
polynomial evaluation, and raw refinement. The hostile audit rejects state or
rule-count changes, decoder insertion into the executable machine,
cleanup-interface removal, polynomial alteration, hidden assumptions, host
lookup, caller certificates, and project overclaims.

Run the focused checks with:

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteLockedNANDSourceParserAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteLockedNANDSourceParser.lean
node --test \
  audits/lean-concrete-locked-nand-source-parser0.test.mjs
```

Repository policy requires running these Lean jobs, the complete build, and
clean-clone reproduction on the configured resource-limited `pnpbuilder`
host.

## Mechanically generated publication evidence

Inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-08-03-97` records 23,671 declarations,
12,853 theorems, 6,809 assumption-free theorems, 14,273 excluded private
declarations, 212 source-closure modules, and 2,115 reviewed milestone
candidates. Its 13,495,531 canonical bytes have SHA-256
`206084d180ff61b20d89dff70ef0d161e0c9e2a15b070601ea0000a29ed4184c`.
The pinned Lean source closure is
`637927ee2f3fe48f8f8c7495ea0c2ecc6da66d85190c80b961b9079aa5e6128c`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-03-97` contains 77 milestones, of
which 74 are earned and three global milestones remain unearned. The map pins
2,115 theorem types. Its 689,227 bytes have SHA-256
`1a7682523289d123a5673e42442ced6f11d8d2d001496447590719101de15338`.
The source-parser milestone contributes 20 theorem types.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-03-97`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-03-RESIDUAL-TERMINAL-FULL-CARRIER-BRIDGE-96`, records
the four disclosed project assumptions, six blockers, absent
`PNP.Main.p_eq_np`, unset activation fingerprints, and a false concrete
publication gate. The status is 1,693,893 bytes with SHA-256
`9d57f950c033ff5a8e80118695112681bbd491a3cf1f3e9780408cf35487b6f6`.

The complete parser audit covers 380 audited declarations: 247 have empty
axiom closure, 58 use only `propext`, and 75 use only `propext` and
`Quot.sound`. No declaration in the transcript reaches `Classical.choice` or
a project axiom.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-03-97` renders as a
71-page A4 PDF. The generated TeX is 181,201 bytes with SHA-256
`e31bb0758834ecf077dc5b861066b1767e9619b1ff545746b4e08259028af981`;
the deterministic PDF is 424,881 bytes with SHA-256
`ab83808e3c98d306f3ac15b0cfa5dc7ffda1c91ed16e8843e2dbd8b41b00b17d`.

## Explicit non-claims

This parser does not emit the locked-NAND target instance. It is not the
candidate emitter or, by itself, the composed source-to-target machine. Its
leaf-machine `RawRefinement` validates source bytes only. The downstream
target-emitter milestone now supplies exact target bytes, its own output-size
bound, and recursive parser/emitter refinement. Their successor packages the
language theorem and exact function as `PolynomialReduction`. These concrete
modules do not discharge the abstract `PNP.LockedNANDThreshold` language, put
CNF-SAT in P, establish CNF-SAT NP-hardness, or prove P = NP.

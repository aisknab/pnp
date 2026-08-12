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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-12-133` records 27,794 declarations,
14,454 theorems, 7,347 assumption-free theorems, 15,008 excluded private
declarations, 250 source-closure modules, and 2,589 reviewed milestone
candidates. Its 18,243,895 canonical bytes have SHA-256
`696c76220a092e5a84e7caa804fd1c57889f193968d1285b520c408f8237f5c1`.
The pinned Lean source closure is
`9b8afc2bac8c5f5b5fbe3c086f22602358c3f9b641aeb91e7de708f9f1001154`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-12-133` contains 111 milestones, of
which 109 are earned and two global milestones remain unearned. The map pins
2,589 theorem types. Its 840,935 bytes have SHA-256
`a9f7ec898fb04e4842ea86281d2a6b257fc0c65dd422eb04a974bde169bf29d6`.
The source-parser milestone contributes 20 theorem types.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-12-133`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`, records
the four disclosed project assumptions, five blockers, absent
`PNP.Main.p_eq_np`, unset activation fingerprints, and a false concrete
publication gate. The status is 2,111,583 bytes with SHA-256
`6e7416a60485390b4414251c3b8f00214ed759f93d8091aef73cdb357da2dbfe`.

The complete parser audit covers 380 audited declarations: 247 have empty
axiom closure, 58 use only `propext`, and 75 use only `propext` and
`Quot.sound`. No declaration in the transcript reaches `Classical.choice` or
a project axiom.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-12-133` renders as an
88-page A4 PDF. The generated TeX is 223,061 bytes with SHA-256
`2e42452a0d270c8e36cf7f381dbd38a64a535d07b8bc653e4e13ff526c574e7d`;
the deterministic PDF is 460,049 bytes with SHA-256
`5bca11cba837c8bdf90e27186974bf5398d4be78fae3360987afbf19746d271b`.

## Explicit non-claims

This parser does not emit the locked-NAND target instance. It is not the
candidate emitter or, by itself, the composed source-to-target machine. Its
leaf-machine `RawRefinement` validates source bytes only. The downstream
target-emitter milestone now supplies exact target bytes, its own output-size
bound, and recursive parser/emitter refinement. Their successor packages the
language theorem and exact function as `PolynomialReduction`. These concrete
modules do not discharge the abstract `PNP.LockedNANDThreshold` language, put
CNF-SAT in P, establish CNF-SAT NP-hardness, or prove P = NP.

# Concrete strict-v0 locked-NAND target emitter

## Plain-language result

The reconstruction now contains a complete, fixed program that turns a
strictly encoded NAND circuit into the exact locked-NAND instance required by
the legacy construction. It does not ask the caller for a schedule, a proof
certificate, or a precomputed answer.

There are two deliberately separate boundaries:

- The standalone emitter checks only the byte grammar. If the bytes describe
  a circuit shape, it emits the corresponding raw target even when a wire
  points outside the valid topological range.
- The published strict function runs the existing strict parser first.
  Malformed or intrinsically invalid circuits therefore produce an empty
  output, while valid circuits produce exactly `buildLockedNANDInstance`.

This separation makes the executable table honest and the public interface
fail-closed. The work closes the missing target-emission component; it does
not by itself prove P = NP.

## Technical boundary

`PNP.Concrete.LockedNAND.RawBuilder` reconstructs the legacy Section 17 target
with lists and natural-number coordinates. Its six closed NAND templates have
lengths 10, 3, 2, 18, 2, and 4. On successfully decoded and elaborated input,
`rawLockedInstance_of_elaborate` and `targetBytes_of_elaborated` prove
byte-for-byte equality with the established typed construction.

`PNP.Concrete.LockedNAND.TargetEmitterController` materializes one finite
grammar-only graph. Its control and block state namespaces are separated by
parity, all graph endpoints resolve, the rule queries are pairwise distinct,
accept and reject are separate halts, and:

```text
TargetEmitterGrammarScanner.ruleCount = 540
TargetEmitterLedger.ruleCount         = 20,556
TargetEmitterController.ruleCount     = 1,387,921
```

No executable rule-table constructor calls `decodeCircuit`,
`decodeElaboratedCircuit`, `RawBuilder.targetBytes`, a semantic schedule,
host-side lookup, or a caller certificate. Decoding occurs only in the
correctness proof that classifies the literal trace.

For every raw bitstring, `allInput_bounded_exact` constructs an exact halted
run internally:

- grammar failure rejects and leaves the observable output empty;
- grammar success accepts and emits exactly `RawBuilder.targetBytes`;
- a decoded but intrinsically invalid reference is accepted by this
  grammar-only boundary, as intended.

The closed work bound is
`512 * (n + 1) * phaseUnit n`. A literal degree-five
`NatPolynomial` evaluates to that expression, and the compiled raw bound is
six times the work bound. The output has a separate explicit quadratic
polynomial bound on every input.

`TargetEmitterControllerCompiled` supplies:

- compiled blank-equivalence;
- exact `machineOutput = RawBuilder.targetBytes`;
- acceptance exactly when the grammar decoder succeeds;
- non-timeout at the advertised polynomial;
- a `PolynomialTimeMachine`;
- a standalone `PolynomialTimeFunction` and exact leaf `RawRefinement`;
- composition with
  `SourceParser.validatedSourceBytesPolynomialTimeFunction`;
- exact strict output `buildLockedNANDInstance`; and
- recursive `RawRefinement` for that parser/emitter composition.

The successor polynomial-reduction milestone now registers the strict
composition as the repository's source-to-target `PolynomialReduction` and
binds the already-proved encoded language equivalence to this exact compiled
function. The abstract `PNP.LockedNANDThreshold` assumption, CNFSAT-in-P
transport, NP-hardness transport, and `PNP.Main.p_eq_np` remain outside both
milestones.

## Audit and regression

The generated transcript
`lean-audit/PNPConcreteLockedNANDTargetEmitterAxiomAudit.lean` follows all
3,295 audited declarations from the 68-module emitter and generic work-graph
surface in exact source order:

- 2,224 have empty axiom closure;
- 429 use only `propext`;
- 642 use only `propext` and `Quot.sound`.

None reaches `Classical.choice`, a project axiom, `sorryAx`, `sorry`, `admit`,
native or SAT decision shortcuts, host lookup, or a caller certificate. The
publication milestone pins 22 theorem types.

The constructive regression covers empty input, one-bit zero and one,
odd-length all-zero, even/odd all-one words, constant-false and constant-true
circuits, a one-gate circuit, and a grammar-decoded invalid reference. It pins
the literal rule count, polynomial evaluation, exact compiled output,
non-timeout, strict fail-closed behavior, and both `RawRefinement` witnesses.

The hostile audit rejects state collisions, entry-bridge removal, table
shadowing, decoder or semantic leakage into executable construction, altered
scanner/ledger/controller counts, target substitution, changed compiled
output, changed polynomial, unlisted declarations, project assumptions,
`Classical.choice`, host lookup, caller certificates, and P = NP overclaims.

Run the focused checks with:

```bash
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteLockedNANDTargetEmitterAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteLockedNANDTargetEmitter.lean
node --test audits/lean-concrete-locked-nand-target-emitter0.test.mjs
```

## Mechanically generated publication evidence

- Lean inventory:
  `PNP-LEAN-THEOREM-INVENTORY-2026-08-08-113`
- publication map:
  `PNP-FORMAL-PUBLICATION-MAP-2026-08-08-113`
- reconstruction status:
  `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-113`
- public surface:
  `PUBLIC-SURFACE-BASELINE-2026-08-08-RESIDUAL-TERMINAL-FOUR-CORNER-SIDE-TIGHT-COMPLETION-112`
- canonical report:
  `PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-08-113`

The compiled inventory records 24,999 declarations, 13,376 theorems, 7,022
assumption-free theorems, 14,691 excluded private declarations, 229
source-closure modules, and 2,364 reviewed milestone candidates. Its
15,930,331 canonical bytes have SHA-256
`82fcdfd7443489f917d3987d31f604af6c163e9cb2a6fca2cd8aff98c38ff97f`;
the exact Lean source closure has SHA-256
`1ed937ea678bb853929da8c6958fe30fe09b837ad53fda5b53d5ce4da2584830`.

The 766,476-byte publication map contains 93 milestones: 90 earned and three
deliberately unearned. It pins 2,364 theorem types and has SHA-256
`6d05c3a4d70ea78994a0302a60c8ba8381e37ff4e9c30a774ab474a13bb9baac`.
The generated 1,916,515-byte status has SHA-256
`b9aff3d3eee8fed7d232c41cf0e81dc2355a3cd27a720b64aafde01746b20656`.
The canonical 199,054-byte TeX source has SHA-256
`73ef5719cc112e91e262b42846db82f4e92cd1dc1184484ad67f2b0b5006a01f`;
its deterministic 78-page, 438,997-byte A4 PDF has SHA-256
`e196ce1a2c373dbab4bf5e0e70418f0029beed4e1cfb959c78981c4880c6db02`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.

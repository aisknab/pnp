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
  `PNP-LEAN-THEOREM-INVENTORY-2026-08-06-106`
- publication map:
  `PNP-FORMAL-PUBLICATION-MAP-2026-08-06-106`
- reconstruction status:
  `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-06-106`
- public surface:
  `PUBLIC-SURFACE-BASELINE-2026-08-06-RESIDUAL-TERMINAL-GOVERNED-SUPPORT-COMPLETION-105`
- canonical report:
  `PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-06-106`

The compiled inventory records 24,405 declarations, 13,134 theorems, 6,945
assumption-free theorems, 14,576 excluded private declarations, 221
source-closure modules, and 2,240 reviewed milestone candidates. Its
14,564,176 canonical bytes have SHA-256
`38c53b1e3e80059332ff62f135ffebcf04d6b5e39e158f0f48965295894c6e8d`;
the exact Lean source closure has SHA-256
`b4be2de72b2909cd9e47f0748e061f03041fbecbac1360e5797e89fef18404f6`.

The 726,779-byte publication map contains 86 milestones: 83 earned and three
deliberately unearned. It pins 2,240 theorem types and has SHA-256
`3b27c4f934c3897bb71584846005e93a4816b63f4f8750a6884d18f1aedfe7ce`.
The generated 1,798,304-byte status has SHA-256
`5e6356f2b13da0161b4b0fb0ea299b504bfef54f7670f3a4371d1b19df26d10f`.
The canonical 191,295-byte TeX source has SHA-256
`1dc4a81c1f7a9805405019d1298f5324aaf39f599a4b58433bf72ceeb97a5a9c`;
its deterministic 75-page, 432,609-byte A4 PDF has SHA-256
`04683262a3cd12a893f7d1d67c750502f52f40a9c8bf7755912b3ebbff76d5fb`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.

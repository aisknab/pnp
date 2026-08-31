# Lean bridge formalization

This directory contains the Lean formalization track for the PNP proof-certificate stack.

The current Lean development contains a conditional theorem bridge corresponding to the report:

```text
exists loop : PCCMinLoopCertificate,
  CheckPCCPackexp (GeneratePCCPack loop) = accept => P = NP
```

The compiled bridge has no project-specific axiom declarations, but it still
requires the explicit loop-certificate existence premise and concrete SAT
hardness. It therefore does **not** constitute a Lean proof of `P = NP`. It is
also not a complete Lean reproof of the custom JavaScript checker, the full
residual-slack package, a deterministic SAT algorithm, or the concrete NP-hardness transport. The purpose of the Lean
track is to replace each trust-base item with a checked theorem in visible stages.

## Build

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPBridgeAxiomAudit.lean
node scripts/export-lean-theorem-inventory.mjs --check
```

The GitHub workflow `.github/workflows/lean-bridge.yml` verifies a checksum-pinned Elan 4.2.3
archive, installs the exact `leanprover/lean4:v4.31.0` toolchain, builds the explicit `PNP` root, and
prints the axiom dependencies of both the root-status declarations and conditional bridge. It also
checks the canonical inventory generated from the compiled environment and the fail-closed formal
publication/report outputs.

## Files

```text
lean-toolchain
lakefile.lean
lean/PNP.lean
lean/PNP/Main.lean
lean/PNP/NANDSemantics.lean
lean/PNP/NANDEnumerator.lean
lean/PNP/NANDTruthTable.lean
lean/PNP/NANDMinimum.lean
lean/PNP/NANDComposition.lean
lean/PNP/NANDSlack.lean
lean/PNP/ResidualRoutes.lean
lean/PNP/ResidualGainChain.lean
lean/PNP/ResidualGainStopping.lean
lean/PNP/ResidualTerminalFullBridge.lean
lean/PNP/ResidualTerminalModeFirewall.lean
lean/PNP/ResidualTerminalProjectionMinimum.lean
lean/PNP/ResidualTerminalProjectionTransfer.lean
lean/PNP/ResidualTerminalSaturation.lean
lean/PNP/ResidualTerminalExecutableSaturation.lean
lean/PNP/ResidualTerminalPhysicalSupportCompletion.lean
lean/PNP/ResidualTerminalSupportExtraction.lean
lean/PNP/ResidualTerminalProperSupport.lean
lean/PNP/ResidualTerminalSupportSquareClosure.lean
lean/PNP/ResidualTerminalGovernedSupportCompletion.lean
lean/PNP/ResidualTerminalFrontierPushout.lean
lean/PNP/ResidualTerminalProjectionSquare.lean
lean/PNP/ResidualTerminalSideTightMinimum.lean
lean/PNP/ResidualTerminalFourCornerCarrier.lean
lean/PNP/ResidualTerminalFourCornerOptimumCompatibility.lean
lean/PNP/ResidualTerminalFourCornerOptimumCoherence.lean
lean/PNP/ResidualTerminalFourCornerSideTightCompletion.lean
lean/PNP/ResidualTerminalFourCornerTightBasisMaximum.lean
lean/PNP/ResidualTerminalBN2SquareLegitimacy.lean
lean/PNP/ResidualTerminalBCELAnchorNucleus.lean
lean/PNP/ResidualTerminalSaturationPositivityFirewall.lean
lean/PNP/ResidualTerminalCandidateSaturation.lean
lean/PNP/ResidualTerminalSaturationCostBalance.lean
lean/PNP/LockedNANDResidualGainBound.lean
lean/PNP/Concrete/BitString.lean
lean/PNP/Concrete/Machine.lean
lean/PNP/Concrete/TapeHandoff.lean
lean/PNP/Concrete/PipelineTapeGeometry.lean
lean/PNP/Concrete/PipelineInputFramer.lean
lean/PNP/Concrete/PipelineOutputHandoff.lean
lean/PNP/Concrete/PipelineMachineSimulation.lean
lean/PNP/Concrete/PipelineStateNamespace.lean
lean/PNP/Concrete/PipelineSequentialStateNamespace.lean
lean/PNP/Concrete/PipelineSequentialCompiler.lean
lean/PNP/Concrete/PipelineStageBridges.lean
lean/PNP/Concrete/TerminalOutputPacker.lean
lean/PNP/Concrete/PipelineTerminalBridge.lean
lean/PNP/Concrete/PipelinePairedCompiler.lean
lean/PNP/Concrete/PipelineCompiler.lean
lean/PNP/Concrete/Complexity.lean
lean/PNP/Concrete/PipelineRefinement.lean
lean/PNP/Concrete/LockedNANDEncoding.lean
lean/PNP/Concrete/LockedNANDReduction.lean
lean/PNP/Concrete/LockedNANDSourceParserSpec.lean
lean/PNP/Concrete/LockedNANDSourceParserSemantics.lean
lean/PNP/Concrete/LockedNANDSourceParserMachine.lean
lean/PNP/Concrete/LockedNANDSourceParserFailureShapes.lean
lean/PNP/Concrete/LockedNANDSourceParserValidTrace.lean
lean/PNP/Concrete/LockedNANDSourceParserTotalTrace.lean
lean/PNP/Concrete/LockedNANDSourceParserCorrectness.lean
lean/PNP/Concrete/LockedNANDSourceParserCompiled.lean
lean/PNP/Concrete/LockedNANDSourceParser.lean
lean/PNP/Concrete/LockedNANDRawBuilder.lean
lean/PNP/Concrete/LockedNANDTargetEmitterSpec.lean
lean/PNP/Concrete/LockedNANDTargetEmitterControllerCompiled.lean
lean/PNP/Concrete/LockedNANDTargetEmitter.lean
lean/PNP/Concrete/Target.lean
lean/PNP/Concrete/WorkInput.lean
lean/PNP/Concrete/WorkMachine.lean
lean/PNP/Concrete/CNF.lean
lean/PNP/Concrete/CNFVerifier.lean
lean/PNP/Concrete/CNFWorkInput.lean
lean/PNP/Concrete/CNFWorkMachine.lean
lean/PNP/Concrete/CNFWorkTransitions.lean
lean/PNP/Concrete/CNFWorkFrameCorrectness.lean
lean/PNP/Concrete/CNFWorkCorrectness.lean
lean/PNP/Concrete/CNFWorkUniversalCorrectness.lean
lean/PNP/Complexity.lean
lean/PNP/SAT.lean
lean/PNP/LockedNANDMacros.lean
lean/PNP/LockedNANDPrefix.lean
lean/PNP/LockedNANDDirect.lean
lean/PNP/DirectWireBaseline.lean
lean/PNP/LockedNANDBaseline.lean
lean/PNP/LockedNANDLocalBaseline.lean
lean/PNP/LockedNANDThresholdBoundary.lean
lean/PNP/LockedNANDCarrierTrace.lean
lean/PNP/LockedNANDGlobalCandidates.lean
lean/PNP/LockedNANDGlobalUnsatisfiableFinalZero.lean
lean/PNP/LockedNANDGlobalSemanticThreshold.lean
lean/PNP/LockedNAND.lean
lean/PNP/ResidualBand.lean
lean/PNP/ZeroSlack.lean
lean/PNP/PCCMin.lean
lean/PNP/Bridge.lean
lean-audit/PNPBridgeAxiomAudit.lean
lean-audit/PNPTheoremInventory.lean
lean-audit/PNPConcreteBitStringAxiomAudit.lean
lean-audit/PNPConcreteMachineAxiomAudit.lean
lean-audit/PNPConcreteTapeHandoffAxiomAudit.lean
lean-audit/PNPConcretePipelineTapeGeometryAxiomAudit.lean
lean-audit/PNPConcretePipelineInputFramerAxiomAudit.lean
lean-audit/PNPConcretePipelineOutputHandoffAxiomAudit.lean
lean-audit/PNPConcretePipelineStateNamespaceAxiomAudit.lean
lean-audit/PNPConcretePipelineSequentialStateNamespaceAxiomAudit.lean
lean-audit/PNPConcretePipelineSequentialCompilerAxiomAudit.lean
lean-audit/PNPConcretePipelineStageBridgesAxiomAudit.lean
lean-audit/PNPConcreteTerminalOutputPackerAxiomAudit.lean
lean-audit/PNPConcretePipelineTerminalBridgeAxiomAudit.lean
lean-audit/PNPConcretePipelinePairedCompilerAxiomAudit.lean
lean-audit/PNPConcretePipelineCompilerAxiomAudit.lean
lean-audit/PNPConcretePipelineMachineSimulationAxiomAudit.lean
lean-audit/PNPConcreteComplexityAxiomAudit.lean
lean-audit/PNPConcretePipelineRefinementAxiomAudit.lean
lean-audit/PNPConcreteLockedNANDSourceParserAxiomAudit.lean
lean-audit/PNPConcreteLockedNANDTargetEmitterAxiomAudit.lean
lean-audit/PNPConcreteTargetAxiomAudit.lean
lean-audit/PNPConcreteCNFAxiomAudit.lean
lean-audit/PNPConcreteCNFVerifierAxiomAudit.lean
lean-audit/PNPConcreteCNFWorkInputAxiomAudit.lean
lean-audit/PNPConcreteCNFWorkAxiomAudit.lean
lean-audit/PNPNANDSemanticsAxiomAudit.lean
lean-audit/PNPNANDEnumeratorAxiomAudit.lean
lean-audit/PNPNANDTruthTableAxiomAudit.lean
lean-audit/PNPNANDMinimumAxiomAudit.lean
lean-audit/PNPNANDCompositionAxiomAudit.lean
lean-audit/PNPNANDSlackAxiomAudit.lean
lean-audit/PNPResidualRoutesAxiomAudit.lean
lean-audit/PNPResidualGainChainAxiomAudit.lean
lean-audit/PNPResidualGainStoppingAxiomAudit.lean
lean-audit/PNPResidualTerminalFullBridgeAxiomAudit.lean
lean-audit/PNPResidualTerminalModeFirewallAxiomAudit.lean
lean-audit/PNPResidualTerminalProjectionMinimumAxiomAudit.lean
lean-audit/PNPResidualTerminalProjectionTransferAxiomAudit.lean
lean-audit/PNPResidualTerminalSaturationAxiomAudit.lean
lean-audit/PNPResidualTerminalPhysicalSupportCompletionAxiomAudit.lean
lean-audit/PNPResidualTerminalSupportExtractionAxiomAudit.lean
lean-audit/PNPResidualTerminalProperSupportAxiomAudit.lean
lean-audit/PNPResidualTerminalSupportSquareClosureAxiomAudit.lean
lean-audit/PNPResidualTerminalGovernedSupportCompletionAxiomAudit.lean
lean-audit/PNPResidualTerminalFrontierPushoutAxiomAudit.lean
lean-audit/PNPResidualTerminalProjectionSquareAxiomAudit.lean
lean-audit/PNPResidualTerminalSideTightMinimumAxiomAudit.lean
lean-audit/PNPResidualTerminalFourCornerCarrierAxiomAudit.lean
lean-audit/PNPResidualTerminalFourCornerOptimumCompatibilityAxiomAudit.lean
lean-audit/PNPResidualTerminalFourCornerOptimumCoherenceAxiomAudit.lean
lean-audit/PNPResidualTerminalFourCornerSideTightCompletionAxiomAudit.lean
lean-audit/PNPLockedNANDResidualGainBoundAxiomAudit.lean
lean-audit/PNPLockedNANDDirectAxiomAudit.lean
lean-audit/PNPDirectWireBaselineAxiomAudit.lean
lean-audit/PNPLockedNANDBaselineAxiomAudit.lean
lean-audit/PNPLockedNANDLocalBaselineAxiomAudit.lean
lean-audit/PNPLockedNANDThresholdBoundaryAxiomAudit.lean
lean-audit/PNPLockedNANDCarrierTraceAxiomAudit.lean
lean-audit/PNPLockedNANDGlobalCandidatesAxiomAudit.lean
lean-audit/PNPLockedNANDGlobalBaselineDistinctAxiomAudit.lean
lean-audit/PNPLockedNANDGlobalUnsatisfiableFinalZeroAxiomAudit.lean
lean-audit/PNPLockedNANDGlobalSemanticThresholdAxiomAudit.lean
lean-regression/PNPConcreteLockedNANDSourceParser.lean
lean-regression/PNPConcreteLockedNANDTargetEmitter.lean
docs/lean_nand_semantics.md
docs/lean_concrete_machine.md
docs/lean_tape_handoff.md
docs/lean_pipeline_tape_geometry.md
docs/lean_pipeline_input_framer.md
docs/lean_pipeline_output_handoff.md
docs/lean_pipeline_state_namespace.md
docs/lean_pipeline_machine_simulation.md
docs/lean_pipeline_paired_compiler.md
docs/lean_pipeline_compiler.md
docs/lean_concrete_complexity.md
docs/lean_concrete_locked_nand_source_parser.md
docs/lean_nand_enumerator.md
docs/lean_locked_nand_macros.md
docs/lean_locked_nand_prefix.md
docs/lean_locked_nand_baseline.md
docs/lean_locked_nand_threshold_boundary.md
docs/lean_concrete_legacy_locked_nand_compatibility.md
docs/lean_residual_routes.md
docs/lean_theorem_inventory.md
```

## Concrete machine foundation, charged complexity interface, and report-facing bridge

`lean/PNP/Concrete/BitString.lean` defines canonical executable bitstring codecs and natural
polynomial syntax. `lean/PNP/Concrete/Machine.lean` defines finite rule-list machine programs,
focused-tape configurations, fuel-bounded execution, three-way verdicts, and proof-bearing
`PolynomialTimeMachine` witnesses. All 79 explicit declarations have empty axiom closures. See
[`lean_concrete_machine.md`](./lean_concrete_machine.md) for the exact boundary.

`lean/PNP/Concrete/Complexity.lean` adds a finite charged interpreter interface. Function and
decision syntax trees have concrete `Machine` leaves and explicit `NatPolynomial` budgets.
Proof-bearing wrappers bound runtime, intermediate-output handoff/copy cost, output size, and
certificate size. Verifiers use either canonical `BitString.pair input certificate` input or the
input-only mode needed for a deterministic decider that ignores the empty certificate. The module
constructs:

```text
PNP.Concrete.p_subset_np
PNP.Concrete.reduction_refl
PNP.Concrete.reduction_comp
PNP.Concrete.reduction_transports_p
PNP.Concrete.np_complete_in_p_implies_p_eq_np
```

All 48 explicit complexity declarations have empty axiom closures. The fourteen declarations in
`lean/PNP/Concrete/TapeHandoff.lean` are also axiom-free: they define first-blank output semantics
and the pure canonical handoff target, prove representation-stable decoding, and make no executable
handoff claim. The twenty declarations in `lean/PNP/Concrete/PipelineTapeGeometry.lean` are also
axiom-free: they define distinct two-track data and boundary tags, an arbitrary-exterior-garbage
frame, and pure write/move/boundary-expansion geometry. They define no rules, machine, simulation,
or runtime bound. `lean/PNP/Concrete/PipelineInputFramer.lean` supplies a separate literal finite
machine from every raw bitstring to an accepting represented frame. It proves exact empty,
complete-cell, and partial-final-cell work costs plus the uniform compiled bound
`6 * m * m + 39 * m + 75` from ordinary raw input; all 70 public declarations have empty axiom
closure. The predecessor bridge and paired-compiler theorems quantify canonical pairs.
`PipelineCompiler.lean` now consumes the same framer endpoint for
every raw bitstring and broadens the complete literal pipeline's input domain.
`lean/PNP/Concrete/PipelineOutputHandoff.lean` supplies another literal finite machine from an
already represented logical tape to an accepting representation of its blank-delimited handoff
target. Its exact costs are `2 * n + 4` work steps and `12 * n + 24` compiled steps for logical
output length `n`. Its compiled trace starts from an encoded internal configuration, not ordinary
`startConfig`, and its represented two-track encoding is not a terminal raw `machineOutput` layout.
`lean/PNP/Concrete/PipelineStateNamespace.lean` injectively renames the framer, simulator, and
handoff into pairwise-disjoint state images, proves first-match lookup isolation in their literal
concatenated rule table, and transports all three existing exact stage-local traces. The subsequent
56-declaration `PipelineStageBridges.lean` adds literal symbol-preserving launch rules, two disjoint
verdict-indexed handoff copies, first-match isolation under bridge priority, cumulative exact work
traces, and six-for-one compiled raw traces from canonical paired input for every supplied exact
target run. It preserves accept/reject classification and leaves a supplied stuck nonhalting
endpoint as timeout at the exact prefix budget. `lean/PNP/Concrete/PipelineMachineSimulation.lean` supplies
the separate finite rule lift: it preserves ordered first-match selection and lifts every supplied exact `n`-step chain
of successful raw transitions from an already represented configuration to exactly `3 * n`
successful work steps. An ordinary `F`-fuel raw run also yields an exact prefix of length `k ≤ F`
to its endpoint. Conditional on that endpoint being designated halting, `workRun` at fuel
`3 * F` and compiled `run` at fuel `18 * F` reach its representation and encoding. This proves no
termination result: those full fuels are at-most budgets rather than successful-step counts or
input-size bounds, and a stuck nonhalting stop is not a verdict. The layer does not create the
frame inside its own theorem or prove target termination. The bridge module supplies exact launch
and verdict theorems. `TerminalOutputPacker.lean` performs terminal de-tagging and proves ordinary
raw output equality with a local quadratic bound. The 59-declaration
`PipelineTerminalBridge.lean` places two disjoint packer copies after the earlier bridge rules and
proves exact accepting/rejecting launches, terminal halts, and output equality from represented
handoff endpoints under the local bound `18*n^2 + 36*n + 12`. It preserves every successful
earlier bridge step in the extended table and, for each caller-supplied exact accepting or rejecting
target execution, composes one exact four-stage trace from paired `startConfig` with exact verdict
and raw-output equality. `PipelinePairedCompiler.lean` derives target termination and an external
polynomial for canonical pairs. Its 29-declaration successor `PipelineCompiler.lean` proves exact
verdict, no-timeout, language acceptance, and ordinary output equality for every raw bitstring at
the explicit output bound `B(m) = m + p(m) + 1` and complete runtime polynomial. Every public
successor declaration has empty axiom closure. This wraps an already-raw proof-bearing target; the
recursive refinement module consumes that wrapper at every syntax-tree node. The two declarations in
`lean/PNP/Concrete/Target.lean` are also axiom-free: `PNP.Main.ConcretePEqualsNP` is an inactive
definition naming mutual inclusion, and `PNP.Main.concretePEqualsNP_iff` pins its expansion. This
does not prove the target. The 16 explicit declarations in
`lean/PNP/Concrete/PipelineRefinement.lean` are axiom-free. They pin exact
raw-machine refinement obligations, prove the raw function/decision leaf cases, compose function
refinements, precompose decision refinements, recursively compile both finite program syntaxes,
preserve exact output/verdict, and expose a complete decider as one raw machine.

The 26 declarations in `PipelineSequentialStateNamespace.lean` are also axiom-free. They rename
two complete component tables into disjoint outer state images, isolate first-match lookup for both
images, transport exact local steps and runs, and provide literal accept/reject launches from the
first component to the second simulator. The 31 public declarations in
`PipelineSequentialCompiler.lean` then prove the complete all-input run in the literal combined
table. Either first verdict continues on the represented first output; the second verdict and
ordinary raw output are exact, stuck first endpoints remain timeout, and the external bound is
`PipelineRaw(p)(m) + 6 + PipelineRaw(q)(m + p(m) + 1)`. Their compiled axiom closures are empty.
The recursive `RawRefinement` constructors consume this compiler at every composite node, so
`Formal.ConcreteComplexityMachineLink` is now discharged. CNF-SAT in P, CNF-SAT NP-completeness,
and the root theorem remain absent. See
[`lean_concrete_complexity.md`](./lean_concrete_complexity.md) and
[`lean_pipeline_compiler.md`](./lean_pipeline_compiler.md), and
[`lean_pipeline_sequential_compiler.md`](./lean_pipeline_sequential_compiler.md).

### Direct concrete CNF verifier

The concrete CNF path is a closed raw-machine instance. The general compiler is now available for
future charged-program compositions. `lean/PNP/Concrete/CNF.lean` defines canonical encodings for
finite CNF formulae and assignments, propositional satisfaction, the executable
`checkEncodedCertificate`, a linear certificate-size bound, and the language
`PNP.Concrete.CNFSAT`. `CNFWorkInput.lean` proves that canonical pairing and the work-tape layout
agree exactly. `CNFWorkMachine.lean` gives a finite work machine, compiles it to the raw machine
`cnfCompiledMachine`, and defines the explicit raw-input polynomial

```text
cnfCompiledStepPolynomial(n) = 6 * (8 + 64 * (n + 2)^3).
```

`CNFWorkCorrectness.lean` and `CNFWorkUniversalCorrectness.lean` prove the framing, width,
formula-grammar, assignment-grammar, clause, literal, restoration, semantic, and cost cases. Their
final universal surface is:

```lean
theorem cnfCompiled_accept_iff_check (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) = .accept ↔
      checkEncodedCertificate input certificate = true

theorem cnfCompiled_reject_iff_check_false (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) = .reject ↔
      checkEncodedCertificate input certificate = false

theorem cnfCompiled_ne_timeout (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) ≠ .timeout

def cnfConcreteVerifier : PolynomialTimeVerifier CNFSAT
theorem cnfSATInNP : InNP CNFSAT
```

The verifier program has `.paired` input mode and its decision is literally
`.machine cnfCompiledMachine cnfCompiledStepPolynomial`. The verifier-level input-size bound
substitutes `6n+6` for the paired raw length, while certificates are bounded by `2n+2`. The four
dedicated CNF axiom transcripts cover the codec/semantics, work-input bridge, generic verifier
bridge, and every public universal-correctness declaration; their closures are empty.

This proves `CNFSAT ∈ NP`. It does **not** prove `CNFSAT ∈ P`, supply a deterministic
polynomial-time SAT algorithm, establish NP-hardness or NP-completeness, or prove `P = NP`.

`lean/PNP/Complexity.lean` now exposes report-facing compatibility names for
the exact concrete objects:

```text
Language
PolyTimeDecider
NondetPolyVerifier
PolyTimeManyOneReduction
PClass
NPClass
ReducesToPoly
NPComplete
```

and proves:

```lean
theorem p_subset_np_witness_model {A : Language} :
    PClass A → NPClass A

theorem reduction_transports_p_witness_model {A B : Language} :
    ReducesToPoly A B → PClass B → PClass A

theorem np_complete_in_p_implies_p_eq_np
    {L : Language}
    (hComplete : NPComplete L)
    (hInP : PClass L) : PEqualsNP
```

These are abbreviations of the finite `PNP.Concrete.*` definitions, not
parallel string or name handles. `PNP.SAT` and `PNP.LockedNANDThreshold` are
likewise exact definitions of the concrete source and target languages. The
compatibility identity is checked in
[`lean_concrete_legacy_locked_nand_compatibility.md`](./lean_concrete_legacy_locked_nand_compatibility.md).

## Root status

`lean/PNP/Main.lean` exposes `PNP.Main.rootTheoremStatus`, an assumption-free structure recording
that formal reconstruction is in progress, external assumptions remain, and no public theorem has
been released. There is deliberately no declaration named `PNP.Main.p_eq_np` in the current root.
Building this status is evidence that the complete import root compiles; the status is not a theorem
of `P = NP`.

## Compiled theorem inventory and publication gate

After the root builds, `lean-audit/PNPTheoremInventory.lean` traverses
`Lean.Environment.constants` and applies `Lean.collectAxioms` to each public declaration in the
compiled `PNP` module closure. This avoids treating source-text parsing as kernel declaration or
dependency evidence. The deterministic output is mirrored byte-for-byte at
[`status/LEAN_THEOREM_INVENTORY.json`](../status/LEAN_THEOREM_INVENTORY.json) and
[`public/pnp-theorem-inventory.json`](../public/pnp-theorem-inventory.json).

For configured intermediate rows, the inventory also carries detailed theorem types. Credit
requires exact names/kinds, empty axiom closures, per-name domain-separated kernel-type SHA-256
matches, and the pinned closure of all Lean sources plus toolchain/Lake pins and the inventory
probe. Exact declaration, theorem, assumption-free-theorem, axiom, module, excluded-private, and
milestone counts are generated from the compiled environment rather than duplicated here. This
milestone binding is separate from the concrete publication gate.

Publication is controlled by a separate, fail-closed gate for compatibility declaration
`PNP.Main.p_eq_np` and concrete target `PNP.Main.ConcretePEqualsNP`. The target is present as an
axiom-free definition, but the compatibility/root theorem is absent. The expected target
type/value, root type, axiom-closure, and source-closure fingerprints are intentionally `null`;
unset fingerprints do not match and cannot activate the gate. The recursively compiled
charged-pipeline model is now eligible, but model eligibility cannot replace the absent SAT
completeness, SAT-in-P, and compatibility-root theorems. The
`PNP.PEqualsNP` compatibility alias cannot substitute for that root theorem. See
[`lean_theorem_inventory.md`](./lean_theorem_inventory.md) for the full contract and commands.

The inventory and false gate generate the current root TeX/PDF: a concise
formal-reconstruction report with no theorem emission. It replaces the historical 56-page claim
manuscript at the repository root; that historical artifact is available only through the pinned
legacy coordinate recorded under [`archive/legacy-v0/`](../archive/legacy-v0/README.md).

## Direct-wire NAND semantics

`lean/PNP/NANDSemantics.lean` defines an intrinsically topological NAND program: every gate source
is a boundary coordinate, a Boolean carrier constant, or an earlier gate. Ordered output wiring is
separate from the program, so projections, constants, and repeated coordinates add no gate cost.
The module gives total Boolean semantics, gate-count size, extensional equivalence laws, append
semantics, and checked zero-, one-, and two-gate examples.

`DirectWireSemanticsCertificate` and every explicit declaration in the module are assumption-free under
`#print axioms`. This milestone does not provide an enumerator, minimum-size definition, compatible
replacement, the slack law, a locked builder, or the locked threshold. See
`docs/lean_nand_semantics.md` for the precise boundary.

## Exact-width NAND enumeration

`lean/PNP/NANDEnumerator.lean` constructively lists every finite index, available source, ordered
NAND gate, topological program, output tuple, and implementation pair at fixed input/gate/output
widths. Membership theorems prove literal syntactic completeness, and the output tuple bridge covers
the function-backed `DirectWireWord` pointwise. Output width zero has one empty tuple; ordered NAND
inputs are not quotiented by commutativity.

The enumerator certificate and every explicit declaration are assumption-free under the dedicated axiom audit. It does not claim a
canonical or duplicate-free list. See `docs/lean_nand_enumerator.md` for its precise scope.

## Exhaustive direct-wire reference minimum

`lean/PNP/NANDTruthTable.lean` recursively enumerates every finite Boolean input tuple and checks
every ordered output coordinate. `equivalentBool_eq_true_iff` proves that the resulting Boolean is
true exactly when the two candidates satisfy pointwise `DirectWire.Equivalent`.

`lean/PNP/NANDMinimum.lean` scans exact candidate sizes in increasing order, bounded by the target
itself. `referenceMinimumWitness_equivalent` supplies a witness at the selected size,
`referenceMinimum_le_of_equivalent` proves the global lower bound against an equivalent candidate
of any size, and `referenceMinimum_invariant` makes the selected size semantic rather than
syntactic. `residualSlack_eq_zero_iff_minimum` characterizes zero slack. This exhaustive definition
has no polynomial-runtime claim and is not the historical residual-band minimizer axiom.

`lean/PNP/NANDComposition.lean` constructs physical serial composition and a
`FramedContext` with environment, support, bypass, and continuation blocks.
`compatibleReplacement_framed` transports direct-wire equivalence through that concrete frame.
`lean/PNP/NANDSlack.lean` derives the corresponding framed additive slack identity. These modules
do not formalize arbitrary support profiles or the locked-NAND global replacement claim. See
`docs/lean_nand_reference_minimum.md` for the audited boundary.

## Legacy witness-model SAT layer

`lean/PNP/SAT.lean` separates SAT membership in NP from SAT hardness:

```lean
theorem sat_in_np_witness_model : NPClass SAT

def SATHard : Prop :=
  ∀ {A : Language}, NPClass A → ReducesToPoly A SAT

def sat_np_complete_from_hardness (hHard : SATHard) : NPComplete SAT
```

This `PNP.SAT` object is an ordinary string-labelled value, not an axiom. Its verifier is still an
abstract witness handle, and it is deliberately not identified with `PNP.Concrete.CNFSAT`. The
direct raw-machine theorem above establishes NP membership only for the concrete language.

## Concrete locked-NAND macro layer

`lean/PNP/LockedNANDMacros.lean` is a concrete Boolean formalization of the report's local macros.

It defines every displayed gate for:

```text
M=  equality macro
M1  constant-one macro
M0  constant-zero macro
MN  NAND trace-check macro
four-gate final conjunction
```

Lean proves the distinguished-output identities by exhaustive Boolean case analysis:

```lean
(equalityMacro r u s).a8 = r && boolEq u s
(constantOneMacro r u).b2 = r && u
(constantZeroMacro r u).d3 = r && !u
(traceMacro l t u v).q16 = l && boolEq t (boolNand u v)
finalConjunction4 z t y = z && t && y
```

Lean also computes every exposed single-instance truth signature and checks that:

```text
10 equality outputs are pairwise distinct
2 constant-one outputs are pairwise distinct
3 constant-zero outputs are pairwise distinct
18 trace outputs are pairwise distinct
all exposed outputs are nonconstant
all exposed outputs differ from every positive projection
```

These results are assembled into:

```lean
def lockedNANDMacroCertificate : LockedNANDMacroCertificate
```

See `docs/lean_locked_nand_macros.md` for the exact scope.

## Concrete locked-NAND prefix layer

`lean/PNP/LockedNANDPrefix.lean` formalizes the report's two-gate prefix-conjunction node and the complete conjunction of a supplied check list.

It proves:

```lean
theorem prefixAndMacro_neg_spec (a b : Bool) :
    (prefixAndMacro a b).neg = !(a && b)

theorem prefixAndMacro_out_spec (a b : Bool) :
    (prefixAndMacro a b).out = (a && b)

theorem prefixConjunction_spec (checks : List Bool) :
    prefixConjunction checks = allChecks checks

theorem prefixConjunction_eq_true_iff (checks : List Bool) :
    prefixConjunction checks = true ↔
      ∀ b ∈ checks, b = true
```

For a nonempty list with `n` checks, Lean also proves that the construction has `n - 1` prefix nodes and exactly `2(n - 1)` NAND gates. The two exposed outputs of a prefix node are checked to be distinct, nonconstant, and nonprojection.

These results are assembled into:

```lean
def lockedNANDPrefixCertificate : LockedNANDPrefixCertificate
```

See `docs/lean_locked_nand_prefix.md` for the exact scope.

## Typed locked-NAND candidates and local baselines

`lean/PNP/LockedNANDDirect.lean` embeds all six displayed gadgets into the intrinsically typed
direct-wire model. Their gate/output widths are `10/10`, `2/2`, `3/3`, `18/18`, `2/2`, and `4/1`.
The embeddings agree with the Boolean macro semantics, and all six internal programs are proved to
contain no carrier constants.

`lean/PNP/DirectWireBaseline.lean` proves a general semantic output lower bound. If candidate
outputs are nonconstant, are not positive input projections, and are pairwise semantically
distinct, they inject into the program gates. Thus `outputs ≤ gates`; a square candidate satisfying
those conditions has exact empty-context `referenceMinimum` equal to its gate count.

`lean/PNP/LockedNANDLocalBaseline.lean` checks finite truth signatures and discharges those
conditions for the five square local candidates. Their exact minima are 10, 2, 3, 18, and 2. The
four-gate final conjunction has one output and is intentionally excluded from that exact-minimum
claim.

`lean/PNP/LockedNANDBaseline.lean` derives occurrence counts from actual typed sources. It proves
that an `m`-gate program has `2m` sources, `3m` distinguished checks, and report baseline
`18m + 10w_= + 3w_0 + 2w_1 + 2(3m-1)`, with four further displayed final gates. Its global
exactness theorem is conditional on constructing a real square baseline candidate and proving its
semantic output conditions.

The report convention is multi-output: the baseline coordinates plus one final coordinate remain
exposed. A legacy synthetic `m = 2` seed is quarantined because honest program-derived counts give
`86/90`, metadata-consistent counts give `95/99`, and its stored hybrid gives `91/95` for
baseline/displayed gates. See `docs/lean_locked_nand_baseline.md` for the derivation and proof
boundary.

## Conditional locked-NAND threshold boundary

`lean/PNP/LockedNANDThresholdBoundary.lean` packages the semantic boundary into six explicit
proof-bearing fields: `baselineCandidate`, `fullCandidate`, `baselineConditions`,
`initialOutputsPreserved`, `unsatisfiableFinalZero`, and `satisfiableFinalConditions`. Given those
fields, Lean proves that the full minimum is at least the baseline and its residual slack is at
most four. It also proves minimum exactly equal to the baseline in the unsatisfiable branch,
minimum in `[baseline + 1, baseline + 4]` in the satisfiable branch, and the conditional threshold
iff when the proposition is decidable.

The module also proves the model-level zero-output convention: one constant-zero output can be
appended by wiring without changing the program or gate count. This closes one direct-wire concern
from the hostile review, not the source-circuit trace theorem.

The package is not constructed in the conditional module. Its `satisfiable` parameter is an arbitrary proposition and
its `baseline` parameter an arbitrary natural number; neither is identified with circuit SAT or
`lockedBaselineCount`. Later global modules now supply complete baseline/full candidates,
cross-instance `BaselineDistinct`/`MacroDistinct`, both final-output laws,
`FinalLockSeparation`, and all six fields for one answer-independent typed candidate. An encoded
uniform polynomial builder and report-facing compatibility remain outside the
conditional module; downstream milestones now supply both. A deterministic
target decider remains missing. See
`docs/lean_locked_nand_threshold_boundary.md` for the exact premise and hostile-review inventories.

## Locked-NAND global carrier and trace equivalence

`lean/PNP/LockedNANDCarrierTrace.lean` defines the exact
`X ⊔ T ⊔ O ⊔ R ⊔ L ⊔ {z}` carrier for an arbitrary finite topological NAND
program. Its numeric width is `inputs + 6*gates + 1`; typed encoders and the
total decoder are mutual inverses, and the final lock is fresh from every
non-final family.

The module derives the ordered source occurrences and exactly three
distinguished checks per actual gate from the typed program. A canonical
coherent extension makes every check true. Conversely, topological induction
proves that every accepted trace coordinate is genuine program evaluation.
The fixed-input and existential forms establish the legacy Section 17
`TraceEquivalence` boundary for arbitrary finite NAND circuits.

The 71-declaration audit uses only empty closure, `propext`, and
`propext`/`Quot.sound`; it has no `Classical.choice` or project axiom. This is
not the complete exposed baseline/full candidate, cross-instance
`BaselineDistinct`, the four-gate final-output argument, a polynomial builder,
or the threshold theorem. See `docs/lean_locked_nand_carrier_trace.md`.

## Locked-NAND global candidate assembly

`lean/PNP/LockedNANDGlobalCandidates.lean` follows the next dependency in
legacy Section 17 for every finite typed circuit. It flattens the exact
carrier, builds every source and trace macro in topological order, folds the
three checks per gate with the exact two-gate prefix construction, and proves
the resulting count equals `lockedBaselineCount`.

Writing that count as `B`, Lean now constructs an exact `B`-gate/`B`-output
square baseline and an exact `B + 4`-gate/`B + 1`-output full candidate. Every
baseline output is preserved by the append. The new final coordinate is
proved equal to `z ∧ TraceChecks ∧ T_out`; both programs contain no internal
constants, and every baseline output is structurally independent of `z`.

The complete 64-declaration audit has three empty closures, two using only
`propext`, and 59 using only `propext` plus `Quot.sound`, with no
`Classical.choice` or project axiom.

The final five declarations establish global baseline distinctness. Every
exposed output is nonconstant, is not a positive carrier projection, and is
pairwise semantically distinct; the square baseline consequently has exact
exhaustive reference minimum `B`. The dedicated five-theorem transcript uses
only `propext` and `Quot.sound`.

The next module proves `unsatisfiableFinalZero` on the whole carrier and the
corresponding exact full-candidate minimum `B`. The following semantic-threshold
module proves all three satisfiable final conditions by fresh-lock separation,
packages all six fields, derives the exact typed threshold, and proves residual
slack at most four. A further concrete layer now fixes strict external source
and target bytes, proves direct output-normalization semantics, serializes the
complete candidate and threshold, and proves the pure all-bitstring semantic
transformation. The following source-parser layer now supplies the literal
validator machine, its all-input exact verdict/output theorem, compiled cubic
bound, polynomial machine/function witnesses, and leaf `RawRefinement`. The
following target-emitter layer now supplies exact raw target bytes,
polynomial bounds, strict parser composition, and recursive raw refinement.
The strict parser/emitter function is now packaged as
`PolynomialReduction EncodedNANDSAT EncodedLockedNANDThreshold`. A separate
all-input finite compiler packages `PolynomialReduction CNFSAT EncodedNANDSAT`
and their explicit composition. M186 now makes the report-level SAT and
locked-NAND endpoints exact definitions of those concrete languages and
consumes the compiled composition directly. A target decider and the
residual-band route remain absent. See
`docs/lean_locked_nand_global_candidates.md` and
`docs/lean_locked_nand_global_baseline_distinct.md`, then
`docs/lean_locked_nand_global_unsatisfiable_final_zero.md` and
`docs/lean_locked_nand_global_semantic_threshold.md`, followed by
`docs/lean_concrete_locked_nand_semantic_reduction.md`.

## Concrete strict-v0 source parser

`lean/PNP/Concrete/LockedNANDSourceParser.lean` is the public aggregate for
the executable source side of the encoded locked-NAND boundary. Its direct
work machine has a fixed nine-symbol alphabet, 228 control states, and 2,052
pairwise query-distinct literal rules. The executable table does not call the
pure token/circuit decoder or a host-side schedule.

The constructive failure layer classifies reserved `11xx` code points,
one-to-three trailing bits, malformed unary counts, both gate-source
positions, every required terminator, and trailing circuit tokens with exact
input equalities. The operational layers prove canonical packed layouts,
exact local source/reference traces, generic guard-seek and output-erasing
cleanup, and the restored accepting boundary. At those proved endpoints the
accepting tape exposes the original circuit bytes and the rejecting tape
exposes the empty output.

The compiled-bound layer fixes the conservative expression

```text
validWorkBound(n) = 4096 * (n + 1)^3
validRawBound(n) = 6 * validWorkBound(n).
```

It proves the polynomial evaluation and ordinary-start blank equivalence.
The aggregate's total exact theorem connects every valid, grammar-invalid,
and reference-invalid input to a halted endpoint within the work bound.
Acceptance is equivalent to `ValidEncodedCircuit`; the exact output is the
original source for valid input and the empty word for invalid input.

Compilation preserves those results for ordinary raw input. At
`6 * 4096 * (n + 1)^3` raw transitions, the compiled machine accepts exactly
the valid source language, returns exactly `validatedSourceBytes`, and never
times out. The module packages this as a `PolynomialTimeMachine`, a
nonexpanding `PolynomialTimeFunction`, and the validator program's leaf
`RawRefinement`. The axiom audit, regression, and hostile test are:

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteLockedNANDSourceParserAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteLockedNANDSourceParser.lean
node --test audits/lean-concrete-locked-nand-source-parser0.test.mjs
```

See
[`lean_concrete_locked_nand_source_parser.md`](./lean_concrete_locked_nand_source_parser.md)
for the exact current boundary.

## Concrete strict-v0 target emitter

`lean/PNP/Concrete/LockedNANDTargetEmitter.lean` is the public aggregate for
the executable target side. It combines a direct raw reconstruction of the
legacy locked-NAND candidate with one fixed 1,387,921-rule grammar-only
controller. Its executable graph uses disjoint parity-tagged control/block
addresses and does not call the decoder, semantic target function, host
schedule, or caller certificate while constructing the table.

Every input has an internally constructed exact halted trace. Grammar failure
rejects with empty output; grammar success accepts and emits
`RawBuilder.targetBytes`, including the deliberately broader
decoded-but-intrinsically-invalid case. A degree-five all-input runtime
polynomial and quadratic output-size polynomial bound the compiled function.

The strict public function composes this emitter with the source parser. It
therefore clears malformed and intrinsically invalid inputs and computes
`buildLockedNANDInstance` exactly on valid inputs. Both the standalone leaf
and recursive composition have `RawRefinement` witnesses. The audit,
regression, and hostile checks are:

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteLockedNANDTargetEmitterAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteLockedNANDTargetEmitter.lean
node --test audits/lean-concrete-locked-nand-target-emitter0.test.mjs
```

See
[`lean_concrete_locked_nand_target_emitter.md`](./lean_concrete_locked_nand_target_emitter.md)
for the exact grammar/strict boundary and remaining non-claims.

## Concrete strict-v0 polynomial reduction

`lean/PNP/Concrete/LockedNANDPolynomialReduction.lean` packages the exact
strict parser/emitter composition as
`PolynomialReduction EncodedNANDSAT EncodedLockedNANDThreshold`. The
reduction function is definitionally the existing
`strictLockedNANDPolynomialTimeFunction`; its output is exactly
`buildLockedNANDInstance`, its correctness field is the existing all-bitstring
language equivalence, and its recursive `RawRefinement` is retained.

This closes the concrete reduction-packaging edge in the legacy locked-NAND
route. It does not discharge the separate abstract threshold-language link.
Run the focused checks with:

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteLockedNANDPolynomialReductionAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteLockedNANDPolynomialReduction.lean
node --test \
  audits/lean-concrete-locked-nand-polynomial-reduction0.test.mjs
```

See
[`lean_concrete_locked_nand_polynomial_reduction.md`](./lean_concrete_locked_nand_polynomial_reduction.md)
for the exact interface and non-claims.

## Concrete CNF-to-NAND semantic compiler

`lean/PNP/Concrete/CNFToNAND.lean` traverses any decoded CNF formula
structurally and constructs an intrinsically topological NAND circuit without
querying satisfiability. Lean proves strict decoder inversion, exact
valuation and satisfiability semantics, well-formed strict-v0 output, exact
gate count, a quadratic serialized-output bound in external input length,
and fail-closed equivalence on every bitstring. Empty formulas are true,
empty clauses are false, and both signs of an out-of-range literal are false.

Pure semantic composition with the existing locked-NAND builder proves the
corresponding `EncodedLockedNANDThreshold` equivalence. The all-input milestone
in the following section now implements this exact pure function with a fixed
finite work machine and packages the resulting polynomial reductions.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCNFToNANDAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCNFToNAND.lean
node --test audits/lean-concrete-cnf-to-nand0.test.mjs
```

See
[`lean_concrete_cnf_to_nand_semantic_compiler.md`](./lean_concrete_cnf_to_nand_semantic_compiler.md)
for the exact semantic foundation and accounting.

## Concrete all-input CNF-to-NAND polynomial reduction

`lean/PNP/Concrete/CNFToNANDPolynomialReduction.lean` closes the executable
edge left by the semantic compiler. A fixed three-node work graph validates
every bitstring, constructs a retained CNF carrier, counts the exact target
gates, and emits the exact strict NAND bytes. Malformed inputs halt in reject
with empty output. Successfully decoded inputs halt in accept with output
equal to `CNFToNAND.compileEncodedCNFToNAND`.

The complete path has one polynomial bound in the original encoded input
length. The compiled boundary never times out at that bound and supplies a
literal `PolynomialTimeFunction` plus `FunctionProgram.RawRefinement`.
`CNFToNAND.cnfToNANDPolynomialReduction` reduces strict encoded CNF
satisfiability to strict encoded NAND satisfiability. Its explicit composition
with `LockedNAND.strictLockedNANDPolynomialReduction` reduces the same source
language to strict locked-NAND threshold instances.

The machine performs only syntax-directed compilation. It does not itself
decide CNF-SAT, prove CNF-SAT is in deterministic polynomial time, put the
locked-NAND threshold language in P, or establish `P = NP`.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCNFToNANDPolynomialReductionAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCNFToNANDPolynomialReduction.lean
node --test \
  audits/lean-concrete-cnf-to-nand-polynomial-reduction0.test.mjs
```

See
[`lean_concrete_cnf_to_nand_polynomial_reduction.md`](./lean_concrete_cnf_to_nand_polynomial_reduction.md)
for the executable architecture, exact theorem boundary, and non-claims.

## Global locked-NAND layer

`lean/PNP/LockedNAND.lean` now binds the report-facing endpoint to the exact
strict concrete language and reuses the compiled all-bitstring reduction:

```lean
def LockedNANDThreshold : Language :=
  Concrete.LockedNAND.EncodedLockedNANDThreshold

theorem sat_reduces_to_locked_nand_checked :
    ReducesToPoly SAT LockedNANDThreshold :=
  Main.locked_nand_threshold
```

The local macro truth laws, supplied-list prefix exactness, typed local candidates, source-derived
accounting, semantic output lower bound, five local square minima, carrier/trace equivalence, and
deductions from the six-field conditional boundary package are no longer part of that trust
object. The complete exposed candidates and cross-instance baseline separation
are now constructed on that carrier, and the whole-carrier unsatisfiable
final-zero law, satisfiable final-lock separation, typed semantic threshold,
and residual-slack-at-most-four theorem are proved. A strict encoded semantic
boundary now contains the complete candidate and proves source/target
equivalence. Its strict-v0 source parser now has total exact correctness,
compiled non-timeout, exact validated-byte output, polynomial machine/function
witnesses, and leaf raw refinement. Its target emitter now adds exact raw
target bytes, an all-input compiled polynomial, an output-size polynomial,
strict parser composition, and recursive raw refinement. The report-level
language linkage and reduction edge are therefore checked rather than caller
supplied. Remaining global work is to put that concrete target in P through
the unconditional residual-band/ZeroSlack/PCCMin route; concrete SAT
NP-hardness and the eligible root theorem also remain open.

## Residual-band, ZeroSlack, and PCCMin layers

`lean/PNP/ResidualRoutes.lean` is the current executable foothold. It checks a caller-supplied
finite list for a strictly smaller truth-table-equivalent implementation. Scanner success carries
list membership, semantic equivalence, strict gate-count reduction, and strict residual-slack
descent. The scanner result type has only `gain` and `unresolved` constructors. Separate `exact`
and `zeroSlack` route constructors require proofs of `IsSemanticallyMinimum`.

Search failure is not ZeroSlack. `firstListedGain_none_no_listed_gain` excludes only members of the
supplied list, and `unresolved_positiveSlack_regression` constructs an unresolved empty-list case
with residual slack one. No list-generation completeness, global route completeness, or polynomial
runtime is proved. See `docs/lean_residual_routes.md`.

`lean/PNP/ResidualGainChain.lean` now closes the separate iteration-count
edge from report §16. It validates every adjacent strict equivalent gain in
an arbitrary finite disclosed chain, preserves the endpoint semantics and
reference minimum, and proves that endpoint residual slack plus chain length
is at most starting residual slack. The locked candidate's report-§17 slack
bound then gives at most four verified steps. This still does not generate a
route, turn failure into ZeroSlack, prove exact minimization, or establish a
polynomial runtime. See `docs/lean_residual_gain_chain.md`.

`lean/PNP/ResidualGainStopping.lean` closes the next semantic edge from report
§16. For every finite direct-wire implementation, positive residual slack is
equivalent to existence of some strict equivalent gain; zero slack and
semantic minimality are equivalent to global absence of every such gain. A
proof-bearing or executably checked chain whose endpoint separately carries
that global no-gain proof therefore yields endpoint slack zero and an exact
minimum result. The positive witness is supplied by the exhaustive semantic
reference minimum, so this statement neither generates a route nor supplies a
polynomial stopping procedure. Finite-list failure remains insufficient. See
`docs/lean_residual_gain_stopping.md`.

`lean/PNP/ResidualTerminalFullBridge.lean` closes the direct-wire full-mode
part of the terminal whole-carrier bridge from report §8. Its terminal
realizations agree with the whole implementation at every input/output
coordinate, terminalization preserves exact gate count, and an independently
stated attained universal minimum is equal to the exhaustive reference
minimum. This gives the direct-wire terminal `RW-MuBridge`. Positive slack is
equivalent to a cheaper complete whole-span realization, which supplies strict
residual descent, while zero slack is equivalent to absence of such a
realization. This does not formalize the manuscript's quotient carrier or mode
firewall in this module, proper supports, saturation, BCEL/BN2–BN6, selectors,
ZeroSlack, PCCMin, or polynomial runtime. See
`docs/lean_residual_terminal_full_bridge.md`.

`lean/PNP/ResidualTerminalModeFirewall.lean` closes the adjacent finite-profile
mode edge from report §§5.1–5.2. A role-indexed observer computes finite
carrier-profile coordinates from the represented implementation, and a
forgetful projection selects which coordinates a quotient comparison retains.
Projection preserves the exact implementation, gate count, and all Boolean
semantics. Promotion back to the full carrier is checked: it exists exactly
when every forgotten coordinate agrees, and a concrete forgotten mismatch
rules it out. Obligation-coordinate discharge also transports across a checked
lift. This is still only the terminal comparison/lifting firewall; it does not
construct proper or governed supports, a projection-defect minimum, saturation,
Package E, BCEL/BN2–BN6, ZeroSlack, PCCMin, or a polynomial residual route. See
`docs/lean_residual_terminal_mode_firewall.md`.

`lean/PNP/ResidualTerminalProjectionMinimum.lean` closes the next unbounded
finite-family edge from report §5.1, Projection Monotonicity. For every finite
direct-wire implementation, computed terminal-profile observer, and explicit
projection, it exhaustively scans all candidate sizes through the current gate
count and returns attained full-profile and quotient-profile minima. Both are
universal minima, projection cannot increase the quotient minimum, and their
difference is an exact nonnegative projection defect. The defect is zero
exactly when an attained quotient minimum has the mode firewall's checked full
lift; positive defect rules that lift out at every quotient minimum. This is a
finite reference computation, not a polynomial minimizer, and it does not yet
construct proper supports, SaturatePositive, Package E, BCEL/BN2–BN6,
ZeroSlack, or PCCMin. See
`docs/lean_residual_terminal_projection_minimum.md`.

`lean/PNP/ResidualTerminalProjectionTransfer.lean` closes the adjacent bounded
arithmetic edge from report §5.2, Mode firewall and transfer identity. Four
implementations share one computed observer and one projection. Their full and
quotient four-corner deltas live in signed integers, and the difference of
those deltas is proved exactly equal to the corresponding balance of the four
projection defects. Under the manuscript's constant-cut defect hypotheses,
the projection excess equals the join defect and is positive when that defect
is positive. The record carries data, not a certificate that the corners form
a proper or saturated support square. Proper-support construction,
`SaturatePositive`, Package E, BCEL/BN2–BN6, ZeroSlack, PCCMin, and polynomial
runtime therefore remain open. See
`docs/lean_residual_terminal_projection_transfer.md`.

`lean/PNP/ResidualTerminalSaturation.lean` closes the general support-closure
edge from report §3, Saturated support calculus and square closure.  A finite
primitive universe contains gate, boundary, interface, and computed profile
records.  An explicit Boolean dependency relation uses the manuscript's ten
rule tags.  Its reflexive transitive closure is proved extensive, closed,
least, monotone, and idempotent, with fixed points exactly the closed supports.
This does not yet extract those dependencies from an arbitrary circuit or
construct proper support, support completion, a legitimate projection square,
`SaturatePositive`, Package E, BCEL/BN2–BN6, ZeroSlack, PCCMin, or polynomial
runtime.  See `docs/lean_residual_terminal_saturation.md`.

`lean/PNP/ResidualTerminalExecutableSaturation.lean` and
`lean/PNP/ResidualTerminalPhysicalSupportCompletion.lean` close the next
bounded dependency edge from report §§2–3. A deterministic finite work list
computes exactly the existing inductive saturation for every finite seed and
explicit terminal dependency system. The actual direct-wire program then
computes the canonically ordered physical support triple `(U, ∂U, ιU)` for the
selected gates: input and external-gate wires crossing inward form `∂U`, while
selected gate outputs consumed outside the selection or exposed as program
outputs form `ιU`. Constants and internal wires remain internal. Universal
membership theorems prove no crossing wire is omitted or added and package the
combined saturation/physical result as compatible. The dependency system is
still explicit rather than the manuscript profile frontier; proper positive
support, square legitimacy, the required projection square,
`SaturatePositive`, ZeroSlack, PCCMin, and polynomial runtime remain open. See
`docs/lean_residual_terminal_physical_support_completion.md`.

`lean/PNP/ResidualTerminalSupportExtraction.lean` closes the adjacent general
extraction edge from report §2.2. It structurally scans every finite direct-wire
program and extracts any canonically selected, possibly noncontiguous gate set
over the exact incoming boundary and ordered outgoing interface. Constants and
selected-to-selected wires stay local; primary inputs and unselected
predecessors become boundary inputs. The extracted candidate is proved equal
to an independent open-support semantics for every boundary valuation and to
recover original interface values on whole-circuit-induced boundaries. This
still does not derive the profile frontier, proper positive support, square
legitimacy, `SaturatePositive`, ZeroSlack, PCCMin, or polynomial runtime. See
`docs/lean_residual_terminal_support_extraction.md`.

`lean/PNP/ResidualTerminalProperSupport.lean` closes the next finite
proper-positive search edge from report §§2.2, 3, and 10. It enumerates every
canonical subset of the terminal primitive-record universe, saturates and
extracts each seed, and computes exact local gain against the exhaustive
minimum for the same open function. A proof-bearing result is nonempty,
strictly smaller than the ambient gate carrier, dependency-closed, physically
compatible, and equipped with an equivalent strictly smaller minimum
replacement. Search failure is equivalent to absence of every governed
proper-positive canonical seed. The explicit dependency system remains data,
and the exhaustive search has no polynomial-runtime claim. Full profile
frontier derivation, governed completion, square legitimacy, the projection
square, `SaturatePositive`, `BCELReady`, ZeroSlack, and PCCMin remain open. See
`docs/lean_residual_terminal_proper_support.md`.

`lean/PNP/ResidualTerminalSupportSquareClosure.lean` closes the algebraic and
physical part of the report §3 saturated support-square closure edge. For every
finite direct-wire candidate, explicit terminal dependency system, and pair of
finite seeds, it computes closed left and right saturations, their canonical
intersection meet, and the saturated-union join. The meet and join satisfy the
exact greatest-lower-bound and least-upper-bound laws, all four corners are
closed, and seed ordering or duplication does not change corner membership.
Every corner has a computed compatible physical boundary and an exact open
candidate with proved semantics and induced whole-circuit recovery. The
dependency system is still explicit data. Frontier pushout, profile transport,
projection compatibility, BN2 square legitimacy, `SaturatePositive`,
`BCELReady`, ZeroSlack, PCCMin, and polynomial runtime remain open. See
`docs/lean_residual_terminal_support_square_closure.md`.

`lean/PNP/ResidualTerminalGovernedSupportCompletion.lean` closes the next
bounded completed-support edge from report §§2 and 3. For every saturated
support-square corner, it retains the exact closed record list and computes
the physical boundary, ordered interface, and selected profile coordinates in
each of the ten terminal profile roles. Lean proves exact profile membership,
duplicate freedom, pairwise role disjointness, complete selected-record
coverage, dependency closure, and physical compatibility. The dependency
system remains explicit data. This does not prove the frontier pushout,
projection compatibility, side-tight minima, BN2 square legitimacy,
`SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, polynomial runtime, or the
root theorem. See
`docs/lean_residual_terminal_governed_support_completion.md`.

`lean/PNP/ResidualTerminalFrontierPushout.lean` closes the report §3
governed frontier-gluing edge. For every finite direct-wire candidate and
computed saturated support square, it constructs the boundary, interface, and
role-preserving profile gluing from the two side completions alone. Lean proves
that the independently computed join frontier equals this pushout, that the
meet profiles are exactly the shared side coordinates, and that physical
coordinates which disappear are genuinely internalized by the opposite side
or by the combined support. The dependency system remains explicit data. This
does not prove projection compatibility, side-tight minima, BN2 square
legitimacy, `SaturatePositive`, `BCELReady`, obstruction routing, ZeroSlack,
PCCMin, polynomial runtime, or the root theorem. See
`docs/lean_residual_terminal_frontier_pushout.md`.

`lean/PNP/ResidualTerminalProjectionSquare.lean` closes the next report §3
structural projection-commutation edge. For every finite computed saturated
support square and every explicit forgetful terminal projection, it retains
the exact physical boundary and interface, filters each profile role exactly,
proves projected meet is the shared side profile, and proves projected join is
the side-only projected frontier pushout. The terminal dependency system
remains explicit data. This does not prove side-tight four-corner minima, BN2
square legitimacy, `SaturatePositive`, `BCELReady`, obstruction routing,
ZeroSlack, PCCMin, polynomial runtime, or the root theorem. See
`docs/lean_residual_terminal_projection_square.md`.

`lean/PNP/ResidualTerminalSideTightMinimum.lean` closes the numerical
arithmetic and no-overclaim edge in report §11.1 `BN2-CoherentOptimum`. For
every finite four-corner family it proves componentwise lower bounds for typed
full and quotient bases, the signed four-slack identity, and a fail-closed
extractor which returns the existing delta only after all four minima are
attained exactly. Canonical independently attained full and quotient minima
pass that gate. This does not construct a coherent four-corner basis, prove
BN2 square legitimacy, maximize a tight family, or establish
`SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, polynomial runtime, or the
root theorem. See
`docs/lean_residual_terminal_side_tight_minimum.md`.

`lean/PNP/ResidualTerminalFourCornerCarrier.lean` closes the checked common
carrier prerequisite between report §3 and §11.1
`BN2-CoherentOptimum`. Every computed saturated support square supplies the
meet, left, right, and join endpoints from the same candidate and projection.
Lean proves exact extracted endpoints, duplicate-free canonical coordinate
lists, exact profile overlap and union, fail-closed retained or internalized
physical transport, and projection compatibility. No caller supplies a
coordinate map or transport certificate. This does not transport four optimum
realizers, prove `fourCornerOptimaCarrierCompatible`, construct a coherent
four-corner optimum, prove BN2 square legitimacy, or establish
`SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, polynomial runtime, or the
root theorem. See
`docs/lean_residual_terminal_four_corner_carrier.md`.

`lean/PNP/ResidualTerminalFourCornerOptimumCompatibility.lean` closes the
legacy §11.1 obligation `fourCornerOptimaCarrierCompatible`. It provides a
reversible common ambient coordinate system for all four exact corner
candidates and proves semantic, equivalence, gate-count, and
reference-minimum preservation in both directions. One explicit observer and
the carrier's one quotient projection then govern all four canonical full and
quotient optima, whose localized realizers retain their exact minimum counts.
This does not establish coherent square-leg transport,
`sideTightCompletionExists`, BN2 square legitimacy, `SaturatePositive`,
`BCELReady`, ZeroSlack, PCCMin, polynomial runtime, or the root theorem. See
`docs/lean_residual_terminal_four_corner_optimum_compatibility.md`.

`lean/PNP/ResidualTerminalFourCornerOptimumCoherence.lean` closes the next
finite interface in the legacy §11.1 `BN2-CoherentOptimum` paragraph. It
derives the four support inclusions from the computed square, uses exact
ambient coordinates on every leg, compares only retained output semantics,
and checks profiles in the manuscript's ten-role order. Full mode checks open
obligations first. Quotient mode checks only retained coordinates and exposes
a separate forgotten-coordinate failure query, so quotient evidence is never
silently promoted. The universal theorem returns either a checked side-tight
canonical tuple or the exact sound first failure. It does not prove that the
coherent branch always occurs, discharge the later no-outcome routes, prove
`sideTightCompletionExists`, establish BN2 square legitimacy, or establish
`SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, polynomial runtime, or the
root theorem. See
`docs/lean_residual_terminal_four_corner_optimum_coherence.md`.

`lean/PNP/ResidualTerminalFourCornerSideTightCompletion.lean` closes the local
legacy Section 11.1 `sideTightCompletionExists` edge. It reuses the exact
deterministic first coherence-failure query as a proof-bearing local route.
For every finite carrier and selected mode, Lean returns either that exact
first sound route or the complete checked side-tight coherent optimum tuple.
The route and completion branches are disjoint, and computed route silence
implies the completion together with the exact full or quotient incidence
value. The forgotten-coordinate promotion query remains separate and cannot
promote quotient evidence into a full completion. This does not prove
universal route silence, discharge the complete global no-outcome routes,
prove BN2 square legitimacy, derive the terminal dependency system, maximize
the complete tight-basis family, or establish `SaturatePositive`, `BCELReady`,
ZeroSlack, PCCMin, polynomial runtime, or the root theorem. See
`docs/lean_residual_terminal_four_corner_side_tight_completion.md`.

`lean/PNP/ResidualTerminalCandidateSaturation.lean` and
`lean/PNP/ResidualTerminalSaturationCostBalance.lean` close two more finite
edges of the legacy `RW-SaturatePositive` boundary. The production classifier
derives physical dependencies from actual circuit incidence and profile
dependencies from exhaustive context-sensitive observer influence; it accepts
no caller-supplied dependency relation or extraction certificate. A
rule-labelled deterministic trace then recomputes exact support, full-minimum,
and quotient-minimum costs at every event. It either proves transparent cost
balance through the complete linked history, preserving full slack and
positivity, or returns the exact first nontransparent event with one of five
typed reasons. Together with the preceding positivity firewall, this closes
the finite terminal forms of `transparentSaturationCostBalanced` and
`firstNontransparentStepRecorded`. Nontransparent events are recorded but not
yet routed: `interfaceExposureRoutesToE` and
`originKernelObligationClosureRouted` remain open, so `SaturatePositive`,
`BCELReady`, ZeroSlack, PCCMin, polynomial runtime, and the root theorem remain
unproved. See
`docs/lean_residual_terminal_saturation_cost_balance.md`.

`lean/PNP/ResidualTerminalInterfaceExposureRouting.lean` closes the finite
local form of `interfaceExposureRoutesToE`. Its shape recognizer accepts only
the outgoing interface coordinate or its gate/boundary materializer, and the
production query independently recomputes the exact candidate-derived
`interfaceConsumer` edge. The step classifier returns either the existing
transparent cost-balance proof or a local E-route carrying the computed
coordinate, exact typed failure reason, and nontransparency evidence. At trace
level the route is tied to the deterministic first nontransparent event and
its complete transparent prefix; a first non-interface failure remains a
separate fail-closed outcome. Transparent outgoing-coordinate completion is an
exact zero-cost retract preserving full slack. This is not Package E
`VerifyDW`, global gain, or global route completeness, and it does not close
`originKernelObligationClosureRouted`, full `SaturatePositive`, `BCELReady`,
ZeroSlack, PCCMin, polynomial runtime, or the root theorem. See
`docs/lean_residual_terminal_interface_exposure_routing.md`.

`lean/PNP/ResidualTerminalOriginKernelObligationRouting.lean` recognizes exact
candidate-derived origin, kernel, and obligation closure edges in both
gate/profile orientations. Its safety check combines the existing transparent
cost proof with an after-state obligation check and equality of every forgotten
profile coordinate across the event. Unsafe recognized events carry one
deterministic reason: the existing balance failure, an open obligation, or a
forgotten-profile mismatch. The composed trace dispatcher gives interface
routing first priority, then closure routing, and retains every other first
nontransparent event in a separate fail-closed branch with its complete safe
prefix.

`lean/PNP/ResidualTerminalFiniteSaturatePositive.lean` defines the explicit
proof-bearing problem used for finite composition: an existing
`TerminalCandidateBCELAnchorProblem` plus positive full slack at its normalized
seed. When every trace event is safe, linked cost balance preserves positive
full slack and the existing projection-positivity classifier returns either a
zero-defect checked full lift or a positive-defect BCEL outcome. Otherwise the
composite returns the exact first interface, origin/kernel/obligation, or other
nontransparent route. This composes the five reconstructed finite terminal
sub-obligations only. It is not a mapping to the manuscript's complete global
outcome set, Package E, RankWF, full `SaturatePositive`, or `BCELReady`. See
`docs/lean_residual_terminal_finite_saturate_positive.md`.

`lean/PNP/ResidualTerminalFiniteBCELReady.lean` runs one checked bridge across
both existing classifiers. `checkTerminalFiniteBCELReady` recomputes the finite
`SaturatePositive` outcome and accepts only a positive-projection branch whose
nested BCEL result is `ready`. The proof-bearing certificate retains the exact
selection equality, safe trace, both positivity facts, and computed nucleus;
projection theorems expose the nontrivial anchor bound, exact proper-cut
equation, and local BN2 conclusion. It does not infer the initial positivity
premise, map rejected local branches globally, construct BN3--BN6 inputs,
derive constant activation, or establish full `SaturatePositive`, `BCELReady`,
ZeroSlack, or PCCMin. See
`docs/lean_residual_terminal_finite_bcel_ready.md`.

`lean/PNP/ResidualTerminalFiniteBCELPacketCarrierCoherence.lean` closes the
next structural seam without rerunning either underlying classifier. Its
certificate is indexed by the exact accepted Packet/budget no-lower record, so
the M183 terminal problem uses the same candidate and model. An injective and
surjective anchor map plus a reflected list equality identifies the ready
nucleus image with the exact grouped Packet carrier. This transfers the
nontrivial-size theorem and combines it with the existing same-family Packet
exclusion to rule out constant activation. The problem, positive premise,
family, map, payloads, realizer/dependency tables, and ranks remain supplied;
activation weights are not identified with projection excess, and this is not
unconditional ZeroSlack or polynomial PCCMin. See
`docs/lean_residual_terminal_finite_bcel_packet_carrier_coherence.md`.

`lean/PNP/ResidualTerminalFiniteBCELPacketActivationObstruction.lean` makes the
remaining numerical compatibility question executable on that exact family.
It computes the terminal defect from the M183 problem and nucleus, checks the
Packet cut value, and exhaustively checks every canonical nonempty proper-cut
activation weight. Acceptance would recover the mapped-cut projection
equation, while M184's same-family Packet exclusion proves that complete
activation coherence cannot hold. The deterministic result is therefore a
proof-bearing cut-value mismatch or first proper-cut activation mismatch. This
diagnoses, but does not repair, the missing bridge. All terminal, family, map,
activation, payload, table, and rank data remain supplied; the scan may be
exponential, and unconditional ZeroSlack and polynomial PCCMin remain open.
See
`docs/lean_residual_terminal_finite_bcel_packet_activation_obstruction.md`.

`lean/PNP/ResidualTerminalRankWF.lean` formalizes the fixed rank named after
`RW-SaturatePositive`: witness type, span type, mode, frontier defect,
projection defect, saturation defect, anchor count, charge size, profile size,
and canonical code. The exact right-associated product is ordered by nine
nested `Prod.lex` constructions over `Nat.lt_wfRel`; Lean proves this relation
well-founded and exposes accessibility, induction, per-coordinate priority
witnesses, and an equivalent executable comparison. A concrete descent record
must carry the relation proposition. This is `RankWF` only: the current finite
routes have not been mapped to the complete global outcome system or proved to
decrease this rank. See `docs/lean_residual_terminal_rank_wf.md`.

`lean/PNP/ResidualTerminalBN3RequestEnvelope.lean` constructs a finite BN3
request envelope after the computed BCEL anchor-nucleus classifier succeeds.
One canonical duplicate-free primitive-record list supplies stable monotone
membership requests and exact singleton minimal consumers across every proper
cut. Filtering it gives exact duplicate-free incidence, while one canonical
full/quotient basis function is proved side-tight and coherent at every proper
cut. The total classifier retains all existing proof-bearing failure branches.
Its all-subsets cut enumeration is exponential, and it does not construct the
full historical BN4–BN6 chain, complete the global route system, prove
selector/realizer closure, ZeroSlack, PCCMin, SAT in P, or the root theorem. See
`docs/lean_residual_terminal_bn3_request_envelope.md`.

`lean/PNP/ResidualTerminalBN4ActivationCancellation.lean` closes the adjacent
finite activation and cancellation edge. From a successful BN3 envelope it
uses the exact singleton minimal consumer as a canonical activation code and
proves code equality equivalent to activation-function equality without a cut
scan. Explicit signed cells carry a complete key consisting of the request
atom, semantic signature, and transport type. The executable per-key
classifier proves exact integer mass conservation and produces a canonical
balanced or one-sign positive-mass residual with the full key preserved and no
opposite-sign pair. Its total wrapper preserves every upstream failure and
rejects foreign atoms. The typed ledger and its semantic/transport labels are
still caller data, so this is not the full historical BN4 theorem and supplies
no PkgC/BN6, complete routes or selectors, ZeroSlack, PCCMin, polynomial
runtime, SAT in P, or root theorem. See
`docs/lean_residual_terminal_bn4_activation_cancellation.md`.

`lean/PNP/ResidualTerminalBN5FullShadowLocalization.lean` closes a finite
full-shadow localization edge over arbitrary explicit finite inputs. It
canonically refines a negative BN4 residual into indexed full units whose
complete coordinates include the BN4 key, frontier, charge owner, obligation,
origin kernel, and mode projection. The total classifier validates the exact
negative mass, computes cut silence, and otherwise computes complete
exact-coordinate multiplicity coverage or a strict Hall deficit. Every
deficit exposes a smaller literal shadow-neighbor list than its full-unit
fibre and routes to local X1, so an active unmatched unit cannot disappear as
silence. The payloads and shadow universe are still explicit inputs, matching
is not connected to a BN4 contradiction, and this is not the full historical
BN5 theorem. CritC/Q/E/L/X2-X4, PkgC/BN6, global routes and selectors,
polynomial generation/runtime, ZeroSlack, PCCMin, SAT in P, and the root
theorem remain open. See
`docs/lean_residual_terminal_bn5_full_shadow_localization.md`.

`lean/PNP/ResidualTerminalPkgCSeparatingConsumers.lean` reconstructs a finite
PkgC separating-consumer restoration edge for an arbitrary explicit
minimal-consumer antichain. Its canonical nested scan selects the first
disjoint pair that is not singleton-singleton; scan absence is proved
equivalent to the exact V54 singletonization premise. For a found pair, the
module generates canonically indexed quotient units from all atoms of both
consumers, maps them into exact BN5 coordinates, and classifies an explicit
finite full-restoration universe as complete coordinate multiplicity coverage
or a strict Hall deficit with a named local Q route. Its 27-declaration axiom
transcript stays within `propext` and `Quot.sound`, and regressions exercise
the singletonized, covered, and Hall-localized branches. The restoration
universe remains explicit, matching is not connected to a BN4/BN5
contradiction, and the local route is not embedded into the complete global
outcome system. Full historical PkgC and route silence, terminal-candidate
derivation, BN6/Packet selector-realizer completeness, polynomial runtime,
ZeroSlack, PCCMin, SAT in P, and the root theorem remain open. See
`docs/lean_residual_terminal_pkgc_separating_consumers.md`.

`lean/PNP/ResidualTerminalPkgCTypedRestoration.lean` strengthens the same
finite edge with actual typed full candidates. An explicit
coordinate-preserving restorer is mapped over every atom of the canonical
first separating pair. Lean proves exact candidate count, positional
coordinate preservation, and complete equality-fibre multiplicity coverage;
the same coverage excludes a strict Hall deficit. The total classifier has
only V54 singletonization or a proof-bearing typed realization. Its exact
17-declaration transcript stays within `propext` and `Quot.sound`. The
restorer and its preservation theorem remain caller data, so this does not
construct restoration from a terminal candidate, prove semantic adequacy,
connect the covered branch to a BN4 or BN5 contradiction, complete global
routing, or establish full PkgC, BN6/Packet, polynomial runtime, ZeroSlack,
PCCMin, SAT in P, or the root theorem. See
`docs/lean_residual_terminal_pkgc_typed_restoration.md`.

`lean/PNP/ResidualTerminalPkgCSameKeyCancellation.lean` consumes that typed
realization at the next manuscript edge. It constructs, rather than accepts,
an opposite-sign unit-cell ledger for every atom of the canonical separating
pair. Complete BN5-coordinate preservation gives literal equality of the
nested BN4 keys. Lean then proves the exact cell count, positive/negative mass
equality at every BN4 key, empty executable residual lists, and zero signed
mass. The total result is singletonization or a proof-bearing typed
cancellation realization; excluding every such realization forces the exact
V54 singletonization premise. The restorer and coordinate maps remain explicit.
The successor module binds the generated ledger to an explicit ambient BN4
ledger while retaining a candidate-derived BN4 kernel, but does not derive
that ledger or binding from the candidate,
so global route integration and silence, full historical
PkgC, BN6/Packet selector-realizer completeness, polynomial runtime,
ZeroSlack, PCCMin, SAT in P, and the root theorem remain open. See
`docs/lean_residual_terminal_pkgc_same_key_cancellation.md`.

`lean/PNP/ResidualTerminalPkgCAmbientBN4Ledger.lean` then binds the generated
cells to an explicit ambient BN4 ledger by exact permutation with an explicit
remainder. It preserves duplicate counts, decomposes positive and negative
mass, and proves that removing the balanced generated subledger leaves exactly
the remainder's signed mass and executable residual contribution. When given
a successful candidate-derived BN4 kernel, every embedded generated cell is
also tied to its canonical request-atom space. The executable classifier only
accepts canonical generated-then-remainder serialization; arbitrary order
requires a kernel-checked permutation proof. The module does not derive the
ambient ledger or restorer from the candidate, establish semantic restoration
adequacy, complete global routes or silence, or prove the downstream global
claims. See
`docs/lean_residual_terminal_pkgc_ambient_bn4_ledger.md`.

`lean/PNP/ResidualTerminalPkgCAmbientBN4ResidualReduction.lean` then proves
the executable reduction hidden behind that signed-mass equality. Removing the
exact balanced generated subledger preserves every per-key residual cell and
the complete residual ledger on the ambient canonical key universe. It proves
that universe contains every remainder key, provides a fail-closed canonical
classifier that constructs the reduction mechanically, and derives empty
ambient residuals when the explicit remainder is empty. It does not derive the
ledger, restorer, embedding, or remainder from the candidate, prove the
remainder is empty or route-producing, establish restoration semantics or
global route silence, or discharge downstream global claims. See
`docs/lean_residual_terminal_pkgc_ambient_bn4_residual_reduction.md`.

`lean/PNP/ResidualTerminalConsumerAntichainNormalForm.lean` reconstructs the
manuscript's unbounded V54 consumer-antichain theorem. For an arbitrary finite
carrier and explicit minimal-consumer antichain, it generates the monotone
empty-false request function, proves that nonzero two-sided activation is
equivalent to existence of a disjoint consumer pair, and proves under PkgC's
exact singletonization premise that the activation Boolean equals the cut
indicator of the singleton footprint on every cut. The source contains no
fixed `Fin` carrier or hard-coded cut coordinate. It consumes the explicit
antichain and therefore does not complete PkgC or prove its global route
silence, derive consumers from a terminal candidate, connect the V54 footprint
to V53 or BN6 payloads, complete global routing or selectors, establish
polynomial runtime, prove ZeroSlack or PCCMin, put SAT in P, or produce the root
theorem. See
`docs/lean_residual_terminal_consumer_antichain_normal_form.md`.

`lean/PNP/ResidualTerminalConstantCutHypergraphRigidity.lean` reconstructs the
manuscript's V53 constant-cut classification for arbitrary finite
duplicate-free carriers and sparse positive hyperedges. Exact cut mass
partition and singleton-to-pair comparison prove the q=2, q=3, and q>=4
branches without a fixed `Fin` carrier: full-span weight `D`; equal pair weight
`p` with `w_A + 2p = D`; or zero proper-footprint weight and full-span weight
`D`. Its 58-declaration transcript stays within `propext` and `Quot.sound` and
the regression exercises all three branches plus hostile unequal-pair data.
It consumes an explicit hypergraph and therefore does not construct PkgC,
derive that hypergraph from a terminal candidate, build BN6 cells or payloads,
complete global routes or selectors, establish polynomial runtime, prove
ZeroSlack or PCCMin, put SAT in P, or produce the root theorem. See
`docs/lean_residual_terminal_constant_cut_hypergraph_rigidity.md`.

`lean/PNP/ResidualTerminalBN6HypergraphPacket.lean` reconstructs the adjacent
finite BN6 hypergraph-packet bridge for an arbitrary finite duplicate-free
anchor carrier and an explicit already-grouped positive survivor family. Each
group retains its V54 consumer system, exact PkgC singletonization premise,
positive atom ledger, and payloads. The bridge identifies group activation
with hyperedge crossing pointwise, sums those identities into the exact V53
cut weight, applies the constant-cut classification, and retains an original
payload witness at every positive emitted footprint. Its 21-declaration axiom
transcript stays within `propext` and `Quot.sound`; regressions cover the q=2,
mixed q=3, and q>=4 cases plus hostile grouping, singletonization, and
constant-cut failures. It does not construct PkgC, derive or group survivors
from a terminal candidate, prove the full historical BN6 or Packet
selector/realizer route, establish polynomial generation/runtime, prove
ZeroSlack or PCCMin, put SAT in P, or produce the root theorem. See
`docs/lean_residual_terminal_bn6_hypergraph_packet.md`.

`lean/PNP/ResidualTerminalPacketSelectorSeeds.lean` reconstructs the next
finite Packet edge over every exact BN6 conclusion. It preserves carrier
containment, selector-relevant footprint size, and the original cell-and-atom
payload witness. The exhaustive conclusion yields one pair seed, seeds for
every positive balanced-triple pair footprint, or one positive full-span seed,
including the full-span side of the mixed three-anchor branch. Its exact
five-declaration transcript stays within `propext` and `Quot.sound`, and its
generic regression fixes no carrier. This does not prove selector-universe
membership, faithfulness or compatibility, construct realizers or routes,
establish enumeration or polynomial runtime, complete PkgC, ZeroSlack, or
PCCMin, put SAT in P, or produce the root theorem. See
`docs/lean_residual_terminal_packet_selector_seeds.md`.

`lean/PNP/ResidualTerminalPacketSelectorUniverse.lean` reconstructs the next
finite Packet edge. It enumerates the exact duplicate-free grouped-footprint
list of an arbitrary explicit BN6 family, proves membership equivalent to an
original grouped cell, and upgrades each earlier raw seed to membership while
retaining its carrier, footprint-size, cell, and atom evidence. This is an
input-relative payload-selector universe only. It does not construct the
manuscript's encoded or polynomial selector universe, prove manuscript-level
faithfulness or compatibility, construct a realizer or route, derive the
grouped family, or establish polynomial bounds, ZeroSlack, PCCMin, SAT in P,
or the root theorem. See
`docs/lean_residual_terminal_packet_selector_universe.md`.

`lean/PNP/ResidualTerminalPacketSelectorHandles.lean` adds canonical finite
handles indexed by the exact input-relative grouped-footprint list. Its total
decoder is injective, every payload selector has a unique handle, and every
decoded footprint retains carrier containment, length at least two, and its
original grouped cell-and-atom evidence. The exhaustive Packet alternatives
remain unchanged. These list positions are not the manuscript's bit encoding
or a polynomial selector universe and do not prove manuscript-level
faithfulness or compatibility, construct a realizer or route, derive the
grouped family, establish polynomial bounds, ZeroSlack, PCCMin, SAT in P, or
the root theorem. See
`docs/lean_residual_terminal_packet_selector_handles.md`.

`lean/PNP/ResidualTerminalPacketSelectorCodec.lean` adds a canonical unary
bitstring for every input-relative handle and a total fail-closed decoder. It
proves exact round trip, encoding injectivity, canonical re-encoding after
successful decoding, exact and explicit-list-bounded length, unique accepted
codes for payload selectors, retained carrier/size/cell/atom evidence, and the
same pair, balanced-triple, and full-span alternatives. The bound is relative
to the supplied grouped-family list, not encoded circuit size. This does not
establish polynomial selector enumeration/runtime, atom or payload encoding,
manuscript-level faithfulness or compatibility, a realizer or route, family
derivation, ZeroSlack, PCCMin, SAT in P, or the root theorem. See
`docs/lean_residual_terminal_packet_selector_codec.md`.

`lean/PNP/ResidualTerminalPacketSelectorPayloadRealization.lean` maps each
accepted code through the total decoder to its exact source cell in the
explicit grouped BN6 family and the canonical first original positive payload
atom of that cell. Successful results recover the exact input code, retain
source membership and footprint equality, and preserve the pair,
balanced-triple, and full-span alternatives; rejection is exactly decoder
rejection. This is source-payload materialization, not the manuscript's gain-
or-blocker realizer. It does not serialize payload data, construct a replacement
circuit or route, prove faithfulness or compatibility, derive the family, or
establish encoded-size or polynomial-runtime bounds, ZeroSlack, PCCMin, SAT in
P, or the root theorem. See
`docs/lean_residual_terminal_packet_selector_payload_realization.md`.

`lean/PNP/ResidualBand.lean` factors locked-NAND threshold through residual-band exact minimization:

```lean
structure ResidualBandReductionTrust where
  lockedNANDReducesToResidualBand :
    ReducesToPoly LockedNANDThreshold ResidualBandExactMinimization
```

`lean/PNP/ZeroSlack.lean` exposes structured certificate boundaries for:

```text
HResolveSidecarCertificate
BudgetSidecarCertificate
SelectorHBZeroSlackSidecarCertificate
BCELContradictionCertificate
ZeroSlackCertificate
PCCOracleCertificate
```

`lean/PNP/ResidualTerminalHResolveCoverageLedger.lean` now supplies the first
typed executable refinement of that HResolve boundary. It generates
exact/gain/blocked/unresolved rows for every candidate in an arbitrary finite
supplied list, recomputes uniqueness, and accepts a NoHereditary sidecar only
when every listed candidate is positively blocked after both constructive
routes fail. This is coverage relative to supplied decidable predicates, not a
proof that the predicates implement HN grammar, BWL exactness, H-disjointness,
exact-minimum/gain semantics, blocker dependency semantics, or the full
historical HResolve theorem.

`lean/PNP/ResidualTerminalHResolveSupportResolver.lean` removes those two
supplied constructive inputs for the canonical terminal support branch. It
constructs every terminal support seed, proves the family duplicate-free,
derives saturation from the candidate model, and computes exact versus gain
from the extracted support's reference residual slack. Exact is reflected to
semantic minimality and gain to a strict equivalent witness. The subset
enumeration and reference minimum may be exponential, so this is not the HN
grammar or BWL algorithm, ParseOrExit, H-disjointness, NoHereditary blocker
semantics, or polynomial HResolve.

`lean/PNP/ResidualTerminalHResolveHDisjointFamily.lean` closes the bounded
family-assembly edge over supplied footprints. It computes exact
noninterference across all eight manuscript domains, selects a duplicate-free
maximal pairwise H-disjoint subfamily, and proves every rejected governed
candidate has a selected blocker with its first exact interference route. It
does not derive the footprints, prove HN grammar, BWL or ParseOrExit, build the
full `NoHereditary` sidecar, connect blockers to HB ranks, or complete full or
polynomial HResolve, ZeroSlack, or PCCMin.

`lean/PNP/ResidualTerminalHNBWLCertifiedPathMinimum.lean` closes the bounded
finite-minimum edge over a supplied nonempty certified path family. Each path
carries one of four HN shape tags, block coverage, complete direct-wire
semantic equivalence, and frontier fidelity. The computed objective derives
realization cost and compares residual rank, frontier deviation, and
direct-wire code in order. Lean proves the selected path is listed and no
governed alternative is smaller when supplied family completeness holds. This
does not derive or prove complete the accepted HN grammar, establish LN
confluence, ParseOrExit, leaf tightness, the full BWL theorem, polynomial
HResolve, ZeroSlack, or PCCMin.

`lean/PNP/ResidualTerminalHResolveCertifiedPathFamily.lean` composes those two
bounded kernels. Each supplied hereditary candidate carries its own expected
frontier, eight-domain footprint, nonempty finite certified-path family,
governed predicate, completeness proof, and path-to-footprint coherence.
The selector produces a duplicate-free maximal pairwise H-disjoint family.
Every retained candidate exposes an exact four-coordinate BWL minimum with
semantic, frontier, block, shape, and footprint evidence; every rejected
candidate exposes a selected blocker and exact first interference route. The
candidates remain supplied. This does not derive terminal candidates, HN
grammar completeness, LN confluence, ParseOrExit, leaf tightness, the H0-H4
sidecar, full or polynomial HResolve, ZeroSlack, or PCCMin.

`lean/PNP/ResidualTerminalHResolveZeroSlackSidecar.lean` upgrades the
report-facing ZeroSlack boundary itself. Its `HResolveSidecarCertificate`
stores the exact executable `NoHereditary` checker equation for an arbitrary
finite supplied governed family and semantic proofs for both exact-minimum and
strict-equivalent-gain routes; the former three HResolve string fields are no
longer accepted. Checker reflection yields duplicate-free total blocked
coverage and constructive-route exclusion. The family, implementation map,
predicates, decidability witnesses, and blocker semantics remain supplied.
This is not terminal candidate generation, H0-H4 blocker semantics, full or
polynomial HResolve, unconditional ZeroSlack, or PCCMin.

`lean/PNP/ResidualTerminalBudgetZeroSlackSidecar.lean` upgrades the matching
Budget boundary in the report-facing ZeroSlack record. Its
`BudgetSidecarCertificate` stores the actual equation showing that exhaustive
search over every canonical terminal support returned no feasible member;
the former `NoBudget`, exact-soundness, and gain-soundness strings are no longer
accepted. Reflection excludes the recomputed envelope predicate everywhere,
while existing residual-slack theorems give every explicit exact or gain route
its semantic minimum or strict equivalent gain meaning. The caps remain
supplied and the scan, saturation, and reference minimum may be exponential.
This is not the BUD grammar or B0--B4 sidecar, full or polynomial
BudgetResolve, unconditional ZeroSlack, or PCCMin.

`lean/PNP/ResidualTerminalSelectorHBZeroSlackSidecar.lean` upgrades the joint
selector/HB boundary in the report-facing ZeroSlack record. Its
`SelectorHBZeroSlackSidecarCertificate` stores the exact all-row
selector-silence and ranked no-outcome HB-closure equations instead of eight
strings. Existing reflection and strong finite-rank induction prove every
canonical selector nonfaithful, every realizer claim an exact typed bottom,
every supplied HN/BUD activity bit false, and the dependency relation well
founded. The grouped family, realizer and dependency tables, environment,
claims, activity bits, and rank map remain supplied. This is not terminal-data
construction, selector faithfulness or compatibility, blocker semantics,
semantic dependency completeness, unconditional ZeroSlack, or polynomial
PCCMin.

`lean/PNP/ResidualTerminalBudgetEnvelopeResolver.lean` adds the next finite BUD
edge. For supplied natural gate and saturated-record caps, it searches the
complete canonical terminal support universe, recomputes candidate-derived
saturation, requires a nonempty implementation and interface, and returns a
feasible semantic minimum, a feasible strict equivalent gain, or proof that no
canonical seed fits the caps. The caps are inputs and the support scan plus
reference minimization are exhaustive and may be exponential. This is not the
manuscript HN/BUD grammar, BWL, the budget-envelope dynamic program, blocker
semantics, polynomial `BudgetResolve`, complete no-lower, unconditional
`ZeroSlack`, or polynomial `PCCMin`.

`lean/PNP/ResidualTerminalBudgetNoLowerLedger.lean` extends that resolver from
one first-feasible result to an exhaustive route ledger. Every canonical seed
is classified as exact, strict gain, or outside the supplied envelope. The
no-lower Boolean accepts exactly when every budget-feasible governed seed is a
semantic minimum, so its endpoint excludes every feasible strict-equivalent
gain. Supplied caps, subset enumeration, saturation, and reference minimization
remain; this is an exponential finite reference boundary, not polynomial
`BudgetResolve`, Packet or complete no-lower composition, unconditional
`ZeroSlack`, or polynomial `PCCMin`.

`lean/PNP/ResidualTerminalPacketBudgetNoLowerComposition.lean` joins that
canonical budget ledger to the independently checked five-row Packet ledger
over the same direct-wire candidate. Its Boolean recomputes both components,
and acceptance proves every budget-feasible canonical support minimum,
excludes every feasible strict gain, and excludes a positive Packet for the
supplied family and tables. The caps, Packet data, ranks, claims, activity
environment, and dependency rows remain supplied. This is a finite two-branch
composition, not the complete no-lower ledger, a terminal construction of the
Packet inputs, unconditional `ZeroSlack`, or polynomial `PCCMin`.

`lean/PNP/ResidualTerminalPacketBudgetNoLowerZeroSlackSidecar.lean` upgrades
the matching report-facing ZeroSlack field from a no-lower string to the exact
same-candidate Packet/budget composition equation. Its proof-bearing
`PacketBudgetNoLowerZeroSlackSidecarCertificate` reflects acceptance, proves
every governed budget-feasible support semantically minimum, excludes every
such strict equivalent gain, and excludes a positive Packet conclusion for the
supplied family. The caps, candidate-derived model, grouped family, payloads,
ranks, claims, activity, dependencies, and rank maps remain supplied. This is
the existing finite two-branch boundary, not the complete manuscript no-lower
ledger, unconditional `ZeroSlack`, or polynomial `PCCMin`.

`lean/PNP/ResidualTerminalBCELPacketNoLowerZeroSlackSidecar.lean` upgrades the
remaining BCEL contradiction bundle from five strings to one dependent
proof-bearing boundary. Its type ties the exact M180 certificate to the same
grouped family, and its only stored equation checks that the carrier contains
at least two anchors. BCEL constant activation would construct a positive BN6
Packet by `terminalBN6_hypergraph_packet`; the accepted same-family no-lower
certificate excludes that Packet. The family and all M180 inputs remain
supplied. This does not derive BCELReady or constant activation from positive
residual slack, complete the no-lower ledger, establish unconditional
`ZeroSlack`, or prove polynomial `PCCMin`.

`lean/PNP/ResidualTerminalZeroSlackPacketSelectorHBCoherence.lean` closes
the same-family Selector/HB, Packet, and BCEL seam in the report-facing
certificate. It derives the Selector/HB sidecar from M180's exact grouped
family, computed realizer table, and dependency table, so selector silence, HB
closure, Packet exclusion, and the dependent M181 BCEL contradiction cannot be
assembled from detached inputs. The family and all terminal, budget, Packet,
realizer, dependency, rank, and BCEL inputs remain supplied. This does not
derive those inputs or constant activation from positive residual slack,
establish unconditional `ZeroSlack`, or prove polynomial `PCCMin`.

`lean/PNP/PCCMin.lean` exposes the structured loop certificate and constructs the witness-model residual-band decider from it.

Most fields in these certificate objects are still digest/ledger handles. Replacing those handles by actual propositions and proofs is a major remaining task.

## Final bridge

`lean/PNP/Bridge.lean` proves:

```lean
theorem final_report_bridge
    (T : CheckerTrustModel) :
    FinalReportAntecedent → FinalReportConsequent
```

where:

```text
FinalReportAntecedent = exists loop : PCCMinLoopCertificate,
  CheckPCCPackexp (GeneratePCCPack loop) = Verdict.accept
FinalReportConsequent = PClass = NPClass
```

The current route is:

```text
accepted PCC package
-> structured PCCMin/ZeroSlack certificate
-> residual-band exact minimization in P
-> locked NAND threshold in P
-> SAT in P
-> P = NP
```

M188 makes `PCCPack` a typed container for the exact explicit loop
certificate. `GeneratePCCPack` is a transparent constructor and
`CheckPCCPackexp` is a transparent canonical-identifier check. The current
compiled project-specific axiom inventory is therefore empty:

```text
[]
```

`lean-audit/PNPBridgeAxiomAudit.lean` confirms that the root-status declarations depend on no axioms
and prints the allowed Lean logical-infrastructure dependencies for the conditional bridge.
`lean-audit/PNPTypedPCCPackReflectionAxiomAudit.lean` separately pins generated
acceptance, exact certificate reflection, mismatched-identifier rejection, and
the active bridge closure. The source audit fails closed if another `axiom`, a `constant`/`opaque`
declaration, or a `sorry`/`admit` placeholder appears in the tracked root closure.

The remaining burden has not disappeared: `FinalReportAntecedent` requires an
explicit proof-bearing loop certificate to exist, and `CheckerTrustModel.satHard`
remains an explicit theorem premise. Packaging and structural acceptance do not
construct that certificate, prove unconditional ZeroSlack/PCCMin or polynomial
runtime, establish deterministic SAT in P, or prove `P = NP`.

M189 separately formalizes the general control flow that such a construction
would drive. `PCCMinTotalOracle` must return either a checked strict equivalent
gain, a checked exact minimum, or a checked ZeroSlack result for every current
implementation. `runPCCMinTotalOracleLoop` is transparent well-founded
recursion on residual slack, and its public endpoint returns semantic
equivalence, global minimality, exact reference gate count, zero slack, and the
strict-gain iteration bound. The oracle itself is not constructed or inferred
from `PCCPack`; no encoded-size polynomial bound follows. The bridge antecedent,
unconditional ZeroSlack, PCCMin construction, deterministic SAT theorem, and
root publication gate therefore remain open.

M190 now matches the manuscript's two-stage iteration more closely.
`PCCMinTotalNormalizer` may produce a checked direct gain or a semantically
equivalent non-increasing normal form. `composePCCMinNormalizerOracle` proves
that an oracle gain after normalization is still a strict gain from the
pre-normalized implementation and transports exact-minimum or ZeroSlack
endpoints back through that equivalence. The resulting route reuses the M189
well-founded loop and retains its exact result and iteration bound. Neither the
normalizer nor the oracle is constructed or inferred from `PCCPack`, and no
encoded-size polynomial bound follows. The bridge antecedent, unconditional
ZeroSlack, PCCMin construction, deterministic SAT theorem, and root publication
gate therefore remain open.

M191 opens the supplied oracle boundary into the manuscript's exact stage
order. `PCCMinRankOrderedOracleBuilder` provides a proof-bearing HResolve
outcome, makes BudgetResolve depend on the actual NoHereditary evidence, and
makes the selector plan depend on both negative resolver outcomes. The
selector runner scans arbitrary finite rows through the complete canonical
`allFin` rank list. It returns the first strict gain or retains a typed blocker
equation for every selector at every rank; only the latter ledger can be passed
to the explicit ZeroSlack closure. The adapter then reuses the M190
normalization composition and M189 recursive loop. The component builders,
blocker semantics, and ZeroSlack implication remain supplied, so this does not
construct PCCMin, prove unconditional ZeroSlack, or establish polynomial
runtime. See
[`lean_pccmin_rank_ordered_oracle.md`](./lean_pccmin_rank_ordered_oracle.md).

M192 narrows the M191 selector boundary to complete checked Packet data.
`TerminalPacketTypedRealizerTable.checkEveryClaim` validates a data-only claim
at every canonical handle. `selectorsAtRank` then derives each row from the
complete handle list and the table-owned finite rank rather than accepting a
caller-supplied row. An accepted gain blueprint reconstructs the existing
strict equivalent-gain theorem; accepted HN, budget, and lower-seed claims
become typed blockers. `PCCMinCheckedPacketRankOrderedOracleBuilder` converts
that checked interface to M191 and reuses the M190/M189 loop. The grouped
family, table, rank map, resolver algorithms, blocker meanings, and ZeroSlack
silence closure remain supplied, so this does not construct PCCMin, prove
unconditional ZeroSlack, or establish polynomial runtime. See
[`lean_pccmin_checked_packet_ranked_selector.md`](./lean_pccmin_checked_packet_ranked_selector.md).

The M193 checked Packet/HB bridge removes the remaining opaque
silence-to-ZeroSlack callback at this boundary. Complete checked claims and
all-rank blocked outcomes are reflected
into the executable selector-silence Boolean. Together with checked HB
no-outcome closure, the existing well-founded induction proves every canonical
handle nonfaithful. `PCCMinCheckedPacketHBZeroSlackData` retains one exact
load-bearing premise: positive residual slack supplies a faithful canonical
handle. Its contradiction yields conditional ZeroSlack and constructs the
M192 adapter before reusing the same rank scan and recursive loop. The fifteen
focused declarations use no project-specific axiom or `Classical.choice`.
Because the positive-slack bridge, terminal data, resolvers, normalizer, and
polynomial bounds remain supplied or open, this is not unconditional
ZeroSlack or polynomial PCCMin. The risk-weighted proof-completion estimate
therefore remains 35 percent and zero of five global gates are closed. See
[`lean_pccmin_checked_packet_hb_zeroslack_bridge.md`](./lean_pccmin_checked_packet_hb_zeroslack_bridge.md).

The M194 BN6 computed-faithfulness bridge replaces M193's arbitrary
positive-slack-to-faithful-selector premise. Positive slack now supplies only
the earlier constant-activation premise for an arbitrary finite grouped
family. The general BN6 theorem constructs the Packet conclusion; the
route-clear payload checker and canonical table constructor then compute a
faithful handle without an independent binding premise. The M193 checked HB
contradiction derives conditional ZeroSlack and feeds the same total loop. The
twelve focused declarations use no project-specific axiom or
`Classical.choice`. Because constant activation, terminal data, route-clear
evidence, resolvers, normalizer, and polynomial bounds remain supplied or open,
this is not manuscript-wide SaturatePositive or BCELReady, unconditional
ZeroSlack, or polynomial PCCMin. The risk-weighted proof-completion estimate
therefore remains 35 percent and zero of five global gates are closed. See
[`lean_pccmin_checked_packet_bn6_hb_zeroslack_bridge.md`](./lean_pccmin_checked_packet_bn6_hb_zeroslack_bridge.md).

The M195 same-candidate BCEL activation-route classifier removes M194's opaque
positive-slack-to-constant-activation callback from the new endpoint. It binds
the supplied Packet carrier to the computed checked BCEL-ready nucleus, checks
the exact cut value and every canonical nonempty proper-cut activation weight,
and returns one proof-bearing mismatch route or coherent evidence. Coherence
derives constant activation, identifies it with the BCEL projection excess,
and feeds M194's conditional ZeroSlack bridge. The fifteen focused declarations
use no project-specific axiom or `Classical.choice`. The terminal problem,
positive premise, ready certificate, family, tables, ranks, route-clear and HB
data, resolvers, normalizer, and polynomial bounds remain supplied or open.
Mismatch routes are not yet constructed gains or globally decreasing routes,
and the finite subset scan is not proved polynomial. This is not
manuscript-wide SaturatePositive or BCELReady, unconditional ZeroSlack, or
polynomial PCCMin. The risk-weighted proof-completion estimate therefore
remains 35 percent and zero of five global gates are closed. See
[`lean_pccmin_checked_packet_bn6_bcel_activation_route.md`](./lean_pccmin_checked_packet_bn6_bcel_activation_route.md).

The M196 BCEL-derived-family boundary removes M195's duplicate carrier and cut
value inputs. A grouped-cell ledger constructs the BN6 family over the exact
computed nucleus, while carrier uniqueness, the cut value, and its positivity
come from the checked BCEL result. This makes M195's carrier and cut-value
mismatch routes impossible by reduction. The new endpoint preserves only the
exact proper-cut activation mismatch or the conditional ZeroSlack branch. The
fourteen focused declarations use no project-specific axiom or
`Classical.choice`. The grouped cells, payloads, grouping proofs, tables,
ranks, route-clear and HB data, resolvers, normalizer, and polynomial bounds
remain supplied or open. The remaining mismatch is not a gain or decreasing
global route, and the inherited finite subset scan is not proved polynomial.
This does not complete PkgC/BN3--BN6 integration, prove manuscript-wide
SaturatePositive or BCELReady, establish unconditional ZeroSlack, or construct
polynomial PCCMin. The risk-weighted proof-completion estimate therefore
remains 35 percent and zero of five global gates are closed. See
[`lean_pccmin_checked_packet_bn6_bcel_derived_family.md`](./lean_pccmin_checked_packet_bn6_bcel_derived_family.md).

The M197 canonical-grouping boundary removes the supplied V54 consumer
systems, singletonization certificates, exact group-footprint-size proofs, and
duplicate-free grouping proof from M196. It normalizes every supplied raw
support inside the checked BCEL carrier, constructs the corresponding
singleton consumer system, coalesces duplicate footprints, and preserves every
positive payload atom in the canonical group ledger. The thirty-four focused
declarations use no project-specific axiom or `Classical.choice`. The raw
supports and payload atoms, terminal data, tables, ranks, route-clear and HB
data, resolvers, normalizer, and polynomial bounds remain supplied or open.
The remaining activation mismatch is not a gain or decreasing global route,
and the inherited finite subset scan is not proved polynomial. This does not
complete PkgC/BN3--BN6 integration, prove manuscript-wide SaturatePositive or
BCELReady, establish unconditional ZeroSlack, or construct polynomial PCCMin.
The risk-weighted proof-completion estimate therefore remains 35 percent and
zero of five global gates are closed. See
[`lean_pccmin_checked_packet_bn6_bcel_canonical_grouping.md`](./lean_pccmin_checked_packet_bn6_bcel_canonical_grouping.md).

The M198 canonical cut-ledger boundary proves that M197's coalescing operation
preserves the direct raw positive-cell crossing-mass sum on every finite cut.
The checked endpoint consequently exposes the remaining proper-cut BCEL
mismatch directly against that raw positive-cell cut ledger rather than only
against a derived grouped-family activation total. The nine focused
declarations use no project-specific axiom or `Classical.choice`; only permitted `propext` and
`Quot.sound` closure appears where required. Raw cells and payloads, terminal
construction, the constant-activation equation, tables, ranks, route-clear and
HB data, resolvers, normalizer, and polynomial bounds remain supplied or open.
The mismatch is not yet a strict gain or decreasing global route, and the
finite subset scan is not proved polynomial. This does not complete
PkgC/BN3--BN6 integration, prove manuscript-wide SaturatePositive or BCELReady,
establish unconditional ZeroSlack, or construct polynomial PCCMin. The
risk-weighted proof-completion estimate therefore remains 35 percent and zero
of five global gates are closed. See
[`lean_pccmin_checked_packet_bn6_bcel_canonical_cut_ledger.md`](./lean_pccmin_checked_packet_bn6_bcel_canonical_cut_ledger.md).

The M199 canonical constant-cut-basis boundary removes the all-proper-cut
powerset scan from the new checked endpoint. Lean proves, for every sparse V53
carrier with at least two anchors, that a fixed shape-specific basis is
equivalent to the complete proper-cut equation: one full-span weight at two
anchors, three singleton cuts at three anchors, and full-span-only support plus
its weight at four or more anchors. A total typed classifier either installs
the resulting constant activation in the existing Packet/BN6/BCEL/HB
conditional ZeroSlack boundary or returns one exact structural obstruction.
The twenty-two reviewed declarations use no project-specific axiom or
`Classical.choice`; only permitted `propext` and `Quot.sound` closure appears
where required. Raw cells and payloads, terminal construction, tables, ranks,
route-clear and HB data, resolvers, normalizer, and complete encoded-size
polynomial bounds remain supplied or open. A rejected basis is not a strict
gain or decreasing global route, and upstream construction may still enumerate
subsets. This does not complete PkgC/BN3--BN6 integration, prove
manuscript-wide SaturatePositive or BCELReady, establish unconditional
ZeroSlack, or construct polynomial PCCMin. The risk-weighted proof-completion
estimate therefore remains 35 percent and zero of five global gates are
closed. See
[`lean_pccmin_checked_packet_bn6_bcel_canonical_constant_cut_basis.md`](./lean_pccmin_checked_packet_bn6_bcel_canonical_constant_cut_basis.md).

The M200 sparse activation-route boundary replaces M199's structural-only
rejection with one exact small proper-cut mismatch. Lean proves that all
singleton and order-preserving pair cuts form a duplicate-free, quadratic-size
test family equivalent to the complete V53 proper-cut equation for every
finite carrier with at least two anchors. The total classifier either supplies
that equation to M199's checked conditional ZeroSlack branch or returns its
first mismatching cut, which is reflected through M198's direct raw positive-
cell ledger. The thirty reviewed declarations use no project-specific axiom or
`Classical.choice`. Raw cells and payloads, terminal construction, tables,
ranks, route-clear and HB data, gain and global rank-decrease semantics, and
the complete encoded-input polynomial construction remain supplied or open.
The local quadratic family-size theorem is not a complete PCCMin runtime bound.
The risk-weighted estimate remains 35 percent and zero of five global gates
are closed. See
[`lean_pccmin_checked_packet_bn6_bcel_sparse_activation_route.md`](./lean_pccmin_checked_packet_bn6_bcel_sparse_activation_route.md).

M201 now reconnects the manuscript's PkgC classification directly to raw BN6
positive cells over arbitrary finite supplied active V54 consumer systems. The
total recursive classifier returns an exact proof-bearing same-key
cancellation at the first nonsingletonized system; otherwise it derives every
BN6 support from the singleton consumer footprint, obtains the required
support cardinality from activity, preserves payload order, and conserves the
exact V54 activation ledger for every cut. All nineteen audited declarations
avoid project-specific axioms and `Classical.choice`. This is still a supplied-
data boundary: it does not construct the consumer systems, active cuts,
payloads, or restorer from a terminal candidate, turn cancellation into a
global decreasing route, complete PkgC/BN3--BN6, prove unconditional ZeroSlack,
or establish complete polynomial PCCMin. The risk-weighted estimate remains
35 percent and zero of five global gates are closed. See
[`lean_residual_terminal_pkgc_bn6_positive_cellization.md`](./lean_residual_terminal_pkgc_bn6_positive_cellization.md).

M202 now feeds M201's constructed BN6 cells into M200's canonical checked
Packet/HB boundary without a parallel raw-cell input. Its total source-level
classifier preserves exact PkgC cancellation evidence, returns genuine
conditional ZeroSlack on the checked coherent branch, or transports M200's
singleton/pair raw-cell mismatch through all-cut conservation to the original
PkgC source activation ledger. All seven audited declarations avoid
project-specific axioms and `Classical.choice`. The source systems, active
cuts, payloads, restorer, checked tables, ranks, dependency closure,
route-clear result, and selector silence remain supplied; neither returned
obstruction is yet a global decreasing gain. Complete PkgC/BN3--BN6,
unconditional ZeroSlack, and polynomial PCCMin remain open. The risk-weighted
estimate remains 35 percent and zero of five global gates are closed. See
[`lean_pccmin_checked_packet_pkgc_bn6_bcel_source_route.md`](./lean_pccmin_checked_packet_pkgc_bn6_bcel_source_route.md).

M203 computes the ambient BN4 consequence of M202's PkgC cancellation rather
than accepting a proposed remainder and permutation. Remove-first recursion is
order independent and multiplicity preserving: success returns the exact
remainder, permutation and complete residual-ledger equality, while failure
proves that no exact embedding exists. The same checked BCEL nucleus constructs
the BN4 kernel internally. All ten audited declarations avoid project-specific
axioms and `Classical.choice`. The ambient ledger, source systems, restorer,
payloads, downstream tables and selector silence remain supplied; the
remainder is not shown empty and neither branch is a global gain or rank
decrease. Complete PkgC/BN3--BN6, unconditional ZeroSlack and polynomial PCCMin
remain open. The risk-weighted estimate remains 35 percent and zero of five
global gates are closed. See
[`lean_pccmin_checked_packet_pkgc_ambient_bn4_extraction_route.md`](./lean_pccmin_checked_packet_pkgc_ambient_bn4_extraction_route.md).

M204 runs the finite restoration-coordinate classifier before ambient BN4
extraction. It preserves singletonization or the exact first Hall deficit
with its forced Q route. Complete coverage constructs one balanced
opposite-sign unit pair per quotient coordinate, then computes the exact
remainder and residual-ledger equality for every admissible ambient order or
proves no exact embedding. All 17 audited declarations avoid
project-specific axioms and Classical.choice. The restoration universe,
coordinate maps, consumer system and ambient ledger remain supplied;
coordinate coverage does not materialize semantic full candidates, and
neither Hall failure nor ambient incompatibility is a global decreasing
route. Complete PkgC/BN3--BN6, unconditional ZeroSlack and polynomial PCCMin
remain open. The risk-weighted estimate remains 35 percent and zero of five
global gates are closed. See
[lean_residual_terminal_pkgc_restoration_coverage_ambient_route.md](./lean_residual_terminal_pkgc_restoration_coverage_ambient_route.md).

M205 lifts that four-way exact result over the complete arbitrary-finite
active PkgC source ledger. Only an all-source singletonization proof constructs
the BN6 ledger; Lean then preserves source length, payload order, and activation
weight on every cut. Otherwise, the first source member carrying a Hall
deficit, computed ambient reduction, or no-embedding witness is retained.
All 11 audited declarations avoid project-specific axioms and
Classical.choice. The source cells and active cuts, payloads, restoration
universes and maps, and ambient ledgers remain supplied, so complete
PkgC/BN3--BN6, global route descent, unconditional ZeroSlack, and polynomial
PCCMin remain open. Formal artefact coverage is 181 of 183, the risk-weighted
estimate remains 35 percent, and zero of five global gates are closed. See
[lean_residual_terminal_pkgc_restoration_coverage_bn6_ledger.md](./lean_residual_terminal_pkgc_restoration_coverage_bn6_ledger.md).

M206 ties every M205 source and ambient activation atom to one computed BCEL
nucleus and enters the checked sparse BN6/BCEL route only after all source
systems singletonize. The first Hall deficit, ambient reduction, or
no-embedding witness remains exact; the downstream branch returns conditional
ZeroSlack or reflects one proper singleton/pair activation mismatch to the
original enriched source ledger. All four audited declarations avoid
project-specific axioms and Classical.choice. The terminal problem, source,
restoration, ambient, rank, claim, dependency, and selector data remain
supplied, so complete PkgC/BN3--BN6, global route descent, unconditional
ZeroSlack, and polynomial PCCMin remain open. Formal artefact coverage is 182
of 184, the risk-weighted estimate remains 35 percent, and zero of five global
gates are closed. See
[lean_pccmin_checked_packet_pkgc_restoration_coverage_bn6_bcel_route.md](./lean_pccmin_checked_packet_pkgc_restoration_coverage_bn6_bcel_route.md).

M207 computes a mass-sensitive unsigned BN4 charge measure over M206's exact
ambient embedding. The removed coverage subledger has positive charge, so the
computed remainder has strictly smaller charge while preserving the complete
canonical residual ledger. Installing those two computed values into the
eighth coordinate of `TerminalResidualRank` gives exact `LexLT` descent for
every fixed surrounding context. All 16 audited declarations avoid
project-specific axioms and Classical.choice. This closes only the successful
ambient branch: Hall, incompatibility, activation mismatch, terminal-data
construction, complete route coverage, unconditional ZeroSlack, and
polynomial PCCMin remain open. Formal artefact coverage is 183 of 185, the
risk-weighted estimate remains 35 percent, and zero of five global gates are
closed. See
[lean_pccmin_checked_packet_pkgc_restoration_coverage_charge_descent.md](./lean_pccmin_checked_packet_pkgc_restoration_coverage_charge_descent.md).

M208 replaces continued fixed-slot Cook-Levin control extension with one
all-input full-schedule controller. The verifier-derived polynomial body count
covers every clause-token opportunity plus final `Finish`; the semantic cursor
returns the complete canonical token schedule, while one deterministic finite
raw machine consumes that count and materializes the exact terminal coordinate
within an explicit polynomial bound. The loop does not yet decode or emit each
visited entry, so the complete builder, `RawRefinement`, and packaged reduction
remain open. Formal artefact coverage is 184 of 186, the risk-weighted estimate
remains 35 percent, and zero of five global gates are closed. See
[lean_cook_levin_builder_full_schedule_cursor_controller.md](./lean_cook_levin_builder_full_schedule_cursor_controller.md).

M209 adds the first uniform raw decoder branch above that controller. One fixed
54-rule comparator routes every arbitrary coordinate at the exact
problem-derived first-body boundary, agrees with the top-level direct-slot
semantics, rejects equality and later coordinates, and compiles within
`36 * terminalSlotPolynomial^2` for every in-range coordinate. One-step-short
fuel and malformed symbols remain timeout. It does not decode the post-header
quotient/remainder or emit a body token, so the complete builder,
`RawRefinement`, and packaged reduction remain open. Formal artefact coverage
is 185 of 187, the risk-weighted estimate remains 35 percent, and zero of five
global gates are closed. See
[lean_cook_levin_builder_arbitrary_slot_header_router.md](./lean_cook_levin_builder_arbitrary_slot_header_router.md).

M210 refines every natural post-header remainder through a structurally
recursive rectangle decoder. It returns the exact typed clause and
within-clause coordinate, the unique `Finish`, or the out-of-range suffix;
reconstructs each body coordinate; agrees with direct token lookup; and reads
the exact shifted remainder from M209's checked raw result configuration. It
does not implement raw division or raw body-token emission, so the complete raw
builder, `RawRefinement`, and packaged reduction remain open. Formal artefact
coverage is 186 of 188, the risk-weighted estimate remains 35 percent, and zero
of five global gates are closed. See
[lean_cook_levin_builder_arbitrary_slot_post_header_decoder.md](./lean_cook_levin_builder_arbitrary_slot_post_header_decoder.md).

M211 adds a fixed 99-rule raw divider for every natural post-header index and
positive unary width. It proves the exact natural quotient and strict
remainder tape, dividend reconstruction, exact six-step raw compilation,
one-step-short timeout, and a quadratic full-input bound. The M210 body route
instantiates the same decoded clause and within-clause coordinates. This is a
standalone arithmetic kernel: it is not spliced onto M209's checked raw result
and emits no token, so the complete builder, `RawRefinement`, and packaged
reduction remain open. Formal artefact coverage is 187 of 189, the
risk-weighted estimate remains 35 percent, and zero of five global gates are
closed. See
[lean_cook_levin_builder_post_header_raw_divider.md](./lean_cook_levin_builder_post_header_raw_divider.md).

M212 connects M209's checked raw remainder, M210's semantic route classifier,
and M211's exact divider through executable all-coordinate Lean orchestration.
Every natural coordinate derives its launch without a supplied route witness;
both exact traces remain visible; body, `Finish`, and out-of-range results are
recovered; and one verifier-derived source-size polynomial bounds the combined
compiled work. This constructs M211's canonical input from the checked value;
it is not a literal raw tape-to-tape rewrite, does not preserve the complete
builder workspace through such a bridge, and emits no token. Formal artefact
coverage is 188 of 190, the risk-weighted estimate remains 35 percent, and zero
of five global gates are closed. See
[lean_cook_levin_builder_post_header_raw_launch.md](./lean_cook_levin_builder_post_header_raw_launch.md).

M213 closes that physical boundary with one fixed 351-rule literal tape bridge
from both exact M209 post-header terminal layouts into a shielded M211 input.
It copies the derived remainder and positive problem width, preserves arbitrary
exterior builder workspace, retains the exact bridge and divider traces,
decodes the final quotient and remainder, compiles at six raw steps per work
step, times out one step short, and fits one verifier-derived source-size
polynomial for every in-range coordinate. It emits no selected body or
`Finish` token and does not iterate the complete schedule. Formal artefact
coverage is 189 of 191, the risk-weighted estimate remains 35 percent, and zero
of five global gates are closed. See
[lean_cook_levin_builder_post_header_raw_tape_bridge.md](./lean_cook_levin_builder_post_header_raw_tape_bridge.md).

M214 continues from that exact divider tape with one fixed 180-rule literal
post-divider classifier. It copies the problem-derived clause count from a
restored workspace sidecar, preserves the full exterior and remainder ledger,
and exposes the quotient to a shielded M209 comparator. Exact bridge and
comparator traces compile at six raw steps per work step, time out one step
short, agree with every in-range M210 body or unique `Finish` route, and fit
one verifier-derived source-size polynomial. It still does not inspect, select,
emit, or append the corresponding token or iterate the complete schedule, so
the complete raw builder, `RawRefinement`, and packaged reduction remain
open. Formal artefact coverage is 190 of 192, the risk-weighted estimate
remains 35 percent, and zero of five global gates are closed. See
[lean_cook_levin_builder_post_divider_raw_route_classifier.md](./lean_cook_levin_builder_post_divider_raw_route_classifier.md).

M215 derives every post-header padding, body-token, or unique `Finish` entry
from the canonical schedule without a supplied route or token. It retains
M214's physical classifier contract for arbitrary workspace, leaves the
canonical emitted prefix unchanged at padding, and runs the existing fixed
59-rule appender for every populated coordinate to reach exactly the next
emitted prefix. Exact work and six-for-one compiled traces, one-step-short
nonhalting, and the combined staged source-size polynomial are all checked.
The selection handoff is still executable Lean orchestration rather than one
literal raw selector, and the schedule is not iterated, so the complete raw
builder, `RawRefinement`, and packaged reduction remain open. Formal artefact
coverage is 191 of 193, the risk-weighted estimate remains 35 percent, and
zero of five global gates are closed. See
[lean_cook_levin_builder_post_divider_selected_token_launch.md](./lean_cook_levin_builder_post_divider_selected_token_launch.md).

## Discharged by Lean so far

```text
1. P is a subset of NP in the finite charged-pipeline model.
2. Polynomial reductions transport P membership in that concrete model.
3. An NP-complete language in P implies P = NP in that concrete model.
4. Report-facing compatibility names reuse those same concrete interfaces rather
   than parallel closure fields or string handles.
5. Identity and composition of polynomial reductions, including polynomial substitution and
   intermediate-output handoff cost.
6. SAT-in-NP plus SAT hardness gives SAT NP-completeness in the legacy witness layer.
7. The displayed local locked-NAND macro Boolean identities.
8. Single-instance macro output distinctness and nonconstant/nonprojection checks.
9. The two-gate prefix conjunction semantics.
10. Exact supplied-list prefix coverage and the true-iff-all-checks theorem.
11. The exact 2(n-1) prefix gate count for nonempty check lists.
12. Prefix-node exposed-output distinctness and nonconstant/nonprojection checks.
13. Conditional composition from PCCMin through the concrete residual-band and
    locked-NAND endpoints, SAT, and the concrete equality proposition, assuming
    the two disclosed project axioms.
14. Typed direct-wire realizations of all six local locked-NAND gadgets, with honest output widths and constant-free internal syntax.
15. The semantic direct-wire lower bound `outputs ≤ gates` and conditional exactness for square baseline candidates.
16. Source-derived locked-baseline occurrence, check, prefix, and displayed-gate accounting.
17. Finite baseline conditions and exact reference minima for the five square local macros, excluding the one-output final conjunction.
18. The conditional locked-NAND unsat/sat minimum boundary and residual-slack-at-most-four deduction from six explicit typed semantic premises.
19. Canonical concrete CNF and bounded-assignment semantics, including Boolean-checker correctness.
20. Universal accept/reject/no-timeout correctness and an explicit polynomial bound for a finite
    raw machine on every paired CNF input/certificate, yielding `CNFSAT ∈ NP`.
21. Injective work-machine state renaming, three disjoint stage images, lookup-isolated finite
    rule-table concatenation, and exact stage-local trace transport for the framer, simulator, and
    internal handoff.
22. Exact framer-to-simulator and accept/reject-to-verdict-indexed-handoff launches, first-match
    bridge isolation, cumulative internal work cost, six-for-one compiled raw cost from canonical
    paired input, and accept/reject/timeout preservation for supplied exact target traces.
23. A literal 228-state, 2,052-rule strict-v0 locked-NAND source parser with constructive exact
    decoder-failure normal forms, all-input exact accept/reject behavior, valid-byte preservation,
    invalid-byte erasure, compiled non-timeout within `6 * 4096 * (n + 1)^3`, polynomial
    machine/function witnesses, and an exact leaf raw-machine refinement.
24. A literal 1,387,921-rule grammar-only locked-NAND target emitter with internally constructed
    all-input exact traces, exact target bytes, explicit runtime and output-size polynomials,
    compiled non-timeout, polynomial machine/function witnesses, leaf raw refinement, and strict
    parser/emitter composition with recursive raw refinement.
25. A concrete strict-v0 polynomial many-one reduction from `EncodedNANDSAT` to
    `EncodedLockedNANDThreshold`, with exact composed-function identity, exact output,
    all-bitstring language equivalence, a `ReducesTo` witness, and recursive raw refinement.
26. A universal answer-independent semantic compiler from strict canonical CNF to
    intrinsically topological NAND circuits, with exact edge semantics, exact gate count,
    a quadratic serialized-output bound, all-bitstring fail-closed language equivalence,
    and semantic composition with the concrete locked-NAND threshold builder.
27. A fixed 135,070-rule three-node all-input implementation of that compiler, with exact
    output on every bitstring, one external polynomial bound, compiled non-timeout,
    `PolynomialTimeFunction`, literal `RawRefinement`, a direct reduction from `CNFSAT` to
    `EncodedNANDSAT`, and explicit composition to `EncodedLockedNANDThreshold`.
28. Exact report-facing identities for concrete CNFSAT and encoded locked-NAND,
    direct reuse of the compiled NP verifier and all-bitstring reduction, removal
    of the duplicate locked-NAND project axiom, and a three-field checker trust boundary.
```

## Explicit trust base after this pass

```text
1. Checker/reflection soundness: accepted PCCPack emits a semantically valid structured PCCMin loop certificate.
2. Semantic adequacy of the PCCMin and ZeroSlack certificate fields.
3. The locked-NAND-to-residual-band reduction theorem.
4. A deterministic polynomial-time decider proving `CNFSAT ∈ P`, together with concrete SAT
   NP-hardness/NP-completeness; the current direct verifier proves only `CNFSAT ∈ NP`.
```

## Next formalization targets

The highest-value next targets are:

```text
1. Construct the locked-NAND-to-residual-band route and deterministic target decider without adding an assumption.
2. Implement M215's remaining literal raw selector/workspace handoff, iterate it across the complete schedule, and then package the complete Cook--Levin polynomial reduction.
3. Replace the remaining supplied ZeroSlack objects with terminal-derived propositions and prove the contradiction chain.
4. Formalize concrete SAT NP-hardness, without treating the `CNFSAT ∈ NP` verifier as
   a deterministic decider.
5. Formalize checker/reflection soundness for the PCC package.
```

A passing Lean build is a real checked artifact. At this stage it checks an assumption-free status
declaration, the direct theorem `CNFSAT ∈ NP`, other local results, and an explicitly
assumption-bearing conditional bridge. It is not a root theorem or an independent Lean proof of the
report's conclusion.

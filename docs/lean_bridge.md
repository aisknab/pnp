# Lean bridge formalization

This directory contains the Lean formalization track for the PNP proof-certificate stack.

The current Lean development contains a conditional theorem bridge corresponding to the report:

```text
CheckPCCPackexp(GeneratePCCPack()) = accept => P = NP
```

That bridge still depends on four project-specific axioms and does **not** constitute a Lean proof of
`P = NP`. It is also not a complete Lean reproof of the custom JavaScript checker, the full
residual-slack package, the complete SAT reduction, or the compiler/refinement connecting the new
finite charged-pipeline complexity interface to the raw machine kernel. The purpose of the Lean
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
lean-audit/PNPLockedNANDDirectAxiomAudit.lean
lean-audit/PNPDirectWireBaselineAxiomAudit.lean
lean-audit/PNPLockedNANDBaselineAxiomAudit.lean
lean-audit/PNPLockedNANDLocalBaselineAxiomAudit.lean
lean-audit/PNPLockedNANDThresholdBoundaryAxiomAudit.lean
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
docs/lean_nand_enumerator.md
docs/lean_locked_nand_macros.md
docs/lean_locked_nand_prefix.md
docs/lean_locked_nand_baseline.md
docs/lean_locked_nand_threshold_boundary.md
docs/lean_residual_routes.md
docs/lean_theorem_inventory.md
```

## Concrete machine foundation, charged complexity interface, and legacy bridge

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
successor declaration has empty axiom closure. This wraps an already-raw proof-bearing target; it
does not construct recursive composition/precomposition pipeline refinement. The two declarations in
`lean/PNP/Concrete/Target.lean` are also axiom-free: `PNP.Main.ConcretePEqualsNP` is an inactive
definition naming mutual inclusion, and `PNP.Main.concretePEqualsNP_iff` pins its expansion. This
does not prove the target. The six explicit declarations in
`lean/PNP/Concrete/PipelineRefinement.lean` are axiom-free. They
pin exact raw-machine refinement obligations, prove the raw function/decision leaf cases, transport
a function output-size bound, and convert a decider to a raw-machine witness only from a supplied
complete-program refinement. They do not build that refinement for composition or precomposition.

The 26 declarations in `PipelineSequentialStateNamespace.lean` are also axiom-free. They rename
two complete component tables into disjoint outer state images, isolate first-match lookup for both
images, transport exact local steps and runs, and provide literal accept/reject launches from the
first component to the second simulator. The 31 public declarations in
`PipelineSequentialCompiler.lean` then prove the complete all-input run in the literal combined
table. Either first verdict continues on the represented first output; the second verdict and
ordinary raw output are exact, stuck first endpoints remain timeout, and the external bound is
`PipelineRaw(p)(m) + 6 + PipelineRaw(q)(m + p(m) + 1)`. Their compiled axiom closures are empty.
The charged function/decision program syntax still lacks recursive composition and precomposition
`RawRefinement` constructors, so `Formal.ConcreteComplexityMachineLink` remains blocked. See
[`lean_concrete_complexity.md`](./lean_concrete_complexity.md) and
[`lean_pipeline_compiler.md`](./lean_pipeline_compiler.md), and
[`lean_pipeline_sequential_compiler.md`](./lean_pipeline_sequential_compiler.md).

### Direct concrete CNF verifier

The concrete CNF path is a closed raw-machine instance rather than an invocation of the still-
missing general pipeline compiler. `lean/PNP/Concrete/CNF.lean` defines canonical encodings for
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
polynomial-time SAT algorithm, establish NP-hardness or NP-completeness, connect the legacy
string-handle `PNP.SAT` label to `PNP.Concrete.CNFSAT`, or prove `P = NP`.

`lean/PNP/Complexity.lean` defines the witness-level objects:

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

These legacy witness objects still use abstract code handles and are not connected to the new
machine kernel or charged interface. They remain publication-ineligible historical bridge
objects. The finite `PNP.Concrete.*` definitions above, rather than abstract `PNP.PEqualsNP`, are
the current concrete target vocabulary.

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
unset fingerprints do not match and cannot activate the gate. Raw-machine linkage is still
ineligible for the general charged-pipeline target, even though the direct CNF verifier is linked
to one raw machine. The abstract `PNP.PEqualsNP` bridge remains ineligible. See
[`lean_theorem_inventory.md`](./lean_theorem_inventory.md) for the full contract and commands.

The inventory and false gate generate the current root TeX/PDF: a concise nine-page
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

The package is not constructed here. Its `satisfiable` parameter is an arbitrary proposition and
its `baseline` parameter an arbitrary natural number; neither is identified with circuit SAT or
`lockedBaselineCount`. Global carrier layout, cross-instance `BaselineDistinct`/`MacroDistinct`,
`TraceEquivalence`, derived unsatisfiable and satisfiable final-output laws,
`FinalLockSeparation`, an answer-independent uniform polynomial builder, and connection to
`PNP.LockedNANDThreshold` remain absent. See `docs/lean_locked_nand_threshold_boundary.md` for the
exact premise and hostile-review inventories.

## Global locked-NAND layer

`lean/PNP/LockedNAND.lean` keeps the full SAT builder and threshold theorem abstract:

```lean
axiom LockedNANDThreshold : Language

structure LockedNANDReductionTrust where
  satReducesToLockedNAND : ReducesToPoly SAT LockedNANDThreshold
```

The local macro truth laws, supplied-list prefix exactness, typed local candidates, source-derived
accounting, semantic output lower bound, five local square minima, and deductions from the
six-field conditional boundary package are no longer part of that trust object. Remaining global
work includes instantiating that package with the exact global distinguished-check list and
candidates, carrier freshness, cross-instance separation, trace equivalence, derived final-output
laws, the uniform polynomial builder, and the report threshold/unconditional slack theorem.

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
SelectorSilenceCertificate
HBClosureCertificate
BCELContradictionCertificate
ZeroSlackCertificate
PCCOracleCertificate
```

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
FinalReportAntecedent = CheckPCCPackexp GeneratePCCPack = Verdict.accept
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

The source audit permits exactly these four project-specific axioms in the current root closure:

```text
PNP.LockedNANDThreshold
PNP.ResidualBandExactMinimization
PNP.GeneratePCCPack
PNP.CheckPCCPackexp
```

`lean-audit/PNPBridgeAxiomAudit.lean` confirms that the root-status declarations depend on no axioms
and prints those project assumptions (along with Lean's logical infrastructure dependencies) for
the conditional bridge. The audit fails closed if another `axiom`, a `constant`/`opaque`
declaration, or a `sorry`/`admit` placeholder appears in the tracked root closure.

## Discharged by Lean so far

```text
1. P is a subset of NP in the witness model.
2. Polynomial reductions transport P membership in the witness model.
3. An NP-complete language in P implies P = NP.
4. The same three closure results for the finite charged-pipeline model, with concrete program
   construction rather than closure fields.
5. Identity and composition of polynomial reductions, including polynomial substitution and
   intermediate-output handoff cost.
6. SAT-in-NP plus SAT hardness gives SAT NP-completeness in the legacy witness layer.
7. The displayed local locked-NAND macro Boolean identities.
8. Single-instance macro output distinctness and nonconstant/nonprojection checks.
9. The two-gate prefix conjunction semantics.
10. Exact supplied-list prefix coverage and the true-iff-all-checks theorem.
11. The exact 2(n-1) prefix gate count for nonempty check lists.
12. Prefix-node exposed-output distinctness and nonconstant/nonprojection checks.
13. Conditional composition from PCCMin through residual band, locked NAND, SAT, and the witness-model equality proposition, assuming the disclosed project axioms.
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
```

## Explicit trust base after this pass

```text
1. Checker/reflection soundness: accepted PCCPack emits a semantically valid structured PCCMin loop certificate.
2. Semantic adequacy of the PCCMin and ZeroSlack certificate fields.
3. The locked-NAND-to-residual-band reduction theorem.
4. The global SAT-to-locked-NAND builder and threshold theorem beyond the checked local macro and prefix semantics.
5. A deterministic polynomial-time decider proving `CNFSAT ∈ P`, together with concrete SAT
   NP-hardness/NP-completeness; the current direct verifier proves only `CNFSAT ∈ NP`.
6. A compiler/refinement proving that every finite charged function, decision, and verifier
   pipeline is implemented with the stated input-size costs by the selected raw machine model. The
   exact terminal bridge still does not provide this result because its complete trace requires a
   caller-supplied exact target execution; target termination, external-input-size bounds, and the
   complete refinement contract remain unproved.
```

## Next formalization targets

The highest-value next targets are:

```text
1. Construct the exact global distinguished-check list, baseline candidate, and full candidate.
2. Formalize carrier layout, cross-instance locked-NAND freshness, and baseline distinctness.
3. Prove first-output preservation, `TraceEquivalence`, and the two derived final-output laws.
4. Instantiate the conditional boundary uniformly and prove the report threshold theorem.
5. Replace key ZeroSlack string handles with propositions and prove the contradiction chain.
6. Transport the exact framer/simulator/handoff trace into `terminalBridgeMachine`, then turn the
   proved four-stage trace into one full pipeline refinement with external-input-size polynomial
   runtime/output bounds.
7. Formalize or import concrete SAT NP-hardness, without treating the `CNFSAT ∈ NP` verifier as
   a deterministic decider.
8. Formalize checker/reflection soundness for the PCC package.
```

A passing Lean build is a real checked artifact. At this stage it checks an assumption-free status
declaration, the direct theorem `CNFSAT ∈ NP`, other local results, and an explicitly
assumption-bearing conditional bridge. It is not a root theorem or an independent Lean proof of the
report's conclusion.

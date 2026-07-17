#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import {
  ComputeLeanSourceClosureSha2560,
  DeriveFormalPublication0,
  FORMAL_PUBLICATION_MAP_PATH0,
  LEAN_INVENTORY_PATH0,
  LEAN_INVENTORY_PUBLIC_PATH0,
} from './formal-publication0.mjs';

const CHECKER = 'CheckFormalReconstructionStatus0';
const VERSION = 0;
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-17-48';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const SITE_PATH = 'public/pnp-status.json';
const OUTPUT_PATH = 'artifacts/formal-reconstruction-status/latest-verdict.json';

export const FORMAL_RECONSTRUCTION_BLOCKERS0 = Object.freeze([
  'Formal.ConcreteSAT',
  'Formal.LockedNANDThreshold',
  'Formal.ResidualBandMinimizer',
  'Formal.ZeroSlack',
  'Formal.PolynomialRuntimeAndCertificateBounds',
  'Formal.RootTheoremAndAxiomAudit',
]);

const PROJECT_SPECIFIC_AXIOM_INVENTORY = Object.freeze([
  'PNP.CheckPCCPackexp',
  'PNP.GeneratePCCPack',
  'PNP.LockedNANDThreshold',
  'PNP.ResidualBandExactMinimization',
]);

const LOCKED_NAND_THRESHOLD_HOSTILE_REVIEW_LEMMA_INVENTORY = Object.freeze([
  'DirectWireOutputLowerBound',
  'MacroDistinct',
  'TraceEquivalence',
  'ZeroOutputConvention',
  'FinalLockSeparation',
]);

const LOCKED_NAND_THRESHOLD_PREMISE_INVENTORY = Object.freeze([
  'baselineCandidate',
  'fullCandidate',
  'baselineConditions',
  'initialOutputsPreserved',
  'unsatisfiableFinalZero',
  'satisfiableFinalConditions',
]);

const LOCKED_NAND_THRESHOLD_MISSING_INSTANTIATION_INVENTORY =
  LOCKED_NAND_THRESHOLD_PREMISE_INVENTORY;

const VERIFICATION_COMMANDS = Object.freeze([
  'node pcc-formal-reconstruction-status0.mjs --json',
  'node pcc-formal-public-surface0.mjs --json',
  'npm run legacy:v0:check',
  'npm run pnp:verify -- --no-write',
  'node --test audits/lean-root-target0.test.mjs',
  'node --test audits/lean-concrete-machine0.test.mjs',
  'node --test audits/lean-concrete-tape-handoff0.test.mjs',
  'node --test audits/lean-concrete-tape-blank-equivalence0.test.mjs',
  'node --test audits/lean-concrete-pipeline-tape-geometry0.test.mjs',
  'node --test audits/lean-concrete-pipeline-input-framer0.test.mjs',
  'node --test audits/lean-concrete-pipeline-output-handoff0.test.mjs',
  'node --test audits/lean-concrete-pipeline-state-namespace0.test.mjs',
  'node --test audits/lean-concrete-pipeline-sequential-state-namespace0.test.mjs',
  'node --test audits/lean-concrete-pipeline-sequential-compiler0.test.mjs',
  'node --test audits/lean-concrete-pipeline-stage-bridges0.test.mjs',
  'node --test audits/lean-concrete-terminal-output-packer0.test.mjs',
  'node --test audits/lean-concrete-pipeline-terminal-bridge0.test.mjs',
  'node --test audits/lean-concrete-pipeline-paired-compiler0.test.mjs',
  'node --test audits/lean-concrete-pipeline-compiler0.test.mjs',
  'node --test audits/lean-concrete-pipeline-machine-simulation0.test.mjs',
  'node --test audits/lean-concrete-complexity0.test.mjs',
  'node --test audits/lean-concrete-pipeline-refinement0.test.mjs',
  'node --test audits/lean-concrete-cnf0.test.mjs',
  'node --test audits/lean-concrete-cook-levin-raw-tape-bridge0.test.mjs',
  'node --test audits/lean-concrete-cook-levin-formula-size0.test.mjs',
  'node --test audits/lean-concrete-cook-levin-formula-schedule0.test.mjs',
  'node --test audits/lean-concrete-cook-levin-formula-cursor0.test.mjs',
  'node --test audits/lean-concrete-cook-levin-builder-input-length0.test.mjs',
  'node --test audits/lean-concrete-cook-levin-builder-input-prefix0.test.mjs',
  'node --test audits/lean-concrete-cook-levin-builder-token-appender0.test.mjs',
  'node --test audits/lean-concrete-cook-levin-builder-first-token-prefix0.test.mjs',
  'node --test audits/lean-concrete-cook-levin-builder-complete-header0.test.mjs',
  'node --test audits/lean-concrete-cook-levin-builder-body-start-prefix0.test.mjs',
  'node --test audits/lean-nand-semantics0.test.mjs',
  'node --test audits/lean-nand-enumerator0.test.mjs',
  'node --test audits/lean-nand-reference-minimum0.test.mjs',
  'node --test audits/lean-locked-nand-baseline0.test.mjs',
  'node --test audits/lean-locked-nand-threshold-boundary0.test.mjs',
  'node --test audits/lean-residual-routes0.test.mjs',
  'lake build PNP',
  'lake env lean -DwarningAsError=true lean-audit/PNPBridgeAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteBitStringAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteMachineAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteTapeHandoffAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteTapeBlankEquivalenceAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteTapeBlankEquivalence.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineTapeGeometryAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineInputFramerAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineOutputHandoffAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineStateNamespaceAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineSequentialStateNamespaceAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineSequentialCompilerAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcretePipelineSequentialCompiler.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineStageBridgesAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteTerminalOutputPackerAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineTerminalBridgeAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelinePairedCompilerAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcretePipelinePairedCompiler.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineCompilerAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcretePipelineCompiler.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineMachineSimulationAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteComplexityAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineRefinementAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcretePipelineRefinementRecursive.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteTargetAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCNFAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCNFWorkInputAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCNFVerifierAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCNFWorkAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinRawTapeBridgeAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinFormulaSizeAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinFormulaSize.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinFormulaScheduleAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinFormulaSchedule.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinFormulaCursorAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinFormulaCursor.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderInputLengthAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderInputLength.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderInputPrefixAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderInputPrefix.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderTokenAppenderAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderTokenAppender.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderFirstTokenPrefixAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderFirstTokenPrefix.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderUnaryPolynomialAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderCompleteHeaderAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderCompleteHeader.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderBodyStartPrefixAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderBodyStartPrefix.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCNFWorkCanonical.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteWorkCompilerEdges.lean',
  'lake env lean -DwarningAsError=true --run lean-regression/PNPConcreteCNFWorkCanonicalExtended.lean',
  'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCNFWorkExhaustive.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPNANDSemanticsAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPNANDEnumeratorAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPNANDTruthTableAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPNANDMinimumAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPNANDCompositionAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPNANDSlackAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDDirectAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPDirectWireBaselineAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDBaselineAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDLocalBaselineAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDThresholdBoundaryAxiomAudit.lean',
  'lake env lean -DwarningAsError=true lean-audit/PNPResidualRoutesAxiomAudit.lean',
  'node scripts/export-lean-theorem-inventory.mjs --check',
  'node scripts/generate-formal-publication.mjs --check',
  'node --test audits/lean-theorem-inventory0.test.mjs audits/formal-publication0.test.mjs',
  'npm run report:check',
]);

const NON_CLAIMS = Object.freeze([
  'The repository does not currently establish P = NP.',
  'Legacy JavaScript checker acceptance verifies assertion-bearing records under implemented predicates; it is not a formal proof of the named mathematical propositions.',
  'The current Lean bridge is partial and does not contain the required concrete, assumption-audited root theorem.',
  'The pinned Lean library/root-status build is reconstruction data, not a proof of P = NP.',
  'Blank-delimited Tape.outputBits removes dependence on the unobservable represented-list boundary; Tape.handoffTarget itself is a pure canonical specification. PipelineOutputHandoff is a separate executable internal represented handoff, not terminal raw output normalization.',
  'TapeBlankEquivalence proves that finite tapes which differ only by materialized exterior blanks have identical raw execution and observable output. PipelineCompiler uses that relation to connect every ordinary empty, odd, or even raw startConfig to the same literal four-stage work pipeline.',
  'PipelineTape frames raw cells between distinct two-track markers and tolerates arbitrary exterior garbage; its boundary expansions are pure tape identities, not transition rules, a handoff machine, a compiler, or a runtime proof.',
  'PipelineInputFramer is one literal finite machine for every raw bitstring. It handles the empty word, complete two-bit work cells, and an odd final raw bit through explicit finite transitions; reaches an accepting represented frame with permitted exterior garbage at exact branch costs; and from ordinary startConfig accepts without timeout within 6 * m * m + 39 * m + 75 raw steps. All 70 public declarations have empty axiom closure. PipelineCompiler and PipelineRefinement now transport that endpoint through complete recursive raw refinement, but CNF-SAT in P, NP-completeness, and P = NP remain absent.',
  'PipelineOutputHandoff is one literal finite machine for an already represented internal tape. For logical output length n it reaches an accepting representation of Tape.handoffTarget in exactly 2 * n + 4 work steps and 12 * n + 24 compiled steps. PipelineTerminalBridge preserves the earlier ordinary-input trace in its extended rule table and composes it with verdict-indexed terminal-packer copies for every supplied exact target execution. This still supplies no target-termination theorem, complete external-input-size polynomial, or RawRefinement. CNF-SAT in P, NP-completeness, and P = NP remain unproved.',
  'PipelineMachineSimulation extracts from every at-most raw run with fuel F an exact successful prefix of length k at most F reaching the same endpoint, and each supplied exact n-step run costs exactly 3 * n work transitions. PipelineCompiler extracts that prefix internally on every raw bitstring, bounds target output by m + F + 1, composes all four executable stages in one literal raw machine, and proves exact verdict, no-timeout, and machineOutput equality at an explicit polynomial in external length m. PipelineRefinement now recursively composes those raw implementations; CNF-SAT in P, NP-completeness, and P = NP remain missing.',
  'PipelineStateNamespace remains the injective renaming and lookup-isolation prerequisite. PipelineTerminalBridge now proves that every successful earlier bridge step and exact trace is preserved without shadowing, then composes accepting and rejecting supplied traces through two disjoint packer copies. Target termination, an external-input-size polynomial, and pipeline RawRefinement remain missing.',
  'PipelineSequentialStateNamespace nests two complete component machines in disjoint outer state images and supplies literal accept/reject launches from the first component into the second simulator. PipelineSequentialCompiler composes both exact executions in that one finite table for every raw input, passes either first verdict onward, preserves the second verdict and ordinary output, retains stuck-first timeout, and proves the external polynomial R(m) = PipelineRaw(p)(m) + 6 + PipelineRaw(q)(m + p(m) + 1). PipelineRefinement recursively applies that compiler to function composition and decision precomposition, closing the concrete machine-link blocker. CNF-SAT in P, NP-completeness, and P = NP remain absent.',
  'PipelineStageBridges proves exact framer-to-simulator and accept/reject-to-handoff launches, collision-free first-match dispatch, exact cumulative work cost, six-for-one compiled raw cost, and accept/reject/timeout classification for supplied exact target traces. PipelineTerminalBridge transports those traces into the extended machine and composes the terminal suffix, with exact ordinary machineOutput and the local 18*n^2 + 36*n + 12 suffix bound. This module alone does not prove target termination or an external-input-size polynomial; downstream modules now supply both and recursive RawRefinement. CNF-SAT in P, NP-completeness, and P = NP remain absent.',
  'TerminalOutputPacker is a literal finite work machine that uniformly packs empty, one-bit, odd, even, all-zero, all-one, and mixed logical outputs in the presence of arbitrary exterior garbage. It proves exact work execution, a designated halt, ordinary blank-delimited raw output equality, exact six-for-one compilation, the local raw bound 18*n^2 + 36*n + 6, and one-step-short timeout, all with empty axiom closure. Downstream modules connect it to target termination, an external encoded-input-size polynomial, and recursive RawRefinement. CNF-SAT in P, NP-completeness, and P = NP remain absent.',
  'PipelineTerminalBridge is one literal extended finite work machine containing the earlier bridge rules and two disjoint terminal-packer copies. PipelineCompiler transports every raw input through that table, supplies target termination from PolynomialTimeMachine.haltsWithin, preserves exact verdict and ordinary machineOutput, and retains stuck-endpoint timeout. PipelineRefinement now supplies the recursive FunctionProgram and DecisionProgram RawRefinement constructors.',
  'PipelinePairedCompiler remains the sharper canonical-pair theorem and compiles the same four-stage work table. PipelineCompiler is its all-input successor: all 29 public declarations have empty axiom closure, and pipeline_boundedDecide_eq, pipeline_machineOutput_eq, pipeline_ne_timeout, and pipeline_accepts_iff quantify every raw BitString. The output polynomial is B(m) = m + p(m) + 1; the runtime polynomial adds 6*m*m + 39*m + 75, two six-step launches, 18*p(m), and output-bound substitutions into the handoff and terminal-packer polynomials. PipelineRefinement recursively compiles composite charged programs to one raw machine; there is still no CNF-SAT in P, NP-completeness, or P = NP claim.',
  'The concrete bitstring, natural-polynomial, and finite-rule machine kernel is consumed by a finite charged-pipeline P/NP/reduction interface, and every finite function/decision program tree now has a literal raw-machine refinement with a recursively generated polynomial bound. This closes only the concrete machine link.',
  'The concrete complexity interface proves P subset NP, reduction composition and transport, and the NP-complete-in-P implication relative to its exact pipeline semantics; it does not prove concrete SAT complete or in P.',
  'The integrated direct CNF-SAT finite-machine verifier proves exact accept/reject correctness, bounded no-timeout behavior, and PNP.Concrete.FinalUniversalDesign.cnfSATInNP; it proves CNF-SAT membership in NP only, not CNF-SAT in P, NP-completeness, or P = NP.',
  'CookLevinRawTapeBridge proves that the finite tableau semantics exactly represent ordinary two-sided raw Tape execution for both input-only and paired-certificate verifier modes, and derives CNFSAT problem.encodedFormula iff language problem.input. CookLevinFormulaSize supplies the external encoded-formula-size polynomial, CookLevinFormulaSchedule supplies an exact answer-independent padded slot schedule, CookLevinFormulaCursor supplies direct coordinate decoders plus exact fuelled traversal, and BuilderInputLength supplies the first literal raw builder stage: an input-preserving unary length tally. Formula emission, a complete raw finite formula builder, a concrete PolynomialReduction, CNFSAT NP-completeness, CNFSAT in P, and P = NP remain absent.',
  'CookLevinFormulaSize bounds the actual canonical unary-indexed CNF bitstring by an explicit fixed-verifier NatPolynomial evaluated only at external source-input length. Exact codec costs, both input modes, all concrete constraint families, program and clause counts, and clause width are covered. This is an output-size theorem only: it does not implement or time a raw finite formula builder or package a PolynomialReduction.',
  'CookLevinFormulaSchedule allocates exact rectangular constraint, clause, token, and raw-bit slots without reading the canonical program, formula, token encoding, or encoded formula as schedule inputs. Filtering populated slots reproduces those existing canonical objects, and the bit-slot count is exactly encodedFormulaSizePolynomial at external input length. This is a pure schedule specification: it is not a raw finite builder, a construction-runtime theorem, a RawRefinement, or a PolynomialReduction.',
  'CookLevinFormulaCursor decodes constraint, clause, token, and raw-bit coordinates without constructing the complete canonical program, formula, token stream, or encoded formula. Its nested options distinguish out-of-range, valid padding, and populated slots; exact prefix, full, one-step-short, terminal, and excess-fuel theorems reproduce the canonical schedule and encoded output. This remains a Lean specification cursor, not a constant-time raw slot interpreter, raw finite builder, construction-runtime theorem, RawRefinement, or PolynomialReduction.',
  'CookLevin.BuilderInputLength is a fixed 19-rule work machine that preserves every source bit, appends exactly one unary tally cell per bit in fresh right-side workspace, and accepts after exactly 2*n*n + 4*n + 2 work steps. Its compiled raw run uses exactly 12*n*n + 24*n + 12 steps, malformed internal scan symbols and one-step-short fuel time out, and its start tape is definitionally the proved total-input-framer endpoint. This is one preparatory builder stage only: it does not emit a formula bit, interpret a formula cursor slot, compose the complete builder, establish RawRefinement or PolynomialReduction, prove CNFSAT NP-completeness or in P, or prove P = NP.',
  'CookLevin.BuilderInputPrefix places the total all-input framer, one total symbol-preserving launch, and BuilderInputLength in one collision-free finite work-machine table. Every raw bitstring reaches the exact preserved-input unary-tally endpoint within 18*n*n + 63*n + 93 compiled raw steps; a tally scan configuration headed by the unused zeroOne symbol times out for every exterior tape and fuel, and one-step-short fuel remains fail-closed. This is still only an input-preparation prefix: it emits no formula bit, interprets no formula cursor coordinate, supplies no complete builder, RawRefinement, PolynomialReduction, CNFSAT NP-completeness or in-P theorem, or P = NP theorem.',
  'CookLevin.BuilderTokenAppender remains the independently audited fixed 59-rule state-selected component. For every raw source word, arbitrary exterior-left garbage, canonical prior token list, and each of F, T, separator, and finish, it appends exactly the selected two-bit token and restores the input focus. Its distinguished start requests the first T header token, reaches a supplied tally endpoint within 24*n + 48 compiled raw steps, and those bits are proved equal to direct formula coordinates zero and one and to encodedFormula.take 2 for both Cook-Levin input modes.',
  'CookLevin.BuilderFirstTokenPrefix is one literal 184-rule finite work machine: all 116 input-prefix rules and all 59 token-appender rules occupy disjoint injective state images after a total nine-symbol bridge. Every raw bitstring reaches the preserved input/tally workspace containing exactly the first T header token within 18*n*n + 87*n + 147 compiled raw steps. The exact prefix endpoint before launch, malformed prefix/appender phases, and one-step-short fuel remain timeout. This emits only the first two fixed formula bits; the remaining width header, dynamic cursor interpreter, complete formula builder, builder RawRefinement, PolynomialReduction, CNFSAT NP-completeness or in-P theorem, and P = NP theorem remain absent.',
  'CookLevin.BuilderCompleteHeader compiles the verifier-fixed formula-width NatPolynomial into a literal unary evaluator, then composes the 184-rule raw-input/first-token prefix, five total nine-symbol bridges, a 16-rule unary-root controller, and two 59-rule appender copies in disjoint injective state images. Every raw bitstring reaches exactly FormulaWidth copies of T followed by F under an external NatPolynomial compiled-time bound, and those token pairs equal the complete canonical encodedFormula width header. The 74 evaluator and 83 composed-header public declarations use only propext and Quot.sound, never Classical.choice or a project axiom. This does not implement the dynamic formula cursor, emit the formula body, supply builder RawRefinement or PolynomialReduction, establish CNFSAT NP-completeness or in P, or prove P = NP.',
  'CookLevin.BuilderBodyStartPrefix composes the complete width-header machine, a structurally generated unary evaluator for the retained next-token coordinate FormulaVariableSlotBound + 2, two total nine-symbol bridges, and a 59-rule Sep appender in disjoint injective state images. Every raw bitstring reaches exactly FormulaWidth copies of T followed by F and Sep, retains the corresponding doubled bit cursor, and obeys the external compiled bound CompleteHeader.rawTimeBound + 72 + 6*Unary.workSteps(nextTokenSlotPolynomial) + 24*n + 12*width. Its 58 public declarations use only propext and Quot.sound, never Classical.choice or a project axiom. This is not a dynamic cursor or complete formula builder and supplies no builder RawRefinement, PolynomialReduction, CNFSAT NP-completeness or in-P result, or P = NP theorem.',
  'The 9,300-pair canonical sweep, 40,020-pair extended sweep, 261,121-pair bounded differential sweep, and ten compiler-edge cases are finite regression evidence; the universal result comes from the audited Lean theorems, not from testing.',
  'The formalized direct-wire NAND semantics layer does not by itself prove enumeration, minimum size, replacement/slack, the locked NAND builder, its threshold, SAT, or P = NP.',
  'The exact-width syntactic NAND enumeration remains intentionally noncanonical and may contain duplicates.',
  'The exhaustive direct-wire truth-table and reference-minimum computation has no polynomial-runtime claim and does not formalize the report\'s residual-band minimizer.',
  'Replacement and global slack are proved only for the concrete serial framed-context construction, not arbitrary support profiles or the report\'s locked-NAND family.',
  'The typed local locked-NAND candidates, source-derived accounting, conditional square-baseline theorem, and five discharged local square baselines do not prove global cross-instance BaselineDistinct, a locked builder or threshold, residual slack at most four, or polynomial runtime.',
  'The report threshold word is multi-output: its baseline coordinates remain present alongside one final coordinate; a legacy single-output seed is not that construction.',
  'The legacy synthetic m=2 fixture is quarantined as internally inconsistent: honest source-derived baseline/displayed counts are 86/90, metadata-consistent counts are 95/99, and stored hybrid counts are 91/95.',
  'The proof-bearing conditional locked-NAND semantic boundary is not the report threshold theorem: it assumes typed baseline and full candidates, baseline output conditions, preservation of the first outputs, an unsatisfiable final-zero law, and satisfiable final-output laws instead of constructing them for arbitrary circuits.',
  'The residual-slack-at-most-four result is conditional on that six-field premise package; it is not an unconditional result for the report locked-NAND family.',
  'Against the hostile-review inventory, DirectWireOutputLowerBound and the model-level ZeroOutputConvention are now discharged, while global MacroDistinct, TraceEquivalence, FinalLockSeparation, carrier layout, and uniform polynomial premise construction remain missing.',
  'The conditional module quantifies an arbitrary satisfiable proposition and baseline natural number; it does not identify them with source-circuit SAT and lockedBaselineCount, enforce answer-independent uniform construction, or connect the candidate boundary to the abstract PNP.LockedNANDThreshold language.',
  'The executable residual-route scan is complete only for the explicit finite implementation list supplied by its caller; unresolved excludes no unlisted gain and does not imply global minimality or ZeroSlack.',
  'An empty-list scan is formally shown to remain unresolved on a positive-slack implementation, so search failure cannot be promoted to zero residual slack.',
  'Exact and ZeroSlack route results require Lean proofs of semantic minimality and are never manufactured by the executable gain scanner; no BCEL, HN/BUD, selector, PCCMin-loop, or residual-band completeness follows.',
  'The residual-route equivalence check exhausts finite Boolean valuations and has no polynomial-runtime claim.',
  'External review is optional audit evidence and is not a mathematical premise or release blocker.',
  'Historical releases and coordinates are preserved for auditability but are not current theorem-status authority.',
  'The designated legacy-v0 command replays pinned assertion-checker behavior only; it is neither current theorem authority nor a mathematical proof.',
  'The compiled Lean theorem inventory is declaration and axiom-dependency evidence; it does not widen any theorem beyond its exact type and stated scope.',
  'PNP.PEqualsNP uses abstract string-handle witnesses rather than a concrete standard complexity model and is categorically ineligible for public theorem activation.',
  'PNP.Main.ConcretePEqualsNP now names the inactive finite charged-pipeline target, while PNP.Main.p_eq_np remains absent.',
  'All five reviewed activation fingerprints remain intentionally unset, so target presence alone cannot open the concrete publication gate.',
  'The current canonical TeX and PDF are generated non-claiming reconstruction reports; the historical 56-page direct-claim report remains historical audit material only.',
]);

const SUPERSEDED_COORDINATES = Object.freeze([
  'PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01',
  'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01',
  'PNP-ACTIVATED-STATUS-2026-07-05-01',
]);

const SUBORDINATE_LEGACY_SURFACES = Object.freeze([
  'PNP_STATUS.json',
  'status/ACTIVATED_PNP_STATUS.json',
  'proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json',
  'proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.md',
  'proof-obligations/UNIFORM_INPUT_FAMILY.json',
  'proof-obligations/UNIFORM_INPUT_FAMILY.md',
  'proof-obligations/UNIFORM_LOCKED_NAND_CONSTRUCTION.json',
  'proof-obligations/UNIFORM_LOCKED_NAND_CONSTRUCTION.md',
  'proof-obligations/UNIFORM_LOCKED_NAND_THRESHOLD.json',
  'proof-obligations/UNIFORM_LOCKED_NAND_THRESHOLD.md',
  'proof-obligations/UNIFORM_RESIDUAL_BAND_MINIMIZER.json',
  'proof-obligations/UNIFORM_RESIDUAL_BAND_MINIMIZER.md',
  'proof-obligations/UNIFORM_ZEROSLACK_CLOSURE.json',
  'proof-obligations/UNIFORM_ZEROSLACK_CLOSURE.md',
  'proof-obligations/UNIFORM_NO_HIDDEN_ORACLE_SEMANTIC.json',
  'proof-obligations/UNIFORM_NO_HIDDEN_ORACLE_SEMANTIC.md',
  'proof-obligations/UNIFORM_COMPLEXITY_CONCLUSION.json',
  'proof-obligations/UNIFORM_COMPLEXITY_CONCLUSION.md',
  'proof-obligations/UNRESTRICTED_FINAL_SOUNDNESS_RELEASE.json',
  'proof-obligations/UNRESTRICTED_FINAL_SOUNDNESS_RELEASE.md',
  'proof-obligations/PUBLIC_THEOREM_ACTIVATION.json',
  'proof-obligations/PUBLIC_THEOREM_ACTIVATION.md',
  'proof-obligations/OBLIGATION_LEDGER.json',
  'proof-obligations/GAP_LEDGER.json',
  'proof-obligations/GAP_LEDGER.md',
  'proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json',
  'proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.md',
  'complexity/COMPLEXITY_LEDGER.json',
  'complexity/COMPLEXITY_LEDGER.md',
  'trust-base/TRUST_BASE.json',
  'trust-base/SHRINK_PLAN.json',
  'trust-base/SHRINK_PLAN.md',
  'release/PUBLIC_REVIEW_BOUNDARY.json',
  'release/PUBLIC_REVIEW_BOUNDARY.md',
  'release/PUBLIC_REVIEW_HANDOFF.json',
  'release/PUBLIC_REVIEW_HANDOFF.md',
  'review/PUBLIC_REVIEW_CHECKLIST.json',
  'review/PUBLIC_REVIEW_CHECKLIST.md',
  'release/PUBLIC_THEOREM_EMISSION_DENIAL.json',
  'release/PUBLIC_THEOREM_EMISSION_DENIAL.md',
  'release/PUBLIC_THEOREM_EMISSION_GATE.json',
  'release/PUBLIC_THEOREM_EMISSION_GATE.md',
  'release/PUBLIC_THEOREM_EMISSION_NEGATIVE_TRANSITIONS.json',
  'release/PUBLIC_THEOREM_EMISSION_NEGATIVE_TRANSITIONS.md',
  'release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json',
  'release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.md',
  'release/RELEASE_BLOCKER_CLEARANCE.json',
  'release/RELEASE_BLOCKER_CLEARANCE.md',
  'review/EXTERNAL_REVIEW_STATUS.md',
  'REVIEWER_MAP.md',
  'TRUST_BASE.md',
  'PUBLIC_REVIEW.json',
  'PUBLIC_REVIEW.md',
  'RELEASE_LADDER.md',
  'release/RELEASE_LADDER.json',
  'review/EXTERNAL_REVIEW_STATUS.json',
]);

const SUBORDINATE_LEGACY_SURFACE_ROOTS = Object.freeze([
  'checker-cycles/',
  'checker-mutations/',
  'checker-totality/',
  'complexity/',
  'independent-verifiers/',
  'kernel/',
  'oracle-audit/',
  'proof-obligations/',
  'release/',
  'report-bindings/',
  'reproducibility/',
  'review/',
  'trust-base/',
  'artifacts/multi-platform-ci/',
  'artifacts/regeneration/',
  'archive/legacy-v0/',
]);

const ACTIVE_CORE_WORKFLOWS = Object.freeze([
  '.github/workflows/ci.yml',
  '.github/workflows/lean-bridge.yml',
  '.github/workflows/pnp-verify-all.yml',
  '.github/workflows/proof-development.yml',
]);

const HISTORICAL_REPLAY_WORKFLOWS = Object.freeze([
  '.github/workflows/legacy-v0-replay.yml',
]);

const ACTIVE_COMPANION_WORKFLOWS = Object.freeze([
  '.github/workflows/ci.yml',
  '.github/workflows/pnp-public-payloads.yml',
  '.github/workflows/pnp-upstream-status-consistency.yml',
  '.github/workflows/pnp-verification-run-issue-ingest.yml',
  '.github/workflows/pnp-verifier-run-import.yml',
  '.github/workflows/sync-public-access-report.yml',
]);

const EXACT_FIELDS = Object.freeze({
  kind: 'PNPFormalReconstructionStatus0',
  version: VERSION,
  project: 'PNP',
  coordinate: COORDINATE,
  status: 'formal-reconstruction-in-progress',
  claimStatus: 'formal-reconstruction-in-progress',
  currentStatusAuthority: true,
  targetTheorem: 'P = NP',
  leanToolchain: 'leanprover/lean4:v4.31.0',
  leanCompilerVersion: '4.31.0',
  leanCompilerCommit: '68218e876d2a38b1985b8590fff244a83c321783',
  lakeVersion: '5.0.0-src+68218e8',
  elanVersion: '4.2.3',
  elanReleaseCommit: 'b6cec7e10fe4965a605aaf60d1cb4a5837f0462b',
  elanArchiveSha256: 'df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2',
  leanBuildTarget: 'PNP',
  leanRootModule: 'PNP',
  leanRootStatusDeclaration: 'PNP.Main.rootTheoremStatus',
  leanBuildConfigurationPinned: true,
  explicitLeanRootTargetPresent: true,
  leanLibraryTargetBuilt: true,
  leanSourcePlaceholderAuditPassed: true,
  leanConcreteCNFVerifierCorrectnessFormalized: true,
  leanConcreteCNFVerifierNoTimeoutFormalized: true,
  leanConcreteCNFVerifierAxiomAuditPassed: true,
  leanConcreteCNFWorkAxiomAuditPassed: true,
  leanConcreteCNFWorkAuditedDeclarationCount: 766,
  leanConcreteCNFSATMembershipFormalized: true,
  leanConcreteCNFSATMembershipTheorem: 'PNP.Concrete.FinalUniversalDesign.cnfSATInNP',
  leanConcreteCNFProofScope: 'direct-finite-machine-verifier-correctness-and-np-membership-only',
  leanConcreteCNFSATInPFormalized: false,
  leanConcreteCNFNPCompletenessFormalized: false,
  leanConcreteCookLevinBuilderInputLengthFormalized: true,
  leanConcreteCookLevinBuilderInputLengthAxiomAuditPassed: true,
  leanConcreteCookLevinBuilderInputLengthAuditedDeclarationCount: 39,
  leanConcreteCookLevinBuilderInputLengthCompiledRawMachineFormalized: true,
  leanConcreteCookLevinBuilderInputLengthExternalInputSizePolynomialFormalized: true,
  leanConcreteCookLevinBuilderInputLengthMalformedInternalInputTimeoutFormalized: true,
  leanConcreteCookLevinBuilderInputLengthConnectedToTotalInputFramerEndpointFormalized: true,
  leanConcreteCookLevinBuilderInputPrefixFormalized: true,
  leanConcreteCookLevinBuilderInputPrefixAxiomAuditPassed: true,
  leanConcreteCookLevinBuilderInputPrefixAuditedDeclarationCount: 40,
  leanConcreteCookLevinBuilderInputPrefixCompiledRawMachineFormalized: true,
  leanConcreteCookLevinBuilderInputPrefixExternalInputSizePolynomialFormalized: true,
  leanConcreteCookLevinBuilderInputPrefixMalformedScanSymbolTimeoutFormalized: true,
  leanConcreteCookLevinBuilderInputPrefixLiteralFramerLaunchFormalized: true,
  leanConcreteCookLevinBuilderTokenAppenderFormalized: true,
  leanConcreteCookLevinBuilderTokenAppenderAxiomAuditPassed: true,
  leanConcreteCookLevinBuilderTokenAppenderAuditedDeclarationCount: 68,
  leanConcreteCookLevinBuilderTokenAppenderCompiledRawMachineFormalized: true,
  leanConcreteCookLevinBuilderTokenAppenderExternalInputSizePolynomialFormalized: true,
  leanConcreteCookLevinBuilderTokenAppenderAllTokensExactFormalized: true,
  leanConcreteCookLevinBuilderTokenAppenderFirstFormulaBitsFormalized: true,
  leanConcreteCookLevinBuilderTokenAppenderMalformedPhaseTimeoutFormalized: true,
  leanConcreteCookLevinBuilderTokenAppenderInputPrefixComposed: true,
  leanConcreteCookLevinBuilderFirstTokenPrefixFormalized: true,
  leanConcreteCookLevinBuilderFirstTokenPrefixAxiomAuditPassed: true,
  leanConcreteCookLevinBuilderFirstTokenPrefixAuditedDeclarationCount: 37,
  leanConcreteCookLevinBuilderFirstTokenPrefixCompiledRawMachineFormalized: true,
  leanConcreteCookLevinBuilderFirstTokenPrefixExternalInputSizePolynomialFormalized: true,
  leanConcreteCookLevinBuilderFirstTokenPrefixExactFormulaBitsFormalized: true,
  leanConcreteCookLevinBuilderFirstTokenPrefixMalformedPhaseTimeoutFormalized: true,
  leanConcreteCookLevinBuilderUnaryPolynomialFormalized: true,
  leanConcreteCookLevinBuilderUnaryPolynomialAxiomAuditPassed: true,
  leanConcreteCookLevinBuilderUnaryPolynomialAuditedDeclarationCount: 74,
  leanConcreteCookLevinBuilderUnaryPolynomialCompiledRawMachineFormalized: true,
  leanConcreteCookLevinBuilderUnaryPolynomialExactRuntimePolynomialFormalized: true,
  leanConcreteCookLevinBuilderCompleteHeaderFormalized: true,
  leanConcreteCookLevinBuilderCompleteHeaderAxiomAuditPassed: true,
  leanConcreteCookLevinBuilderCompleteHeaderAuditedDeclarationCount: 83,
  leanConcreteCookLevinBuilderCompleteHeaderCompiledRawMachineFormalized: true,
  leanConcreteCookLevinBuilderCompleteHeaderExternalInputSizePolynomialFormalized: true,
  leanConcreteCookLevinBuilderCompleteHeaderExactFormulaBitsFormalized: true,
  leanConcreteCookLevinBuilderCompleteHeaderInputPrefixAppenderComposed: true,
  leanConcreteCookLevinBuilderCompleteHeaderFailClosedBoundaryTimeoutFormalized: true,
  leanConcreteCookLevinBuilderBodyStartPrefixFormalized: true,
  leanConcreteCookLevinBuilderBodyStartPrefixAxiomAuditPassed: true,
  leanConcreteCookLevinBuilderBodyStartPrefixAuditedDeclarationCount: 58,
  leanConcreteCookLevinBuilderBodyStartPrefixCompiledRawMachineFormalized: true,
  leanConcreteCookLevinBuilderBodyStartPrefixExternalInputSizePolynomialFormalized: true,
  leanConcreteCookLevinBuilderBodyStartPrefixExactFormulaBitsFormalized: true,
  leanConcreteCookLevinBuilderBodyStartPrefixRetainedNextTokenCoordinateFormalized: true,
  leanConcreteCookLevinBuilderBodyStartPrefixInputPrefixAppenderComposed: true,
  leanConcreteCookLevinBuilderBodyStartPrefixFailClosedBoundaryTimeoutFormalized: true,
  leanConcreteCookLevinBuilderInputPrefixAppenderComposed: true,
  leanConcreteCookLevinBuilderDynamicCursorFormalized: false,
  leanConcreteCookLevinFormulaBuilderFormalized: false,
  leanConcreteCookLevinBuilderRawRefinementFormalized: false,
  leanConcreteCookLevinBuilderPolynomialReductionFormalized: false,
  leanConcretePipelineStateNamespaceFormalized: true,
  leanConcretePipelineStateNamespaceAxiomAuditPassed: true,
  leanConcretePipelineStateNamespaceAuditedDeclarationCount: 39,
  leanConcretePipelineSequentialNamespaceFormalized: true,
  leanConcretePipelineSequentialNamespaceAxiomAuditPassed: true,
  leanConcretePipelineSequentialNamespaceAuditedDeclarationCount: 26,
  leanConcretePipelineSequentialCompilationFormalized: true,
  leanConcretePipelineSequentialCompilerAxiomAuditPassed: true,
  leanConcretePipelineSequentialCompilerAuditedDeclarationCount: 31,
  leanConcretePipelineSequentialVerdictAndOutputPreservationFormalized: true,
  leanConcretePipelineSequentialExternalInputSizePolynomialFormalized: true,
  leanConcretePipelineSequentialStuckFirstTimeoutFormalized: true,
  leanConcretePipelineRuleTableCompositionFormalized: true,
  leanConcretePipelineStageBridgesFormalized: true,
  leanConcretePipelineStageBridgesAxiomAuditPassed: true,
  leanConcretePipelineStageBridgesAuditedDeclarationCount: 56,
  leanConcretePipelineStageLaunchFormalized: true,
  leanConcretePipelineVerdictPreservationFormalized: true,
  leanConcretePipelineInternalOutputHandoffComposed: true,
  leanConcretePipelineTerminalOutputPackingFormalized: true,
  leanConcretePipelineTerminalOutputPackerAxiomAuditPassed: true,
  leanConcretePipelineTerminalOutputPackerAuditedDeclarationCount: 69,
  leanConcretePipelineTerminalOutputPackerConnectedToBridgeEndpointFormalized: true,
  leanConcretePipelineTerminalBridgeAxiomAuditPassed: true,
  leanConcretePipelineTerminalBridgeAuditedDeclarationCount: 59,
  leanConcretePipelinePriorTraceTransportToTerminalBridgeFormalized: true,
  leanConcretePipelinePairedCompilerAxiomAuditPassed: true,
  leanConcretePipelinePairedCompilerAuditedDeclarationCount: 28,
  leanConcretePipelineCanonicalPairCompilationFormalized: true,
  leanConcretePipelineCompilerAxiomAuditPassed: true,
  leanConcretePipelineCompilerAuditedDeclarationCount: 29,
  leanConcretePipelineAllInputCompilationFormalized: true,
  leanConcretePipelineInputFramerAxiomAuditPassed: true,
  leanConcretePipelineInputFramerAuditedDeclarationCount: 70,
  leanConcretePipelineAllInputFramingFormalized: true,
  leanConcretePipelineMalformedInputBehaviorFormalized: true,
  leanConcretePipelineRawRefinementFormalized: true,
  leanConcretePipelineRefinementAxiomAuditPassed: true,
  leanConcretePipelineRefinementAuditedDeclarationCount: 16,
  leanConcreteFunctionProgramRecursiveCompilationFormalized: true,
  leanConcreteDecisionProgramRecursiveCompilationFormalized: true,
  leanConcretePolynomialTimeDeciderRawCompilationFormalized: true,
  leanConcretePipelineExternalInputSizePolynomialFormalized: true,
  leanNANDDirectWireCoreFormalized: true,
  leanNANDDirectWireCoreAxiomAuditPassed: true,
  leanNANDEnumeratorFormalized: true,
  leanNANDEnumeratorAxiomAuditPassed: true,
  leanNANDExactWidthEnumerationComplete: true,
  leanNANDEnumeratorUsesOrderedGatePairs: true,
  leanNANDEnumeratorIncludesUniqueEmptyOutputTuple: true,
  leanNANDEnumeratorDeduplicated: false,
  leanNANDTruthTableFormalized: true,
  leanNANDTruthTableAxiomAuditPassed: true,
  leanNANDSemanticEquivalenceDecidable: true,
  leanNANDMinimumAndSlackFormalized: true,
  leanNANDReferenceMinimumFormalized: true,
  leanNANDReferenceMinimumAxiomAuditPassed: true,
  leanNANDReferenceMinimumExhaustive: true,
  leanNANDReferenceMinimumScope: 'finite-boolean-direct-wire-empty-profile',
  leanNANDReferenceMinimumPolynomialRuntimeProved: false,
  leanNANDResidualSlackZeroIffMinimumFormalized: true,
  leanNANDCompositionFormalized: true,
  leanNANDCompositionAxiomAuditPassed: true,
  leanNANDFramedReplacementFormalized: true,
  leanNANDFramedGlobalSlackLawFormalized: true,
  leanNANDFramedSlackAxiomAuditPassed: true,
  leanNANDReplacementScope: 'concrete-serial-framed-context',
  leanLockedNANDDirectCandidatesFormalized: true,
  leanLockedNANDDirectAxiomAuditPassed: true,
  leanLockedNANDInternalMacroConstantsAbsent: true,
  leanDirectWireOutputLowerBoundFormalized: true,
  leanDirectWireBaselineAxiomAuditPassed: true,
  leanLockedNANDSourceDerivedCountsFormalized: true,
  leanLockedNANDBaselineAccountingFormalized: true,
  leanLockedNANDBaselineAxiomAuditPassed: true,
  leanLockedNANDConditionalSquareBaselineExactnessFormalized: true,
  leanLockedNANDLocalBaselineConditionsFormalized: true,
  leanLockedNANDLocalSquareBaselineExactnessFormalized: true,
  leanLockedNANDLocalBaselineAxiomAuditPassed: true,
  leanLockedNANDProofScope: 'typed-local-macros-source-derived-counts-and-five-local-square-baselines',
  leanLockedNANDConditionalThresholdBoundaryFormalized: true,
  leanLockedNANDConditionalResidualSlackAtMostFourFormalized: true,
  leanLockedNANDThresholdBoundaryAxiomAuditPassed: true,
  leanLockedNANDThresholdBoundaryScope: 'proof-bearing-typed-candidate-and-semantic-premises-only',
  leanLockedNANDThresholdBoundaryPremisesInstantiated: false,
  leanLockedNANDGlobalBaselineDistinctFormalized: false,
  leanLockedNANDCarrierLayoutFormalized: false,
  leanLockedNANDTraceEquivalenceFormalized: false,
  leanLockedNANDDerivedFinalOutputLawsFormalized: false,
  leanLockedNANDResidualSlackAtMostFourFormalized: false,
  leanLockedNANDPolynomialBuilderFormalized: false,
  leanCompatibleReplacementFormalized: false,
  leanGlobalSlackLawFormalized: false,
  leanLockedNANDBuilderFormalized: false,
  leanLockedNANDThresholdFormalized: false,
  leanResidualRoutesListedGainScanFormalized: true,
  leanResidualRoutesAxiomAuditPassed: true,
  leanResidualRoutesGainSoundnessFormalized: true,
  leanResidualRoutesStrictResidualDescentFormalized: true,
  leanResidualRoutesExactResultProofBearing: true,
  leanResidualRoutesZeroSlackResultProofBearing: true,
  leanResidualRoutesUnresolvedFailClosed: true,
  leanResidualRoutesScope: 'explicit-caller-supplied-finite-candidate-list',
  leanResidualRoutesCandidateListCompletenessFormalized: false,
  leanResidualRoutesGlobalGainCompletenessFormalized: false,
  leanZeroSlackPositiveSlackContradictionFormalized: false,
  leanZeroSlackCompletenessFormalized: false,
  leanPCCMinLoopExactnessFormalized: false,
  leanPCCMinPolynomialRuntimeFormalized: false,
  leanResidualBandMinimizerFormalized: false,
  lockedNANDOutputConvention: 'ordered-multi-output-baseline-coordinates-plus-final-coordinate',
  legacySyntheticLockedNANDM2FixtureStatus: 'quarantined-internally-inconsistent',
  legacySyntheticLockedNANDM2HonestBaseline: 86,
  legacySyntheticLockedNANDM2MetadataConsistentBaseline: 95,
  legacySyntheticLockedNANDM2StoredBaseline: 91,
  legacySyntheticLockedNANDM2HonestDisplayedGateCount: 90,
  legacySyntheticLockedNANDM2MetadataConsistentDisplayedGateCount: 99,
  legacySyntheticLockedNANDM2StoredDisplayedGateCount: 95,
  rootLeanTheorem: 'PNP.Main.p_eq_np',
  rootLeanTheoremPresent: false,
  rootLeanTheoremBuilt: false,
  rootLeanTheoremAxiomAuditPassed: false,
  projectSpecificAxiomsRemaining: true,
  sorryOrAdmitInRootDependencyClosure: null,
  checkerAcceptanceIsMathematicalProof: false,
  legacyCheckerStackStatus: 'historical-assertion-checker-evidence-only',
  externalReviewIsMathematicalPremise: false,
  statusVerificationCommand: 'node pcc-formal-reconstruction-status0.mjs --json',
  legacyCheckerArchiveManifest: 'archive/legacy-v0/ARCHIVE.json',
  legacyCheckerArchiveCheckCommand: 'npm run legacy:v0:check',
  legacyCheckerReplayCommand: 'npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d',
  publicSurfaceBaselineCoordinate: 'PUBLIC-SURFACE-BASELINE-2026-07-17-COOK-LEVIN-BUILDER-BODY-START-PREFIX-47',
  formalReconstructionStatusPayload: STATUS_PATH,
  siteStatusPayload: SITE_PATH,
  historicalActivatedStatusCoordinate: 'PNP-ACTIVATED-STATUS-2026-07-05-01',
  reconstructionNotice: 'docs/FORMAL_RECONSTRUCTION.md',
});

export function BuildFormalReconstructionBaseStatus0() {
  return {
    ...EXACT_FIELDS,
    activeFinalNodeIds: [],
    activeCoreWorkflows: [...ACTIVE_CORE_WORKFLOWS],
    historicalReplayWorkflows: [...HISTORICAL_REPLAY_WORKFLOWS],
    activeCompanionWorkflows: [...ACTIVE_COMPANION_WORKFLOWS],
    supersededCoordinates: [...SUPERSEDED_COORDINATES],
    subordinateLegacySurfaces: [...SUBORDINATE_LEGACY_SURFACES],
    subordinateLegacySurfaceRoots: [...SUBORDINATE_LEGACY_SURFACE_ROOTS],
    remainingFormalObligations: [...FORMAL_RECONSTRUCTION_BLOCKERS0],
    remainingBlockers: [...FORMAL_RECONSTRUCTION_BLOCKERS0],
    projectSpecificAxiomInventory: [...PROJECT_SPECIFIC_AXIOM_INVENTORY],
    lockedNANDThresholdHostileReviewLemmaInventory: [
      ...LOCKED_NAND_THRESHOLD_HOSTILE_REVIEW_LEMMA_INVENTORY,
    ],
    leanLockedNANDThresholdPremiseInventory: [...LOCKED_NAND_THRESHOLD_PREMISE_INVENTORY],
    leanLockedNANDThresholdMissingInstantiationInventory: [
      ...LOCKED_NAND_THRESHOLD_MISSING_INSTANTIATION_INVENTORY,
    ],
    verificationCommands: [...VERIFICATION_COMMANDS],
    nonClaims: [...NON_CLAIMS],
  };
}

export async function CheckFormalReconstructionStatus0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;
  try {
    const inventoryBytes = await readFile(path.join(root, LEAN_INVENTORY_PATH0));
    const publicInventoryBytes = await readFile(path.join(root, LEAN_INVENTORY_PUBLIC_PATH0));
    if (!inventoryBytes.equals(publicInventoryBytes)) {
      return write0(root, outputPath, writeOutput, reject0(
        'FormalReconstructionStatus.InventoryMirrorMismatch',
        [LEAN_INVENTORY_PUBLIC_PATH0],
        'public Lean theorem inventory must byte-for-byte mirror the status inventory',
      ));
    }
    const publicationMapBytes = await readFile(path.join(root, FORMAL_PUBLICATION_MAP_PATH0));
    const inventory = JSON.parse(inventoryBytes.toString('utf8'));
    const publicationMap = JSON.parse(publicationMapBytes.toString('utf8'));
    const sourceClosureSha256 = await ComputeLeanSourceClosureSha2560(root, inventory);
    const publication = DeriveFormalPublication0(
      inventory,
      publicationMap,
      inventoryBytes,
      sourceClosureSha256,
    );
    const publicationExpected = publicationExpected0(
      publication,
      inventory,
      publicationMap,
      sha2560(publicationMapBytes),
      sourceClosureSha256,
    );
    const statusRead = await readJson0({
      root,
      filePath: options.statusPath ?? STATUS_PATH,
      override: options.statusOverride,
      bytesOverride: options.statusBytesOverride,
      label: STATUS_PATH,
    });
    if (statusRead.tag === 'reject') return write0(root, outputPath, writeOutput, statusRead);

    const siteRead = await readJson0({
      root,
      filePath: options.sitePath ?? SITE_PATH,
      override: options.siteOverride,
      bytesOverride: options.siteBytesOverride,
      label: SITE_PATH,
    });
    if (siteRead.tag === 'reject') return write0(root, outputPath, writeOutput, siteRead);

    const statusCheck = validateStatus0(statusRead.value, STATUS_PATH, publicationExpected);
    if (statusCheck.tag === 'reject') return write0(root, outputPath, writeOutput, statusCheck);
    const siteCheck = validateStatus0(siteRead.value, SITE_PATH, publicationExpected);
    if (siteCheck.tag === 'reject') return write0(root, outputPath, writeOutput, siteCheck);

    if (!statusRead.bytes.equals(siteRead.bytes)) {
      return write0(root, outputPath, writeOutput, reject0(
        'FormalReconstructionStatus.SiteMirrorMismatch',
        [SITE_PATH],
        'public status payload must byte-for-byte mirror the formal reconstruction status',
      ));
    }

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORDINATE,
      claimStatus: 'formal-reconstruction-status-accepted',
      formalReconstructionStatusAccepted: true,
      targetTheorem: 'P = NP',
      ...publication.emissionFields,
      leanToolchain: 'leanprover/lean4:v4.31.0',
      leanCompilerVersion: '4.31.0',
      leanCompilerCommit: '68218e876d2a38b1985b8590fff244a83c321783',
      lakeVersion: '5.0.0-src+68218e8',
      elanVersion: '4.2.3',
      elanReleaseCommit: 'b6cec7e10fe4965a605aaf60d1cb4a5837f0462b',
      elanArchiveSha256: 'df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2',
      leanBuildTarget: 'PNP',
      leanRootModule: 'PNP',
      leanRootStatusDeclaration: 'PNP.Main.rootTheoremStatus',
      leanBuildConfigurationPinned: true,
      explicitLeanRootTargetPresent: true,
      leanLibraryTargetBuilt: true,
      leanSourcePlaceholderAuditPassed: true,
      leanConcreteCNFVerifierCorrectnessFormalized: true,
      leanConcreteCNFVerifierNoTimeoutFormalized: true,
      leanConcreteCNFVerifierAxiomAuditPassed: true,
      leanConcreteCNFWorkAxiomAuditPassed: true,
      leanConcreteCNFWorkAuditedDeclarationCount: 766,
      leanConcreteCNFSATMembershipFormalized: true,
      leanConcreteCNFSATMembershipTheorem: 'PNP.Concrete.FinalUniversalDesign.cnfSATInNP',
      leanConcreteCNFProofScope: 'direct-finite-machine-verifier-correctness-and-np-membership-only',
      leanConcreteCNFSATInPFormalized: false,
      leanConcreteCNFNPCompletenessFormalized: false,
      leanConcreteCookLevinBuilderInputLengthFormalized: true,
      leanConcreteCookLevinBuilderInputLengthAxiomAuditPassed: true,
      leanConcreteCookLevinBuilderInputLengthAuditedDeclarationCount: 39,
      leanConcreteCookLevinBuilderInputLengthCompiledRawMachineFormalized: true,
      leanConcreteCookLevinBuilderInputLengthExternalInputSizePolynomialFormalized: true,
      leanConcreteCookLevinBuilderInputLengthMalformedInternalInputTimeoutFormalized: true,
      leanConcreteCookLevinBuilderInputLengthConnectedToTotalInputFramerEndpointFormalized: true,
      leanConcreteCookLevinBuilderInputPrefixFormalized: true,
      leanConcreteCookLevinBuilderInputPrefixAxiomAuditPassed: true,
      leanConcreteCookLevinBuilderInputPrefixAuditedDeclarationCount: 40,
      leanConcreteCookLevinBuilderInputPrefixCompiledRawMachineFormalized: true,
      leanConcreteCookLevinBuilderInputPrefixExternalInputSizePolynomialFormalized: true,
      leanConcreteCookLevinBuilderInputPrefixMalformedScanSymbolTimeoutFormalized: true,
      leanConcreteCookLevinBuilderInputPrefixLiteralFramerLaunchFormalized: true,
      leanConcreteCookLevinBuilderTokenAppenderFormalized: true,
      leanConcreteCookLevinBuilderTokenAppenderAxiomAuditPassed: true,
      leanConcreteCookLevinBuilderTokenAppenderAuditedDeclarationCount: 68,
      leanConcreteCookLevinBuilderTokenAppenderCompiledRawMachineFormalized: true,
      leanConcreteCookLevinBuilderTokenAppenderExternalInputSizePolynomialFormalized: true,
      leanConcreteCookLevinBuilderTokenAppenderAllTokensExactFormalized: true,
      leanConcreteCookLevinBuilderTokenAppenderFirstFormulaBitsFormalized: true,
      leanConcreteCookLevinBuilderTokenAppenderMalformedPhaseTimeoutFormalized: true,
      leanConcreteCookLevinBuilderTokenAppenderInputPrefixComposed: true,
      leanConcreteCookLevinBuilderFirstTokenPrefixFormalized: true,
      leanConcreteCookLevinBuilderFirstTokenPrefixAxiomAuditPassed: true,
      leanConcreteCookLevinBuilderFirstTokenPrefixAuditedDeclarationCount: 37,
      leanConcreteCookLevinBuilderFirstTokenPrefixCompiledRawMachineFormalized: true,
      leanConcreteCookLevinBuilderFirstTokenPrefixExternalInputSizePolynomialFormalized: true,
      leanConcreteCookLevinBuilderFirstTokenPrefixExactFormulaBitsFormalized: true,
      leanConcreteCookLevinBuilderFirstTokenPrefixMalformedPhaseTimeoutFormalized: true,
      leanConcreteCookLevinBuilderUnaryPolynomialFormalized: true,
      leanConcreteCookLevinBuilderUnaryPolynomialAxiomAuditPassed: true,
      leanConcreteCookLevinBuilderUnaryPolynomialAuditedDeclarationCount: 74,
      leanConcreteCookLevinBuilderUnaryPolynomialCompiledRawMachineFormalized: true,
      leanConcreteCookLevinBuilderUnaryPolynomialExactRuntimePolynomialFormalized: true,
      leanConcreteCookLevinBuilderCompleteHeaderFormalized: true,
      leanConcreteCookLevinBuilderCompleteHeaderAxiomAuditPassed: true,
      leanConcreteCookLevinBuilderCompleteHeaderAuditedDeclarationCount: 83,
      leanConcreteCookLevinBuilderCompleteHeaderCompiledRawMachineFormalized: true,
      leanConcreteCookLevinBuilderCompleteHeaderExternalInputSizePolynomialFormalized: true,
      leanConcreteCookLevinBuilderCompleteHeaderExactFormulaBitsFormalized: true,
      leanConcreteCookLevinBuilderCompleteHeaderInputPrefixAppenderComposed: true,
      leanConcreteCookLevinBuilderCompleteHeaderFailClosedBoundaryTimeoutFormalized: true,
      leanConcreteCookLevinBuilderBodyStartPrefixFormalized: true,
      leanConcreteCookLevinBuilderBodyStartPrefixAxiomAuditPassed: true,
      leanConcreteCookLevinBuilderBodyStartPrefixAuditedDeclarationCount: 58,
      leanConcreteCookLevinBuilderBodyStartPrefixCompiledRawMachineFormalized: true,
      leanConcreteCookLevinBuilderBodyStartPrefixExternalInputSizePolynomialFormalized: true,
      leanConcreteCookLevinBuilderBodyStartPrefixExactFormulaBitsFormalized: true,
      leanConcreteCookLevinBuilderBodyStartPrefixRetainedNextTokenCoordinateFormalized: true,
      leanConcreteCookLevinBuilderBodyStartPrefixInputPrefixAppenderComposed: true,
      leanConcreteCookLevinBuilderBodyStartPrefixFailClosedBoundaryTimeoutFormalized: true,
      leanConcreteCookLevinBuilderInputPrefixAppenderComposed: true,
      leanConcreteCookLevinBuilderDynamicCursorFormalized: false,
      leanConcreteCookLevinFormulaBuilderFormalized: false,
      leanConcreteCookLevinBuilderRawRefinementFormalized: false,
      leanConcreteCookLevinBuilderPolynomialReductionFormalized: false,
      leanConcretePipelineStateNamespaceFormalized: true,
      leanConcretePipelineStateNamespaceAxiomAuditPassed: true,
      leanConcretePipelineStateNamespaceAuditedDeclarationCount: 39,
      leanConcretePipelineSequentialNamespaceFormalized: true,
      leanConcretePipelineSequentialNamespaceAxiomAuditPassed: true,
      leanConcretePipelineSequentialNamespaceAuditedDeclarationCount: 26,
      leanConcretePipelineSequentialCompilationFormalized: true,
      leanConcretePipelineSequentialCompilerAxiomAuditPassed: true,
      leanConcretePipelineSequentialCompilerAuditedDeclarationCount: 31,
      leanConcretePipelineSequentialVerdictAndOutputPreservationFormalized: true,
      leanConcretePipelineSequentialExternalInputSizePolynomialFormalized: true,
      leanConcretePipelineSequentialStuckFirstTimeoutFormalized: true,
      leanConcretePipelineRuleTableCompositionFormalized: true,
      leanConcretePipelineStageBridgesFormalized: true,
      leanConcretePipelineStageBridgesAxiomAuditPassed: true,
      leanConcretePipelineStageBridgesAuditedDeclarationCount: 56,
      leanConcretePipelineStageLaunchFormalized: true,
      leanConcretePipelineVerdictPreservationFormalized: true,
      leanConcretePipelineInternalOutputHandoffComposed: true,
      leanConcretePipelineTerminalOutputPackingFormalized: true,
      leanConcretePipelineTerminalOutputPackerAxiomAuditPassed: true,
      leanConcretePipelineTerminalOutputPackerAuditedDeclarationCount: 69,
      leanConcretePipelineTerminalOutputPackerConnectedToBridgeEndpointFormalized: true,
      leanConcretePipelineTerminalBridgeAxiomAuditPassed: true,
      leanConcretePipelineTerminalBridgeAuditedDeclarationCount: 59,
      leanConcretePipelinePriorTraceTransportToTerminalBridgeFormalized: true,
      leanConcretePipelinePairedCompilerAxiomAuditPassed: true,
      leanConcretePipelinePairedCompilerAuditedDeclarationCount: 28,
      leanConcretePipelineCanonicalPairCompilationFormalized: true,
      leanConcretePipelineCompilerAxiomAuditPassed: true,
      leanConcretePipelineCompilerAuditedDeclarationCount: 29,
      leanConcretePipelineAllInputCompilationFormalized: true,
      leanConcretePipelineInputFramerAxiomAuditPassed: true,
      leanConcretePipelineInputFramerAuditedDeclarationCount: 70,
      leanConcretePipelineAllInputFramingFormalized: true,
      leanConcretePipelineMalformedInputBehaviorFormalized: true,
      leanConcretePipelineRawRefinementFormalized: true,
      leanConcretePipelineRefinementAxiomAuditPassed: true,
      leanConcretePipelineRefinementAuditedDeclarationCount: 16,
      leanConcreteFunctionProgramRecursiveCompilationFormalized: true,
      leanConcreteDecisionProgramRecursiveCompilationFormalized: true,
      leanConcretePolynomialTimeDeciderRawCompilationFormalized: true,
      leanConcretePipelineExternalInputSizePolynomialFormalized: true,
      leanNANDDirectWireCoreFormalized: true,
      leanNANDDirectWireCoreAxiomAuditPassed: true,
      leanNANDEnumeratorFormalized: true,
      leanNANDEnumeratorAxiomAuditPassed: true,
      leanNANDExactWidthEnumerationComplete: true,
      leanNANDEnumeratorUsesOrderedGatePairs: true,
      leanNANDEnumeratorIncludesUniqueEmptyOutputTuple: true,
      leanNANDEnumeratorDeduplicated: false,
      leanNANDTruthTableFormalized: true,
      leanNANDTruthTableAxiomAuditPassed: true,
      leanNANDSemanticEquivalenceDecidable: true,
      leanNANDMinimumAndSlackFormalized: true,
      leanNANDReferenceMinimumFormalized: true,
      leanNANDReferenceMinimumAxiomAuditPassed: true,
      leanNANDReferenceMinimumExhaustive: true,
      leanNANDReferenceMinimumScope: 'finite-boolean-direct-wire-empty-profile',
      leanNANDReferenceMinimumPolynomialRuntimeProved: false,
      leanNANDResidualSlackZeroIffMinimumFormalized: true,
      leanNANDCompositionFormalized: true,
      leanNANDCompositionAxiomAuditPassed: true,
      leanNANDFramedReplacementFormalized: true,
      leanNANDFramedGlobalSlackLawFormalized: true,
      leanNANDFramedSlackAxiomAuditPassed: true,
      leanNANDReplacementScope: 'concrete-serial-framed-context',
      leanLockedNANDDirectCandidatesFormalized: true,
      leanLockedNANDDirectAxiomAuditPassed: true,
      leanLockedNANDInternalMacroConstantsAbsent: true,
      leanDirectWireOutputLowerBoundFormalized: true,
      leanDirectWireBaselineAxiomAuditPassed: true,
      leanLockedNANDSourceDerivedCountsFormalized: true,
      leanLockedNANDBaselineAccountingFormalized: true,
      leanLockedNANDBaselineAxiomAuditPassed: true,
      leanLockedNANDConditionalSquareBaselineExactnessFormalized: true,
      leanLockedNANDLocalBaselineConditionsFormalized: true,
      leanLockedNANDLocalSquareBaselineExactnessFormalized: true,
      leanLockedNANDLocalBaselineAxiomAuditPassed: true,
      leanLockedNANDProofScope: 'typed-local-macros-source-derived-counts-and-five-local-square-baselines',
      leanLockedNANDConditionalThresholdBoundaryFormalized: true,
      leanLockedNANDConditionalResidualSlackAtMostFourFormalized: true,
      leanLockedNANDThresholdBoundaryAxiomAuditPassed: true,
      leanLockedNANDThresholdBoundaryScope: 'proof-bearing-typed-candidate-and-semantic-premises-only',
      leanLockedNANDThresholdBoundaryPremisesInstantiated: false,
      leanLockedNANDGlobalBaselineDistinctFormalized: false,
      leanLockedNANDCarrierLayoutFormalized: false,
      leanLockedNANDTraceEquivalenceFormalized: false,
      leanLockedNANDDerivedFinalOutputLawsFormalized: false,
      leanLockedNANDResidualSlackAtMostFourFormalized: false,
      leanLockedNANDPolynomialBuilderFormalized: false,
      leanCompatibleReplacementFormalized: false,
      leanGlobalSlackLawFormalized: false,
      leanLockedNANDBuilderFormalized: false,
      leanLockedNANDThresholdFormalized: false,
      leanResidualRoutesListedGainScanFormalized: true,
      leanResidualRoutesAxiomAuditPassed: true,
      leanResidualRoutesGainSoundnessFormalized: true,
      leanResidualRoutesStrictResidualDescentFormalized: true,
      leanResidualRoutesExactResultProofBearing: true,
      leanResidualRoutesZeroSlackResultProofBearing: true,
      leanResidualRoutesUnresolvedFailClosed: true,
      leanResidualRoutesScope: 'explicit-caller-supplied-finite-candidate-list',
      leanResidualRoutesCandidateListCompletenessFormalized: false,
      leanResidualRoutesGlobalGainCompletenessFormalized: false,
      leanZeroSlackPositiveSlackContradictionFormalized: false,
      leanZeroSlackCompletenessFormalized: false,
      leanPCCMinLoopExactnessFormalized: false,
      leanPCCMinPolynomialRuntimeFormalized: false,
      leanResidualBandMinimizerFormalized: false,
      lockedNANDOutputConvention: 'ordered-multi-output-baseline-coordinates-plus-final-coordinate',
      legacySyntheticLockedNANDM2FixtureStatus: 'quarantined-internally-inconsistent',
      legacySyntheticLockedNANDM2HonestBaseline: 86,
      legacySyntheticLockedNANDM2MetadataConsistentBaseline: 95,
      legacySyntheticLockedNANDM2StoredBaseline: 91,
      legacySyntheticLockedNANDM2HonestDisplayedGateCount: 90,
      legacySyntheticLockedNANDM2MetadataConsistentDisplayedGateCount: 99,
      legacySyntheticLockedNANDM2StoredDisplayedGateCount: 95,
      rootLeanTheoremPresent: publicationExpected.rootLeanTheoremPresent,
      rootLeanTheoremBuilt: publicationExpected.rootLeanTheoremBuilt,
      rootLeanTheoremAxiomAuditPassed: publicationExpected.rootLeanTheoremAxiomAuditPassed,
      projectSpecificAxiomsRemaining: true,
      projectSpecificAxiomInventory: [...PROJECT_SPECIFIC_AXIOM_INVENTORY],
      lockedNANDThresholdHostileReviewLemmaInventory: [...LOCKED_NAND_THRESHOLD_HOSTILE_REVIEW_LEMMA_INVENTORY],
      leanLockedNANDThresholdPremiseInventory: [...LOCKED_NAND_THRESHOLD_PREMISE_INVENTORY],
      leanLockedNANDThresholdMissingInstantiationInventory: [...LOCKED_NAND_THRESHOLD_MISSING_INSTANTIATION_INVENTORY],
      externalReviewIsMathematicalPremise: false,
      legacyCheckerArchiveManifest: 'archive/legacy-v0/ARCHIVE.json',
      legacyCheckerReplayCommand: 'npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d',
      remainingFormalObligations: [...FORMAL_RECONSTRUCTION_BLOCKERS0],
      remainingBlockers: [...FORMAL_RECONSTRUCTION_BLOCKERS0],
      statusPayload: STATUS_PATH,
      siteStatusPayload: SITE_PATH,
      statusSha256: sha2560(statusRead.bytes),
      siteStatusSha256: sha2560(siteRead.bytes),
      leanTheoremInventorySha256: publication.inventorySha256,
      concretePublicationGatePassed: publication.gate.passed,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0(
      'FormalReconstructionStatus.UnhandledException',
      [],
      'status checker threw unexpectedly',
      normalizeError0(error),
    ));
  }
}

function publicationExpected0(publication, inventory, publicationMap, publicationMapSha256, sourceClosureSha256) {
  const rootCandidate = inventory.compatibilityRootCandidate;
  return {
    ...publication.emissionFields,
    rootLeanTheoremPresent: rootCandidate !== null,
    rootLeanTheoremBuilt: rootCandidate !== null
      && publication.gate.subchecks.compatibilityRootIsTheorem
      && publication.gate.subchecks.compatibilityRootHasExactConcreteType,
    rootLeanTheoremAxiomAuditPassed: rootCandidate !== null
      && publication.gate.subchecks.compatibilityRootIsTheorem
      && publication.gate.subchecks.compatibilityRootHasExactConcreteType
      && rootCandidate.axioms.every((name) => publication.gate.allowedLeanStandardAxioms.includes(name)),
    sorryOrAdmitInRootDependencyClosure: rootCandidate === null
      ? null
      : rootCandidate.axioms.some((name) => name === 'sorryAx'),
    standardComplexityModelFormalized: publication.gate.subchecks.standardComplexityModelEligible,
    abstractPEqualsNPPublicationEligible: false,
    publicationStatusDerivedOnlyFromConcreteGate: true,
    leanTheoremInventoryCoordinate: inventory.coordinate,
    leanTheoremInventoryPath: LEAN_INVENTORY_PATH0,
    leanTheoremInventoryPublicPath: LEAN_INVENTORY_PUBLIC_PATH0,
    leanTheoremInventorySha256: publication.inventorySha256,
    leanTheoremInventoryGeneratedFromCompiledEnvironment: true,
    leanTheoremInventoryUsesEnvironmentConstants: true,
    leanTheoremInventoryUsesCollectAxioms: true,
    leanTheoremInventoryDeclarationCount: inventory.declarationCount,
    leanTheoremInventoryExcludedPrivateDeclarationCount: inventory.excludedPrivateDeclarationCount,
    leanTheoremInventoryTheoremCount: inventory.theoremCount,
    leanTheoremInventoryAssumptionFreeTheoremCount: inventory.assumptionFreeTheoremCount,
    leanTheoremInventorySourceClosureModuleCount: inventory.sourceClosureModuleCount,
    leanSourceClosureSha256: sourceClosureSha256,
    formalPublicationMapCoordinate: publicationMap.coordinate,
    formalPublicationMapPath: FORMAL_PUBLICATION_MAP_PATH0,
    formalPublicationMapSha256: publicationMapSha256,
    canonicalReportCoordinate: 'PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-17-48',
    canonicalReportSource: 'canonical_proof_report.tex',
    canonicalReportPdf: 'canonical_proof_report.pdf',
    canonicalReportDerivedFromLeanInventory: true,
    concretePublicationGate: publication.gate,
    formalPublicationMilestones: publication.milestones,
  };
}

function validateStatus0(status, label, publicationExpected) {
  if (!plainObject0(status)) return reject0('FormalReconstructionStatus.Shape', [label], 'status payload must be an object');
  const expectedPrimitiveFields = { ...EXACT_FIELDS, ...publicationExpected };
  delete expectedPrimitiveFields.concretePublicationGate;
  delete expectedPrimitiveFields.formalPublicationMilestones;
  const expectedKeys = [
    ...Object.keys(expectedPrimitiveFields),
    'activeFinalNodeIds',
    'activeCoreWorkflows',
    'historicalReplayWorkflows',
    'activeCompanionWorkflows',
    'supersededCoordinates',
    'subordinateLegacySurfaces',
    'subordinateLegacySurfaceRoots',
    'remainingFormalObligations',
    'remainingBlockers',
    'projectSpecificAxiomInventory',
    'lockedNANDThresholdHostileReviewLemmaInventory',
    'leanLockedNANDThresholdPremiseInventory',
    'leanLockedNANDThresholdMissingInstantiationInventory',
    'verificationCommands',
    'nonClaims',
    'concretePublicationGate',
    'formalPublicationMilestones',
  ].sort();
  const actualKeys = Object.keys(status).sort();
  if (!sameArray0(actualKeys, expectedKeys)) {
    return reject0('FormalReconstructionStatus.Keys', [label], 'status payload keys must match the closed schema', {
      expectedKeys,
      actualKeys,
      missingKeys: expectedKeys.filter((key) => !actualKeys.includes(key)),
      extraKeys: actualKeys.filter((key) => !expectedKeys.includes(key)),
    });
  }
  for (const [field, expected] of Object.entries(expectedPrimitiveFields)) {
    if (status[field] !== expected) {
      return reject0('FormalReconstructionStatus.Field', [label, field], 'status field mismatch', {
        expected,
        actual: status[field],
      });
    }
  }
  if (stableStringify0(status.concretePublicationGate)
      !== stableStringify0(publicationExpected.concretePublicationGate)) {
    return reject0('FormalReconstructionStatus.ConcretePublicationGate',
      [label, 'concretePublicationGate'],
      'concrete publication gate must be derived from the compiled Lean inventory');
  }
  if (stableStringify0(status.formalPublicationMilestones)
      !== stableStringify0(publicationExpected.formalPublicationMilestones)) {
    return reject0('FormalReconstructionStatus.PublicationMilestones',
      [label, 'formalPublicationMilestones'],
      'formal publication milestones must be derived from exact Lean declarations');
  }
  const cnfMilestone = publicationExpected.formalPublicationMilestones.find(
    (entry) => entry.id === 'concrete-cnf-universal-verifier',
  );
  if (cnfMilestone?.earned !== true
      || cnfMilestone.status !== 'formalized-np-membership-only'
      || !cnfMilestone.requiredTheorems.includes(
        'PNP.Concrete.FinalUniversalDesign.cnfSATInNP',
      )) {
    return reject0('FormalReconstructionStatus.ConcreteCNFMilestone',
      [label, 'formalPublicationMilestones', 'concrete-cnf-universal-verifier'],
      'direct CNF verifier status requires the exact earned NP-membership milestone');
  }
  if (!sameArray0(status.activeFinalNodeIds, [])) {
    return reject0('FormalReconstructionStatus.ActiveFinalNodes', [label, 'activeFinalNodeIds'], 'active final nodes must be empty');
  }
  if (!sameArray0(status.activeCoreWorkflows, ACTIVE_CORE_WORKFLOWS)) {
    return reject0('FormalReconstructionStatus.CoreWorkflows', [label, 'activeCoreWorkflows'], 'active core workflow inventory mismatch');
  }
  if (!sameArray0(status.historicalReplayWorkflows, HISTORICAL_REPLAY_WORKFLOWS)) {
    return reject0('FormalReconstructionStatus.HistoricalReplayWorkflows', [label, 'historicalReplayWorkflows'], 'historical replay workflow inventory mismatch');
  }
  if (!sameArray0(status.activeCompanionWorkflows, ACTIVE_COMPANION_WORKFLOWS)) {
    return reject0('FormalReconstructionStatus.CompanionWorkflows', [label, 'activeCompanionWorkflows'], 'active companion workflow inventory mismatch');
  }
  if (!sameArray0(status.supersededCoordinates, SUPERSEDED_COORDINATES)) {
    return reject0('FormalReconstructionStatus.SupersededCoordinates', [label, 'supersededCoordinates'], 'superseded activation coordinates mismatch');
  }
  if (!sameArray0(status.subordinateLegacySurfaces, SUBORDINATE_LEGACY_SURFACES)) {
    return reject0('FormalReconstructionStatus.LegacySurfaces', [label, 'subordinateLegacySurfaces'], 'subordinate legacy surface list mismatch');
  }
  if (!sameArray0(status.subordinateLegacySurfaceRoots, SUBORDINATE_LEGACY_SURFACE_ROOTS)) {
    return reject0('FormalReconstructionStatus.LegacySurfaceRoots', [label, 'subordinateLegacySurfaceRoots'], 'subordinate legacy surface root list mismatch');
  }
  if (!sameArray0(status.projectSpecificAxiomInventory, PROJECT_SPECIFIC_AXIOM_INVENTORY)) {
    return reject0('FormalReconstructionStatus.ProjectSpecificAxiomInventory', [label, 'projectSpecificAxiomInventory'], 'project-specific axiom inventory mismatch', {
      expected: PROJECT_SPECIFIC_AXIOM_INVENTORY,
      actual: status.projectSpecificAxiomInventory,
    });
  }
  if (!sameArray0(status.lockedNANDThresholdHostileReviewLemmaInventory,
    LOCKED_NAND_THRESHOLD_HOSTILE_REVIEW_LEMMA_INVENTORY)) {
    return reject0('FormalReconstructionStatus.LockedNANDHostileReviewInventory',
      [label, 'lockedNANDThresholdHostileReviewLemmaInventory'],
      'locked-NAND hostile-review lemma inventory mismatch');
  }
  if (!sameArray0(status.leanLockedNANDThresholdPremiseInventory,
    LOCKED_NAND_THRESHOLD_PREMISE_INVENTORY)) {
    return reject0('FormalReconstructionStatus.LockedNANDThresholdPremiseInventory',
      [label, 'leanLockedNANDThresholdPremiseInventory'],
      'locked-NAND threshold premise inventory mismatch');
  }
  if (!sameArray0(status.leanLockedNANDThresholdMissingInstantiationInventory,
    LOCKED_NAND_THRESHOLD_MISSING_INSTANTIATION_INVENTORY)) {
    return reject0('FormalReconstructionStatus.LockedNANDMissingInstantiationInventory',
      [label, 'leanLockedNANDThresholdMissingInstantiationInventory'],
      'locked-NAND missing-instantiation inventory mismatch');
  }
  if (!sameArray0(status.remainingFormalObligations, FORMAL_RECONSTRUCTION_BLOCKERS0)) {
    return reject0('FormalReconstructionStatus.FormalObligations', [label, 'remainingFormalObligations'], 'formal obligations mismatch');
  }
  if (!sameArray0(status.remainingBlockers, FORMAL_RECONSTRUCTION_BLOCKERS0)) {
    return reject0('FormalReconstructionStatus.Blockers', [label, 'remainingBlockers'], 'formal blockers mismatch');
  }
  if (!sameArray0(status.verificationCommands, VERIFICATION_COMMANDS)) {
    return reject0('FormalReconstructionStatus.Commands', [label, 'verificationCommands'], 'verification commands must exactly match the conservative command list', {
      expected: VERIFICATION_COMMANDS,
      actual: status.verificationCommands,
    });
  }
  if (!sameArray0(status.nonClaims, NON_CLAIMS)) {
    return reject0('FormalReconstructionStatus.NonClaims', [label, 'nonClaims'], 'non-claims must exactly match the conservative boundary', {
      expected: NON_CLAIMS,
      actual: status.nonClaims,
    });
  }
  return { tag: 'accept' };
}

async function readJson0({ root, filePath, override, bytesOverride, label }) {
  if (bytesOverride !== undefined) {
    try {
      const bytes = Buffer.isBuffer(bytesOverride) ? bytesOverride : Buffer.from(String(bytesOverride), 'utf8');
      return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes };
    } catch (error) {
      return reject0('FormalReconstructionStatus.ReadOrParseFailed', [filePath], `could not parse ${label} bytes override`, normalizeError0(error));
    }
  }
  if (override !== undefined) {
    const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8');
    return { tag: 'accept', value: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, filePath));
    return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('FormalReconstructionStatus.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error));
  }
}

async function write0(root, outputPath, enabled, verdict) {
  const rendered = { ...verdict, outputPath: enabled ? outputPath : null };
  if (enabled) {
    const absolute = path.join(root, outputPath);
    await mkdir(path.dirname(absolute), { recursive: true });
    await writeFile(absolute, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8');
  }
  return rendered;
}

function reject0(coord, pathArray, reason, witness = {}) {
  return {
    tag: 'reject',
    kind: 'reject',
    checker: CHECKER,
    version: VERSION,
    coord,
    path: pathArray,
    witness: { reason, ...witness },
    mathematicalTheoremEstablished: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    remainingBlockers: [...FORMAL_RECONSTRUCTION_BLOCKERS0],
  };
}

function plainObject0(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function sameArray0(left, right) {
  return Array.isArray(left) && left.length === right.length && left.every((value, index) => value === right[index]);
}

function stableStringify0(value) {
  if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`;
  if (plainObject0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`;
  return JSON.stringify(value);
}

function sha2560(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function normalizeError0(error) {
  return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null };
}

function parseArgs0(argv) {
  const options = { json: false, writeOutput: true };
  for (const arg of argv) {
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
  } catch (error) {
    console.error(JSON.stringify(reject0('FormalReconstructionStatus.CliBadArgument', [], 'bad CLI argument', normalizeError0(error)), null, 2));
    process.exit(2);
  }
  const verdict = await CheckFormalReconstructionStatus0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();

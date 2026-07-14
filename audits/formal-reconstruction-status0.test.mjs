import assert from 'node:assert/strict';
import { readFile, readdir } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckFormalReconstructionStatus0,
  FORMAL_RECONSTRUCTION_BLOCKERS0,
} from '../pcc-formal-reconstruction-status0.mjs';

async function currentStatus0() {
  return JSON.parse(await readFile(new URL('../status/FORMAL_RECONSTRUCTION_STATUS.json', import.meta.url), 'utf8'));
}

test('formal reconstruction status accepts the current source and public mirrors', async () => {
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-14-36');
  assert.equal(out.formalReconstructionStatusAccepted, true);
  assert.equal(out.mathematicalTheoremEstablished, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.publicTheoremStatement, null);
  assert.equal(out.finalTheoremReady, false);
  assert.equal(out.internalFinalTheoremReady, false);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, false);
  assert.equal(out.uniformFinalSoundnessProved, false);
  assert.equal(out.satInPConclusionAccepted, false);
  assert.equal(out.pEqualsNPConclusionAccepted, false);
  assert.equal(out.leanToolchain, 'leanprover/lean4:v4.31.0');
  assert.equal(out.leanCompilerVersion, '4.31.0');
  assert.equal(out.leanCompilerCommit, '68218e876d2a38b1985b8590fff244a83c321783');
  assert.equal(out.lakeVersion, '5.0.0-src+68218e8');
  assert.equal(out.elanVersion, '4.2.3');
  assert.equal(out.elanReleaseCommit, 'b6cec7e10fe4965a605aaf60d1cb4a5837f0462b');
  assert.equal(out.elanArchiveSha256, 'df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2');
  assert.equal(out.leanBuildTarget, 'PNP');
  assert.equal(out.leanRootModule, 'PNP');
  assert.equal(out.leanRootStatusDeclaration, 'PNP.Main.rootTheoremStatus');
  assert.equal(out.leanBuildConfigurationPinned, true);
  assert.equal(out.explicitLeanRootTargetPresent, true);
  assert.equal(out.leanLibraryTargetBuilt, true);
  assert.equal(out.leanSourcePlaceholderAuditPassed, true);
  assert.equal(out.leanConcreteCNFVerifierCorrectnessFormalized, true);
  assert.equal(out.leanConcreteCNFVerifierNoTimeoutFormalized, true);
  assert.equal(out.leanConcreteCNFVerifierAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCNFWorkAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCNFWorkAuditedDeclarationCount, 766);
  assert.equal(out.leanConcreteCNFSATMembershipFormalized, true);
  assert.equal(out.leanConcreteCNFSATMembershipTheorem,
    'PNP.Concrete.FinalUniversalDesign.cnfSATInNP');
  assert.equal(out.leanConcreteCNFProofScope,
    'direct-finite-machine-verifier-correctness-and-np-membership-only');
  assert.equal(out.leanConcreteCNFSATInPFormalized, false);
  assert.equal(out.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(out.leanConcretePipelineStateNamespaceFormalized, true);
  assert.equal(out.leanConcretePipelineStateNamespaceAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineStateNamespaceAuditedDeclarationCount, 39);
  assert.equal(out.leanConcretePipelineSequentialNamespaceFormalized, true);
  assert.equal(out.leanConcretePipelineSequentialNamespaceAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineSequentialNamespaceAuditedDeclarationCount, 26);
  assert.equal(out.leanConcretePipelineSequentialCompilationFormalized, true);
  assert.equal(out.leanConcretePipelineSequentialCompilerAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineSequentialCompilerAuditedDeclarationCount, 31);
  assert.equal(out.leanConcretePipelineSequentialVerdictAndOutputPreservationFormalized, true);
  assert.equal(out.leanConcretePipelineSequentialExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcretePipelineSequentialStuckFirstTimeoutFormalized, true);
  assert.equal(out.leanConcretePipelineRuleTableCompositionFormalized, true);
  assert.equal(out.leanConcretePipelineStageBridgesFormalized, true);
  assert.equal(out.leanConcretePipelineStageBridgesAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineStageBridgesAuditedDeclarationCount, 56);
  assert.equal(out.leanConcretePipelineStageLaunchFormalized, true);
  assert.equal(out.leanConcretePipelineVerdictPreservationFormalized, true);
  assert.equal(out.leanConcretePipelineInternalOutputHandoffComposed, true);
  assert.equal(out.leanConcretePipelineTerminalOutputPackingFormalized, true);
  assert.equal(out.leanConcretePipelineTerminalOutputPackerAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineTerminalOutputPackerAuditedDeclarationCount, 69);
  assert.equal(out.leanConcretePipelineTerminalOutputPackerConnectedToBridgeEndpointFormalized, true);
  assert.equal(out.leanConcretePipelineTerminalBridgeAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineTerminalBridgeAuditedDeclarationCount, 59);
  assert.equal(out.leanConcretePipelinePriorTraceTransportToTerminalBridgeFormalized, true);
  assert.equal(out.leanConcretePipelinePairedCompilerAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelinePairedCompilerAuditedDeclarationCount, 28);
  assert.equal(out.leanConcretePipelineCanonicalPairCompilationFormalized, true);
  assert.equal(out.leanConcretePipelineCompilerAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineCompilerAuditedDeclarationCount, 29);
  assert.equal(out.leanConcretePipelineAllInputCompilationFormalized, true);
  assert.equal(out.leanConcretePipelineInputFramerAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineInputFramerAuditedDeclarationCount, 70);
  assert.equal(out.leanConcretePipelineAllInputFramingFormalized, true);
  assert.equal(out.leanConcretePipelineMalformedInputBehaviorFormalized, true);
  assert.equal(out.leanConcretePipelineRawRefinementFormalized, true);
  assert.equal(out.leanConcretePipelineRefinementAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineRefinementAuditedDeclarationCount, 16);
  assert.equal(out.leanConcreteFunctionProgramRecursiveCompilationFormalized, true);
  assert.equal(out.leanConcreteDecisionProgramRecursiveCompilationFormalized, true);
  assert.equal(out.leanConcretePolynomialTimeDeciderRawCompilationFormalized, true);
  assert.equal(out.leanConcretePipelineExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanNANDDirectWireCoreFormalized, true);
  assert.equal(out.leanNANDDirectWireCoreAxiomAuditPassed, true);
  assert.equal(out.leanNANDEnumeratorFormalized, true);
  assert.equal(out.leanNANDEnumeratorAxiomAuditPassed, true);
  assert.equal(out.leanNANDExactWidthEnumerationComplete, true);
  assert.equal(out.leanNANDEnumeratorUsesOrderedGatePairs, true);
  assert.equal(out.leanNANDEnumeratorIncludesUniqueEmptyOutputTuple, true);
  assert.equal(out.leanNANDEnumeratorDeduplicated, false);
  assert.equal(out.leanNANDTruthTableFormalized, true);
  assert.equal(out.leanNANDTruthTableAxiomAuditPassed, true);
  assert.equal(out.leanNANDSemanticEquivalenceDecidable, true);
  assert.equal(out.leanNANDMinimumAndSlackFormalized, true);
  assert.equal(out.leanNANDReferenceMinimumFormalized, true);
  assert.equal(out.leanNANDReferenceMinimumAxiomAuditPassed, true);
  assert.equal(out.leanNANDReferenceMinimumExhaustive, true);
  assert.equal(out.leanNANDReferenceMinimumScope, 'finite-boolean-direct-wire-empty-profile');
  assert.equal(out.leanNANDReferenceMinimumPolynomialRuntimeProved, false);
  assert.equal(out.leanNANDResidualSlackZeroIffMinimumFormalized, true);
  assert.equal(out.leanNANDCompositionFormalized, true);
  assert.equal(out.leanNANDCompositionAxiomAuditPassed, true);
  assert.equal(out.leanNANDFramedReplacementFormalized, true);
  assert.equal(out.leanNANDFramedGlobalSlackLawFormalized, true);
  assert.equal(out.leanNANDFramedSlackAxiomAuditPassed, true);
  assert.equal(out.leanNANDReplacementScope, 'concrete-serial-framed-context');
  assert.equal(out.leanLockedNANDDirectCandidatesFormalized, true);
  assert.equal(out.leanLockedNANDDirectAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDInternalMacroConstantsAbsent, true);
  assert.equal(out.leanDirectWireOutputLowerBoundFormalized, true);
  assert.equal(out.leanDirectWireBaselineAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDSourceDerivedCountsFormalized, true);
  assert.equal(out.leanLockedNANDBaselineAccountingFormalized, true);
  assert.equal(out.leanLockedNANDBaselineAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDConditionalSquareBaselineExactnessFormalized, true);
  assert.equal(out.leanLockedNANDLocalBaselineConditionsFormalized, true);
  assert.equal(out.leanLockedNANDLocalSquareBaselineExactnessFormalized, true);
  assert.equal(out.leanLockedNANDLocalBaselineAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDProofScope, 'typed-local-macros-source-derived-counts-and-five-local-square-baselines');
  assert.equal(out.leanLockedNANDConditionalThresholdBoundaryFormalized, true);
  assert.equal(out.leanLockedNANDConditionalResidualSlackAtMostFourFormalized, true);
  assert.equal(out.leanLockedNANDThresholdBoundaryAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDThresholdBoundaryScope, 'proof-bearing-typed-candidate-and-semantic-premises-only');
  assert.equal(out.leanLockedNANDThresholdBoundaryPremisesInstantiated, false);
  assert.equal(out.leanLockedNANDGlobalBaselineDistinctFormalized, false);
  assert.equal(out.leanLockedNANDCarrierLayoutFormalized, false);
  assert.equal(out.leanLockedNANDTraceEquivalenceFormalized, false);
  assert.equal(out.leanLockedNANDDerivedFinalOutputLawsFormalized, false);
  assert.equal(out.leanLockedNANDResidualSlackAtMostFourFormalized, false);
  assert.equal(out.leanLockedNANDPolynomialBuilderFormalized, false);
  assert.equal(out.leanCompatibleReplacementFormalized, false);
  assert.equal(out.leanGlobalSlackLawFormalized, false);
  assert.equal(out.leanLockedNANDBuilderFormalized, false);
  assert.equal(out.leanLockedNANDThresholdFormalized, false);
  for (const field of [
    'leanResidualRoutesListedGainScanFormalized',
    'leanResidualRoutesAxiomAuditPassed',
    'leanResidualRoutesGainSoundnessFormalized',
    'leanResidualRoutesStrictResidualDescentFormalized',
    'leanResidualRoutesExactResultProofBearing',
    'leanResidualRoutesZeroSlackResultProofBearing',
    'leanResidualRoutesUnresolvedFailClosed',
  ]) assert.equal(out[field], true, field);
  assert.equal(out.leanResidualRoutesScope, 'explicit-caller-supplied-finite-candidate-list');
  for (const field of [
    'leanResidualRoutesCandidateListCompletenessFormalized',
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanZeroSlackPositiveSlackContradictionFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
    'leanResidualBandMinimizerFormalized',
  ]) assert.equal(out[field], false, field);
  assert.equal(out.rootLeanTheoremPresent, false);
  assert.equal(out.rootLeanTheoremBuilt, false);
  assert.equal(out.rootLeanTheoremAxiomAuditPassed, false);
  assert.equal(out.projectSpecificAxiomsRemaining, true);
  assert.deepEqual(out.projectSpecificAxiomInventory, [
    'PNP.CheckPCCPackexp',
    'PNP.GeneratePCCPack',
    'PNP.LockedNANDThreshold',
    'PNP.ResidualBandExactMinimization',
  ]);
  assert.equal(out.externalReviewIsMathematicalPremise, false);
  assert.deepEqual(out.remainingBlockers, FORMAL_RECONSTRUCTION_BLOCKERS0);
  assert.equal(out.remainingBlockers.length, 6);
  assert.equal(out.remainingBlockers.includes('Formal.ConcreteComplexityMachineLink'), false);
  assert.equal(out.remainingBlockers.includes('Formal.PinnedLeanBuildAndRootTarget'), false);
  assert.match(out.statusSha256, /^[0-9a-f]{64}$/u);
  assert.match(out.siteStatusSha256, /^[0-9a-f]{64}$/u);
});

test('formal reconstruction status pins the recursive refinement inventory and source closure', async () => {
  const status = await currentStatus0();
  assert.equal(status.leanTheoremInventoryDeclarationCount, 5828);
  assert.equal(status.leanTheoremInventoryTheoremCount, 2454);
  assert.equal(status.leanTheoremInventoryAssumptionFreeTheoremCount, 2344);
  assert.equal(status.leanTheoremInventoryExcludedPrivateDeclarationCount, 1042);
  assert.equal(status.leanTheoremInventorySourceClosureModuleCount, 55);
  assert.equal(status.leanSourceClosureSha256,
    '2614476660c4d0ef7480ddcb55847879284d71a0bc5570390a5d6fcc9cb50f09');
  const machine = status.formalPublicationMilestones.find(
    (entry) => entry.id === 'concrete-machine-cost-kernel',
  );
  assert.equal(machine.status, 'formalized-foundation-only');
  assert.equal(machine.earned, true);
  for (const name of [
    'PNP.Concrete.PipelineCompiler.pipeline_correct',
    'PNP.Concrete.PipelineCompiler.pipeline_boundedDecide_eq',
    'PNP.Concrete.PipelineCompiler.pipeline_machineOutput_eq',
    'PNP.Concrete.PipelineCompiler.pipeline_ne_timeout',
    'PNP.Concrete.PipelineCompiler.pipeline_accepts_iff',
    'PNP.Concrete.PipelineCompiler.pipeline_timeout_of_stuck_rawRunExact',
    'PNP.Concrete.PipelineCompiler.pipelineOutputSizeBound_eval',
    'PNP.Concrete.PipelineCompiler.suppliedTraceRawSteps_le_pipelineRawTimeBound',
    'PNP.Concrete.PipelineSequentialStateNamespace.findWorkRule_sequential_first_of_some',
    'PNP.Concrete.PipelineSequentialStateNamespace.findWorkRule_sequential_second_of_some',
    'PNP.Concrete.PipelineSequentialStateNamespace.firstAcceptLaunch_workStep',
    'PNP.Concrete.PipelineSequentialStateNamespace.firstPipelineState_ne_secondPipelineState',
    'PNP.Concrete.PipelineSequentialStateNamespace.firstRejectLaunch_workStep',
    'PNP.Concrete.PipelineSequentialStateNamespace.sequentialWorkMachine_acceptState_ne_rejectState',
    'PNP.Concrete.PipelineSequentialCompiler.acceptingSequentialTrace_workRunExact_of_rawRunExact',
    'PNP.Concrete.PipelineSequentialCompiler.firstOutputSizeBound_eval',
    'PNP.Concrete.PipelineSequentialCompiler.firstTraceAndLaunch_workRunExact_of_rawRunExact',
    'PNP.Concrete.PipelineSequentialCompiler.rejectingSequentialTrace_workRunExact_of_rawRunExact',
    'PNP.Concrete.PipelineSequentialCompiler.run_sequential_accept_at_bound_of_rawRunExact',
    'PNP.Concrete.PipelineSequentialCompiler.run_sequential_reject_at_bound_of_rawRunExact',
    'PNP.Concrete.PipelineSequentialCompiler.sequentialOutputSizeBound_eval',
    'PNP.Concrete.PipelineSequentialCompiler.sequentialRawSteps_le_of_rawRunExact',
    'PNP.Concrete.PipelineSequentialCompiler.sequentialRawSteps_le_sequentialRawTimeBound',
    'PNP.Concrete.PipelineSequentialCompiler.sequential_accepts_iff',
    'PNP.Concrete.PipelineSequentialCompiler.sequential_boundedDecide_eq',
    'PNP.Concrete.PipelineSequentialCompiler.sequential_correct',
    'PNP.Concrete.PipelineSequentialCompiler.sequential_machineOutput_eq',
    'PNP.Concrete.PipelineSequentialCompiler.sequential_ne_timeout',
    'PNP.Concrete.PipelineSequentialCompiler.sequential_timeout_of_stuck_first_rawRunExact',
    'PNP.Concrete.FunctionProgram.RawRefinement.compile_haltsWithin',
    'PNP.Concrete.FunctionProgram.RawRefinement.compile_output_eq',
    'PNP.Concrete.DecisionProgram.RawRefinement.compile_haltsWithin',
    'PNP.Concrete.DecisionProgram.RawRefinement.compile_verdict_eq',
    'PNP.Concrete.PolynomialTimeDecider.compileToMachine_accepts_iff',
  ]) assert.equal(machine.requiredTheorems.includes(name), true, name);
  for (const name of [
    'PNP.Concrete.PipelineInputFramer.boundedDecide_compileTotalInputFramer_accept',
    'PNP.Concrete.PipelineInputFramer.boundedDecide_compileTotalInputFramer_ne_timeout',
    'PNP.Concrete.PipelineInputFramer.run_compileTotalInputFramer_encoded_rawTimeBound',
    'PNP.Concrete.PipelineInputFramer.run_compileTotalInputFramer_rawTimeBound_blankEquivalent',
    'PNP.Concrete.PipelineInputFramer.totalInputFramerFinal_isHalted',
    'PNP.Concrete.PipelineInputFramer.totalInputFramerFinal_represents',
    'PNP.Concrete.PipelineInputFramer.totalInputFramerRawTimeBound_le',
    'PNP.Concrete.PipelineInputFramer.totalInputFramer_workRunExact',
  ]) assert.equal(machine.requiredTheorems.includes(name), true, name);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.workRunExact_three_of_step'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_of_step'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.workRunExact_three_mul_of_rawRunExact'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_mul_of_rawRunExact'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.liftMachine_isHalted_eq_of_representsConfiguration'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.rawRunExact?_exists_le_run'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.workRun_three_mul_of_run_halted'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_mul_of_run_halted'), true);
  for (const name of [
    'PNP.Concrete.PipelineStageBridges.inputLaunch_workStep',
    'PNP.Concrete.PipelineStageBridges.acceptingLaunch_workStep',
    'PNP.Concrete.PipelineStageBridges.rejectingLaunch_workStep',
    'PNP.Concrete.PipelineStageBridges.bridgedWorkSteps_eq',
    'PNP.Concrete.PipelineStageBridges.workBoundedDecide_bridged_accept_of_rawRunExact',
    'PNP.Concrete.PipelineStageBridges.workBoundedDecide_bridged_reject_of_rawRunExact',
    'PNP.Concrete.PipelineStageBridges.workBoundedDecide_bridged_timeout_of_stuck_rawRunExact',
    'PNP.Concrete.PipelineStageBridges.run_compileBridgedMachine_accept_of_rawRunExact',
    'PNP.Concrete.PipelineStageBridges.run_compileBridgedMachine_reject_of_rawRunExact',
    'PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_workRunExact',
    'PNP.Concrete.TerminalOutputPacker.terminalOutputPackerFinal_isHalted',
    'PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_output_eq',
    'PNP.Concrete.TerminalOutputPacker.run_compileTerminalOutputPacker_exact',
    'PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_runtime_le',
    'PNP.Concrete.TerminalOutputPacker.run_compileTerminalOutputPacker',
    'PNP.Concrete.TerminalOutputPacker.machineOutput_compileTerminalOutputPacker_eq',
    'PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_one_step_short_timeout',
    'PNP.Concrete.PipelineTerminalBridge.acceptingPackerLaunch_workStep',
    'PNP.Concrete.PipelineTerminalBridge.acceptingSuppliedTrace_workRunExact_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.acceptingTerminalFinal_isHalted',
    'PNP.Concrete.PipelineTerminalBridge.acceptingTerminal_workRunExact_of_represents',
    'PNP.Concrete.PipelineTerminalBridge.bridged_workRunExact_of_exact',
    'PNP.Concrete.PipelineTerminalBridge.bridged_workStep?_of_some',
    'PNP.Concrete.PipelineTerminalBridge.findWorkRule_terminalBridge_acceptingPacker_of_some',
    'PNP.Concrete.PipelineTerminalBridge.findWorkRule_terminalBridge_rejectingPacker_of_some',
    'PNP.Concrete.PipelineTerminalBridge.machineOutput_compileTerminalBridge_accept_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.machineOutput_compileTerminalBridge_reject_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.outputBits_compileTerminalBridge_accepting_of_represents',
    'PNP.Concrete.PipelineTerminalBridge.outputBits_compileTerminalBridge_rejecting_of_represents',
    'PNP.Concrete.PipelineTerminalBridge.rejectingPackerLaunch_workStep',
    'PNP.Concrete.PipelineTerminalBridge.rejectingSuppliedTrace_workRunExact_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.rejectingTerminalFinal_isHalted',
    'PNP.Concrete.PipelineTerminalBridge.rejectingTerminal_workRunExact_of_represents',
    'PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_accept_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_accepting_of_represents',
    'PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_accepting_of_represents_at_bound',
    'PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_reject_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_rejecting_of_represents',
    'PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_rejecting_of_represents_at_bound',
    'PNP.Concrete.PipelineTerminalBridge.simulationPrefix_terminalBridge_workBoundedDecide_timeout',
    'PNP.Concrete.PipelineTerminalBridge.suppliedTraceTerminalWorkSteps_eq',
    'PNP.Concrete.PipelineTerminalBridge.terminalBridgeMachine_acceptState_ne_rejectState',
    'PNP.Concrete.PipelineTerminalBridge.terminalBridge_runtime_le',
    'PNP.Concrete.PipelineTerminalBridge.workBoundedDecide_terminalBridge_accept_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.workBoundedDecide_terminalBridge_reject_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.workBoundedDecide_terminalBridge_timeout_of_stuck_rawRunExact',
    'PNP.Concrete.PipelinePairedCompiler.machineOutput_length_le_input_add_fuel',
    'PNP.Concrete.PipelinePairedCompiler.outputBits_length_le_pairedPipelineOutputSizeBound_of_rawRunExact',
    'PNP.Concrete.PipelinePairedCompiler.pairedPipelineOutputSizeBound_eval',
    'PNP.Concrete.PipelinePairedCompiler.pairedPipeline_accepts_iff',
    'PNP.Concrete.PipelinePairedCompiler.pairedPipeline_boundedDecide_eq',
    'PNP.Concrete.PipelinePairedCompiler.pairedPipeline_correct_on_pair',
    'PNP.Concrete.PipelinePairedCompiler.pairedPipeline_machineOutput_eq',
    'PNP.Concrete.PipelinePairedCompiler.pairedPipeline_ne_timeout',
    'PNP.Concrete.PipelinePairedCompiler.run_pairedPipeline_accept_at_bound_of_rawRunExact',
    'PNP.Concrete.PipelinePairedCompiler.run_pairedPipeline_reject_at_bound_of_rawRunExact',
    'PNP.Concrete.PipelinePairedCompiler.suppliedTraceTerminalRawSteps_le_of_rawRunExact',
    'PNP.Concrete.PipelinePairedCompiler.suppliedTraceTerminalRawSteps_le_pairedPipelineRawTimeBound',
  ]) assert.equal(machine.requiredTheorems.includes(name), true, name);
  assert.match(machine.scope, /One literal finite four-stage pipeline handles every raw bitstring/u);
  assert.match(machine.scope, /exactly 4 work steps on empty input/u);
  assert.match(machine.scope, /6 \* m \* m \+ 39 \* m \+ 75/u);
  assert.match(machine.scope, /PipelineCompiler preserves one raw target's verdict and ordinary output/u);
  assert.match(machine.scope, /PipelineSequentialCompiler composes two raw targets/u);
  assert.match(machine.scope, /R\(m\) = PipelineRaw\(p\)\(m\) \+ 6 \+ PipelineRaw\(q\)\(m \+ p\(m\) \+ 1\)/u);
  assert.match(machine.scope, /PipelineRefinement recursively applies that compiler/u);
  assert.match(machine.scope, /16 audited declarations have empty axiom closure/u);
  assert.match(machine.nonClaim, /closes the concrete complexity machine-link blocker only/u);
  assert.match(machine.nonClaim, /P = NP/u);
  const cnf = status.formalPublicationMilestones.find(
    (entry) => entry.id === 'concrete-cnf-universal-verifier',
  );
  assert.equal(cnf.status, 'formalized-np-membership-only');
  assert.equal(cnf.earned, true);
  assert.equal(cnf.requiredTheorems.includes(
    'PNP.Concrete.FinalUniversalDesign.cnfSATInNP'), true);
  for (const command of [
    'node --test audits/lean-concrete-pipeline-input-framer0.test.mjs',
    'node --test audits/lean-concrete-pipeline-output-handoff0.test.mjs',
    'node --test audits/lean-concrete-pipeline-state-namespace0.test.mjs',
    'node --test audits/lean-concrete-pipeline-sequential-state-namespace0.test.mjs',
    'node --test audits/lean-concrete-pipeline-stage-bridges0.test.mjs',
    'node --test audits/lean-concrete-terminal-output-packer0.test.mjs',
    'node --test audits/lean-concrete-pipeline-terminal-bridge0.test.mjs',
    'node --test audits/lean-concrete-pipeline-paired-compiler0.test.mjs',
    'node --test audits/lean-concrete-pipeline-compiler0.test.mjs',
    'node --test audits/lean-concrete-pipeline-sequential-compiler0.test.mjs',
    'node --test audits/lean-concrete-pipeline-machine-simulation0.test.mjs',
    'node --test audits/lean-concrete-pipeline-tape-geometry0.test.mjs',
    'node --test audits/lean-concrete-tape-handoff0.test.mjs',
    'node --test audits/lean-concrete-pipeline-refinement0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineInputFramerAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineOutputHandoffAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineStateNamespaceAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineSequentialStateNamespaceAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineStageBridgesAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteTerminalOutputPackerAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineTerminalBridgeAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelinePairedCompilerAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcretePipelinePairedCompiler.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineCompilerAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcretePipelineCompiler.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineSequentialCompilerAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcretePipelineSequentialCompiler.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineMachineSimulationAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineTapeGeometryAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteTapeHandoffAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineRefinementAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcretePipelineRefinementRecursive.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCNFWorkAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCNFWorkCanonical.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteWorkCompilerEdges.lean',
    'lake env lean -DwarningAsError=true --run lean-regression/PNPConcreteCNFWorkCanonicalExtended.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCNFWorkExhaustive.lean',
  ]) assert.equal(status.verificationCommands.includes(command), true, command);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PNP.Concrete.FinalUniversalDesign.cnfSATInNP')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'exact successful prefix of length k at most F')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineInputFramer is one literal finite machine for every raw bitstring')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineOutputHandoff is one literal finite machine for an already represented internal tape')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineTerminalBridge preserves the earlier ordinary-input trace')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'stuck-endpoint timeout')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineStateNamespace remains the injective renaming and lookup-isolation prerequisite')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineSequentialStateNamespace nests two complete component machines')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineSequentialCompiler composes both exact executions')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineStageBridges proves exact framer-to-simulator and accept/reject-to-handoff launches')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'TerminalOutputPacker is a literal finite work machine')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineTerminalBridge is one literal extended finite work machine')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelinePairedCompiler remains the sharper canonical-pair theorem')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineCompiler extracts that prefix internally on every raw bitstring')), true);
});

test('formal status records the exhaustive direct-wire reference minimum conservatively', async () => {
  const status = await currentStatus0();

  assert.equal(status.publicSurfaceBaselineCoordinate, 'PUBLIC-SURFACE-BASELINE-2026-07-14-COOK-LEVIN-LOCAL-CNF-35');
  assert.equal(status.leanNANDDirectWireCoreFormalized, true);
  assert.equal(status.leanNANDDirectWireCoreAxiomAuditPassed, true);
  assert.equal(status.leanNANDEnumeratorFormalized, true);
  assert.equal(status.leanNANDEnumeratorAxiomAuditPassed, true);
  assert.equal(status.leanNANDExactWidthEnumerationComplete, true);
  assert.equal(status.leanNANDEnumeratorUsesOrderedGatePairs, true);
  assert.equal(status.leanNANDEnumeratorIncludesUniqueEmptyOutputTuple, true);
  assert.equal(status.leanNANDEnumeratorDeduplicated, false);
  assert.equal(status.leanNANDTruthTableFormalized, true);
  assert.equal(status.leanNANDTruthTableAxiomAuditPassed, true);
  assert.equal(status.leanNANDSemanticEquivalenceDecidable, true);
  assert.equal(status.leanNANDMinimumAndSlackFormalized, true);
  assert.equal(status.leanNANDReferenceMinimumFormalized, true);
  assert.equal(status.leanNANDReferenceMinimumAxiomAuditPassed, true);
  assert.equal(status.leanNANDReferenceMinimumExhaustive, true);
  assert.equal(status.leanNANDReferenceMinimumScope, 'finite-boolean-direct-wire-empty-profile');
  assert.equal(status.leanNANDReferenceMinimumPolynomialRuntimeProved, false);
  assert.equal(status.leanNANDResidualSlackZeroIffMinimumFormalized, true);
  assert.equal(status.leanNANDCompositionFormalized, true);
  assert.equal(status.leanNANDCompositionAxiomAuditPassed, true);
  assert.equal(status.leanNANDFramedReplacementFormalized, true);
  assert.equal(status.leanNANDFramedGlobalSlackLawFormalized, true);
  assert.equal(status.leanNANDFramedSlackAxiomAuditPassed, true);
  assert.equal(status.leanNANDReplacementScope, 'concrete-serial-framed-context');
  assert.equal(status.leanLockedNANDDirectCandidatesFormalized, true);
  assert.equal(status.leanLockedNANDDirectAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDInternalMacroConstantsAbsent, true);
  assert.equal(status.leanDirectWireOutputLowerBoundFormalized, true);
  assert.equal(status.leanDirectWireBaselineAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDSourceDerivedCountsFormalized, true);
  assert.equal(status.leanLockedNANDBaselineAccountingFormalized, true);
  assert.equal(status.leanLockedNANDBaselineAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDConditionalSquareBaselineExactnessFormalized, true);
  assert.equal(status.leanLockedNANDLocalBaselineConditionsFormalized, true);
  assert.equal(status.leanLockedNANDLocalSquareBaselineExactnessFormalized, true);
  assert.equal(status.leanLockedNANDLocalBaselineAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDConditionalThresholdBoundaryFormalized, true);
  assert.equal(status.leanLockedNANDConditionalResidualSlackAtMostFourFormalized, true);
  assert.equal(status.leanLockedNANDThresholdBoundaryAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDThresholdBoundaryScope, 'proof-bearing-typed-candidate-and-semantic-premises-only');
  assert.equal(status.leanLockedNANDThresholdBoundaryPremisesInstantiated, false);
  assert.equal(status.leanLockedNANDGlobalBaselineDistinctFormalized, false);
  assert.equal(status.leanLockedNANDCarrierLayoutFormalized, false);
  assert.equal(status.leanLockedNANDTraceEquivalenceFormalized, false);
  assert.equal(status.leanLockedNANDDerivedFinalOutputLawsFormalized, false);
  assert.equal(status.leanLockedNANDResidualSlackAtMostFourFormalized, false);
  assert.equal(status.leanLockedNANDPolynomialBuilderFormalized, false);
  assert.equal(status.leanCompatibleReplacementFormalized, false);
  assert.equal(status.leanGlobalSlackLawFormalized, false);
  assert.equal(status.leanLockedNANDBuilderFormalized, false);
  assert.equal(status.leanLockedNANDThresholdFormalized, false);
  assert.equal(status.leanResidualRoutesListedGainScanFormalized, true);
  assert.equal(status.leanResidualRoutesAxiomAuditPassed, true);
  assert.equal(status.leanResidualRoutesGainSoundnessFormalized, true);
  assert.equal(status.leanResidualRoutesStrictResidualDescentFormalized, true);
  assert.equal(status.leanResidualRoutesExactResultProofBearing, true);
  assert.equal(status.leanResidualRoutesZeroSlackResultProofBearing, true);
  assert.equal(status.leanResidualRoutesUnresolvedFailClosed, true);
  assert.equal(status.leanResidualRoutesScope, 'explicit-caller-supplied-finite-candidate-list');
  assert.equal(status.leanResidualRoutesCandidateListCompletenessFormalized, false);
  assert.equal(status.leanResidualRoutesGlobalGainCompletenessFormalized, false);
  assert.equal(status.leanZeroSlackPositiveSlackContradictionFormalized, false);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinLoopExactnessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.leanResidualBandMinimizerFormalized, false);
  assert.equal(status.nonClaims.some((entry) => entry.includes('direct-wire NAND semantics layer does not by itself prove enumeration')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('reference-minimum computation has no polynomial-runtime claim')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('concrete serial framed-context construction')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('do not prove global cross-instance BaselineDistinct')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('baseline coordinates remain present alongside one final coordinate')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('honest source-derived baseline/displayed counts are 86/90')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('is not the report threshold theorem')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('conditional on that six-field premise package')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('arbitrary satisfiable proposition and baseline natural number')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('complete only for the explicit finite implementation list')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('empty-list scan is formally shown')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('never manufactured by the executable gain scanner')), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-nand-semantics0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-nand-enumerator0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-nand-reference-minimum0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-locked-nand-baseline0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-locked-nand-threshold-boundary0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-routes0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDSemanticsAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDEnumeratorAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDTruthTableAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDMinimumAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDCompositionAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDSlackAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDDirectAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPDirectWireBaselineAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDBaselineAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDLocalBaselineAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDThresholdBoundaryAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualRoutesAxiomAudit.lean'), true);
  assert.deepEqual(status.lockedNANDThresholdHostileReviewLemmaInventory, [
    'DirectWireOutputLowerBound',
    'MacroDistinct',
    'TraceEquivalence',
    'ZeroOutputConvention',
    'FinalLockSeparation',
  ]);
  assert.deepEqual(status.leanLockedNANDThresholdPremiseInventory, [
    'baselineCandidate',
    'fullCandidate',
    'baselineConditions',
    'initialOutputsPreserved',
    'unsatisfiableFinalZero',
    'satisfiableFinalConditions',
  ]);
  assert.deepEqual(status.leanLockedNANDThresholdMissingInstantiationInventory,
    status.leanLockedNANDThresholdPremiseInventory);
  assert.equal(status.remainingBlockers.includes('Formal.LockedNANDThreshold'), true);
});

test('formal status records a pinned Lean library root without claiming a root theorem', async () => {
  const status = await currentStatus0();

  assert.equal(status.leanToolchain, 'leanprover/lean4:v4.31.0');
  assert.equal(status.leanBuildTarget, 'PNP');
  assert.equal(status.leanRootModule, 'PNP');
  assert.equal(status.leanRootStatusDeclaration, 'PNP.Main.rootTheoremStatus');
  assert.equal(status.leanBuildConfigurationPinned, true);
  assert.equal(status.explicitLeanRootTargetPresent, true);
  assert.equal(status.leanLibraryTargetBuilt, true);
  assert.equal(status.leanSourcePlaceholderAuditPassed, true);
  assert.equal(status.rootLeanTheorem, 'PNP.Main.p_eq_np');
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.rootLeanTheoremBuilt, false);
  assert.equal(status.rootLeanTheoremAxiomAuditPassed, false);
  assert.equal(status.projectSpecificAxiomsRemaining, true);
  assert.equal(status.sorryOrAdmitInRootDependencyClosure, null);
  assert.equal(status.nonClaims.some((entry) => entry.includes('root-status build is reconstruction data')), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-root-target0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake build PNP'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPBridgeAxiomAudit.lean'), true);
});

test('formal status separates current-authority and historical replay workflows', async () => {
  const status = await currentStatus0();
  const names = (await readdir(new URL('../.github/workflows/', import.meta.url)))
    .filter((name) => name.endsWith('.yml'))
    .sort()
    .map((name) => `.github/workflows/${name}`);

  assert.deepEqual([
    ...status.activeCoreWorkflows,
    ...status.historicalReplayWorkflows,
  ].sort(), names);
  assert.deepEqual(status.historicalReplayWorkflows, ['.github/workflows/legacy-v0-replay.yml']);
  assert.equal(status.activeCoreWorkflows.includes('.github/workflows/legacy-v0-replay.yml'), false);
});

test('formal status designates only the pinned legacy-v0 archive replay', async () => {
  const status = await currentStatus0();
  assert.equal(status.legacyCheckerArchiveManifest, 'archive/legacy-v0/ARCHIVE.json');
  assert.equal(status.legacyCheckerArchiveCheckCommand, 'npm run legacy:v0:check');
  assert.equal(status.legacyCheckerReplayCommand, 'npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d');
  assert.equal(status.nonClaims.some((entry) => entry.includes('neither current theorem authority nor a mathematical proof')), true);
});

test('formal reconstruction status rejects theorem emission activation', async () => {
  const status = await currentStatus0();
  status.publicTheoremEmissionAllowed = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'publicTheoremEmissionAllowed']);
});

test('formal reconstruction status rejects an unearned root theorem', async () => {
  const status = await currentStatus0();
  status.rootLeanTheoremPresent = true;
  status.rootLeanTheoremBuilt = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'rootLeanTheoremPresent']);
});

test('formal reconstruction status rejects weakened or broadened direct CNF status', async () => {
  for (const [field, value] of [
    ['leanConcreteCNFVerifierCorrectnessFormalized', false],
    ['leanConcreteCNFVerifierNoTimeoutFormalized', false],
    ['leanConcreteCNFVerifierAxiomAuditPassed', false],
    ['leanConcreteCNFWorkAxiomAuditPassed', false],
    ['leanConcreteCNFSATMembershipFormalized', false],
    ['leanConcreteCNFSATInPFormalized', true],
    ['leanConcreteCNFNPCompletenessFormalized', true],
    ['leanConcreteCNFSATMembershipTheorem', 'PNP.Main.p_eq_np'],
  ]) {
    const status = await currentStatus0();
    status[field] = value;
    const out = await CheckFormalReconstructionStatus0({
      writeOutput: false,
      statusOverride: status,
      siteOverride: status,
    });
    assert.equal(out.tag, 'reject', field);
    assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});

test('formal reconstruction status rejects a drifting Lean toolchain pin', async () => {
  const status = await currentStatus0();
  status.leanToolchain = 'leanprover/lean4:stable';
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'leanToolchain']);
});

test('formal reconstruction status rejects a disabled Lean placeholder audit', async () => {
  const status = await currentStatus0();
  status.leanSourcePlaceholderAuditPassed = false;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'leanSourcePlaceholderAuditPassed']);
});

test('formal reconstruction status rejects disabling the audited direct-wire NAND core', async () => {
  const status = await currentStatus0();
  status.leanNANDDirectWireCoreAxiomAuditPassed = false;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'leanNANDDirectWireCoreAxiomAuditPassed']);
});

test('formal reconstruction status rejects disabling an earned NAND enumerator property', async () => {
  const fields = [
    'leanNANDEnumeratorFormalized',
    'leanNANDEnumeratorAxiomAuditPassed',
    'leanNANDExactWidthEnumerationComplete',
    'leanNANDEnumeratorUsesOrderedGatePairs',
    'leanNANDEnumeratorIncludesUniqueEmptyOutputTuple',
    'leanNANDTruthTableFormalized',
    'leanNANDTruthTableAxiomAuditPassed',
    'leanNANDSemanticEquivalenceDecidable',
    'leanNANDMinimumAndSlackFormalized',
    'leanNANDReferenceMinimumFormalized',
    'leanNANDReferenceMinimumAxiomAuditPassed',
    'leanNANDReferenceMinimumExhaustive',
    'leanNANDResidualSlackZeroIffMinimumFormalized',
    'leanNANDCompositionFormalized',
    'leanNANDCompositionAxiomAuditPassed',
    'leanNANDFramedReplacementFormalized',
    'leanNANDFramedGlobalSlackLawFormalized',
    'leanNANDFramedSlackAxiomAuditPassed',
    'leanLockedNANDDirectCandidatesFormalized',
    'leanLockedNANDDirectAxiomAuditPassed',
    'leanLockedNANDInternalMacroConstantsAbsent',
    'leanDirectWireOutputLowerBoundFormalized',
    'leanDirectWireBaselineAxiomAuditPassed',
    'leanLockedNANDSourceDerivedCountsFormalized',
    'leanLockedNANDBaselineAccountingFormalized',
    'leanLockedNANDBaselineAxiomAuditPassed',
    'leanLockedNANDConditionalSquareBaselineExactnessFormalized',
    'leanLockedNANDLocalBaselineConditionsFormalized',
    'leanLockedNANDLocalSquareBaselineExactnessFormalized',
    'leanLockedNANDLocalBaselineAxiomAuditPassed',
    'leanLockedNANDConditionalThresholdBoundaryFormalized',
    'leanLockedNANDConditionalResidualSlackAtMostFourFormalized',
    'leanLockedNANDThresholdBoundaryAxiomAuditPassed',
    'leanResidualRoutesListedGainScanFormalized',
    'leanResidualRoutesAxiomAuditPassed',
    'leanResidualRoutesGainSoundnessFormalized',
    'leanResidualRoutesStrictResidualDescentFormalized',
    'leanResidualRoutesExactResultProofBearing',
    'leanResidualRoutesZeroSlackResultProofBearing',
    'leanResidualRoutesUnresolvedFailClosed',
  ];

  for (const field of fields) {
    const status = await currentStatus0();
    status[field] = false;
    const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
    assert.equal(out.tag, 'reject', field);
    assert.equal(out.coord, 'FormalReconstructionStatus.Field', field);
    assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});

test('formal reconstruction status rejects unearned broad downstream NAND claims', async () => {
  const fields = [
    'leanNANDEnumeratorDeduplicated',
    'leanNANDReferenceMinimumPolynomialRuntimeProved',
    'leanLockedNANDGlobalBaselineDistinctFormalized',
    'leanLockedNANDThresholdBoundaryPremisesInstantiated',
    'leanLockedNANDCarrierLayoutFormalized',
    'leanLockedNANDTraceEquivalenceFormalized',
    'leanLockedNANDDerivedFinalOutputLawsFormalized',
    'leanLockedNANDResidualSlackAtMostFourFormalized',
    'leanLockedNANDPolynomialBuilderFormalized',
    'leanCompatibleReplacementFormalized',
    'leanGlobalSlackLawFormalized',
    'leanLockedNANDBuilderFormalized',
    'leanLockedNANDThresholdFormalized',
    'leanResidualRoutesCandidateListCompletenessFormalized',
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanZeroSlackPositiveSlackContradictionFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
    'leanResidualBandMinimizerFormalized',
  ];

  for (const field of fields) {
    const status = await currentStatus0();
    status[field] = true;
    const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
    assert.equal(out.tag, 'reject', field);
    assert.equal(out.coord, 'FormalReconstructionStatus.Field', field);
    assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});

test('formal reconstruction status rejects removing the locked NAND threshold blocker', async () => {
  const status = await currentStatus0();
  status.remainingBlockers = status.remainingBlockers.filter((entry) => entry !== 'Formal.LockedNANDThreshold');
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Blockers');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'remainingBlockers']);
});

test('formal reconstruction status rejects legacy locked-NAND quarantine drift', async () => {
  for (const [field, replacement] of [
    ['legacySyntheticLockedNANDM2FixtureStatus', 'accepted'],
    ['legacySyntheticLockedNANDM2HonestBaseline', 91],
    ['legacySyntheticLockedNANDM2MetadataConsistentBaseline', 91],
    ['legacySyntheticLockedNANDM2StoredBaseline', 86],
    ['legacySyntheticLockedNANDM2HonestDisplayedGateCount', 95],
    ['legacySyntheticLockedNANDM2MetadataConsistentDisplayedGateCount', 95],
    ['legacySyntheticLockedNANDM2StoredDisplayedGateCount', 90],
    ['lockedNANDOutputConvention', 'single-output'],
  ]) {
    const status = await currentStatus0();
    status[field] = replacement;
    const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
    assert.equal(out.tag, 'reject', field);
    assert.equal(out.coord, 'FormalReconstructionStatus.Field', field);
    assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});

test('formal reconstruction status rejects threshold-boundary inventory drift', async () => {
  for (const field of [
    'lockedNANDThresholdHostileReviewLemmaInventory',
    'leanLockedNANDThresholdPremiseInventory',
    'leanLockedNANDThresholdMissingInstantiationInventory',
  ]) {
    const status = await currentStatus0();
    status[field] = status[field].slice(0, -1);
    const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
    assert.equal(out.tag, 'reject', field);
    assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});

test('formal reconstruction status rejects a hidden project-specific axiom', async () => {
  const status = await currentStatus0();
  status.projectSpecificAxiomInventory = status.projectSpecificAxiomInventory.slice(0, -1);
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.ProjectSpecificAxiomInventory');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'projectSpecificAxiomInventory']);
});

test('formal reconstruction status rejects external review as a theorem premise', async () => {
  const status = await currentStatus0();
  status.externalReviewIsMathematicalPremise = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'externalReviewIsMathematicalPremise']);
});

test('formal reconstruction status rejects hidden formal blockers', async () => {
  const status = await currentStatus0();
  status.remainingBlockers = [];
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Blockers');
});

test('formal reconstruction status rejects a drifting public mirror', async () => {
  const status = await currentStatus0();
  const site = { ...status, nonClaims: [...status.nonClaims, 'drift'] };
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: site });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.NonClaims');
  assert.deepEqual(out.path, ['public/pnp-status.json', 'nonClaims']);
});

test('formal reconstruction status rejects formatting-only public mirror drift', async () => {
  const status = await currentStatus0();
  const statusText = `${JSON.stringify(status, null, 2)}\n`;
  const siteText = JSON.stringify(status);
  const out = await CheckFormalReconstructionStatus0({
    writeOutput: false,
    statusBytesOverride: statusText,
    siteBytesOverride: siteText,
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.SiteMirrorMismatch');
  assert.deepEqual(out.path, ['public/pnp-status.json']);
});

test('formal reconstruction status rejects unknown theorem authority fields', async () => {
  const status = await currentStatus0();
  status.publicTheoremEmissionAllowedByLegacyRoute = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Keys');
  assert.deepEqual(out.witness.extraKeys, ['publicTheoremEmissionAllowedByLegacyRoute']);
});

test('formal reconstruction status rejects reintroduced upload commands', async () => {
  const status = await currentStatus0();
  status.verificationCommands.push('npm run pnp:verify:upload');
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Commands');
});

test('formal reconstruction status rejects contradictory non-claims', async () => {
  const status = await currentStatus0();
  status.nonClaims.push('P = NP is established by another route.');
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.NonClaims');
});

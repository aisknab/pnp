import { createHash } from 'node:crypto';
import { lstat, readFile, readdir } from 'node:fs/promises';
import path from 'node:path';

export const LEAN_INVENTORY_PATH0 = 'status/LEAN_THEOREM_INVENTORY.json';
export const LEAN_INVENTORY_PUBLIC_PATH0 = 'public/pnp-theorem-inventory.json';
export const FORMAL_PUBLICATION_MAP_PATH0 = 'publication/FORMAL_PUBLICATION_MAP.json';
const REQUIRED_PUBLICATION_MAP_SHA2560 = '3e94ad852ebc0c6f28ac0156c9cabe61f2e78f698dfbf18f5d7d52854a7f6f07';

export const REQUIRED_MILESTONE_THEOREMS0 = Object.freeze([
  'PNP.Concrete.BitString.decodePair_pair',
  'PNP.Concrete.CookLevin.BoundedLiteral.emit_variable_lt',
  'PNP.Concrete.CookLevin.FixedTableauInstance.exists_accepting_iff_boundedDecide_accept',
  'PNP.Concrete.CookLevin.FixedTableauInstance.tableauVerdict_of_valid',
  'PNP.Concrete.CookLevin.FixedTableauInstance.valid_iff_eq_canonical',
  'PNP.Concrete.CookLevin.LocalConstraint.emit_holds_iff',
  'PNP.Concrete.CookLevin.LocalProgram.emitted_clause_count',
  'PNP.Concrete.CookLevin.LocalProgram.toFormula_satisfiable_iff',
  'PNP.Concrete.CookLevin.LocalProgram.toFormula_satisfied_iff',
  'PNP.Concrete.CookLevin.VariableLayout.certificateBitVariable_lt_variableCount',
  'PNP.Concrete.CookLevin.VariableLayout.certificateBitVariable_ne_certificateLengthVariable',
  'PNP.Concrete.CookLevin.VariableLayout.certificateLengthVariable_lt_variableCount',
  'PNP.Concrete.CookLevin.VariableLayout.headVariable_lt_variableCount',
  'PNP.Concrete.CookLevin.VariableLayout.headVariable_ne_stateVariable',
  'PNP.Concrete.CookLevin.VariableLayout.stateVariable_lt_variableCount',
  'PNP.Concrete.CookLevin.VariableLayout.stateVariable_ne_certificateBitVariable',
  'PNP.Concrete.CookLevin.VariableLayout.symbolVariable_lt_variableCount',
  'PNP.Concrete.CookLevin.VariableLayout.symbolVariable_ne_headVariable',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.FiniteRow.next_represents_advance',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.actualFuel_le_uniformFuel',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.actualFuel_ne_timeout',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.certificateBitWidth_eq_of_paired',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.certificateLengthWidth_eq_of_paired',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.certificateOf_certificate',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.decode_encodedFormula',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.decodedInitialRow_eq_paired',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.decodedRow_next',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.decodedTableau_transitions',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.dimensions_encodedInputLength',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.dimensions_timeBound',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormulaSizePolynomial_eval',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff_finiteAccepting',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff_language',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormula_size_le',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.exists_accepting_iff_program_accept',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.findRule_some_mem',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.finiteRun_head_bounds',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.finiteRun_represents_run',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formulaBitSchedule_emit_eq_encodedFormula',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formulaBitSchedule_length',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formulaClauseSchedule_emit_eq_formulaClauses',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formulaClauseSchedule_length',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formulaConstraintCountPolynomial_eval',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formulaConstraintSchedule_emit_eq_program',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formulaConstraintSchedule_length',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formulaTokenSchedule_length',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formulaVariableCountPolynomial_eval',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formula_clauseCount',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formula_clauseCount_le_formulaClauseCountPolynomial',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formula_clause_length_le',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formula_satisfiable_iff',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formula_satisfiable_iff_finiteAccepting',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formula_satisfied_iff',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.formula_wellScoped',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.hasFiniteAccepting_iff_language',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.initialCellAtCoordinate_eq_initialCellAt',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.language_iff_exists_acceptingTableau',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.pairedInitialRowFor_represents',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.program_length_le_formulaConstraintCountPolynomial',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.rawInput_size_le',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.tableauAssignment_transitionProgram_holds',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.tableauVerdict_eq_program_of_valid',
  'PNP.Concrete.CookLevin.VerifierTableauProblem.uniformFuel_verdict_eq',
  'PNP.Concrete.CookLevin.assignmentAt_assignmentOf',
  'PNP.Concrete.CookLevin.atLeastOneClause_satisfied_iff',
  'PNP.Concrete.CookLevin.canonicalTableau_valid',
  'PNP.Concrete.CookLevin.encodeCNF_size_exact',
  'PNP.Concrete.CookLevin.encodeCNF_size_le',
  'PNP.Concrete.CookLevin.eval_encodedInputPolynomial',
  'PNP.Concrete.CookLevin.eval_tapeWidthPolynomial',
  'PNP.Concrete.CookLevin.exactlyOneBoundedClauses_holds_iff',
  'PNP.Concrete.CookLevin.excludePairClause_not_satisfied_of_both_true',
  'PNP.Concrete.CookLevin.implicationClauses_holds_iff',
  'PNP.Concrete.CookLevin.localProgram_formula_wellScoped',
  'PNP.Concrete.CookLevin.machine_acceptState_lt_bound',
  'PNP.Concrete.CookLevin.machine_rejectState_lt_bound',
  'PNP.Concrete.CookLevin.machine_startState_lt_bound',
  'PNP.Concrete.CookLevin.rule_source_lt_machineStateBound',
  'PNP.Concrete.CookLevin.rule_target_lt_machineStateBound',
  'PNP.Concrete.CookLevin.run_pad_of_halted',
  'PNP.Concrete.CookLevin.run_pad_of_stuck',
  'PNP.Concrete.CookLevin.run_succ_eq_run_advance',
  'PNP.Concrete.CookLevin.tableauEndpoint_of_valid',
  'PNP.Concrete.CookLevin.trace_length',
  'PNP.Concrete.CookLevin.validTableau_iff_eq_trace',
  'PNP.Concrete.CookLevin.verifierEncodedInput_size_le',
  'PNP.Concrete.DecisionProgram.RawRefinement.compile_haltsWithin',
  'PNP.Concrete.DecisionProgram.RawRefinement.compile_verdict_eq',
  'PNP.Concrete.FinalUniversalDesign.cnfCompiled_accept_iff_check',
  'PNP.Concrete.FinalUniversalDesign.cnfCompiled_ne_timeout',
  'PNP.Concrete.FinalUniversalDesign.cnfCompiled_reject_iff_check_false',
  'PNP.Concrete.FinalUniversalDesign.cnfConcreteVerifier_decision',
  'PNP.Concrete.FinalUniversalDesign.cnfConcreteVerifier_inputMode',
  'PNP.Concrete.FinalUniversalDesign.cnfSATInNP',
  'PNP.Concrete.FinalUniversalDesign.cnfUniversalWorkOutcome',
  'PNP.Concrete.FinalUniversalDesign.formulaGrammarOutcome',
  'PNP.Concrete.FunctionProgram.RawRefinement.compile_haltsWithin',
  'PNP.Concrete.FunctionProgram.RawRefinement.compile_output_eq',
  'PNP.Concrete.FunctionProgram.RawRefinement.output_size_le',
  'PNP.Concrete.NatPolynomial.eval_mono',
  'PNP.Concrete.PipelineCompiler.acceptingSuppliedTrace_workRunExact_of_rawRunExact',
  'PNP.Concrete.PipelineCompiler.outputBits_length_le_pipelineOutputSizeBound_of_rawRunExact',
  'PNP.Concrete.PipelineCompiler.pipelineOutputSizeBound_eval',
  'PNP.Concrete.PipelineCompiler.pipeline_accepts_iff',
  'PNP.Concrete.PipelineCompiler.pipeline_boundedDecide_eq',
  'PNP.Concrete.PipelineCompiler.pipeline_correct',
  'PNP.Concrete.PipelineCompiler.pipeline_machineOutput_eq',
  'PNP.Concrete.PipelineCompiler.pipeline_ne_timeout',
  'PNP.Concrete.PipelineCompiler.pipeline_timeout_of_stuck_rawRunExact',
  'PNP.Concrete.PipelineCompiler.rejectingSuppliedTrace_workRunExact_of_rawRunExact',
  'PNP.Concrete.PipelineCompiler.run_pipeline_accept_at_bound_of_rawRunExact',
  'PNP.Concrete.PipelineCompiler.run_pipeline_reject_at_bound_of_rawRunExact',
  'PNP.Concrete.PipelineCompiler.suppliedTraceRawSteps_le_of_rawRunExact',
  'PNP.Concrete.PipelineCompiler.suppliedTraceRawSteps_le_pipelineRawTimeBound',
  'PNP.Concrete.PipelineCompiler.totalInputLaunch_workStep',
  'PNP.Concrete.PipelineInputFramer.boundedDecide_compilePairedInputFramer_accept',
  'PNP.Concrete.PipelineInputFramer.boundedDecide_compileTotalInputFramer_accept',
  'PNP.Concrete.PipelineInputFramer.boundedDecide_compileTotalInputFramer_ne_timeout',
  'PNP.Concrete.PipelineInputFramer.pairedInputFramerFinal_isHalted',
  'PNP.Concrete.PipelineInputFramer.pairedInputFramerFinal_represents',
  'PNP.Concrete.PipelineInputFramer.pairedInputFramerRawTimeBound_exact',
  'PNP.Concrete.PipelineInputFramer.pairedInputFramer_workRunExact',
  'PNP.Concrete.PipelineInputFramer.run_compilePairedInputFramer_rawTimeBound',
  'PNP.Concrete.PipelineInputFramer.run_compileTotalInputFramer_encoded_rawTimeBound',
  'PNP.Concrete.PipelineInputFramer.run_compileTotalInputFramer_rawTimeBound_blankEquivalent',
  'PNP.Concrete.PipelineInputFramer.totalInputFramerFinal_isHalted',
  'PNP.Concrete.PipelineInputFramer.totalInputFramerFinal_represents',
  'PNP.Concrete.PipelineInputFramer.totalInputFramerRawTimeBound_le',
  'PNP.Concrete.PipelineInputFramer.totalInputFramer_workRunExact',
  'PNP.Concrete.PipelineMachineSimulation.findIndexedRawRuleFrom_map_snd',
  'PNP.Concrete.PipelineMachineSimulation.find_liftMachine_entry',
  'PNP.Concrete.PipelineMachineSimulation.liftMachine_isHalted_eq_of_representsConfiguration',
  'PNP.Concrete.PipelineMachineSimulation.rawRunExact?_exists_le_run',
  'PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_mul_of_rawRunExact',
  'PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_mul_of_run_halted',
  'PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_of_step',
  'PNP.Concrete.PipelineMachineSimulation.workRunExact_three_mul_of_rawRunExact',
  'PNP.Concrete.PipelineMachineSimulation.workRunExact_three_of_step',
  'PNP.Concrete.PipelineMachineSimulation.workRun_three_mul_of_run_halted',
  'PNP.Concrete.PipelineOutputHandoff.framedOutputHandoffFinal_isHalted',
  'PNP.Concrete.PipelineOutputHandoff.framedOutputHandoffRawTimeBound_exact',
  'PNP.Concrete.PipelineOutputHandoff.framedOutputHandoff_workRunExact_of_represents',
  'PNP.Concrete.PipelineOutputHandoff.run_compileFramedOutputHandoff_of_represents',
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
  'PNP.Concrete.PipelineSequentialStateNamespace.findWorkRule_sequential_first_of_some',
  'PNP.Concrete.PipelineSequentialStateNamespace.findWorkRule_sequential_second_of_some',
  'PNP.Concrete.PipelineSequentialStateNamespace.firstAcceptLaunch_workStep',
  'PNP.Concrete.PipelineSequentialStateNamespace.firstPipelineState_ne_secondPipelineState',
  'PNP.Concrete.PipelineSequentialStateNamespace.firstRejectLaunch_workStep',
  'PNP.Concrete.PipelineSequentialStateNamespace.sequentialWorkMachine_acceptState_ne_rejectState',
  'PNP.Concrete.PipelineStageBridges.acceptingHandoffState_ne_rejectingHandoffState',
  'PNP.Concrete.PipelineStageBridges.acceptingLaunch_workStep',
  'PNP.Concrete.PipelineStageBridges.bridgedAccept_workRunExact_of_rawRunExact',
  'PNP.Concrete.PipelineStageBridges.bridgedReject_workRunExact_of_rawRunExact',
  'PNP.Concrete.PipelineStageBridges.bridgedWorkSteps_eq',
  'PNP.Concrete.PipelineStageBridges.findWorkRule_bridged_acceptingHandoff_of_some',
  'PNP.Concrete.PipelineStageBridges.findWorkRule_bridged_input_of_some',
  'PNP.Concrete.PipelineStageBridges.findWorkRule_bridged_rejectingHandoff_of_some',
  'PNP.Concrete.PipelineStageBridges.findWorkRule_bridged_simulation_of_some',
  'PNP.Concrete.PipelineStageBridges.inputLaunch_workStep',
  'PNP.Concrete.PipelineStageBridges.rejectingLaunch_workStep',
  'PNP.Concrete.PipelineStageBridges.run_compileBridgedMachine_accept_of_rawRunExact',
  'PNP.Concrete.PipelineStageBridges.run_compileBridgedMachine_reject_of_rawRunExact',
  'PNP.Concrete.PipelineStageBridges.workBoundedDecide_bridged_accept_of_rawRunExact',
  'PNP.Concrete.PipelineStageBridges.workBoundedDecide_bridged_reject_of_rawRunExact',
  'PNP.Concrete.PipelineStageBridges.workBoundedDecide_bridged_timeout_of_stuck_rawRunExact',
  'PNP.Concrete.PipelineStateNamespace.findWorkRule_composedRules_handoff',
  'PNP.Concrete.PipelineStateNamespace.findWorkRule_composedRules_input',
  'PNP.Concrete.PipelineStateNamespace.findWorkRule_composedRules_simulation',
  'PNP.Concrete.PipelineStateNamespace.findWorkRule_rename',
  'PNP.Concrete.PipelineStateNamespace.renamedInputFramer_workRunExact',
  'PNP.Concrete.PipelineStateNamespace.renamedLiftMachine_workRunExact_of_rawRunExact',
  'PNP.Concrete.PipelineStateNamespace.renamedOutputHandoff_workRunExact_of_represents',
  'PNP.Concrete.PipelineStateNamespace.stageState_injective',
  'PNP.Concrete.PipelineStateNamespace.workBoundedDecide_rename',
  'PNP.Concrete.PipelineStateNamespace.workRunExact?_rename',
  'PNP.Concrete.PipelineTape.frameWithGarbage_represents',
  'PNP.Concrete.PipelineTape.handoffTarget_withGarbage_represents',
  'PNP.Concrete.PipelineTape.represents_expandLeft_of_nil',
  'PNP.Concrete.PipelineTape.represents_expandRight_of_nil',
  'PNP.Concrete.PipelineTape.represents_moveLeft_of_cons',
  'PNP.Concrete.PipelineTape.represents_moveRight_of_cons',
  'PNP.Concrete.PipelineTape.represents_write',
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
  'PNP.Concrete.PolynomialTimeDecider.compileToMachine_accepts_iff',
  'PNP.Concrete.PolynomialTimeMachine.verdict_accepts_iff',
  'PNP.Concrete.PolynomialTimeMachine.verdict_ne_timeout',
  'PNP.Concrete.Tape.outputBits_handoffTarget',
  'PNP.Concrete.Tape.outputBits_moveRight_moveLeft',
  'PNP.Concrete.Tape.outputBits_ofInput',
  'PNP.Concrete.Tape.outputBits_right_append_blank',
  'PNP.Concrete.Tape.symbolAt_moveLeft',
  'PNP.Concrete.Tape.symbolAt_moveRight',
  'PNP.Concrete.TerminalOutputPacker.machineOutput_compileTerminalOutputPacker_eq',
  'PNP.Concrete.TerminalOutputPacker.run_compileTerminalOutputPacker',
  'PNP.Concrete.TerminalOutputPacker.run_compileTerminalOutputPacker_exact',
  'PNP.Concrete.TerminalOutputPacker.terminalOutputPackerFinal_isHalted',
  'PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_one_step_short_timeout',
  'PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_output_eq',
  'PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_runtime_le',
  'PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_workRunExact',
  'PNP.Concrete.np_complete_in_p_implies_p_eq_np',
  'PNP.Concrete.p_subset_np',
  'PNP.Concrete.reduction_comp',
  'PNP.Concrete.reduction_refl',
  'PNP.Concrete.reduction_transports_p',
  'PNP.Concrete.run_succ',
  'PNP.Concrete.run_zero',
  'PNP.DirectWire.ConditionalThresholdBoundaryPremises.fullResidualSlack_le_four',
  'PNP.DirectWire.ConditionalThresholdBoundaryPremises.satisfiable_iff_minimum_ge_succ',
  'PNP.DirectWire.Equivalent.trans',
  'PNP.DirectWire.StrictEquivalentGain.strictResidualDescent',
  'PNP.DirectWire.andCircuit_spec',
  'PNP.DirectWire.compatibleReplacement_framed',
  'PNP.DirectWire.constantOneDirect_referenceMinimum',
  'PNP.DirectWire.constantZeroDirect_referenceMinimum',
  'PNP.DirectWire.equalityDirect_referenceMinimum',
  'PNP.DirectWire.equivalentBool_eq_true_iff',
  'PNP.DirectWire.exactWidthEnumeration_complete',
  'PNP.DirectWire.firstListedGain_none_no_listed_gain',
  'PNP.DirectWire.firstListedGain_sound',
  'PNP.DirectWire.framedGlobalSlackLaw',
  'PNP.DirectWire.lockedBaselineCount_report_formula',
  'PNP.DirectWire.nandCircuit_spec',
  'PNP.DirectWire.prefixAndDirect_referenceMinimum',
  'PNP.DirectWire.referenceMinimum_invariant',
  'PNP.DirectWire.residualSlack_eq_zero_iff_minimum',
  'PNP.DirectWire.strictEquivalentGainBool_complete',
  'PNP.DirectWire.traceDirect_referenceMinimum',
  'PNP.DirectWire.unresolved_positiveSlack_regression',
  'PNP.Main.concretePEqualsNP_iff',
]);

export const REQUIRED_PROJECT_AXIOMS0 = Object.freeze([
  'PNP.CheckPCCPackexp',
  'PNP.GeneratePCCPack',
  'PNP.LockedNANDThreshold',
  'PNP.ResidualBandExactMinimization',
]);

export function sha256Text0(value) {
  return createHash('sha256').update(value, 'utf8').digest('hex');
}

export function MilestoneTheoremKernelTypeSha2560(name, kernelType) {
  if (typeof name !== 'string' || typeof kernelType !== 'string') {
    throw new Error('milestone theorem kernel fingerprint requires a name and compiled type');
  }
  return kernelFingerprint0(`milestone-theorem-type:${name}`, kernelType);
}

export function stableStringify0(value) {
  if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`;
  if (isObject0(value)) {
    return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`;
  }
  return JSON.stringify(value);
}

export function ValidateLeanTheoremInventory0(inventory) {
  if (!isObject0(inventory)) throw new Error('Lean theorem inventory must be an object');
  if (inventory.kind !== 'PNPLeanTheoremInventory0' || inventory.version !== 0) {
    throw new Error('Lean theorem inventory kind/version mismatch');
  }
  if (inventory.coordinate !== 'PNP-LEAN-THEOREM-INVENTORY-2026-07-15-41') {
    throw new Error('Lean theorem inventory coordinate mismatch');
  }
  if (inventory.leanToolchain !== 'leanprover/lean4:v4.31.0' || inventory.rootModule !== 'PNP') {
    throw new Error('Lean theorem inventory toolchain/root mismatch');
  }
  if (inventory.environmentProbeComplete !== true) throw new Error('Lean environment probe is incomplete');
  if (!Array.isArray(inventory.declarations)) throw new Error('Lean theorem declarations must be an array');
  const names = inventory.declarations.map((entry) => entry?.name);
  if (names.some((name) => typeof name !== 'string') || !strictlySorted0(names)) {
    throw new Error('Lean theorem declarations must have unique lexically sorted names');
  }
  for (const entry of inventory.declarations) {
    if (!isObject0(entry) || typeof entry.module !== 'string' || !entry.module.startsWith('PNP')) {
      throw new Error(`invalid module for declaration ${entry?.name ?? '<unknown>'}`);
    }
    if (!['axiom', 'definition', 'theorem', 'opaque', 'quotient', 'inductive', 'constructor', 'recursor'].includes(entry.kind)) {
      throw new Error(`invalid declaration kind for ${entry.name}`);
    }
    if (!Array.isArray(entry.axioms) || !strictlySorted0(entry.axioms)) {
      throw new Error(`axioms must be unique and sorted for ${entry.name}`);
    }
  }
  const theoremRows = inventory.declarations.filter((entry) => entry.kind === 'theorem');
  const axiomRows = inventory.declarations.filter((entry) => entry.kind === 'axiom');
  if (inventory.declarationCount !== inventory.declarations.length
      || inventory.theoremCount !== theoremRows.length
      || inventory.axiomCount !== axiomRows.length
      || inventory.assumptionFreeTheoremCount !== theoremRows.filter((entry) => entry.axioms.length === 0).length) {
    throw new Error('Lean theorem inventory counts do not match declaration rows');
  }
  const actualKindCounts = Object.fromEntries(
    ['axiom', 'constructor', 'definition', 'inductive', 'opaque', 'quotient', 'recursor', 'theorem']
      .map((kind) => [kind, inventory.declarations.filter((entry) => entry.kind === kind).length]),
  );
  if (stableStringify0(inventory.declarationKindCounts) !== stableStringify0(actualKindCounts)) {
    throw new Error('Lean declaration-kind counts do not match declaration rows');
  }
  const actualModules = [...new Set(inventory.declarations.map((entry) => entry.module))].sort();
  if (inventory.sourceClosureModuleCount !== actualModules.length
      || stableStringify0(inventory.sourceClosureModules) !== stableStringify0(actualModules)) {
    throw new Error('Lean source-closure module inventory mismatch');
  }
  if (!Number.isInteger(inventory.excludedPrivateDeclarationCount)
      || inventory.excludedPrivateDeclarationCount < 0) {
    throw new Error('Lean excluded-private declaration count is invalid');
  }
  if (stableStringify0(inventory.projectAxioms) !== stableStringify0(REQUIRED_PROJECT_AXIOMS0)) {
    throw new Error('Lean project axiom inventory must remain the disclosed four-axiom set');
  }
  if (stableStringify0(inventory.projectAxioms) !== stableStringify0(axiomRows.map((entry) => entry.name))) {
    throw new Error('Lean project axiom side inventory drifted from compiled axiom declaration rows');
  }
  if (inventory.compatibilityRootName !== 'PNP.Main.p_eq_np'
      || inventory.concreteTargetName !== 'PNP.Main.ConcretePEqualsNP') {
    throw new Error('Lean publication declaration names mismatch');
  }
  validateDetailedCandidate0(inventory.compatibilityRootCandidate, inventory.compatibilityRootName, inventory.declarations);
  validateDetailedCandidate0(inventory.concreteTargetCandidate, inventory.concreteTargetName, inventory.declarations);
  if (!Array.isArray(inventory.milestoneCandidates)) {
    throw new Error('reviewed milestone theorem candidates must be an array');
  }
  const milestoneNames = inventory.milestoneCandidates.map((candidate) => candidate?.name);
  if (stableStringify0(milestoneNames) !== stableStringify0(REQUIRED_MILESTONE_THEOREMS0)) {
    throw new Error('reviewed milestone theorem candidate inventory mismatch');
  }
  for (const candidate of inventory.milestoneCandidates) {
    validateDetailedCandidate0(candidate, candidate.name, inventory.declarations);
    if (candidate.kind !== 'theorem' || candidate.kernelValue !== null) {
      throw new Error(`reviewed milestone candidate is not a theorem: ${candidate.name}`);
    }
  }
  return inventory;
}

export async function CollectLeanSourceFiles0(root) {
  const repositoryRoot = path.resolve(root);
  const leanRoot = path.join(repositoryRoot, 'lean');
  const leanRootInfo = await lstat(leanRoot);
  if (leanRootInfo.isSymbolicLink() || !leanRootInfo.isDirectory()) {
    throw new Error('Lean source root must be a real directory');
  }
  const files = [];
  async function walk0(directory) {
    const entries = await readdir(directory, { withFileTypes: true });
    entries.sort((left, right) => left.name < right.name ? -1 : left.name > right.name ? 1 : 0);
    for (const entry of entries) {
      const absolute = path.join(directory, entry.name);
      const relative = path.relative(repositoryRoot, absolute);
      if (relative === '' || relative === '..' || relative.startsWith(`..${path.sep}`)
          || path.isAbsolute(relative)) {
        throw new Error(`Lean source path escaped repository root: ${absolute}`);
      }
      if (entry.isSymbolicLink()) throw new Error(`Lean source path must not be a symlink: ${relative}`);
      if (entry.isDirectory()) await walk0(absolute);
      else if (entry.isFile() && entry.name.endsWith('.lean')) files.push(relative.split(path.sep).join('/'));
    }
  }
  await walk0(leanRoot);
  return files.sort((left, right) => left < right ? -1 : left > right ? 1 : 0);
}

export async function ComputeLeanSourceClosureSha2560(root, inventoryInput) {
  ValidateLeanTheoremInventory0(inventoryInput);
  const leanSourceFiles = await CollectLeanSourceFiles0(root);
  const files = [...new Set([
    'lean-toolchain',
    'lakefile.lean',
    'lake-manifest.json',
    'lean-audit/PNPTheoremInventory.lean',
    ...leanSourceFiles,
  ])].sort();
  const hash = createHash('sha256');
  hash.update('PNP-LEAN-SOURCE-CLOSURE-v0\n', 'utf8');
  for (const relative of files) {
    const bytes = await readFile(path.join(root, relative));
    hash.update(`${relative}\n${bytes.length}\n`, 'utf8');
    hash.update(bytes);
    hash.update('\n', 'utf8');
  }
  return hash.digest('hex');
}

export function DeriveFormalPublication0(inventoryInput, publicationMap, inventoryBytes, sourceClosureSha256 = null) {
  const inventory = ValidateLeanTheoremInventory0(inventoryInput);
  validatePublicationMap0(publicationMap);
  if (!(Buffer.isBuffer(inventoryBytes) || inventoryBytes instanceof Uint8Array)) {
    throw new Error('Lean theorem inventory digest input must be bytes');
  }
  const canonicalInventoryBytes = Buffer.from(`${stableStringify0(inventory)}\n`, 'utf8');
  if (!canonicalInventoryBytes.equals(Buffer.from(inventoryBytes))) {
    throw new Error('Lean theorem inventory bytes do not match the validated canonical inventory');
  }
  const inventorySha256 = createHash('sha256').update(canonicalInventoryBytes).digest('hex');
  const declarations = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const milestoneCandidates = new Map(
    inventory.milestoneCandidates.map((candidate) => [candidate.name, candidate]),
  );
  const profile = publicationMap.gate;
  const root = inventory.compatibilityRootCandidate;
  const target = inventory.concreteTargetCandidate;
  const targetTypeSha256 = target ? kernelFingerprint0('concrete-target-type', target.kernelType) : null;
  const targetValueSha256 = target?.kernelValue ? kernelFingerprint0('concrete-target-value', target.kernelValue) : null;
  const rootTypeSha256 = root ? kernelFingerprint0('publication-root-type', root.kernelType) : null;
  const axiomClosure = [...new Set([...(target?.axioms ?? []), ...(root?.axioms ?? [])])].sort();
  const axiomClosureSha256 = kernelFingerprint0('publication-axiom-closure', stableStringify0(axiomClosure));
  const expectedExactRootType = `Lean.Expr.const \`${profile.concreteTargetName} []`;
  const allowedAxioms = new Set(profile.allowedLeanStandardAxioms);
  const subchecks = Object.freeze({
    standardComplexityModelEligible: profile.standardComplexityModelEligible === true,
    concreteTargetPresent: target !== null,
    concreteTargetIsDefinition: target?.kind === 'definition',
    concreteTargetKernelTypeFingerprintConfigured: isSha2560(profile.expectedConcreteTargetKernelTypeSha256),
    concreteTargetKernelTypeFingerprintMatches: isSha2560(profile.expectedConcreteTargetKernelTypeSha256)
      && targetTypeSha256 === profile.expectedConcreteTargetKernelTypeSha256,
    concreteTargetKernelValueFingerprintConfigured: isSha2560(profile.expectedConcreteTargetKernelValueSha256),
    concreteTargetKernelValueFingerprintMatches: isSha2560(profile.expectedConcreteTargetKernelValueSha256)
      && targetValueSha256 === profile.expectedConcreteTargetKernelValueSha256,
    compatibilityRootPresent: root !== null,
    compatibilityRootIsTheorem: root?.kind === 'theorem',
    compatibilityRootHasExactConcreteType: root?.kernelType === expectedExactRootType,
    compatibilityRootKernelTypeFingerprintConfigured: isSha2560(profile.expectedRootKernelTypeSha256),
    compatibilityRootKernelTypeFingerprintMatches: isSha2560(profile.expectedRootKernelTypeSha256)
      && rootTypeSha256 === profile.expectedRootKernelTypeSha256,
    axiomClosureFingerprintConfigured: isSha2560(profile.expectedAxiomClosureSha256),
    axiomClosureFingerprintMatches: isSha2560(profile.expectedAxiomClosureSha256)
      && axiomClosureSha256 === profile.expectedAxiomClosureSha256,
    sourceClosureFingerprintConfigured: isSha2560(profile.expectedSourceClosureSha256),
    sourceClosureFingerprintMatches: isSha2560(profile.expectedSourceClosureSha256)
      && sourceClosureSha256 === profile.expectedSourceClosureSha256,
    axiomClosureUsesOnlyLeanStandardAllowlist: target !== null && root !== null
      && axiomClosure.every((name) => allowedAxioms.has(name)),
  });
  const passed = Object.values(subchecks).every((value) => value === true);
  const gate = Object.freeze({
    kind: 'PNPConcretePublicationGate0',
    version: 0,
    compatibilityRootName: profile.compatibilityRootName,
    concreteTargetName: profile.concreteTargetName,
    expectedConcreteTargetKernelTypeSha256: profile.expectedConcreteTargetKernelTypeSha256,
    expectedConcreteTargetKernelValueSha256: profile.expectedConcreteTargetKernelValueSha256,
    expectedRootKernelTypeSha256: profile.expectedRootKernelTypeSha256,
    expectedAxiomClosureSha256: profile.expectedAxiomClosureSha256,
    expectedSourceClosureSha256: profile.expectedSourceClosureSha256,
    actualConcreteTargetKernelTypeSha256: targetTypeSha256,
    actualConcreteTargetKernelValueSha256: targetValueSha256,
    actualRootKernelTypeSha256: rootTypeSha256,
    actualAxiomClosureSha256: axiomClosureSha256,
    actualSourceClosureSha256: sourceClosureSha256,
    axiomClosure,
    allowedLeanStandardAxioms: [...profile.allowedLeanStandardAxioms],
    abstractPEqualsNPIsPublicationIneligible: true,
    unsetFingerprintIsIntentionalFailClosedMigrationGate: true,
    subchecks,
    passed,
  });
  const milestones = publicationMap.milestones.map((spec) => {
    const theoremRows = spec.requiredTheorems.map((name) => declarations.get(name) ?? null);
    const detailedRows = spec.requiredTheorems.map((name) => milestoneCandidates.get(name) ?? null);
    const expectedTypeHashes = spec.requiredTheorems.map(
      (name) => publicationMap.earnedMilestoneTheoremKernelTypeSha256[name] ?? null,
    );
    const actualTypeHashes = detailedRows.map((entry) => entry === null
      ? null
      : MilestoneTheoremKernelTypeSha2560(entry.name, entry.kernelType));
    const allPresent = theoremRows.every((entry) => entry?.kind === 'theorem');
    const allAssumptionFree = allPresent && theoremRows.every((entry) => entry.axioms.length === 0);
    const axiomClosureUsesOnlyLeanStandardAllowlist = allPresent
      && theoremRows.every((entry) => entry.axioms.every((name) => allowedAxioms.has(name)));
    const allKernelTypesMatch = detailedRows.every((entry, index) => entry !== null
      && isSha2560(expectedTypeHashes[index])
      && actualTypeHashes[index] === expectedTypeHashes[index]);
    const sourceClosureFingerprintMatches = isSha2560(publicationMap.milestoneSourceClosureSha256)
      && sourceClosureSha256 === publicationMap.milestoneSourceClosureSha256;
    const earned = spec.classification.startsWith('formalized')
      && axiomClosureUsesOnlyLeanStandardAllowlist
      && allKernelTypesMatch
      && sourceClosureFingerprintMatches;
    return Object.freeze({
      ...spec,
      theoremRows: theoremRows.map((entry, index) => ({
        name: spec.requiredTheorems[index],
        present: entry !== null,
        kind: entry?.kind ?? null,
        axioms: entry?.axioms ?? null,
        actualKernelTypeSha256: actualTypeHashes[index],
        expectedKernelTypeSha256: expectedTypeHashes[index],
        kernelTypeFingerprintMatches: actualTypeHashes[index] !== null
          && actualTypeHashes[index] === expectedTypeHashes[index],
      })),
      allPresent,
      allAssumptionFree,
      axiomClosureUsesOnlyLeanStandardAllowlist,
      allKernelTypesMatch,
      sourceClosureFingerprintMatches,
      earned,
      status: earned ? spec.classification : 'not-formalized',
    });
  });
  const emitted = passed;
  const emissionFields = Object.freeze({
    mathematicalTheoremEstablished: emitted,
    publicTheoremEmissionAllowed: emitted,
    publicTheoremStatement: emitted ? 'P = NP' : null,
    publicTheoremConclusion: emitted ? 'P = NP' : null,
    finalTheoremReady: emitted,
    internalFinalTheoremReady: emitted,
    unrestrictedFinalSoundnessDischarged: emitted,
    uniformFinalSoundnessProved: emitted,
    satInPConclusionAccepted: emitted,
    pEqualsNPConclusionAccepted: emitted,
  });
  return Object.freeze({ inventorySha256, gate, milestones, emissionFields });
}

function validateDetailedCandidate0(candidate, name, declarations) {
  const row = declarations.find((entry) => entry.name === name) ?? null;
  if (candidate === null) {
    if (row !== null) throw new Error(`missing detailed candidate for ${name}`);
    return;
  }
  if (!isObject0(candidate) || candidate.name !== name || row === null) {
    throw new Error(`invalid detailed candidate for ${name}`);
  }
  if (candidate.module !== row.module || candidate.kind !== row.kind
      || stableStringify0(candidate.axioms) !== stableStringify0(row.axioms)
      || typeof candidate.kernelType !== 'string'
      || !(candidate.kernelValue === null || typeof candidate.kernelValue === 'string')) {
    throw new Error(`detailed candidate drift for ${name}`);
  }
}

function validatePublicationMap0(map) {
  if (!isObject0(map) || map.kind !== 'PNPFormalPublicationMap0' || map.version !== 0
      || !isObject0(map.gate) || !Array.isArray(map.milestones)) {
    throw new Error('formal publication map shape mismatch');
  }
  if (map.coordinate !== 'PNP-FORMAL-PUBLICATION-MAP-2026-07-15-41') {
    throw new Error('formal publication map coordinate mismatch');
  }
  if (map.gate.compatibilityRootName !== 'PNP.Main.p_eq_np'
      || map.gate.concreteTargetName !== 'PNP.Main.ConcretePEqualsNP'
      || map.gate.standardComplexityModelEligible !== true) {
    throw new Error('formal publication map must retain the fail-closed concrete gate');
  }
  if (stableStringify0(map.gate.allowedLeanStandardAxioms)
      !== stableStringify0(['Classical.choice', 'Quot.sound', 'propext'])) {
    throw new Error('Lean standard axiom allowlist is immutable and may not be caller-expanded');
  }
  for (const field of [
    'expectedConcreteTargetKernelTypeSha256',
    'expectedConcreteTargetKernelValueSha256',
    'expectedRootKernelTypeSha256',
    'expectedAxiomClosureSha256',
    'expectedSourceClosureSha256',
  ]) if (map.gate[field] !== null) throw new Error(`${field} must remain intentionally unset in release 41`);
  if (!isSha2560(map.milestoneSourceClosureSha256)
      || !isObject0(map.earnedMilestoneTheoremKernelTypeSha256)) {
    throw new Error('reviewed milestone theorem/source fingerprints are missing');
  }
  const formalizedTheoremNames = [...new Set(map.milestones
    .filter((milestone) => milestone?.classification?.startsWith('formalized'))
    .flatMap((milestone) => milestone.requiredTheorems ?? []))]
    .sort((left, right) => left < right ? -1 : left > right ? 1 : 0);
  if (stableStringify0(formalizedTheoremNames) !== stableStringify0(REQUIRED_MILESTONE_THEOREMS0)) {
    throw new Error('reviewed milestone theorem names drifted from the compiled candidate contract');
  }
  const pinnedTheoremNames = Object.keys(map.earnedMilestoneTheoremKernelTypeSha256)
    .sort((left, right) => left < right ? -1 : left > right ? 1 : 0);
  if (stableStringify0(pinnedTheoremNames) !== stableStringify0(REQUIRED_MILESTONE_THEOREMS0)
      || pinnedTheoremNames.some((name) => !isSha2560(map.earnedMilestoneTheoremKernelTypeSha256[name]))) {
    throw new Error('reviewed milestone theorem kernel-type fingerprint inventory mismatch');
  }
  if (sha256Text0(stableStringify0(map)) !== REQUIRED_PUBLICATION_MAP_SHA2560) {
    throw new Error('formal publication milestone map drifted from the reviewed release-41 specification');
  }
}

function strictlySorted0(values) {
  return Array.isArray(values) && values.every((value, index) => index === 0 || values[index - 1] < value);
}

function isSha2560(value) {
  return typeof value === 'string' && /^[0-9a-f]{64}$/u.test(value);
}

function kernelFingerprint0(domain, value) {
  return sha256Text0(`PNP-FORMAL-PUBLICATION-FINGERPRINT-v0\nleanprover/lean4:v4.31.0\n${domain}\n${value}`);
}

function isObject0(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

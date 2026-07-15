import Lean
import PNP

open Lean Elab Command

namespace PNP.TheoremInventory

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def kernelType (info : ConstantInfo) : String :=
  toString (repr info.type)

private def kernelValue? : ConstantInfo → Option String
  | .defnInfo value => some (toString (repr value.value))
  | .opaqueInfo value => some (toString (repr value.value))
  | _ => none

private def jsonNames (names : Array Name) : Json :=
  Json.arr (names.map fun name => toJson name.toString)

private structure InventoryRow where
  name : Name
  moduleName : Name
  info : ConstantInfo
  axioms : Array Name

private def InventoryRow.asJson (row : InventoryRow) : Json :=
  Json.mkObj [
    ("name", toJson row.name.toString),
    ("module", toJson row.moduleName.toString),
    ("kind", toJson (declarationKind row.info)),
    ("axioms", jsonNames row.axioms)
  ]

private def InventoryRow.asDetailedJson (row : InventoryRow) : Json :=
  Json.mkObj [
    ("name", toJson row.name.toString),
    ("module", toJson row.moduleName.toString),
    ("kind", toJson (declarationKind row.info)),
    ("kernelType", toJson (kernelType row.info)),
    ("kernelValue", toJson (kernelValue? row.info)),
    ("axioms", jsonNames row.axioms)
  ]

private def moduleFor (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some moduleIndex => env.header.moduleNames[moduleIndex]!
  | none => env.mainModule

private def isProjectModuleDeclaration (env : Environment) (name : Name) : Bool :=
  (`PNP).isPrefixOf (moduleFor env name)

private def isProjectDeclaration (env : Environment) (name : Name) : Bool :=
  !isPrivateName name && (`PNP).isPrefixOf name &&
    isProjectModuleDeclaration env name

private def reviewedMilestoneTheoremNames : Array Name := #[
  `PNP.Concrete.BitString.decodePair_pair,
  `PNP.Concrete.CookLevin.BuilderInputLength.finalTape_represents,
  `PNP.Concrete.CookLevin.BuilderInputLength.inputTape_eq_totalInputFramerFinalTape,
  `PNP.Concrete.CookLevin.BuilderInputLength.malformedScanSymbol_timeout,
  `PNP.Concrete.CookLevin.BuilderInputLength.rawTimeBound_exact,
  `PNP.Concrete.CookLevin.BuilderInputLength.run_compile,
  `PNP.Concrete.CookLevin.BuilderInputLength.tallySizeBound_exact,
  `PNP.Concrete.CookLevin.BuilderInputLength.workBoundedDecide_accept,
  `PNP.Concrete.CookLevin.BuilderInputLength.workRunExact,
  `PNP.Concrete.CookLevin.BuilderInputLength.workRunExact_after_totalInputFramer,
  `PNP.Concrete.CookLevin.BuilderInputLength.work_one_step_short_timeout,
  `PNP.Concrete.CookLevin.FixedTableauInstance.exists_accepting_iff_boundedDecide_accept,
  `PNP.Concrete.CookLevin.FixedTableauInstance.tableauVerdict_of_valid,
  `PNP.Concrete.CookLevin.FixedTableauInstance.valid_iff_eq_canonical,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.FiniteRow.next_represents_advance,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.FormulaBitCursor.run_excess,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.FormulaBitCursor.run_full,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.FormulaBitCursor.run_full_emit_eq_encodedFormula,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.FormulaBitCursor.run_one_step_short,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.FormulaBitCursor.run_prefix,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.FormulaBitCursor.run_to_end,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.FormulaBitCursor.step_after_one_step_short,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.FormulaBitCursor.step_at_end,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.actualFuel_le_uniformFuel,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.actualFuel_ne_timeout,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.certificateBitWidth_eq_of_paired,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.certificateLengthWidth_eq_of_paired,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.certificateOf_certificate,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.decode_encodedFormula,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.decodedInitialRow_eq_paired,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.decodedRow_next,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.decodedTableau_transitions,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.dimensions_encodedInputLength,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.dimensions_timeBound,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormulaSizePolynomial_eval,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff_finiteAccepting,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff_language,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormula_size_le,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.exists_accepting_iff_program_accept,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.findRule_some_mem,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.finiteRun_head_bounds,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.finiteRun_represents_run,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaConstraintCountPolynomial_eval,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaConstraintSchedule_emit_eq_program,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaConstraintSchedule_length,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaConstraintSlotDirect_eq,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaVariableCountPolynomial_eval,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaBitSchedule_emit_eq_encodedFormula,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaBitSchedule_length,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaBitSlotCountDirect_eq_polynomial,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaBitSlotDirect_eq,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaClauseSchedule_emit_eq_formulaClauses,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaClauseSchedule_length,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaClauseSlotDirect_eq,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaTokenSchedule_length,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formulaTokenSlotDirect_eq,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formula_clauseCount,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formula_clauseCount_le_formulaClauseCountPolynomial,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formula_clause_length_le,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formula_satisfiable_iff,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formula_satisfiable_iff_finiteAccepting,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formula_satisfied_iff,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.formula_wellScoped,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.hasFiniteAccepting_iff_language,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.initialCellAtCoordinate_eq_initialCellAt,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.language_iff_exists_acceptingTableau,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.pairedInitialRowFor_represents,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.program_length_le_formulaConstraintCountPolynomial,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.rawInput_size_le,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.tableauAssignment_transitionProgram_holds,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.tableauVerdict_eq_program_of_valid,
  `PNP.Concrete.CookLevin.VerifierTableauProblem.uniformFuel_verdict_eq,
  `PNP.Concrete.CookLevin.BoundedLiteral.emit_variable_lt,
  `PNP.Concrete.CookLevin.LocalConstraint.emit_holds_iff,
  `PNP.Concrete.CookLevin.LocalProgram.emitted_clause_count,
  `PNP.Concrete.CookLevin.LocalProgram.toFormula_satisfied_iff,
  `PNP.Concrete.CookLevin.LocalProgram.toFormula_satisfiable_iff,
  `PNP.Concrete.CookLevin.assignmentAt_assignmentOf,
  `PNP.Concrete.CookLevin.exactlyOneBoundedClauses_holds_iff,
  `PNP.Concrete.CookLevin.implicationClauses_holds_iff,
  `PNP.Concrete.CookLevin.localProgram_formula_wellScoped,
  `PNP.Concrete.CookLevin.atLeastOneClause_satisfied_iff,
  `PNP.Concrete.CookLevin.canonicalTableau_valid,
  `PNP.Concrete.CookLevin.encodeCNF_size_exact,
  `PNP.Concrete.CookLevin.encodeCNF_size_le,
  `PNP.Concrete.CookLevin.eval_encodedInputPolynomial,
  `PNP.Concrete.CookLevin.eval_tapeWidthPolynomial,
  `PNP.Concrete.CookLevin.excludePairClause_not_satisfied_of_both_true,
  `PNP.Concrete.CookLevin.machine_startState_lt_bound,
  `PNP.Concrete.CookLevin.machine_acceptState_lt_bound,
  `PNP.Concrete.CookLevin.machine_rejectState_lt_bound,
  `PNP.Concrete.CookLevin.rule_source_lt_machineStateBound,
  `PNP.Concrete.CookLevin.rule_target_lt_machineStateBound,
  `PNP.Concrete.CookLevin.run_pad_of_halted,
  `PNP.Concrete.CookLevin.run_pad_of_stuck,
  `PNP.Concrete.CookLevin.run_succ_eq_run_advance,
  `PNP.Concrete.CookLevin.tableauEndpoint_of_valid,
  `PNP.Concrete.CookLevin.trace_length,
  `PNP.Concrete.CookLevin.validTableau_iff_eq_trace,
  `PNP.Concrete.CookLevin.verifierEncodedInput_size_le,
  `PNP.Concrete.CookLevin.VariableLayout.symbolVariable_ne_headVariable,
  `PNP.Concrete.CookLevin.VariableLayout.headVariable_ne_stateVariable,
  `PNP.Concrete.CookLevin.VariableLayout.stateVariable_ne_certificateBitVariable,
  `PNP.Concrete.CookLevin.VariableLayout.certificateBitVariable_ne_certificateLengthVariable,
  `PNP.Concrete.CookLevin.VariableLayout.symbolVariable_lt_variableCount,
  `PNP.Concrete.CookLevin.VariableLayout.headVariable_lt_variableCount,
  `PNP.Concrete.CookLevin.VariableLayout.stateVariable_lt_variableCount,
  `PNP.Concrete.CookLevin.VariableLayout.certificateBitVariable_lt_variableCount,
  `PNP.Concrete.CookLevin.VariableLayout.certificateLengthVariable_lt_variableCount,
  `PNP.Concrete.DecisionProgram.RawRefinement.compile_haltsWithin,
  `PNP.Concrete.DecisionProgram.RawRefinement.compile_verdict_eq,
  `PNP.Concrete.FinalUniversalDesign.cnfCompiled_accept_iff_check,
  `PNP.Concrete.FinalUniversalDesign.cnfCompiled_ne_timeout,
  `PNP.Concrete.FinalUniversalDesign.cnfCompiled_reject_iff_check_false,
  `PNP.Concrete.FinalUniversalDesign.cnfConcreteVerifier_decision,
  `PNP.Concrete.FinalUniversalDesign.cnfConcreteVerifier_inputMode,
  `PNP.Concrete.FinalUniversalDesign.cnfSATInNP,
  `PNP.Concrete.FinalUniversalDesign.cnfUniversalWorkOutcome,
  `PNP.Concrete.FinalUniversalDesign.formulaGrammarOutcome,
  `PNP.Concrete.FunctionProgram.RawRefinement.compile_haltsWithin,
  `PNP.Concrete.FunctionProgram.RawRefinement.compile_output_eq,
  `PNP.Concrete.FunctionProgram.RawRefinement.output_size_le,
  `PNP.Concrete.NatPolynomial.eval_mono,
  `PNP.Concrete.PipelineCompiler.acceptingSuppliedTrace_workRunExact_of_rawRunExact,
  `PNP.Concrete.PipelineCompiler.outputBits_length_le_pipelineOutputSizeBound_of_rawRunExact,
  `PNP.Concrete.PipelineCompiler.pipelineOutputSizeBound_eval,
  `PNP.Concrete.PipelineCompiler.pipeline_accepts_iff,
  `PNP.Concrete.PipelineCompiler.pipeline_boundedDecide_eq,
  `PNP.Concrete.PipelineCompiler.pipeline_correct,
  `PNP.Concrete.PipelineCompiler.pipeline_machineOutput_eq,
  `PNP.Concrete.PipelineCompiler.pipeline_ne_timeout,
  `PNP.Concrete.PipelineCompiler.pipeline_timeout_of_stuck_rawRunExact,
  `PNP.Concrete.PipelineCompiler.rejectingSuppliedTrace_workRunExact_of_rawRunExact,
  `PNP.Concrete.PipelineCompiler.run_pipeline_accept_at_bound_of_rawRunExact,
  `PNP.Concrete.PipelineCompiler.run_pipeline_reject_at_bound_of_rawRunExact,
  `PNP.Concrete.PipelineCompiler.suppliedTraceRawSteps_le_of_rawRunExact,
  `PNP.Concrete.PipelineCompiler.suppliedTraceRawSteps_le_pipelineRawTimeBound,
  `PNP.Concrete.PipelineCompiler.totalInputLaunch_workStep,
  `PNP.Concrete.PipelineInputFramer.boundedDecide_compilePairedInputFramer_accept,
  `PNP.Concrete.PipelineInputFramer.boundedDecide_compileTotalInputFramer_accept,
  `PNP.Concrete.PipelineInputFramer.boundedDecide_compileTotalInputFramer_ne_timeout,
  `PNP.Concrete.PipelineInputFramer.pairedInputFramerFinal_isHalted,
  `PNP.Concrete.PipelineInputFramer.pairedInputFramerFinal_represents,
  `PNP.Concrete.PipelineInputFramer.pairedInputFramerRawTimeBound_exact,
  `PNP.Concrete.PipelineInputFramer.pairedInputFramer_workRunExact,
  `PNP.Concrete.PipelineInputFramer.run_compilePairedInputFramer_rawTimeBound,
  `PNP.Concrete.PipelineInputFramer.run_compileTotalInputFramer_encoded_rawTimeBound,
  `PNP.Concrete.PipelineInputFramer.run_compileTotalInputFramer_rawTimeBound_blankEquivalent,
  `PNP.Concrete.PipelineInputFramer.totalInputFramerFinal_isHalted,
  `PNP.Concrete.PipelineInputFramer.totalInputFramerFinal_represents,
  `PNP.Concrete.PipelineInputFramer.totalInputFramerRawTimeBound_le,
  `PNP.Concrete.PipelineInputFramer.totalInputFramer_workRunExact,
  `PNP.Concrete.PipelineMachineSimulation.findIndexedRawRuleFrom_map_snd,
  `PNP.Concrete.PipelineMachineSimulation.find_liftMachine_entry,
  `PNP.Concrete.PipelineMachineSimulation.liftMachine_isHalted_eq_of_representsConfiguration,
  `PNP.Concrete.PipelineMachineSimulation.rawRunExact?_exists_le_run,
  `PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_mul_of_rawRunExact,
  `PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_mul_of_run_halted,
  `PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_of_step,
  `PNP.Concrete.PipelineMachineSimulation.workRunExact_three_mul_of_rawRunExact,
  `PNP.Concrete.PipelineMachineSimulation.workRunExact_three_of_step,
  `PNP.Concrete.PipelineMachineSimulation.workRun_three_mul_of_run_halted,
  `PNP.Concrete.PipelineOutputHandoff.framedOutputHandoffFinal_isHalted,
  `PNP.Concrete.PipelineOutputHandoff.framedOutputHandoffRawTimeBound_exact,
  `PNP.Concrete.PipelineOutputHandoff.framedOutputHandoff_workRunExact_of_represents,
  `PNP.Concrete.PipelineOutputHandoff.run_compileFramedOutputHandoff_of_represents,
  `PNP.Concrete.PipelinePairedCompiler.machineOutput_length_le_input_add_fuel,
  `PNP.Concrete.PipelinePairedCompiler.outputBits_length_le_pairedPipelineOutputSizeBound_of_rawRunExact,
  `PNP.Concrete.PipelinePairedCompiler.pairedPipelineOutputSizeBound_eval,
  `PNP.Concrete.PipelinePairedCompiler.pairedPipeline_accepts_iff,
  `PNP.Concrete.PipelinePairedCompiler.pairedPipeline_boundedDecide_eq,
  `PNP.Concrete.PipelinePairedCompiler.pairedPipeline_correct_on_pair,
  `PNP.Concrete.PipelinePairedCompiler.pairedPipeline_machineOutput_eq,
  `PNP.Concrete.PipelinePairedCompiler.pairedPipeline_ne_timeout,
  `PNP.Concrete.PipelinePairedCompiler.run_pairedPipeline_accept_at_bound_of_rawRunExact,
  `PNP.Concrete.PipelinePairedCompiler.run_pairedPipeline_reject_at_bound_of_rawRunExact,
  `PNP.Concrete.PipelinePairedCompiler.suppliedTraceTerminalRawSteps_le_of_rawRunExact,
  `PNP.Concrete.PipelinePairedCompiler.suppliedTraceTerminalRawSteps_le_pairedPipelineRawTimeBound,
  `PNP.Concrete.PipelineSequentialCompiler.acceptingSequentialTrace_workRunExact_of_rawRunExact,
  `PNP.Concrete.PipelineSequentialCompiler.firstOutputSizeBound_eval,
  `PNP.Concrete.PipelineSequentialCompiler.firstTraceAndLaunch_workRunExact_of_rawRunExact,
  `PNP.Concrete.PipelineSequentialCompiler.rejectingSequentialTrace_workRunExact_of_rawRunExact,
  `PNP.Concrete.PipelineSequentialCompiler.run_sequential_accept_at_bound_of_rawRunExact,
  `PNP.Concrete.PipelineSequentialCompiler.run_sequential_reject_at_bound_of_rawRunExact,
  `PNP.Concrete.PipelineSequentialCompiler.sequentialOutputSizeBound_eval,
  `PNP.Concrete.PipelineSequentialCompiler.sequentialRawSteps_le_of_rawRunExact,
  `PNP.Concrete.PipelineSequentialCompiler.sequentialRawSteps_le_sequentialRawTimeBound,
  `PNP.Concrete.PipelineSequentialCompiler.sequential_accepts_iff,
  `PNP.Concrete.PipelineSequentialCompiler.sequential_boundedDecide_eq,
  `PNP.Concrete.PipelineSequentialCompiler.sequential_correct,
  `PNP.Concrete.PipelineSequentialCompiler.sequential_machineOutput_eq,
  `PNP.Concrete.PipelineSequentialCompiler.sequential_ne_timeout,
  `PNP.Concrete.PipelineSequentialCompiler.sequential_timeout_of_stuck_first_rawRunExact,
  `PNP.Concrete.PipelineSequentialStateNamespace.findWorkRule_sequential_first_of_some,
  `PNP.Concrete.PipelineSequentialStateNamespace.findWorkRule_sequential_second_of_some,
  `PNP.Concrete.PipelineSequentialStateNamespace.firstAcceptLaunch_workStep,
  `PNP.Concrete.PipelineSequentialStateNamespace.firstPipelineState_ne_secondPipelineState,
  `PNP.Concrete.PipelineSequentialStateNamespace.firstRejectLaunch_workStep,
  `PNP.Concrete.PipelineSequentialStateNamespace.sequentialWorkMachine_acceptState_ne_rejectState,
  `PNP.Concrete.TerminalOutputPacker.machineOutput_compileTerminalOutputPacker_eq,
  `PNP.Concrete.TerminalOutputPacker.run_compileTerminalOutputPacker,
  `PNP.Concrete.TerminalOutputPacker.run_compileTerminalOutputPacker_exact,
  `PNP.Concrete.TerminalOutputPacker.terminalOutputPackerFinal_isHalted,
  `PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_one_step_short_timeout,
  `PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_output_eq,
  `PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_runtime_le,
  `PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_workRunExact,
  `PNP.Concrete.PipelineTerminalBridge.acceptingPackerLaunch_workStep,
  `PNP.Concrete.PipelineTerminalBridge.acceptingSuppliedTrace_workRunExact_of_rawRunExact,
  `PNP.Concrete.PipelineTerminalBridge.acceptingTerminalFinal_isHalted,
  `PNP.Concrete.PipelineTerminalBridge.acceptingTerminal_workRunExact_of_represents,
  `PNP.Concrete.PipelineTerminalBridge.bridged_workRunExact_of_exact,
  `PNP.Concrete.PipelineTerminalBridge.bridged_workStep?_of_some,
  `PNP.Concrete.PipelineTerminalBridge.findWorkRule_terminalBridge_acceptingPacker_of_some,
  `PNP.Concrete.PipelineTerminalBridge.findWorkRule_terminalBridge_rejectingPacker_of_some,
  `PNP.Concrete.PipelineTerminalBridge.machineOutput_compileTerminalBridge_accept_of_rawRunExact,
  `PNP.Concrete.PipelineTerminalBridge.machineOutput_compileTerminalBridge_reject_of_rawRunExact,
  `PNP.Concrete.PipelineTerminalBridge.outputBits_compileTerminalBridge_accepting_of_represents,
  `PNP.Concrete.PipelineTerminalBridge.outputBits_compileTerminalBridge_rejecting_of_represents,
  `PNP.Concrete.PipelineTerminalBridge.rejectingPackerLaunch_workStep,
  `PNP.Concrete.PipelineTerminalBridge.rejectingSuppliedTrace_workRunExact_of_rawRunExact,
  `PNP.Concrete.PipelineTerminalBridge.rejectingTerminalFinal_isHalted,
  `PNP.Concrete.PipelineTerminalBridge.rejectingTerminal_workRunExact_of_represents,
  `PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_accept_of_rawRunExact,
  `PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_accepting_of_represents,
  `PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_accepting_of_represents_at_bound,
  `PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_reject_of_rawRunExact,
  `PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_rejecting_of_represents,
  `PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_rejecting_of_represents_at_bound,
  `PNP.Concrete.PipelineTerminalBridge.simulationPrefix_terminalBridge_workBoundedDecide_timeout,
  `PNP.Concrete.PipelineTerminalBridge.suppliedTraceTerminalWorkSteps_eq,
  `PNP.Concrete.PipelineTerminalBridge.terminalBridgeMachine_acceptState_ne_rejectState,
  `PNP.Concrete.PipelineTerminalBridge.terminalBridge_runtime_le,
  `PNP.Concrete.PipelineTerminalBridge.workBoundedDecide_terminalBridge_accept_of_rawRunExact,
  `PNP.Concrete.PipelineTerminalBridge.workBoundedDecide_terminalBridge_reject_of_rawRunExact,
  `PNP.Concrete.PipelineTerminalBridge.workBoundedDecide_terminalBridge_timeout_of_stuck_rawRunExact,
  `PNP.Concrete.PipelineStateNamespace.findWorkRule_composedRules_handoff,
  `PNP.Concrete.PipelineStateNamespace.findWorkRule_composedRules_input,
  `PNP.Concrete.PipelineStateNamespace.findWorkRule_composedRules_simulation,
  `PNP.Concrete.PipelineStateNamespace.findWorkRule_rename,
  `PNP.Concrete.PipelineStateNamespace.renamedInputFramer_workRunExact,
  `PNP.Concrete.PipelineStateNamespace.renamedLiftMachine_workRunExact_of_rawRunExact,
  `PNP.Concrete.PipelineStateNamespace.renamedOutputHandoff_workRunExact_of_represents,
  `PNP.Concrete.PipelineStateNamespace.stageState_injective,
  `PNP.Concrete.PipelineStateNamespace.workBoundedDecide_rename,
  `PNP.Concrete.PipelineStateNamespace.workRunExact?_rename,
  `PNP.Concrete.PipelineStageBridges.acceptingHandoffState_ne_rejectingHandoffState,
  `PNP.Concrete.PipelineStageBridges.acceptingLaunch_workStep,
  `PNP.Concrete.PipelineStageBridges.bridgedAccept_workRunExact_of_rawRunExact,
  `PNP.Concrete.PipelineStageBridges.bridgedReject_workRunExact_of_rawRunExact,
  `PNP.Concrete.PipelineStageBridges.bridgedWorkSteps_eq,
  `PNP.Concrete.PipelineStageBridges.findWorkRule_bridged_acceptingHandoff_of_some,
  `PNP.Concrete.PipelineStageBridges.findWorkRule_bridged_input_of_some,
  `PNP.Concrete.PipelineStageBridges.findWorkRule_bridged_rejectingHandoff_of_some,
  `PNP.Concrete.PipelineStageBridges.findWorkRule_bridged_simulation_of_some,
  `PNP.Concrete.PipelineStageBridges.inputLaunch_workStep,
  `PNP.Concrete.PipelineStageBridges.rejectingLaunch_workStep,
  `PNP.Concrete.PipelineStageBridges.run_compileBridgedMachine_accept_of_rawRunExact,
  `PNP.Concrete.PipelineStageBridges.run_compileBridgedMachine_reject_of_rawRunExact,
  `PNP.Concrete.PipelineStageBridges.workBoundedDecide_bridged_accept_of_rawRunExact,
  `PNP.Concrete.PipelineStageBridges.workBoundedDecide_bridged_reject_of_rawRunExact,
  `PNP.Concrete.PipelineStageBridges.workBoundedDecide_bridged_timeout_of_stuck_rawRunExact,
  `PNP.Concrete.PipelineTape.frameWithGarbage_represents,
  `PNP.Concrete.PipelineTape.handoffTarget_withGarbage_represents,
  `PNP.Concrete.PipelineTape.represents_expandLeft_of_nil,
  `PNP.Concrete.PipelineTape.represents_expandRight_of_nil,
  `PNP.Concrete.PipelineTape.represents_moveLeft_of_cons,
  `PNP.Concrete.PipelineTape.represents_moveRight_of_cons,
  `PNP.Concrete.PipelineTape.represents_write,
  `PNP.Concrete.PolynomialTimeDecider.compileToMachine_accepts_iff,
  `PNP.Concrete.PolynomialTimeMachine.verdict_accepts_iff,
  `PNP.Concrete.PolynomialTimeMachine.verdict_ne_timeout,
  `PNP.Concrete.Tape.outputBits_handoffTarget,
  `PNP.Concrete.Tape.outputBits_moveRight_moveLeft,
  `PNP.Concrete.Tape.outputBits_ofInput,
  `PNP.Concrete.Tape.outputBits_right_append_blank,
  `PNP.Concrete.Tape.symbolAt_moveLeft,
  `PNP.Concrete.Tape.symbolAt_moveRight,
  `PNP.Concrete.np_complete_in_p_implies_p_eq_np,
  `PNP.Concrete.p_subset_np,
  `PNP.Concrete.reduction_comp,
  `PNP.Concrete.reduction_refl,
  `PNP.Concrete.reduction_transports_p,
  `PNP.Concrete.run_succ,
  `PNP.Concrete.run_zero,
  `PNP.DirectWire.ConditionalThresholdBoundaryPremises.fullResidualSlack_le_four,
  `PNP.DirectWire.ConditionalThresholdBoundaryPremises.satisfiable_iff_minimum_ge_succ,
  `PNP.DirectWire.Equivalent.trans,
  `PNP.DirectWire.StrictEquivalentGain.strictResidualDescent,
  `PNP.DirectWire.andCircuit_spec,
  `PNP.DirectWire.compatibleReplacement_framed,
  `PNP.DirectWire.constantOneDirect_referenceMinimum,
  `PNP.DirectWire.constantZeroDirect_referenceMinimum,
  `PNP.DirectWire.equalityDirect_referenceMinimum,
  `PNP.DirectWire.equivalentBool_eq_true_iff,
  `PNP.DirectWire.exactWidthEnumeration_complete,
  `PNP.DirectWire.firstListedGain_sound,
  `PNP.DirectWire.firstListedGain_none_no_listed_gain,
  `PNP.DirectWire.framedGlobalSlackLaw,
  `PNP.DirectWire.lockedBaselineCount_report_formula,
  `PNP.DirectWire.nandCircuit_spec,
  `PNP.DirectWire.prefixAndDirect_referenceMinimum,
  `PNP.DirectWire.referenceMinimum_invariant,
  `PNP.DirectWire.residualSlack_eq_zero_iff_minimum,
  `PNP.DirectWire.strictEquivalentGainBool_complete,
  `PNP.DirectWire.traceDirect_referenceMinimum,
  `PNP.DirectWire.unresolved_positiveSlack_regression,
  `PNP.Main.concretePEqualsNP_iff
]

private def inventory : CommandElabM Json := do
  let env ← getEnv
  let allDeclarationNames := env.constants.fold
    (init := #[])
    (fun names name _ => names.push name)
  let excludedPrivateDeclarationCount :=
    (allDeclarationNames.filter fun name =>
      isPrivateName name && isProjectModuleDeclaration env name).size
  let declarationNames := env.constants.fold
    (init := #[])
    (fun names name _ =>
      if isProjectDeclaration env name then names.push name else names)
  let declarationNames := declarationNames.qsort fun left right =>
    left.toString < right.toString
  let mut rows : Array InventoryRow := #[]
  for name in declarationNames do
    let some info := env.find? name
      | throwError "compiled declaration disappeared from the environment: {name}"
    let axioms ← collectAxioms name
    let axioms := axioms.qsort fun left right =>
      left.toString < right.toString
    rows := rows.push { name, moduleName := moduleFor env name, info, axioms }
  let theoremRows := rows.filter fun row => declarationKind row.info == "theorem"
  let axiomRows := rows.filter fun row => declarationKind row.info == "axiom"
  let constructorRows := rows.filter fun row => declarationKind row.info == "constructor"
  let definitionRows := rows.filter fun row => declarationKind row.info == "definition"
  let inductiveRows := rows.filter fun row => declarationKind row.info == "inductive"
  let opaqueRows := rows.filter fun row => declarationKind row.info == "opaque"
  let quotientRows := rows.filter fun row => declarationKind row.info == "quotient"
  let recursorRows := rows.filter fun row => declarationKind row.info == "recursor"
  let assumptionFreeTheoremCount :=
    (theoremRows.filter fun row => row.axioms.isEmpty).size
  let mut sourceClosureModules : Array Name := #[]
  for row in rows do
    unless sourceClosureModules.contains row.moduleName do
      sourceClosureModules := sourceClosureModules.push row.moduleName
  sourceClosureModules := sourceClosureModules.qsort fun left right =>
    left.toString < right.toString
  let compatibilityRootName := `PNP.Main.p_eq_np
  let concreteTargetName := `PNP.Main.ConcretePEqualsNP
  let compatibilityRootCandidate :=
    rows.find? (fun row => row.name == compatibilityRootName)
  let concreteTargetCandidate :=
    rows.find? (fun row => row.name == concreteTargetName)
  let milestoneTheoremNames := reviewedMilestoneTheoremNames.qsort fun left right =>
    left.toString < right.toString
  let mut milestoneCandidates : Array InventoryRow := #[]
  for name in milestoneTheoremNames do
    let some row := rows.find? (fun row => row.name == name)
      | throwError "reviewed milestone theorem is absent from the compiled environment: {name}"
    unless declarationKind row.info == "theorem" do
      throwError "reviewed milestone declaration is not a theorem: {name}"
    milestoneCandidates := milestoneCandidates.push row
  return Json.mkObj [
    ("kind", toJson "PNPLeanTheoremInventory0"),
    ("version", toJson 0),
    ("coordinate", toJson "PNP-LEAN-THEOREM-INVENTORY-2026-07-15-43"),
    ("leanToolchain", toJson "leanprover/lean4:v4.31.0"),
    ("rootModule", toJson "PNP"),
    ("environmentProbeComplete", toJson true),
    ("declarationCount", toJson rows.size),
    ("excludedPrivateDeclarationCount", toJson excludedPrivateDeclarationCount),
    ("theoremCount", toJson theoremRows.size),
    ("assumptionFreeTheoremCount", toJson assumptionFreeTheoremCount),
    ("axiomCount", toJson axiomRows.size),
    ("declarationKindCounts", Json.mkObj [
      ("axiom", toJson axiomRows.size),
      ("constructor", toJson constructorRows.size),
      ("definition", toJson definitionRows.size),
      ("inductive", toJson inductiveRows.size),
      ("opaque", toJson opaqueRows.size),
      ("quotient", toJson quotientRows.size),
      ("recursor", toJson recursorRows.size),
      ("theorem", toJson theoremRows.size)
    ]),
    ("sourceClosureModuleCount", toJson sourceClosureModules.size),
    ("sourceClosureModules", Json.arr (sourceClosureModules.map fun name => toJson name.toString)),
    ("projectAxioms", Json.arr (axiomRows.map fun row => toJson row.name.toString)),
    ("compatibilityRootName", toJson compatibilityRootName.toString),
    ("compatibilityRootCandidate", toJson (compatibilityRootCandidate.map InventoryRow.asDetailedJson)),
    ("concreteTargetName", toJson concreteTargetName.toString),
    ("concreteTargetCandidate", toJson (concreteTargetCandidate.map InventoryRow.asDetailedJson)),
    ("milestoneCandidates", Json.arr (milestoneCandidates.map InventoryRow.asDetailedJson)),
    ("declarations", Json.arr (rows.map InventoryRow.asJson))
  ]

run_cmd do
  let output ← inventory
  liftIO <| IO.println output.compress

end PNP.TheoremInventory

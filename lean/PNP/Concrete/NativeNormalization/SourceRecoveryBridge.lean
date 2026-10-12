import PNP.Concrete.NativeNormalization.RecoveryBridge

namespace PNP.Concrete.NativeNormalization.RecoverySourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks
open NativeContext NativeSource OwnerCacheSourceBridge
attribute [local irreducible] SourceCheck.result

private theorem requested_projection (r : CutDriver.State) (width : Nat) :
    SourceRecovery.sourceView (SourceRecovery.withRecovery r
      {SourceRecovery.view r with remaining := List.replicate width true}) =
      {SourceRecovery.sourceView r with remaining := List.replicate width true} := rfl

private theorem requested_source_of_fields (F : CNFFormula) (b : MeasuredSourceRecovery.Cache F)
    (r : CutDriver.State)
    (formula : r.core.formula = GraphQuery.clauseData (NativeTseitin.frontend F).clauses)
    (matching : r.core.table = MatchingTable.encode (matchingEntries b.context.toCutData))
    (variables : r.variables = SearchVertices.encodeVertices (variableVertices b.context.toCutData))
    (candidate : SourceCheck.candidate r = (MeasuredCandidate.assignment (MeasuredCache.operations b.data)).value) :
    (SourceRecovery.called (SourceRecovery.withRecovery r
      {SourceRecovery.view r with remaining := List.replicate F.variableCount true})).registers.output =
      (MeasuredSourceRecovery.candidate F b).value := by
  rw [SourceRecovery.called_output,requested_projection]
  let data : Recovery.State :=
    {SourceRecovery.sourceView r with remaining := List.replicate F.variableCount true}
  have checked := original_source F b data (List.length_replicate ..) formula matching variables
  have assignment : data.assignment = SourceCheck.candidate r := rfl
  rw [assignment,candidate] at checked
  exact checked

def requestedState (width : Nat) (input : BitString) : CutDriver.State :=
  let r := SourceCheck.result input
  SourceRecovery.withRecovery r {SourceRecovery.view r with remaining := List.replicate width true}
theorem requested_call_source (F : CNFFormula) :
    (SourceRecovery.called (requestedState F.variableCount (encodedInput (NativeTseitin.frontend F)))).registers.output =
      (MeasuredSourceRecovery.candidate F (MeasuredSourceCache.fromSource F).value).value := by
  exact requested_source_of_fields F (MeasuredSourceCache.fromSource F).value
    (SourceCheck.result (encodedInput (NativeTseitin.frontend F)))
    (SourceCheck.result_data (NativeTseitin.frontend F).variableCount (NativeTseitin.frontend F).clauses).formulaRead
    (checked_matching _ (NativeFrontend.frontend_three F))
    (checked_variables _ (NativeFrontend.frontend_three F))
    (CheckSourceBridge.candidate_retained _ (NativeFrontend.frontend_three F))

theorem requested_call_model_from_runtime_success (F : CNFFormula)
    (passed : (SourceCheck.result (encodedInput (NativeTseitin.frontend F))).registers.output =
      TableOwner.answer none) :
    F.Satisfied
      (SourceRecovery.called (requestedState F.variableCount (encodedInput (NativeTseitin.frontend F)))).registers.output := by
  rw [requested_call_source,← checked_original_source]
  exact checked_model_from_runtime_success F passed


private theorem full_width_source_of_fields {F : CNFFormula} (C : CutData F) (r : CutDriver.State)
    (width : r.core.width.length = F.variableCount)
    (formula : r.core.formula = GraphQuery.clauseData F.clauses)
    (matching : r.core.table = MatchingTable.encode (matchingEntries C))
    (variables : r.variables = SearchVertices.encodeVertices (variableVertices C)) :
    (SourceRecovery.fullWidthResult r).registers.output =
      (MeasuredCutRecovery.recover C (SourceCheck.candidate r)).value := by
  let data := SourceRecovery.sourceView (SourceRecovery.widthLoaded r)
  have checked := complete_source C data width formula matching variables
  have assignment : data.assignment = SourceCheck.candidate r := rfl
  rw [assignment] at checked
  rw [SourceRecovery.fullWidthResult,SourceRecovery.called_output]
  exact checked

theorem result_source (F : CNFFormula) (three : ThreeCore F) :
    (SourceRecovery.result (encodedInput F)).registers.output =
      (MeasuredCutRecovery.recover (MeasuredSourceCache.build F three).value.context.toCutData
        (MeasuredCandidate.assignment
          (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value).value := by
  have width : (SourceCheck.result (encodedInput F)).core.width.length = F.variableCount := by
    rw [(SourceCheck.result_data F.variableCount F.clauses).widthRead,List.length_replicate]
  have checked := full_width_source_of_fields (MeasuredSourceCache.build F three).value.context.toCutData
    (SourceCheck.result (encodedInput F)) width
    (SourceCheck.result_data F.variableCount F.clauses).formulaRead
    (checked_matching F three) (checked_variables F three)
  exact checked.trans (congrArg
    (fun a => (MeasuredCutRecovery.recover (MeasuredSourceCache.build F three).value.context.toCutData a).value)
    (CheckSourceBridge.candidate_retained F three))

theorem polynomial_source (F : CNFFormula) (three : ThreeCore F) :
    SourceRecovery.polynomial.output (encodedInput F) =
      (MeasuredCutRecovery.recover (MeasuredSourceCache.build F three).value.context.toCutData
        (MeasuredCandidate.assignment
          (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value).value := by
  rw [SourceRecovery.polynomial_output,result_source F three]

theorem machine_source (F : CNFFormula) (three : ThreeCore F) :
    machineOutput (BitRegister.CompilerIO.rawMachine SourceRecovery.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 SourceRecovery.sourceFuel).eval (encodedInput F).length)
      (encodedInput F) =
      (MeasuredCutRecovery.recover (MeasuredSourceCache.build F three).value.context.toCutData
        (MeasuredCandidate.assignment
          (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value).value := by
  rw [SourceRecovery.machine_output,polynomial_source F three]

theorem runtime_success (F : CNFFormula) (three : ThreeCore F)
    (passed : (SourceCheck.result (encodedInput F)).registers.output = TableOwner.answer none) :
    (MeasuredCandidate.firstFailed
      (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value = none := by
  have computed := CheckSourceBridge.result_source F three
  rw [passed] at computed
  cases h : (MeasuredCandidate.firstFailed
      (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value with
  | none => rfl
  | some i =>
      rw [h] at computed
      cases computed

theorem machine_model_from_runtime_success (F : CNFFormula) (three : ThreeCore F)
    (passed : (SourceCheck.result (encodedInput F)).registers.output = TableOwner.answer none) :
    F.Satisfied (machineOutput (BitRegister.CompilerIO.rawMachine SourceRecovery.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 SourceRecovery.sourceFuel).eval (encodedInput F).length)
      (encodedInput F)) := by
  rw [machine_source F three,MeasuredCutRecovery.recover_value]
  exact cache_candidate_sound F three (MeasuredSourceCache.build F three).value (runtime_success F three passed)


end PNP.Concrete.NativeNormalization.RecoverySourceBridge

import PNP.Concrete.NativeNormalization.SourceCheckBridge
import PNP.Concrete.NormalizerSourceRecoveryPolynomial
import PNP.Concrete.NativeNormalization.MeasuredSourceRecovery
import PNP.Concrete.NativeNormalization.MeasuredRunCorrectness

namespace PNP.Concrete.NativeNormalization.RecoverySourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks
open NativeContext NativeSource OwnerCacheSourceBridge

theorem owner_source {F : CNFFormula} (C : CutData F) (v : Fin F.variableCount) :
    TableOwner.owner (matchingEntries C) v.val = (Matching.owner C.matchAt v).map Fin.val := by
  have found := OwnerSearchBridge.owner_source (MeasuredAccess.table C) v
  rw [MeasuredSearch.owner_value,MeasuredAccess.table_get] at found
  exact found

theorem preferred_source {F : CNFFormula} (C : CutData F) (v : Fin F.variableCount) :
    Recovery.preferredValue F.clauses (matchingEntries C) v.val = C.preferred v := by
  rw [Recovery.preferredValue,owner_source]
  cases h : Matching.owner C.matchAt v with
  | none => simp only [h,Option.map_none,CutData.preferred]
  | some row =>
      simp only [h,Option.map_some,CutData.preferred]
      unfold Recovery.literalValue CNFCore.occurrence CNFCore.clause
      rw [List.getElem?_eq_getElem row.isLt]
      rfl

theorem bit_source {F : CNFFormula} (C : CutData F) (a : BitString) (v : Fin F.variableCount) :
    Recovery.bitValue F.clauses (matchingEntries C) (variableVertices C) a v.val =
      if v ∈ C.variableData then (assignmentAt a (C.variableData.idxOf v)).getD false else C.preferred v := by
  unfold Recovery.bitValue variableVertices
  rw [ModeCacheSourceBridge.variable_position,MeasuredSelection.contains_value,MeasuredSelection.position_value]
  by_cases member : v ∈ C.variableData
  · simp only [member,decide_true,ite_true]
    exact (MeasuredBits.read_getElem a (C.variableData.idxOf v)).symm.trans
      (MeasuredBits.read_value a (C.variableData.idxOf v))
  · simp only [member,decide_false,Bool.false_eq_true,ite_false]
    exact preferred_source C v

theorem complete_source {F : CNFFormula} (C : CutData F) (r : Recovery.State)
    (width : r.remaining.length = F.variableCount)
    (formula : r.formula = GraphQuery.clauseData F.clauses)
    (matching : r.matching = MatchingTable.encode (matchingEntries C))
    (variables : r.variables = SearchVertices.encodeVertices (variableVertices C)) :
    (Recovery.called r).core.output = (MeasuredCutRecovery.recover C r.assignment).value := by
  rw [Recovery.called_canonical r F.clauses (matchingEntries C) (variableVertices C)
    F.variableCount width formula matching variables,MeasuredCutRecovery.recover_value]
  unfold CutData.recover
  apply congrArg List.ofFn
  funext v
  exact bit_source C r.assignment v

theorem recovered_lookup {F : CNFFormula} (C : CutData F) (a : BitString) (v : Fin F.variableCount) :
    (C.recover a)[v.val]?.getD false =
      Recovery.bitValue F.clauses (matchingEntries C) (variableVertices C) a v.val := by
  rw [CutData.recover,List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact v.isLt),List.getElem_ofFn]
  exact (bit_source C a v).symm

theorem original_width (F : CNFFormula) : F.variableCount ≤ (NativeTseitin.frontend F).variableCount := by
  change F.variableCount ≤ F.variableCount+2+_
  omega

theorem original_source (F : CNFFormula) (b : MeasuredSourceRecovery.Cache F) (r : Recovery.State)
    (width : r.remaining.length = F.variableCount)
    (formula : r.formula = GraphQuery.clauseData (NativeTseitin.frontend F).clauses)
    (matching : r.matching = MatchingTable.encode (matchingEntries b.context.toCutData))
    (variables : r.variables = SearchVertices.encodeVertices (variableVertices b.context.toCutData)) :
    (Recovery.called r).core.output = (MeasuredSourceRecovery.finish F b r.assignment).value := by
  rw [Recovery.called_canonical r (NativeTseitin.frontend F).clauses (matchingEntries b.context.toCutData)
    (variableVertices b.context.toCutData) F.variableCount width formula matching variables,
    MeasuredSourceRecovery.finish_value]
  change List.ofFn _ = List.ofFn (fun v : Fin F.variableCount =>
    (b.context.toCutData.recover r.assignment)[v.val]?.getD false)
  apply congrArg List.ofFn
  funext v
  exact (recovered_lookup b.context.toCutData r.assignment
    ⟨v.val,Nat.lt_of_lt_of_le v.isLt (original_width F)⟩).symm


abbrev encodedInput (F : CNFFormula) : BitString := MatchingDriver.encode F.variableCount F.clauses
def checkedState (width : Nat) (input : BitString) : Recovery.State :=
  let r := SourceCheck.result input
  ⟨r.registers,r.core.formula,r.core.table,r.variables,SourceCheck.candidate r,
    List.replicate width true,[],[]⟩
attribute [local irreducible] SourceCheck.result

theorem checked_matching (F : CNFFormula) (three : ThreeCore F) :
    (SourceCheck.result (encodedInput F)).core.table =
      MatchingTable.encode (matchingEntries (MeasuredSourceCache.build F three).value.context.toCutData) := by
  rw [(SourceCheck.result_data F.variableCount F.clauses).matchingRead,
    FullMatchingSourceBridge.fullTable_source]
  rfl

theorem checked_variables (F : CNFFormula) (three : ThreeCore F) :
    (SourceCheck.result (encodedInput F)).variables =
      SearchVertices.encodeVertices (variableVertices (MeasuredSourceCache.build F three).value.context.toCutData) := by
  rw [(SourceCheck.result_data F.variableCount F.clauses).variablesRead,
    CutTraceSourceBridge.trace_value_source,CutSelectionSourceBridge.selected_variables,
    ← CutSelectionSourceBridge.cut_variable_projection]
  rfl

theorem checked_complete_source (F : CNFFormula) (three : ThreeCore F) :
    (Recovery.called (checkedState F.variableCount (encodedInput F))).core.output =
      (MeasuredCutRecovery.recover (MeasuredSourceCache.build F three).value.context.toCutData
        (MeasuredCandidate.assignment
          (MeasuredCache.operations (MeasuredSourceCache.build F three).value.data)).value).value := by
  have checked := complete_source (MeasuredSourceCache.build F three).value.context.toCutData
    (checkedState F.variableCount (encodedInput F)) (List.length_replicate ..)
    (SourceCheck.result_data F.variableCount F.clauses).formulaRead
    (checked_matching F three) (checked_variables F three)
  change (Recovery.called (checkedState F.variableCount (encodedInput F))).core.output =
    (MeasuredCutRecovery.recover _ (SourceCheck.candidate (SourceCheck.result (encodedInput F)))).value at checked
  rw [CheckSourceBridge.candidate_retained F three] at checked
  exact checked

theorem checked_original_source (F : CNFFormula) :
    (Recovery.called (checkedState F.variableCount (encodedInput (NativeTseitin.frontend F)))).core.output =
      (MeasuredSourceRecovery.candidate F (MeasuredSourceCache.fromSource F).value).value := by
  have checked := original_source F (MeasuredSourceCache.fromSource F).value
    (checkedState F.variableCount (encodedInput (NativeTseitin.frontend F))) (List.length_replicate ..)
    (SourceCheck.result_data (NativeTseitin.frontend F).variableCount (NativeTseitin.frontend F).clauses).formulaRead
    (checked_matching _ (NativeFrontend.frontend_three F))
    (checked_variables _ (NativeFrontend.frontend_three F))
  change (Recovery.called (checkedState F.variableCount (encodedInput (NativeTseitin.frontend F)))).core.output =
    (MeasuredSourceRecovery.finish F (MeasuredSourceCache.fromSource F).value
      (SourceCheck.candidate (SourceCheck.result (encodedInput (NativeTseitin.frontend F))))).value at checked
  rw [CheckSourceBridge.candidate_retained _ (NativeFrontend.frontend_three F)] at checked
  exact checked

theorem candidate_spec_sound (F : CNFFormula) (three : ThreeCore F) (a : BitString)
    (answer : MeasuredRun.spec (selection F three) = .candidate a) :
    F.Satisfied (CNFCore.recover F a) := by
  unfold MeasuredRun.spec at answer
  cases h : (List.finRange (CNFCore.positions F).length).find?
      (fun i => !NativeSource.clauseTrue (selection F three) (NativeBasis.sigma (selection F three)) i) with
  | none =>
      rw [h] at answer
      cases answer
      exact NativeSource.firstFailed_none F three h
  | some i =>
      rw [h] at answer
      cases answer

theorem transport_candidate {c c' : Nat} (hc : c = c') (a : BitString) :
    MeasuredRunCorrectness.transportOutput hc (MeasuredRun.Output.candidate (c := c) a) =
      MeasuredRun.Output.candidate (c := c') a := by
  cases hc
  rfl

theorem cache_candidate_sound (F : CNFFormula) (three : ThreeCore F)
    (b : MeasuredSourceCache.Built F three)
    (passed : (MeasuredCandidate.firstFailed (MeasuredCache.operations b.data)).value = none) :
    F.Satisfied (b.context.toCutData.recover
      (MeasuredCandidate.assignment (MeasuredCache.operations b.data)).value) := by
  let a := (MeasuredCandidate.assignment (MeasuredCache.operations b.data)).value
  have computed : (MeasuredRun.run (MeasuredCache.operations b.data)).value = .candidate a := by
    simp only [MeasuredRun.run,passed]
    rfl
  have runtime : MeasuredRun.spec (MeasuredCache.selection b.data) = .candidate a := by
    rw [MeasuredCache.selection_eq]
    exact (MeasuredRun.run_value (MeasuredCache.operations b.data)).symm.trans computed
  have same : NativeDimensionCache.transportSelection b.columns_eq b.rows_eq
      (MeasuredCache.selection b.data) = selection F three :=
    MeasuredSourceCache.canonicalSelection_eq b
  have canonical : MeasuredRun.spec (selection F three) = .candidate a := by
    rw [← same,MeasuredRunCorrectness.spec_transport,runtime,transport_candidate]
  rw [b.context.toCutData.recover_eq]
  exact candidate_spec_sound F three a canonical

theorem checked_model_sound (F : CNFFormula)
    (passed : (MeasuredCandidate.firstFailed
      (MeasuredCache.operations (MeasuredSourceCache.fromSource F).value.data)).value = none) :
    F.Satisfied
      (Recovery.called (checkedState F.variableCount (encodedInput (NativeTseitin.frontend F)))).core.output := by
  rw [checked_original_source]
  have correct := cache_candidate_sound (NativeTseitin.frontend F)
    (NativeFrontend.frontend_three F) (MeasuredSourceCache.fromSource F).value passed
  change F.Satisfied (MeasuredSourceRecovery.finish F (MeasuredSourceCache.fromSource F).value
    (MeasuredCandidate.assignment
      (MeasuredCache.operations (MeasuredSourceCache.fromSource F).value.data)).value).value
  rw [MeasuredSourceRecovery.finish_value]
  exact NativeTseitin.frontend_recovery F _ correct

theorem checked_model_from_runtime_success (F : CNFFormula)
    (passed : (SourceCheck.result (encodedInput (NativeTseitin.frontend F))).registers.output =
      TableOwner.answer none) :
    F.Satisfied
      (Recovery.called (checkedState F.variableCount (encodedInput (NativeTseitin.frontend F)))).core.output := by
  apply checked_model_sound F
  have computed := CheckSourceBridge.result_fromSource F
  rw [passed] at computed
  cases h : (MeasuredCandidate.firstFailed
      (MeasuredCache.operations (MeasuredSourceCache.fromSource F).value.data)).value with
  | none => rfl
  | some i =>
      rw [h] at computed
      cases computed



end PNP.Concrete.NativeNormalization.RecoverySourceBridge

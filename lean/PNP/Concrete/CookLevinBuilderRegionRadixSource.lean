/-
Copyright (c) 2026 PNP Labs.

Source-derived radix entry programs for the canonical region branches.
Widths, state count and the literal three are copied from polynomial registers
already computed by initialization. The selected coordinate is copied from the
actual dispatch frame, then the fixed-count radix machine executes.

These are branch-entry programs. Wiring them into one uniform dispatcher,
constructing the local constraints, input reads and the full builder loop
remain separate; the region parameter must not become an input oracle.
-/

import PNP.Concrete.CookLevinBuilderPolynomialRegisterCopies

namespace PNP.Concrete.CookLevin.BuilderRegionRadixSource

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count)
open BuilderClauseDividerOperands (quotient)
open BuilderConstraintRegionRegisters (Region)
open BuilderConstraintRegionDispatch (regionTag)
open BuilderPolynomialRegisterCopies (Address)

inductive Field where
  | shapeWidth | tapeWidth | states | three
  deriving DecidableEq, Repr

private def shapeAddress {language : Language} (verifier : PolynomialTimeVerifier language)
    (address : Address (BuilderConstraintRegionRegisters.termPolynomial verifier .shape)) :
    Address (formulaClauseCountPolynomial verifier) :=
  .mulLeft (.addLeft (.addLeft (.addLeft (.addLeft address))))

private def controlAddress {language : Language} (verifier : PolynomialTimeVerifier language)
    (address : Address (BuilderConstraintRegionRegisters.termPolynomial verifier .control)) :
    Address (formulaClauseCountPolynomial verifier) :=
  .mulLeft (.addLeft (.addLeft (.addLeft (.addRight address))))

private def preservationAddress {language : Language} (verifier : PolynomialTimeVerifier language)
    (address : Address (BuilderConstraintRegionRegisters.termPolynomial verifier .preservation)) :
    Address (formulaClauseCountPolynomial verifier) :=
  .mulLeft (.addLeft (.addLeft (.addRight address)))

def fieldAddress {language : Language} (verifier : PolynomialTimeVerifier language) :
    Field → Address (formulaClauseCountPolynomial verifier)
  | .shapeWidth => shapeAddress verifier (.mulRight (.root _))
  | .tapeWidth => shapeAddress verifier (.mulRight (.addLeft (.root _)))
  | .states => controlAddress verifier (.mulRight (.mulRight (.root _)))
  | .three => preservationAddress verifier (.mulLeft (.root _))

def fieldPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) : Field → NatPolynomial
  | .shapeWidth => .add (formulaTapeWidthPolynomial verifier) (.constant 2)
  | .tapeWidth => formulaTapeWidthPolynomial verifier
  | .states => formulaStateCountPolynomial verifier
  | .three => .constant 3

theorem fieldAddress_selected {language : Language} (verifier : PolynomialTimeVerifier language) (field : Field) :
    (fieldAddress verifier field).selected = fieldPolynomial verifier field := by
  cases field <;> rfl

def fieldValue {language : Language} (problem : VerifierTableauProblem language) (field : Field) : Nat :=
  (fieldAddress problem.verifier field).selected.eval problem.input.length

theorem fieldValue_eq {language : Language} (problem : VerifierTableauProblem language) (field : Field) :
    fieldValue problem field = (fieldPolynomial problem.verifier field).eval problem.input.length := by
  unfold fieldValue
  rw [fieldAddress_selected]

theorem fieldValue_shapeWidth {language : Language} (problem : VerifierTableauProblem language) :
    fieldValue problem .shapeWidth = problem.dimensions.tapeWidth problem.tableauInputMode + 2 := by
  rw [fieldValue_eq]
  have h := problem.formulaTapeWidthPolynomial_eval
  simp only [BitString.size] at h
  change (formulaTapeWidthPolynomial problem.verifier).eval problem.input.length + 2 = _
  rw [h]

theorem fieldValue_tapeWidth {language : Language} (problem : VerifierTableauProblem language) :
    fieldValue problem .tapeWidth = problem.dimensions.tapeWidth problem.tableauInputMode := by
  rw [fieldValue_eq]
  exact problem.formulaTapeWidthPolynomial_eval

theorem fieldValue_states {language : Language} (problem : VerifierTableauProblem language) :
    fieldValue problem .states = problem.dimensions.stateBound := by
  rw [fieldValue_eq]
  exact problem.formulaStateCountPolynomial_eval

theorem fieldValue_three {language : Language} (problem : VerifierTableauProblem language) :
    fieldValue problem .three = 3 := rfl

theorem fieldValue_positive {language : Language} (problem : VerifierTableauProblem language) (field : Field) :
    0 < fieldValue problem field := by
  cases field with
  | shapeWidth => rw [fieldValue_shapeWidth]; omega
  | tapeWidth =>
    rw [fieldValue_tapeWidth]
    exact problem.dimensions.tapeWidth_positive problem.tableauInputMode
  | states =>
    rw [fieldValue_states]
    change 0 < machineStateBound problem.rawMachine
    unfold machineStateBound
    exact Nat.zero_lt_succ _
  | three => exact Nat.zero_lt_succ 2

/-- Least-significant split first; fixed by the canonical region schemas. -/
def radixFields : Region → List Field
  | .shape => [.shapeWidth]
  | .initial => []
  | .control => [.three, .three, .states, .tapeWidth]
  | .preservation => [.three, .tapeWidth, .tapeWidth]
  | .accepting => []

def radices {language : Language} (problem : VerifierTableauProblem language) (region : Region) : List Nat :=
  (radixFields region).map (fieldValue problem)

def addresses {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    List (Address (formulaClauseCountPolynomial verifier)) :=
  (radixFields region).reverse.map (fieldAddress verifier)

theorem address_count {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (addresses verifier region).length = (radixFields region).length := by cases region <;> rfl

theorem radices_length {language : Language} (problem : VerifierTableauProblem language) (region : Region) :
    (radices problem region).length = (radixFields region).length := by
  simp only [radices, List.length_map]

theorem written_radices {language : Language} (problem : VerifierTableauProblem language) (region : Region) :
    BuilderPolynomialRegisterCopies.values (addresses problem.verifier region) problem.input.length =
      (radices problem region).reverse := by cases region <;> rfl

theorem radices_positive {language : Language} (problem : VerifierTableauProblem language) (region : Region) :
    ∀ radix ∈ radices problem region, 0 < radix := by
  intro radix hMem
  obtain ⟨field, _, rfl⟩ := List.mem_map.mp hMem
  exact fieldValue_positive problem field

theorem shape_radices {language : Language} (problem : VerifierTableauProblem language) :
    radices problem .shape = [problem.dimensions.tapeWidth problem.tableauInputMode + 2] := by
  simp only [radices, radixFields, List.map_cons, List.map_nil, fieldValue_shapeWidth]

theorem control_radices {language : Language} (problem : VerifierTableauProblem language) :
    radices problem .control = [3, 3, problem.dimensions.stateBound,
      problem.dimensions.tapeWidth problem.tableauInputMode] := by
  simp only [radices, radixFields, List.map_cons, List.map_nil, fieldValue_three,
    fieldValue_states, fieldValue_tapeWidth]

theorem preservation_radices {language : Language} (problem : VerifierTableauProblem language) :
    radices problem .preservation = [3, problem.dimensions.tapeWidth problem.tableauInputMode,
      problem.dimensions.tapeWidth problem.tableauInputMode] := by
  simp only [radices, radixFields, List.map_cons, List.map_nil, fieldValue_three, fieldValue_tapeWidth]

def sourceAfter {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  BuilderOperandRegisters.newerValues problem index remaining .clauseCount ++
    BuilderConstraintRegionRegisters.coordinateSuffix problem index

theorem source_layout {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderClauseCoordinateRegisters.finalValues problem index remaining =
      registerValues (formulaClauseCountPolynomial problem.verifier) problem.input.length ++
        sourceAfter problem index remaining := by
  rw [BuilderClauseCoordinateRegisters.finalValues_eq,
    BuilderOperandRegisters.retainedValues_selection problem .clauseCount index remaining]
  rw [BuilderOperandRegisters.registerValues_rootPrefix (formulaClauseCountPolynomial problem.verifier) problem.input.length]
  simp only [BuilderOperandRegisters.olderValues, BuilderOperandRegisters.copiedValue, sourceAfter,
    BuilderConstraintRegionRegisters.coordinateSuffix, List.append_assoc]

def sourceSuffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (region : Region) : List Nat :=
  sourceAfter problem index remaining ++ BuilderConstraintRegionAssembly.preparedFrame problem index ++
    BuilderConstraintRegionSource.selectedScratch problem index region

def sourceCount {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) : Nat :=
  BuilderOperandRegisters.newerCount verifier .clauseCount + 22 + 4 * regionTag region

theorem selectedScratch_length {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (region : Region) :
    (BuilderConstraintRegionSource.selectedScratch problem index region).length = 4 * regionTag region + 5 := by
  cases region <;>
    simp only [BuilderConstraintRegionSource.selectedScratch, BuilderConstraintRegionDispatch.prefixScratch,
      BuilderConstraintRegionDispatch.rejectScratch, BuilderConstraintRegionDispatch.restored_length,
      List.length_append, List.length_cons, List.length_nil, regionTag]

theorem sourceSuffix_length {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) :
    (sourceSuffix problem index remaining region).length = sourceCount problem.verifier region := by
  simp only [sourceSuffix, sourceAfter, sourceCount, List.length_append,
    BuilderOperandRegisters.newerValues_length, BuilderConstraintRegionRegisters.coordinateSuffix,
    List.length_cons, List.length_nil, BuilderConstraintRegionAssembly.preparedFrame_length,
    selectedScratch_length]
  omega

def selectedValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) : List Nat :=
  BuilderConstraintRegionAssembly.finalValues problem index remaining ++
    BuilderConstraintRegionSource.selectedScratch problem index region

theorem selectedValues_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) :
    selectedValues problem index remaining region =
      BuilderPolynomialRegisterCopies.inputValues (formulaClauseCountPolynomial problem.verifier)
        problem.input.length [] (sourceSuffix problem index remaining region) := by
  unfold selectedValues BuilderConstraintRegionAssembly.finalValues
  rw [source_layout]
  simp only [BuilderPolynomialRegisterCopies.inputValues, sourceSuffix, List.nil_append, List.append_assoc]

theorem selected_source_handoff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    (BuilderConstraintRegionSource.finalConfiguration problem index remaining output).tape =
      endTape (selectedValues problem index remaining region) (inside problem.input output) [] :=
  BuilderConstraintRegionSource.final_selected_tape problem index remaining output region hRegion

private theorem chain_run (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some { state := first.acceptState, tape := middle })
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some { state := second.acceptState, tape := final }) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some { state := (WorkMachineChain.machine first second).acceptState, tape := final } :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

def prepareMachine {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) : WorkMachine :=
  WorkMachineChain.machine
    (BuilderPolynomialRegisterCopies.machine (addresses verifier region) (sourceCount verifier region))
    (RegisterCopy.machine ((radixFields region).length + 1))

def prepareSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (region : Region) : Nat :=
  BuilderPolynomialRegisterCopies.workSteps (addresses problem.verifier region) problem.input.length
    (sourceSuffix problem index remaining region) + 1 +
    RegisterCopy.steps ([regionTag region] ++ (radices problem region).reverse)
      (BuilderConstraintRegionSource.localCoordinate problem index region)

def preparedValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (region : Region) : List Nat :=
  selectedValues problem index remaining region ++ (radices problem region).reverse ++
    [BuilderConstraintRegionSource.localCoordinate problem index region]

theorem prepare_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (workspace : List WorkSymbol) (region : Region) :
    workRunExact? (prepareMachine problem.verifier region) (prepareSteps problem index remaining region)
      (workStartConfiguration (prepareMachine problem.verifier region)
        (endTape (selectedValues problem index remaining region) workspace [])) =
      some {
        state := (prepareMachine problem.verifier region).acceptState
        tape := endTape (preparedValues problem index remaining region) workspace []
      } := by
  have hFields := BuilderPolynomialRegisterCopies.workRunExact (addresses problem.verifier region)
    (sourceCount problem.verifier region) problem.input.length [] (sourceSuffix problem index remaining region)
    workspace (sourceSuffix_length problem index remaining region)
  rw [← selectedValues_layout, written_radices] at hFields
  have hLength : ([regionTag region] ++ (radices problem region).reverse).length =
      (radixFields region).length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse, radices_length]
    omega
  have hCoordinate := BuilderRegionComparisonOperands.copy_workRunExact ((radixFields region).length + 1)
    (BuilderConstraintRegionAssembly.finalValues problem index remaining ++
      BuilderConstraintRegionDispatch.prefixScratch (BuilderConstraintRegionSource.lengths problem)
        (BuilderClauseDividerExecution.constraintIndex problem index) region ++
      BuilderConstraintRegionDispatch.restored (BuilderConstraintRegionSource.localCoordinate problem index region)
        (BuilderConstraintRegionRegisters.regionLength problem region))
    ([regionTag region] ++ (radices problem region).reverse)
    (BuilderConstraintRegionSource.localCoordinate problem index region) workspace [] hLength
  have hCopy :
      workRunExact? (RegisterCopy.machine ((radixFields region).length + 1))
        (RegisterCopy.steps ([regionTag region] ++ (radices problem region).reverse)
          (BuilderConstraintRegionSource.localCoordinate problem index region))
        (workStartConfiguration (RegisterCopy.machine ((radixFields region).length + 1))
          (endTape (selectedValues problem index remaining region ++ (radices problem region).reverse) workspace [])) =
        some {
          state := (RegisterCopy.machine ((radixFields region).length + 1)).acceptState
          tape := endTape (preparedValues problem index remaining region) workspace []
        } := by
    simpa only [selectedValues, BuilderConstraintRegionSource.selectedScratch, preparedValues,
      List.append_assoc, List.cons_append, List.nil_append, List.drop_nil] using hCoordinate
  exact chain_run _ _ _ _ _ _ _ hFields hCopy

/-- A branch program, to be wired to its actual region node in the uniform graph. -/
def machine {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) : WorkMachine :=
  WorkMachineChain.machine (prepareMachine verifier region)
    (BuilderRegionRadixDecoder.machine (radixFields region).length 0)

def workSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) : Nat :=
  prepareSteps problem index remaining region + 1 +
    BuilderRegionRadixDecoder.workSteps (radices problem region) []
      (BuilderConstraintRegionSource.localCoordinate problem index region)

def finalValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) : List Nat :=
  BuilderRegionRadixDecoder.finalValues (selectedValues problem index remaining region)
    (radices problem region) [] (BuilderConstraintRegionSource.localCoordinate problem index region)

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (workspace : List WorkSymbol) (region : Region) :
    workRunExact? (machine problem.verifier region) (workSteps problem index remaining region)
      (workStartConfiguration (machine problem.verifier region)
        (endTape (selectedValues problem index remaining region) workspace [])) =
      some {
        state := (machine problem.verifier region).acceptState
        tape := endTape (finalValues problem index remaining region) workspace []
      } := by
  have hPrepare := prepare_workRunExact problem index remaining workspace region
  have hDivide := BuilderRegionRadixDecoder.workRunExact 0 (selectedValues problem index remaining region)
    (radices problem region) [] (BuilderConstraintRegionSource.localCoordinate problem index region) workspace rfl
    (radices_positive problem region)
  simp only [BuilderRegionRadixDecoder.initialConfiguration, BuilderRegionRadixDecoder.finalConfiguration,
    BuilderRegionRadixDecoder.inputValues, List.append_nil, radices_length] at hDivide
  exact chain_run _ _ _ _ _ _ _ hPrepare hDivide

theorem source_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    workRunExact? (machine problem.verifier region) (workSteps problem index remaining region)
      (workStartConfiguration (machine problem.verifier region)
        (BuilderConstraintRegionSource.finalConfiguration problem index remaining output).tape) =
      some {
        state := (machine problem.verifier region).acceptState
        tape := endTape (finalValues problem index remaining region) (inside problem.input output) []
      } := by
  rw [selected_source_handoff problem index remaining output region hRegion]
  exact workRunExact problem index remaining (inside problem.input output) region

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    run (compileWorkMachine (machine problem.verifier region)) (6 * workSteps problem index remaining region)
      (encodeWorkConfiguration (workStartConfiguration (machine problem.verifier region)
        (BuilderConstraintRegionSource.finalConfiguration problem index remaining output).tape)) =
      encodeWorkConfiguration {
        state := (machine problem.verifier region).acceptState
        tape := endTape (finalValues problem index remaining region) (inside problem.input output) []
      } :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (source_workRunExact problem index remaining output region hRegion)

theorem finalValues_preserve_source {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) :
    finalValues problem index remaining region =
      preparedValues problem index remaining region ++
        BuilderRegionRadixDecoder.extraValues (radices problem region)
          (BuilderConstraintRegionSource.localCoordinate problem index region) := by
  simp only [finalValues, BuilderRegionRadixDecoder.finalValues_eq,
    BuilderRegionRadixDecoder.inputValues, preparedValues, List.append_nil, List.append_assoc]

theorem written_coordinate_reconstruct {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) :
    BuilderRegionRadixDecoder.reconstruct (radices problem region)
      (BuilderRegionRadixDecoder.packetDigits
        (BuilderRegionRadixDecoder.extraValues (radices problem region)
          (BuilderConstraintRegionSource.localCoordinate problem index region)))
      ((finalValues problem index remaining region).reverse.headD 0) =
        BuilderConstraintRegionSource.localCoordinate problem index region :=
  BuilderRegionRadixDecoder.reconstruct_written_packets _ _ _ _

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
    WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
    WorkMachineChain.noRuleAtAccept first { second with acceptState := second.rejectState } hSecond.2.2.1,
    WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩

private theorem copy_good (offset : Nat) : Good (RegisterCopy.machine offset) := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct _, ?_, ?_, RegisterCopy.machine_acceptState_ne_rejectState _⟩
  · intro rule hRule
    exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState _ rule hRule)
  · intro rule hRule
    have h := RegisterCopy.rule_source_lt_acceptState _ rule hRule
    rw [RegisterCopy.machine_acceptState] at h
    rw [RegisterCopy.machine_rejectState]
    omega

private theorem good {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    Good (machine verifier region) := by
  have hFields : Good (BuilderPolynomialRegisterCopies.machine (addresses verifier region) (sourceCount verifier region)) :=
    ⟨BuilderPolynomialRegisterCopies.rules_pairwise_query_distinct _ _,
      BuilderPolynomialRegisterCopies.noRuleAtAccept _ _, BuilderPolynomialRegisterCopies.noRuleAtReject _ _,
      BuilderPolynomialRegisterCopies.acceptState_ne_rejectState _ _⟩
  have hPrepare := chain_good _ _ hFields (copy_good ((radixFields region).length + 1))
  have hDecoder : Good (BuilderRegionRadixDecoder.machine (radixFields region).length 0) :=
    ⟨BuilderRegionRadixDecoder.rules_pairwise_query_distinct _ _, BuilderRegionRadixDecoder.noRuleAtAccept _ _,
      BuilderRegionRadixDecoder.noRuleAtReject _ _, BuilderRegionRadixDecoder.acceptState_ne_rejectState _ _⟩
  exact chain_good _ _ hPrepare hDecoder

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (machine verifier region).rules.Pairwise WorkMachineChain.QueryDistinct := (good verifier region).1

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    WorkMachineChain.NoRuleAtAccept (machine verifier region) := (good verifier region).2.1

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier region) (machine verifier region).rejectState := (good verifier region).2.2.1

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (machine verifier region).acceptState ≠ (machine verifier region).rejectState := (good verifier region).2.2.2

def sourceBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.mul (.constant 31) (BuilderDividerSourceExecution.sourceSpan verifier)) (.constant 42)

theorem selected_span_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    (registerWord (selectedValues problem index remaining region)).length ≤
      (sourceBound problem.verifier).eval problem.input.length := by
  unfold selectedValues
  rw [← BuilderConstraintRegionSource.finalValues_of_region problem index remaining region hRegion]
  exact BuilderConstraintRegionSource.final_register_span_le problem index remaining hBody hBalance

theorem coordinate_le_span {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (bound : Nat)
    (hSpan : (registerWord (selectedValues problem index remaining region)).length ≤ bound) :
    BuilderConstraintRegionSource.localCoordinate problem index region ≤ bound := by
  simp only [selectedValues, BuilderConstraintRegionSource.selectedScratch, registerWord_length,
    List.length_append, List.length_cons, List.length_nil, List.sum_append, List.sum_cons, List.sum_nil] at hSpan
  omega

theorem radices_le_span {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (bound : Nat)
    (hSpan : (registerWord (selectedValues problem index remaining region)).length ≤ bound) :
    ∀ radix ∈ radices problem region, radix ≤ bound := by
  intro radix hMem
  obtain ⟨field, _, rfl⟩ := List.mem_map.mp hMem
  rw [selectedValues_layout] at hSpan
  exact (BuilderPolynomialRegisterCopies.selection_bounds (fieldAddress problem.verifier field)
    problem.input.length [] (sourceSuffix problem index remaining region) bound hSpan).1

def preparedBound (splitCount bound : Nat) : Nat :=
  2 * BuilderPolynomialRegisterCopies.spanBound splitCount bound + 1

theorem prepared_span_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (bound : Nat)
    (hSpan : (registerWord (selectedValues problem index remaining region)).length ≤ bound) :
    (registerWord (preparedValues problem index remaining region)).length ≤
      preparedBound (radixFields region).length bound := by
  have hQ := coordinate_le_span problem index remaining region bound hSpan
  have hGrow := BuilderPolynomialRegisterCopies.spanBound_ge (radixFields region).length bound
  rw [selectedValues_layout] at hSpan
  have hFields := BuilderPolynomialRegisterCopies.final_span_le (addresses problem.verifier region)
    problem.input.length [] (sourceSuffix problem index remaining region) bound hSpan
  rw [← selectedValues_layout, written_radices, address_count] at hFields
  simp only [preparedValues, preparedBound, registerWord_append, List.length_append] at *
  have hQWord :
      (registerWord [BuilderConstraintRegionSource.localCoordinate problem index region]).length =
        1 + BuilderConstraintRegionSource.localCoordinate problem index region := by
    simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [hQWord]
  omega

def workBound (splitCount bound : Nat) : Nat :=
  BuilderPolynomialRegisterCopies.workBound splitCount bound + 1 +
    BuilderPolynomialRegisterCopies.copyBound (BuilderPolynomialRegisterCopies.spanBound splitCount bound) + 1 +
    BuilderRegionRadixDecoder.workBound splitCount (preparedBound splitCount bound)

theorem workSteps_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (bound : Nat)
    (hSpan : (registerWord (selectedValues problem index remaining region)).length ≤ bound) :
    workSteps problem index remaining region ≤ workBound (radixFields region).length bound := by
  have hQ := coordinate_le_span problem index remaining region bound hSpan
  have hRadices := radices_le_span problem index remaining region bound hSpan
  have hGrow := BuilderPolynomialRegisterCopies.spanBound_ge (radixFields region).length bound
  have hInput := hSpan
  rw [selectedValues_layout] at hInput
  have hFields := BuilderPolynomialRegisterCopies.workSteps_le (addresses problem.verifier region)
    problem.input.length [] (sourceSuffix problem index remaining region) bound hInput
  rw [address_count] at hFields
  have hFieldSpan := BuilderPolynomialRegisterCopies.final_span_le (addresses problem.verifier region)
    problem.input.length [] (sourceSuffix problem index remaining region) bound hInput
  rw [← selectedValues_layout, written_radices, address_count] at hFieldSpan
  have hNewer :
      ([regionTag region] ++ (radices problem region).reverse).length +
        ([regionTag region] ++ (radices problem region).reverse).sum ≤
          BuilderPolynomialRegisterCopies.spanBound (radixFields region).length bound := by
    simp only [selectedValues, BuilderConstraintRegionSource.selectedScratch, registerWord_length,
      List.length_append, List.length_cons, List.length_nil, List.sum_append, List.sum_cons, List.sum_nil] at hFieldSpan ⊢
    omega
  have hCopy := RegisterCopy.steps_le ([regionTag region] ++ (radices problem region).reverse)
    (BuilderConstraintRegionSource.localCoordinate problem index region)
    (BuilderPolynomialRegisterCopies.spanBound (radixFields region).length bound) (Nat.le_trans hQ hGrow) hNewer
  have hCopy' :
      RegisterCopy.steps ([regionTag region] ++ (radices problem region).reverse)
        (BuilderConstraintRegionSource.localCoordinate problem index region) ≤
      BuilderPolynomialRegisterCopies.copyBound
        (BuilderPolynomialRegisterCopies.spanBound (radixFields region).length bound) := by
    simpa only [BuilderPolynomialRegisterCopies.copyBound, Nat.pow_two, Nat.mul_assoc] using hCopy
  have hPrepared : bound ≤ preparedBound (radixFields region).length bound := by
    unfold preparedBound
    omega
  have hDecode := BuilderRegionRadixDecoder.workSteps_le (radices problem region) []
    (BuilderConstraintRegionSource.localCoordinate problem index region)
    (preparedBound (radixFields region).length bound)
    (Nat.le_trans hQ hPrepared) (by simp only [List.length_nil, List.sum_nil]; omega)
    (fun radix hMem => Nat.le_trans (hRadices radix hMem) hPrepared) (radices_positive problem region)
  rw [radices_length] at hDecode
  unfold workSteps prepareSteps workBound
  omega

def preparedPolynomial (splitCount : Nat) (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 2) (BuilderPolynomialRegisterCopies.spanPolynomial splitCount bound)) (.constant 1)

theorem preparedPolynomial_eval (splitCount : Nat) (bound : NatPolynomial) (input : Nat) :
    (preparedPolynomial splitCount bound).eval input = preparedBound splitCount (bound.eval input) := by
  simp only [preparedPolynomial, preparedBound, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, BuilderPolynomialRegisterCopies.spanPolynomial_eval]

def rawTimePolynomial (splitCount : Nat) (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderPolynomialRegisterCopies.rawTimePolynomial splitCount bound)
    (.add (.constant 6)
      (.add (.mul (.constant 6) (BuilderPolynomialRegisterCopies.copyPolynomial
        (BuilderPolynomialRegisterCopies.spanPolynomial splitCount bound)))
        (.add (.constant 6) (BuilderRegionRadixDecoder.rawTimePolynomial splitCount
          (preparedPolynomial splitCount bound)))))

theorem rawTimePolynomial_eval (splitCount : Nat) (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial splitCount bound).eval input = 6 * workBound splitCount (bound.eval input) := by
  simp only [rawTimePolynomial, workBound, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, BuilderPolynomialRegisterCopies.rawTimePolynomial_eval,
    BuilderPolynomialRegisterCopies.copyPolynomial_eval, BuilderPolynomialRegisterCopies.spanPolynomial_eval,
    BuilderRegionRadixDecoder.rawTimePolynomial_eval, preparedPolynomial_eval,
    Nat.mul_add, Nat.mul_one, Nat.add_assoc]

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) : NatPolynomial :=
  rawTimePolynomial (radixFields region).length (sourceBound verifier)

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    6 * workSteps problem index remaining region ≤
      (rawTimeBound problem.verifier region).eval problem.input.length := by
  unfold rawTimeBound
  rw [rawTimePolynomial_eval]
  exact Nat.mul_le_mul_left 6 (workSteps_le problem index remaining region _
    (selected_span_le problem index remaining region hBody hBalance hRegion))

theorem final_span_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (bound : Nat)
    (hSpan : (registerWord (selectedValues problem index remaining region)).length ≤ bound) :
    (registerWord (finalValues problem index remaining region)).length ≤
      preparedBound (radixFields region).length bound +
        (radixFields region).length * (3 * preparedBound (radixFields region).length bound + 6) := by
  have hQ := coordinate_le_span problem index remaining region bound hSpan
  have hRadices := radices_le_span problem index remaining region bound hSpan
  have hGrow := BuilderPolynomialRegisterCopies.spanBound_ge (radixFields region).length bound
  have hBound : bound ≤ preparedBound (radixFields region).length bound := by unfold preparedBound; omega
  have hPrepared := prepared_span_le problem index remaining region bound hSpan
  have h := BuilderRegionRadixDecoder.final_register_span_le (selectedValues problem index remaining region)
    (radices problem region) [] (BuilderConstraintRegionSource.localCoordinate problem index region)
    (preparedBound (radixFields region).length bound) (Nat.le_trans hQ hBound)
    (fun radix hMem => Nat.le_trans (hRadices radix hMem) hBound)
  simp only [BuilderRegionRadixDecoder.inputValues, List.append_nil, radices_length] at h
  exact Nat.le_trans h (Nat.add_le_add_right hPrepared _)

end PNP.Concrete.CookLevin.BuilderRegionRadixSource

/-
Copyright (c) 2026 PNP Labs.

Bind a token request to the actual source cursor and its canonical five-family
payload. Fixed root locators read the preserved index, width and quotient;
multiplication and restored comparison recover the real token remainder.
The payload is retained, not erased and reconstructed. No request value or
branch certificate is a machine input. Token dispatch and the complete builder
remain downstream obligations.
-/

import PNP.Concrete.CookLevinBuilderSourceClauseCoordinate
import PNP.Concrete.CookLevinBuilderExclusionClauseTokenSelector

namespace PNP.Concrete.CookLevin.BuilderSourceTokenRequest

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count width)
open BuilderClauseDividerOperands (quotient clauseWidth)
open BuilderClauseDividerExecution (clauseIndex constraintIndex)
open BuilderArbitrarySlotHeaderRouter
open PipelineStateNamespace (renameConfiguration)

inductive Field where
  | index | width | quotient | clause
  deriving DecidableEq, Repr

def fieldValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Field → Nat
  | .index => index
  | .width => width problem
  | .quotient => quotient problem index
  | .clause => clauseIndex problem index

def indexBefore {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  BuilderOperandRegisters.retainedValues problem index remaining ++ [count problem, 0]
def indexOrdinal {language : Language} (verifier : PolynomialTimeVerifier language) : Nat :=
  nodeCount (BuilderFullScheduleCursorController.bodySlotCountPolynomial verifier) +
    nodeCount (BuilderDimensionRegisters.widthPolynomial verifier) + 5
def fieldOrdinal {language : Language} (verifier : PolynomialTimeVerifier language) : Field → Nat
  | .index => indexOrdinal verifier
  | .width => indexOrdinal verifier + 1
  | .quotient => indexOrdinal verifier + 2
  | .clause => BuilderSourceClauseCoordinate.rootOrdinal verifier
def sourceValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : List Nat :=
  BuilderSourceClauseCoordinate.finalValues problem index remaining hBody
def commonAfter {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : List Nat :=
  [count problem, 0, constraintIndex problem index * clauseWidth problem, clauseIndex problem index] ++
    BuilderSourceClauseCoordinate.after problem index remaining hBody ++ [clauseIndex problem index]
def fieldBefore {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Field → List Nat
  | .index => indexBefore problem index remaining
  | .width => indexBefore problem index remaining ++ [index]
  | .quotient => indexBefore problem index remaining ++ [index, width problem]
  | .clause => BuilderSourceClauseCoordinate.before problem index remaining
def fieldAfter {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : Field → List Nat
  | .index => [width problem, quotient problem index] ++ commonAfter problem index remaining hBody
  | .width => [quotient problem index] ++ commonAfter problem index remaining hBody
  | .quotient => commonAfter problem index remaining hBody
  | .clause => BuilderSourceClauseCoordinate.after problem index remaining hBody ++ [clauseIndex problem index]

theorem source_layout {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) :
    sourceValues problem index remaining hBody =
      indexBefore problem index remaining ++ [index, width problem, quotient problem index] ++
        commonAfter problem index remaining hBody := by
  rw [sourceValues, BuilderSourceClauseCoordinate.finalValues, BuilderSourceClauseCoordinate.source_coordinate_layout]
  simp only [BuilderSourceClauseCoordinate.before, indexBefore, commonAfter,
    List.append_assoc, List.cons_append, List.nil_append]

theorem field_layout {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) (field : Field) :
    sourceValues problem index remaining hBody =
      fieldBefore problem index remaining field ++ [fieldValue problem index field] ++
        fieldAfter problem index remaining hBody field := by
  cases field with
  | index =>
      rw [source_layout]
      simp only [fieldBefore, fieldValue, fieldAfter, List.append_assoc, List.cons_append, List.nil_append]
  | width =>
      rw [source_layout]
      simp only [fieldBefore, fieldValue, fieldAfter, List.append_assoc, List.cons_append, List.nil_append]
  | quotient =>
      rw [source_layout]
      simp only [fieldBefore, fieldValue, fieldAfter, List.append_assoc, List.cons_append, List.nil_append]
  | clause =>
      rw [sourceValues, BuilderSourceClauseCoordinate.finalValues, BuilderSourceClauseCoordinate.source_coordinate_layout]
      simp only [fieldBefore, fieldValue, fieldAfter, List.append_assoc]

theorem field_before_length {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (field : Field) :
    (fieldBefore problem index remaining field).length = fieldOrdinal problem.verifier field := by
  have hBase : (indexBefore problem index remaining).length = indexOrdinal problem.verifier := by
    simp only [indexBefore, indexOrdinal, BuilderOperandRegisters.retainedValues,
      BuilderOperandRegisters.prefixValues, List.length_append, List.length_cons, List.length_nil,
      registerValues_length]
    omega
  cases field with
  | index => exact hBase
  | width => simp only [fieldBefore, fieldOrdinal, List.length_append, List.length_cons, List.length_nil, hBase]
  | quotient => simp only [fieldBefore, fieldOrdinal, List.length_append, List.length_cons, List.length_nil, hBase]
  | clause => exact BuilderSourceClauseCoordinate.before_length problem index remaining

def fieldMachine {language : Language} (verifier : PolynomialTimeVerifier language) (field : Field) : WorkMachine :=
  BuilderRegisterRootCopy.machine (fieldOrdinal verifier field)
def fieldSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) (field : Field) (extra : List Nat) : Nat :=
  BuilderRegisterRootCopy.workSteps (fieldBefore problem index remaining field) (fieldValue problem index field)
    (fieldAfter problem index remaining hBody field ++ extra)

theorem field_workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) (field : Field) (extra : List Nat)
    (output : List CNFToken) (outside : List WorkSymbol) :
    workRunExact? (fieldMachine problem.verifier field) (fieldSteps problem index remaining hBody field extra)
      (workStartConfiguration (fieldMachine problem.verifier field)
        (endTape (sourceValues problem index remaining hBody ++ extra) (inside problem.input output) outside)) =
      some {
        state := (fieldMachine problem.verifier field).acceptState
        tape := endTape (sourceValues problem index remaining hBody ++ extra ++ [fieldValue problem index field])
          (inside problem.input output) (outside.drop (fieldValue problem index field + 1)) } := by
  have h := BuilderRegisterRootCopy.workRunExact (fieldOrdinal problem.verifier field)
    (fieldBefore problem index remaining field) (fieldValue problem index field)
    (fieldAfter problem index remaining hBody field ++ extra) (inside problem.input output).tail outside
    (field_before_length problem index remaining field)
  have hInside : leftMarker :: (inside problem.input output).tail = inside problem.input output := rfl
  simpa only [BuilderRegisterRootCopy.initialConfiguration, BuilderRegisterRootCopy.finalConfiguration,
    fieldMachine, fieldSteps, field_layout problem index remaining hBody field, hInside, List.append_assoc] using h

theorem field_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) (field : Field) (extra : List Nat) (outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (sourceValues problem index remaining hBody ++ extra)).length + outside.length ≤ bound.eval input) :
    (registerWord (sourceValues problem index remaining hBody ++ extra ++ [fieldValue problem index field])).length +
        (outside.drop (fieldValue problem index field + 1)).length ≤ (BuilderRegisterRootCopy.spanPolynomial bound).eval input ∧
      6 * fieldSteps problem index remaining hBody field extra ≤ (BuilderRegisterRootCopy.rawTimePolynomial bound).eval input := by
  have h := BuilderRegisterRootCopy.source_polynomial_bounds (fieldBefore problem index remaining field)
    (fieldValue problem index field) (fieldAfter problem index remaining hBody field ++ extra) outside bound input
    (by simpa only [field_layout problem index remaining hBody field, List.append_assoc] using hSpan)
  simpa only [field_layout problem index remaining hBody field, fieldSteps, List.append_assoc] using h

def consumed {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  width problem * quotient problem index
def tokenPosition {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  index % width problem
def comparisonResult {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : RawRouter.ComparisonResult :=
  RawRouter.compareResult 0 index (consumed problem index)

theorem token_reconstruction {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    tokenPosition problem index + consumed problem index = index :=
  Nat.mod_add_div index (width problem)

theorem comparison_residual {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    BuilderRegisterCompareResidual.resultCoordinate (comparisonResult problem index) = tokenPosition problem index := by
  have hParts := token_reconstruction problem index
  rw [comparisonResult, BuilderRegisterCompareResidual.resultCoordinate_eq,
    if_neg (show ¬ index < consumed problem index by omega)]
  omega

private def compareNode : WorkMachineProgramGraph.Node :=
  {name := 0, program := BuilderRegisterCompareResidual.machine, onAccept := .accept, onReject := .accept}
private def compareGraph : WorkMachineProgramGraph.Graph := {nodes := [compareNode], entry := compareNode.reference}
def compareMachine : WorkMachine := WorkMachineProgramGraph.machine compareGraph

private theorem compare_wellFormed : compareGraph.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact List.Pairwise.cons (by intro node h; cases h) List.Pairwise.nil
  · intro node hMem
    simp only [compareGraph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    subst node
    exact ⟨BuilderRegisterCompareResidual.rules_pairwise_query_distinct, BuilderRegisterCompareResidual.noRuleAtAccept,
      BuilderRegisterCompareResidual.noRuleAtReject, BuilderRegisterCompareResidual.acceptState_ne_rejectState⟩
  · exact ⟨compareNode, List.Mem.head _, rfl, rfl⟩
  · intro node hMem
    simp only [compareGraph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    subst node
    exact ⟨True.intro, True.intro⟩

private theorem configuration_eq (configuration : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : configuration.state = state) (hTape : configuration.tape = tape) :
    configuration = {state := state, tape := tape} := by
  cases configuration
  cases hState
  cases hTape
  rfl

private theorem compare_start (tape : WorkTape) :
    workStartConfiguration compareMachine tape =
      WorkMachineProgramGraph.endpointConfiguration (.node compareNode.reference) tape := rfl

private theorem compare_accept (tape : WorkTape) :
    ({state := compareMachine.acceptState, tape := tape} : WorkConfiguration) =
      WorkMachineProgramGraph.endpointConfiguration .accept tape := rfl

theorem compare_workRunExact (coordinate boundary : Nat) (older : List Nat) (inner outer : List WorkSymbol) :
    workRunExact? compareMachine (BuilderRegisterCompareResidual.workSteps coordinate boundary + 1)
      (workStartConfiguration compareMachine (endTape (older ++ [coordinate, boundary]) inner outer)) =
      some {
        state := compareMachine.acceptState
        tape := endTape (older ++ BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 coordinate boundary))
          inner (outer.drop (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 coordinate boundary))) } := by
  rw [compare_start, compare_accept]
  have hRun := BuilderRegisterCompareResidual.workRunExact coordinate boundary older inner outer
  have hTape : (BuilderRegisterCompareResidual.finalConfiguration coordinate boundary older inner outer).tape =
      endTape (older ++ BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 coordinate boundary))
        inner (outer.drop (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 coordinate boundary))) := rfl
  by_cases hLess : coordinate < boundary
  · have hState := (BuilderRegisterCompareResidual.final_accept_iff coordinate boundary older inner outer).mpr hLess
    rw [configuration_eq _ _ _ hState hTape] at hRun
    have hPath := WorkMachineProgramPath.AcceptPath.step (graph := compareGraph) compareNode .accept _ 0 _ _ _
      (List.Mem.head []) hRun (.terminal .accept _)
    have h := WorkMachineProgramPath.runExact compareGraph _ _ _ _ _ compare_wellFormed hPath
    simpa only [compareMachine, Nat.add_zero] using h
  · have hState := (BuilderRegisterCompareResidual.final_reject_iff coordinate boundary older inner outer).mpr (by omega)
    rw [configuration_eq _ _ _ hState hTape] at hRun
    have hPath := WorkMachineProgramPath.AcceptPath.stepReject (graph := compareGraph) compareNode .accept _ 0 _ _ _
      (List.Mem.head []) hRun (.terminal .accept _)
    have h := WorkMachineProgramPath.runExact compareGraph _ _ _ _ _ compare_wellFormed hPath
    simpa only [compareMachine, Nat.add_zero] using h

private theorem binary_run (operator : RegisterBinary.Operator) (older between : List Nat) (left right : Nat)
    (inner outer : List WorkSymbol) :
    workRunExact? (RegisterBinary.machine operator between.length) (RegisterBinary.steps operator between left right)
      (workStartConfiguration (RegisterBinary.machine operator between.length)
        (endTape (older ++ [left] ++ between ++ [right]) inner outer)) =
      some {
        state := (RegisterBinary.machine operator between.length).acceptState
        tape := endTape (older ++ [left] ++ between ++ [right, RegisterBinary.value operator left right])
          inner (outer.drop (RegisterBinary.value operator left right + 1)) } := by
  rw [RegisterBinary.machine_acceptState]
  exact RegisterBinary.workRunExact operator older between left right inner outer

private theorem multiply_workRunExact (older : List Nat) (left right : Nat) (inner outer : List WorkSymbol) :
    workRunExact? (RegisterBinary.machine .mul 0) (RegisterBinary.steps .mul [] left right)
      (workStartConfiguration (RegisterBinary.machine .mul 0) (endTape (older ++ [left,right]) inner outer)) =
      some {
        state := (RegisterBinary.machine .mul 0).acceptState
        tape := endTape (older ++ [left,right,left * right]) inner (outer.drop (left * right + 1)) } := by
  simpa only [RegisterBinary.value, List.append_nil, List.append_assoc, List.cons_append,
    List.nil_append, List.length_nil] using binary_run .mul older [] left right inner outer

def suffixExpression : BuilderRegisterExpression.Expr 2 := .argument ⟨0, by decide⟩
def suffixEnvironment (position clause : Nat) : Fin 2 → Nat := fun field => if field.val = 0 then position else clause
theorem suffix_environment_values (position clause : Nat) : List.ofFn (suffixEnvironment position clause) = [position,clause] := rfl
theorem suffix_expression_values (position clause : Nat) :
    BuilderRegisterExpression.values suffixExpression (suffixEnvironment position clause) = [position] := rfl

def extra {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat → List Nat
  | 0 => []
  | 1 => [width problem]
  | 2 => [width problem,quotient problem index]
  | 3 => [width problem,quotient problem index,consumed problem index]
  | 4 => [width problem,quotient problem index,consumed problem index,index]
  | 5 => [width problem,quotient problem index,consumed problem index,index,consumed problem index]
  | 6 => [width problem,quotient problem index,consumed problem index] ++
      BuilderRegisterCompareResidual.outputValues (comparisonResult problem index)
  | 7 => ([width problem,quotient problem index,consumed problem index] ++
      BuilderRegisterCompareResidual.outputValues (comparisonResult problem index)) ++ [clauseIndex problem index]
  | _ => ([width problem,quotient problem index,consumed problem index] ++
      BuilderRegisterCompareResidual.outputValues (comparisonResult problem index)) ++
      [clauseIndex problem index,tokenPosition problem index]
def allocation {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat → Nat
  | 0 => width problem + 1
  | 1 => quotient problem index + 1
  | 2 => consumed problem index + 1
  | 3 => index + 1
  | 4 => consumed problem index + 1
  | 5 => BuilderRegisterCompareResidual.allocatedCells (comparisonResult problem index)
  | 6 => clauseIndex problem index + 1
  | _ => tokenPosition problem index + 1
def phaseOutside {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (outer : List WorkSymbol) : Nat → List WorkSymbol
  | 0 => outer
  | phase + 1 => (phaseOutside problem index outer phase).drop (allocation problem index phase)
def stepMachine {language : Language} (verifier : PolynomialTimeVerifier language) : Nat → WorkMachine
  | 0 => fieldMachine verifier .width
  | 1 => fieldMachine verifier .quotient
  | 2 => RegisterBinary.machine .mul 0
  | 3 => fieldMachine verifier .index
  | 4 => BuilderRegisterExpression.machine suffixExpression 0
  | 5 => compareMachine
  | 6 => fieldMachine verifier .clause
  | _ => BuilderRegisterExpression.machine suffixExpression 0
def stepSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : Nat → Nat
  | 0 => fieldSteps problem index remaining hBody .width (extra problem index 0)
  | 1 => fieldSteps problem index remaining hBody .quotient (extra problem index 1)
  | 2 => RegisterBinary.steps .mul [] (width problem) (quotient problem index)
  | 3 => fieldSteps problem index remaining hBody .index (extra problem index 3)
  | 4 => BuilderRegisterExpression.workSteps suffixExpression (suffixEnvironment (consumed problem index) index) []
  | 5 => BuilderRegisterCompareResidual.workSteps index (consumed problem index) + 1
  | 6 => fieldSteps problem index remaining hBody .clause (extra problem index 6)
  | _ => BuilderRegisterExpression.workSteps suffixExpression
      (suffixEnvironment (tokenPosition problem index) (clauseIndex problem index)) []

theorem comparison_output_suffix {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    BuilderRegisterCompareResidual.outputValues (comparisonResult problem index) =
      (BuilderRegisterLessThan.resultValues (comparisonResult problem index) ++ [consumed problem index]) ++ [tokenPosition problem index] := by
  simp only [BuilderRegisterCompareResidual.outputValues,
    show BuilderRegisterCompareResidual.resultBoundary (comparisonResult problem index) = consumed problem index from
      BuilderRegisterCompareResidual.resultBoundary_eq _ _, comparison_residual,
    List.append_assoc, List.cons_append, List.nil_append]

private theorem step_workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) (output : List CNFToken) (outer : List WorkSymbol)
    (phase : Nat) (hPhase : phase < 8) :
    workRunExact? (stepMachine problem.verifier phase) (stepSteps problem index remaining hBody phase)
      (workStartConfiguration (stepMachine problem.verifier phase)
        (endTape (sourceValues problem index remaining hBody ++ extra problem index phase) (inside problem.input output) outer)) =
      some {
        state := (stepMachine problem.verifier phase).acceptState
        tape := endTape (sourceValues problem index remaining hBody ++ extra problem index (phase + 1))
          (inside problem.input output) (outer.drop (allocation problem index phase)) } := by
  rcases phase with _ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | phase)))))))
  · simpa only [stepMachine, stepSteps, allocation, fieldValue, extra, List.append_nil] using
      field_workRunExact problem index remaining hBody .width [] output outer
  · simpa only [stepMachine, stepSteps, allocation, fieldValue, extra,
      List.append_assoc, List.cons_append, List.nil_append] using
      field_workRunExact problem index remaining hBody .quotient (extra problem index 1) output outer
  · exact multiply_workRunExact (sourceValues problem index remaining hBody) (width problem) (quotient problem index)
      (inside problem.input output) outer
  · simpa only [stepMachine, stepSteps, allocation, fieldValue, extra,
      List.append_assoc, List.cons_append, List.nil_append] using
      field_workRunExact problem index remaining hBody .index (extra problem index 3) output outer
  · have h := BuilderRegisterExpression.workRunExact suffixExpression 0
      (sourceValues problem index remaining hBody ++ [width problem,quotient problem index])
      (suffixEnvironment (consumed problem index) index) [] (inside problem.input output) outer rfl
    simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
      suffix_environment_values, suffix_expression_values, stepMachine, stepSteps, allocation, extra,
      List.append_nil, List.append_assoc, List.cons_append, List.nil_append, registerWord,
      List.length_append, List.length_replicate, List.length_cons, List.length_nil, Nat.add_zero] using h
  · simpa only [stepMachine, stepSteps, allocation, extra, comparisonResult,
      List.append_assoc, List.cons_append, List.nil_append] using
      compare_workRunExact index (consumed problem index)
        (sourceValues problem index remaining hBody ++ [width problem,quotient problem index,consumed problem index])
        (inside problem.input output) outer
  · simpa only [stepMachine, stepSteps, allocation, fieldValue, extra, List.append_assoc] using
      field_workRunExact problem index remaining hBody .clause (extra problem index 6) output outer
  · have h := BuilderRegisterExpression.workRunExact suffixExpression 0
      (sourceValues problem index remaining hBody ++ [width problem,quotient problem index,consumed problem index] ++
        BuilderRegisterLessThan.resultValues (comparisonResult problem index) ++ [consumed problem index])
      (suffixEnvironment (tokenPosition problem index) (clauseIndex problem index)) [] (inside problem.input output) outer rfl
    simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
      suffix_environment_values, suffix_expression_values, stepMachine, stepSteps, allocation, extra, comparison_output_suffix,
      List.append_nil, List.append_assoc, List.cons_append, List.nil_append, registerWord, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil, Nat.add_zero] using h
  · exfalso
    omega

def doneMachine : WorkMachine := {rules := [], startState := 0, acceptState := 0, rejectState := 1}
def prefixMachine {language : Language} (verifier : PolynomialTimeVerifier language) : Nat → WorkMachine
  | 0 => doneMachine
  | phase + 1 => WorkMachineChain.machine (prefixMachine verifier phase) (stepMachine verifier phase)
def prefixSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : Nat → Nat
  | 0 => 0
  | phase + 1 => prefixSteps problem index remaining hBody phase + 1 + stepSteps problem index remaining hBody phase
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderSourceClauseCoordinate.machine verifier) (prefixMachine verifier 8)
def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : Nat :=
  BuilderSourceClauseCoordinate.workSteps problem index remaining hBody + 1 + prefixSteps problem index remaining hBody 8
def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : List Nat :=
  sourceValues problem index remaining hBody ++ extra problem index 8
def exterior {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : List WorkSymbol :=
  phaseOutside problem index (BuilderSourceClauseCoordinate.exterior problem index remaining hBody) 8
def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (BuilderCursorSource.cursorTape problem index remaining output)
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) : WorkConfiguration :=
  {state := (machine problem.verifier).acceptState,
   tape := endTape (finalValues problem index remaining hBody) (inside problem.input output) (exterior problem index remaining hBody)}

private theorem chain_run (first second : WorkMachine) (firstSteps secondSteps : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

private theorem prefix_workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) (output : List CNFToken) (outer : List WorkSymbol)
    (phase : Nat) (hPhase : phase ≤ 8) :
    workRunExact? (prefixMachine problem.verifier phase) (prefixSteps problem index remaining hBody phase)
      (workStartConfiguration (prefixMachine problem.verifier phase)
        (endTape (sourceValues problem index remaining hBody) (inside problem.input output) outer)) =
      some {
        state := (prefixMachine problem.verifier phase).acceptState
        tape := endTape (sourceValues problem index remaining hBody ++ extra problem index phase)
          (inside problem.input output) (phaseOutside problem index outer phase) } := by
  induction phase with
  | zero =>
      simp only [prefixSteps, prefixMachine, phaseOutside, extra, List.append_nil]
      rfl
  | succ phase ih =>
      have hPrev := ih (by omega)
      have hNext := step_workRunExact problem index remaining hBody output (phaseOutside problem index outer phase) phase (by omega)
      exact chain_run _ _ _ _ _ _ _ hPrev hNext

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining hBody)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output hBody) := by
  have hSource := BuilderSourceClauseCoordinate.workRunExact problem index remaining output hBody
  have hTail := prefix_workRunExact problem index remaining hBody output
    (BuilderSourceClauseCoordinate.exterior problem index remaining hBody) 8 (by decide)
  exact chain_run _ _ _ _ _ _ _ hSource hTail

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hBody)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output hBody) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output hBody)

theorem final_tape {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    (finalConfiguration problem index remaining output hBody).tape =
      endTape (finalValues problem index remaining hBody) (inside problem.input output) (exterior problem index remaining hBody) := rfl

def gap {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  [clauseIndex problem index,width problem,quotient problem index,consumed problem index] ++
    BuilderRegisterCompareResidual.outputValues (comparisonResult problem index)
def request {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  [clauseIndex problem index,tokenPosition problem index]

theorem gap_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (gap problem index).length = 9 := by
  simp only [gap, List.length_append, BuilderRegisterCompareResidual.outputValues_length, List.length_cons, List.length_nil]
theorem request_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (request problem index).length = 2 := rfl
theorem request_value {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    request problem index =
      [(index / width problem) % clauseWidth problem,index % width problem] := rfl
theorem final_request_layout {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) :
    finalValues problem index remaining hBody =
      BuilderSourcePayload.history problem index remaining hBody ++
        BuilderLocalConstraintPayload.values (problem.formulaConstraintSlotDirect (constraintIndex problem index)) ++
        gap problem index ++ request problem index := by
  rw [finalValues, sourceValues, BuilderSourceClauseCoordinate.finalValues,
    BuilderSourcePayload.final_suffix, BuilderSourcePayload.payload_canonical]
  simp only [extra, gap, request, List.append_assoc, List.cons_append, List.nil_append]

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧ WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem field_good {language : Language} (verifier : PolynomialTimeVerifier language) (field : Field) :
    Good (fieldMachine verifier field) :=
  ⟨BuilderRegisterRootCopy.rules_pairwise_query_distinct _, BuilderRegisterRootCopy.noRuleAtAccept _,
   BuilderRegisterRootCopy.noRuleAtReject _, BuilderRegisterRootCopy.acceptState_ne_rejectState _⟩
private theorem multiply_good : Good (RegisterBinary.machine .mul 0) := by
  refine ⟨RegisterBinary.rules_pairwise_query_distinct _ _, ?_, ?_, RegisterBinary.machine_acceptState_ne_rejectState _ _⟩
  · intro rule hRule
    exact Nat.ne_of_lt (RegisterBinary.rule_source_lt_acceptState _ _ rule hRule)
  · intro rule hRule
    have h := RegisterBinary.rule_source_lt_acceptState RegisterBinary.Operator.mul 0 rule hRule
    rw [RegisterBinary.machine_acceptState] at h
    change rule.sourceState ≠ (RegisterBinary.machine .mul 0).rejectState
    rw [RegisterBinary.machine_rejectState]
    omega
private theorem compare_good : Good compareMachine :=
  ⟨WorkMachineProgramGraph.rules_pairwise compareGraph compare_wellFormed,
   WorkMachineProgramGraph.noRuleAt_globalAccept _, WorkMachineProgramGraph.noRuleAt_globalReject _, by decide⟩
private theorem suffix_good : Good (BuilderRegisterExpression.machine suffixExpression 0) :=
  ⟨BuilderRegisterExpression.rules_pairwise_query_distinct _ _, BuilderRegisterExpression.noRuleAtAccept _ _,
   BuilderRegisterExpression.noRuleAtReject _ _, BuilderRegisterExpression.acceptState_ne_rejectState _ _⟩
private theorem step_good {language : Language} (verifier : PolynomialTimeVerifier language) (phase : Nat) :
    Good (stepMachine verifier phase) := by
  rcases phase with _ | (_ | (_ | (_ | (_ | (_ | (_ | phase))))))
  · exact field_good verifier .width
  · exact field_good verifier .quotient
  · exact multiply_good
  · exact field_good verifier .index
  · exact suffix_good
  · exact compare_good
  · exact field_good verifier .clause
  · exact suffix_good

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
   WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
   WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩
private theorem prefix_good {language : Language} (verifier : PolynomialTimeVerifier language) (phase : Nat) :
    Good (prefixMachine verifier phase) := by
  induction phase with
  | zero =>
      refine ⟨List.Pairwise.nil, ?_, ?_, ?_⟩
      · intro rule h
        cases h
      · intro rule h
        cases h
      · change (0 : Nat) ≠ 1
        decide
  | succ phase ih => exact chain_good _ _ ih (step_good verifier phase)
private theorem good {language : Language} (verifier : PolynomialTimeVerifier language) : Good (machine verifier) :=
  chain_good _ _
    ⟨BuilderSourceClauseCoordinate.rules_pairwise_query_distinct verifier, BuilderSourceClauseCoordinate.noRuleAtAccept verifier,
     BuilderSourceClauseCoordinate.noRuleAtReject verifier, BuilderSourceClauseCoordinate.acceptState_ne_rejectState verifier⟩
    (prefix_good verifier 8)

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := (good verifier).1
theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := (good verifier).2.1
theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState := (good verifier).2.2.1
theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := (good verifier).2.2.2


def multiplySpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add bound (.mul bound bound)) (.constant 1)
def multiplyWorkPolynomial (bound : NatPolynomial) : NatPolynomial :=
  let twice := NatPolynomial.mul (.constant 2) bound
  let square := NatPolynomial.mul bound bound
  .add (.constant 2)
    (.add (.add (.add (.add
      (.mul bound (.add (.add (.add twice square) (.mul (.constant 7) bound)) (.constant 7)))
      (.mul (.mul (.add (.add square twice) (.constant 1)) bound) bound))
      twice) (.mul twice bound)) (.add twice (.constant 3)))
def multiplyRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6) (multiplyWorkPolynomial bound)
private theorem multiply_work_polynomial_eval (bound : NatPolynomial) (input : Nat) :
    (multiplyWorkPolynomial bound).eval input = RegisterBinary.workBound .mul (bound.eval input) := by
  simp only [multiplyWorkPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, RegisterBinary.workBound, Nat.add_assoc]

private theorem multiply_polynomial_bounds (older : List Nat) (left right : Nat) (outer : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ [left,right])).length + outer.length ≤ bound.eval input) :
    (registerWord (older ++ [left,right,left * right])).length + (outer.drop (left * right + 1)).length ≤
        (multiplySpanPolynomial bound).eval input ∧
      6 * RegisterBinary.steps .mul [] left right ≤ (multiplyRawTimePolynomial bound).eval input := by
  have hArgs : (registerWord ([left,right] : List Nat)).length ≤ bound.eval input ∧
      left ≤ bound.eval input ∧ right ≤ bound.eval input := by
    simp only [registerWord_append, registerWord_length, List.length_append, List.length_cons,
      List.length_nil, List.sum_cons, List.sum_nil] at hSpan ⊢
    constructor
    · omega
    · constructor <;> omega
  have hProduct := Nat.mul_le_mul hArgs.2.1 hArgs.2.2
  have hTime := RegisterBinary.steps_le RegisterBinary.Operator.mul [] left right (bound.eval input) hArgs.1
  have hWord : (registerWord (older ++ [left,right,left * right])).length =
      (registerWord (older ++ [left,right])).length + left * right + 1 := by
    simpa only [RegisterBinary.value, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] using
      RegisterBinary.register_span_added RegisterBinary.Operator.mul older [] left right
  constructor
  · simp only [hWord, List.length_drop, multiplySpanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
      NatPolynomial.eval_constant]
    omega
  · simp only [multiplyRawTimePolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_constant, multiply_work_polynomial_eval]
    exact Nat.mul_le_mul_left 6 hTime

def compareSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterCompareResidual.spanPolynomial bound) bound
def compareRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterCompareResidual.rawTimePolynomial bound) (.constant 6)
private theorem compare_polynomial_bounds (coordinate boundary : Nat) (older : List Nat) (outer : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ [coordinate,boundary])).length + outer.length ≤ bound.eval input) :
    (registerWord (older ++ BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 coordinate boundary))).length +
        (outer.drop (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 coordinate boundary))).length ≤
          (compareSpanPolynomial bound).eval input ∧
      6 * (BuilderRegisterCompareResidual.workSteps coordinate boundary + 1) ≤ (compareRawTimePolynomial bound).eval input := by
  have h := BuilderRegisterCompareResidual.source_polynomial_bounds coordinate boundary older bound input (by omega)
  constructor
  · simp only [compareSpanPolynomial, NatPolynomial.eval_add, List.length_drop]
    omega
  · simp only [compareRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

def suffixSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterExpression.spanPolynomial suffixExpression bound) bound
private theorem suffix_polynomial_bounds (older : List Nat) (position clause : Nat) (outer : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ [position,clause])).length + outer.length ≤ bound.eval input) :
    (registerWord (older ++ [position,clause,position])).length + (outer.drop (position + 1)).length ≤
        (suffixSpanPolynomial bound).eval input ∧
      6 * BuilderRegisterExpression.workSteps suffixExpression (suffixEnvironment position clause) [] ≤
        (BuilderRegisterExpression.rawTimePolynomial suffixExpression bound).eval input := by
  have h := BuilderRegisterExpression.source_polynomial_bounds suffixExpression bound input older
    (suffixEnvironment position clause) [] (by
      simpa only [suffix_environment_values, List.append_nil] using (show (registerWord (older ++ [position,clause])).length ≤ bound.eval input by omega))
  rw [suffix_expression_values] at h
  constructor
  · have hWord : (registerWord (older ++ [position,clause,position])).length ≤
        (BuilderRegisterExpression.spanPolynomial suffixExpression bound).eval input := by
      simpa only [suffix_environment_values, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] using h.1
    simp only [suffixSpanPolynomial, NatPolynomial.eval_add, List.length_drop]
    omega
  · exact h.2

def stepSpanPolynomial : Nat → NatPolynomial → NatPolynomial
  | 0, bound => BuilderRegisterRootCopy.spanPolynomial bound
  | 1, bound => BuilderRegisterRootCopy.spanPolynomial bound
  | 2, bound => multiplySpanPolynomial bound
  | 3, bound => BuilderRegisterRootCopy.spanPolynomial bound
  | 4, bound => suffixSpanPolynomial bound
  | 5, bound => compareSpanPolynomial bound
  | 6, bound => BuilderRegisterRootCopy.spanPolynomial bound
  | _, bound => suffixSpanPolynomial bound
def stepRawTimePolynomial : Nat → NatPolynomial → NatPolynomial
  | 0, bound => BuilderRegisterRootCopy.rawTimePolynomial bound
  | 1, bound => BuilderRegisterRootCopy.rawTimePolynomial bound
  | 2, bound => multiplyRawTimePolynomial bound
  | 3, bound => BuilderRegisterRootCopy.rawTimePolynomial bound
  | 4, bound => BuilderRegisterExpression.rawTimePolynomial suffixExpression bound
  | 5, bound => compareRawTimePolynomial bound
  | 6, bound => BuilderRegisterRootCopy.rawTimePolynomial bound
  | _, bound => BuilderRegisterExpression.rawTimePolynomial suffixExpression bound

private theorem step_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) (outer : List WorkSymbol) (phase : Nat) (hPhase : phase < 8)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (sourceValues problem index remaining hBody ++ extra problem index phase)).length + outer.length ≤ bound.eval input) :
    (registerWord (sourceValues problem index remaining hBody ++ extra problem index (phase + 1))).length +
        (outer.drop (allocation problem index phase)).length ≤ (stepSpanPolynomial phase bound).eval input ∧
      6 * stepSteps problem index remaining hBody phase ≤ (stepRawTimePolynomial phase bound).eval input := by
  rcases phase with _ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | phase)))))))
  · simpa only [extra, stepSpanPolynomial, stepRawTimePolynomial, stepSteps, allocation, fieldValue, List.append_nil] using
      field_polynomial_bounds problem index remaining hBody .width [] outer bound input hSpan
  · simpa only [extra, stepSpanPolynomial, stepRawTimePolynomial, stepSteps, allocation, fieldValue,
      List.append_assoc, List.cons_append, List.nil_append] using
      field_polynomial_bounds problem index remaining hBody .quotient (extra problem index 1) outer bound input hSpan
  · exact multiply_polynomial_bounds (sourceValues problem index remaining hBody) (width problem) (quotient problem index) outer bound input hSpan
  · simpa only [extra, stepSpanPolynomial, stepRawTimePolynomial, stepSteps, allocation, fieldValue,
      List.append_assoc, List.cons_append, List.nil_append] using
      field_polynomial_bounds problem index remaining hBody .index (extra problem index 3) outer bound input hSpan
  · have h := suffix_polynomial_bounds
      (sourceValues problem index remaining hBody ++ [width problem,quotient problem index])
      (consumed problem index) index outer bound input (by
        simpa only [extra, List.append_assoc, List.cons_append, List.nil_append] using hSpan)
    simpa only [extra, stepSpanPolynomial, stepRawTimePolynomial, stepSteps, allocation,
      List.append_assoc, List.cons_append, List.nil_append] using h
  · have h := compare_polynomial_bounds index (consumed problem index)
      (sourceValues problem index remaining hBody ++ [width problem,quotient problem index,consumed problem index])
      outer bound input (by
        simpa only [extra, List.append_assoc, List.cons_append, List.nil_append] using hSpan)
    simpa only [extra, stepSpanPolynomial, stepRawTimePolynomial, stepSteps, allocation, comparisonResult,
      List.append_assoc, List.cons_append, List.nil_append] using h
  · simpa only [extra, stepSpanPolynomial, stepRawTimePolynomial, stepSteps, allocation, fieldValue, List.append_assoc] using
      field_polynomial_bounds problem index remaining hBody .clause (extra problem index 6) outer bound input hSpan
  · have h := suffix_polynomial_bounds
      (sourceValues problem index remaining hBody ++ [width problem,quotient problem index,consumed problem index] ++
        BuilderRegisterLessThan.resultValues (comparisonResult problem index) ++ [consumed problem index])
      (tokenPosition problem index) (clauseIndex problem index) outer bound input (by
        simpa only [extra, comparison_output_suffix, List.append_assoc, List.cons_append, List.nil_append] using hSpan)
    simpa only [extra, comparison_output_suffix, stepSpanPolynomial, stepRawTimePolynomial, stepSteps, allocation,
      List.append_assoc, List.cons_append, List.nil_append] using h
  · exfalso
    omega

def prefixSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : Nat → NatPolynomial
  | 0 => BuilderSourceClauseCoordinate.spanBound verifier
  | phase + 1 => stepSpanPolynomial phase (prefixSpanBound verifier phase)
def prefixRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : Nat → NatPolynomial
  | 0 => .constant 0
  | phase + 1 => .add (.add (prefixRawTimeBound verifier phase) (.constant 6))
      (stepRawTimePolynomial phase (prefixSpanBound verifier phase))
def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial := prefixSpanBound verifier 8
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderSourceClauseCoordinate.rawTimeBound verifier) (.constant 6)) (prefixRawTimeBound verifier 8)

private theorem prefix_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (phase : Nat) (hPhase : phase ≤ 8) :
    (registerWord (sourceValues problem index remaining hBody ++ extra problem index phase)).length +
        (phaseOutside problem index (BuilderSourceClauseCoordinate.exterior problem index remaining hBody) phase).length ≤
          (prefixSpanBound problem.verifier phase).eval problem.input.length ∧
      6 * prefixSteps problem index remaining hBody phase ≤ (prefixRawTimeBound problem.verifier phase).eval problem.input.length := by
  have hSource := BuilderSourceClauseCoordinate.source_polynomial_bounds problem index remaining hBody hBalance
  induction phase with
  | zero =>
      constructor
      · simpa only [prefixSpanBound, sourceValues, extra, phaseOutside, List.append_nil] using hSource.1
      · exact Nat.le_refl 0
  | succ phase ih =>
      have hPrev := ih (by omega)
      have hNext := step_polynomial_bounds problem index remaining hBody
        (phaseOutside problem index (BuilderSourceClauseCoordinate.exterior problem index remaining hBody) phase)
        phase (by omega) (prefixSpanBound problem.verifier phase) problem.input.length hPrev.1
      constructor
      · exact hNext.1
      · have hPrevTime := hPrev.2
        have hNextTime := hNext.2
        simp only [prefixSteps, prefixRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
        omega

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining hBody)).length + (exterior problem index remaining hBody).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hBody ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hSource := BuilderSourceClauseCoordinate.source_polynomial_bounds problem index remaining hBody hBalance
  have hTail := prefix_polynomial_bounds problem index remaining hBody hBalance 8 (by decide)
  constructor
  · exact hTail.1
  · have hSourceTime := hSource.2
    have hTailTime := hTail.2
    simp only [workSteps, rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem uniform_source_request {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ rawSteps, rawSteps ≤ (rawTimeBound problem.verifier).eval problem.input.length ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
        encodeWorkConfiguration (finalConfiguration problem index remaining output hBody) ∧
      (finalConfiguration problem index remaining output hBody).tape =
        endTape (BuilderSourcePayload.history problem index remaining hBody ++
          BuilderLocalConstraintPayload.values (problem.formulaConstraintSlotDirect (constraintIndex problem index)) ++
          gap problem index ++ [(index / width problem) % clauseWidth problem,index % width problem])
          (inside problem.input output) (exterior problem index remaining hBody) ∧
      (registerWord (finalValues problem index remaining hBody)).length + (exterior problem index remaining hBody).length ≤
        (spanBound problem.verifier).eval problem.input.length := by
  have hBounds := source_polynomial_bounds problem index remaining hBody hBalance
  refine ⟨6 * workSteps problem index remaining hBody, hBounds.2,
    run_compile_exact problem index remaining output hBody, ?_, hBounds.1⟩
  rw [final_tape, final_request_layout, request_value]

end PNP.Concrete.CookLevin.BuilderSourceTokenRequest

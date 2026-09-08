/-
Copyright (c) 2026 PNP Labs.

Actual source/radix packet to the complete input-only initial-cell payload.
The fixed composition derives all runtime fields, executes comparisons and the
actual input read, and identifies the unchanged canonical initial/formula slot.
Prefix routing, complete family dispatch and emission remain downstream.
-/

import PNP.Concrete.CookLevinBuilderInitialInputOnlyPayload
import PNP.Concrete.CookLevinBuilderLiteralArgumentSource

namespace PNP.Concrete.CookLevin.BuilderInitialInputOnlySource

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)
open BuilderLiteralArgumentSource (inputValues inputCount environment environment_values field field_eval)
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)

def coordinate {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  BuilderConstraintRegionSource.localCoordinate problem index .initial
def data {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : BuilderInitialInputOnlyPayload.Data :=
  ⟨problem.input.length, problem.uniformFuel, problem.dimensions.tapeWidth problem.tableauInputMode, coordinate problem index⟩
def sourceFrame {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  inputValues problem index remaining .initial []
def fields {language : Language} (verifier : PolynomialTimeVerifier language) :
    List (BuilderRegisterPack.Field (inputCount verifier .initial 0)) :=
  [field verifier .initial 0 (.source .inputLength),
   field verifier .initial 0 (.source .fuel),
   field verifier .initial 0 (.source .tapeWidth),
   field verifier .initial 0 .quotient]

theorem fields_values {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderRegisterPack.values (fields problem.verifier) (environment problem index remaining .initial 0 []) =
      BuilderInitialInputOnlyPayload.dataValues (data problem index) := by
  simp only [fields, BuilderRegisterPack.values, List.map_cons, List.map_nil, field_eval]
  rfl

def payloadNode : Node :=
  {name := 1, program := BuilderInitialInputOnlyPayload.machine, onAccept := .accept, onReject := .reject}
def sourceNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 0, program := BuilderRegisterPack.machine (fields verifier) 0,
   onAccept := .node payloadNode.reference, onReject := .dead}
def graph {language : Language} (verifier : PolynomialTimeVerifier language) : Graph :=
  {nodes := [sourceNode verifier, payloadNode], entry := (sourceNode verifier).reference}
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph verifier)
theorem graph_nodes_length {language : Language} (verifier : PolynomialTimeVerifier language) : (graph verifier).nodes.length = 2 := rfl
private theorem source_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    sourceNode verifier ∈ (graph verifier).nodes := List.Mem.head _
private theorem payload_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    payloadNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.head _)

theorem graph_wellFormed {language : Language} (verifier : PolynomialTimeVerifier language) : (graph verifier).WellFormed := by
  have hNames : ((graph verifier).nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0,1] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact ⟨BuilderRegisterPack.rules_pairwise_query_distinct (fields verifier) 0,
        BuilderRegisterPack.noRuleAtAccept (fields verifier) 0, BuilderRegisterPack.noRuleAtReject (fields verifier) 0,
        BuilderRegisterPack.acceptState_ne_rejectState (fields verifier) 0⟩
    · exact ⟨BuilderInitialInputOnlyPayload.rules_pairwise_query_distinct, BuilderInitialInputOnlyPayload.noRuleAtAccept,
        BuilderInitialInputOnlyPayload.noRuleAtReject, BuilderInitialInputOnlyPayload.acceptState_ne_rejectState⟩
  · exact ⟨sourceNode verifier, source_mem verifier, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact ⟨⟨payloadNode, payload_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def prepareSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderRegisterPack.workSteps (fields problem.verifier) (environment problem index remaining .initial 0 []) []
def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  prepareSteps problem index remaining + 1 +
    (BuilderInitialInputOnlyPayload.workSteps (data problem index) (sourceFrame problem index remaining) problem.input + 1)
def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  sourceFrame problem index remaining ++ BuilderInitialInputOnlyPayload.outputValues (data problem index) problem.input
def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : WorkConfiguration :=
  WorkMachineProgramGraph.endpointConfiguration (BuilderInitialInputOnlyPayload.endpoint (data problem index))
    (endTape (finalValues problem index remaining) (inside problem.input output) [])

private theorem prepare_run {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    workRunExact? (BuilderRegisterPack.machine (fields problem.verifier) 0) (prepareSteps problem index remaining)
      (workStartConfiguration (BuilderRegisterPack.machine (fields problem.verifier) 0)
        (endTape (sourceFrame problem index remaining) (inside problem.input output) [])) =
      some
        {state := (BuilderRegisterPack.machine (fields problem.verifier) 0).acceptState,
         tape := endTape (sourceFrame problem index remaining ++ BuilderInitialInputOnlyPayload.dataValues (data problem index))
           (inside problem.input output) []} := by
  have h := BuilderRegisterPack.workRunExact (fields problem.verifier) 0 []
    (environment problem index remaining .initial 0 []) [] (inside problem.input output) [] rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    environment_values problem index remaining .initial 0 [] rfl, fields_values,
    List.nil_append, List.append_nil, List.drop_nil, sourceFrame, prepareSteps] using h

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) = some (finalConfiguration problem index remaining output) := by
  have hPayload := BuilderInitialInputOnlyPayload.workRunExact (data problem index) (sourceFrame problem index remaining) problem.input output
  simp only [BuilderInitialInputOnlyPayload.initialConfiguration, BuilderInitialInputOnlyPayload.finalConfiguration] at hPayload
  have hPath : AcceptPath (graph problem.verifier) (.node payloadNode.reference)
      (BuilderInitialInputOnlyPayload.endpoint (data problem index))
      (BuilderInitialInputOnlyPayload.workSteps (data problem index) (sourceFrame problem index remaining) problem.input + 1)
      (endTape (sourceFrame problem index remaining ++ BuilderInitialInputOnlyPayload.dataValues (data problem index))
        (inside problem.input output) [])
      (endTape (finalValues problem index remaining) (inside problem.input output) []) := by
    by_cases hPrefix : coordinate problem index < 2
    · have hData : (data problem index).coordinate < 2 := hPrefix
      simp only [BuilderInitialInputOnlyPayload.endpoint, if_pos hData] at hPayload ⊢
      have h := AcceptPath.stepReject payloadNode .reject _ 0 _ _ _ (payload_mem problem.verifier) hPayload (.terminal .reject _)
      simpa only [finalValues, Nat.add_zero] using h
    · have hData : ¬ (data problem index).coordinate < 2 := hPrefix
      simp only [BuilderInitialInputOnlyPayload.endpoint, if_neg hData] at hPayload ⊢
      have h := AcceptPath.step payloadNode .accept _ 0 _ _ _ (payload_mem problem.verifier) hPayload (.terminal .accept _)
      simpa only [finalValues, Nat.add_zero] using h
  have hPrepare := prepare_run problem index remaining output
  have hP := AcceptPath.step (sourceNode problem.verifier) _ _ _ _ _ _ (source_mem problem.verifier) hPrepare hPath
  have h := WorkMachineProgramPath.runExact (graph problem.verifier) _ _ _ _ _ (graph_wellFormed problem.verifier) hP
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node (sourceNode problem.verifier).reference) tape =
        workStartConfiguration (machine problem.verifier) tape := rfl
  have hMachine : WorkMachineProgramGraph.machine (graph problem.verifier) = machine problem.verifier := rfl
  rw [hStart, hMachine] at h
  simpa only [workSteps, initialConfiguration, finalConfiguration] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output)

def payloadValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  if BuilderInitialInputOnlyPayload.position (data problem index) < problem.dimensions.tapeWidth problem.tableauInputMode
  then BuilderInitialInputOnlyPayload.payloadValues (data problem index) problem.input else [1]
def history {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  sourceFrame problem index remaining ++
    if BuilderInitialInputOnlyPayload.position (data problem index) < problem.dimensions.tapeWidth problem.tableauInputMode
    then BuilderInitialInputOnlyPayload.centerStage (data problem index) ++
      BuilderInitialInputOnlyPayload.resolvedValues (data problem index) problem.input ++
      BuilderInitialInputOnlyPayload.indexValues (data problem index) problem.input
    else BuilderInitialInputOnlyPayload.widthStage (data problem index)

theorem final_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hPrefix : ¬ coordinate problem index < 2) :
    finalValues problem index remaining = history problem index remaining ++ payloadValues problem index := by
  have hData : ¬ (data problem index).coordinate < 2 := hPrefix
  simp only [finalValues, BuilderInitialInputOnlyPayload.outputValues, if_neg hData, history, payloadValues]
  change sourceFrame problem index remaining ++
      (if BuilderInitialInputOnlyPayload.position (data problem index) < problem.dimensions.tapeWidth problem.tableauInputMode
      then BuilderInitialInputOnlyPayload.cellValues (data problem index) problem.input
      else BuilderInitialInputOnlyPayload.widthStage (data problem index) ++ [1]) = _
  split <;> simp only [*, BuilderInitialInputOnlyPayload.cellValues, List.append_assoc]

theorem index_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hPosition : BuilderInitialInputOnlyPayload.position (data problem index) <
      problem.dimensions.tapeWidth problem.tableauInputMode) :
    BuilderInitialInputOnlyPayload.indexValue (data problem index) problem.input =
      (problem.symbolLiteral problem.initialTime ⟨BuilderInitialInputOnlyPayload.position (data problem index), hPosition⟩
        (BuilderInitialConstraintPayload.inputOnlySymbol problem.input problem.uniformFuel
          (BuilderInitialInputOnlyPayload.position (data problem index)))).index.val := by
  rw [BuilderInitialInputOnlyPayload.indexValue, BuilderInitialInputOnlyPayload.code_canonical]
  have h := BuilderLiteralIndexExpression.eval_eq_index
    (.symbol problem.initialTime ⟨BuilderInitialInputOnlyPayload.position (data problem index), hPosition⟩
      (BuilderInitialConstraintPayload.inputOnlySymbol problem.input problem.uniformFuel
        (BuilderInitialInputOnlyPayload.position (data problem index))) :
      BuilderLiteralIndexExpression.Request problem.layout)
  change ((0 * problem.dimensions.tapeWidth problem.tableauInputMode +
    BuilderInitialInputOnlyPayload.position (data problem index)) * 3 +
    VariableLayout.tapeSymbolCode (BuilderInitialConstraintPayload.inputOnlySymbol problem.input problem.uniformFuel
      (BuilderInitialInputOnlyPayload.position (data problem index)))) = _ at h
  have hLiteral :
      ((.symbol problem.initialTime ⟨BuilderInitialInputOnlyPayload.position (data problem index), hPosition⟩
        (BuilderInitialConstraintPayload.inputOnlySymbol problem.input problem.uniformFuel
          (BuilderInitialInputOnlyPayload.position (data problem index))) :
        BuilderLiteralIndexExpression.Request problem.layout)).index =
      (problem.symbolLiteral problem.initialTime ⟨BuilderInitialInputOnlyPayload.position (data problem index), hPosition⟩
        (BuilderInitialConstraintPayload.inputOnlySymbol problem.input problem.uniformFuel
          (BuilderInitialInputOnlyPayload.position (data problem index)))).index.val := rfl
  have hFuel : (data problem index).fuel = problem.uniformFuel := rfl
  rw [hLiteral] at h
  simpa only [Nat.zero_mul, Nat.zero_add, hFuel] using h

theorem source_capacity {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    coordinate problem index - 2 < BuilderInitialConstraintPayload.symbolCapacity problem := by
  have hBound := BuilderConstraintRegionSource.localCoordinate_valid problem index .initial hRegion
  have hLengths := BuilderConstraintRegionRegisters.orderedLengths_match_schedule problem
  have hInitial := congrArg (fun values : List Nat => values.getD 1 0) hLengths
  change BuilderConstraintRegionRegisters.regionLength problem .initial =
    3 + 2 * ((problem.certificateLimit + 1) * problem.dimensions.tapeWidth problem.tableauInputMode) at hInitial
  rw [hInitial] at hBound
  change coordinate problem index < 3 + 2 * ((problem.certificateLimit + 1) * problem.dimensions.tapeWidth problem.tableauInputMode) at hBound
  unfold BuilderInitialConstraintPayload.symbolCapacity
  omega

theorem payload_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode ≠ .paired)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial)
    (hPrefix : ¬ coordinate problem index < 2) :
    payloadValues problem index = BuilderInitialConstraintPayload.values problem (coordinate problem index) := by
  have hCapacity := source_capacity problem index hRegion
  have hCoordinate : coordinate problem index = (coordinate problem index - 2) + 2 := by omega
  rw [hCoordinate, BuilderInitialConstraintPayload.values, if_pos hCapacity, dif_neg hMode]
  unfold payloadValues BuilderInitialConstraintPayload.inputOnlySymbolsValues
  by_cases hPosition : BuilderInitialInputOnlyPayload.position (data problem index) <
      problem.dimensions.tapeWidth problem.tableauInputMode
  · have hPosition' : coordinate problem index - 2 < problem.dimensions.tapeWidth problem.tableauInputMode := hPosition
    simp only [if_pos hPosition, dif_pos hPosition', Option.getD_some,
      BuilderInitialInputOnlyPayload.payloadValues, index_canonical problem index hPosition,
      BuilderInitialConstraintPayload.requiredValues]
    rfl
  · have hPosition' : ¬ coordinate problem index - 2 < problem.dimensions.tapeWidth problem.tableauInputMode := hPosition
    simp only [if_neg hPosition, dif_neg hPosition', Option.getD_none]

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode ≠ .paired)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial)
    (hPrefix : ¬ coordinate problem index < 2) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index) =
      some (problem.initialConstraintSlotDirect (coordinate problem index)) := by
  rw [payload_canonical problem index hMode hRegion hPrefix, BuilderInitialConstraintPayload.decode_values]

theorem whole_formula_payload {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode ≠ .paired)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial)
    (hPrefix : ¬ coordinate problem index < 2) :
    payloadValues problem index = BuilderLocalConstraintPayload.values
      (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) := by
  rw [payload_canonical problem index hMode hRegion hPrefix, BuilderInitialConstraintPayload.values_canonical,
    ← BuilderConstraintRegionSource.regionSlot_eq problem index .initial hRegion]
  rfl

theorem source_canonical_payload {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hMode : problem.tableauInputMode ≠ .paired)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial)
    (hPrefix : ¬ coordinate problem index < 2) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) =
      some
        {state := (machine problem.verifier).acceptState,
         tape := endTape (history problem index remaining ++ BuilderLocalConstraintPayload.values
           (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)))
           (inside problem.input output) []} := by
  have hData : ¬ (data problem index).coordinate < 2 := hPrefix
  have h := workRunExact problem index remaining output
  rw [finalConfiguration, BuilderInitialInputOnlyPayload.endpoint, if_neg hData,
    final_suffix problem index remaining hPrefix, whole_formula_payload problem index hMode hRegion hPrefix] at h
  exact h

theorem final_tape {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      endTape (finalValues problem index remaining) (inside problem.input output) [] := rfl
theorem final_frontier {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : (finalConfiguration problem index remaining output).tape.left = [] := rfl

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise (graph verifier) (graph_wellFormed verifier)
theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept (graph verifier)
theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject (graph verifier)
theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := by
  change (0 : Nat) ≠ 1
  decide

def sourceBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderLiteralArgumentSource.inputBound verifier .initial (.constant 0)
def preparedSpan {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (fields verifier) (sourceBound verifier)
def spanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderInitialInputOnlyPayload.spanPolynomial (preparedSpan verifier)
def rawTimePolynomial {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderRegisterPack.rawTimePolynomial (fields verifier) (sourceBound verifier))
    (.add (.constant 12) (BuilderInitialInputOnlyPayload.rawTimePolynomial (preparedSpan verifier)))

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    (registerWord (finalValues problem index remaining)).length ≤ (spanPolynomial problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining ≤ (rawTimePolynomial problem.verifier).eval problem.input.length := by
  have hSource := BuilderLiteralArgumentSource.input_span_le problem index remaining .initial [] (.constant 0)
    hBody hBalance hRegion (Nat.le_refl 0)
  have hPack := BuilderRegisterPack.source_polynomial_bounds (fields problem.verifier) (sourceBound problem.verifier)
    problem.input.length [] (environment problem index remaining .initial 0 []) [] (by
      simpa only [sourceBound, List.nil_append, List.append_nil, environment_values problem index remaining .initial 0 [] rfl] using hSource)
  simp only [List.nil_append, List.append_nil, environment_values problem index remaining .initial 0 [] rfl,
    fields_values] at hPack
  have hPayload := BuilderInitialInputOnlyPayload.packet_polynomial_bounds (data problem index)
    (sourceFrame problem index remaining) problem.input (preparedSpan problem.verifier) problem.input.length hPack.1
  constructor
  · exact hPayload.1
  · have hPackTime := hPack.2
    have hPayloadTime := hPayload.2
    simp only [workSteps, prepareSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderInitialInputOnlySource

/-
Copyright (c) 2026 PNP Labs.

The complete preservation-family payload kernel from the written source/radix
frame. One fixed graph copies the two position fields, decides equality on tape,
erases the comparison scratch, and executes either literal padding or the
canonical implication constructor. No constraint, equality verdict, literal
index, or correctness certificate is supplied to the machine.

The other families, clause emission, full loop and packaged reduction remain
separate obligations of the complete Cook-Levin builder.
-/

import PNP.Concrete.CookLevinBuilderPreservationImplicationPayload
import PNP.Concrete.CookLevinBuilderRegisterEquality

namespace PNP.Concrete.CookLevin.BuilderPreservationPayload

open BuilderUnaryPolynomial (registerWord registerWord_append registerWord_length)
open BuilderDividerOperands (endTape)
open BuilderLiteralArgumentSource
  (Reference field field_eval inputValues inputCount environment environment_values)
open BuilderPreservationCoordinates (ofSource)
open WorkMachineProgramGraph (Node Graph Endpoint)
open WorkMachineProgramPath (LocalAcceptRun LocalRejectRun AcceptPath)

def headReference : Reference .preservation 0 := .digit ⟨2, by decide⟩
def otherReference : Reference .preservation 0 := .digit ⟨1, by decide⟩

def headValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  BuilderLiteralArgumentSource.referenceValue problem index .preservation [] headReference

def otherValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  BuilderLiteralArgumentSource.referenceValue problem index .preservation [] otherReference

def frame {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  inputValues problem index remaining .preservation []

def pairFields {language : Language} (verifier : PolynomialTimeVerifier language) :
    List (BuilderRegisterPack.Field (inputCount verifier .preservation 0)) :=
  [field verifier .preservation 0 headReference, field verifier .preservation 0 otherReference]

theorem pairFields_length {language : Language} (verifier : PolynomialTimeVerifier language) :
    (pairFields verifier).length = 2 := rfl

theorem pair_values {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderRegisterPack.values (pairFields problem.verifier)
      (environment problem index remaining .preservation 0 []) =
        [headValue problem index, otherValue problem index] := by
  simp only [pairFields, BuilderRegisterPack.values, List.map_cons, List.map_nil, field_eval, headValue, otherValue]

theorem source_positions {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    headValue problem index = (ofSource problem index hRegion).head.val ∧
      otherValue problem index = (ofSource problem index hRegion).other.val := by
  have hDigits := (BuilderPreservationCoordinates.source_radix_coordinates problem index hRegion).1
  simp only [headValue, otherValue, headReference, otherReference,
    BuilderLiteralArgumentSource.referenceValue, hDigits, List.getD_cons_succ, List.getD_cons_zero, and_self]

def pairMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderRegisterPack.machine (pairFields verifier) 0

def pairSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderRegisterPack.workSteps (pairFields problem.verifier)
    (environment problem index remaining .preservation 0 []) []

def comparisonBlanks {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List WorkSymbol :=
  List.replicate (BuilderRegisterEquality.clearedSpan (headValue problem index) (otherValue problem index)) .blank

def retainedValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  if headValue problem index = otherValue problem index then []
  else BuilderPreservationImplicationPayload.allValues problem index

def payloadValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  if headValue problem index = otherValue problem index then [1]
  else BuilderPreservationImplicationPayload.payloadValues problem index remaining

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  frame problem index remaining ++ retainedValues problem index ++ payloadValues problem index remaining

def finalTape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) : WorkTape :=
  endTape (finalValues problem index remaining) inside
    ((comparisonBlanks problem index).drop
      (registerWord (retainedValues problem index ++ payloadValues problem index remaining)).length)

def branchSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  if headValue problem index = otherValue problem index then 5
  else BuilderPreservationImplicationPayload.workSteps problem index remaining

def implicationNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  { name := 3
    program := BuilderPreservationImplicationPayload.machine verifier
    onAccept := .accept
    onReject := .dead }

def paddingNode : Node :=
  { name := 2
    program := BuilderConstraintRegionAssembly.oneMachine
    onAccept := .accept
    onReject := .dead }

def comparisonNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  { name := 1
    program := BuilderRegisterEquality.machine
    onAccept := .node paddingNode.reference
    onReject := .node (implicationNode verifier).reference }

def pairNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  { name := 0
    program := pairMachine verifier
    onAccept := .node (comparisonNode verifier).reference
    onReject := .dead }

def graph {language : Language} (verifier : PolynomialTimeVerifier language) : Graph :=
  { nodes := [pairNode verifier, comparisonNode verifier, paddingNode, implicationNode verifier]
    entry := (pairNode verifier).reference }

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph verifier)

private theorem pair_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    pairNode verifier ∈ (graph verifier).nodes := List.Mem.head _
private theorem comparison_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    comparisonNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.head _)
private theorem padding_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    paddingNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem implication_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    implicationNode verifier ∈ (graph verifier).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem pair_good {language : Language} (verifier : PolynomialTimeVerifier language) : Good (pairMachine verifier) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct (pairFields verifier) 0,
    BuilderRegisterPack.noRuleAtAccept (pairFields verifier) 0,
    BuilderRegisterPack.noRuleAtReject (pairFields verifier) 0,
    BuilderRegisterPack.acceptState_ne_rejectState (pairFields verifier) 0⟩

private theorem comparison_good : Good BuilderRegisterEquality.machine :=
  ⟨BuilderRegisterEquality.rules_pairwise_query_distinct, BuilderRegisterEquality.noRuleAtAccept,
    BuilderRegisterEquality.noRuleAtReject, BuilderRegisterEquality.acceptState_ne_rejectState⟩

private theorem implication_good {language : Language} (verifier : PolynomialTimeVerifier language) :
    Good (BuilderPreservationImplicationPayload.machine verifier) :=
  ⟨BuilderPreservationImplicationPayload.rules_pairwise_query_distinct verifier,
    BuilderPreservationImplicationPayload.noRuleAtAccept verifier,
    BuilderPreservationImplicationPayload.noRuleAtReject verifier,
    BuilderPreservationImplicationPayload.acceptState_ne_rejectState verifier⟩

private theorem padding_good : Good BuilderConstraintRegionAssembly.oneMachine := by
  refine ⟨WorkMachineChain.rules_pairwise_query_distinct _ _
      BuilderDividerOperands.Delimiter.rules_pairwise_query_distinct
      BuilderConstraintRegionAssembly.Increment.rules_pairwise_query_distinct
      BuilderDividerOperands.Delimiter.noRuleAtAccept,
    WorkMachineChain.noRuleAtAccept _ _ BuilderConstraintRegionAssembly.Increment.noRuleAtAccept,
    ?_, WorkMachineChain.machine_acceptState_ne_rejectState _ _
      BuilderConstraintRegionAssembly.Increment.acceptState_ne_rejectState⟩
  intro rule hMem
  decide +revert

theorem graph_wellFormed {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).WellFormed := by
  have hNames : ((graph verifier).nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1, 2, 3] : List Nat).Pairwise (fun left right => left ≠ right)
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact pair_good verifier
    · exact comparison_good
    · exact padding_good
    · exact implication_good verifier
  · exact ⟨pairNode verifier, pair_mem verifier, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact ⟨⟨comparisonNode verifier, comparison_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨paddingNode, padding_mem verifier, rfl, rfl⟩,
        ⟨implicationNode verifier, implication_mem verifier, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  pairSteps problem index remaining + 1 +
    (BuilderRegisterEquality.workSteps (headValue problem index) (otherValue problem index) + 1 +
      (branchSteps problem index remaining + 1))

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (endTape (frame problem index remaining) inside [])

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  { state := (machine problem.verifier).acceptState
    tape := finalTape problem index remaining inside }

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat)
    (tape : WorkTape) (hState : config.state = state) (hTape : config.tape = tape) :
    config = { state := state, tape := tape } := by
  cases config with
  | mk currentState currentTape =>
      change currentState = state at hState
      change currentTape = tape at hTape
      subst currentState
      subst currentTape
      rfl

theorem pair_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    workRunExact? (pairMachine problem.verifier) (pairSteps problem index remaining)
      (workStartConfiguration (pairMachine problem.verifier) (endTape (frame problem index remaining) inside [])) =
      some {
        state := (pairMachine problem.verifier).acceptState
        tape := endTape (frame problem index remaining ++ [headValue problem index, otherValue problem index]) inside [] } := by
  have h := BuilderRegisterPack.workRunExact (pairFields problem.verifier) 0 []
    (environment problem index remaining .preservation 0 []) [] inside [] rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    pairMachine, pairSteps, frame, environment_values problem index remaining .preservation 0 [] rfl,
    pair_values, List.nil_append, List.append_nil, List.drop_nil] using h

private theorem padding_path {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) (hEqual : headValue problem index = otherValue problem index) :
    AcceptPath (graph problem.verifier) (.node paddingNode.reference) .accept
      (branchSteps problem index remaining + 1)
      (endTape (frame problem index remaining) inside (comparisonBlanks problem index))
      (finalTape problem index remaining inside) := by
  have h := BuilderConstraintRegionAssembly.one_workRunExact (frame problem index remaining) inside (comparisonBlanks problem index)
  have hLocal : LocalAcceptRun paddingNode 5
      (endTape (frame problem index remaining) inside (comparisonBlanks problem index))
      (finalTape problem index remaining inside) := by
    simpa only [LocalAcceptRun, paddingNode, workStartConfiguration, finalTape, finalValues,
      retainedValues, payloadValues, if_pos hEqual, List.append_nil, List.nil_append,
      registerWord, List.length_cons, List.length_append, List.length_replicate, List.length_nil, Nat.add_zero] using h
  simpa only [branchSteps, if_pos hEqual, Nat.add_zero] using
    AcceptPath.step paddingNode .accept 5 0 _ _ _ (padding_mem problem.verifier) hLocal
      (AcceptPath.terminal .accept (finalTape problem index remaining inside))

private theorem implication_path {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) (hDifferent : headValue problem index ≠ otherValue problem index) :
    AcceptPath (graph problem.verifier) (.node (implicationNode problem.verifier).reference) .accept
      (branchSteps problem index remaining + 1)
      (endTape (frame problem index remaining) inside (comparisonBlanks problem index))
      (finalTape problem index remaining inside) := by
  have h := BuilderPreservationImplicationPayload.workRunExact problem index remaining inside (comparisonBlanks problem index)
  have hLocal : LocalAcceptRun (implicationNode problem.verifier)
      (BuilderPreservationImplicationPayload.workSteps problem index remaining)
      (endTape (frame problem index remaining) inside (comparisonBlanks problem index))
      (finalTape problem index remaining inside) := by
    simpa only [LocalAcceptRun, implicationNode, workStartConfiguration,
      BuilderPreservationImplicationPayload.initialConfiguration,
      BuilderPreservationImplicationPayload.finalConfiguration,
      BuilderPreservationImplicationPayload.finalValues, finalTape, finalValues,
      frame, inputValues, retainedValues, payloadValues, if_neg hDifferent,
      List.append_nil, List.append_assoc] using h
  simpa only [branchSteps, if_neg hDifferent, Nat.add_zero] using
    AcceptPath.step (implicationNode problem.verifier) .accept _ 0 _ _ _
      (implication_mem problem.verifier) hLocal
      (AcceptPath.terminal .accept (finalTape problem index remaining inside))

private theorem comparison_path {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    AcceptPath (graph problem.verifier) (.node (comparisonNode problem.verifier).reference) .accept
      (BuilderRegisterEquality.workSteps (headValue problem index) (otherValue problem index) + 1 +
        (branchSteps problem index remaining + 1))
      (endTape (frame problem index remaining ++ [headValue problem index, otherValue problem index]) inside [])
      (finalTape problem index remaining inside) := by
  have hCompare := BuilderRegisterEquality.workRunExact (headValue problem index) (otherValue problem index)
    (frame problem index remaining) inside
  have hTape := BuilderRegisterEquality.final_tape (headValue problem index) (otherValue problem index)
    (frame problem index remaining) inside
  by_cases hEqual : headValue problem index = otherValue problem index
  · have hState := (BuilderRegisterEquality.final_accept_iff (headValue problem index) (otherValue problem index)
      (frame problem index remaining) inside).2 hEqual
    rw [configuration_eq_of_fields _ _ _ hState hTape] at hCompare
    have hLocal : LocalAcceptRun (comparisonNode problem.verifier)
        (BuilderRegisterEquality.workSteps (headValue problem index) (otherValue problem index))
        (endTape (frame problem index remaining ++ [headValue problem index, otherValue problem index]) inside [])
        (endTape (frame problem index remaining) inside (comparisonBlanks problem index)) := by
      simpa only [LocalAcceptRun, comparisonNode, workStartConfiguration,
        BuilderRegisterEquality.initialConfiguration, comparisonBlanks] using hCompare
    exact AcceptPath.step (comparisonNode problem.verifier) .accept _ _ _ _ _ (comparison_mem problem.verifier)
      hLocal (padding_path problem index remaining inside hEqual)
  · have hState := (BuilderRegisterEquality.final_reject_iff (headValue problem index) (otherValue problem index)
      (frame problem index remaining) inside).2 hEqual
    rw [configuration_eq_of_fields _ _ _ hState hTape] at hCompare
    have hLocal : LocalRejectRun (comparisonNode problem.verifier)
        (BuilderRegisterEquality.workSteps (headValue problem index) (otherValue problem index))
        (endTape (frame problem index remaining ++ [headValue problem index, otherValue problem index]) inside [])
        (endTape (frame problem index remaining) inside (comparisonBlanks problem index)) := by
      simpa only [LocalRejectRun, comparisonNode, workStartConfiguration,
        BuilderRegisterEquality.initialConfiguration, comparisonBlanks] using hCompare
    exact AcceptPath.stepReject (comparisonNode problem.verifier) .accept _ _ _ _ _ (comparison_mem problem.verifier)
      hLocal (implication_path problem index remaining inside hEqual)

/-- All source-derived positions, both runtime branches and every control bridge. -/
theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside) =
      some (finalConfiguration problem index remaining inside) := by
  have hPair : LocalAcceptRun (pairNode problem.verifier) (pairSteps problem index remaining)
      (endTape (frame problem index remaining) inside [])
      (endTape (frame problem index remaining ++ [headValue problem index, otherValue problem index]) inside []) := by
    simpa only [LocalAcceptRun, pairNode, workStartConfiguration] using pair_workRunExact problem index remaining inside
  have hPath := AcceptPath.step (pairNode problem.verifier) .accept _ _ _ _ _ (pair_mem problem.verifier)
    hPair (comparison_path problem index remaining inside)
  exact WorkMachineProgramPath.runExact (graph problem.verifier) _ _ _ _ _ (graph_wellFormed problem.verifier) hPath

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining inside)

theorem payload_canonical {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    payloadValues problem index remaining =
      BuilderLocalConstraintPayload.values
        (problem.preservationConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .preservation)) := by
  have hPositions := source_positions problem index hRegion
  have hSlot := BuilderPreservationCoordinates.source_slot problem index hRegion
  change problem.preservationConstraintSlotDirect
    (BuilderConstraintRegionSource.localCoordinate problem index .preservation) =
      BuilderPreservationCoordinates.slot (ofSource problem index hRegion) at hSlot
  rw [hSlot]
  by_cases hDiagonal : (ofSource problem index hRegion).head = (ofSource problem index hRegion).other
  · have hEqual : headValue problem index = otherValue problem index := by
      rw [hPositions.1, hPositions.2]
      exact congrArg Fin.val hDiagonal
    rw [BuilderPreservationCoordinates.slot_diagonal _ hDiagonal, payloadValues, if_pos hEqual]
    rfl
  · have hDifferent : headValue problem index ≠ otherValue problem index := by
      intro hEqual
      rw [hPositions.1, hPositions.2] at hEqual
      exact hDiagonal (Fin.ext hEqual)
    rw [BuilderPreservationCoordinates.slot_off_diagonal _ hDiagonal, payloadValues, if_neg hDifferent]
    exact BuilderPreservationImplicationPayload.payload_values_eq problem index remaining hRegion

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining) =
      some (problem.preservationConstraintSlotDirect
        (BuilderConstraintRegionSource.localCoordinate problem index .preservation)) := by
  rw [payload_canonical problem index remaining hRegion, BuilderLocalConstraintPayload.decode_values]

theorem final_canonical_payload {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    finalValues problem index remaining = frame problem index remaining ++ retainedValues problem index ++
      BuilderLocalConstraintPayload.values
        (problem.preservationConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .preservation)) := by
  rw [finalValues, payload_canonical problem index remaining hRegion]

theorem final_inside_preserved {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape.right =
      (registerWord (retainedValues problem index ++ payloadValues problem index remaining)).reverse ++
        ((registerWord (frame problem index remaining)).reverse ++ inside) := by
  simp only [finalConfiguration, finalTape, finalValues, endTape, registerWord_append,
    List.reverse_append, List.append_assoc]

theorem final_exterior {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape.left =
      (comparisonBlanks problem index).drop
        (registerWord (retainedValues problem index ++ payloadValues problem index remaining)).length := rfl

def inputSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderLiteralArgumentSource.inputBound verifier .preservation (.constant 0)

def pairSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (pairFields verifier) (inputSpanBound verifier)

def pairRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterPack.rawTimePolynomial (pairFields verifier) (inputSpanBound verifier)

def comparisonSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.constant 4) (.mul (.constant 4) (pairSpanBound verifier))

def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderPreservationImplicationPayload.spanBound verifier)
    (.add (inputSpanBound verifier) (.add (.constant 2) (comparisonSpanBound verifier)))

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (pairRawTimeBound verifier)
    (.add (BuilderRegisterEquality.rawTimePolynomial (pairSpanBound verifier))
      (.add (BuilderPreservationImplicationPayload.rawTimeBound verifier) (.constant 48)))

private theorem input_span_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (registerWord (frame problem index remaining)).length ≤ (inputSpanBound problem.verifier).eval problem.input.length :=
  BuilderLiteralArgumentSource.input_span_le problem index remaining .preservation [] (.constant 0)
    hBody hBalance hRegion (Nat.le_refl 0)

theorem pair_source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (registerWord (frame problem index remaining ++ [headValue problem index, otherValue problem index])).length ≤
      (pairSpanBound problem.verifier).eval problem.input.length ∧
    6 * pairSteps problem index remaining ≤ (pairRawTimeBound problem.verifier).eval problem.input.length := by
  have hInput := input_span_le problem index remaining hBody hBalance hRegion
  have hEnvironment :
      (registerWord ([] ++ List.ofFn (environment problem index remaining .preservation 0 []) ++ [])).length ≤
        (inputSpanBound problem.verifier).eval problem.input.length := by
    simpa only [List.nil_append, List.append_nil, environment_values problem index remaining .preservation 0 [] rfl,
      frame] using hInput
  have hPack := BuilderRegisterPack.source_polynomial_bounds (pairFields problem.verifier) (inputSpanBound problem.verifier)
    problem.input.length [] (environment problem index remaining .preservation 0 []) [] hEnvironment
  simpa only [pairSpanBound, pairRawTimeBound, pairSteps, frame, pair_values,
    environment_values problem index remaining .preservation 0 [] rfl, List.nil_append, List.append_nil] using hPack

theorem comparison_source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (comparisonBlanks problem index).length ≤ (comparisonSpanBound problem.verifier).eval problem.input.length ∧
    6 * BuilderRegisterEquality.workSteps (headValue problem index) (otherValue problem index) ≤
      (BuilderRegisterEquality.rawTimePolynomial (pairSpanBound problem.verifier)).eval problem.input.length := by
  have hPair := (pair_source_polynomial_bounds problem index remaining hBody hBalance hRegion).1
  have hFields : headValue problem index ≤ (pairSpanBound problem.verifier).eval problem.input.length ∧
      otherValue problem index ≤ (pairSpanBound problem.verifier).eval problem.input.length := by
    simp only [registerWord_append, List.length_append, registerWord_length, List.length_cons, List.length_nil,
      List.sum_cons, List.sum_nil] at hPair
    constructor <;> omega
  have hComparison := BuilderRegisterEquality.source_polynomial_bounds (headValue problem index) (otherValue problem index)
    problem.input.length (pairSpanBound problem.verifier) hFields.1 hFields.2
  simpa only [comparisonBlanks, List.length_replicate, comparisonSpanBound,
    NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant] using hComparison

/-- The bound includes both the final register word and explicitly cleared exterior cells. -/
theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (registerWord (finalValues problem index remaining)).length +
        (finalConfiguration problem index remaining inside).tape.left.length ≤
      (spanBound problem.verifier).eval problem.input.length ∧
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hInput := input_span_le problem index remaining hBody hBalance hRegion
  have hPair := pair_source_polynomial_bounds problem index remaining hBody hBalance hRegion
  have hComparison := comparison_source_polynomial_bounds problem index remaining hBody hBalance hRegion
  have hPayload := BuilderPreservationImplicationPayload.source_polynomial_bounds problem index remaining hBody hBalance hRegion
  have hRegisters : (registerWord (finalValues problem index remaining)).length ≤
      (BuilderPreservationImplicationPayload.spanBound problem.verifier).eval problem.input.length +
        (inputSpanBound problem.verifier).eval problem.input.length + 2 := by
    by_cases hEqual : headValue problem index = otherValue problem index
    · simp only [finalValues, retainedValues, payloadValues, if_pos hEqual, List.append_nil,
        registerWord_append, List.length_append, registerWord, List.length_cons, List.length_replicate, List.length_nil]
      omega
    · have hWhole : (registerWord (finalValues problem index remaining)).length ≤
          (BuilderPreservationImplicationPayload.spanBound problem.verifier).eval problem.input.length := by
        simpa only [finalValues, BuilderPreservationImplicationPayload.finalValues, frame, inputValues,
          retainedValues, payloadValues, if_neg hEqual, List.append_nil, List.append_assoc] using hPayload.1
      omega
  have hExterior : (finalConfiguration problem index remaining inside).tape.left.length ≤
      (comparisonBlanks problem index).length := by
    change ((comparisonBlanks problem index).drop _).length ≤ _
    rw [List.length_drop]
    exact Nat.sub_le _ _
  have hBranch : 6 * branchSteps problem index remaining ≤
      (BuilderPreservationImplicationPayload.rawTimeBound problem.verifier).eval problem.input.length + 30 := by
    by_cases hEqual : headValue problem index = otherValue problem index
    · simp only [branchSteps, if_pos hEqual]
      omega
    · simp only [branchSteps, if_neg hEqual]
      omega
  constructor
  · simp only [spanBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega
  · simp only [workSteps, rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise (graph verifier) (graph_wellFormed verifier)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineProgramGraph.noRuleAt_globalAccept (graph verifier)

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject (graph verifier)

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := by
  change (0 : Nat) ≠ 1
  decide

end PNP.Concrete.CookLevin.BuilderPreservationPayload

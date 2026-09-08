/-
Copyright (c) 2026 PNP Labs.

Actual paired source packet to the complete canonical initial-cell payload.
The fixed composition derives requests and symbols using the verified source
resolver, then physically computes canonical literal indices and writes the
guarded payload. Source input and prior output are preserved; all source work,
retained scratch, arithmetic and graph bridges have encoded-size bounds.
Initial-prefix, input-only and accepting families and full emission remain open.
-/

import PNP.Concrete.CookLevinBuilderInitialPairedCellResolution
import PNP.Concrete.CookLevinBuilderInitialPairedLiteralPayload

namespace PNP.Concrete.CookLevin.BuilderInitialPairedCellPayload

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)
open BuilderInitialPairedCellSource (metadata coordinate selection sourceFrame sourceBound)
open BuilderInitialPairedCellResolution (cell request)
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)

/-- All ten fields come from the existing actual source-to-symbol resolution. -/
def data {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) : BuilderInitialPairedLiteralPayload.Data :=
  BuilderInitialPairedLiteralPayload.ofResolved (metadata problem length.val)
    (cell problem length offset).1 (cell problem length offset).2 (request problem length offset) problem.input

def payloadValues {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) : List Nat :=
  BuilderInitialPairedLiteralPayload.payloadValues (BuilderInitialPairedLiteralPayload.stateCount problem.verifier)
    (data problem length offset)

theorem data_values {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) :
    BuilderInitialPairedLiteralPayload.dataValues (data problem length offset) =
      BuilderInitialPairedCellResolution.resultFrame problem length offset := rfl

def sourceHistory {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  let values := BuilderInitialPairedCellResolution.finalValues problem index remaining
  values.take (values.length - 10)

private theorem take_prefix (leading suffix : List Nat) :
    (leading ++ suffix).take leading.length = leading := by
  induction leading with
  | nil => rfl
  | cons value rest ih =>
      change value :: (rest ++ suffix).take rest.length = value :: rest
      exact congrArg (List.cons value) ih

/-- The history is computed from the actual run rather than supplied by a caller. -/
theorem source_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    BuilderInitialPairedCellResolution.finalValues problem index remaining =
      sourceHistory problem index remaining ++ BuilderInitialPairedLiteralPayload.dataValues (data problem length offset) := by
  obtain ⟨history, hSource⟩ := BuilderInitialPairedCellResolution.found_suffix
    problem index remaining length offset hPrefix hFound
  have hCut : sourceHistory problem index remaining = history := by
    simp only [sourceHistory, hSource, List.length_append, BuilderInitialPairedCellResolution.resultFrame_length,
      Nat.add_sub_cancel]
    exact take_prefix history _
  rw [hCut, data_values]
  exact hSource

def writtenValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) : List Nat :=
  sourceHistory problem index remaining ++
    BuilderInitialPairedLiteralPayload.outputValues (BuilderInitialPairedLiteralPayload.stateCount problem.verifier)
      (data problem length offset)

def payloadSteps {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) : Nat :=
  BuilderInitialPairedLiteralPayload.workSteps (BuilderInitialPairedLiteralPayload.stateCount problem.verifier)
    (data problem length offset)

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  if coordinate problem index < 3 then BuilderInitialPairedCellResolution.finalValues problem index remaining
  else match selection problem index with
    | none => BuilderInitialPairedCellResolution.finalValues problem index remaining
    | some found => writtenValues problem index remaining found.1 found.2

def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderInitialPairedCellResolution.workSteps problem index remaining + 1 +
    if coordinate problem index < 3 then 0
    else match selection problem index with
      | none => 0
      | some found => payloadSteps problem found.1 found.2 + 1

def payloadNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 1, program := BuilderInitialPairedLiteralPayload.machine (BuilderInitialPairedLiteralPayload.stateCount verifier),
   onAccept := .accept, onReject := .dead}
def sourceNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 0, program := BuilderInitialPairedCellResolution.machine verifier,
   onAccept := .node (payloadNode verifier).reference, onReject := .reject}
def graph {language : Language} (verifier : PolynomialTimeVerifier language) : Graph :=
  {nodes := [sourceNode verifier, payloadNode verifier], entry := (sourceNode verifier).reference}
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph verifier)

theorem graph_nodes_length {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).nodes.length = 2 := rfl

private theorem source_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    sourceNode verifier ∈ (graph verifier).nodes := List.Mem.head _
private theorem payload_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    payloadNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.head _)

theorem graph_wellFormed {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).WellFormed := by
  have hNames : ((graph verifier).nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0, 1] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact ⟨BuilderInitialPairedCellResolution.rules_pairwise_query_distinct verifier,
        BuilderInitialPairedCellResolution.noRuleAtAccept verifier, BuilderInitialPairedCellResolution.noRuleAtReject verifier,
        BuilderInitialPairedCellResolution.acceptState_ne_rejectState verifier⟩
    · exact ⟨BuilderInitialPairedLiteralPayload.rules_pairwise_query_distinct _,
        BuilderInitialPairedLiteralPayload.noRuleAtAccept _, BuilderInitialPairedLiteralPayload.noRuleAtReject _,
        BuilderInitialPairedLiteralPayload.acceptState_ne_rejectState _⟩
  · exact ⟨sourceNode verifier, source_mem verifier, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact ⟨⟨payloadNode verifier, payload_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  WorkMachineProgramGraph.endpointConfiguration (BuilderInitialPairedCellSource.endpoint problem index)
    (endTape (finalValues problem index remaining) (inside problem.input output) [])

/-- Source selection, actual reads, index construction and payload writes form one exact physical run. -/
theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hMode : problem.tableauInputMode = .paired) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  have hSource := BuilderInitialPairedCellResolution.workRunExact problem index remaining output hMode
  simp only [BuilderInitialPairedCellResolution.initialConfiguration, BuilderInitialPairedCellResolution.finalConfiguration,
    BuilderInitialPairedCellSource.endpoint_selection] at hSource
  have hPath : AcceptPath (graph problem.verifier) (.node (sourceNode problem.verifier).reference)
      (BuilderInitialPairedCellSource.endpoint problem index) (workSteps problem index remaining)
      (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
      (endTape (finalValues problem index remaining) (inside problem.input output) []) := by
    rw [BuilderInitialPairedCellSource.endpoint_selection]
    by_cases hPrefix : coordinate problem index < 3
    · simp only [if_pos hPrefix, workSteps, finalValues] at hSource ⊢
      have h := AcceptPath.stepReject (sourceNode problem.verifier) .reject _ 0 _ _ _
        (source_mem problem.verifier) hSource (.terminal .reject _)
      simpa only [Nat.add_zero] using h
    · simp only [if_neg hPrefix, workSteps, finalValues] at hSource ⊢
      cases hFound : selection problem index with
      | none =>
          simp only [hFound] at hSource ⊢
          have h := AcceptPath.stepReject (sourceNode problem.verifier) .reject _ 0 _ _ _
            (source_mem problem.verifier) hSource (.terminal .reject _)
          simpa only [Nat.add_zero] using h
      | some found =>
          rcases found with ⟨length, offset⟩
          simp only [hFound] at hSource ⊢
          have hSuffix := source_suffix problem index remaining length offset hPrefix hFound
          rw [hSuffix] at hSource
          have hPayload := BuilderInitialPairedLiteralPayload.workRunExact
            (BuilderInitialPairedLiteralPayload.stateCount problem.verifier) (data problem length offset)
            (sourceHistory problem index remaining) (inside problem.input output)
          simp only [BuilderInitialPairedLiteralPayload.initialConfiguration, BuilderInitialPairedLiteralPayload.finalConfiguration] at hPayload
          have hP := AcceptPath.step (payloadNode problem.verifier) .accept _ 0 _ _ _ (payload_mem problem.verifier)
            hPayload (.terminal .accept _)
          have h := AcceptPath.step (sourceNode problem.verifier) .accept _ _ _ _ _
            (source_mem problem.verifier) hSource hP
          simpa only [payloadSteps, writtenValues, Nat.add_zero] using h
  have h := WorkMachineProgramPath.runExact (graph problem.verifier) _ _ _ _ _
    (graph_wellFormed problem.verifier) hPath
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node (sourceNode problem.verifier).reference) tape =
        workStartConfiguration (machine problem.verifier) tape := rfl
  have hMachine : WorkMachineProgramGraph.machine (graph problem.verifier) = machine problem.verifier := rfl
  rw [hStart, hMachine] at h
  simpa only [initialConfiguration, finalConfiguration] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hMode : problem.tableauInputMode = .paired) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output hMode)

theorem final_tape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      endTape (finalValues problem index remaining) (inside problem.input output) [] := rfl
theorem final_frontier {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape.left = [] := rfl
theorem endpoint_selection {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    BuilderInitialPairedCellSource.endpoint problem index =
      if coordinate problem index < 3 then .reject
      else match selection problem index with | none => .reject | some _ => .accept :=
  BuilderInitialPairedCellSource.endpoint_selection problem index

private theorem final_state {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state =
      WorkMachineProgramGraph.endpointState (BuilderInitialPairedCellSource.endpoint problem index) := rfl
private theorem accept_state {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState = 0 := rfl
private theorem reject_state {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rejectState = 1 := rfl

theorem final_accept_iff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState ↔
      (BuilderInitialPairedCellSource.decodedCoordinate problem index).isSome = true := by
  have h := BuilderInitialPairedCellResolution.final_accept_iff problem index remaining output
  have hState : (BuilderInitialPairedCellResolution.finalConfiguration problem index remaining output).state =
      WorkMachineProgramGraph.endpointState (BuilderInitialPairedCellSource.endpoint problem index) := rfl
  have hAccept : (BuilderInitialPairedCellResolution.machine problem.verifier).acceptState = 0 := rfl
  rw [hState, hAccept] at h
  rw [final_state, accept_state]
  exact h

theorem final_reject_iff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).rejectState ↔
      BuilderInitialPairedCellSource.decodedCoordinate problem index = none := by
  have h := BuilderInitialPairedCellResolution.final_reject_iff problem index remaining output
  have hState : (BuilderInitialPairedCellResolution.finalConfiguration problem index remaining output).state =
      WorkMachineProgramGraph.endpointState (BuilderInitialPairedCellSource.endpoint problem index) := rfl
  have hReject : (BuilderInitialPairedCellResolution.machine problem.verifier).rejectState = 1 := rfl
  rw [hState, hReject] at h
  rw [final_state, reject_state]
  exact h

theorem found_output {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3) (hFound : selection problem index = some (length, offset)) :
    finalValues problem index remaining = writtenValues problem index remaining length offset := by
  simp only [finalValues, if_neg hPrefix, hFound]

theorem found_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3) (hFound : selection problem index = some (length, offset)) :
    ∃ history : List Nat, finalValues problem index remaining = history ++ payloadValues problem length offset := by
  obtain ⟨history, h⟩ := BuilderInitialPairedLiteralPayload.output_suffix
    (BuilderInitialPairedLiteralPayload.stateCount problem.verifier) (data problem length offset)
  refine ⟨sourceHistory problem index remaining ++ history, ?_⟩
  rw [found_output problem index remaining length offset hPrefix hFound]
  simp only [writtenValues, payloadValues, h, List.append_assoc]

/-- The valid position and one/two-slot bound are consequences of actual source selection. -/
theorem selected_payload_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hFound : selection problem index = some (length, offset)) :
    ∃ position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode),
      position.val = (cell problem length offset).1 ∧
      BuilderInitialConstraintPayload.pairedCellValues problem hMode length position (cell problem length offset).2 =
        some (payloadValues problem length offset) := by
  have hBounds := BuilderInitialPairedCellSource.decoded_bounds problem index hMode length offset hFound
  let position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode) :=
    ⟨(cell problem length offset).1, hBounds.1⟩
  have hOffset : (cell problem length offset).2 <
      BuilderInitialCellCoordinates.requestWidth (request problem length offset) := by
    rw [request, BuilderInitialCellCoordinates.pairedRequest_width]
    exact hBounds.2
  refine ⟨position, rfl, ?_⟩
  have h := BuilderInitialPairedLiteralPayload.canonical_payload problem hMode length position
    (request problem length offset) (cell problem length offset).2 hOffset
  simpa only [BuilderInitialConstraintPayload.pairedCellValues, payloadValues,
    BuilderInitialPairedLiteralPayload.canonicalData, data, request, position] using h

theorem found_canonical_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3) (hFound : selection problem index = some (length, offset)) :
    ∃ (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (payload history : List Nat),
      position.val = (cell problem length offset).1 ∧
      BuilderInitialConstraintPayload.pairedCellValues problem hMode length position (cell problem length offset).2 =
        some payload ∧
      finalValues problem index remaining = history ++ payload := by
  obtain ⟨position, hPosition, hCanonical⟩ := selected_payload_canonical problem index hMode length offset hFound
  obtain ⟨history, hWritten⟩ := found_suffix problem index remaining length offset hPrefix hFound
  exact ⟨position, payloadValues problem length offset, history, hPosition, hCanonical, hWritten⟩

/-- The exact physical endpoint contains the existing canonical payload, without supplied indices or bits. -/
theorem source_canonical_payload {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3) (hFound : selection problem index = some (length, offset)) :
    ∃ (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (payload history : List Nat),
      position.val = (cell problem length offset).1 ∧
      BuilderInitialConstraintPayload.pairedCellValues problem hMode length position (cell problem length offset).2 =
        some payload ∧
      workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
        some
          {state := (machine problem.verifier).acceptState,
           tape := endTape (history ++ payload) (inside problem.input output) []} := by
  obtain ⟨position, payload, history, hPosition, hCanonical, hWritten⟩ :=
    found_canonical_suffix problem index remaining hMode length offset hPrefix hFound
  have hFinal : finalConfiguration problem index remaining output =
      {state := (machine problem.verifier).acceptState,
        tape := endTape (history ++ payload) (inside problem.input output) []} := by
    rw [finalConfiguration, endpoint_selection, if_neg hPrefix, hFound, hWritten]
    rfl
  exact ⟨position, payload, history, hPosition, hCanonical,
    (workRunExact problem index remaining output hMode).trans (congrArg some hFinal)⟩

theorem final_uniform_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hMode : problem.tableauInputMode = .paired) :
    if coordinate problem index < 3 then True
    else match selection problem index with
      | none => True
      | some found => ∃ (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (payload history : List Nat),
          position.val = (cell problem found.1 found.2).1 ∧
          BuilderInitialConstraintPayload.pairedCellValues problem hMode found.1 position (cell problem found.1 found.2).2 =
            some payload ∧ finalValues problem index remaining = history ++ payload := by
  by_cases hPrefix : coordinate problem index < 3
  · simp only [if_pos hPrefix]
  · rw [if_neg hPrefix]
    cases hFound : selection problem index with
    | none => trivial
    | some found => exact found_canonical_suffix problem index remaining hMode found.1 found.2 hPrefix hFound

theorem prefix_output {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hPrefix : coordinate problem index < 3) :
    finalValues problem index remaining = BuilderInitialPairedCellResolution.finalValues problem index remaining := by
  simp only [finalValues, if_pos hPrefix]
theorem exhausted_output {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hFound : selection problem index = none) :
    finalValues problem index remaining = BuilderInitialPairedCellResolution.finalValues problem index remaining := by
  by_cases hPrefix : coordinate problem index < 3
  · simp only [finalValues, if_pos hPrefix]
  · simp only [finalValues, if_neg hPrefix, hFound]

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

def spanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderInitialPairedCellResolution.spanPolynomial verifier bound)
    (BuilderInitialPairedLiteralPayload.spanPolynomial (BuilderInitialPairedLiteralPayload.stateCount verifier)
      (BuilderInitialPairedCellResolution.spanPolynomial verifier bound))
def rawTimePolynomial {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderInitialPairedCellResolution.rawTimePolynomial verifier bound)
    (.add (BuilderInitialPairedLiteralPayload.rawTimePolynomial (BuilderInitialPairedLiteralPayload.stateCount verifier)
      (BuilderInitialPairedCellResolution.spanPolynomial verifier bound)) (.constant 12))

theorem packet_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (bound : NatPolynomial) (inputSize : Nat) (hMode : problem.tableauInputMode = .paired)
    (hSpan : (registerWord (sourceFrame problem index remaining)).length ≤ bound.eval inputSize) :
    (registerWord (finalValues problem index remaining)).length ≤ (spanPolynomial problem.verifier bound).eval inputSize ∧
      6 * workSteps problem index remaining ≤ (rawTimePolynomial problem.verifier bound).eval inputSize := by
  have hSource := BuilderInitialPairedCellResolution.packet_polynomial_bounds problem index remaining bound inputSize hMode hSpan
  by_cases hPrefix : coordinate problem index < 3
  · constructor
    · simp only [finalValues, if_pos hPrefix, spanPolynomial, NatPolynomial.eval_add]
      omega
    · simp only [workSteps, if_pos hPrefix, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
        Nat.mul_add, Nat.mul_one]
      omega
  · cases hFound : selection problem index with
    | none =>
        constructor
        · simp only [finalValues, if_neg hPrefix, hFound, spanPolynomial, NatPolynomial.eval_add]
          omega
        · simp only [workSteps, if_neg hPrefix, hFound, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
            Nat.mul_add, Nat.mul_one]
          omega
    | some found =>
        rcases found with ⟨length, offset⟩
        have hSuffix := source_suffix problem index remaining length offset hPrefix hFound
        have hPayload := BuilderInitialPairedLiteralPayload.source_polynomial_bounds
          (BuilderInitialPairedLiteralPayload.stateCount problem.verifier) (data problem length offset)
          (sourceHistory problem index remaining) (BuilderInitialPairedCellResolution.spanPolynomial problem.verifier bound)
          inputSize (by simpa only [hSuffix] using hSource.1)
        constructor
        · have hFinal : (registerWord (finalValues problem index remaining)).length ≤
              (BuilderInitialPairedLiteralPayload.spanPolynomial (BuilderInitialPairedLiteralPayload.stateCount problem.verifier)
                (BuilderInitialPairedCellResolution.spanPolynomial problem.verifier bound)).eval inputSize := by
            simpa only [finalValues, if_neg hPrefix, hFound, writtenValues] using hPayload.1
          simp only [spanPolynomial, NatPolynomial.eval_add]
          omega
        · simp only [workSteps, if_neg hPrefix, hFound, payloadSteps, Nat.mul_add, Nat.mul_one,
            rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
          omega

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hMode : problem.tableauInputMode = .paired)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    (registerWord (finalValues problem index remaining)).length ≤
        (spanPolynomial problem.verifier (sourceBound problem.verifier)).eval problem.input.length ∧
      6 * workSteps problem index remaining ≤
        (rawTimePolynomial problem.verifier (sourceBound problem.verifier)).eval problem.input.length := by
  apply packet_polynomial_bounds problem index remaining _ _ hMode
  exact BuilderLiteralArgumentSource.input_span_le problem index remaining .initial [] (.constant 0)
    hBody hBalance hRegion (Nat.le_refl 0)

end PNP.Concrete.CookLevin.BuilderInitialPairedCellPayload

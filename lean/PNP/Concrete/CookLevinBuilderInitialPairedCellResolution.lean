/-
Copyright (c) 2026 PNP Labs.

Actual paired source packet to canonical cell request and resolved symbol.
This composition reuses the verified source selector and fixed request
resolver. It derives the request from the physical nine-field source result,
reads actual input when needed, preserves prior output and charges the complete
source-to-resolution run. Literal/payload writing remains downstream.
-/

import PNP.Concrete.CookLevinBuilderInitialPairedCellSource
import PNP.Concrete.CookLevinBuilderInitialRequestResolution

namespace PNP.Concrete.CookLevin.BuilderInitialPairedCellResolution

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)
open BuilderInitialPairedCellSource (metadata startValue coordinate selection sourceFrame sourceBound)
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)

def cell {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) : Nat × Nat :=
  BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset

def request {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) :
    BuilderInitialCellCoordinates.Request problem.certificateLimit :=
  BuilderInitialCellCoordinates.pairedRequest problem.input.length length problem.uniformFuel
    (cell problem length offset).1

def frame {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) : List Nat :=
  BuilderInitialRequestResolution.inputValues (metadata problem length.val)
    (cell problem length offset).1 (cell problem length offset).2 (request problem length offset)

def resultFrame {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) : List Nat :=
  BuilderInitialRequestResolution.resultValues (metadata problem length.val)
    (cell problem length offset).1 (cell problem length offset).2
    (request problem length offset) problem.input

def sourcePrefix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  let values := BuilderInitialPairedCellSource.finalValues problem index remaining
  values.take (values.length - 9)

theorem frame_length {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) : (frame problem length offset).length = 9 := rfl

theorem resultFrame_length {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) : (resultFrame problem length offset).length = 10 := rfl

theorem request_derived {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) :
    BuilderInitialPairedCellSource.requestCode problem length.val offset =
      BuilderInitialPairedRequest.encodeRequest (request problem length offset) :=
  BuilderInitialPairedCellSource.request_canonical problem length offset

theorem resultFrame_values {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) :
    resultFrame problem length offset = frame problem length offset ++
      [BuilderInitialRequestResolution.symbolCode problem.input (request problem length offset)
        (cell problem length offset).2] := rfl

theorem resolved_symbol_bound {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) :
    BuilderInitialRequestResolution.symbolCode problem.input (request problem length offset)
      (cell problem length offset).2 ≤ 2 :=
  BuilderInitialRequestResolution.symbolCode_le _ _ _

private theorem take_prefix (leading suffix : List Nat) :
    (leading ++ suffix).take leading.length = leading := by
  induction leading with
  | nil => rfl
  | cons value rest ih =>
      change value :: (rest ++ suffix).take rest.length = value :: rest
      exact congrArg (List.cons value) ih

/-- The computable history cut is proved from the actual source machine's canonical suffix. -/
theorem source_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    BuilderInitialPairedCellSource.finalValues problem index remaining =
      sourcePrefix problem index remaining ++ frame problem length offset := by
  obtain ⟨history, hSource⟩ := BuilderInitialPairedCellSource.found_canonical_suffix
    problem index remaining length offset hPrefix hFound
  have h : BuilderInitialPairedCellSource.finalValues problem index remaining =
      history ++ frame problem length offset := by
    simpa only [frame, request, cell, BuilderInitialRequestResolution.inputValues] using hSource
  have hCut : sourcePrefix problem index remaining = history := by
    simp only [sourcePrefix, h, List.length_append, frame_length, Nat.add_sub_cancel]
    exact take_prefix history _
  rw [hCut]
  exact h

def resolvedValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) : List Nat :=
  sourcePrefix problem index remaining ++
    BuilderInitialRequestResolution.outputValues (metadata problem length.val)
      (cell problem length offset).1 (cell problem length offset).2 (request problem length offset) problem.input

def resolutionSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) : Nat :=
  BuilderInitialRequestResolution.workSteps (metadata problem length.val)
    (cell problem length offset).1 (cell problem length offset).2 (request problem length offset)
    (sourcePrefix problem index remaining) problem.input

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  if coordinate problem index < 3 then BuilderInitialPairedCellSource.finalValues problem index remaining
  else match selection problem index with
    | none => BuilderInitialPairedCellSource.finalValues problem index remaining
    | some found => resolvedValues problem index remaining found.1 found.2

def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderInitialPairedCellSource.workSteps problem index remaining + 1 +
    if coordinate problem index < 3 then 0
    else match selection problem index with
      | none => 0
      | some found => resolutionSteps problem index remaining found.1 found.2 + 1

def resolveNode : Node :=
  {name := 1, program := BuilderInitialRequestResolution.machine, onAccept := .accept, onReject := .dead}
def sourceNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 0, program := BuilderInitialPairedCellSource.machine verifier, onAccept := .node resolveNode.reference,
   onReject := .reject}
def graph {language : Language} (verifier : PolynomialTimeVerifier language) : Graph :=
  {nodes := [sourceNode verifier, resolveNode], entry := (sourceNode verifier).reference}
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph verifier)

theorem graph_nodes_length {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).nodes.length = 2 := rfl

private theorem source_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    sourceNode verifier ∈ (graph verifier).nodes := List.Mem.head _
private theorem resolve_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    resolveNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.head _)

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
    · exact ⟨BuilderInitialPairedCellSource.rules_pairwise_query_distinct verifier,
        BuilderInitialPairedCellSource.noRuleAtAccept verifier, BuilderInitialPairedCellSource.noRuleAtReject verifier,
        BuilderInitialPairedCellSource.acceptState_ne_rejectState verifier⟩
    · exact ⟨BuilderInitialRequestResolution.rules_pairwise_query_distinct,
        BuilderInitialRequestResolution.noRuleAtAccept, BuilderInitialRequestResolution.noRuleAtReject,
        BuilderInitialRequestResolution.acceptState_ne_rejectState⟩
  · exact ⟨sourceNode verifier, source_mem verifier, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact ⟨⟨resolveNode, resolve_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  WorkMachineProgramGraph.endpointConfiguration (BuilderInitialPairedCellSource.endpoint problem index)
    (endTape (finalValues problem index remaining) (inside problem.input output) [])

/-- No request or input bit is supplied: both are derived by the physical source-to-resolution run. -/
theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hMode : problem.tableauInputMode = .paired) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  have hSource := BuilderInitialPairedCellSource.workRunExact problem index remaining (inside problem.input output) hMode
  simp only [BuilderInitialPairedCellSource.initialConfiguration, BuilderInitialPairedCellSource.finalConfiguration,
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
          have hResolve := BuilderInitialRequestResolution.workRunExact (metadata problem length.val)
            (cell problem length offset).1 (cell problem length offset).2 (request problem length offset)
            (sourcePrefix problem index remaining) problem.input output
          simp only [BuilderInitialRequestResolution.initialConfiguration, BuilderInitialRequestResolution.finalConfiguration] at hResolve
          have hR := AcceptPath.step resolveNode .accept _ 0 _ _ _ (resolve_mem problem.verifier)
            hResolve (.terminal .accept _)
          have h := AcceptPath.step (sourceNode problem.verifier) .accept _ _ _ _ _
            (source_mem problem.verifier) hSource hR
          simpa only [frame, resolutionSteps, resolvedValues, Nat.add_zero] using h
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
      (BuilderInitialPairedCellSource.decodedCoordinate problem index).isSome = true :=
by
  have h := BuilderInitialPairedCellSource.final_accept_iff problem index remaining (inside problem.input output)
  have hState : (BuilderInitialPairedCellSource.finalConfiguration problem index remaining (inside problem.input output)).state =
      WorkMachineProgramGraph.endpointState (BuilderInitialPairedCellSource.endpoint problem index) := rfl
  have hAccept : (BuilderInitialPairedCellSource.machine problem.verifier).acceptState = 0 := rfl
  rw [hState, hAccept] at h
  rw [final_state, accept_state]
  exact h

theorem final_reject_iff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).rejectState ↔
      BuilderInitialPairedCellSource.decodedCoordinate problem index = none :=
by
  have h := BuilderInitialPairedCellSource.final_reject_iff problem index remaining (inside problem.input output)
  have hState : (BuilderInitialPairedCellSource.finalConfiguration problem index remaining (inside problem.input output)).state =
      WorkMachineProgramGraph.endpointState (BuilderInitialPairedCellSource.endpoint problem index) := rfl
  have hReject : (BuilderInitialPairedCellSource.machine problem.verifier).rejectState = 1 := rfl
  rw [hState, hReject] at h
  rw [final_state, reject_state]
  exact h

theorem found_output {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3) (hFound : selection problem index = some (length, offset)) :
    finalValues problem index remaining = resolvedValues problem index remaining length offset := by
  simp only [finalValues, if_neg hPrefix, hFound]
theorem found_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3) (hFound : selection problem index = some (length, offset)) :
    ∃ history : List Nat, finalValues problem index remaining = history ++ resultFrame problem length offset := by
  obtain ⟨history, h⟩ := BuilderInitialRequestResolution.output_suffix (metadata problem length.val)
    (cell problem length offset).1 (cell problem length offset).2 (request problem length offset) problem.input
  refine ⟨sourcePrefix problem index remaining ++ history, ?_⟩
  rw [found_output problem index remaining length offset hPrefix hFound]
  simp only [resolvedValues, resultFrame, h, List.append_assoc]

/-- Every actual successful source selection returns its canonical request and resolved symbol. -/
theorem final_uniform_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    if coordinate problem index < 3 then True
    else match selection problem index with
      | none => True
      | some found => ∃ history : List Nat, finalValues problem index remaining =
          history ++ resultFrame problem found.1 found.2 := by
  by_cases hPrefix : coordinate problem index < 3
  · simp only [if_pos hPrefix]
  · rw [if_neg hPrefix]
    cases hFound : selection problem index with
    | none => trivial
    | some found =>
        exact found_suffix problem index remaining found.1 found.2 hPrefix hFound

theorem prefix_output {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hPrefix : coordinate problem index < 3) :
    finalValues problem index remaining = BuilderInitialPairedCellSource.finalValues problem index remaining := by
  simp only [finalValues, if_pos hPrefix]
theorem exhausted_output {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hFound : selection problem index = none) :
    finalValues problem index remaining = BuilderInitialPairedCellSource.finalValues problem index remaining := by
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
  .add (BuilderInitialPairedCellSource.spanPolynomial verifier bound)
    (BuilderInitialRequestResolution.spanPolynomial (BuilderInitialPairedCellSource.spanPolynomial verifier bound))
def rawTimePolynomial {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderInitialPairedCellSource.rawTimePolynomial verifier bound)
    (.add (BuilderInitialRequestResolution.rawTimePolynomial (BuilderInitialPairedCellSource.spanPolynomial verifier bound))
      (.constant 12))

theorem packet_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (bound : NatPolynomial) (inputSize : Nat) (hMode : problem.tableauInputMode = .paired)
    (hSpan : (registerWord (sourceFrame problem index remaining)).length ≤ bound.eval inputSize) :
    (registerWord (finalValues problem index remaining)).length ≤ (spanPolynomial problem.verifier bound).eval inputSize ∧
      6 * workSteps problem index remaining ≤ (rawTimePolynomial problem.verifier bound).eval inputSize := by
  have hSource := BuilderInitialPairedCellSource.packet_polynomial_bounds problem index remaining bound inputSize hMode hSpan
  by_cases hPrefix : coordinate problem index < 3
  · constructor
    · simp only [finalValues, if_pos hPrefix, spanPolynomial, NatPolynomial.eval_add]
      omega
    · simp only [workSteps, if_pos hPrefix, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega
  · cases hFound : selection problem index with
    | none =>
        constructor
        · simp only [finalValues, if_neg hPrefix, hFound, spanPolynomial, NatPolynomial.eval_add]
          omega
        · simp only [workSteps, if_neg hPrefix, hFound, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
          omega
    | some found =>
        rcases found with ⟨length, offset⟩
        have hSuffix := source_suffix problem index remaining length offset hPrefix hFound
        have hResolve := BuilderInitialRequestResolution.source_polynomial_bounds (metadata problem length.val)
          (cell problem length offset).1 (cell problem length offset).2 (request problem length offset)
          (sourcePrefix problem index remaining) problem.input
          (BuilderInitialPairedCellSource.spanPolynomial problem.verifier bound) inputSize (by
            simpa only [hSuffix, frame] using hSource.1)
        constructor
        · have hFinal : (registerWord (finalValues problem index remaining)).length ≤
              (BuilderInitialRequestResolution.spanPolynomial
                (BuilderInitialPairedCellSource.spanPolynomial problem.verifier bound)).eval inputSize := by
            simpa only [finalValues, if_neg hPrefix, hFound, resolvedValues] using hResolve.1
          simp only [spanPolynomial, NatPolynomial.eval_add]
          omega
        · simp only [workSteps, if_neg hPrefix, hFound, resolutionSteps, Nat.mul_add, Nat.mul_one,
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

end PNP.Concrete.CookLevin.BuilderInitialPairedCellResolution

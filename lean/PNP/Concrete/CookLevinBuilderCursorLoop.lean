/-
Copyright (c) 2026 PNP Labs.

The complete repeated physical Cook-Levin body loop on its source-derived
cursor. A fixed graph tests the remaining register, performs actual token
lookup/recovery/emission/advancement, and follows a literal back edge. Only
remaining = 1 selects final Finish emission. Missing lookup rejects.

The universal exact-run theorem assumes only the original cursor balance.
It charges all bridges, scans and output-prefix growth. This prepared-cursor
loop is not yet the complete original-input builder or packaged reduction.
-/
import PNP.Concrete.CookLevinBuilderCursorOutputAdvance
import PNP.Concrete.CookLevinBuilderCursorRemainingOne

namespace PNP.Concrete.CookLevin.BuilderCursorLoop

open WorkMachineProgramGraph (NodeRef Node Graph NoRuleAt endpointConfiguration)
open PipelineStateNamespace (renameConfiguration)
open BuilderCursorOutputAdvance (nextOutput)

/-- A fixed empty continuation normalizes the five successful result tags. -/
private def returnProgram : WorkMachine :=
  {rules := [], startState := 0, acceptState := 0, rejectState := 1}

def bodyClassify (state : Nat) : Fin 6 := if state < 5 then 0 else 1

def bodyProgram {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineTerminalHandoff.machine (BuilderCursorOutputAdvance.machine verifier) returnProgram bodyClassify

/-- Same finite appender/advance rules, with the fixed Finish entry selected. -/
def finishProgram : WorkMachine :=
  {BuilderCursorOutputAdvance.continuation with startState := BuilderCursorOutputAdvance.entry 4}

private theorem return_rules : returnProgram.rules.Pairwise WorkMachineChain.QueryDistinct :=
  List.Pairwise.nil

private theorem return_no_accept : NoRuleAt returnProgram returnProgram.acceptState := by
  intro rule member
  cases member

theorem bodyClassify_success (request : Option CNFToken) :
    bodyClassify (BuilderCursorTokenRecovery.encodeResult (some request)).val = 0 := by
  cases request with
  | none => rfl
  | some token => cases token <;> rfl

theorem bodyClassify_missing : bodyClassify (BuilderCursorTokenRecovery.encodeResult none).val = 1 := rfl

theorem body_control {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyProgram verifier).rules.Pairwise WorkMachineChain.QueryDistinct ∧
      NoRuleAt (bodyProgram verifier) (bodyProgram verifier).acceptState ∧
      NoRuleAt (bodyProgram verifier) (bodyProgram verifier).rejectState ∧
      (bodyProgram verifier).acceptState ≠ (bodyProgram verifier).rejectState :=
  ⟨WorkMachineTerminalHandoff.rules_pairwise _ _ _
      (BuilderCursorOutputAdvance.rules_pairwise_query_distinct verifier) return_rules return_no_accept,
    WorkMachineTerminalHandoff.noRuleAt_outcome _ _ _ 0,
    WorkMachineTerminalHandoff.noRuleAt_outcome _ _ _ 1, Nat.zero_ne_one⟩

theorem finish_control :
    finishProgram.rules.Pairwise WorkMachineChain.QueryDistinct ∧
      NoRuleAt finishProgram finishProgram.acceptState ∧
      NoRuleAt finishProgram finishProgram.rejectState ∧
      finishProgram.acceptState ≠ finishProgram.rejectState := by
  refine ⟨BuilderCursorOutputAdvance.continuation_rules_pairwise,
    BuilderCursorOutputAdvance.continuation_noRuleAtAccept, ?_, ?_⟩
  · intro rule member
    decide +revert
  · exact WorkMachineChain.machine_acceptState_ne_rejectState
      BuilderTokenAppender.machine BuilderBalancedCursor.machine (by decide)

def guardReference : NodeRef := {name := 0, startState := BuilderCursorRemainingOne.machine.startState}

def bodyNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 1, program := bodyProgram verifier, onAccept := .node guardReference, onReject := .reject}

def finishNode : Node :=
  {name := 2, program := finishProgram, onAccept := .accept, onReject := .reject}

def guardNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 0, program := BuilderCursorRemainingOne.machine,
    onAccept := .node finishNode.reference, onReject := .node (bodyNode verifier).reference}

def graph {language : Language} (verifier : PolynomialTimeVerifier language) : Graph :=
  {nodes := [guardNode verifier, bodyNode verifier, finishNode], entry := (guardNode verifier).reference}

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph verifier)

private theorem guard_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    guardNode verifier ∈ (graph verifier).nodes := List.Mem.head _

private theorem body_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    bodyNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.head _)

private theorem finish_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    finishNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem graph_nodes_length {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).nodes.length = 3 := rfl

theorem graph_wellFormed {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).WellFormed := by
  have hNames : ((graph verifier).nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0, 1, 2] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact ⟨BuilderCursorRemainingOne.rules_pairwise_query_distinct,
        BuilderCursorRemainingOne.noRuleAtAccept, BuilderCursorRemainingOne.noRuleAtReject,
        BuilderCursorRemainingOne.acceptState_ne_rejectState⟩
    · exact body_control verifier
    · exact finish_control
  · exact ⟨guardNode verifier, guard_mem verifier, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact ⟨⟨finishNode, finish_mem verifier, rfl, rfl⟩,
        ⟨bodyNode verifier, body_mem verifier, rfl, rfl⟩⟩
    · exact ⟨⟨guardNode verifier, guard_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise _ (graph_wellFormed verifier)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    NoRuleAt (machine verifier) (machine verifier).acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept _

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject _

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineProgramGraph.machine_accept_ne_reject _

/-- A proof-level output specification, not a runtime request oracle. The
source invariant below proves that the outer optional lookup is present. -/
def completeOutput {language : Language} (problem : VerifierTableauProblem language) :
    Nat → Nat → List CNFToken → List CNFToken
  | _, 0, output => output ++ [CNFToken.finish]
  | index, remaining + 1, output =>
      completeOutput problem (index + 1) remaining
        (nextOutput output ((BuilderCursorTokenLookup.canonicalResult problem index).getD none))

theorem nextOutput_length_le (output : List CNFToken) (request : Option CNFToken) :
    (nextOutput output request).length ≤ output.length + 1 := by
  cases request <;>
    simp only [nextOutput, List.length_append, List.length_cons, List.length_nil] <;> omega

theorem completeOutput_length_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (completeOutput problem index remaining output).length ≤ output.length + remaining + 1 := by
  induction remaining generalizing index output with
  | zero =>
      simp only [completeOutput, List.length_append, List.length_cons, List.length_nil]
      omega
  | succ remaining ih =>
      have hStep := nextOutput_length_le output
        ((BuilderCursorTokenLookup.canonicalResult problem index).getD none)
      have hTail := ih (index + 1)
        (nextOutput output ((BuilderCursorTokenLookup.canonicalResult problem index).getD none))
      change (completeOutput problem (index + 1) remaining
        (nextOutput output ((BuilderCursorTokenLookup.canonicalResult problem index).getD none))).length ≤ _
      omega

theorem body_domain_of_balance {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + (remaining + 2) = BuilderFullScheduleCursorController.bodySlotCount problem) :
    BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem := by
  have hCount : BuilderFullScheduleCursorController.bodySlotCount problem =
      BuilderDividerOperands.count problem * BuilderDividerOperands.width problem + 1 := by
    rw [BuilderFullScheduleCursorController.bodySlotCount_eq]
    rfl
  have hLt : index < BuilderDividerOperands.count problem * BuilderDividerOperands.width problem := by
    rw [hCount] at hBalance
    omega
  exact (Nat.div_lt_iff_lt_mul (BuilderDividerSourceExecution.width_pos problem)).mpr hLt

def stepPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderCursorRemainingOne.rawTimeBound verifier)
    (BuilderCursorOutputAdvance.rawTimeBound verifier)) (.constant 24)

theorem stepPolynomial_eval {language : Language} (verifier : PolynomialTimeVerifier language) (n : Nat) :
    (stepPolynomial verifier).eval n = (BuilderCursorRemainingOne.rawTimeBound verifier).eval n +
      (BuilderCursorOutputAdvance.rawTimeBound verifier).eval n + 24 := rfl

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (BuilderCursorSource.cursorTape problem index remaining output)

private theorem body_classify_of_observe (state : Nat) (request : Option CNFToken)
    (hObserve : BuilderCursorTokenRecovery.decodeState state = some request) :
    bodyClassify state = 0 := by
  by_cases hLt : state < 5
  · simp only [bodyClassify, if_pos hLt]
  · have h0 : state ≠ 0 := by omega
    have h1 : state ≠ 1 := by omega
    have h2 : state ≠ 2 := by omega
    have h3 : state ≠ 3 := by omega
    have h4 : state ≠ 4 := by omega
    simp only [BuilderCursorTokenRecovery.decodeState,
      if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4] at hObserve
    cases hObserve

private theorem body_source {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + (remaining + 1) = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (steps : Nat) (request : Option CNFToken) (final : WorkConfiguration),
      BuilderCursorTokenLookup.canonicalResult problem index = some request ∧
      workRunExact? (bodyProgram problem.verifier) steps
        (workStartConfiguration (bodyProgram problem.verifier)
          (BuilderCursorSource.cursorTape problem index (remaining + 1) output)) = some final ∧
      final.state = (bodyProgram problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (index + 1) remaining (nextOutput output request)) ∧
      6 * steps ≤ (BuilderCursorOutputAdvance.rawTimeBound problem.verifier).eval problem.input.length +
        12 * output.length + 12 := by
  obtain ⟨steps, request, final, hCanonical, hRun, _, hNo, hObserve, hTape, _, hTime⟩ :=
    BuilderCursorOutputAdvance.workRun_polynomial_output_advance problem index remaining output hBody hBalance
  have hClass := body_classify_of_observe final.state request hObserve
  have hNormalized := WorkMachineTerminalHandoff.workRunExact
    (BuilderCursorOutputAdvance.machine problem.verifier) returnProgram bodyClassify
    steps 0 (BuilderCursorSource.cursorTape problem index (remaining + 1) output) final final.tape
    (BuilderCursorOutputAdvance.rules_pairwise_query_distinct problem.verifier)
    return_rules return_no_accept hRun hNo rfl
  rw [hClass] at hNormalized
  refine ⟨steps + 1 + 0 + 1, request, {state := 0, tape := final.tape},
    hCanonical, hNormalized, rfl, hTape, ?_⟩
  omega

private theorem finish_source {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (output : List CNFToken) :
    workRunExact? finishProgram
      (BuilderCursorOutputAdvance.continuationSteps problem index 0 output (some CNFToken.finish))
      (workStartConfiguration finishProgram (BuilderCursorSource.cursorTape problem index 1 output)) =
      some {state := finishProgram.acceptState,
            tape := BuilderCursorSource.cursorTape problem (index + 1) 0 (output ++ [CNFToken.finish])} := by
  have hRun := BuilderCursorOutputAdvance.continuation_workRunExact problem index 0 output (some CNFToken.finish)
  exact PipelineStageBridges.workRunExact?_transport
    BuilderCursorOutputAdvance.continuation finishProgram (fun state => state)
    (fun _ _ h => h) _ _ _ hRun

private theorem guard_accept {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (BuilderCursorRemainingOne.workSteps problem index 1 + 1)
      (initialConfiguration problem index 1 output) =
      some (endpointConfiguration (.node finishNode.reference)
        (BuilderCursorSource.cursorTape problem index 1 output)) := by
  exact WorkMachineProgramGraph.local_then_accept (graph problem.verifier) (guardNode problem.verifier)
    _ _ _ (graph_wellFormed problem.verifier) (guard_mem problem.verifier)
    (BuilderCursorRemainingOne.source_workRunExact problem index 1 output)
    ((BuilderCursorRemainingOne.result_accept_iff 1).mpr rfl)

private theorem guard_reject {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (BuilderCursorRemainingOne.workSteps problem index (remaining + 2) + 1)
      (initialConfiguration problem index (remaining + 2) output) =
      some (endpointConfiguration (.node (bodyNode problem.verifier).reference)
        (BuilderCursorSource.cursorTape problem index (remaining + 2) output)) := by
  exact WorkMachineProgramGraph.local_then_reject (graph problem.verifier) (guardNode problem.verifier)
    _ _ _ (graph_wellFormed problem.verifier) (guard_mem problem.verifier)
    (BuilderCursorRemainingOne.source_workRunExact problem index (remaining + 2) output)
    ((BuilderCursorRemainingOne.result_reject_iff (remaining + 2)).mpr (by omega))

/-- Actual repeated execution from every balanced positive cursor. The only
premise is the original balance; neither requests nor loop executions are
supplied. The result includes final Finish and charges growing output. -/
theorem workRun_complete {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBalance : index + (remaining + 1) = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (steps : Nat) (final : WorkConfiguration),
      workRunExact? (machine problem.verifier) steps
        (initialConfiguration problem index (remaining + 1) output) = some final ∧
      final.state = (machine problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (index + remaining + 1) 0
          (completeOutput problem index remaining output)) ∧
      6 * steps ≤ (remaining + 1) * ((stepPolynomial problem.verifier).eval problem.input.length +
        12 * (output.length + remaining + 1)) := by
  induction remaining generalizing index output with
  | zero =>
      have hGuard := guard_accept problem index output
      have hFinish := WorkMachineProgramGraph.local_then_accept (graph problem.verifier) finishNode
        _ _ _ (graph_wellFormed problem.verifier) (finish_mem problem.verifier)
        (finish_source problem index output) rfl
      have hRun := PipelineMachineSimulation.workRunExact?_compose _ _ _ _ _ _ hGuard hFinish
      have hGuardTime := BuilderCursorRemainingOne.rawTimeBound_le problem index 1 hBalance
      have hFinishTime := BuilderCursorOutputAdvance.continuation_rawTime_le problem index 0 output
        (some CNFToken.finish) hBalance
      refine ⟨(BuilderCursorRemainingOne.workSteps problem index 1 + 1) +
          (BuilderCursorOutputAdvance.continuationSteps problem index 0 output (some CNFToken.finish) + 1),
        endpointConfiguration .accept (BuilderCursorSource.cursorTape problem (index + 1) 0 (output ++ [CNFToken.finish])),
        hRun, rfl, ?_, ?_⟩
      · exact WorkTape.blankEquivalent_refl _
      · simp only [Nat.zero_add, Nat.add_zero, Nat.one_mul, stepPolynomial_eval,
          BuilderCursorOutputAdvance.rawTimeBound_eval]
        omega
  | succ remaining ih =>
      have hBody := body_domain_of_balance problem index remaining hBalance
      obtain ⟨bodySteps, request, bodyFinal, hCanonical, hBodyRun, hBodyAccept, hBodyTape, hBodyTime⟩ :=
        body_source problem index (remaining + 1) output hBody hBalance
      have hNextBalance : (index + 1) + (remaining + 1) =
          BuilderFullScheduleCursorController.bodySlotCount problem := by omega
      obtain ⟨tailSteps, tailFinal, hTailRun, hTailAccept, hTailTape, hTailTime⟩ :=
        ih (index + 1) (nextOutput output request) hNextBalance
      have hEquivalent : WorkConfiguration.BlankEquivalent
          (workStartConfiguration (machine problem.verifier) bodyFinal.tape)
          (initialConfiguration problem (index + 1) (remaining + 1) (nextOutput output request)) :=
        ⟨rfl, hBodyTape⟩
      obtain ⟨actualFinal, hActualRun, hActualEquivalent⟩ :=
        PNP.Concrete.workRunExact?_transport (machine problem.verifier) tailSteps hEquivalent hTailRun
      have hGuard := guard_reject problem index remaining output
      have hBodyGlobal := WorkMachineProgramGraph.local_then_accept (graph problem.verifier)
        (bodyNode problem.verifier) _ _ _ (graph_wellFormed problem.verifier) (body_mem problem.verifier)
        hBodyRun hBodyAccept
      have hPrefix := PipelineMachineSimulation.workRunExact?_compose _ _ _ _ _ _ hGuard hBodyGlobal
      have hRun := PipelineMachineSimulation.workRunExact?_compose _ _ _ _ _ _ hPrefix hActualRun
      refine ⟨(BuilderCursorRemainingOne.workSteps problem index (remaining + 2) + 1) +
          (bodySteps + 1) + tailSteps, actualFinal, hRun,
        hActualEquivalent.state.trans hTailAccept, ?_, ?_⟩
      · have hTape := WorkTape.blankEquivalent_trans hActualEquivalent.tape hTailTape
        have hIndex : (index + 1) + remaining + 1 = index + (remaining + 1) + 1 := by omega
        rw [hIndex] at hTape
        simpa only [completeOutput, hCanonical, Option.getD] using hTape
      · have hGrowth := nextOutput_length_le output request
        have hGuardTime := BuilderCursorRemainingOne.rawTimeBound_le problem index (remaining + 2) hBalance
        have hCapacity : (stepPolynomial problem.verifier).eval problem.input.length +
              12 * ((nextOutput output request).length + remaining + 1) ≤
            (stepPolynomial problem.verifier).eval problem.input.length +
              12 * (output.length + (remaining + 1) + 1) := by omega
        have hTailBound := Nat.le_trans hTailTime (Nat.mul_le_mul_left (remaining + 1) hCapacity)
        have hPrefixTime :
            6 * ((BuilderCursorRemainingOne.workSteps problem index (remaining + 2) + 1) + (bodySteps + 1)) ≤
              (stepPolynomial problem.verifier).eval problem.input.length +
                12 * (output.length + (remaining + 1) + 1) := by
          rw [stepPolynomial_eval]
          omega
        calc
          6 * ((BuilderCursorRemainingOne.workSteps problem index (remaining + 2) + 1) +
              (bodySteps + 1) + tailSteps) =
              6 * ((BuilderCursorRemainingOne.workSteps problem index (remaining + 2) + 1) +
                (bodySteps + 1)) + 6 * tailSteps := by omega
          _ ≤ ((stepPolynomial problem.verifier).eval problem.input.length +
                12 * (output.length + (remaining + 1) + 1)) +
              (remaining + 1) * ((stepPolynomial problem.verifier).eval problem.input.length +
                12 * (output.length + (remaining + 1) + 1)) :=
            Nat.add_le_add hPrefixTime hTailBound
          _ = ((remaining + 1) + 1) * ((stepPolynomial problem.verifier).eval problem.input.length +
                12 * (output.length + (remaining + 1) + 1)) := by
            exact (Nat.add_comm _ _).trans (Nat.succ_mul _ _).symm

theorem uniform_raw_complete {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBalance : index + (remaining + 1) = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (rawSteps : Nat) (final : WorkConfiguration),
      rawSteps ≤ (remaining + 1) * ((stepPolynomial problem.verifier).eval problem.input.length +
        12 * (output.length + remaining + 1)) ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (initialConfiguration problem index (remaining + 1) output)) =
        encodeWorkConfiguration final ∧
      final.state = (machine problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (index + remaining + 1) 0
          (completeOutput problem index remaining output)) := by
  obtain ⟨steps, final, hRun, hAccept, hTape, hTime⟩ :=
    workRun_complete problem index remaining output hBalance
  exact ⟨6 * steps, final, hTime, run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun, hAccept, hTape⟩

end PNP.Concrete.CookLevin.BuilderCursorLoop

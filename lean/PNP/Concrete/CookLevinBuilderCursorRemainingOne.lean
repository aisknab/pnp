/-
Copyright (c) 2026 PNP Labs.

Source-derived, tape-preserving test for the final Cook-Levin body opportunity.
One fixed machine scans to the live remaining register, runs the existing unary
test for one, and returns to the original cursor while retaining the result.

Acceptance means remaining = 1. Rejection means remaining ≠ 1, including zero;
the full loop must use its positive-remaining invariant before treating rejection
as an ordinary body branch. This is the loop guard, not the completed loop or
formula builder. The entire scan, test, return and all bridges are charged.
-/
import PNP.Concrete.CookLevinBuilderCursorTokenRecovery
import PNP.Concrete.CookLevinBuilderUnaryTagMatch

namespace PNP.Concrete.CookLevin.BuilderCursorRemainingOne

open PipelineTape
open PipelineStateNamespace (renameConfiguration)
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)

def probe : WorkMachine :=
  WorkMachineChain.machine BuilderRegisterAccess.seekMachine (BuilderUnaryTagMatch.machine 1)

def classify (state : Nat) : Fin 6 := if state = probe.acceptState then 0 else 1

def machine : WorkMachine :=
  WorkMachineTerminalHandoff.machine probe BuilderCursorRecovery.returnMachine classify

def result (remaining : Nat) : Fin 6 := if remaining = 1 then 0 else 1

def word {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    List WorkSymbol := registerWord (BuilderOperandRegisters.retainedValues problem index remaining)

def probeSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  (word problem index remaining).length + 3 + 1 + BuilderUnaryTagMatch.workSteps 1 remaining

def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  probeSteps problem index remaining + 1 + ((word problem index remaining).length + 2) + 1

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration machine (BuilderCursorSource.cursorTape problem index remaining output)

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  {state := (result remaining).val, tape := BuilderCursorSource.cursorTape problem index remaining output}

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderCursorSource.rawTimeBound verifier) (.constant 42)

private theorem probe_rules : probe.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    BuilderRegisterAccess.seekRules_pairwise_query_distinct
    (BuilderUnaryTagMatch.rules_pairwise_query_distinct 1) BuilderRegisterAccess.seek_noRuleAtAccept

private theorem probe_no_accept : WorkMachineChain.NoRuleAtAccept probe :=
  WorkMachineChain.noRuleAtAccept _ _ (BuilderUnaryTagMatch.noRuleAtAccept 1)

private theorem probe_no_reject : WorkMachineProgramGraph.NoRuleAt probe probe.rejectState := by
  intro rule member
  decide +revert

private theorem probe_ne : probe.acceptState ≠ probe.rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ (BuilderUnaryTagMatch.acceptState_ne_rejectState 1)

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineTerminalHandoff.rules_pairwise _ _ _ probe_rules
    BuilderCursorRecovery.return_control.1 BuilderCursorRecovery.return_control.2.1

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine :=
  WorkMachineTerminalHandoff.noRuleAt_outcome _ _ _ 0

theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineTerminalHandoff.noRuleAt_outcome _ _ _ 1

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState :=
  Nat.zero_ne_one

theorem result_lt_two (remaining : Nat) : (result remaining).val < 2 := by
  unfold result
  split <;> decide

theorem result_accept_iff (remaining : Nat) : (result remaining).val = machine.acceptState ↔ remaining = 1 := by
  by_cases h : remaining = 1
  · simp only [result, if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · simp only [result, if_neg h]
    exact ⟨fun equality => False.elim (Nat.one_ne_zero equality), fun impossible => False.elim (h impossible)⟩

theorem result_reject_iff (remaining : Nat) : (result remaining).val = machine.rejectState ↔ remaining ≠ 1 := by
  by_cases h : remaining = 1
  · simp only [result, if_pos h]
    exact ⟨fun equality => False.elim (Nat.zero_ne_one equality), fun impossible => False.elim (impossible h)⟩
  · simp only [result, if_neg h]
    exact ⟨fun _ => h, fun _ => rfl⟩

private def frame {language : Language} (problem : VerifierTableauProblem language)
    (output : List CNFToken) : WorkTape := BuilderTokenAppender.workspaceTape problem.input [] output

private theorem frame_head {language : Language} (problem : VerifierTableauProblem language)
    (output : List CNFToken) :
    (frame problem output).head = .blank ∨ (frame problem output).head = .zeroBlank ∨
      (frame problem output).head = .oneBlank := by
  unfold frame
  cases problem.input with
  | nil => exact Or.inl rfl
  | cons bit rest =>
      cases bit with
      | false => exact Or.inr (Or.inl rfl)
      | true => exact Or.inr (Or.inr rfl)

private theorem cursor_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    BuilderCursorSource.cursorTape problem index remaining output =
      BuilderRegisterAccess.sourceTape (frame problem output).head (frame problem output).right
        (word problem index remaining) (BuilderCursorSource.preservedTail problem) := by
  unfold BuilderCursorSource.cursorTape BuilderBalancedCursor.sourceTape BuilderBalancedCursor.outside
  rw [BuilderOperandRegisters.cursorWord_values]
  rfl

private theorem root_last {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    ∃ older, BuilderOperandRegisters.retainedValues problem index remaining = older ++ [remaining] := by
  refine ⟨BuilderOperandRegisters.prefixValues
    (BuilderFullScheduleCursorController.bodySlotCountPolynomial problem.verifier)
    (BuilderDimensionRegisters.widthPolynomial problem.verifier) problem.input.length ++ [index], ?_⟩
  simp only [BuilderOperandRegisters.retainedValues, List.append_assoc, List.cons_append, List.nil_append]

private def probeFinalState (remaining : Nat) : Nat :=
  if remaining = 1 then probe.acceptState else probe.rejectState

private theorem probe_final_class (remaining : Nat) : classify (probeFinalState remaining) = result remaining := by
  by_cases h : remaining = 1
  · simp only [probeFinalState, result, if_pos h, classify, if_true]
  · simp only [probeFinalState, result, if_neg h, classify, if_neg (Ne.symm probe_ne)]

private theorem probe_source {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? probe (probeSteps problem index remaining)
      (workStartConfiguration probe (BuilderCursorSource.cursorTape problem index remaining output)) =
      some {state := probeFinalState remaining,
            tape := endTape (BuilderOperandRegisters.retainedValues problem index remaining)
              (leftMarker :: (frame problem output).head :: (frame problem output).right)
              (BuilderCursorSource.preservedTail problem)} := by
  have hSeek := BuilderRegisterAccess.seek_workRunExact
    (frame problem output).head (frame problem output).right (word problem index remaining)
    (BuilderCursorSource.preservedTail problem) (frame_head problem output)
    (BuilderRegisterAccess.registerWord_symbols _)
  obtain ⟨older, hValues⟩ := root_last problem index remaining
  have hMatch : workRunExact? (BuilderUnaryTagMatch.machine 1) (BuilderUnaryTagMatch.workSteps 1 remaining)
      (workStartConfiguration (BuilderUnaryTagMatch.machine 1)
        (endTape (BuilderOperandRegisters.retainedValues problem index remaining)
          (leftMarker :: (frame problem output).head :: (frame problem output).right)
          (BuilderCursorSource.preservedTail problem))) =
      some {state := if remaining = 1 then (BuilderUnaryTagMatch.machine 1).acceptState
          else (BuilderUnaryTagMatch.machine 1).rejectState,
            tape := endTape (BuilderOperandRegisters.retainedValues problem index remaining)
              (leftMarker :: (frame problem output).head :: (frame problem output).right)
              (BuilderCursorSource.preservedTail problem)} := by
    rw [hValues]
    by_cases h : remaining = 1
    · simpa only [h, if_true] using BuilderUnaryTagMatch.accept_workRunExact 1 older
        (leftMarker :: (frame problem output).head :: (frame problem output).right)
        (BuilderCursorSource.preservedTail problem)
    · rw [if_neg h]
      exact BuilderUnaryTagMatch.reject_workRunExact 1 remaining older _ _ h
  have hRun := WorkMachineChain.workRunExact
    BuilderRegisterAccess.seekMachine (BuilderUnaryTagMatch.machine 1)
    ((word problem index remaining).length + 3) (BuilderUnaryTagMatch.workSteps 1 remaining)
    _ _ _ hSeek rfl hMatch
  rw [cursor_layout]
  by_cases h : remaining = 1 <;>
    simpa only [probeSteps, probe, probeFinalState, h, if_true, if_false,
      BuilderRegisterAccess.seekInitialConfiguration, BuilderRegisterAccess.seekFinalConfiguration,
      BuilderRegisterAccess.endTape, word, endTape, workStartConfiguration,
      WorkMachineChain.machine, BuilderRegisterAccess.seekMachine, renameConfiguration] using hRun

/-- Test the actual remaining register, preserving every input/output/cursor
cell. No register-layout, selected result or test-execution premise is supplied. -/
theorem source_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? machine (workSteps problem index remaining) (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  let middle : WorkConfiguration :=
    {state := probeFinalState remaining,
      tape := endTape (BuilderOperandRegisters.retainedValues problem index remaining)
        (leftMarker :: (frame problem output).head :: (frame problem output).right)
        (BuilderCursorSource.preservedTail problem)}
  have hProbe := probe_source problem index remaining output
  have hNo : WorkMachineProgramGraph.NoRuleAt probe middle.state := by
    dsimp only [middle, probeFinalState]
    split
    · exact probe_no_accept
    · exact probe_no_reject
  have hReturn := BuilderCursorRecovery.return_workRunExact
    (BuilderOperandRegisters.retainedValues problem index remaining) (frame problem output).head
    (frame problem output).right (BuilderCursorSource.preservedTail problem)
  have hRun := WorkMachineTerminalHandoff.workRunExact
    probe BuilderCursorRecovery.returnMachine classify
    (probeSteps problem index remaining) ((word problem index remaining).length + 2)
    (BuilderCursorSource.cursorTape problem index remaining output) middle
    (BuilderCursorSource.cursorTape problem index remaining output)
    probe_rules BuilderCursorRecovery.return_control.1 BuilderCursorRecovery.return_control.2.1
    hProbe hNo (by rw [cursor_layout]; exact hReturn)
  simpa only [initialConfiguration, finalConfiguration, workSteps, middle, probe_final_class, machine] using hRun

theorem source_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine machine) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (source_workRunExact problem index remaining output)

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hSpan := BuilderCursorSource.invariant_span problem index remaining hBalance
  rw [BuilderOperandRegisters.cursorWord_values] at hSpan
  have hTest := BuilderUnaryTagMatch.workSteps_le 1 remaining
  simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant,
    BuilderCursorSource.rawTimeBound_eval, workSteps, probeSteps, word]
  omega

end PNP.Concrete.CookLevin.BuilderCursorRemainingOne

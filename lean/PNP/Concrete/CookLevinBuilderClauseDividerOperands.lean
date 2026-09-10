/-
Copyright (c) 2026 PNP Labs.

Source-derived operands for clause-occupancy division. Copy the live first
quotient and the clause-slot width already materialized in the source postorder
registers. No caller supplies either value, a tape or a correctness certificate.
All control offsets depend only on the fixed verifier, never its input.

The body continuation preserves the original workspace. This component prepares
the second division; occupancy, emission, Finish integration and the complete
formula-builder loop and reduction remain open.
-/

import PNP.Concrete.CookLevinBuilderSourceRegisterRestore

namespace PNP.Concrete.CookLevin.BuilderClauseDividerOperands

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count width quadratic)
open BuilderDividerSourceExecution (sourceSpan)

def clauseWidthPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.constant 1)
    (.mul (formulaVariableCountPolynomial verifier) (formulaVariableCountPolynomial verifier))

def clauseWidth {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  (clauseWidthPolynomial problem.verifier).eval problem.input.length

theorem clauseWidth_value {language : Language} (problem : VerifierTableauProblem language) :
    clauseWidth problem = problem.formulaClauseSlotsPerConstraint := rfl

theorem clauseWidth_pos {language : Language} (problem : VerifierTableauProblem language) :
    0 < clauseWidth problem := by
  change 0 < 1 + (formulaVariableCountPolynomial problem.verifier).eval problem.input.length *
    (formulaVariableCountPolynomial problem.verifier).eval problem.input.length
  omega

theorem clauseCount_product {language : Language} (problem : VerifierTableauProblem language) :
    count problem = problem.formulaConstraintSlotCount * clauseWidth problem := rfl

def olderValues {language : Language} (problem : VerifierTableauProblem language) : List Nat :=
  registerValues (formulaConstraintCountPolynomial problem.verifier) problem.input.length ++
    BuilderOperandRegisters.rootPrefix (clauseWidthPolynomial problem.verifier) problem.input.length

def newerValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : List Nat :=
  count problem :: BuilderOperandRegisters.newerValues problem index remaining .clauseCount

def newerCount {language : Language} (verifier : PolynomialTimeVerifier language) : Nat :=
  BuilderOperandRegisters.newerCount verifier .clauseCount + 1

theorem newerValues_length {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    (newerValues problem index remaining).length = newerCount problem.verifier := by
  simp only [newerValues, newerCount, List.length_cons, BuilderOperandRegisters.newerValues_length]

theorem newerCount_eq {language : Language} (verifier : PolynomialTimeVerifier language) :
    newerCount verifier = nodeCount (formulaClauseTokenPolynomial verifier) +
      nodeCount (BuilderDimensionRegisters.widthPolynomial verifier) + 7 := rfl

/-- Locate the already-compiled clause-width subexpression, not a supplied divisor. -/
theorem retainedValues_selection {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    BuilderOperandRegisters.retainedValues problem index remaining =
      olderValues problem ++ [clauseWidth problem] ++ newerValues problem index remaining := by
  have hRoot := BuilderOperandRegisters.registerValues_rootPrefix
    (formulaClauseCountPolynomial problem.verifier) problem.input.length
  have hProduct : registerValues (formulaClauseCountPolynomial problem.verifier) problem.input.length =
      (registerValues (formulaConstraintCountPolynomial problem.verifier) problem.input.length ++
        registerValues (clauseWidthPolynomial problem.verifier) problem.input.length) ++ [count problem] := rfl
  have hPrefix := List.append_cancel_right (hRoot.symm.trans hProduct)
  rw [BuilderOperandRegisters.retainedValues_selection problem .clauseCount index remaining]
  change BuilderOperandRegisters.rootPrefix (formulaClauseCountPolynomial problem.verifier)
      problem.input.length ++ [count problem] ++
        BuilderOperandRegisters.newerValues problem index remaining .clauseCount =
    olderValues problem ++ [clauseWidth problem] ++ newerValues problem index remaining
  rw [hPrefix, BuilderOperandRegisters.registerValues_rootPrefix
    (clauseWidthPolynomial problem.verifier) problem.input.length]
  simp only [olderValues, newerValues, clauseWidth, List.append_assoc, List.cons_append, List.nil_append]

private theorem retained_span {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (BuilderOperandRegisters.retainedValues problem index remaining)).length =
      (sourceSpan problem.verifier).eval problem.input.length := by
  have h := BuilderCursorSource.invariant_span problem index remaining hBalance
  rw [BuilderOperandRegisters.cursorWord_values, scratchWord_length] at h
  exact h

/-- Both the selected magnitude and all intervening registers fit the original source span. -/
theorem source_selection_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    clauseWidth problem ≤ (sourceSpan problem.verifier).eval problem.input.length ∧
      (newerValues problem index remaining).length + (newerValues problem index remaining).sum ≤
        (sourceSpan problem.verifier).eval problem.input.length := by
  have hLength := congrArg (fun values => (registerWord values).length)
    (retainedValues_selection problem index remaining)
  rw [retained_span problem index remaining hBalance] at hLength
  simp only [registerWord_length, List.length_append, List.length_cons, List.length_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at hLength
  constructor <;> omega

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

private theorem copy_run (older newer : List Nat) (value offset : Nat)
    (inside tail : List WorkSymbol) (hOffset : newer.length = offset) :
    workRunExact? (RegisterCopy.machine offset) (RegisterCopy.steps newer value)
        (workStartConfiguration (RegisterCopy.machine offset)
          (endTape (older ++ [value] ++ newer) inside tail)) =
      some {
        state := (RegisterCopy.machine offset).acceptState
        tape := endTape (older ++ [value] ++ newer ++ [value]) inside (tail.drop (value + 1))
      } := by
  rw [← hOffset, RegisterCopy.machine_acceptState]
  have h := RegisterCopy.workRunExact (registerWord older) inside tail value newer
  change workRunExact? (RegisterCopy.machine newer.length) (RegisterCopy.steps newer value)
      { state := 0, tape := {
          left := tail
          head := scratchEndSymbol
          right := (registerWord older ++ registerWord ([value] ++ newer)).reverse ++ inside
        } } =
    some {
      state := RegisterCopy.stateCount newer.length
      tape := {
        left := tail.drop (value + 1)
        head := scratchEndSymbol
        right := (registerWord older ++ registerWord ([value] ++ newer ++ [value])).reverse ++ inside
      }
    } at h
  simpa only [workStartConfiguration, RegisterCopy.machine_startState,
    endTape, registerWord_append, List.append_assoc] using h

private theorem copy_noRule (offset : Nat) :
    WorkMachineChain.NoRuleAtAccept (RegisterCopy.machine offset) := by
  intro rule hRule
  exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState offset rule hRule)

namespace QuotientPreparation

def machine : WorkMachine :=
  WorkMachineChain.machine BuilderDividerOperands.Delimiter.machine (RegisterCopy.machine 2)

def steps (count quotient : Nat) : Nat := 2 + 1 + RegisterCopy.steps [count, 0] quotient

/-- Allocate zero and copy the live quotient across precisely two newer registers. -/
theorem workRunExact (older : List Nat) (count quotient : Nat) (workspace : List WorkSymbol) :
    workRunExact? machine (steps count quotient)
        (workStartConfiguration machine (endTape (older ++ [quotient, count]) workspace [])) =
      some {
        state := machine.acceptState
        tape := endTape (older ++ [quotient, count, 0, quotient]) workspace []
      } := by
  have hEmpty : workRunExact? BuilderDividerOperands.Delimiter.machine 2
      (workStartConfiguration BuilderDividerOperands.Delimiter.machine
        (endTape (older ++ [quotient, count]) workspace [])) =
      some {
        state := BuilderDividerOperands.Delimiter.machine.acceptState
        tape := endTape (older ++ [quotient, count, 0]) workspace []
      } := by
    simpa only [List.drop_nil, List.append_assoc, List.cons_append, List.nil_append] using
      BuilderDividerOperands.Delimiter.workRunExact (older ++ [quotient, count]) workspace []
  have hCopy : workRunExact? (RegisterCopy.machine 2) (RegisterCopy.steps [count, 0] quotient)
      (workStartConfiguration (RegisterCopy.machine 2)
        (endTape (older ++ [quotient, count, 0]) workspace [])) =
      some {
        state := (RegisterCopy.machine 2).acceptState
        tape := endTape (older ++ [quotient, count, 0, quotient]) workspace []
      } := by
    simpa only [List.drop_nil, List.append_assoc, List.cons_append, List.nil_append] using
      copy_run older [count, 0] quotient 2 workspace [] rfl
  exact chain_run BuilderDividerOperands.Delimiter.machine (RegisterCopy.machine 2)
    2 (RegisterCopy.steps [count, 0] quotient) _ _ _ hEmpty hCopy

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct BuilderDividerOperands.Delimiter.machine
    (RegisterCopy.machine 2) BuilderDividerOperands.Delimiter.rules_pairwise_query_distinct
    (RegisterCopy.rules_pairwise_query_distinct 2) BuilderDividerOperands.Delimiter.noRuleAtAccept

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine :=
  WorkMachineChain.noRuleAtAccept BuilderDividerOperands.Delimiter.machine
    (RegisterCopy.machine 2) (copy_noRule 2)

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ (RegisterCopy.machine_acceptState_ne_rejectState 2)

end QuotientPreparation

def quotient {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  index / width problem

def extraBeforeWidth {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  BuilderSourceRegisterRestore.appended problem index ++ [0, quotient problem index]

def preparedExtra {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  BuilderSourceRegisterRestore.appended problem index ++ [0, quotient problem index, clauseWidth problem]

def newerForCopy {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : List Nat :=
  newerValues problem index remaining ++ extraBeforeWidth problem index

def copyOffset {language : Language} (verifier : PolynomialTimeVerifier language) : Nat :=
  newerCount verifier + 8

theorem copyOffset_eq {language : Language} (verifier : PolynomialTimeVerifier language) :
    copyOffset verifier = nodeCount (formulaClauseTokenPolynomial verifier) +
      nodeCount (BuilderDimensionRegisters.widthPolynomial verifier) + 15 := rfl

theorem newerForCopy_length {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    (newerForCopy problem index remaining).length = copyOffset problem.verifier := by
  simp only [newerForCopy, extraBeforeWidth, BuilderSourceRegisterRestore.appended,
    copyOffset, newerValues_length, List.length_append, List.length_cons, List.length_nil]

def tapeAfter {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (extra : List Nat) : WorkTape :=
  endTape (BuilderOperandRegisters.retainedValues problem index remaining ++
    BuilderSourceRegisterRestore.appended problem index ++ extra) (inside problem.input output) []

theorem restored_tape_handoff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderSourceRegisterRestore.restorationFinal problem index remaining output).tape =
      tapeAfter problem index remaining output [] := by
  simp only [BuilderSourceRegisterRestore.restorationFinal, tapeAfter, List.append_nil]

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine QuotientPreparation.machine (RegisterCopy.machine (copyOffset verifier))

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (BuilderSourceRegisterRestore.restorationFinal problem index remaining output).tape

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  {
    state := (machine problem.verifier).acceptState
    tape := tapeAfter problem index remaining output [0, quotient problem index, clauseWidth problem]
  }

def workSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  QuotientPreparation.steps (count problem) (quotient problem index) + 1 +
    RegisterCopy.steps (newerForCopy problem index remaining) (clauseWidth problem)

private theorem quotient_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? QuotientPreparation.machine (QuotientPreparation.steps (count problem) (quotient problem index))
        (workStartConfiguration QuotientPreparation.machine (tapeAfter problem index remaining output [])) =
      some {
        state := QuotientPreparation.machine.acceptState
        tape := tapeAfter problem index remaining output [0, quotient problem index]
      } := by
  have h := QuotientPreparation.workRunExact
    (BuilderOperandRegisters.retainedValues problem index remaining ++ [count problem, 0, index, width problem])
    (count problem) (quotient problem index) (inside problem.input output)
  simpa only [tapeAfter, BuilderSourceRegisterRestore.appended, quotient,
    List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using h

private theorem width_copy_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (RegisterCopy.machine (copyOffset problem.verifier))
        (RegisterCopy.steps (newerForCopy problem index remaining) (clauseWidth problem))
        (workStartConfiguration (RegisterCopy.machine (copyOffset problem.verifier))
          (tapeAfter problem index remaining output [0, quotient problem index])) =
      some {
        state := (RegisterCopy.machine (copyOffset problem.verifier)).acceptState
        tape := tapeAfter problem index remaining output [0, quotient problem index, clauseWidth problem]
      } := by
  have hValues : BuilderOperandRegisters.retainedValues problem index remaining ++
      BuilderSourceRegisterRestore.appended problem index ++ [0, quotient problem index] =
    olderValues problem ++ [clauseWidth problem] ++ newerForCopy problem index remaining := by
    rw [retainedValues_selection problem index remaining]
    simp only [newerForCopy, extraBeforeWidth, List.append_assoc]
  have h := copy_run (olderValues problem) (newerForCopy problem index remaining)
    (clauseWidth problem) (copyOffset problem.verifier) (inside problem.input output) []
    (newerForCopy_length problem index remaining)
  rw [← hValues] at h
  simpa only [tapeAfter, List.append_assoc, List.cons_append, List.nil_append, List.drop_nil] using h

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  unfold initialConfiguration
  rw [restored_tape_handoff]
  exact chain_run QuotientPreparation.machine (RegisterCopy.machine (copyOffset problem.verifier))
    (QuotientPreparation.steps (count problem) (quotient problem index))
    (RegisterCopy.steps (newerForCopy problem index remaining) (clauseWidth problem)) _ _ _
    (quotient_run problem index remaining output) (width_copy_run problem index remaining output)

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output)

def dividerOlder {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : List Nat :=
  BuilderOperandRegisters.retainedValues problem index remaining ++
    [count problem, 0, index, width problem, quotient problem index]

theorem final_tape_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      endTape (dividerOlder problem index remaining ++
        [count problem, 0, quotient problem index, clauseWidth problem])
        (inside problem.input output) [] := by
  simp only [finalConfiguration, tapeAfter, dividerOlder, BuilderSourceRegisterRestore.appended,
    quotient, List.append_assoc, List.cons_append, List.nil_append]

theorem finalConfiguration_state {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState := rfl

theorem preparedExtra_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (preparedExtra problem index).length = 9 := rfl

theorem final_register_span_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (BuilderOperandRegisters.retainedValues problem index remaining ++
      preparedExtra problem index)).length ≤
        8 * (sourceSpan problem.verifier).eval problem.input.length + 9 := by
  let span := (sourceSpan problem.verifier).eval problem.input.length
  have hCount : count problem ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .clauseCount index remaining hBalance
  have hIndex : index ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .index index remaining hBalance
  have hWidth : width problem ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .tokenWidth index remaining hBalance
  have hQuotient := Nat.le_trans (Nat.div_le_self index (width problem)) hIndex
  have hClause : clauseWidth problem ≤ span := (source_selection_bounds problem index remaining hBalance).1
  rw [registerWord_append, List.length_append, retained_span problem index remaining hBalance]
  simp only [registerWord_length, preparedExtra, BuilderSourceRegisterRestore.appended,
    quotient, List.length_append, List.length_cons, List.length_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
  omega

/-- The two copy scans include their allocations; the two serial bridges and empty register cost four. -/
theorem workSteps_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    workSteps problem index remaining ≤
      4 + 2 * quadratic (7 * (sourceSpan problem.verifier).eval problem.input.length + 8) := by
  let span := (sourceSpan problem.verifier).eval problem.input.length
  let larger := 7 * span + 8
  have hCount : count problem ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .clauseCount index remaining hBalance
  have hIndex : index ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .index index remaining hBalance
  have hWidth : width problem ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .tokenWidth index remaining hBalance
  have hQuotient := Nat.le_trans (Nat.div_le_self index (width problem)) hIndex
  have hSelected := source_selection_bounds problem index remaining hBalance
  have hQNewer : ([count problem, 0] : List Nat).length + [count problem, 0].sum ≤ larger := by
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
    dsimp only [larger]
    omega
  have hDNewer : (newerForCopy problem index remaining).length +
      (newerForCopy problem index remaining).sum ≤ larger := by
    simp only [newerForCopy, extraBeforeWidth, BuilderSourceRegisterRestore.appended,
      quotient, List.length_append, List.length_cons, List.length_nil, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
    dsimp only [larger]
    omega
  have hQCopy := RegisterCopy.steps_le [count problem, 0] (quotient problem index) larger
    (by unfold quotient; dsimp only [larger]; omega) hQNewer
  have hDCopy := RegisterCopy.steps_le (newerForCopy problem index remaining) (clauseWidth problem) larger
    (by dsimp only [larger]; omega) hDNewer
  change workSteps problem index remaining ≤ 4 + 2 * quadratic larger
  unfold workSteps QuotientPreparation.steps quadratic
  omega

private def quadraticPolynomial (value : NatPolynomial) : NatPolynomial :=
  let next := NatPolynomial.add value (.constant 1)
  .add (.add (.mul (.mul (.constant 4) next) next) (.mul (.constant 9) next)) (.constant 5)

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let larger := NatPolynomial.add (.mul (.constant 7) (sourceSpan verifier)) (.constant 8)
  .mul (.constant 6) (.add (.constant 4) (.mul (.constant 2) (quadraticPolynomial larger)))

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have h := Nat.mul_le_mul_left 6 (workSteps_le problem index remaining hBalance)
  simpa only [rawTimeBound, quadraticPolynomial, quadratic, NatPolynomial.eval_add,
    NatPolynomial.eval_mul, NatPolynomial.eval_constant] using h

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct QuotientPreparation.machine
    (RegisterCopy.machine (copyOffset verifier)) QuotientPreparation.rules_pairwise_query_distinct
    (RegisterCopy.rules_pairwise_query_distinct (copyOffset verifier)) QuotientPreparation.noRuleAtAccept

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineChain.noRuleAtAccept QuotientPreparation.machine (RegisterCopy.machine (copyOffset verifier))
    (copy_noRule (copyOffset verifier))

theorem machine_acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _
    (RegisterCopy.machine_acceptState_ne_rejectState (copyOffset verifier))

def bodyMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderSourceRegisterRestore.bodyMachine verifier) (machine verifier)

def bodyInitial {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (bodyMachine problem.verifier)
    (BuilderCursorSource.cursorTape problem index remaining output)

def bodyFinal {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState (finalConfiguration problem index remaining output)

def bodySteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  BuilderSourceRegisterRestore.bodySteps problem index remaining + 1 + workSteps problem index remaining

private theorem body_initial_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    bodyInitial problem index remaining output =
      renameConfiguration WorkMachineChain.firstState
        (BuilderSourceRegisterRestore.bodyInitial problem index remaining output) := rfl

/-- Continue the actual body branch; no continuation from a rejecting Finish state is claimed. -/
theorem body_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : index / width problem < count problem) :
    workRunExact? (bodyMachine problem.verifier) (bodySteps problem index remaining)
        (bodyInitial problem index remaining output) = some (bodyFinal problem index remaining output) := by
  have hPrepare := workRunExact problem index remaining output
  have hInitial : initialConfiguration problem index remaining output =
      workStartConfiguration (machine problem.verifier)
        (BuilderSourceRegisterRestore.bodyFinal problem index remaining output).tape := rfl
  rw [hInitial] at hPrepare
  have h := WorkMachineChain.workRunExact (BuilderSourceRegisterRestore.bodyMachine problem.verifier)
    (machine problem.verifier) (BuilderSourceRegisterRestore.bodySteps problem index remaining)
    (workSteps problem index remaining)
    (BuilderSourceRegisterRestore.bodyInitial problem index remaining output)
    (BuilderSourceRegisterRestore.bodyFinal problem index remaining output)
    (finalConfiguration problem index remaining output)
    (BuilderSourceRegisterRestore.body_workRunExact problem index remaining output hBody)
    (BuilderSourceRegisterRestore.body_finalConfiguration_state problem index remaining output)
    hPrepare
  simpa only [bodyMachine, bodySteps, bodyFinal, body_initial_eq] using h

theorem body_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : index / width problem < count problem) :
    run (compileWorkMachine (bodyMachine problem.verifier)) (6 * bodySteps problem index remaining)
        (encodeWorkConfiguration (bodyInitial problem index remaining output)) =
      encodeWorkConfiguration (bodyFinal problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (body_workRunExact problem index remaining output hBody)

theorem body_finalConfiguration_state {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (bodyFinal problem index remaining output).state = (bodyMachine problem.verifier).acceptState := rfl

theorem body_final_tape_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (bodyFinal problem index remaining output).tape =
      endTape (dividerOlder problem index remaining ++ [count problem, 0, quotient problem index, clauseWidth problem])
        (inside problem.input output) [] := final_tape_layout problem index remaining output

def bodyRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderSourceRegisterRestore.bodyRawTimeBound verifier) (.constant 6)) (rawTimeBound verifier)

theorem body_rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * bodySteps problem index remaining ≤ (bodyRawTimeBound problem.verifier).eval problem.input.length := by
  have hBody := BuilderSourceRegisterRestore.body_rawTimeBound_le problem index remaining hBalance
  have hPrepare := rawTimeBound_le problem index remaining hBalance
  simp only [bodyRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  unfold bodySteps
  omega

theorem body_rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct (BuilderSourceRegisterRestore.bodyMachine verifier)
    (machine verifier) (BuilderSourceRegisterRestore.body_rules_pairwise_query_distinct verifier)
    (rules_pairwise_query_distinct verifier) (BuilderSourceRegisterRestore.body_noRuleAtAccept verifier)

theorem body_noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (bodyMachine verifier) :=
  WorkMachineChain.noRuleAtAccept (BuilderSourceRegisterRestore.bodyMachine verifier)
    (machine verifier) (noRuleAtAccept verifier)

theorem body_acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).acceptState ≠ (bodyMachine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ (machine_acceptState_ne_rejectState verifier)

end PNP.Concrete.CookLevin.BuilderClauseDividerOperands

/-
Copyright (c) 2026 PNP Labs.

Source-derived divider operands: append the clause count, an empty boundary
register, the current index and the token width without resupplying their values.
Every copy is executed by a fixed finite machine. Original registers and the
represented input/output survive, and the exact consumed exterior tail is stated.
Marker conversion, divider execution, cleanup and the complete loop remain open.
-/

import PNP.Concrete.CookLevinBuilderOperandRegisters

namespace PNP.Concrete.CookLevin.BuilderDividerOperands

open PipelineTape PipelineStateNamespace
open BuilderUnaryPolynomial

/-- An end-focused register word; the exterior tail is not assumed empty. -/
def endTape (values : List Nat) (inside tail : List WorkSymbol) : WorkTape :=
  { left := tail, head := scratchEndSymbol, right := (registerWord values).reverse ++ inside }

namespace Delimiter

private def firstSpec : StateSpec := fun read =>
  if read = scratchEndSymbol then writeAction 1 separatorSymbol .left else deadAction 3 read

private def secondSpec : StateSpec := fun _ => writeAction 2 scratchEndSymbol .stay

/-- Allocate one genuinely empty register, independently of the cursor value. -/
def machine : WorkMachine :=
  { rules := rulesFrom 0 [firstSpec, secondSpec],
    startState := 0, acceptState := 2, rejectState := 3 }

theorem rules_length : machine.rules.length = 18 := rfl

theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  rulesFrom_pairwise_query_distinct 0 [firstSpec, secondSpec]

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := by
  intro rule hRule
  change rule.sourceState ≠ 2
  change rule ∈ rulesFrom 0 [firstSpec, secondSpec] at hRule
  decide +revert

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

private theorem second_step (left right : List WorkSymbol) (symbol : WorkSymbol) :
    workStep? machine { state := 1, tape := { left := left, head := symbol, right := right } } =
      some { state := 2, tape := { left := left, head := scratchEndSymbol, right := right } } := by
  have hFind := findWorkRule_rulesFrom_at_append 0 [firstSpec] secondSpec [] symbol
  exact workStep?_eq_apply_of_find machine _ (ruleOf 1 secondSpec symbol) rfl hFind

theorem workRunExact (values : List Nat) (inside tail : List WorkSymbol) :
    workRunExact? machine 2 (workStartConfiguration machine (endTape values inside tail)) =
      some { state := machine.acceptState, tape := endTape (values ++ [0]) inside (tail.drop 1) } := by
  let middle : WorkConfiguration :=
    { state := 1, tape := {
        left := tail.drop 1
        head := tail.headD .blank
        right := separatorSymbol :: ((registerWord values).reverse ++ inside)
      } }
  have hFirst : workStep? machine (workStartConfiguration machine (endTape values inside tail)) =
      some middle := by
    cases tail <;> rfl
  have hSecond : workStep? machine middle =
      some { state := machine.acceptState, tape := endTape (values ++ [0]) inside (tail.drop 1) } := by
    rw [show machine.acceptState = 2 from rfl]
    simpa only [middle, endTape, registerWord_append, registerWord, List.replicate_zero,
      List.append_nil, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append] using
      second_step (tail.drop 1) (separatorSymbol :: ((registerWord values).reverse ++ inside))
        (tail.headD .blank)
  simp only [workRunExact?, hFirst, hSecond]

end Delimiter

/-- Common exact endpoint wrapper; every serial bridge costs one work step. -/
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

def count {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  BuilderOperandRegisters.copiedValue problem 0 .clauseCount

def width {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  BuilderOperandRegisters.copiedValue problem 0 .tokenWidth

/-- These values are output specifications, not inputs to the finite machine. -/
def appended {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    List Nat :=
  [count problem, 0, index, width problem]

def inside (input : BitString) (output : List CNFToken) : List WorkSymbol :=
  let frame := BuilderTokenAppender.workspaceTape input [] output
  leftMarker :: frame.head :: frame.right

def tapeAfter {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (extra : List Nat) : WorkTape :=
  endTape (BuilderOperandRegisters.retainedValues problem index remaining ++ extra)
    (inside problem.input output)
    ((BuilderCursorSource.preservedTail problem).drop (registerWord extra).length)

private theorem count_tape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderOperandRegisters.finalConfiguration problem .clauseCount index remaining output).tape =
      tapeAfter problem index remaining output [count problem] := by
  have hValues := BuilderOperandRegisters.retainedValues_selection problem .clauseCount index remaining
  have hLength : (registerWord [count problem]).length = count problem + 1 := by
    simp [registerWord_length, Nat.add_comm]
  unfold tapeAfter endTape
  rw [hValues, hLength]
  change ({
      left := (BuilderCursorSource.preservedTail problem).drop (count problem + 1)
      head := scratchEndSymbol
      right := (registerWord (BuilderOperandRegisters.olderValues problem .clauseCount) ++
        registerWord ([count problem] ++ BuilderOperandRegisters.newerValues problem index remaining .clauseCount ++
          [count problem])).reverse ++ inside problem.input output
    } : WorkTape) = _
  simp only [registerWord_append, List.append_assoc, count, BuilderOperandRegisters.copiedValue]

def countDelimiterMachine {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachine :=
  WorkMachineChain.machine (BuilderOperandRegisters.machine verifier .clauseCount) Delimiter.machine

def indexMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (countDelimiterMachine verifier) (RegisterCopy.machine 3)

def tokenOffset {language : Language} (verifier : PolynomialTimeVerifier language) : Nat :=
  BuilderOperandRegisters.newerCount verifier .tokenWidth + 3

/-- Only the verifier determines this control table; input values never generate rules. -/
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (indexMachine verifier) (RegisterCopy.machine (tokenOffset verifier))

private def indexNewer {language : Language} (problem : VerifierTableauProblem language)
    (remaining : Nat) : List Nat := [remaining, count problem, 0]

private def tokenNewer {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : List Nat :=
  BuilderOperandRegisters.newerValues problem index remaining .tokenWidth ++ [count problem, 0, index]

private theorem tokenNewer_length {language : Language}
    (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (tokenNewer problem index remaining).length = tokenOffset problem.verifier := by
  simp only [tokenNewer, tokenOffset, List.length_append, BuilderOperandRegisters.newerValues_length,
    List.length_cons, List.length_nil]

private def countDelimiterSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  BuilderOperandRegisters.workSteps problem .clauseCount index remaining + 1 + 2

private def indexSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  countDelimiterSteps problem index remaining + 1 +
    RegisterCopy.steps (indexNewer problem remaining) index

def workSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  indexSteps problem index remaining + 1 +
    RegisterCopy.steps (tokenNewer problem index remaining) (width problem)

private theorem delimiter_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? Delimiter.machine 2
        (workStartConfiguration Delimiter.machine
          (tapeAfter problem index remaining output [count problem])) =
      some {
        state := Delimiter.machine.acceptState
        tape := tapeAfter problem index remaining output [count problem, 0]
      } := by
  have h := Delimiter.workRunExact
    (BuilderOperandRegisters.retainedValues problem index remaining ++ [count problem])
    (inside problem.input output)
    ((BuilderCursorSource.preservedTail problem).drop (registerWord [count problem]).length)
  simpa only [tapeAfter, List.append_assoc, List.cons_append, List.nil_append,
    List.drop_drop, registerWord_length, List.length_cons, List.length_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem index_copy_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (RegisterCopy.machine 3) (RegisterCopy.steps (indexNewer problem remaining) index)
        (workStartConfiguration (RegisterCopy.machine 3)
          (tapeAfter problem index remaining output [count problem, 0])) =
      some {
        state := (RegisterCopy.machine 3).acceptState
        tape := tapeAfter problem index remaining output [count problem, 0, index]
      } := by
  have hValues : BuilderOperandRegisters.retainedValues problem index remaining ++ [count problem, 0] =
      BuilderOperandRegisters.olderValues problem .index ++ [index] ++ indexNewer problem remaining := by
    rw [BuilderOperandRegisters.retainedValues_selection problem .index index remaining]
    simp only [BuilderOperandRegisters.copiedValue, BuilderOperandRegisters.newerValues, indexNewer,
      List.append_assoc, List.cons_append, List.nil_append]
  have h := copy_run (BuilderOperandRegisters.olderValues problem .index) (indexNewer problem remaining)
    index 3 (inside problem.input output)
    ((BuilderCursorSource.preservedTail problem).drop (registerWord [count problem, 0]).length) rfl
  rw [← hValues] at h
  simpa only [tapeAfter, List.append_assoc, List.cons_append, List.nil_append,
    List.drop_drop, registerWord_length, List.length_cons, List.length_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem token_copy_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (RegisterCopy.machine (tokenOffset problem.verifier))
        (RegisterCopy.steps (tokenNewer problem index remaining) (width problem))
        (workStartConfiguration (RegisterCopy.machine (tokenOffset problem.verifier))
          (tapeAfter problem index remaining output [count problem, 0, index])) =
      some {
        state := (RegisterCopy.machine (tokenOffset problem.verifier)).acceptState
        tape := tapeAfter problem index remaining output (appended problem index)
      } := by
  have hValues : BuilderOperandRegisters.retainedValues problem index remaining ++ [count problem, 0, index] =
      BuilderOperandRegisters.olderValues problem .tokenWidth ++ [width problem] ++
        tokenNewer problem index remaining := by
    rw [BuilderOperandRegisters.retainedValues_selection problem .tokenWidth index remaining]
    simp only [width, BuilderOperandRegisters.copiedValue, tokenNewer, List.append_assoc]
  have h := copy_run (BuilderOperandRegisters.olderValues problem .tokenWidth) (tokenNewer problem index remaining)
    (width problem) (tokenOffset problem.verifier) (inside problem.input output)
    ((BuilderCursorSource.preservedTail problem).drop (registerWord [count problem, 0, index]).length)
    (tokenNewer_length problem index remaining)
  rw [← hValues] at h
  simpa only [tapeAfter, appended, List.append_assoc, List.cons_append, List.nil_append,
    List.drop_drop, registerWord_length, List.length_cons, List.length_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (BuilderCursorSource.cursorTape problem index remaining output)

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  { state := (machine problem.verifier).acceptState,
    tape := tapeAfter problem index remaining output (appended problem index) }

theorem finalConfiguration_state {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state =
      (machine problem.verifier).acceptState := rfl

theorem final_tape_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      { left := (BuilderCursorSource.preservedTail problem).drop
          (count problem + index + width problem + 4),
        head := scratchEndSymbol,
        right := (registerWord
          (BuilderOperandRegisters.retainedValues problem index remaining ++
            [count problem, 0, index, width problem])).reverse ++ inside problem.input output } := by
  unfold finalConfiguration tapeAfter appended endTape
  have hLength : (registerWord [count problem, 0, index, width problem]).length =
      count problem + index + width problem + 4 := by
    simp [registerWord_length] <;> omega
  rw [hLength]

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  have hCount := BuilderOperandRegisters.workRunExact problem .clauseCount index remaining output
  have hFinal :
      BuilderOperandRegisters.finalConfiguration problem .clauseCount index remaining output =
        { state := (BuilderOperandRegisters.machine problem.verifier .clauseCount).acceptState,
          tape := tapeAfter problem index remaining output [count problem] } := by
    exact configuration_eq_of_fields _ _ _
      (BuilderOperandRegisters.finalConfiguration_state problem .clauseCount index remaining output)
      (count_tape problem index remaining output)
  rw [hFinal] at hCount
  have hFirst := chain_run (BuilderOperandRegisters.machine problem.verifier .clauseCount) Delimiter.machine
    (BuilderOperandRegisters.workSteps problem .clauseCount index remaining) 2 _ _ _ hCount
    (delimiter_run problem index remaining output)
  have hIndex := chain_run (countDelimiterMachine problem.verifier) (RegisterCopy.machine 3)
    (countDelimiterSteps problem index remaining)
    (RegisterCopy.steps (indexNewer problem remaining) index) _ _ _ hFirst
    (index_copy_run problem index remaining output)
  exact chain_run (indexMachine problem.verifier) (RegisterCopy.machine (tokenOffset problem.verifier))
    (indexSteps problem index remaining)
    (RegisterCopy.steps (tokenNewer problem index remaining) (width problem)) _ _ _ hIndex
    (token_copy_run problem index remaining output)

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output)

theorem rules_pairwise_query_distinct {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := by
  have hCount := BuilderRegisterAccess.rules_pairwise_query_distinct
    (BuilderOperandRegisters.newerCount verifier .clauseCount)
  have hCountNo := BuilderRegisterAccess.noRuleAtAccept (BuilderOperandRegisters.newerCount verifier .clauseCount)
  have hFirst := WorkMachineChain.rules_pairwise_query_distinct
    (BuilderOperandRegisters.machine verifier .clauseCount) Delimiter.machine hCount
    Delimiter.rules_pairwise_query_distinct hCountNo
  have hFirstNo : WorkMachineChain.NoRuleAtAccept (countDelimiterMachine verifier) := by
    apply WorkMachineChain.noRuleAtAccept
    exact Delimiter.noRuleAtAccept
  have hIndex := WorkMachineChain.rules_pairwise_query_distinct
    (countDelimiterMachine verifier) (RegisterCopy.machine 3) hFirst
    (RegisterCopy.rules_pairwise_query_distinct 3) hFirstNo
  have hIndexNo : WorkMachineChain.NoRuleAtAccept (indexMachine verifier) := by
    apply WorkMachineChain.noRuleAtAccept
    exact copy_noRule 3
  exact WorkMachineChain.rules_pairwise_query_distinct
    (indexMachine verifier) (RegisterCopy.machine (tokenOffset verifier)) hIndex
    (RegisterCopy.rules_pairwise_query_distinct (tokenOffset verifier)) hIndexNo

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := by
  apply WorkMachineChain.noRuleAtAccept
  exact copy_noRule (tokenOffset verifier)

theorem machine_acceptState_ne_rejectState {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _
    (RegisterCopy.machine_acceptState_ne_rejectState (tokenOffset verifier))

/-- Original register span bounds values and scans even at a nonzero cursor. -/
private theorem selection_span {language : Language} (problem : VerifierTableauProblem language)
    (operand : BuilderOperandRegisters.Operand) (index remaining : Nat) :
    let span := (registerWord (BuilderOperandRegisters.retainedValues problem index remaining)).length
    BuilderOperandRegisters.copiedValue problem index operand ≤ span ∧
      (BuilderOperandRegisters.newerValues problem index remaining operand).length +
        (BuilderOperandRegisters.newerValues problem index remaining operand).sum ≤ span := by
  have hValues := BuilderOperandRegisters.retainedValues_selection problem operand index remaining
  have hLength := congrArg (fun values => (registerWord values).length) hValues
  simp only [registerWord_length, List.length_append, List.length_cons, List.length_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at hLength
  dsimp only
  simp only [registerWord_length]
  constructor <;> omega

def quadratic (value : Nat) : Nat :=
  4 * (value + 1) * (value + 1) + 9 * (value + 1) + 5

theorem workSteps_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    let span := (registerWord (BuilderOperandRegisters.retainedValues problem index remaining)).length
    workSteps problem index remaining ≤ span + 4 + quadratic span + 5 +
      2 * quadratic (3 * span + 3) := by
  let span := (registerWord (BuilderOperandRegisters.retainedValues problem index remaining)).length
  have hCount := selection_span problem .clauseCount index remaining
  have hIndex := selection_span problem .index index remaining
  have hToken := selection_span problem .tokenWidth index remaining
  have hC : count problem ≤ span := hCount.1
  have hI : index ≤ span := hIndex.1
  have hT : width problem ≤ span := hToken.1
  have hR : remaining ≤ span := by
    have h := hIndex.2
    change 1 + remaining ≤ span at h
    omega
  have hIndexNewer : (indexNewer problem remaining).length +
      (indexNewer problem remaining).sum ≤ 3 * span + 3 := by
    simp only [indexNewer, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Nat.zero_add]
    omega
  have hTokenNewer : (tokenNewer problem index remaining).length +
      (tokenNewer problem index remaining).sum ≤ 3 * span + 3 := by
    have h := hToken.2
    simp only [tokenNewer, List.length_append, List.length_cons, List.length_nil,
      List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
    omega
  have hIndexBound := RegisterCopy.steps_le (indexNewer problem remaining) index
    (3 * span + 3) (by omega) hIndexNewer
  have hTokenBound := RegisterCopy.steps_le (tokenNewer problem index remaining) (width problem)
    (3 * span + 3) (by omega) hTokenNewer
  have hAccess := BuilderRegisterAccess.workSteps_le
    (registerWord (BuilderOperandRegisters.olderValues problem .clauseCount))
    (BuilderOperandRegisters.copiedValue problem index .clauseCount)
    (BuilderOperandRegisters.newerValues problem index remaining .clauseCount) span (by
      rw [← BuilderOperandRegisters.cursorWord_selection problem .clauseCount index remaining,
        BuilderOperandRegisters.cursorWord_values]
      exact Nat.le_refl _)
  change workSteps problem index remaining ≤ span + 4 + quadratic span + 5 +
    2 * quadratic (3 * span + 3)
  unfold workSteps indexSteps countDelimiterSteps BuilderOperandRegisters.workSteps
  unfold quadratic
  omega

private def quadraticPolynomial (value : NatPolynomial) : NatPolynomial :=
  let next := NatPolynomial.add value (.constant 1)
  .add (.add (.mul (.mul (.constant 4) next) next) (.mul (.constant 9) next)) (.constant 5)

/-- Includes the source scan, three register allocations/copies and all bridges. -/
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let span := registerSpanPolynomial (BuilderDimensionRegisters.polynomial verifier)
  let larger := NatPolynomial.add (.mul (.constant 3) span) (.constant 3)
  .mul (.constant 6)
    (.add (.add (.add (.add span (.constant 4)) (quadraticPolynomial span)) (.constant 5))
      (.mul (.constant 2) (quadraticPolynomial larger)))

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have h := Nat.mul_le_mul_left 6 (workSteps_le problem index remaining)
  have hSpan := BuilderCursorSource.invariant_span problem index remaining hBalance
  rw [BuilderOperandRegisters.cursorWord_values] at hSpan
  rw [hSpan, scratchWord_length] at h
  simpa only [rawTimeBound, quadraticPolynomial, quadratic,
    NatPolynomial.eval_mul, NatPolynomial.eval_add, NatPolynomial.eval_constant] using h

def fromRawMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderInitialization.machine verifier) (machine verifier)

def fromRawInitial {language : Language} (problem : VerifierTableauProblem language) :
    WorkConfiguration :=
  workStartConfiguration (fromRawMachine problem.verifier) (rawInputWorkTape problem.input)

def fromRawFinal {language : Language} (problem : VerifierTableauProblem language) :
    WorkConfiguration :=
  { state := (fromRawMachine problem.verifier).acceptState,
    tape := (finalConfiguration problem 0
      (BuilderFullScheduleCursorController.bodySlotCount problem)
      (encodeUnaryTokens problem.FormulaWidth)).tape }

def fromRawSteps {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  BuilderInitialization.workSteps problem + 1 +
    workSteps problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)

theorem fromRaw_workRunExact {language : Language} (problem : VerifierTableauProblem language) :
    workRunExact? (fromRawMachine problem.verifier) (fromRawSteps problem)
        (fromRawInitial problem) = some (fromRawFinal problem) := by
  have hInit := BuilderInitialization.workRunExact problem
  have hInitFinal : BuilderInitialization.finalConfiguration problem =
      { state := (BuilderInitialization.machine problem.verifier).acceptState,
        tape := BuilderCursorSource.cursorTape problem 0
          (BuilderFullScheduleCursorController.bodySlotCount problem)
          (encodeUnaryTokens problem.FormulaWidth) } := by
    exact configuration_eq_of_fields _ _ _
      (BuilderInitialization.finalConfiguration_state problem)
      (BuilderCursorSource.initializer_tape_handoff problem)
  rw [hInitFinal] at hInit
  exact chain_run (BuilderInitialization.machine problem.verifier) (machine problem.verifier)
    (BuilderInitialization.workSteps problem)
    (workSteps problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)) _ _ _ hInit
    (workRunExact problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)
      (encodeUnaryTokens problem.FormulaWidth))

theorem fromRaw_run_compile_exact {language : Language} (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (fromRawMachine problem.verifier)) (6 * fromRawSteps problem)
        (encodeWorkConfiguration (fromRawInitial problem)) =
      encodeWorkConfiguration (fromRawFinal problem) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (fromRaw_workRunExact problem)

def fromRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) :
    NatPolynomial :=
  .add (.add (BuilderInitialization.rawTimeBound verifier) (.constant 6)) (rawTimeBound verifier)

theorem fromRawTimeBound_le {language : Language} (problem : VerifierTableauProblem language) :
    6 * fromRawSteps problem ≤ (fromRawTimeBound problem.verifier).eval problem.input.length := by
  have hInit := BuilderInitialization.rawTimeBound_le problem
  have hAssembly := rawTimeBound_le problem 0
    (BuilderFullScheduleCursorController.bodySlotCount problem) (Nat.zero_add _)
  simp only [fromRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  unfold fromRawSteps
  omega

end PNP.Concrete.CookLevin.BuilderDividerOperands

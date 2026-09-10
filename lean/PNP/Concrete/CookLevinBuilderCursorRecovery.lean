/-
Copyright (c) 2026 PNP Labs.

Physical recovery of the original cursor after arbitrary nonempty scratch
history. A fixed root ordinal, independent of runtime values and suffix length,
selects the preserved registers. The existing root eraser clears the suffix;
a four-rule scan returns to the original input head without changing the input,
output, or retained registers. Every scan is charged.

This is the recovery component. Connecting all actual token endpoints while
preserving their outcomes, and the complete formula-building loop, remain open.
-/
import PNP.Concrete.CookLevinBuilderRegisterRootErase
import PNP.Concrete.CookLevinBuilderRequestedPairLookup

namespace PNP.Concrete.CookLevin.BuilderCursorRecovery

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRequestedPairLookup (BlankExterior storedCells)

private def keep (source target : Nat) (symbol : WorkSymbol) (move : HeadMove) : WorkRule :=
  {sourceState := source, targetState := target, readSymbol := symbol, writeSymbol := symbol, move := move}

def returnMachine : WorkMachine :=
  {rules := [keep 0 1 scratchEndSymbol .right,
    keep 1 1 unitSymbol .right, keep 1 1 separatorSymbol .right,
    keep 1 2 leftMarker .right], startState := 0, acceptState := 2, rejectState := 3}

theorem return_rules_length : returnMachine.rules.length = 4 := rfl

private def rightFocus (left right : List WorkSymbol) : WorkTape :=
  match right with
  | [] => {left := left, head := .blank, right := []}
  | symbol :: rest => {left := left, head := symbol, right := rest}

private theorem compose {program : WorkMachine} {n m : Nat} {a b c : WorkConfiguration}
    (first : workRunExact? program n a = some b) (second : workRunExact? program m b = some c) :
    workRunExact? program (n + m) a = some c :=
  PipelineMachineSimulation.workRunExact?_compose program n m a b c first second

private theorem one_step {program : WorkMachine} {a b : WorkConfiguration}
    (step : workStep? program a = some b) : workRunExact? program 1 a = some b := by
  simp only [workRunExact?, step]

private theorem scan_right (word : List WorkSymbol) (after before : List WorkSymbol)
    (hSymbols : BuilderBalancedCursor.RegisterSymbols word) :
    workRunExact? returnMachine word.length
      {state := 1, tape := rightFocus before (word ++ after)} =
      some {state := 1, tape := rightFocus (word.reverse ++ before) after} := by
  induction word generalizing before with
  | nil => rfl
  | cons symbol rest ih =>
      have hSymbol := hSymbols symbol List.mem_cons_self
      have hRest : BuilderBalancedCursor.RegisterSymbols rest := by
        intro item hItem
        exact hSymbols item (List.mem_cons_of_mem symbol hItem)
      have hStep : workStep? returnMachine
          {state := 1, tape := rightFocus before ((symbol :: rest) ++ after)} =
          some {state := 1, tape := rightFocus (symbol :: before) (rest ++ after)} := by
        rcases hSymbol with rfl | rfl <;>
          simp only [List.cons_append, rightFocus] <;> cases rest ++ after <;> rfl
      have hRun := compose (one_step hStep) (ih (symbol :: before) hRest)
      have hClock : 1 + rest.length = (symbol :: rest).length := by
        simp only [List.length_cons]
        omega
      rw [hClock] at hRun
      simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using hRun

/-- Return across every retained register, including an empty root prefix. -/
theorem return_workRunExact (before : List Nat) (head : WorkSymbol) (tail outside : List WorkSymbol) :
    workRunExact? returnMachine ((registerWord before).length + 2)
      (workStartConfiguration returnMachine (endTape before (leftMarker :: head :: tail) outside)) =
      some {
        state := returnMachine.acceptState
        tape := BuilderRegisterAccess.sourceTape head tail (registerWord before) outside
      } := by
  let word := (registerWord before).reverse
  have hStart : workStep? returnMachine
      (workStartConfiguration returnMachine (endTape before (leftMarker :: head :: tail) outside)) =
      some {state := 1, tape := rightFocus (scratchEndSymbol :: outside) (word ++ leftMarker :: head :: tail)} := by
    simp only [workStartConfiguration, endTape, word]
    cases (registerWord before).reverse <;> rfl
  have hSymbols : BuilderBalancedCursor.RegisterSymbols word := by
    intro symbol hSymbol
    exact BuilderRegisterAccess.registerWord_symbols before symbol (List.mem_reverse.mp hSymbol)
  have hScan := scan_right word (leftMarker :: head :: tail) (scratchEndSymbol :: outside) hSymbols
  have hStop : workStep? returnMachine
      {
        state := 1
        tape := {
          left := registerWord before ++ scratchEndSymbol :: outside
          head := leftMarker
          right := head :: tail
        }
      } =
      some {
        state := returnMachine.acceptState
        tape := BuilderRegisterAccess.sourceTape head tail (registerWord before) outside
      } := rfl
  simp only [word, List.reverse_reverse, rightFocus] at hScan
  have hRun := compose (compose (one_step hStart) hScan) (one_step hStop)
  have hClock : 1 + word.length + 1 = (registerWord before).length + 2 := by
    simp only [word, List.length_reverse]
    omega
  rw [hClock] at hRun
  exact hRun

theorem return_control :
    returnMachine.rules.Pairwise WorkMachineChain.QueryDistinct ∧
      WorkMachineChain.NoRuleAtAccept returnMachine ∧
      WorkMachineProgramGraph.NoRuleAt returnMachine returnMachine.rejectState ∧
      returnMachine.acceptState ≠ returnMachine.rejectState := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · unfold WorkMachineChain.QueryDistinct
    decide
  · intro item h
    decide +revert
  · intro item h
    decide +revert

def machine (beforeCount : Nat) : WorkMachine :=
  WorkMachineChain.machine (BuilderRegisterRootErase.machine beforeCount) returnMachine

def clearedOutside (value : Nat) (after : List Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  List.replicate (BuilderRegisterRootErase.discardedSpan value after) WorkSymbol.blank ++ outside

def workSteps (before : List Nat) (value : Nat) (after : List Nat) : Nat :=
  BuilderRegisterRootErase.workSteps before value after + 1 + ((registerWord before).length + 2)

def initialConfiguration (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine beforeCount)
    (endTape (before ++ [value] ++ after) (leftMarker :: head :: tail) outside)

def finalConfiguration (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside : List WorkSymbol) : WorkConfiguration :=
  {state := (machine beforeCount).acceptState,
    tape := BuilderRegisterAccess.sourceTape head tail (registerWord before) (clearedOutside value after outside)}

/-- The finite program depends on the retained root count, never the scratch history. -/
theorem workRunExact (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside : List WorkSymbol) (hLength : before.length = beforeCount) :
    workRunExact? (machine beforeCount) (workSteps before value after)
      (initialConfiguration beforeCount before value after head tail outside) =
      some (finalConfiguration beforeCount before value after head tail outside) := by
  have hErase := BuilderRegisterRootErase.workRunExact beforeCount before value after (head :: tail) outside hLength
  have hReturn := return_workRunExact before head tail (clearedOutside value after outside)
  exact WorkMachineChain.workRunExact _ _ _ _ _ _ _ hErase rfl hReturn

theorem run_compile_exact (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside : List WorkSymbol) (hLength : before.length = beforeCount) :
    run (compileWorkMachine (machine beforeCount)) (6 * workSteps before value after)
      (encodeWorkConfiguration (initialConfiguration beforeCount before value after head tail outside)) =
      encodeWorkConfiguration (finalConfiguration beforeCount before value after head tail outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact beforeCount before value after head tail outside hLength)

theorem final_head_and_tail (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside : List WorkSymbol) :
    (finalConfiguration beforeCount before value after head tail outside).tape.head = head ∧
      (finalConfiguration beforeCount before value after head tail outside).tape.right = tail := ⟨rfl, rfl⟩

theorem final_storedCells (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside : List WorkSymbol) :
    storedCells (finalConfiguration beforeCount before value after head tail outside).tape =
      storedCells (initialConfiguration beforeCount before value after head tail outside).tape := by
  simp only [storedCells, finalConfiguration, initialConfiguration, workStartConfiguration,
    BuilderRegisterAccess.sourceTape, endTape, clearedOutside,
    BuilderRegisterRootErase.discardedSpan, registerWord_append, List.length_append,
    List.length_cons, List.length_reverse, List.length_replicate]
  omega

private theorem blank_replicate_append (amount : Nat) (outside : List WorkSymbol) (hBlank : BlankExterior outside) :
    BlankExterior (List.replicate amount WorkSymbol.blank ++ outside) := by
  intro index
  induction amount generalizing index with
  | zero => exact hBlank index
  | succ amount ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index

theorem clearedOutside_blank (value : Nat) (after : List Nat) (outside : List WorkSymbol)
    (hBlank : BlankExterior outside) : BlankExterior (clearedOutside value after outside) :=
  blank_replicate_append _ outside hBlank

private theorem blank_prefix_eq (wordPrefix first second : List WorkSymbol)
    (hFirst : BlankExterior first) (hSecond : BlankExterior second) (index : Nat) :
    WorkTape.blankCellAt (wordPrefix ++ first) index = WorkTape.blankCellAt (wordPrefix ++ second) index := by
  induction wordPrefix generalizing index with
  | nil => exact (hFirst index).trans (hSecond index).symm
  | cons symbol rest ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index

/-- Cleared finite blanks can differ in length without changing the recovered cursor. -/
theorem final_blankEquivalent (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside expectedOutside : List WorkSymbol)
    (hBlank : BlankExterior outside) (hExpected : BlankExterior expectedOutside) :
    WorkTape.BlankEquivalent (finalConfiguration beforeCount before value after head tail outside).tape
      (BuilderRegisterAccess.sourceTape head tail (registerWord before) expectedOutside) := by
  refine ⟨rfl, ?_, fun _ => rfl⟩
  intro index
  have h := blank_prefix_eq (leftMarker :: (registerWord before ++ [scratchEndSymbol]))
    (clearedOutside value after outside) expectedOutside
    (clearedOutside_blank value after outside hBlank) hExpected index
  simpa only [finalConfiguration, BuilderRegisterAccess.sourceTape, List.cons_append,
    List.append_assoc, List.nil_append] using h

theorem workSteps_le (before : List Nat) (value : Nat) (after : List Nat) (bound : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length ≤ bound) :
    workSteps before value after ≤ 5 * bound + 10 := by
  have hErase := BuilderRegisterRootErase.workSteps_le before value after bound hSpan
  have hBefore : (registerWord before).length ≤ bound := by
    simp only [registerWord_append, List.length_append] at hSpan
    omega
  unfold workSteps
  omega

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6) (.add (.mul (.constant 5) bound) (.constant 10))

theorem source_polynomial_bounds (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length + outside.length ≤ bound.eval input) :
    storedCells (finalConfiguration beforeCount before value after head tail outside).tape ≤
        tail.length + 2 + bound.eval input ∧
      6 * workSteps before value after ≤ (rawTimePolynomial bound).eval input := by
  have hTime := workSteps_le before value after (bound.eval input) (by omega)
  constructor
  · rw [final_storedCells]
    simp only [storedCells, initialConfiguration, workStartConfiguration, endTape,
      List.length_append, List.length_reverse, List.length_cons]
    omega
  · simp only [rawTimePolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

/-- The preserved root count is fixed by the verifier's initialization syntax. -/
def rootCount {language : Language} (verifier : PolynomialTimeVerifier language) : Nat :=
  nodeCount (BuilderFullScheduleCursorController.bodySlotCountPolynomial verifier) +
    nodeCount (BuilderDimensionRegisters.widthPolynomial verifier) + 3

theorem retainedValues_length {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    (BuilderOperandRegisters.retainedValues problem index remaining).length = rootCount problem.verifier := by
  simp only [BuilderOperandRegisters.retainedValues, BuilderOperandRegisters.prefixValues,
    List.length_append, registerValues_length, List.length_cons, List.length_nil, rootCount]
  omega

def recoveredCursorTape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (outside : List WorkSymbol) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input
    (BuilderBalancedCursor.outside (BuilderCursorSource.registerPrefix problem) index remaining outside) output

private theorem recovered_cursor_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (outside : List WorkSymbol) :
    recoveredCursorTape problem index remaining output outside =
      BuilderRegisterAccess.sourceTape (BuilderTokenAppender.workspaceTape problem.input [] output).head
        (BuilderTokenAppender.workspaceTape problem.input [] output).right
        (registerWord (BuilderOperandRegisters.retainedValues problem index remaining)) outside := by
  unfold recoveredCursorTape BuilderBalancedCursor.outside
  rw [BuilderOperandRegisters.cursorWord_values]
  cases problem.input <;> rfl

theorem recovered_original_cursor {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    recoveredCursorTape problem index remaining output (BuilderCursorSource.preservedTail problem) =
      BuilderCursorSource.cursorTape problem index remaining output :=
  (BuilderCursorSource.cursorTape_eq_workspace problem index remaining output).symm

/-- Specialization to the real source root; no input-dependent root count is supplied. -/
theorem source_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (value : Nat) (after : List Nat) (outside : List WorkSymbol) :
    workRunExact? (machine (rootCount problem.verifier))
      (workSteps (BuilderOperandRegisters.retainedValues problem index remaining) value after)
      (workStartConfiguration (machine (rootCount problem.verifier))
        (endTape (BuilderOperandRegisters.retainedValues problem index remaining ++ [value] ++ after)
          (BuilderDividerOperands.inside problem.input output) outside)) =
      some {
        state := (machine (rootCount problem.verifier)).acceptState
        tape := recoveredCursorTape problem index remaining output (clearedOutside value after outside)
      } := by
  rw [recovered_cursor_layout]
  exact workRunExact (rootCount problem.verifier)
    (BuilderOperandRegisters.retainedValues problem index remaining) value after
    (BuilderTokenAppender.workspaceTape problem.input [] output).head
    (BuilderTokenAppender.workspaceTape problem.input [] output).right outside
    (retainedValues_length problem index remaining)

theorem rules_pairwise_query_distinct (beforeCount : Nat) :
    (machine beforeCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderRegisterRootErase.rules_pairwise_query_distinct beforeCount) return_control.1
    (BuilderRegisterRootErase.noRuleAtAccept beforeCount)

theorem noRuleAtAccept (beforeCount : Nat) : WorkMachineChain.NoRuleAtAccept (machine beforeCount) :=
  WorkMachineChain.noRuleAtAccept _ _ return_control.2.1

theorem noRuleAtReject (beforeCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine beforeCount) (machine beforeCount).rejectState :=
  WorkMachineChain.noRuleAtAccept (BuilderRegisterRootErase.machine beforeCount)
    {returnMachine with acceptState := returnMachine.rejectState} return_control.2.2.1

theorem acceptState_ne_rejectState (beforeCount : Nat) :
    (machine beforeCount).acceptState ≠ (machine beforeCount).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ return_control.2.2.2

end PNP.Concrete.CookLevin.BuilderCursorRecovery

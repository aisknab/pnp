/-
Copyright (c) 2026 PNP Labs.

Literal removal of a fixed number of disposable unary registers. Every cell
is erased by the finite machine; retained registers and arbitrary interior
and exterior data are preserved. Cleared cells remain explicit blanks.
This restores the source frame after the preservation-position comparison.
-/

import PNP.Concrete.CookLevinBuilderDividerOperands
import PNP.Concrete.WorkMachineProgramPath

namespace PNP.Concrete.CookLevin.BuilderRegisterErase

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

/-- Three literal transitions; no value determines control. -/
def oneMachine : WorkMachine :=
  { rules :=
      [{ sourceState := 0, readSymbol := scratchEndSymbol, targetState := 1,
         writeSymbol := .blank, move := .right },
       { sourceState := 1, readSymbol := unitSymbol, targetState := 1,
         writeSymbol := .blank, move := .right },
       { sourceState := 1, readSymbol := separatorSymbol, targetState := 2,
         writeSymbol := scratchEndSymbol, move := .stay }]
    startState := 0
    acceptState := 2
    rejectState := 3 }

theorem one_rules_length : oneMachine.rules.length = 3 := rfl

theorem one_rules_pairwise_query_distinct :
    oneMachine.rules.Pairwise WorkMachineChain.QueryDistinct := by
  unfold WorkMachineChain.QueryDistinct
  decide

theorem one_noRuleAtAccept : WorkMachineChain.NoRuleAtAccept oneMachine := by
  intro rule hRule
  change rule.sourceState ≠ 2
  change rule ∈ oneMachine.rules at hRule
  decide +revert

theorem one_noRuleAtReject :
    WorkMachineProgramGraph.NoRuleAt oneMachine oneMachine.rejectState := by
  intro rule hRule
  change rule.sourceState ≠ 3
  change rule ∈ oneMachine.rules at hRule
  decide +revert

theorem one_acceptState_ne_rejectState : oneMachine.acceptState ≠ oneMachine.rejectState := by decide

private def scanTape (remaining cleared : Nat) (sourceTail outside : List WorkSymbol) : WorkTape :=
  match remaining with
  | 0 =>
      { left := List.replicate cleared .blank ++ outside
        head := separatorSymbol
        right := sourceTail }
  | remaining + 1 =>
      { left := List.replicate cleared .blank ++ outside
        head := unitSymbol
        right := List.replicate remaining unitSymbol ++ separatorSymbol :: sourceTail }

private theorem scan_run (remaining cleared : Nat) (sourceTail outside : List WorkSymbol) :
    workRunExact? oneMachine (remaining + 1)
      { state := 1, tape := scanTape remaining cleared sourceTail outside } =
      some {
        state := oneMachine.acceptState
        tape := { left := List.replicate (cleared + remaining) .blank ++ outside
                  head := scratchEndSymbol
                  right := sourceTail } } := by
  induction remaining generalizing cleared with
  | zero => rfl
  | succ remaining ih =>
      have hStep : workStep? oneMachine
          { state := 1, tape := scanTape (remaining + 1) cleared sourceTail outside } =
          some { state := 1, tape := scanTape remaining (cleared + 1) sourceTail outside } := by
        cases remaining <;> rfl
      rw [show remaining + 1 + 1 = (remaining + 1) + 1 from rfl, workRunExact?, hStep]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (cleared + 1)

/-- Erasure retains the exact exterior as a suffix, not an empty-tail fiction. -/
theorem one_workRunExact (older : List Nat) (value : Nat) (inside outside : List WorkSymbol) :
    workRunExact? oneMachine (value + 2)
      (workStartConfiguration oneMachine (endTape (older ++ [value]) inside outside)) =
      some {
        state := oneMachine.acceptState
        tape := endTape older inside (List.replicate (value + 1) .blank ++ outside) } := by
  have hTape : endTape (older ++ [value]) inside outside =
      { left := outside, head := scratchEndSymbol,
        right := List.replicate value unitSymbol ++ separatorSymbol ::
          ((registerWord older).reverse ++ inside) } := by
    simp only [endTape, registerWord_append, registerWord, List.append_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_replicate,
      List.nil_append, List.cons_append, List.append_assoc]
  rw [hTape]
  have hStep : workStep? oneMachine
      (workStartConfiguration oneMachine
        { left := outside, head := scratchEndSymbol,
          right := List.replicate value unitSymbol ++ separatorSymbol ::
            ((registerWord older).reverse ++ inside) }) =
      some { state := 1, tape := scanTape value 1 ((registerWord older).reverse ++ inside) outside } := by
    cases value <;> rfl
  rw [show value + 2 = (value + 1) + 1 from rfl, workRunExact?, hStep]
  simpa only [endTape, Nat.add_comm] using
    scan_run value 1 ((registerWord older).reverse ++ inside) outside

theorem one_run_compile_exact (older : List Nat) (value : Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine oneMachine) (6 * (value + 2))
      (encodeWorkConfiguration (workStartConfiguration oneMachine
        (endTape (older ++ [value]) inside outside))) =
      encodeWorkConfiguration {
        state := oneMachine.acceptState
        tape := endTape older inside (List.replicate (value + 1) .blank ++ outside) } :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (one_workRunExact older value inside outside)

def doneMachine : WorkMachine :=
  { rules := [], startState := 0, acceptState := 0, rejectState := 1 }

/-- The count is structural; register magnitudes never select a program. -/
def machine : Nat → WorkMachine
  | 0 => doneMachine
  | count + 1 => WorkMachineChain.machine (machine count) oneMachine

def clearedSpan (values : List Nat) : Nat := (registerWord values).length

def workSteps (values : List Nat) : Nat := clearedSpan values + 2 * values.length

def initialConfiguration (count : Nat) (older values : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine count) (endTape (older ++ values) inside outside)

def finalConfiguration (count : Nat) (older values : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  { state := (machine count).acceptState
    tape := endTape older inside (List.replicate (clearedSpan values) .blank ++ outside) }

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

private theorem replicate_join (left right : Nat) (symbol : WorkSymbol) :
    List.replicate left symbol ++ List.replicate right symbol = List.replicate (left + right) symbol := by
  induction left with
  | zero => simp only [List.replicate_zero, List.nil_append, Nat.zero_add]
  | succ left ih =>
      simp only [List.replicate_succ, List.cons_append, Nat.succ_add, ih]

private theorem list_run (values older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine values.length) (workSteps values)
      (initialConfiguration values.length older values inside outside) =
      some (finalConfiguration values.length older values inside outside) := by
  induction values generalizing older with
  | nil =>
      simp only [machine, workSteps, clearedSpan, registerWord, List.length_nil,
        Nat.mul_zero, Nat.zero_add, initialConfiguration, finalConfiguration,
        List.append_nil, List.replicate_zero, List.nil_append, doneMachine,
        workStartConfiguration, workRunExact?]
  | cons value rest ih =>
      have hRest := ih (older ++ [value])
      have hOne := one_workRunExact older value inside (List.replicate (clearedSpan rest) .blank ++ outside)
      simp only [initialConfiguration, finalConfiguration, List.append_assoc,
        List.cons_append, List.nil_append] at hRest
      have h := chain_run (machine rest.length) oneMachine (workSteps rest) (value + 2)
        _ _ _ hRest hOne
      have hSteps : workSteps (value :: rest) = workSteps rest + 1 + (value + 2) := by
        simp only [workSteps, clearedSpan, registerWord, List.length_cons, List.length_append,
          List.length_replicate]
        omega
      have hBlanks : List.replicate (value + 1) WorkSymbol.blank ++
            (List.replicate (clearedSpan rest) .blank ++ outside) =
          List.replicate (clearedSpan (value :: rest)) .blank ++ outside := by
        have hSpan : value + 1 + clearedSpan rest = clearedSpan (value :: rest) := by
          simp only [clearedSpan, registerWord, List.length_cons, List.length_append, List.length_replicate]
          omega
        rw [← List.append_assoc, replicate_join, hSpan]
      simpa only [initialConfiguration, finalConfiguration, List.length_cons, machine,
        hSteps, hBlanks] using h

theorem workRunExact (count : Nat) (older values : List Nat) (inside outside : List WorkSymbol)
    (hCount : values.length = count) :
    workRunExact? (machine count) (workSteps values)
      (initialConfiguration count older values inside outside) =
      some (finalConfiguration count older values inside outside) := by
  subst count
  exact list_run values older inside outside

theorem run_compile_exact (count : Nat) (older values : List Nat) (inside outside : List WorkSymbol)
    (hCount : values.length = count) :
    run (compileWorkMachine (machine count)) (6 * workSteps values)
      (encodeWorkConfiguration (initialConfiguration count older values inside outside)) =
      encodeWorkConfiguration (finalConfiguration count older values inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact count older values inside outside hCount)

theorem final_inside_preserved (count : Nat) (older values : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration count older values inside outside).tape.right = (registerWord older).reverse ++ inside := rfl

theorem final_outside_preserved (count : Nat) (older values : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration count older values inside outside).tape.left =
      List.replicate (clearedSpan values) .blank ++ outside := rfl

theorem length_le_clearedSpan (values : List Nat) : values.length ≤ clearedSpan values := by
  induction values with
  | nil => exact Nat.le_refl 0
  | cons value rest ih =>
      simp only [clearedSpan, registerWord, List.length_cons, List.length_append,
        List.length_replicate] at ih ⊢
      omega

theorem workSteps_le (values : List Nat) : workSteps values ≤ 3 * clearedSpan values := by
  have hLength := length_le_clearedSpan values
  unfold workSteps
  omega

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial := .mul (.constant 18) bound

theorem source_polynomial_bound (bound : NatPolynomial) (inputLength : Nat) (values : List Nat)
    (hSpan : clearedSpan values ≤ bound.eval inputLength) :
    6 * workSteps values ≤ (rawTimePolynomial bound).eval inputLength := by
  have hSteps := workSteps_le values
  simp only [rawTimePolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
  omega

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem chain_noRuleAtReject (first second : WorkMachine)
    (hSecond : WorkMachineProgramGraph.NoRuleAt second second.rejectState) :
    WorkMachineProgramGraph.NoRuleAt (WorkMachineChain.machine first second)
      (WorkMachineChain.machine first second).rejectState :=
  WorkMachineChain.noRuleAtAccept first { second with acceptState := second.rejectState } hSecond

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct first second hFirst.1 hSecond.1 hFirst.2.1,
    WorkMachineChain.noRuleAtAccept first second hSecond.2.1,
    chain_noRuleAtReject first second hSecond.2.2.1,
    WorkMachineChain.machine_acceptState_ne_rejectState first second hSecond.2.2.2⟩

private theorem good (count : Nat) : Good (machine count) := by
  induction count with
  | zero =>
      refine ⟨List.Pairwise.nil, ?_, ?_, ?_⟩
      · intro rule hRule; cases hRule
      · intro rule hRule; cases hRule
      · decide
  | succ count ih =>
      exact chain_good (machine count) oneMachine ih
        ⟨one_rules_pairwise_query_distinct, one_noRuleAtAccept, one_noRuleAtReject, one_acceptState_ne_rejectState⟩

theorem rules_pairwise_query_distinct (count : Nat) :
    (machine count).rules.Pairwise WorkMachineChain.QueryDistinct := (good count).1

theorem noRuleAtAccept (count : Nat) : WorkMachineChain.NoRuleAtAccept (machine count) := (good count).2.1

theorem noRuleAtReject (count : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine count) (machine count).rejectState := (good count).2.2.1

theorem acceptState_ne_rejectState (count : Nat) : (machine count).acceptState ≠ (machine count).rejectState :=
  (good count).2.2.2

end PNP.Concrete.CookLevin.BuilderRegisterErase

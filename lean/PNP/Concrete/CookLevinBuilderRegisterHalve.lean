/-
Copyright (c) 2026 PNP Labs.

Fixed physical division by two at the builder's fresh outer frontier.
The actual newest register supplies the dividend; fixed packing supplies
the positive divisor; existing division and restoration produce the result.
Older registers and arbitrary inside/source/output data are preserved.
The row-loop frontier handoff is proved explicitly. No theorem here
transports the divider over an arbitrary nonempty outer tail.
-/

import PNP.Concrete.CookLevinBuilderInitialRowLoop
import PNP.Concrete.CookLevinBuilderDividerCoordinateRegisters

namespace PNP.Concrete.CookLevin.BuilderRegisterHalve

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

private theorem pair_span (first second : Nat) :
    (registerWord [first, second]).length = first + second + 2 := by
  simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  omega

/-- The row loop preserves the actual builder frontier, including exhausted and zero-width rows. -/
theorem row_loop_frontier (remaining length width coordinate : Nat) :
    BuilderInitialRowLoop.finishOutside remaining length width coordinate [] = [] := by
  induction remaining generalizing length width coordinate with
  | zero => rfl
  | succ remaining ih =>
      have hPrepared : BuilderInitialRowLoop.preparedOutside width coordinate [] = [] := by
        unfold BuilderInitialRowLoop.preparedOutside
        rw [pair_span]
        exact List.drop_eq_nil_iff.mpr (by
          simp only [List.length_cons, List.length_nil]
          omega)
      have hAttempt : BuilderInitialRowLoop.attemptOutside width coordinate [] = [] := by
        simp only [BuilderInitialRowLoop.attemptOutside, hPrepared, List.drop_nil]
      have hContinued : BuilderInitialRowLoop.continuedOutside length width coordinate remaining [] = [] := by
        simp only [BuilderInitialRowLoop.continuedOutside, hAttempt, List.drop_nil]
      by_cases hLess : coordinate < width
      · simp only [BuilderInitialRowLoop.finishOutside, if_pos hLess, hAttempt]
      · simp only [BuilderInitialRowLoop.finishOutside, if_neg hLess, hContinued, ih]

theorem row_loop_final_frontier (remaining length width coordinate : Nat) (older : List Nat)
    (inside : List WorkSymbol) :
    (BuilderInitialRowLoop.finalConfiguration remaining length width coordinate older inside []).tape.left = [] := by
  rw [BuilderInitialRowLoop.final_tape, row_loop_frontier]
  rfl

def prepareFields : List (BuilderRegisterPack.Field 1) :=
  [.constant 0, .constant 0, .argument ⟨0, by decide⟩, .constant 2]
def prepareEnvironment (value : Nat) (_ : Fin 1) : Nat := value

theorem prepareEnvironment_ofFn (value : Nat) : List.ofFn (prepareEnvironment value) = [value] := rfl
theorem prepare_values (value : Nat) :
    BuilderRegisterPack.values prepareFields (prepareEnvironment value) = [0, 0, value, 2] := rfl

/-- Describes the result of the existing divider; it is not an input certificate. -/
def view (value : Nat) : BuilderDividerCoordinateRegisters.RestoreView :=
  {quotient := value / 2, width := 2, remainder := value % 2,
   consumed := (value / 2) * 2, sidecarCount := 0}

def restoredValues (value : Nat) : List Nat := BuilderDividerCoordinateRegisters.restoredValues (view value)
def resultEnvironment (value : Nat) (index : Fin 6) : Nat :=
  match index.val with
  | 0 | 1 => 0
  | 2 => (value / 2) * 2
  | 3 => value % 2
  | 4 => 2
  | _ => value / 2
def resultFields : List (BuilderRegisterPack.Field 6) :=
  [.argument ⟨5, by decide⟩, .argument ⟨3, by decide⟩]

theorem resultEnvironment_ofFn (value : Nat) :
    List.ofFn (resultEnvironment value) = restoredValues value := rfl
theorem result_values (value : Nat) :
    BuilderRegisterPack.values resultFields (resultEnvironment value) = [value / 2, value % 2] := rfl

def outputValues (value : Nat) : List Nat :=
  [value] ++ restoredValues value ++ [value / 2, value % 2]

theorem outputValues_length (value : Nat) : (outputValues value).length = 9 := rfl
theorem output_quotient (value : Nat) : (outputValues value)[7]? = some (value / 2) := rfl
theorem output_remainder (value : Nat) : (outputValues value)[8]? = some (value % 2) := rfl

def tailMachine : WorkMachine :=
  WorkMachineChain.machine BuilderDividerCoordinateRegisters.machine
    (BuilderRegisterPack.machine resultFields 0)
def dividedMachine : WorkMachine :=
  WorkMachineChain.machine BuilderClauseDividerExecution.divisionMachine tailMachine

/-- One fixed finite program; no runtime value determines its control. -/
def machine : WorkMachine :=
  WorkMachineChain.machine (BuilderRegisterPack.machine prepareFields 0) dividedMachine

def prepareSteps (value : Nat) : Nat := BuilderRegisterPack.workSteps prepareFields (prepareEnvironment value) []
def resultSteps (value : Nat) : Nat := BuilderRegisterPack.workSteps resultFields (resultEnvironment value) []
def workSteps (value : Nat) : Nat :=
  prepareSteps value + 1 + (BuilderClauseDividerExecution.divisionSteps 0 value 2 + 1 +
    (BuilderDividerCoordinateRegisters.workSteps (view value) + 1 + resultSteps value))

def initialConfiguration (value : Nat) (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ [value]) inside [])
def finalConfiguration (value : Nat) (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  {state := machine.acceptState, tape := endTape (older ++ outputValues value) inside []}

private theorem chain_run (first second : WorkMachine) (n m : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : config.state = state) (hTape : config.tape = tape) :
    config = {state := state, tape := tape} := by
  cases config with
  | mk currentState currentTape =>
      change currentState = state at hState
      change currentTape = tape at hTape
      subst currentState
      subst currentTape
      rfl

theorem division_restore_handoff (value : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (BuilderClauseDividerExecution.divisionFinal 0 value 2 (older ++ [value]) inside).tape =
      BuilderDividerCoordinateRegisters.inputTape (view value)
        ((registerWord (older ++ [value])).reverse ++ inside) [] := by
  rw [BuilderClauseDividerExecution.division_final_tape_layout]
  simp only [BuilderDividerCoordinateRegisters.inputTape, view, List.append_nil]

private theorem restoration_run (value : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? BuilderDividerCoordinateRegisters.machine
      (BuilderDividerCoordinateRegisters.workSteps (view value))
      (workStartConfiguration BuilderDividerCoordinateRegisters.machine
        (BuilderDividerCoordinateRegisters.inputTape (view value)
          ((registerWord (older ++ [value])).reverse ++ inside) [])) =
      some {
        state := BuilderDividerCoordinateRegisters.machine.acceptState
        tape := endTape (older ++ [value] ++ restoredValues value) inside [] } := by
  have h := BuilderDividerCoordinateRegisters.workRunExact (view value)
    ((registerWord (older ++ [value])).reverse ++ inside) [] rfl rfl
  simpa only [BuilderDividerCoordinateRegisters.initialConfiguration,
    BuilderDividerCoordinateRegisters.finalConfiguration, restoredValues, endTape,
    List.drop_nil, registerWord_append, List.reverse_append, List.append_assoc] using h

theorem workRunExact (value : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps value) (initialConfiguration value older inside) =
      some (finalConfiguration value older inside) := by
  have hPrep := BuilderRegisterPack.workRunExact prepareFields 0 older
    (prepareEnvironment value) [] inside [] rfl
  simp only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    prepareEnvironment_ofFn, prepare_values, List.append_nil, List.drop_nil] at hPrep
  have hDivision := BuilderClauseDividerExecution.division_workRunExact 0 value 2
    (older ++ [value]) inside (by decide)
  have hDivisionState :
      (BuilderClauseDividerExecution.divisionFinal 0 value 2 (older ++ [value]) inside).state =
        BuilderClauseDividerExecution.divisionMachine.acceptState := rfl
  rw [configuration_eq_of_fields _ _ _ hDivisionState (division_restore_handoff value older inside)] at hDivision
  have hRestore := restoration_run value older inside
  have hPack := BuilderRegisterPack.workRunExact resultFields 0 (older ++ [value])
    (resultEnvironment value) [] inside [] rfl
  simp only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    resultEnvironment_ofFn, result_values, List.append_nil, List.drop_nil] at hPack
  have hTail := chain_run _ _ _ _ _ _ _ hRestore hPack
  have hMiddle := chain_run _ _ _ _ _ _ _ hDivision hTail
  have hAll := chain_run _ _ _ _ _ _ _ hPrep hMiddle
  simpa only [machine, dividedMachine, tailMachine, workSteps, prepareSteps, resultSteps,
    initialConfiguration, finalConfiguration, outputValues, List.append_assoc] using hAll

theorem run_compile_exact (value : Nat) (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps value)
      (encodeWorkConfiguration (initialConfiguration value older inside)) =
      encodeWorkConfiguration (finalConfiguration value older inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact value older inside)

theorem final_tape (value : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration value older inside).tape =
      endTape (older ++ [value] ++ restoredValues value ++ [value / 2, value % 2]) inside [] := by
  simp only [finalConfiguration, outputValues, List.append_assoc]

theorem final_frontier (value : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration value older inside).tape.left = [] := rfl

theorem quotient_remainder_reconstruct (value : Nat) : (value / 2) * 2 + value % 2 = value :=
  BuilderPostHeaderRawDivider.quotient_remainder_reconstruct value 2
theorem remainder_lt_two (value : Nat) : value % 2 < 2 := Nat.mod_lt value (by decide)

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState
private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
    WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
    WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
    WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩

private theorem pack_good {arity : Nat} (fields : List (BuilderRegisterPack.Field arity)) :
    Good (BuilderRegisterPack.machine fields 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct fields 0, BuilderRegisterPack.noRuleAtAccept fields 0,
    BuilderRegisterPack.noRuleAtReject fields 0, BuilderRegisterPack.acceptState_ne_rejectState fields 0⟩
private theorem division_good : Good BuilderClauseDividerExecution.divisionMachine := by
  refine ⟨BuilderClauseDividerExecution.division_rules_pairwise_query_distinct,
    BuilderClauseDividerExecution.division_noRuleAtAccept, ?_,
    BuilderClauseDividerExecution.division_acceptState_ne_rejectState⟩
  intro rule hMem
  decide +revert
private theorem restore_good : Good BuilderDividerCoordinateRegisters.machine := by
  refine ⟨BuilderDividerCoordinateRegisters.rules_pairwise_query_distinct,
    BuilderDividerCoordinateRegisters.noRuleAtAccept, ?_,
    BuilderDividerCoordinateRegisters.acceptState_ne_rejectState⟩
  intro rule hMem
  decide +revert
private theorem good : Good machine :=
  chain_good _ _ (pack_good prepareFields)
    (chain_good _ _ division_good (chain_good _ _ restore_good (pack_good resultFields)))

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := good.1
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := good.2.1
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := good.2.2.1
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := good.2.2.2

private theorem restored_span (value : Nat) :
    (registerWord (restoredValues value)).length = value + value / 2 + 8 := by
  have h := quotient_remainder_reconstruct value
  simp only [restoredValues, BuilderDividerCoordinateRegisters.restoredValues, view,
    registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  omega

theorem output_span (value : Nat) : (registerWord (outputValues value)).length = 3 * value + 11 := by
  have h := quotient_remainder_reconstruct value
  simp only [outputValues, registerWord_append, List.length_append, restored_span, pair_span]
  simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  omega

def restoredSpanPolynomial (bound : NatPolynomial) : NatPolynomial := .add (.mul (.constant 3) bound) (.constant 9)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial := .add (.mul (.constant 3) bound) (.constant 8)
def divisionWorkPolynomial (bound : NatPolynomial) : NatPolynomial :=
  let enlarged := NatPolynomial.add bound (.constant 2)
  let twice := NatPolynomial.add (.mul (.constant 2) enlarged) (.constant 1)
  .add (.add (.mul (.constant 4) enlarged) (.constant 8)) (.mul (.mul (.constant 20) twice) twice)
def restoreWorkPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 11) bound) (.constant 27)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add
    (.add (BuilderRegisterPack.rawTimePolynomial prepareFields bound)
      (.mul (.constant 6) (divisionWorkPolynomial bound)))
    (.add (.mul (.constant 6) (restoreWorkPolynomial bound))
      (BuilderRegisterPack.rawTimePolynomial resultFields (restoredSpanPolynomial bound)))) (.constant 18)

theorem source_polynomial_bounds (value : Nat) (older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [value])).length ≤ bound.eval inputLength) :
    (registerWord (older ++ outputValues value)).length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps value ≤ (rawTimePolynomial bound).eval inputLength := by
  have hInitial := hSpan
  rw [registerWord_append, List.length_append] at hInitial
  simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hInitial
  have hValue : value ≤ bound.eval inputLength := by omega
  have hQ : value / 2 ≤ value := Nat.div_le_self value 2
  have hR : value % 2 ≤ value := Nat.mod_le value 2
  have hReconstruct := quotient_remainder_reconstruct value
  have hPrep := (BuilderRegisterPack.source_polynomial_bounds prepareFields bound inputLength
    older (prepareEnvironment value) [] (by
      simpa only [prepareEnvironment_ofFn, List.append_nil] using hSpan)).2
  have hDivision := BuilderClauseDividerExecution.divisionSteps_le 0 value 2
    (bound.eval inputLength + 2) (by omega) (by omega) (by omega) (by decide)
  have hRestore : BuilderDividerCoordinateRegisters.workSteps (view value) ≤
      (restoreWorkPolynomial bound).eval inputLength := by
    simp only [BuilderDividerCoordinateRegisters.workSteps, view, restoreWorkPolynomial,
      NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega
  have hRestoredSpan :
      (registerWord ((older ++ [value]) ++ List.ofFn (resultEnvironment value) ++ [])).length ≤
        (restoredSpanPolynomial bound).eval inputLength := by
    rw [List.append_nil, resultEnvironment_ofFn, registerWord_append, List.length_append, restored_span]
    rw [registerWord_append, List.length_append]
    simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
      restoredSpanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega
  have hPack := (BuilderRegisterPack.source_polynomial_bounds resultFields (restoredSpanPolynomial bound)
    inputLength (older ++ [value]) (resultEnvironment value) [] hRestoredSpan).2
  constructor
  · rw [registerWord_append, List.length_append, output_span]
    simp only [spanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant,
      registerWord_length]
    omega
  · simp only [workSteps, rawTimePolynomial, divisionWorkPolynomial, restoreWorkPolynomial,
      NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant,
      prepareSteps, resultSteps] at hPrep hPack hRestore ⊢
    omega

end PNP.Concrete.CookLevin.BuilderRegisterHalve

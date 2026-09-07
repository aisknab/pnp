/-
Copyright (c) 2026 PNP Labs.

Register-preserving division for the canonical region-local rectangle decoders.
One fixed-offset program allocates, copies, divides and restores both results.
The divisor is data on the tape, not part of an input-generated control table.

Region entry linkage, complete local constraints, input reads, occupancy,
emission and the complete formula-builder loop remain separate obligations.
-/

import PNP.Concrete.CookLevinBuilderConstraintRegionSource

namespace PNP.Concrete.CookLevin.BuilderRegionCoordinateDivision

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRegionComparisonOperands (copy_workRunExact)
open BuilderClauseDividerExecution (divisionMachine divisionSteps divisionInitial divisionFinal)
open BuilderDividerCoordinateRegisters (RestoreView)

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

private theorem configuration_eq (configuration : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : configuration.state = state) (hTape : configuration.tape = tape) :
    configuration = { state := state, tape := tape } := by
  cases configuration
  cases hState
  cases hTape
  rfl

def inputValues (older newer : List Nat) (coordinate width : Nat) : List Nat :=
  older ++ [width] ++ newer ++ [coordinate]

def zerosMachine : WorkMachine :=
  WorkMachineChain.machine BuilderDividerOperands.Delimiter.machine BuilderDividerOperands.Delimiter.machine

theorem zeros_workRunExact (values : List Nat) (workspace : List WorkSymbol) :
    workRunExact? zerosMachine 5 (workStartConfiguration zerosMachine (endTape values workspace [])) =
      some { state := zerosMachine.acceptState, tape := endTape (values ++ [0, 0]) workspace [] } := by
  have hFirst := BuilderDividerOperands.Delimiter.workRunExact values workspace []
  have hSecond := BuilderDividerOperands.Delimiter.workRunExact (values ++ [0]) workspace []
  simp only [List.drop_nil] at hFirst hSecond
  have h := chain_run BuilderDividerOperands.Delimiter.machine BuilderDividerOperands.Delimiter.machine
    2 2 _ _ _ hFirst hSecond
  simpa only [zerosMachine, List.append_assoc, List.cons_append, List.nil_append] using h

def copyMachine (offset : Nat) : WorkMachine :=
  WorkMachineChain.machine (RegisterCopy.machine 2) (RegisterCopy.machine (offset + 4))

def copySteps (newer : List Nat) (coordinate width : Nat) : Nat :=
  RegisterCopy.steps [0, 0] coordinate + 1 +
    RegisterCopy.steps (newer ++ [coordinate, 0, 0, coordinate]) width

theorem copy_workRun (offset : Nat) (older newer : List Nat) (coordinate width : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (copyMachine offset) (copySteps newer coordinate width)
      (workStartConfiguration (copyMachine offset)
        (endTape (inputValues older newer coordinate width ++ [0, 0]) workspace [])) =
      some {
        state := (copyMachine offset).acceptState
        tape := endTape (inputValues older newer coordinate width ++ [0, 0, coordinate, width]) workspace []
      } := by
  have hCoordinate := copy_workRunExact 2 (older ++ [width] ++ newer) [0, 0] coordinate workspace [] rfl
  have hWidthLength : (newer ++ [coordinate, 0, 0, coordinate]).length = offset + 4 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hLength]
  have hWidth := copy_workRunExact (offset + 4) older (newer ++ [coordinate, 0, 0, coordinate])
    width workspace [] hWidthLength
  simp only [List.drop_nil] at hCoordinate hWidth
  have h := chain_run (RegisterCopy.machine 2) (RegisterCopy.machine (offset + 4))
    (RegisterCopy.steps [0, 0] coordinate)
    (RegisterCopy.steps (newer ++ [coordinate, 0, 0, coordinate]) width) _ _ _ hCoordinate
    (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hWidth)
  simpa only [copyMachine, copySteps, inputValues, List.append_assoc,
    List.cons_append, List.nil_append] using h

def prepareMachine (offset : Nat) : WorkMachine :=
  WorkMachineChain.machine zerosMachine (copyMachine offset)

def prepareSteps (newer : List Nat) (coordinate width : Nat) : Nat :=
  5 + 1 + copySteps newer coordinate width

theorem prepare_workRunExact (offset : Nat) (older newer : List Nat) (coordinate width : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (prepareMachine offset) (prepareSteps newer coordinate width)
      (workStartConfiguration (prepareMachine offset)
        (endTape (inputValues older newer coordinate width) workspace [])) =
      some {
        state := (prepareMachine offset).acceptState
        tape := endTape (inputValues older newer coordinate width ++ [0, 0, coordinate, width]) workspace []
      } :=
  chain_run zerosMachine (copyMachine offset) 5 (copySteps newer coordinate width) _ _ _
    (zeros_workRunExact _ workspace) (copy_workRun offset older newer coordinate width workspace hLength)

def resultView (coordinate width : Nat) : RestoreView :=
  { quotient := coordinate / width
    width := width
    remainder := coordinate % width
    consumed := (coordinate / width) * width
    sidecarCount := 0 }

def scratchValues (coordinate width : Nat) : List Nat :=
  [0, 0, (coordinate / width) * width, coordinate % width, width, coordinate / width]

def divideMachine : WorkMachine :=
  WorkMachineChain.machine divisionMachine BuilderDividerCoordinateRegisters.machine

def divideSteps (coordinate width : Nat) : Nat :=
  divisionSteps 0 coordinate width + 1 + BuilderDividerCoordinateRegisters.workSteps (resultView coordinate width)

theorem divide_workRunExact (values : List Nat) (coordinate width : Nat)
    (workspace : List WorkSymbol) (hPositive : 0 < width) :
    workRunExact? divideMachine (divideSteps coordinate width)
      (workStartConfiguration divideMachine (endTape (values ++ [0, 0, coordinate, width]) workspace [])) =
      some {
        state := divideMachine.acceptState
        tape := endTape (values ++ scratchValues coordinate width) workspace []
      } := by
  have hDivide := BuilderClauseDividerExecution.division_workRunExact 0 coordinate width values workspace hPositive
  have hRestore := BuilderDividerCoordinateRegisters.workRunExact (resultView coordinate width)
    ((registerWord values).reverse ++ workspace) [] rfl rfl
  have hTape : (divisionFinal 0 coordinate width values workspace).tape =
      BuilderDividerCoordinateRegisters.inputTape (resultView coordinate width)
        ((registerWord values).reverse ++ workspace) [] := by
    rw [BuilderClauseDividerExecution.division_final_tape_layout]
    simp only [BuilderDividerCoordinateRegisters.inputTape, resultView, List.append_nil]
  have hMiddle : divisionFinal 0 coordinate width values workspace =
      { state := divisionMachine.acceptState,
        tape := BuilderDividerCoordinateRegisters.inputTape (resultView coordinate width)
          ((registerWord values).reverse ++ workspace) [] } := by
    exact configuration_eq _ _ _ rfl hTape
  rw [hMiddle] at hDivide
  have h := chain_run divisionMachine BuilderDividerCoordinateRegisters.machine
    (divisionSteps 0 coordinate width)
    (BuilderDividerCoordinateRegisters.workSteps (resultView coordinate width)) _ _ _ hDivide hRestore
  simpa only [divideMachine, divideSteps, BuilderDividerCoordinateRegisters.finalConfiguration,
    BuilderDividerCoordinateRegisters.restoredValues, resultView, scratchValues, endTape,
    registerWord_append, List.reverse_append, List.drop_nil, List.append_assoc] using h

def machine (offset : Nat) : WorkMachine :=
  WorkMachineChain.machine (prepareMachine offset) divideMachine

def workSteps (newer : List Nat) (coordinate width : Nat) : Nat :=
  prepareSteps newer coordinate width + 1 + divideSteps coordinate width

def finalValues (older newer : List Nat) (coordinate width : Nat) : List Nat :=
  inputValues older newer coordinate width ++ scratchValues coordinate width

def initialConfiguration (offset : Nat) (older newer : List Nat) (coordinate width : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine offset) (endTape (inputValues older newer coordinate width) workspace [])

def finalConfiguration (offset : Nat) (older newer : List Nat) (coordinate width : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  { state := (machine offset).acceptState, tape := endTape (finalValues older newer coordinate width) workspace [] }

theorem workRunExact (offset : Nat) (older newer : List Nat) (coordinate width : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset) (hPositive : 0 < width) :
    workRunExact? (machine offset) (workSteps newer coordinate width)
      (initialConfiguration offset older newer coordinate width workspace) =
      some (finalConfiguration offset older newer coordinate width workspace) :=
  chain_run (prepareMachine offset) divideMachine (prepareSteps newer coordinate width)
    (divideSteps coordinate width) _ _ _
    (prepare_workRunExact offset older newer coordinate width workspace hLength)
    (divide_workRunExact _ coordinate width workspace hPositive)

theorem run_compile_exact (offset : Nat) (older newer : List Nat) (coordinate width : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset) (hPositive : 0 < width) :
    run (compileWorkMachine (machine offset)) (6 * workSteps newer coordinate width)
      (encodeWorkConfiguration (initialConfiguration offset older newer coordinate width workspace)) =
      encodeWorkConfiguration (finalConfiguration offset older newer coordinate width workspace) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact offset older newer coordinate width workspace hLength hPositive)

theorem final_tape (offset : Nat) (older newer : List Nat) (coordinate width : Nat) (workspace : List WorkSymbol) :
    (finalConfiguration offset older newer coordinate width workspace).tape =
      endTape (inputValues older newer coordinate width ++ scratchValues coordinate width) workspace [] := rfl

theorem scratch_quotient (coordinate width : Nat) :
    (scratchValues coordinate width)[5]? = some (coordinate / width) := rfl

theorem scratch_remainder (coordinate width : Nat) :
    (scratchValues coordinate width)[3]? = some (coordinate % width) := rfl

theorem quotient_remainder_reconstruct (coordinate width : Nat) :
    (coordinate / width) * width + coordinate % width = coordinate :=
  BuilderPostHeaderRawDivider.quotient_remainder_reconstruct coordinate width

theorem remainder_lt (coordinate width : Nat) (hPositive : 0 < width) :
    coordinate % width < width := Nat.mod_lt coordinate hPositive

theorem quotient_le (coordinate width : Nat) : coordinate / width ≤ coordinate := Nat.div_le_self coordinate width

/-- Reuse the existing canonical rectangle equivalence, preserving its outside guard. -/
theorem written_pair_matches_rectangle (count coordinate width : Nat) :
    (if coordinate < count * width then
      some ((scratchValues coordinate width)[5]?.getD 0, (scratchValues coordinate width)[3]?.getD 0)
    else none) =
      (BuilderArbitrarySlotPostHeaderDecoder.rectangleCoordinate? count width coordinate).map
        (fun pair => (pair.1.val, pair.2.val)) := by
  simp only [scratch_quotient, scratch_remainder, Option.getD_some]
  exact ClauseOccupancy.rectanglePair?_eq count width coordinate

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept program ∧ program.acceptState ≠ program.rejectState

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
   WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2⟩

private theorem delimiter_good : Good BuilderDividerOperands.Delimiter.machine :=
  ⟨BuilderDividerOperands.Delimiter.rules_pairwise_query_distinct,
   BuilderDividerOperands.Delimiter.noRuleAtAccept, BuilderDividerOperands.Delimiter.acceptState_ne_rejectState⟩

private theorem copy_good (offset : Nat) : Good (RegisterCopy.machine offset) :=
  ⟨RegisterCopy.rules_pairwise_query_distinct offset,
   fun rule hMem => Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState offset rule hMem),
   RegisterCopy.machine_acceptState_ne_rejectState offset⟩

private theorem good (offset : Nat) : Good (machine offset) :=
  chain_good _ _
    (chain_good _ _ (chain_good _ _ delimiter_good delimiter_good)
      (chain_good _ _ (copy_good 2) (copy_good (offset + 4))))
    (chain_good _ _
      ⟨BuilderClauseDividerExecution.division_rules_pairwise_query_distinct,
       BuilderClauseDividerExecution.division_noRuleAtAccept,
       BuilderClauseDividerExecution.division_acceptState_ne_rejectState⟩
      ⟨BuilderDividerCoordinateRegisters.rules_pairwise_query_distinct,
       BuilderDividerCoordinateRegisters.noRuleAtAccept,
       BuilderDividerCoordinateRegisters.acceptState_ne_rejectState⟩)

theorem rules_pairwise_query_distinct (offset : Nat) :
    (machine offset).rules.Pairwise WorkMachineChain.QueryDistinct := (good offset).1

theorem noRuleAtAccept (offset : Nat) : WorkMachineChain.NoRuleAtAccept (machine offset) := (good offset).2.1

theorem acceptState_ne_rejectState (offset : Nat) :
    (machine offset).acceptState ≠ (machine offset).rejectState := (good offset).2.2

private theorem restore_noRuleAtReject :
    WorkMachineProgramGraph.NoRuleAt BuilderDividerCoordinateRegisters.machine
      BuilderDividerCoordinateRegisters.machine.rejectState := by
  intro rule hMem
  change rule.sourceState ≠ 16
  change rule ∈ BuilderDividerCoordinateRegisters.rules at hMem
  decide +revert

theorem noRuleAtReject (offset : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine offset) (machine offset).rejectState :=
  WorkMachineChain.noRuleAtAccept (prepareMachine offset)
    { divideMachine with acceptState := divideMachine.rejectState }
    (WorkMachineChain.noRuleAtAccept divisionMachine
      { BuilderDividerCoordinateRegisters.machine with acceptState := BuilderDividerCoordinateRegisters.machine.rejectState }
      restore_noRuleAtReject)

def copyBound (bound : Nat) : Nat := 4 * (bound + 1) * (bound + 1) + 9 * (bound + 1) + 5

def workBound (bound : Nat) : Nat :=
  7 + 2 * copyBound (3 * bound + 4) + 1 +
    (4 * bound + 8 + 20 * (2 * bound + 1) * (2 * bound + 1)) + 1 + (15 * bound + 19)

theorem workSteps_le (newer : List Nat) (coordinate width bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hWidth : width ≤ bound)
    (hNewer : newer.length + newer.sum ≤ bound) (hPositive : 0 < width) :
    workSteps newer coordinate width ≤ workBound bound := by
  have hCoordinate' : coordinate ≤ 3 * bound + 4 := by omega
  have hWidth' : width ≤ 3 * bound + 4 := by omega
  have hFirst : [0, 0].length + [0, 0].sum ≤ 3 * bound + 4 := by
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  have hSecond : (newer ++ [coordinate, 0, 0, coordinate]).length +
      (newer ++ [coordinate, 0, 0, coordinate]).sum ≤ 3 * bound + 4 := by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.sum_append, List.sum_cons, List.sum_nil]
    omega
  have hCopy1 := RegisterCopy.steps_le [0, 0] coordinate (3 * bound + 4) hCoordinate' hFirst
  have hCopy2 := RegisterCopy.steps_le (newer ++ [coordinate, 0, 0, coordinate]) width
    (3 * bound + 4) hWidth' hSecond
  have hDivision := BuilderClauseDividerExecution.divisionSteps_le 0 coordinate width bound
    (Nat.zero_le _) hCoordinate hWidth hPositive
  have hQuotient := Nat.le_trans (Nat.div_le_self coordinate width) hCoordinate
  have hRemainder := Nat.le_trans (Nat.mod_le coordinate width) hCoordinate
  have hConsumed := Nat.le_trans (Nat.div_mul_le_self coordinate width) hCoordinate
  have hRestore := BuilderDividerCoordinateRegisters.workSteps_le (resultView coordinate width) bound
    hQuotient hWidth hRemainder hConsumed (Nat.zero_le _)
  unfold workSteps prepareSteps copySteps divideSteps workBound copyBound
  omega

theorem scratch_span_le (coordinate width bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hWidth : width ≤ bound) :
    (scratchValues coordinate width).length + (scratchValues coordinate width).sum ≤ 3 * bound + 6 := by
  have hReconstruct := quotient_remainder_reconstruct coordinate width
  have hQuotient := Nat.le_trans (quotient_le coordinate width) hCoordinate
  simp only [scratchValues, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  omega

theorem final_register_span_le (older newer : List Nat) (coordinate width bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hWidth : width ≤ bound) :
    (registerWord (finalValues older newer coordinate width)).length ≤
      (registerWord (inputValues older newer coordinate width)).length + (3 * bound + 6) := by
  have hScratch := scratch_span_le coordinate width bound hCoordinate hWidth
  simp only [finalValues, registerWord_append, List.length_append, registerWord_length]
  omega

private def copyPolynomial (bound : NatPolynomial) : NatPolynomial :=
  let next := NatPolynomial.add bound (.constant 1)
  .add (.add (.mul (.constant 4) (.mul next next)) (.mul (.constant 9) next)) (.constant 5)

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  let larger := NatPolynomial.add (.mul (.constant 3) bound) (.constant 4)
  let twice := NatPolynomial.add (.mul (.constant 2) bound) (.constant 1)
  .mul (.constant 6)
    (.add (.add (.add (.add (.add (.constant 7) (.mul (.constant 2) (copyPolynomial larger))) (.constant 1))
      (.add (.add (.mul (.constant 4) bound) (.constant 8)) (.mul (.constant 20) (.mul twice twice)))) (.constant 1))
      (.add (.mul (.constant 15) bound) (.constant 19)))

theorem rawTimePolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := by
  simp only [rawTimePolynomial, copyPolynomial, workBound, copyBound,
    NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant, Nat.mul_assoc]

theorem rawTimePolynomial_le (newer : List Nat) (coordinate width input : Nat) (bound : NatPolynomial)
    (hCoordinate : coordinate ≤ bound.eval input) (hWidth : width ≤ bound.eval input)
    (hNewer : newer.length + newer.sum ≤ bound.eval input) (hPositive : 0 < width) :
    6 * workSteps newer coordinate width ≤ (rawTimePolynomial bound).eval input := by
  rw [rawTimePolynomial_eval]
  exact Nat.mul_le_mul_left 6 (workSteps_le newer coordinate width (bound.eval input) hCoordinate hWidth hNewer hPositive)

end PNP.Concrete.CookLevin.BuilderRegionCoordinateDivision

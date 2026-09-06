/-
Copyright (c) 2026 PNP Labs.

Derive disposable comparison operands from ordinary registers and execute the
general protected comparator. The two copy offsets are fixed control parameters,
not input-dependent programs. The original registers and workspace are preserved.

The source-bound entry executes the existing source body once. This component
does not restore residuals, dispatch all five regions, decode or emit a body
token, execute Finish, or package the complete formula-builder reduction.
-/

import PNP.Concrete.CookLevinBuilderRegionPairComparison

namespace PNP.Concrete.CookLevin.BuilderRegionComparisonOperands

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count quadratic)
open BuilderClauseDividerOperands (quotient)
open BuilderClauseDividerExecution (constraintIndex)
open BuilderDividerSourceExecution (sourceSpan)

/-- Copy a physically selected register without changing its older or newer neighbours. -/
theorem copy_workRunExact (offset : Nat) (older newer : List Nat) (value : Nat)
    (workspace tail : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (RegisterCopy.machine offset) (RegisterCopy.steps newer value)
      (workStartConfiguration (RegisterCopy.machine offset)
        (endTape (older ++ [value] ++ newer) workspace tail)) =
      some {
        state := (RegisterCopy.machine offset).acceptState
        tape := endTape (older ++ [value] ++ newer ++ [value]) workspace (tail.drop (value + 1))
      } := by
  rw [← hLength, RegisterCopy.machine_acceptState]
  have h := RegisterCopy.workRunExact (registerWord older) workspace tail value newer
  change workRunExact? (RegisterCopy.machine newer.length) (RegisterCopy.steps newer value)
      {
        state := 0
        tape := {
          left := tail
          head := scratchEndSymbol
          right := (registerWord older ++ registerWord ([value] ++ newer)).reverse ++ workspace
        }
      } = some {
        state := RegisterCopy.stateCount newer.length
        tape := {
          left := tail.drop (value + 1)
          head := scratchEndSymbol
          right := (registerWord older ++ registerWord ([value] ++ newer ++ [value])).reverse ++ workspace
        }
      } at h
  simpa only [workStartConfiguration, RegisterCopy.machine_startState, endTape,
    registerWord_append, List.append_assoc] using h

private theorem chain_run_accept (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some { state := first.acceptState, tape := middle })
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some { state := second.acceptState, tape := final }) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some { state := (WorkMachineChain.machine first second).acceptState, tape := final } :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

private theorem chain_run_any (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle : WorkTape) (final : WorkConfiguration)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some { state := first.acceptState, tape := middle })
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) = some final) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some (renameConfiguration WorkMachineChain.secondState final) :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

def inputValues (older newer : List Nat) (coordinate boundary : Nat) : List Nat :=
  older ++ [boundary] ++ newer ++ [coordinate]

def prepareMachine (offset : Nat) : WorkMachine :=
  WorkMachineChain.machine (RegisterCopy.machine 0) (RegisterCopy.machine (offset + 2))

def prepareSteps (newer : List Nat) (coordinate boundary : Nat) : Nat :=
  RegisterCopy.steps [] coordinate + 1 + RegisterCopy.steps (newer ++ [coordinate, coordinate]) boundary

theorem prepare_workRunExact (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace tail : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (prepareMachine offset) (prepareSteps newer coordinate boundary)
      (workStartConfiguration (prepareMachine offset)
        (endTape (inputValues older newer coordinate boundary) workspace tail)) =
      some {
        state := (prepareMachine offset).acceptState
        tape := endTape (inputValues older newer coordinate boundary ++ [coordinate, boundary])
          workspace ((tail.drop (coordinate + 1)).drop (boundary + 1))
      } := by
  have hCoordinate := copy_workRunExact 0 (older ++ [boundary] ++ newer) [] coordinate workspace tail rfl
  simp only [List.append_nil] at hCoordinate
  have hBoundaryLength : (newer ++ [coordinate, coordinate]).length = offset + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hLength]
  have hBoundary := copy_workRunExact (offset + 2) older (newer ++ [coordinate, coordinate])
    boundary workspace (tail.drop (coordinate + 1)) hBoundaryLength
  have hAll := chain_run_accept (RegisterCopy.machine 0) (RegisterCopy.machine (offset + 2))
    (RegisterCopy.steps [] coordinate) (RegisterCopy.steps (newer ++ [coordinate, coordinate]) boundary)
    _ _ _ hCoordinate (by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hBoundary)
  simpa only [prepareMachine, prepareSteps, inputValues, List.append_assoc,
    List.cons_append, List.nil_append] using hAll

def machine (offset : Nat) : WorkMachine :=
  WorkMachineChain.machine (prepareMachine offset) BuilderRegionPairComparison.machine

def workSteps (newer : List Nat) (coordinate boundary : Nat) : Nat :=
  prepareSteps newer coordinate boundary + 1 + BuilderRegionPairComparison.workSteps coordinate boundary

def initialConfiguration (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine offset)
    (endTape (inputValues older newer coordinate boundary) workspace [])

def finalConfiguration (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderRegionPairComparison.finalConfiguration coordinate boundary
      (inputValues older newer coordinate boundary) workspace)

theorem workRunExact (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (machine offset) (workSteps newer coordinate boundary)
      (initialConfiguration offset older newer coordinate boundary workspace) =
      some (finalConfiguration older newer coordinate boundary workspace) := by
  have hPrepare := prepare_workRunExact offset older newer coordinate boundary workspace [] hLength
  simp only [List.drop_nil] at hPrepare
  have hCompare := BuilderRegionPairComparison.workRunExact coordinate boundary
    (inputValues older newer coordinate boundary) workspace
  exact WorkMachineChain.workRunExact (prepareMachine offset) BuilderRegionPairComparison.machine
    (prepareSteps newer coordinate boundary) (BuilderRegionPairComparison.workSteps coordinate boundary)
    _ _ _ hPrepare rfl hCompare

theorem run_compile_exact (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset) :
    run (compileWorkMachine (machine offset)) (6 * workSteps newer coordinate boundary)
      (encodeWorkConfiguration (initialConfiguration offset older newer coordinate boundary workspace)) =
      encodeWorkConfiguration (finalConfiguration older newer coordinate boundary workspace) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact offset older newer coordinate boundary workspace hLength)

theorem final_accept_iff (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).state = (machine offset).acceptState ↔
      coordinate < boundary := by
  change WorkMachineChain.secondState
      (BuilderRegionPairComparison.finalConfiguration coordinate boundary
        (inputValues older newer coordinate boundary) workspace).state =
    WorkMachineChain.secondState BuilderRegionPairComparison.machine.acceptState ↔ _
  constructor
  · intro h
    exact (BuilderRegionPairComparison.final_accept_iff coordinate boundary _ workspace).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegionPairComparison.final_accept_iff coordinate boundary _ workspace).2 h)

theorem final_reject_iff (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).state = (machine offset).rejectState ↔
      boundary ≤ coordinate := by
  change WorkMachineChain.secondState
      (BuilderRegionPairComparison.finalConfiguration coordinate boundary
        (inputValues older newer coordinate boundary) workspace).state =
    WorkMachineChain.secondState BuilderRegionPairComparison.machine.rejectState ↔ _
  constructor
  · intro h
    exact (BuilderRegionPairComparison.final_reject_iff coordinate boundary _ workspace).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegionPairComparison.final_reject_iff coordinate boundary _ workspace).2 h)

theorem final_exterior_preserved (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).tape.right =
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration coordinate boundary).tape.left ++
        ((registerWord (inputValues older newer coordinate boundary)).reverse ++ workspace) :=
  BuilderRegionPairComparison.final_exterior_preserved coordinate boundary _ workspace

private def Good (localMachine : WorkMachine) : Prop :=
  localMachine.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept localMachine ∧ localMachine.acceptState ≠ localMachine.rejectState

private theorem copy_good (offset : Nat) : Good (RegisterCopy.machine offset) :=
  ⟨RegisterCopy.rules_pairwise_query_distinct offset,
   (fun selected hMem => Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState offset selected hMem)),
   RegisterCopy.machine_acceptState_ne_rejectState offset⟩

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct first second hFirst.1 hSecond.1 hFirst.2.1,
   WorkMachineChain.noRuleAtAccept first second hSecond.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState first second hSecond.2.2⟩

private theorem prepare_good (offset : Nat) : Good (prepareMachine offset) :=
  chain_good _ _ (copy_good 0) (copy_good (offset + 2))

private theorem machine_good (offset : Nat) : Good (machine offset) :=
  chain_good _ _ (prepare_good offset)
    ⟨BuilderRegionPairComparison.rules_pairwise_query_distinct,
     BuilderRegionPairComparison.noRuleAtAccept, BuilderRegionPairComparison.acceptState_ne_rejectState⟩

theorem prepare_rules_pairwise_query_distinct (offset : Nat) :
    (prepareMachine offset).rules.Pairwise WorkMachineChain.QueryDistinct := (prepare_good offset).1

theorem prepare_noRuleAtAccept (offset : Nat) :
    WorkMachineChain.NoRuleAtAccept (prepareMachine offset) := (prepare_good offset).2.1

theorem prepare_acceptState_ne_rejectState (offset : Nat) :
    (prepareMachine offset).acceptState ≠ (prepareMachine offset).rejectState := (prepare_good offset).2.2

theorem rules_pairwise_query_distinct (offset : Nat) :
    (machine offset).rules.Pairwise WorkMachineChain.QueryDistinct := (machine_good offset).1

theorem noRuleAtAccept (offset : Nat) :
    WorkMachineChain.NoRuleAtAccept (machine offset) := (machine_good offset).2.1

theorem acceptState_ne_rejectState (offset : Nat) :
    (machine offset).acceptState ≠ (machine offset).rejectState := (machine_good offset).2.2

theorem prepareSteps_le (newer : List Nat) (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound)
    (hNewer : newer.length + newer.sum ≤ bound) :
    prepareSteps newer coordinate boundary ≤ 2 * quadratic (3 * bound + 2) + 1 := by
  have hCoordinate' : coordinate ≤ 3 * bound + 2 := by omega
  have hBoundary' : boundary ≤ 3 * bound + 2 := by omega
  have hEmpty : ([] : List Nat).length + ([] : List Nat).sum ≤ 3 * bound + 2 := by
    change 0 ≤ _
    omega
  have hNewer' : (newer ++ [coordinate, coordinate]).length +
      (newer ++ [coordinate, coordinate]).sum ≤ 3 * bound + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.sum_append, List.sum_cons, List.sum_nil]
    omega
  have hFirst := RegisterCopy.steps_le [] coordinate (3 * bound + 2) hCoordinate' hEmpty
  have hSecond := RegisterCopy.steps_le (newer ++ [coordinate, coordinate]) boundary
    (3 * bound + 2) hBoundary' hNewer'
  change RegisterCopy.steps [] coordinate ≤ quadratic (3 * bound + 2) at hFirst
  change RegisterCopy.steps (newer ++ [coordinate, coordinate]) boundary ≤ quadratic (3 * bound + 2) at hSecond
  unfold prepareSteps
  omega

theorem workSteps_le (newer : List Nat) (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound)
    (hNewer : newer.length + newer.sum ≤ bound) :
    workSteps newer coordinate boundary ≤
      2 * quadratic (3 * bound + 2) + 2 + (2 * bound + 4 + 6 * (bound + 1) * (bound + 1)) := by
  have hPrepare := prepareSteps_le newer coordinate boundary bound hCoordinate hBoundary hNewer
  have hCompare := BuilderRegionPairComparison.workSteps_le coordinate boundary bound hCoordinate hBoundary
  unfold workSteps
  omega

private def quadraticPolynomial (bound : NatPolynomial) : NatPolynomial :=
  let plus := NatPolynomial.add bound (.constant 1)
  .add (.add (.mul (.mul (.constant 4) plus) plus) (.mul (.constant 9) plus)) (.constant 5)

private def comparisonPolynomial (bound : NatPolynomial) : NatPolynomial :=
  let plus := NatPolynomial.add bound (.constant 1)
  .add (.add (.mul (.constant 2) bound) (.constant 4)) (.mul (.mul (.constant 6) plus) plus)

/-- Includes both copies, both bridges, the layout adapter and the full comparator. -/
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6)
    (.add
      (.add (.mul (.constant 2)
        (quadraticPolynomial (.add (.mul (.constant 3) bound) (.constant 2)))) (.constant 2))
      (comparisonPolynomial bound))

theorem rawTimePolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input =
      6 * (2 * quadratic (3 * bound.eval input + 2) + 2 +
        (2 * bound.eval input + 4 + 6 * (bound.eval input + 1) * (bound.eval input + 1))) := rfl

theorem rawTimePolynomial_le (newer : List Nat) (coordinate boundary input : Nat) (bound : NatPolynomial)
    (hCoordinate : coordinate ≤ bound.eval input) (hBoundary : boundary ≤ bound.eval input)
    (hNewer : newer.length + newer.sum ≤ bound.eval input) :
    6 * workSteps newer coordinate boundary ≤ (rawTimePolynomial bound).eval input := by
  rw [rawTimePolynomial_eval]
  exact Nat.mul_le_mul_left 6 (workSteps_le newer coordinate boundary (bound.eval input)
    hCoordinate hBoundary hNewer)

namespace Source

open BuilderConstraintRegionRegisters (termValue)

def olderValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : List Nat :=
  BuilderClauseCoordinateRegisters.finalValues problem index remaining ++
    BuilderConstraintRegionAssembly.afterInitial problem

/-- The first region length and the computed index are located in the actual assembled word. -/
theorem assembled_values_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    BuilderConstraintRegionAssembly.finalValues problem index remaining =
      inputValues (olderValues problem index remaining) [] (constraintIndex problem index)
        (termValue problem .shape) := by
  simp only [BuilderConstraintRegionAssembly.finalValues,
    BuilderConstraintRegionAssembly.preparedFrame, BuilderConstraintRegionAssembly.lengthFrame,
    olderValues, BuilderConstraintRegionAssembly.afterInitial, inputValues,
    List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

/-- The source program runs once; every subsequent copy offset is fixed. -/
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderConstraintRegionAssembly.bodyMachine verifier)
    (BuilderRegionComparisonOperands.machine 0)

def workSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  BuilderConstraintRegionAssembly.bodySteps problem index remaining + 1 +
    BuilderRegionComparisonOperands.workSteps [] (constraintIndex problem index) (termValue problem .shape)

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (BuilderCursorSource.cursorTape problem index remaining output)

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderRegionComparisonOperands.finalConfiguration (olderValues problem index remaining) []
      (constraintIndex problem index) (termValue problem .shape) (inside problem.input output))

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  have hAssembly := BuilderConstraintRegionAssembly.body_workRunExact problem index remaining output hBody
  unfold BuilderConstraintRegionAssembly.bodyInitial BuilderConstraintRegionAssembly.bodyFinal at hAssembly
  rw [assembled_values_eq] at hAssembly
  have hCompare := BuilderRegionComparisonOperands.workRunExact 0
    (olderValues problem index remaining) [] (constraintIndex problem index) (termValue problem .shape)
    (inside problem.input output) rfl
  exact chain_run_any (BuilderConstraintRegionAssembly.bodyMachine problem.verifier)
    (BuilderRegionComparisonOperands.machine 0) (BuilderConstraintRegionAssembly.bodySteps problem index remaining)
    (BuilderRegionComparisonOperands.workSteps [] (constraintIndex problem index) (termValue problem .shape))
    _ _ _ hAssembly hCompare

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output hBody)

theorem final_accept_iff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState ↔
      constraintIndex problem index < termValue problem .shape := by
  change WorkMachineChain.secondState
      (BuilderRegionComparisonOperands.finalConfiguration (olderValues problem index remaining) []
        (constraintIndex problem index) (termValue problem .shape) (inside problem.input output)).state =
    WorkMachineChain.secondState (BuilderRegionComparisonOperands.machine 0).acceptState ↔ _
  constructor
  · intro h
    exact (BuilderRegionComparisonOperands.final_accept_iff 0 _ [] _ _ _).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegionComparisonOperands.final_accept_iff 0 _ [] _ _ _).2 h)

theorem final_reject_iff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).rejectState ↔
      termValue problem .shape ≤ constraintIndex problem index := by
  change WorkMachineChain.secondState
      (BuilderRegionComparisonOperands.finalConfiguration (olderValues problem index remaining) []
        (constraintIndex problem index) (termValue problem .shape) (inside problem.input output)).state =
    WorkMachineChain.secondState (BuilderRegionComparisonOperands.machine 0).rejectState ↔ _
  constructor
  · intro h
    exact (BuilderRegionComparisonOperands.final_reject_iff 0 _ [] _ _ _).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegionComparisonOperands.final_reject_iff 0 _ [] _ _ _).2 h)

theorem final_exterior_preserved {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape.right =
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration (constraintIndex problem index)
        (termValue problem .shape)).tape.left ++
        ((registerWord (BuilderConstraintRegionAssembly.finalValues problem index remaining)).reverse ++
          inside problem.input output) := by
  rw [assembled_values_eq]
  exact BuilderRegionComparisonOperands.final_exterior_preserved _ [] _ _ _

theorem source_values_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    constraintIndex problem index ≤ (sourceSpan problem.verifier).eval problem.input.length ∧
      termValue problem .shape ≤ (sourceSpan problem.verifier).eval problem.input.length := by
  have hIndex : constraintIndex problem index ≤ (sourceSpan problem.verifier).eval problem.input.length :=
    (BuilderClauseCoordinateRegisters.source_magnitudes_le problem index remaining hBalance).1
  have hCount := BuilderConstraintRegionAssembly.constraintCount_le_sourceSpan problem index remaining hBalance
  have hFrame := BuilderConstraintRegionAssembly.lengthFrame_sum problem
  simp only [BuilderConstraintRegionAssembly.lengthFrame, List.sum_cons, List.sum_nil, Nat.add_zero] at hFrame
  constructor <;> omega

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderConstraintRegionAssembly.bodyRawTimeBound verifier)
    (.add (.constant 6) (rawTimePolynomial (sourceSpan verifier)))

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hAssembly := BuilderConstraintRegionAssembly.body_rawTimeBound_le problem index remaining hBalance
  have hValues := source_values_le problem index remaining hBalance
  have hNewer : ([] : List Nat).length + ([] : List Nat).sum ≤
      (sourceSpan problem.verifier).eval problem.input.length := Nat.zero_le _
  have hCompare := rawTimePolynomial_le [] (constraintIndex problem index) (termValue problem .shape)
    problem.input.length (sourceSpan problem.verifier) hValues.1 hValues.2 hNewer
  simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  unfold workSteps
  omega

private theorem source_good {language : Language} (verifier : PolynomialTimeVerifier language) :
    Good (machine verifier) :=
  chain_good _ _
    ⟨BuilderConstraintRegionAssembly.body_rules_pairwise_query_distinct verifier,
     BuilderConstraintRegionAssembly.body_noRuleAtAccept verifier,
     BuilderConstraintRegionAssembly.body_acceptState_ne_rejectState verifier⟩ (machine_good 0)

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := (source_good verifier).1

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := (source_good verifier).2.1

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := (source_good verifier).2.2

end Source
end PNP.Concrete.CookLevin.BuilderRegionComparisonOperands

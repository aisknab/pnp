import PNP.Concrete.CookLevinBuilderConstraintRegionSource

namespace PNP.Concrete.CookLevinBuilderConstraintRegionSourceRegression

open CookLevin PipelineTape BuilderUnaryPolynomial
open BuilderConstraintRegionSource
open BuilderConstraintRegionRegisters (Region regionLength)
open BuilderConstraintRegionDispatch (regionTag)
open BuilderDividerOperands (endTape inside count)
open BuilderClauseDividerOperands (quotient)
open BuilderClauseDividerExecution (constraintIndex)
open BuilderDividerSourceExecution (sourceSpan)

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    machine verifier = WorkMachineChain.machine (BuilderConstraintRegionAssembly.bodyMachine verifier)
      BuilderConstraintRegionDispatch.machine := rfl

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    workSteps problem index remaining = BuilderConstraintRegionAssembly.bodySteps problem index remaining + 1 +
      BuilderConstraintRegionDispatch.workSteps (lengths problem) (constraintIndex problem index) := rfl

example {language : Language} (problem : VerifierTableauProblem language) (region : Region) :
    BuilderConstraintRegionDispatch.boundary (lengths problem) region = regionLength problem region :=
  boundary_eq problem region

example {language : Language} (problem : VerifierTableauProblem language) :
    BuilderConstraintRegionDispatch.frame (lengths problem) = BuilderConstraintRegionAssembly.lengthFrame problem :=
  frame_eq problem

example {language : Language} (problem : VerifierTableauProblem language) :
    BuilderConstraintRegionDispatch.total (lengths problem) = problem.formulaConstraintSlotCount := total_eq problem

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderConstraintRegionAssembly.finalValues problem index remaining =
      BuilderConstraintRegionDispatch.initialValues (lengths problem) (constraintIndex problem index)
        (BuilderClauseCoordinateRegisters.finalValues problem index remaining) :=
  assembled_values_eq problem index remaining

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (workStartConfiguration (machine problem.verifier) (BuilderCursorSource.cursorTape problem index remaining output)) =
      some (finalConfiguration problem index remaining output) :=
  workRunExact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compile_exact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      endTape (finalValues problem index remaining) (inside problem.input output) [] :=
  final_tape problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState ↔
      constraintIndex problem index < problem.formulaConstraintSlotCount := final_accept_iff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).rejectState ↔
      problem.formulaConstraintSlotCount ≤ constraintIndex problem index := final_reject_iff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState :=
  final_accept_of_body problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hBody : quotient problem index < count problem) :
    ∃ region, selectedRegion problem index = some region := selectedRegion_some_of_body problem index hBody

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (region : Region)
    (hRegion : selectedRegion problem index = some region) :
    localCoordinate problem index region < regionLength problem region := localCoordinate_valid problem index region hRegion

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (region : Region) (hRegion : selectedRegion problem index = some region) :
    (finalConfiguration problem index remaining output).tape =
      endTape (BuilderConstraintRegionAssembly.finalValues problem index remaining ++
        selectedScratch problem index region) (inside problem.input output) [] :=
  final_selected_tape problem index remaining output region hRegion

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape.left = [] := final_outer_empty problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    constraintIndex problem index ≤ (sourceSpan problem.verifier).eval problem.input.length ∧
      ∀ region, regionLength problem region ≤ (sourceSpan problem.verifier).eval problem.input.length :=
  source_values_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  rawTimeBound_le problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) (input : Nat) :
    (rawTimeBound verifier).eval input =
      (BuilderConstraintRegionAssembly.bodyRawTimeBound verifier).eval input + 6 +
        (BuilderConstraintRegionDispatch.rawTimePolynomial (sourceSpan verifier)).eval input := by
  simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant, Nat.add_assoc]

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState := noRuleAtReject verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := acceptState_ne_rejectState verifier

example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat) :
    slotForCoordinate problem coordinate = problem.formulaConstraintSlotDirect coordinate :=
  slotForCoordinate_eq problem coordinate

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    selectedSlot problem index = problem.formulaConstraintSlotDirect (constraintIndex problem index) :=
  selectedSlot_eq problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (region : Region)
    (hRegion : selectedRegion problem index = some region) :
    regionSlot problem region (localCoordinate problem index region) =
      problem.formulaConstraintSlotDirect (constraintIndex problem index) := regionSlot_eq problem index region hRegion

example {language : Language} (problem : VerifierTableauProblem language) :
    regionSlot problem .accepting 0 =
      some (some (.require (problem.stateLiteral problem.finalTime problem.acceptingState))) := rfl

example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat) :
    regionSlot problem .accepting (coordinate + 1) = none := rfl

-- These cases intentionally distinguish an absent slot from a padded empty slot.
example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat)
    (hOutside : problem.formulaConstraintSlotCount ≤ coordinate) :
    slotForCoordinate problem coordinate = none := by
  have hNone := BuilderConstraintRegionDispatch.selectedRegion_none_iff (lengths problem) coordinate
  rw [total_eq] at hNone
  unfold slotForCoordinate
  rw [hNone.2 hOutside]

example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat)
    (hPadding : problem.formulaConstraintSlotDirect coordinate = some none) :
    slotForCoordinate problem coordinate = some none := by
  rw [slotForCoordinate_eq, hPadding]

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    ∃ region,
      workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
        some {
          state := (machine problem.verifier).acceptState
          tape := endTape (BuilderConstraintRegionAssembly.finalValues problem index remaining ++
            selectedScratch problem index region) (inside problem.input output) []
        } ∧
      localCoordinate problem index region < regionLength problem region ∧
      regionSlot problem region (localCoordinate problem index region) =
        problem.formulaConstraintSlotDirect (constraintIndex problem index) :=
  body_dispatch_correct problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (region : Region)
    (hRegion : selectedRegion problem index = some region) :
    finalValues problem index remaining = BuilderConstraintRegionAssembly.finalValues problem index remaining ++
      selectedScratch problem index region := finalValues_of_region problem index remaining region hRegion

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (region : Region)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : selectedRegion problem index = some region) :
    (selectedScratch problem index region).length + (selectedScratch problem index region).sum ≤
      20 * (sourceSpan problem.verifier).eval problem.input.length + 25 :=
  selectedScratch_size_le problem index remaining region hBalance hRegion

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining)).length ≤
      31 * (sourceSpan problem.verifier).eval problem.input.length + 42 :=
  final_register_span_le problem index remaining hBody hBalance

end PNP.Concrete.CookLevinBuilderConstraintRegionSourceRegression

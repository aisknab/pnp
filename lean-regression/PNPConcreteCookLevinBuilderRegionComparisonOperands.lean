import PNP.Concrete.CookLevinBuilderRegionComparisonOperands

namespace PNP.Concrete.CookLevinBuilderRegionComparisonOperandsRegression

open CookLevin PipelineTape BuilderUnaryPolynomial
open BuilderRegionComparisonOperands
open BuilderDividerOperands (endTape inside count quadratic)
open BuilderClauseDividerOperands (quotient)
open BuilderClauseDividerExecution (constraintIndex)
open BuilderConstraintRegionRegisters (termValue)
open BuilderDividerSourceExecution (sourceSpan)
open BuilderArbitrarySlotHeaderRouter.RawRouter (coordinateMark boundaryMark)

example (offset : Nat) :
    prepareMachine offset =
      WorkMachineChain.machine (RegisterCopy.machine 0) (RegisterCopy.machine (offset + 2)) := rfl

example (offset : Nat) (older newer : List Nat) (value : Nat) (workspace tail : List WorkSymbol)
    (hLength : newer.length = offset) :
    workRunExact? (RegisterCopy.machine offset) (RegisterCopy.steps newer value)
      (workStartConfiguration (RegisterCopy.machine offset)
        (endTape (older ++ [value] ++ newer) workspace tail)) =
      some {
        state := (RegisterCopy.machine offset).acceptState
        tape := endTape (older ++ [value] ++ newer ++ [value]) workspace (tail.drop (value + 1))
      } := copy_workRunExact offset older newer value workspace tail hLength

example (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace tail : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (prepareMachine offset) (prepareSteps newer coordinate boundary)
      (workStartConfiguration (prepareMachine offset)
        (endTape (inputValues older newer coordinate boundary) workspace tail)) =
      some {
        state := (prepareMachine offset).acceptState
        tape := endTape (inputValues older newer coordinate boundary ++ [coordinate, boundary])
          workspace ((tail.drop (coordinate + 1)).drop (boundary + 1))
      } := prepare_workRunExact offset older newer coordinate boundary workspace tail hLength

example :
    workRunExact? (prepareMachine 0) (prepareSteps [] 0 0)
      (workStartConfiguration (prepareMachine 0)
        (endTape [0, 0, 0] [.blankOne] [.zeroBlank, .oneBlank, .oneZero])) =
      some {
        state := (prepareMachine 0).acceptState
        tape := endTape [0, 0, 0, 0, 0] [.blankOne] [.oneZero]
      } := by decide

example :
    workRunExact? (prepareMachine 2) (prepareSteps [1, 0] 1 2)
      (workStartConfiguration (prepareMachine 2)
        (endTape [3, 2, 1, 0, 1] [.blank, .zeroZero]
          [.blank, .oneOne, .zeroZero, .blankOne, .oneZero, .oneBlank, .zeroBlank])) =
      some {
        state := (prepareMachine 2).acceptState
        tape := endTape [3, 2, 1, 0, 1, 1, 2] [.blank, .zeroZero] [.oneBlank, .zeroBlank]
      } := by decide

example :
    workRunExact? (prepareMachine 0) (prepareSteps [1] 0 2)
      (workStartConfiguration (prepareMachine 0) (endTape [2, 1, 0] [] [])) ≠
      some {
        state := (prepareMachine 0).acceptState
        tape := endTape [2, 1, 0, 0, 2] [] []
      } := by decide

example :
    workRunExact? (prepareMachine 0) (prepareSteps [] 0 0 - 1)
      (workStartConfiguration (prepareMachine 0) (endTape [0, 0] [] [])) ≠
      some {
        state := (prepareMachine 0).acceptState
        tape := endTape [0, 0, 0, 0] [] []
      } := by decide

example (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (machine offset) (workSteps newer coordinate boundary)
      (initialConfiguration offset older newer coordinate boundary workspace) =
      some (finalConfiguration older newer coordinate boundary workspace) :=
  workRunExact offset older newer coordinate boundary workspace hLength

example (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset) :
    run (compileWorkMachine (machine offset)) (6 * workSteps newer coordinate boundary)
      (encodeWorkConfiguration (initialConfiguration offset older newer coordinate boundary workspace)) =
      encodeWorkConfiguration (finalConfiguration older newer coordinate boundary workspace) :=
  run_compile_exact offset older newer coordinate boundary workspace hLength

example :
    workRunExact? (machine 0) (workSteps [] 0 0) (initialConfiguration 0 [1] [] 0 0 [.oneBlank]) =
      some {
        state := (machine 0).rejectState
        tape := {
          left := []
          head := scratchEndSymbol
          right := [separatorSymbol, leftMarker] ++ (registerWord [1, 0, 0]).reverse ++ [.oneBlank]
        }
      } := by decide

example :
    workRunExact? (machine 2) (workSteps [0, 1] 1 2)
      (initialConfiguration 2 [0] [0, 1] 1 2 [.zeroZero, .blankOne]) =
      some {
        state := (machine 2).acceptState
        tape := {
          left := [scratchEndSymbol]
          head := unitSymbol
          right := [boundaryMark, separatorSymbol, coordinateMark, leftMarker] ++
            (registerWord [0, 2, 0, 1, 1]).reverse ++ [.zeroZero, .blankOne]
        }
      } := by decide

example :
    workRunExact? (machine 1) (workSteps [0] 2 1) (initialConfiguration 1 [] [0] 2 1 [.zeroBlank]) =
      some {
        state := (machine 1).rejectState
        tape := {
          left := []
          head := scratchEndSymbol
          right := [boundaryMark, separatorSymbol, coordinateMark, coordinateMark, leftMarker] ++
            (registerWord [1, 0, 2]).reverse ++ [.zeroBlank]
        }
      } := by decide

example :
    workRunExact? (machine 0) (workSteps [] 1 1) (initialConfiguration 0 [] [] 1 1 [.blank]) =
      some {
        state := (machine 0).rejectState
        tape := {
          left := []
          head := scratchEndSymbol
          right := [boundaryMark, separatorSymbol, coordinateMark, leftMarker] ++
            (registerWord [1, 1]).reverse ++ [.blank]
        }
      } := by decide

example (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat) (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).state = (machine offset).acceptState ↔
      coordinate < boundary := final_accept_iff offset older newer coordinate boundary workspace

example (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat) (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).state = (machine offset).rejectState ↔
      boundary ≤ coordinate := final_reject_iff offset older newer coordinate boundary workspace

example (older newer : List Nat) (coordinate boundary : Nat) (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).tape.right =
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration coordinate boundary).tape.left ++
        ((registerWord (inputValues older newer coordinate boundary)).reverse ++ workspace) :=
  final_exterior_preserved older newer coordinate boundary workspace

example (offset : Nat) : (prepareMachine offset).rules.Pairwise WorkMachineChain.QueryDistinct :=
  prepare_rules_pairwise_query_distinct offset

example (offset : Nat) : WorkMachineChain.NoRuleAtAccept (prepareMachine offset) := prepare_noRuleAtAccept offset

example (offset : Nat) : (prepareMachine offset).acceptState ≠ (prepareMachine offset).rejectState :=
  prepare_acceptState_ne_rejectState offset

example (offset : Nat) : (machine offset).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct offset

example (offset : Nat) : WorkMachineChain.NoRuleAtAccept (machine offset) := noRuleAtAccept offset

example (offset : Nat) : (machine offset).acceptState ≠ (machine offset).rejectState :=
  acceptState_ne_rejectState offset

example (newer : List Nat) (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound)
    (hNewer : newer.length + newer.sum ≤ bound) :
    prepareSteps newer coordinate boundary ≤ 2 * quadratic (3 * bound + 2) + 1 :=
  prepareSteps_le newer coordinate boundary bound hCoordinate hBoundary hNewer

example (newer : List Nat) (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound)
    (hNewer : newer.length + newer.sum ≤ bound) :
    workSteps newer coordinate boundary ≤
      2 * quadratic (3 * bound + 2) + 2 + (2 * bound + 4 + 6 * (bound + 1) * (bound + 1)) :=
  workSteps_le newer coordinate boundary bound hCoordinate hBoundary hNewer

example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input =
      6 * (2 * quadratic (3 * bound.eval input + 2) + 2 +
        (2 * bound.eval input + 4 + 6 * (bound.eval input + 1) * (bound.eval input + 1))) :=
  rawTimePolynomial_eval bound input

example (newer : List Nat) (coordinate boundary input : Nat) (bound : NatPolynomial)
    (hCoordinate : coordinate ≤ bound.eval input) (hBoundary : boundary ≤ bound.eval input)
    (hNewer : newer.length + newer.sum ≤ bound.eval input) :
    6 * workSteps newer coordinate boundary ≤ (rawTimePolynomial bound).eval input :=
  rawTimePolynomial_le newer coordinate boundary input bound hCoordinate hBoundary hNewer

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderConstraintRegionAssembly.finalValues problem index remaining =
      inputValues (Source.olderValues problem index remaining) [] (constraintIndex problem index)
        (termValue problem .shape) := Source.assembled_values_eq problem index remaining

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (Source.machine problem.verifier) (Source.workSteps problem index remaining)
      (workStartConfiguration (Source.machine problem.verifier)
        (BuilderCursorSource.cursorTape problem index remaining output)) =
      some (Source.finalConfiguration problem index remaining output) :=
  Source.workRunExact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (Source.machine problem.verifier)) (6 * Source.workSteps problem index remaining)
      (encodeWorkConfiguration (Source.initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (Source.finalConfiguration problem index remaining output) :=
  Source.run_compile_exact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    (Source.finalConfiguration problem index remaining output).state = (Source.machine problem.verifier).acceptState ↔
      constraintIndex problem index < termValue problem .shape := Source.final_accept_iff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    (Source.finalConfiguration problem index remaining output).state = (Source.machine problem.verifier).rejectState ↔
      termValue problem .shape ≤ constraintIndex problem index := Source.final_reject_iff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    (Source.finalConfiguration problem index remaining output).tape.right =
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration (constraintIndex problem index)
        (termValue problem .shape)).tape.left ++
        ((registerWord (BuilderConstraintRegionAssembly.finalValues problem index remaining)).reverse ++
          inside problem.input output) := Source.final_exterior_preserved problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    constraintIndex problem index ≤ (sourceSpan problem.verifier).eval problem.input.length ∧
      termValue problem .shape ≤ (sourceSpan problem.verifier).eval problem.input.length :=
  Source.source_values_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * Source.workSteps problem index remaining ≤ (Source.rawTimeBound problem.verifier).eval problem.input.length :=
  Source.rawTimeBound_le problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (Source.machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := Source.rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (Source.machine verifier) := Source.noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (Source.machine verifier).acceptState ≠ (Source.machine verifier).rejectState := Source.acceptState_ne_rejectState verifier

end PNP.Concrete.CookLevinBuilderRegionComparisonOperandsRegression

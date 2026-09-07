import PNP.Concrete.CookLevinBuilderRegionResidualOperands

namespace PNP.Concrete.CookLevinBuilderRegionResidualOperandsRegression

open CookLevin PipelineTape BuilderUnaryPolynomial
open BuilderRegionResidualOperands
open BuilderDividerOperands (endTape inside count quadratic)
open BuilderClauseDividerOperands (quotient)
open BuilderClauseDividerExecution (constraintIndex)
open BuilderConstraintRegionRegisters (termValue)
open BuilderDividerSourceExecution (sourceSpan)
open BuilderRegionComparisonOperands (inputValues prepareMachine)
open BuilderArbitrarySlotHeaderRouter

example (offset : Nat) :
    machine offset = WorkMachineChain.machine (prepareMachine offset) BuilderRegionResidualSelection.machine := rfl

example (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (machine offset) (workSteps newer coordinate boundary)
      (workStartConfiguration (machine offset) (endTape (inputValues older newer coordinate boundary) workspace [])) =
      some (finalConfiguration older newer coordinate boundary workspace) :=
  workRunExact offset older newer coordinate boundary workspace hLength

example (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset) :
    run (compileWorkMachine (machine offset)) (6 * workSteps newer coordinate boundary)
      (encodeWorkConfiguration (initialConfiguration offset older newer coordinate boundary workspace)) =
      encodeWorkConfiguration (finalConfiguration older newer coordinate boundary workspace) :=
  run_compile_exact offset older newer coordinate boundary workspace hLength

example (older newer : List Nat) (coordinate boundary : Nat) (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).tape =
      endTape (finalValues older newer coordinate boundary) workspace [] :=
  final_tape older newer coordinate boundary workspace

example (older newer : List Nat) (coordinate boundary : Nat) :
    finalValues older newer coordinate boundary =
      (inputValues older newer coordinate boundary ++
        BuilderRegionResidualRegisters.restoredValues (BuilderRegionResidualRegisters.ofComparison
          (RawRouter.compareResult 0 coordinate boundary))) ++
      [if coordinate < boundary then coordinate else coordinate - boundary] :=
  finalValues_eq older newer coordinate boundary

example (older newer : List Nat) (coordinate boundary : Nat) :
    (finalValues older newer coordinate boundary).length =
      (inputValues older newer coordinate boundary).length + 4 :=
  finalValues_length older newer coordinate boundary

example (coordinate boundary : Nat) :
    BuilderRegionResidualSelection.nextCoordinate coordinate boundary ≤ coordinate := nextCoordinate_le coordinate boundary

example (coordinate boundary bound : Nat) (hq : coordinate ≤ bound) (hb : boundary ≤ bound) :
    let values := BuilderRegionResidualSelection.scratchValues (RawRouter.compareResult 0 coordinate boundary)
    values.length + values.sum ≤ 4 + 4 * bound := scratch_size_le coordinate boundary bound hq hb

example (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat) (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).state = (machine offset).acceptState ↔
      coordinate < boundary := final_accept_iff offset older newer coordinate boundary workspace

example (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat) (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).state = (machine offset).rejectState ↔
      boundary ≤ coordinate := final_reject_iff offset older newer coordinate boundary workspace

example (older newer : List Nat) (coordinate boundary : Nat) (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).tape.right =
      (registerWord (BuilderRegionResidualSelection.scratchValues
        (RawRouter.compareResult 0 coordinate boundary))).reverse ++
      ((registerWord (inputValues older newer coordinate boundary)).reverse ++ workspace) :=
  final_exterior_preserved older newer coordinate boundary workspace

example (older newer : List Nat) (coordinate boundary : Nat) (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).tape.left = [] :=
  final_outer_empty older newer coordinate boundary workspace

example (offset : Nat) : (machine offset).rules.length = 9 * offset + 818 := rules_length offset
example (offset : Nat) : (machine offset).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct offset
example (offset : Nat) : WorkMachineChain.NoRuleAtAccept (machine offset) := noRuleAtAccept offset
example (offset : Nat) : WorkMachineProgramGraph.NoRuleAt (machine offset) (machine offset).rejectState :=
  noRuleAtReject offset
example (offset : Nat) : (machine offset).acceptState ≠ (machine offset).rejectState := acceptState_ne_rejectState offset

example (newer : List Nat) (coordinate boundary bound : Nat)
    (hq : coordinate ≤ bound) (hb : boundary ≤ bound) (hn : newer.length + newer.sum ≤ bound) :
    workSteps newer coordinate boundary ≤ workBound bound := workSteps_le newer coordinate boundary bound hq hb hn

example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := rawTimePolynomial_eval bound input

example (newer : List Nat) (coordinate boundary input : Nat) (bound : NatPolynomial)
    (hq : coordinate ≤ bound.eval input) (hb : boundary ≤ bound.eval input)
    (hn : newer.length + newer.sum ≤ bound.eval input) :
    6 * workSteps newer coordinate boundary ≤ (rawTimePolynomial bound).eval input :=
  rawTimePolynomial_le newer coordinate boundary input bound hq hb hn

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    Source.machine verifier = WorkMachineChain.machine (BuilderConstraintRegionAssembly.bodyMachine verifier)
      (machine 0) := rfl

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
    (Source.finalConfiguration problem index remaining output).tape =
      endTape (Source.finalValues problem index remaining) (inside problem.input output) [] :=
  Source.final_tape problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    Source.finalValues problem index remaining =
      (BuilderConstraintRegionAssembly.finalValues problem index remaining ++
        BuilderRegionResidualRegisters.restoredValues (BuilderRegionResidualRegisters.ofComparison
          (RawRouter.compareResult 0 (constraintIndex problem index) (termValue problem .shape)))) ++
      [if constraintIndex problem index < termValue problem .shape then constraintIndex problem index
        else constraintIndex problem index - termValue problem .shape] :=
  Source.finalValues_eq problem index remaining

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    (Source.finalConfiguration problem index remaining output).state = (Source.machine problem.verifier).acceptState ↔
      constraintIndex problem index < termValue problem .shape := Source.final_accept_iff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    (Source.finalConfiguration problem index remaining output).state = (Source.machine problem.verifier).rejectState ↔
      termValue problem .shape ≤ constraintIndex problem index := Source.final_reject_iff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * Source.workSteps problem index remaining ≤ (Source.rawTimeBound problem.verifier).eval problem.input.length :=
  Source.rawTimeBound_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    let values := BuilderRegionResidualSelection.scratchValues
      (RawRouter.compareResult 0 (constraintIndex problem index) (termValue problem .shape))
    values.length + values.sum ≤ 4 + 4 * (sourceSpan problem.verifier).eval problem.input.length :=
  Source.scratch_size_le problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (Source.machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := Source.rules_pairwise_query_distinct verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (Source.machine verifier) := Source.noRuleAtAccept verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (Source.machine verifier) (Source.machine verifier).rejectState :=
  Source.noRuleAtReject verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (Source.machine verifier).acceptState ≠ (Source.machine verifier).rejectState := Source.acceptState_ne_rejectState verifier

section LiteralExecutions
set_option maxRecDepth 4096

example : workSteps [] 0 0 = 51 := by decide
example : workSteps [] 1 1 = 103 := by decide
example : workSteps [0, 1] 1 2 = 173 := by decide
example : workSteps [0] 2 1 = 139 := by decide

example :
    workRunExact? (machine 0) 51 (initialConfiguration 0 [1] [] 0 0 [.oneBlank]) =
      some {
        state := (machine 0).rejectState
        tape := endTape [1, 0, 0, 0, 0, 0, 0] [.oneBlank] []
      } := by decide

example :
    workRunExact? (machine 0) 76 (initialConfiguration 0 [] [] 0 1 []) =
      some {
        state := (machine 0).acceptState
        tape := endTape [1, 0, 0, 0, 1, 0] [] []
      } := by decide

example :
    workRunExact? (machine 0) 73 (initialConfiguration 0 [] [] 1 0 []) =
      some {
        state := (machine 0).rejectState
        tape := endTape [0, 1, 1, 0, 0, 1] [] []
      } := by decide

example :
    workRunExact? (machine 0) 103 (initialConfiguration 0 [] [] 1 1 [.blank]) =
      some {
        state := (machine 0).rejectState
        tape := endTape [1, 1, 1, 0, 1, 0] [.blank] []
      } := by decide

example :
    workRunExact? (machine 2) 173 (initialConfiguration 2 [0] [0, 1] 1 2 [.zeroZero, .blankOne]) =
      some {
        state := (machine 2).acceptState
        tape := endTape [0, 2, 0, 1, 1, 1, 0, 2, 1] [.zeroZero, .blankOne] []
      } := by decide

example :
    workRunExact? (machine 1) 139 (initialConfiguration 1 [] [0] 2 1 [.zeroBlank]) =
      some {
        state := (machine 1).rejectState
        tape := endTape [1, 0, 2, 2, 0, 1, 1] [.zeroBlank] []
      } := by decide

example :
    workRunExact? (machine 0) 185 (initialConfiguration 0 [] [] 3 1 []) =
      some {
        state := (machine 0).rejectState
        tape := endTape [1, 3, 2, 1, 1, 2] [] []
      } := by decide

example :
    workRunExact? (machine 0) 50 (initialConfiguration 0 [1] [] 0 0 [.oneBlank]) ≠
      some (finalConfiguration [1] [] 0 0 [.oneBlank]) := by decide

example :
    workRunExact? (machine 0) 52 (initialConfiguration 0 [] [] 0 0 []) = none := by decide

example :
    workRunExact? (machine 0) 77 (initialConfiguration 0 [] [] 0 1 []) = none := by decide

example :
    workRunExact? (machine 0) (workSteps [1] 0 2) (initialConfiguration 0 [] [1] 0 2 []) ≠
      some (finalConfiguration [] [1] 0 2 []) := by decide

-- The total local symbol table first takes its explicit dead action.
-- Its next transition has no rule; rejection is not a zero-transition event.
example :
    workRunExact? (machine 0) 1
      (workStartConfiguration (machine 0) { left := [], head := .blank, right := [] }) =
      some {
        state := WorkMachineChain.firstState
          (WorkMachineChain.firstState (RegisterCopy.machine 0).rejectState)
        tape := { left := [], head := .blank, right := [] }
      } := by decide

example :
    workRunExact? (machine 0) 2
      (workStartConfiguration (machine 0) { left := [], head := .blank, right := [] }) = none := by decide

end LiteralExecutions
end PNP.Concrete.CookLevinBuilderRegionResidualOperandsRegression

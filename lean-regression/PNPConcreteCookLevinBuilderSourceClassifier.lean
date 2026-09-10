import PNP.Concrete.CookLevinBuilderSourceClassifier

namespace PNP.Concrete.CookLevinBuilderSourceClassifierRegression

open CookLevin CookLevin.BuilderSourceClassifier PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (count width)
open BuilderDividerSourceExecution (preservedWorkspace)
open BuilderArbitrarySlotHeaderRouter

example : tailMachine.rules.length = 243 := tail_rules_length
example : tailMachine.rules.Pairwise WorkMachineChain.QueryDistinct := tail_rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept tailMachine := tail_noRuleAtAccept
example : tailMachine.acceptState ≠ tailMachine.rejectState := tail_acceptState_ne_rejectState

example : tailSteps 2 1 2 1 2 = 96 := by decide
example : tailSteps 4 0 2 2 2 = 122 := by decide
example : tailSteps 0 0 2 0 0 = 20 := by decide

example :
    workRunExact? tailMachine 96 (tailInitial 2 1 2 1 2 [leftMarker, rightMarker, .oneBlank]) =
      some (tailFinal 2 1 2 1 2 [leftMarker, rightMarker, .oneBlank]) := by decide

example :
    workRunExact? tailMachine 122 (tailInitial 4 0 2 2 2 [rightMarker]) =
      some (tailFinal 4 0 2 2 2 [rightMarker]) := by decide

example :
    workRunExact? tailMachine 20 (tailInitial 0 0 2 0 0 []) =
      some (tailFinal 0 0 2 0 0 []) := by decide

example : (tailFinal 2 1 2 1 2 []).state = tailMachine.acceptState := by decide
example : (tailFinal 4 0 2 2 2 []).state = tailMachine.rejectState := by decide

/-- A beyond-count quotient is also non-body, but its tape is not the equal Finish tape. -/
example : (tailFinal 6 0 2 3 2 []).state = tailMachine.rejectState := by decide
example : tailFinal 6 0 2 3 2 [] ≠ tailFinal 4 0 2 2 2 [] := by decide

example (consumed remainder width quotient count : Nat) (workspace : List WorkSymbol) :
    workRunExact? tailMachine (tailSteps consumed remainder width quotient count)
        (tailInitial consumed remainder width quotient count workspace) =
      some (tailFinal consumed remainder width quotient count workspace) :=
  tail_workRunExact consumed remainder width quotient count workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderDividerSourceExecution.finalConfiguration problem index remaining output).tape =
      (tailInitial ((index / width problem) * width problem) (index % width problem)
        (width problem) (index / width problem) (count problem)
        (preservedWorkspace problem index remaining output)).tape :=
  divider_classifier_handoff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) :=
  workRunExact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compile_exact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state =
      WorkMachineChain.secondState (WorkMachineChain.secondState
        (RawRouter.finalConfiguration (index / width problem) (count problem)).state) :=
  finalConfiguration_state problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape.right =
      (RawRouter.finalConfiguration (index / width problem) (count problem)).tape.left ++
        tailExterior ((index / width problem) * width problem) (index % width problem)
          (width problem) (count problem) (preservedWorkspace problem index remaining output) :=
  final_workspace_preserved problem index remaining output

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  machine_acceptState_ne_rejectState verifier

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hIndex : index < BuilderFullScheduleCursorController.bodySlotCount problem) :
    RouteAgreement problem index remaining output := routeAgreement problem index remaining output hIndex

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hOutside : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index = .outOfRange) :
    ¬ RouteAgreement problem index remaining output := by
  intro hAgreement
  simp only [RouteAgreement, hOutside] at hAgreement

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  rawTimeBound_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language) :
    workRunExact? (fromRawMachine problem.verifier) (fromRawSteps problem)
        (fromRawInitial problem) = some (fromRawFinal problem) := fromRaw_workRunExact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (fromRawMachine problem.verifier)) (6 * fromRawSteps problem)
        (encodeWorkConfiguration (fromRawInitial problem)) =
      encodeWorkConfiguration (fromRawFinal problem) := fromRaw_run_compile_exact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    6 * fromRawSteps problem ≤ (fromRawTimeBound problem.verifier).eval problem.input.length :=
  fromRawTimeBound_le problem

example {language : Language} (problem : VerifierTableauProblem language) :
    match BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem 0 with
    | .body _ _ => (fromRawFinal problem).state = (fromRawMachine problem.verifier).acceptState
    | .finish => (fromRawFinal problem).state = (fromRawMachine problem.verifier).rejectState
    | .outOfRange => False := fromRaw_routeAgreement problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (fromRawInitial problem).tape = rawInputWorkTape problem.input := rfl

end PNP.Concrete.CookLevinBuilderSourceClassifierRegression

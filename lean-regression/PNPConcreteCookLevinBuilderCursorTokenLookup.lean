import PNP.Concrete.CookLevinBuilderCursorTokenLookup

namespace PNP.Concrete.CookLevin.BuilderCursorTokenLookupRegression

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape inside count width)
open BuilderClauseDividerOperands (quotient clauseWidth)
open BuilderClauseDividerExecution (clauseIndex constraintIndex)
open BuilderConstraintRegionRegisters (Region)
open BuilderRequestedPairLookup (BlankExterior)
open PipelineStateNamespace (renameConfiguration)
open BuilderCursorTokenLookup

/- Exact execution and invariant contracts. In particular the complete lookup
takes no supplied source, request, blank-exterior proof or polynomial bound. -/

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    BlankExterior (BuilderFamilyPayload.exterior problem index remaining region hRegion) :=
  BuilderCursorTokenLookup.family_exterior_blank problem index remaining region hRegion

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem) :
    BlankExterior (BuilderSourceTokenRequest.exterior problem index remaining hBody) :=
  BuilderCursorTokenLookup.source_exterior_blank problem index remaining hBody

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (request problem index).clauseIndex = (index / width problem) % clauseWidth problem ∧
      (request problem index).originalPosition = index % width problem :=
  BuilderCursorTokenLookup.request_coordinates problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem) :
    BuilderSourceTokenRequest.finalValues problem index remaining hBody =
      BuilderRequestDispatch.requestValues (problem.formulaConstraintSlotDirect (constraintIndex problem index))
        (request problem index) (BuilderSourcePayload.history problem index remaining hBody) :=
  BuilderCursorTokenLookup.source_request_layout problem index remaining hBody

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    canonicalResult problem index =
      (problem.formulaConstraintSlotDirect (constraintIndex problem index)).map
        (fun source => source.bind (fun constraint =>
          (constraint.emit[(index / width problem) % clauseWidth problem]?).bind
            (fun clause => (encodeClauseTokens (BoundedClause.emit clause))[index % width problem]?))) :=
  BuilderCursorTokenLookup.canonical_result_eq_emit problem index

example (state : Nat) : WorkMachineChain.secondState state = 3 * state + 1 :=
  BuilderCursorTokenLookup.second_state_code state

example (configuration : WorkConfiguration) :
    (renameConfiguration WorkMachineChain.secondState configuration).state % 3 = 1 :=
  BuilderCursorTokenLookup.token_stage_tag configuration

example (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderRequestTokenLookup.observe configuration :=
  BuilderCursorTokenLookup.observe_rename configuration

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderCursorTokenLookup.rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  BuilderCursorTokenLookup.noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  BuilderCursorTokenLookup.noRuleAtReject verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  BuilderCursorTokenLookup.acceptState_ne_rejectState verifier

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ steps final,
      workRunExact? (machine problem.verifier) steps (initialConfiguration problem index remaining output) = some final ∧
      final.state % 3 = 1 ∧
      WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) final.state ∧
      observe final = canonicalResult problem index ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤
        (inside problem.input output).length + (spanBound problem.verifier).eval problem.input.length ∧
      6 * steps ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  BuilderCursorTokenLookup.workRun_polynomial_lookup problem index remaining output hBody hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ rawSteps final,
      rawSteps ≤ (rawTimeBound problem.verifier).eval problem.input.length ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) = encodeWorkConfiguration final ∧
      final.state % 3 = 1 ∧
      WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) final.state ∧
      observe final = canonicalResult problem index ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤
        (inside problem.input output).length + (spanBound problem.verifier).eval problem.input.length :=
  BuilderCursorTokenLookup.uniform_polynomial_lookup problem index remaining output hBody hBalance

/- Independent coordinate, physical composition and outcome contracts. -/
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (request problem index).gap = BuilderSourceTokenRequest.gap problem index := rfl
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (request problem index).gap.length = 9 := (request problem index).gap_length
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (request problem index).clauseIndex = BuilderClauseDividerExecution.clauseIndex problem index := rfl
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (request problem index).originalPosition = BuilderSourceTokenRequest.tokenPosition problem index := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    machine verifier = WorkMachineChain.machine (BuilderSourceTokenRequest.machine verifier) BuilderRequestDispatch.machine := rfl
example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (output : List CNFToken) :
    initialConfiguration problem index remaining output =
      workStartConfiguration (machine problem.verifier) (BuilderCursorSource.cursorTape problem index remaining output) := rfl
example (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) = BuilderRequestTokenLookup.observe configuration :=
  BuilderCursorTokenLookup.observe_rename configuration
example (tape : WorkTape) :
    observe (renameConfiguration WorkMachineChain.secondState {state := 0,tape := tape}) = some (some .t) := by
  rw [BuilderCursorTokenLookup.observe_rename,BuilderRequestTokenLookup.observe_true]
example (tape : WorkTape) :
    observe (renameConfiguration WorkMachineChain.secondState {state := 1,tape := tape}) = some (some .f) := by
  rw [BuilderCursorTokenLookup.observe_rename,BuilderRequestTokenLookup.observe_false]
example (tape : WorkTape) :
    observe (renameConfiguration WorkMachineChain.secondState {state := 2,tape := tape}) = some none := by
  rw [BuilderCursorTokenLookup.observe_rename,BuilderRequestTokenLookup.observe_padding]
example (tape : WorkTape) :
    observe (renameConfiguration WorkMachineChain.secondState {state := BuilderRequestTokenLookup.missingState,tape := tape}) = none := by
  rw [BuilderCursorTokenLookup.observe_rename,BuilderRequestTokenLookup.observe_missing]
example (configuration : WorkConfiguration) (hWrongStage : configuration.state % 3 ≠ 1) :
    observe configuration = none := by
  simp only [observe,if_neg hWrongStage]
example (tape : WorkTape) : observe {state := 0,tape := tape} = none := rfl
example (state : Nat) : WorkMachineChain.secondState state / 3 = state := by
  rw [second_state_code]
  omega
example {language : Language} (verifier : PolynomialTimeVerifier language) (input : Nat) :
    (rawTimeBound verifier).eval input =
      (BuilderSourceTokenRequest.rawTimeBound verifier).eval input + 6 +
      (BuilderRequestTokenLookup.rawTimePolynomial (BuilderSourceTokenRequest.spanBound verifier)).eval input := by
  rw [rawTimeBound,NatPolynomial.eval_add,NatPolynomial.eval_add,NatPolynomial.eval_constant]
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    spanBound verifier = BuilderRequestTokenLookup.spanPolynomial (BuilderSourceTokenRequest.spanBound verifier) := rfl
example (configuration : WorkConfiguration) :
    (renameConfiguration WorkMachineChain.secondState configuration).tape = configuration.tape := rfl

end PNP.Concrete.CookLevin.BuilderCursorTokenLookupRegression

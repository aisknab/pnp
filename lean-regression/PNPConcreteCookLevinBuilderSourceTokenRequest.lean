import PNP.Concrete.CookLevinBuilderSourceTokenRequest

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderSourceTokenRequest PipelineTape BuilderUnaryPolynomial
open BuilderArbitrarySlotHeaderRouter
open BuilderDividerOperands (endTape inside count width)
open BuilderClauseDividerOperands (quotient clauseWidth)
open BuilderClauseDividerExecution (clauseIndex constraintIndex)

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) :
    sourceValues problem index remaining hBody =
      indexBefore problem index remaining ++ [index, width problem, quotient problem index] ++
        commonAfter problem index remaining hBody:=
  BuilderSourceTokenRequest.source_layout problem index remaining hBody

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) (field : Field) :
    sourceValues problem index remaining hBody =
      fieldBefore problem index remaining field ++ [fieldValue problem index field] ++
        fieldAfter problem index remaining hBody field:=
  BuilderSourceTokenRequest.field_layout problem index remaining hBody field

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (field : Field) :
    (fieldBefore problem index remaining field).length = fieldOrdinal problem.verifier field:=
  BuilderSourceTokenRequest.field_before_length problem index remaining field

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) (field : Field) (extra : List Nat)
    (output : List CNFToken) (outside : List WorkSymbol) :
    workRunExact? (fieldMachine problem.verifier field) (fieldSteps problem index remaining hBody field extra)
      (workStartConfiguration (fieldMachine problem.verifier field)
        (endTape (sourceValues problem index remaining hBody ++ extra) (inside problem.input output) outside)) =
      some {
        state := (fieldMachine problem.verifier field).acceptState
        tape := endTape (sourceValues problem index remaining hBody ++ extra ++ [fieldValue problem index field])
          (inside problem.input output) (outside.drop (fieldValue problem index field + 1)) }:=
  BuilderSourceTokenRequest.field_workRunExact problem index remaining hBody field extra output outside

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) (field : Field) (extra : List Nat) (outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (sourceValues problem index remaining hBody ++ extra)).length + outside.length ≤ bound.eval input) :
    (registerWord (sourceValues problem index remaining hBody ++ extra ++ [fieldValue problem index field])).length +
        (outside.drop (fieldValue problem index field + 1)).length ≤ (BuilderRegisterRootCopy.spanPolynomial bound).eval input ∧
      6 * fieldSteps problem index remaining hBody field extra ≤ (BuilderRegisterRootCopy.rawTimePolynomial bound).eval input:=
  BuilderSourceTokenRequest.field_polynomial_bounds problem index remaining hBody field extra outside bound input hSpan

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    tokenPosition problem index + consumed problem index = index:=
  BuilderSourceTokenRequest.token_reconstruction problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    BuilderRegisterCompareResidual.resultCoordinate (comparisonResult problem index) = tokenPosition problem index:=
  BuilderSourceTokenRequest.comparison_residual problem index

example (coordinate boundary : Nat) (older : List Nat) (inner outer : List WorkSymbol) :
    workRunExact? compareMachine (BuilderRegisterCompareResidual.workSteps coordinate boundary + 1)
      (workStartConfiguration compareMachine (endTape (older ++ [coordinate, boundary]) inner outer)) =
      some {
        state := compareMachine.acceptState
        tape := endTape (older ++ BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 coordinate boundary))
          inner (outer.drop (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 coordinate boundary))) }:=
  BuilderSourceTokenRequest.compare_workRunExact coordinate boundary older inner outer

example (position clause : Nat) : List.ofFn (suffixEnvironment position clause) = [position,clause]:=
  BuilderSourceTokenRequest.suffix_environment_values position clause

example (position clause : Nat) :
    BuilderRegisterExpression.values suffixExpression (suffixEnvironment position clause) = [position]:=
  BuilderSourceTokenRequest.suffix_expression_values position clause

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    BuilderRegisterCompareResidual.outputValues (comparisonResult problem index) =
      (BuilderRegisterLessThan.resultValues (comparisonResult problem index) ++ [consumed problem index]) ++ [tokenPosition problem index]:=
  BuilderSourceTokenRequest.comparison_output_suffix problem index

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining hBody)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output hBody):=
  BuilderSourceTokenRequest.workRunExact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hBody)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output hBody):=
  BuilderSourceTokenRequest.run_compile_exact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    (finalConfiguration problem index remaining output hBody).tape =
      endTape (finalValues problem index remaining hBody) (inside problem.input output) (exterior problem index remaining hBody):=
  BuilderSourceTokenRequest.final_tape problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (gap problem index).length = 9:=
  BuilderSourceTokenRequest.gap_length problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (request problem index).length = 2:=
  BuilderSourceTokenRequest.request_length problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    request problem index =
      [(index / width problem) % clauseWidth problem,index % width problem]:=
  BuilderSourceTokenRequest.request_value problem index

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) :
    finalValues problem index remaining hBody =
      BuilderSourcePayload.history problem index remaining hBody ++
        BuilderLocalConstraintPayload.values (problem.formulaConstraintSlotDirect (constraintIndex problem index)) ++
        gap problem index ++ request problem index:=
  BuilderSourceTokenRequest.final_request_layout problem index remaining hBody

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct:=
  BuilderSourceTokenRequest.rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier):=
  BuilderSourceTokenRequest.noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState:=
  BuilderSourceTokenRequest.noRuleAtReject verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState:=
  BuilderSourceTokenRequest.acceptState_ne_rejectState verifier

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining hBody)).length + (exterior problem index remaining hBody).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hBody ≤ (rawTimeBound problem.verifier).eval problem.input.length:=
  BuilderSourceTokenRequest.source_polynomial_bounds problem index remaining hBody hBalance

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ rawSteps, rawSteps ≤ (rawTimeBound problem.verifier).eval problem.input.length ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
        encodeWorkConfiguration (finalConfiguration problem index remaining output hBody) ∧
      (finalConfiguration problem index remaining output hBody).tape =
        endTape (BuilderSourcePayload.history problem index remaining hBody ++
          BuilderLocalConstraintPayload.values (problem.formulaConstraintSlotDirect (constraintIndex problem index)) ++
          gap problem index ++ [(index / width problem) % clauseWidth problem,index % width problem])
          (inside problem.input output) (exterior problem index remaining hBody) ∧
      (registerWord (finalValues problem index remaining hBody)).length + (exterior problem index remaining hBody).length ≤
        (spanBound problem.verifier).eval problem.input.length:=
  BuilderSourceTokenRequest.uniform_source_request problem index remaining output hBody hBalance

-- Independent source/request, fixed-frame and arithmetic boundary contracts.
example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    (initialConfiguration problem index remaining output).tape =
      BuilderCursorSource.cursorTape problem index remaining output := rfl

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    fieldValue problem index .index = index := rfl
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    fieldValue problem index .width = width problem := rfl
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    fieldValue problem index .quotient = index / width problem := rfl
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    fieldValue problem index .clause = (index / width problem) % clauseWidth problem := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    fieldOrdinal verifier .width = fieldOrdinal verifier .index + 1 := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    fieldOrdinal verifier .quotient = fieldOrdinal verifier .index + 2 := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    fieldOrdinal verifier .clause = BuilderSourceClauseCoordinate.rootOrdinal verifier := rfl

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (extra problem index 6).length = 8 := by
  simp only [extra, List.length_append, BuilderRegisterCompareResidual.outputValues_length,
    List.length_cons, List.length_nil]
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (extra problem index 7).length = 9 := by
  simp only [extra, List.length_append, BuilderRegisterCompareResidual.outputValues_length,
    List.length_cons, List.length_nil]
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (extra problem index 8).length = 10 := by
  simp only [extra, List.length_append, BuilderRegisterCompareResidual.outputValues_length,
    List.length_cons, List.length_nil]

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    stepMachine verifier 0 = fieldMachine verifier .width := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    stepMachine verifier 1 = fieldMachine verifier .quotient := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    stepMachine verifier 2 = RegisterBinary.machine .mul 0 := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    stepMachine verifier 3 = fieldMachine verifier .index := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    stepMachine verifier 4 = BuilderRegisterExpression.machine suffixExpression 0 := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    stepMachine verifier 5 = compareMachine := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    stepMachine verifier 6 = fieldMachine verifier .clause := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    stepMachine verifier 7 = BuilderRegisterExpression.machine suffixExpression 0 := rfl

example : BuilderRegisterCompareResidual.resultCoordinate (RawRouter.compareResult 0 0 0) = 0 := by decide
example : BuilderRegisterCompareResidual.resultCoordinate (RawRouter.compareResult 0 12 12) = 0 := by decide
example : BuilderRegisterCompareResidual.resultCoordinate (RawRouter.compareResult 0 12 17) = 12 := by decide
example : BuilderRegisterCompareResidual.resultCoordinate (RawRouter.compareResult 0 17 12) = 5 := by decide
example : BuilderRegisterCompareResidual.resultCoordinate (RawRouter.compareResult 0 0 5) = 0 := by decide
example : List.ofFn (suffixEnvironment 0 3) = [0,3] := rfl
example : BuilderRegisterExpression.values suffixExpression (suffixEnvironment 5 3) = [5] := rfl

import PNP.Concrete.CookLevinBuilderControlLiteralSources

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderControlLiteralSources
open BuilderUnaryPolynomial (registerWord)

example : kind .currentState = .state := rfl
example : kind .currentHead = .head := rfl
example : kind .currentRead = .symbol := rfl
example : kind .nextState = .state := rfl
example : kind .nextHead = .head := rfl
example : kind .nextWrite = .symbol := rfl
example : kind .nextWrite ≠ .head := by decide
example : plan .nextHead 0 ⟨1, by decide⟩ = .retained ⟨11, by decide⟩ := rfl
example : plan .nextState 0 ⟨2, by decide⟩ = .retained ⟨5, by decide⟩ := rfl
example : plan .nextWrite 0 ⟨3, by decide⟩ = .retained ⟨6, by decide⟩ := rfl
example (extraCount : Nat) : plan .nextState extraCount ⟨0, by decide⟩ = .retained ⟨14, by omega⟩ := rfl

section Universal
variable {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
variable (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control)

example (role : Role) : (request role (BuilderControlCoordinates.ofSource problem index hRegion)).kind = kind role :=
  request_kind role _
example : (preparedValues problem index hRegion).length = 15 := preparedValues_length problem index hRegion
example : preparedValues problem index hRegion = canonicalValues (BuilderControlCoordinates.ofSource problem index hRegion) :=
  prepared_canonical problem index hRegion
example (extraCount : Nat) (extra : List Nat) (role : Role) :
    BuilderLiteralArgumentSource.argumentEnvironment problem index .control
      (preparedValues problem index hRegion ++ extra) (plan role extraCount) =
      (request role (BuilderControlCoordinates.ofSource problem index hRegion)).environment :=
  argument_environment problem index extraCount extra role hRegion
example (extraCount : Nat) (extra : List Nat) (role : Role) :
    BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression (kind role))
      (BuilderLiteralArgumentSource.argumentEnvironment problem index .control
        (preparedValues problem index hRegion ++ extra) (plan role extraCount)) =
      (request role (BuilderControlCoordinates.ofSource problem index hRegion)).index :=
  index_eq problem index extraCount extra role hRegion
example : BuilderRegisterExpression.values (timeExpression problem.verifier)
    (BuilderLiteralArgumentSource.environment problem index remaining .control 12
      (BuilderControlHeadSource.finalRetainedValues problem index hRegion)) = timeValues problem index :=
  time_expression_values problem index remaining hRegion

example (inside outside : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining hRegion)
      (initialConfiguration problem index remaining inside outside) =
      some (finalConfiguration problem index remaining inside outside hRegion) :=
  workRunExact problem index remaining inside outside hRegion
example (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hRegion)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside outside hRegion) :=
  run_compile_exact problem index remaining inside outside hRegion

example (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining hRegion)).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hRegion ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hBody hBalance hRegion
example (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (preparedValues problem index hRegion)).length ≤ (spanBound problem.verifier).eval problem.input.length :=
  retained_span_le problem index remaining hBody hBalance hRegion
example (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.right =
      (registerWord (finalValues problem index remaining hRegion)).reverse ++ inside :=
  final_inside_preserved problem index remaining inside outside hRegion
example (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.left =
      finalOutside problem index outside hRegion := final_exterior_accounted problem index remaining inside outside hRegion

example (role : Role) : (literalWrittenValues problem index role hRegion).length = literalCount role :=
  literalWrittenValues_length problem index role hRegion
example (role : Role) : ∃ leadingValues, literalWrittenValues problem index role hRegion =
    leadingValues ++ [(request role (BuilderControlCoordinates.ofSource problem index hRegion)).index] :=
  literalWrittenValues_end problem index role hRegion
example (role : Role) : (firstLiteralRetained problem index role hRegion).length = 15 + literalCount role :=
  firstLiteralRetained_length problem index role hRegion
example (role : Role) (inside outside : List WorkSymbol) :
    workRunExact? (firstLiteralMachine problem.verifier role) (firstLiteralSteps problem index remaining role hRegion)
      (firstLiteralInitial problem index remaining role inside outside) =
      some (firstLiteralFinal problem index remaining role inside outside hRegion) :=
  firstLiteral_workRunExact problem index remaining role inside outside hRegion
example (role : Role) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (firstLiteralMachine problem.verifier role)) (6 * firstLiteralSteps problem index remaining role hRegion)
      (encodeWorkConfiguration (firstLiteralInitial problem index remaining role inside outside)) =
      encodeWorkConfiguration (firstLiteralFinal problem index remaining role inside outside hRegion) :=
  firstLiteral_run_compile_exact problem index remaining role inside outside hRegion
example (role : Role)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (firstLiteralValues problem index remaining role hRegion)).length ≤
        (firstLiteralSpanBound problem.verifier role).eval problem.input.length ∧
      6 * firstLiteralSteps problem index remaining role hRegion ≤
        (firstLiteralRawTimeBound problem.verifier role).eval problem.input.length :=
  firstLiteral_source_polynomial_bounds problem index remaining role hBody hBalance hRegion
end Universal

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState := noRuleAtReject verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := acceptState_ne_rejectState verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) :
    (firstLiteralMachine verifier role).rules.Pairwise WorkMachineChain.QueryDistinct :=
  firstLiteral_rules_pairwise_query_distinct verifier role
example {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) :
    WorkMachineChain.NoRuleAtAccept (firstLiteralMachine verifier role) := firstLiteral_noRuleAtAccept verifier role
example {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) :
    WorkMachineProgramGraph.NoRuleAt (firstLiteralMachine verifier role) (firstLiteralMachine verifier role).rejectState :=
  firstLiteral_noRuleAtReject verifier role
example {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) :
    (firstLiteralMachine verifier role).acceptState ≠ (firstLiteralMachine verifier role).rejectState :=
  firstLiteral_acceptState_ne_rejectState verifier role

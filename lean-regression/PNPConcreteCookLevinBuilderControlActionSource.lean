import PNP.Concrete.CookLevinBuilderControlActionSource

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderControlActionSource

example : moveCode .stay = 0 := rfl
example : moveCode .left = 1 := rfl
example : moveCode .right = 2 := rfl

section Universal
variable {language : Language} (problem : VerifierTableauProblem language)

example : stateCount problem.verifier = problem.dimensions.stateBound := stateCount_eq problem
example (state : Fin problem.dimensions.stateBound) (symbol : TapeSymbol) :
    rowValues (fixedProblem problem.verifier) state symbol = rowValues problem state symbol :=
  rowValues_input_independent problem state symbol
example (state : Fin problem.dimensions.stateBound) (symbol : TapeSymbol) :
    (rowValues problem state symbol).length = 3 := rowValues_length problem state symbol
example : (table problem.verifier).length = stateCount problem.verifier * 3 := table_length problem.verifier
example (state : Fin problem.dimensions.stateBound) (code : Fin 3) :
    state.val * 3 + code.val < (table problem.verifier).length := key_lt problem state code
example (state : Fin problem.dimensions.stateBound) (code : Fin 3) :
    (table problem.verifier)[state.val * 3 + code.val]'(key_lt problem state code) =
      rowValues problem state (BuilderControlCoordinates.symbol code) := table_at problem state code
example (state : Fin problem.dimensions.stateBound) (symbol : TapeSymbol) :
    rowValues problem state symbol =
      [(problem.localAction state symbol).targetState.val,
        VariableLayout.tapeSymbolCode (problem.localAction state symbol).writeSymbol,
        moveCode (problem.localAction state symbol).move] := rfl

variable (index remaining : Nat)
example : BuilderRegisterExpression.values (keyExpression problem.verifier)
    (BuilderLiteralArgumentSource.environment problem index remaining .control 0 []) = keyValues problem index :=
  key_expression_values problem index remaining
example : keyValues problem index =
    [stateValue problem index, 3, stateValue problem index * 3, symbolValue problem index,
      stateValue problem index * 3 + symbolValue problem index] := rfl
example : (keyValues problem index).length = 5 := keyValues_length problem index
example (inside outside : List WorkSymbol) :
    workRunExact? (BuilderRegisterExpression.machine (keyExpression problem.verifier) 0)
      (keySteps problem index remaining)
      (workStartConfiguration (BuilderRegisterExpression.machine (keyExpression problem.verifier) 0)
        (endTape (frame problem index remaining) inside outside)) =
      some {
        state := (BuilderRegisterExpression.machine (keyExpression problem.verifier) 0).acceptState
        tape := endTape (frame problem index remaining ++ keyValues problem index) inside
          (outside.drop (registerWord (keyValues problem index)).length) } :=
  key_workRunExact problem index remaining inside outside

variable (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control)
example : stateValue problem index = (BuilderControlCoordinates.ofSource problem index hRegion).state.val ∧
    symbolValue problem index = (BuilderControlCoordinates.ofSource problem index hRegion).readCode.val :=
  source_values problem index hRegion
example : keyValue problem index < (table problem.verifier).length := source_key_lt problem index hRegion
example : selectedValues problem index =
    rowValues problem (BuilderControlCoordinates.ofSource problem index hRegion).state
      (BuilderControlCoordinates.symbol (BuilderControlCoordinates.ofSource problem index hRegion).readCode) :=
  selected_canonical problem index hRegion
example : (selectedValues problem index).length = 3 := by
  rw [selected_canonical problem index hRegion]
  rfl
example : finalValues problem index remaining =
    frame problem index remaining ++ keyValues problem index ++
      rowValues problem (BuilderControlCoordinates.ofSource problem index hRegion).state
        (BuilderControlCoordinates.symbol (BuilderControlCoordinates.ofSource problem index hRegion).readCode) := by
  rw [finalValues, selected_canonical problem index hRegion]
example (inside outside : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside outside) =
      some (finalConfiguration problem index remaining inside outside) :=
  workRunExact problem index remaining inside outside hRegion
example (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside outside) :=
  run_compile_exact problem index remaining inside outside hRegion

example (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining)).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hBody hBalance hRegion
example (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside outside).tape.left.length ≤ outside.length :=
  final_exterior_length_le problem index remaining inside outside
example (outside : List WorkSymbol) :
    finalOutside problem index outside =
      outside.drop ((registerWord (keyValues problem index)).length +
        BuilderRegisterTable.rowSpan (selectedValues problem index)) := rfl
example : finalOutside problem index [] = [] := by
  simp only [finalOutside, List.drop_nil]
end Universal

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState := noRuleAtReject verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := acceptState_ne_rejectState verifier

import PNP.Concrete.CookLevinBuilderExclusionPairPreparation

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderExclusionPairSelection (reverseCoordinate)
open LocalConstraint (pairCount)
open BuilderExclusionPairPreparation

example (count : Nat) : product count = 2 * (pairCount count + count) :=
  BuilderExclusionPairPreparation.product_twice count

example (count : Nat) : quotient count = pairCount count + count :=
  BuilderExclusionPairPreparation.quotient_eq count

example (count coordinate : Nat) :
    boundary count coordinate ≤ quotient count ↔ coordinate < pairCount count :=
  BuilderExclusionPairPreparation.valid_iff count coordinate

example (count coordinate : Nat) :
    quotient count < boundary count coordinate ↔ pairCount count ≤ coordinate :=
  BuilderExclusionPairPreparation.invalid_iff count coordinate

example (count coordinate : Nat) (hValid : coordinate < pairCount count) : 2 ≤ count :=
  BuilderExclusionPairPreparation.valid_count count coordinate hValid

example (count coordinate : Nat) (hValid : coordinate < pairCount count) :
    quotient count - boundary count coordinate = reverseCoordinate count coordinate :=
  BuilderExclusionPairPreparation.valid_residual count coordinate hValid

example (count coordinate : Nat) :
    List.ofFn (inputEnvironment count coordinate) = [count, coordinate] :=
  BuilderExclusionPairPreparation.inputEnvironment_ofFn count coordinate

example (count coordinate : Nat) :
    [count, coordinate] ++ BuilderRegisterExpression.values productExpression (inputEnvironment count coordinate) =
      rootValues count coordinate ++ [product count] :=
  BuilderExclusionPairPreparation.product_values count coordinate

example (count coordinate : Nat) :
    List.ofFn (halvedEnvironment count coordinate) = halvedValues count coordinate :=
  BuilderExclusionPairPreparation.halvedEnvironment_ofFn count coordinate

example (count coordinate : Nat) :
    halvedValues count coordinate ++
      BuilderRegisterExpression.values boundaryExpression (halvedEnvironment count coordinate) =
        arithmeticValues count coordinate :=
  BuilderExclusionPairPreparation.boundary_values count coordinate

example (count coordinate : Nat) :
    List.ofFn (arithmeticEnvironment count coordinate) = arithmeticValues count coordinate :=
  BuilderExclusionPairPreparation.arithmeticEnvironment_ofFn count coordinate

example (count coordinate : Nat) :
    BuilderRegisterPack.values comparisonFields (arithmeticEnvironment count coordinate) =
      [quotient count, boundary count coordinate] :=
  BuilderExclusionPairPreparation.comparison_values count coordinate

example (count coordinate : Nat) : (history count coordinate).length = 25 :=
  BuilderExclusionPairPreparation.history_length count coordinate

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps count coordinate) (initialConfiguration count coordinate older inside) =
      some (finalConfiguration count coordinate older inside) :=
  BuilderExclusionPairPreparation.workRunExact count coordinate older inside

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps count coordinate)
      (encodeWorkConfiguration (initialConfiguration count coordinate older inside)) =
      encodeWorkConfiguration (finalConfiguration count coordinate older inside) :=
  BuilderExclusionPairPreparation.run_compile_exact count coordinate older inside

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).state = machine.rejectState ↔
      coordinate < pairCount count :=
  BuilderExclusionPairPreparation.final_valid_iff count coordinate older inside

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).state = machine.acceptState ↔
      pairCount count ≤ coordinate :=
  BuilderExclusionPairPreparation.final_invalid_iff count coordinate older inside

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).tape =
      endTape (older ++ history count coordinate) inside [] :=
  BuilderExclusionPairPreparation.final_tape count coordinate older inside

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).tape.left = [] :=
  BuilderExclusionPairPreparation.final_frontier count coordinate older inside

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  BuilderExclusionPairPreparation.rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  BuilderExclusionPairPreparation.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderExclusionPairPreparation.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState :=
  BuilderExclusionPairPreparation.acceptState_ne_rejectState

example (count coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [count, coordinate])).length ≤ bound.eval inputLength) :
    (registerWord (older ++ history count coordinate)).length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps count coordinate ≤ (rawTimePolynomial bound).eval inputLength :=
  BuilderExclusionPairPreparation.source_polynomial_bounds count coordinate older bound inputLength hSpan

example : product 0 = 0 := rfl
example : quotient 0 = 0 := rfl
example : quotient 1 = 1 := rfl
example : quotient 4 = 10 := rfl
example : quotient 100 = 5050 := by decide
example : quotient 0 < boundary 0 0 := by decide
example : quotient 1 < boundary 1 0 := by decide
example : boundary 2 0 = quotient 2 := rfl
example : quotient 2 < boundary 2 1 := by decide
example : boundary 4 0 < quotient 4 := by decide
example : boundary 4 5 = quotient 4 := rfl
example : quotient 4 < boundary 4 6 := by decide
example : quotient 4 < boundary 4 100 := by decide
example : boundary 100 4949 = quotient 100 := by decide
example : quotient 4 - boundary 4 0 = 5 := rfl
example : quotient 4 - boundary 4 5 = 0 := rfl
example : arithmeticValues 4 5 =
    [4, 5, 4, 4, 1, 5, 20, 0, 0, 20, 0, 2, 10, 10, 0, 4, 5, 9, 1, 10] := rfl
example : BuilderRegisterPack.values comparisonFields (arithmeticEnvironment 4 5) = [10, 10] := rfl
example : BuilderRegisterPack.values comparisonFields (arithmeticEnvironment 4 6) = [10, 11] := rfl
example : (history 4 0).length = 25 := history_length 4 0
example : (finalConfiguration 4 5 [7, 8] []).state = machine.rejectState :=
  (final_valid_iff 4 5 [7, 8] []).mpr (by decide)
example : (finalConfiguration 4 6 [7, 8] []).state = machine.acceptState :=
  (final_invalid_iff 4 6 [7, 8] []).mpr (by decide)

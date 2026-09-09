import PNP.Concrete.CookLevinBuilderExclusionClauseBoundary

open PNP.Concrete PNP.Concrete.CookLevin
open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open BuilderExclusionPairLiteralTokens (frame environment environment_values initialValues)
open BuilderRegisterExpression (Expr)
open PipelineStateNamespace (renameConfiguration)
open BuilderExclusionClauseBoundary

example (first second : Nat) : 0 < boundary first second := by
  apply BuilderExclusionClauseBoundary.boundary_positive <;> assumption

example (first second position : Nat) (retained : List Nat) (hRetained : retained.length = 11) :
    BuilderRegisterExpression.values boundaryExpression (environment first second position retained hRetained) =
      boundaryValues first second := by
  apply BuilderExclusionClauseBoundary.boundary_values <;> assumption

example : BuilderRegisterExpression.nodeCount boundaryExpression = 5 := by
  apply BuilderExclusionClauseBoundary.boundary_nodeCount <;> assumption

example (first second : Nat) : (boundaryValues first second).length = 5 := by
  apply BuilderExclusionClauseBoundary.boundaryValues_length <;> assumption

example (first second position : Nat) (retained : List Nat) (hRetained : retained.length = 11) :
    BuilderRegisterExpression.values positionExpression (environment first second position retained hRetained) = [position] := by
  apply BuilderExclusionClauseBoundary.position_values <;> assumption

example (first second position : Nat) : (scratch first second position).length = 9 := by
  apply BuilderExclusionClauseBoundary.scratch_length <;> assumption

example (first second position : Nat) (retained older : List Nat) :
    finalValues first second position retained older =
      initialValues first second position retained older ++ scratch first second position := by
  apply BuilderExclusionClauseBoundary.final_values_layout <;> assumption

example (first second position : Nat) (hInside : position ≤ boundary first second) :
    BuilderRegisterCompareResidual.resultCoordinate (result first second position) =
      boundary first second - position := by
  apply BuilderExclusionClauseBoundary.residual_eq <;> assumption

example (first second position : Nat) (retained older : List Nat)
    (hInside : position ≤ boundary first second) :
    finalValues first second position retained older =
      (initialValues first second position retained older ++ boundaryPrefix first second ++
        BuilderRegisterLessThan.resultValues (result first second position) ++ [position]) ++
        [boundary first second - position] := by
  apply BuilderExclusionClauseBoundary.residual_suffix <;> assumption

example (first second position : Nat) (retained older : List Nat)
    (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    workRunExact? prepareMachine (prepareSteps first second position retained hRetained)
      (workStartConfiguration prepareMachine (endTape (initialValues first second position retained older) inside outside)) =
      some {
        state := prepareMachine.acceptState
        tape := endTape (preparedValues first second position retained older) inside
          (prepareOutside first second position outside) } := by
  apply BuilderExclusionClauseBoundary.prepare_workRunExact <;> assumption

example (first second position : Nat) (retained older : List Nat)
    (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps first second position retained hRetained)
      (initialConfiguration first second position retained older inside outside) =
      some (finalConfiguration first second position retained older inside outside) := by
  apply BuilderExclusionClauseBoundary.workRunExact <;> assumption

example (first second position : Nat) (retained older : List Nat)
    (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps first second position retained hRetained)
      (encodeWorkConfiguration (initialConfiguration first second position retained older inside outside)) =
      encodeWorkConfiguration (finalConfiguration first second position retained older inside outside) := by
  apply BuilderExclusionClauseBoundary.run_compile_exact <;> assumption

example (first second position : Nat) (retained older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration first second position retained older inside outside).tape =
      endTape (finalValues first second position retained older) inside (finalOutside first second position outside) := by
  apply BuilderExclusionClauseBoundary.final_tape <;> assumption

example (first second position : Nat) (retained older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration first second position retained older inside outside).state = machine.acceptState ↔
      boundary first second < position := by
  apply BuilderExclusionClauseBoundary.final_accept_iff <;> assumption

example (first second position : Nat) (retained older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration first second position retained older inside outside).state = machine.rejectState ↔
      position ≤ boundary first second := by
  apply BuilderExclusionClauseBoundary.final_reject_iff <;> assumption

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := by
  apply BuilderExclusionClauseBoundary.rules_pairwise_query_distinct <;> assumption

example : WorkMachineChain.NoRuleAtAccept machine := by
  apply BuilderExclusionClauseBoundary.noRuleAtAccept <;> assumption

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := by
  apply BuilderExclusionClauseBoundary.noRuleAtReject <;> assumption

example : machine.acceptState ≠ machine.rejectState := by
  apply BuilderExclusionClauseBoundary.acceptState_ne_rejectState <;> assumption

example (first second position : Nat) (retained older : List Nat)
    (hRetained : retained.length = 11) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues first second position retained older)).length ≤ bound.eval input) :
    (registerWord (preparedValues first second position retained older)).length ≤ (preparedSpanPolynomial bound).eval input ∧
      6 * prepareSteps first second position retained hRetained ≤ (prepareRawTimePolynomial bound).eval input := by
  apply BuilderExclusionClauseBoundary.prepare_polynomial_bounds <;> assumption

example (first second position : Nat) (retained older : List Nat)
    (hRetained : retained.length = 11) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues first second position retained older)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues first second position retained older)).length +
        (finalOutside first second position outside).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps first second position retained hRetained ≤ (rawTimePolynomial bound).eval input := by
  apply BuilderExclusionClauseBoundary.source_polynomial_bounds <;> assumption

example : boundary 0 0 = 5 := rfl
example : boundary 0 2 = 7 := rfl
example : boundary 7 2 = 14 := rfl
example : boundary 2 7 = 14 := rfl
example : boundary 2 2 = 9 := rfl
example : boundaryValues 7 2 = [7,2,9,5,14] := rfl
example : BuilderRegisterExpression.values boundaryExpression
    (environment 7 2 20 (List.replicate 11 99) (by decide)) = [7,2,9,5,14] := rfl
example : BuilderRegisterExpression.values positionExpression
    (environment 7 2 20 (List.replicate 11 99) (by decide)) = [20] := rfl
example : BuilderRegisterCompareResidual.resultCoordinate (result 0 2 6) = 1 := rfl
example : BuilderRegisterCompareResidual.resultCoordinate (result 0 2 7) = 0 := rfl
example : BuilderRegisterCompareResidual.resultCoordinate (result 0 2 8) = 7 := rfl
example : (scratch 0 2 7).length = 9 := rfl
example : (scratch 0 2 20).length = 9 := rfl
example : DirectToken.clauseSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 0 = some .sep := rfl
example : DirectToken.clauseSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 7 = some .finish := rfl
example : DirectToken.clauseSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 8 = none := rfl

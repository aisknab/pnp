/-
Copyright (c) 2026 PNP Labs.
Preservation literal arguments must come from actual source/radix registers.
The next-time value is computed on tape before the conclusion kernel uses it.
These general execution contracts do not claim a complete payload dispatcher.
-/
import PNP.Concrete.CookLevinBuilderPreservationLiteralSources

namespace PNP.Concrete.CookLevin.BuilderPreservationLiteralSources.Regression

open BuilderUnaryPolynomial
open BuilderLiteralArgumentSource
open BuilderPreservationCoordinates (ofSource headRequest oldSymbolRequest newSymbolRequest)

example (afterCount : Nat) : headPlan afterCount ⟨0, by decide⟩ = .quotient := rfl
example (afterCount : Nat) : headPlan afterCount ⟨1, by decide⟩ = .digit ⟨2, by decide⟩ := rfl
example (afterCount : Nat) : headPlan afterCount ⟨2, by decide⟩ = .constant 0 := rfl
example (afterCount : Nat) : headPlan afterCount ⟨3, by decide⟩ = .constant 0 := rfl
example (afterCount : Nat) : oldSymbolPlan afterCount ⟨0, by decide⟩ = .quotient := rfl
example (afterCount : Nat) : oldSymbolPlan afterCount ⟨1, by decide⟩ = .digit ⟨1, by decide⟩ := rfl
example (afterCount : Nat) : oldSymbolPlan afterCount ⟨2, by decide⟩ = .constant 0 := rfl
example (afterCount : Nat) : oldSymbolPlan afterCount ⟨3, by decide⟩ = .digit ⟨0, by decide⟩ := rfl
example (extraCount : Nat) : newSymbolPlan extraCount ⟨0, by decide⟩ = .retained ⟨2, by omega⟩ := rfl
example (extraCount : Nat) : newSymbolPlan extraCount ⟨1, by decide⟩ = .digit ⟨1, by decide⟩ := rfl
example (extraCount : Nat) : newSymbolPlan extraCount ⟨2, by decide⟩ = .constant 0 := rfl
example (extraCount : Nat) : newSymbolPlan extraCount ⟨3, by decide⟩ = .digit ⟨0, by decide⟩ := rfl

variable {language : Language} (problem : VerifierTableauProblem language)

example (index : Nat) : (nextTimeValues problem index).length = 3 := nextTimeValues_length problem index
example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    nextTimeValues problem index =
      [(ofSource problem index hRegion).step.val, 1, (ofSource problem index hRegion).step.val + 1] :=
  nextTimeValues_eq problem index hRegion
example (index afterCount : Nat) (after : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    argumentEnvironment problem index .preservation after (headPlan afterCount) =
      (headRequest (ofSource problem index hRegion)).environment := head_environment problem index afterCount after hRegion
example (index afterCount : Nat) (after : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    argumentEnvironment problem index .preservation after (oldSymbolPlan afterCount) =
      (oldSymbolRequest (ofSource problem index hRegion)).environment := oldSymbol_environment problem index afterCount after hRegion
example (index extraCount : Nat) (extra : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    argumentEnvironment problem index .preservation (nextTimeValues problem index ++ extra)
      (newSymbolPlan extraCount) =
      (newSymbolRequest (ofSource problem index hRegion)).environment := newSymbol_environment problem index extraCount extra hRegion
example (index afterCount : Nat) (after : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .head)
      (argumentEnvironment problem index .preservation after (headPlan afterCount)) =
        (headRequest (ofSource problem index hRegion)).index := head_index_eq problem index afterCount after hRegion
example (index afterCount : Nat) (after : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .symbol)
      (argumentEnvironment problem index .preservation after (oldSymbolPlan afterCount)) =
        (oldSymbolRequest (ofSource problem index hRegion)).index := oldSymbol_index_eq problem index afterCount after hRegion
example (index extraCount : Nat) (extra : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .symbol)
      (argumentEnvironment problem index .preservation (nextTimeValues problem index ++ extra)
        (newSymbolPlan extraCount)) = (newSymbolRequest (ofSource problem index hRegion)).index :=
  newSymbol_index_eq problem index extraCount extra hRegion
example (index afterCount : Nat) (after : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .head)
      (argumentEnvironment problem index .preservation after (headPlan afterCount)) < problem.FormulaWidth := by
  rw [head_index_eq problem index afterCount after hRegion]
  exact (headRequest (ofSource problem index hRegion)).index_lt
example (index afterCount : Nat) (after : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .symbol)
      (argumentEnvironment problem index .preservation after (oldSymbolPlan afterCount)) < problem.FormulaWidth := by
  rw [oldSymbol_index_eq problem index afterCount after hRegion]
  exact (oldSymbolRequest (ofSource problem index hRegion)).index_lt
example (index extraCount : Nat) (extra : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .symbol)
      (argumentEnvironment problem index .preservation (nextTimeValues problem index ++ extra)
        (newSymbolPlan extraCount)) < problem.FormulaWidth := by
  rw [newSymbol_index_eq problem index extraCount extra hRegion]
  exact (newSymbolRequest (ofSource problem index hRegion)).index_lt
example (index remaining : Nat) :
    BuilderRegisterExpression.values (nextTimeExpression problem.verifier)
      (environment problem index remaining .preservation 0 []) = nextTimeValues problem index :=
  nextTime_expression_values problem index remaining
example (index remaining : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (nextTimeMachine problem.verifier) (nextTimeSteps problem index remaining)
      (nextTimeInitial problem index remaining inside outside) =
        some (nextTimeFinal problem index remaining inside outside) := nextTime_workRunExact problem index remaining inside outside
example (index remaining : Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (nextTimeMachine problem.verifier)) (6 * nextTimeSteps problem index remaining)
      (encodeWorkConfiguration (nextTimeInitial problem index remaining inside outside)) =
        encodeWorkConfiguration (nextTimeFinal problem index remaining inside outside) :=
  nextTime_run_compile_exact problem index remaining inside outside
example (index remaining : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (newSymbolMachine problem.verifier) (newSymbolSteps problem index remaining)
      (newSymbolInitial problem index remaining inside outside) =
        some (newSymbolFinal problem index remaining inside outside) := newSymbol_workRunExact problem index remaining inside outside
example (index remaining : Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (newSymbolMachine problem.verifier)) (6 * newSymbolSteps problem index remaining)
      (encodeWorkConfiguration (newSymbolInitial problem index remaining inside outside)) =
        encodeWorkConfiguration (newSymbolFinal problem index remaining inside outside) :=
  newSymbol_run_compile_exact problem index remaining inside outside
example (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    ∃ leadingValues, finalValues problem index remaining .preservation (nextTimeValues problem index)
      (newSymbolPlan 0) .symbol =
        leadingValues ++ [(newSymbolRequest (ofSource problem index hRegion)).index] :=
  newSymbol_final_index problem index remaining hRegion

variable (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation)

example : (registerWord (inputValues problem index remaining .preservation [] ++ nextTimeValues problem index)).length ≤
    (nextTimeSpanBound problem.verifier).eval problem.input.length ∧
    6 * nextTimeSteps problem index remaining ≤
      (nextTimeRawTimeBound problem.verifier).eval problem.input.length :=
  nextTime_source_polynomial_bounds problem index remaining hBody hBalance hRegion
example : (registerWord (finalValues problem index remaining .preservation (nextTimeValues problem index)
      (newSymbolPlan 0) .symbol)).length ≤ (newSymbolSpanBound problem.verifier).eval problem.input.length ∧
    6 * newSymbolSteps problem index remaining ≤
      (newSymbolRawTimeBound problem.verifier).eval problem.input.length :=
  newSymbol_source_polynomial_bounds problem index remaining hBody hBalance hRegion

example : (nextTimeMachine problem.verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  nextTime_rules_pairwise_query_distinct problem.verifier
example : WorkMachineChain.NoRuleAtAccept (nextTimeMachine problem.verifier) := nextTime_noRuleAtAccept problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (nextTimeMachine problem.verifier) (nextTimeMachine problem.verifier).rejectState :=
  nextTime_noRuleAtReject problem.verifier
example : (nextTimeMachine problem.verifier).acceptState ≠ (nextTimeMachine problem.verifier).rejectState :=
  nextTime_acceptState_ne_rejectState problem.verifier
example : (newSymbolMachine problem.verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  newSymbol_rules_pairwise_query_distinct problem.verifier
example : WorkMachineChain.NoRuleAtAccept (newSymbolMachine problem.verifier) := newSymbol_noRuleAtAccept problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (newSymbolMachine problem.verifier) (newSymbolMachine problem.verifier).rejectState :=
  newSymbol_noRuleAtReject problem.verifier
example : (newSymbolMachine problem.verifier).acceptState ≠ (newSymbolMachine problem.verifier).rejectState :=
  newSymbol_acceptState_ne_rejectState problem.verifier

end PNP.Concrete.CookLevin.BuilderPreservationLiteralSources.Regression

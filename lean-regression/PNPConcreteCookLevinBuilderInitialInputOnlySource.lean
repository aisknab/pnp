/-
Copyright (c) 2026 PNP Labs.
Source/radix binding, canonical slots, source preservation and full encoded-input
bounds for the input-only cell writer. No finite fixture earns progress credit.
-/
import PNP.Concrete.CookLevinBuilderInitialInputOnlySource

namespace PNP.Concrete.CookLevin.BuilderInitialInputOnlySource.Regression
open BuilderInitialInputOnlySource
open BuilderUnaryPolynomial

section Source
variable {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
variable (output : List CNFToken)

example : (data problem index).inputLength = problem.input.length := rfl
example : (data problem index).fuel = problem.uniformFuel := rfl
example : (data problem index).tapeWidth = problem.dimensions.tapeWidth problem.tableauInputMode := rfl
example : (data problem index).coordinate = BuilderConstraintRegionSource.localCoordinate problem index .initial := rfl
example : BuilderInitialInputOnlyPayload.position (data problem index) = coordinate problem index - 2 := rfl
example : BuilderRegisterPack.values (fields problem.verifier)
    (BuilderLiteralArgumentSource.environment problem index remaining .initial 0 []) =
      [problem.input.length, problem.uniformFuel, problem.dimensions.tapeWidth problem.tableauInputMode, coordinate problem index] :=
  fields_values problem index remaining

example : workRunExact? (machine problem.verifier) (workSteps problem index remaining)
    (initialConfiguration problem index remaining output) = some (finalConfiguration problem index remaining output) :=
  workRunExact problem index remaining output
example : run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
    (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
    encodeWorkConfiguration (finalConfiguration problem index remaining output) := run_compile_exact problem index remaining output
example : (finalConfiguration problem index remaining output).tape =
    BuilderDividerOperands.endTape (finalValues problem index remaining) (BuilderDividerOperands.inside problem.input output) [] :=
  final_tape problem index remaining output
example : (finalConfiguration problem index remaining output).tape.left = [] := final_frontier problem index remaining output
example (hPrefix : ¬ coordinate problem index < 2) :
    finalValues problem index remaining = history problem index remaining ++ payloadValues problem index :=
  final_suffix problem index remaining hPrefix
example (hPrefix : coordinate problem index < 2) :
    finalValues problem index remaining = sourceFrame problem index remaining ++ BuilderInitialInputOnlyPayload.prefixStage (data problem index) := by
  rw [finalValues, BuilderInitialInputOnlyPayload.prefix_output (data problem index) problem.input hPrefix]

example (hPosition : BuilderInitialInputOnlyPayload.position (data problem index) <
    problem.dimensions.tapeWidth problem.tableauInputMode) :
    BuilderInitialInputOnlyPayload.indexValue (data problem index) problem.input =
      (problem.symbolLiteral problem.initialTime ⟨BuilderInitialInputOnlyPayload.position (data problem index), hPosition⟩
        (BuilderInitialConstraintPayload.inputOnlySymbol problem.input problem.uniformFuel
          (BuilderInitialInputOnlyPayload.position (data problem index)))).index.val := index_canonical problem index hPosition
example (hPosition : BuilderInitialInputOnlyPayload.position (data problem index) <
    problem.dimensions.tapeWidth problem.tableauInputMode) :
    BuilderInitialInputOnlyPayload.indexValue (data problem index) problem.input < problem.FormulaWidth := by
  rw [index_canonical problem index hPosition]
  exact (problem.symbolLiteral problem.initialTime
    ⟨BuilderInitialInputOnlyPayload.position (data problem index), hPosition⟩
    (BuilderInitialConstraintPayload.inputOnlySymbol problem.input problem.uniformFuel
      (BuilderInitialInputOnlyPayload.position (data problem index)))).index.isLt
example (hPosition : BuilderInitialInputOnlyPayload.position (data problem index) <
    problem.dimensions.tapeWidth problem.tableauInputMode) : (payloadValues problem index).length = 3 := by
  rw [payloadValues, if_pos hPosition]
  rfl
example (hPosition : ¬ BuilderInitialInputOnlyPayload.position (data problem index) <
    problem.dimensions.tapeWidth problem.tableauInputMode) : payloadValues problem index = [1] := by
  rw [payloadValues, if_neg hPosition]
example (hPosition : ¬ BuilderInitialInputOnlyPayload.position (data problem index) <
    problem.dimensions.tapeWidth problem.tableauInputMode) : payloadValues problem index ≠ [0] := by
  rw [payloadValues, if_neg hPosition]
  decide

variable (hMode : problem.tableauInputMode ≠ .paired)
variable (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial)
variable (hPrefix : ¬ coordinate problem index < 2)
example : coordinate problem index - 2 < BuilderInitialConstraintPayload.symbolCapacity problem :=
  source_capacity problem index hRegion
example : payloadValues problem index = BuilderInitialConstraintPayload.values problem (coordinate problem index) :=
  payload_canonical problem index hMode hRegion hPrefix
example : BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index) =
    some (problem.initialConstraintSlotDirect (coordinate problem index)) := payload_decode problem index hMode hRegion hPrefix
example : payloadValues problem index = BuilderLocalConstraintPayload.values
    (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) :=
  whole_formula_payload problem index hMode hRegion hPrefix
example : workRunExact? (machine problem.verifier) (workSteps problem index remaining)
    (initialConfiguration problem index remaining output) =
    some
      {state := (machine problem.verifier).acceptState,
       tape := BuilderDividerOperands.endTape (history problem index remaining ++ BuilderLocalConstraintPayload.values
         (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)))
         (BuilderDividerOperands.inside problem.input output) []} :=
  source_canonical_payload problem index remaining output hMode hRegion hPrefix
example (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining)).length ≤ (spanPolynomial problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining ≤ (rawTimePolynomial problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hBody hBalance hRegion

example : (graph problem.verifier).nodes.length = 2 := graph_nodes_length problem.verifier
example : (graph problem.verifier).WellFormed := graph_wellFormed problem.verifier
example : (machine problem.verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).acceptState := noRuleAtAccept problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).rejectState := noRuleAtReject problem.verifier
example : (machine problem.verifier).acceptState ≠ (machine problem.verifier).rejectState := acceptState_ne_rejectState problem.verifier
end Source

end PNP.Concrete.CookLevin.BuilderInitialInputOnlySource.Regression

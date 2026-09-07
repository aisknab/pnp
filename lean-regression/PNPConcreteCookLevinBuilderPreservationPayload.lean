/-
Copyright (c) 2026 PNP Labs.
Prepared complete preservation-family contracts: actual source fields, both
runtime outcomes, canonical payloads, retained frame and erased-cell accounting.
These are not complete-builder or unconditional P=NP claims.
-/
import PNP.Concrete.CookLevinBuilderPreservationPayload

namespace PNP.Concrete.CookLevin.BuilderPreservationPayload.Regression

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPreservationCoordinates (ofSource)

variable {language : Language} (problem : VerifierTableauProblem language)

example : (pairFields problem.verifier).length = 2 := pairFields_length problem.verifier
example : (graph problem.verifier).nodes.length = 4 := rfl
example : (pairNode problem.verifier).program = BuilderRegisterPack.machine (pairFields problem.verifier) 0 := rfl
example : (comparisonNode problem.verifier).program = BuilderRegisterEquality.machine := rfl
example : (comparisonNode problem.verifier).onAccept = .node paddingNode.reference := rfl
example : (comparisonNode problem.verifier).onReject = .node (implicationNode problem.verifier).reference := rfl
example : paddingNode.program = BuilderConstraintRegionAssembly.oneMachine := rfl
example : (implicationNode problem.verifier).program = BuilderPreservationImplicationPayload.machine problem.verifier := rfl
example : paddingNode.onAccept = .accept := rfl
example : (implicationNode problem.verifier).onAccept = .accept := rfl
example : (graph problem.verifier).WellFormed := graph_wellFormed problem.verifier

example (index remaining : Nat) :
    BuilderRegisterPack.values (pairFields problem.verifier)
      (BuilderLiteralArgumentSource.environment problem index remaining .preservation 0 []) =
      [headValue problem index, otherValue problem index] := pair_values problem index remaining
example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    headValue problem index = (ofSource problem index hRegion).head.val := (source_positions problem index hRegion).1
example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    otherValue problem index = (ofSource problem index hRegion).other.val := (source_positions problem index hRegion).2

example (index remaining : Nat) (inside : List WorkSymbol) :
    workRunExact? (pairMachine problem.verifier) (pairSteps problem index remaining)
      (workStartConfiguration (pairMachine problem.verifier) (endTape (frame problem index remaining) inside [])) =
      some {
        state := (pairMachine problem.verifier).acceptState
        tape := endTape (frame problem index remaining ++ [headValue problem index, otherValue problem index]) inside [] } :=
  pair_workRunExact problem index remaining inside
example (index remaining : Nat) (inside : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside) =
      some (finalConfiguration problem index remaining inside) := workRunExact problem index remaining inside
example (index remaining : Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside) := run_compile_exact problem index remaining inside
example (index remaining : Nat) :
    workSteps problem index remaining = pairSteps problem index remaining +
      BuilderRegisterEquality.workSteps (headValue problem index) (otherValue problem index) +
      branchSteps problem index remaining + 3 := by
  unfold workSteps
  omega

example (index remaining : Nat) (hEqual : headValue problem index = otherValue problem index) :
    payloadValues problem index remaining = [1] := by rw [payloadValues, if_pos hEqual]
example (index : Nat) (hEqual : headValue problem index = otherValue problem index) :
    retainedValues problem index = [] := by rw [retainedValues, if_pos hEqual]
example (index remaining : Nat) (hEqual : headValue problem index = otherValue problem index) :
    branchSteps problem index remaining = 5 := by rw [branchSteps, if_pos hEqual]
example (index remaining : Nat) (hEqual : headValue problem index = otherValue problem index) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining) = some (some none) := by
  rw [payloadValues, if_pos hEqual]
  change BuilderLocalConstraintPayload.decode problem.FormulaWidth
    (BuilderLocalConstraintPayload.values (width := problem.FormulaWidth) (some none)) = some (some none)
  rw [BuilderLocalConstraintPayload.decode_values]

example (index remaining : Nat) (hDifferent : headValue problem index ≠ otherValue problem index) :
    payloadValues problem index remaining = BuilderPreservationImplicationPayload.payloadValues problem index remaining := by
  rw [payloadValues, if_neg hDifferent]
example (index : Nat) (hDifferent : headValue problem index ≠ otherValue problem index) :
    retainedValues problem index = BuilderPreservationImplicationPayload.allValues problem index := by
  rw [retainedValues, if_neg hDifferent]
example (index remaining : Nat) (hLess : headValue problem index < otherValue problem index) :
    payloadValues problem index remaining = BuilderPreservationImplicationPayload.payloadValues problem index remaining := by
  rw [payloadValues, if_neg (by omega)]
example (index remaining : Nat) (hGreater : otherValue problem index < headValue problem index) :
    payloadValues problem index remaining = BuilderPreservationImplicationPayload.payloadValues problem index remaining := by
  rw [payloadValues, if_neg (by omega)]
example (index remaining : Nat) (hZero : headValue problem index = 0) (hPositive : 0 < otherValue problem index) :
    payloadValues problem index remaining = BuilderPreservationImplicationPayload.payloadValues problem index remaining := by
  rw [payloadValues, if_neg (by omega)]

example (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    payloadValues problem index remaining =
      BuilderLocalConstraintPayload.values
        (problem.preservationConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .preservation)) :=
  payload_canonical problem index remaining hRegion
example (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining) =
      some (problem.preservationConstraintSlotDirect
        (BuilderConstraintRegionSource.localCoordinate problem index .preservation)) := payload_decode problem index remaining hRegion
example (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining) ≠ some none := by
  by_cases hEqual : headValue problem index = otherValue problem index
  · rw [payloadValues, if_pos hEqual]
    change BuilderLocalConstraintPayload.decode problem.FormulaWidth
      (BuilderLocalConstraintPayload.values (width := problem.FormulaWidth) (some none)) ≠ some none
    rw [BuilderLocalConstraintPayload.decode_values]
    intro impossible
    cases impossible
  · rw [payloadValues, if_neg hEqual,
      BuilderPreservationImplicationPayload.payload_decode problem index remaining hRegion]
    intro impossible
    cases impossible
example (index remaining otherRemaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    payloadValues problem index remaining = payloadValues problem index otherRemaining := by
  rw [payload_canonical problem index remaining hRegion, payload_canonical problem index otherRemaining hRegion]
example (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    finalValues problem index remaining = frame problem index remaining ++ retainedValues problem index ++
      BuilderLocalConstraintPayload.values
        (problem.preservationConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .preservation)) :=
  final_canonical_payload problem index remaining hRegion
example (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape.right =
      (registerWord (retainedValues problem index ++ payloadValues problem index remaining)).reverse ++
        ((registerWord (frame problem index remaining)).reverse ++ inside) := final_inside_preserved problem index remaining inside
example (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape.left =
      (comparisonBlanks problem index).drop
        (registerWord (retainedValues problem index ++ payloadValues problem index remaining)).length :=
  final_exterior problem index remaining inside

variable (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation)

example : (registerWord (frame problem index remaining ++ [headValue problem index, otherValue problem index])).length ≤
      (pairSpanBound problem.verifier).eval problem.input.length ∧
    6 * pairSteps problem index remaining ≤ (pairRawTimeBound problem.verifier).eval problem.input.length :=
  pair_source_polynomial_bounds problem index remaining hBody hBalance hRegion
example : (comparisonBlanks problem index).length ≤ (comparisonSpanBound problem.verifier).eval problem.input.length ∧
    6 * BuilderRegisterEquality.workSteps (headValue problem index) (otherValue problem index) ≤
      (BuilderRegisterEquality.rawTimePolynomial (pairSpanBound problem.verifier)).eval problem.input.length :=
  comparison_source_polynomial_bounds problem index remaining hBody hBalance hRegion
example (inside : List WorkSymbol) :
    (registerWord (finalValues problem index remaining)).length +
        (finalConfiguration problem index remaining inside).tape.left.length ≤
      (spanBound problem.verifier).eval problem.input.length ∧
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining inside hBody hBalance hRegion

example : (machine problem.verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct problem.verifier
example : WorkMachineChain.NoRuleAtAccept (machine problem.verifier) := noRuleAtAccept problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).rejectState := noRuleAtReject problem.verifier
example : (machine problem.verifier).acceptState ≠ (machine problem.verifier).rejectState := acceptState_ne_rejectState problem.verifier

end PNP.Concrete.CookLevin.BuilderPreservationPayload.Regression

/-
Copyright (c) 2026 PNP Labs.
Physical preservation candidate payloads: arbitrary source coordinates and
workspace, exact canonical ordering, source-derived bounds and guarded use.
The diagonal must be dispatched separately; a candidate is not padding.
-/
import PNP.Concrete.CookLevinBuilderPreservationImplicationPayload

namespace PNP.Concrete.CookLevin.BuilderPreservationImplicationPayload.Regression

open BuilderUnaryPolynomial (registerWord)
open BuilderLiteralArgumentSource (inputValues)
open BuilderPreservationCoordinates (ofSource headRequest oldSymbolRequest newSymbolRequest)

example : newCount = 3 + literalCount .symbol := rfl
example : headCount = newCount + literalCount .head := rfl
example : allCount = headCount + literalCount .symbol := rfl
example : newCount - 1 < headCount - 1 := by
  simp only [newCount, headCount, literalCount]
  omega
example : headCount - 1 < allCount - 1 := by
  simp only [newCount, headCount, allCount, literalCount]
  omega
example : payloadReferences.length = 8 := rfl

variable {language : Language} (problem : VerifierTableauProblem language)

example (index : Nat) : (newValues problem index).length = newCount := newValues_length problem index
example (index : Nat) : (headValues problem index).length = headCount := headValues_length problem index
example (index : Nat) : (allValues problem index).length = allCount := allValues_length problem index
example : (payloadFields problem.verifier).length = 8 := payloadFields_length problem.verifier
example (index remaining : Nat) : (payloadValues problem index remaining).length = 8 := payloadValues_length problem index remaining

example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (allValues problem index).getD (newCount - 1) 0 = (newSymbolRequest (ofSource problem index hRegion)).index :=
  (retained_indices problem index hRegion).1
example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (allValues problem index).getD (headCount - 1) 0 = (headRequest (ofSource problem index hRegion)).index :=
  (retained_indices problem index hRegion).2.1
example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (allValues problem index).getD (allCount - 1) 0 = (oldSymbolRequest (ofSource problem index hRegion)).index :=
  (retained_indices problem index hRegion).2.2
example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (allValues problem index).getD (newCount - 1) 0 < problem.FormulaWidth := by
  rw [(retained_indices problem index hRegion).1]
  exact (newSymbolRequest (ofSource problem index hRegion)).index_lt
example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (allValues problem index).getD (headCount - 1) 0 < problem.FormulaWidth := by
  rw [(retained_indices problem index hRegion).2.1]
  exact (headRequest (ofSource problem index hRegion)).index_lt
example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (allValues problem index).getD (allCount - 1) 0 < problem.FormulaWidth := by
  rw [(retained_indices problem index hRegion).2.2]
  exact (oldSymbolRequest (ofSource problem index hRegion)).index_lt
example (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    payloadValues problem index remaining =
      [(oldSymbolRequest (ofSource problem index hRegion)).index, 1,
        (headRequest (ofSource problem index hRegion)).index, 1,
        (newSymbolRequest (ofSource problem index hRegion)).index, 1, 2, 3] := by
  rw [payload_values_eq problem index remaining hRegion, BuilderPreservationCoordinates.candidate_payload]
example (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining) =
      some (some (some (BuilderPreservationCoordinates.constraint (ofSource problem index hRegion)))) :=
  payload_decode problem index remaining hRegion
example (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining) ≠ some (some none) := by
  rw [payload_decode problem index remaining hRegion]
  intro impossible
  cases impossible
example (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation)
    (hDifferent : (ofSource problem index hRegion).head ≠ (ofSource problem index hRegion).other) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining) =
      some (problem.preservationConstraintSlotDirect
        (BuilderConstraintRegionSource.localCoordinate problem index .preservation)) :=
  payload_decode_off_diagonal problem index remaining hRegion hDifferent
example (index remaining otherRemaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    payloadValues problem index remaining = payloadValues problem index otherRemaining := by
  rw [payload_values_eq problem index remaining hRegion, payload_values_eq problem index otherRemaining hRegion]
example (index remaining : Nat) :
    (finalValues problem index remaining).length =
      BuilderLiteralArgumentSource.frameCount problem.verifier .preservation + allCount + 8 := by
  simp only [finalValues, inputValues, List.length_append, BuilderLiteralArgumentSource.frame_length,
    allValues_length, payloadValues_length]
example (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    finalValues problem index remaining =
      inputValues problem index remaining .preservation (allValues problem index) ++
        BuilderLocalConstraintPayload.values (some (some (BuilderPreservationCoordinates.constraint
          (ofSource problem index hRegion)))) := final_canonical_payload problem index remaining hRegion
example (index remaining : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (prefixMachine problem.verifier) (prefixSteps problem index remaining)
      (prefixInitial problem index remaining inside outside) =
        some (prefixFinal problem index remaining inside outside) := prefix_workRunExact problem index remaining inside outside
example (index remaining : Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (prefixMachine problem.verifier)) (6 * prefixSteps problem index remaining)
      (encodeWorkConfiguration (prefixInitial problem index remaining inside outside)) =
        encodeWorkConfiguration (prefixFinal problem index remaining inside outside) :=
  prefix_run_compile_exact problem index remaining inside outside
example (index remaining : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside outside) =
        some (finalConfiguration problem index remaining inside outside) := workRunExact problem index remaining inside outside
example (index remaining : Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside outside)) =
        encodeWorkConfiguration (finalConfiguration problem index remaining inside outside) :=
  run_compile_exact problem index remaining inside outside
example (index remaining : Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside outside).tape =
      BuilderDividerOperands.endTape (finalValues problem index remaining) inside
        (outside.drop (registerWord (allValues problem index ++ payloadValues problem index remaining)).length) := rfl

variable (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation)

example : (registerWord (inputValues problem index remaining .preservation (allValues problem index))).length ≤
      (prefixSpanBound problem.verifier).eval problem.input.length ∧
    6 * prefixSteps problem index remaining ≤ (prefixRawTimeBound problem.verifier).eval problem.input.length :=
  prefix_source_polynomial_bounds problem index remaining hBody hBalance hRegion
example : (registerWord (finalValues problem index remaining)).length ≤ (spanBound problem.verifier).eval problem.input.length ∧
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hBody hBalance hRegion

example : (prefixMachine problem.verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  prefix_rules_pairwise_query_distinct problem.verifier
example : WorkMachineChain.NoRuleAtAccept (prefixMachine problem.verifier) := prefix_noRuleAtAccept problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (prefixMachine problem.verifier) (prefixMachine problem.verifier).rejectState :=
  prefix_noRuleAtReject problem.verifier
example : (prefixMachine problem.verifier).acceptState ≠ (prefixMachine problem.verifier).rejectState :=
  prefix_acceptState_ne_rejectState problem.verifier
example : (machine problem.verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct problem.verifier
example : WorkMachineChain.NoRuleAtAccept (machine problem.verifier) := noRuleAtAccept problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).rejectState := noRuleAtReject problem.verifier
example : (machine problem.verifier).acceptState ≠ (machine problem.verifier).rejectState := acceptState_ne_rejectState problem.verifier

end PNP.Concrete.CookLevin.BuilderPreservationImplicationPayload.Regression

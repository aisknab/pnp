/-
Copyright (c) 2026 PNP Labs.

The existing fixed row machine selects the exact ordered exclusion pair from
a prepared reverse-coordinate frame. The pair is decoded from the actual
terminal register suffix, including the physically decremented countdown.
No caller supplies the selected pair or a successful execution certificate.

Preparation of that frame from actual source registers, variable-field reads,
and source-token dispatch remain separate executable composition obligations.
The polynomial theorem here charges the row phase, not those omitted phases.
-/

import PNP.Concrete.CookLevinBuilderExclusionPairSelection
import PNP.Concrete.CookLevinBuilderInitialRowLoop
import PNP.Concrete.CookLevinBuilderExactlyOneClauseOccupancy

namespace PNP.Concrete.CookLevin.BuilderExclusionPairRow

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderExclusionPairSelection
open BuilderInitialRowLoop (attemptValues attemptEnvironment finishValues)

def machine : WorkMachine := BuilderInitialRowLoop.machine

private theorem machine_acceptState : machine.acceptState = BuilderInitialRowLoop.machine.acceptState := rfl
private theorem machine_rejectState : machine.rejectState = BuilderInitialRowLoop.machine.rejectState := rfl

def initialConfiguration (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    WorkConfiguration :=
  BuilderInitialRowLoop.initialConfiguration (count - 1) 0 1
    (reverseCoordinate count coordinate) older inside outside

def finalConfiguration (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    WorkConfiguration :=
  BuilderInitialRowLoop.finalConfiguration (count - 1) 0 1
    (reverseCoordinate count coordinate) older inside outside

def workSteps (count coordinate : Nat) : Nat :=
  BuilderInitialRowLoop.workSteps (count - 1) 0 1 (reverseCoordinate count coordinate)

def resultValues (count coordinate : Nat) (older : List Nat) : List Nat :=
  older ++ finishValues (count - 1) 0 1 (reverseCoordinate count coordinate)

/-- Fixed offsets in the actual final nine-register row-attempt suffix. -/
def decodeValues (values : List Nat) : Option (Nat × Nat) := do
  let remaining ← values.reverse[5]?
  let width ← values.reverse[1]?
  let offset ← values.reverse[0]?
  pure (remaining, remaining + width - offset)

/-- A rejected frame is never interpreted as a selected pair. -/
def observedPair (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    Option (Nat × Nat) :=
  if (finalConfiguration count coordinate older inside outside).state = machine.acceptState then
    decodeValues (resultValues count coordinate older)
  else none

theorem workRunExact (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps count coordinate)
      (initialConfiguration count coordinate older inside outside) =
      some (finalConfiguration count coordinate older inside outside) :=
  BuilderInitialRowLoop.workRunExact (count - 1) 0 1 (reverseCoordinate count coordinate) older inside outside

theorem run_compile_exact (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps count coordinate)
      (encodeWorkConfiguration (initialConfiguration count coordinate older inside outside)) =
      encodeWorkConfiguration (finalConfiguration count coordinate older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact count coordinate older inside outside)

theorem final_reject_iff (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside outside).state = machine.rejectState ↔
      LocalConstraint.pairCount count ≤ coordinate := by
  rw [finalConfiguration, machine_rejectState, BuilderInitialRowLoop.final_reject_iff]
  exact rowSelection_none_iff count coordinate

theorem final_accept_iff (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside outside).state = machine.acceptState ↔
      coordinate < LocalConstraint.pairCount count := by
  rw [finalConfiguration, machine_acceptState, BuilderInitialRowLoop.final_accept_iff]
  change (rowSelection count coordinate).isSome = true ↔ _
  cases hFound : rowSelection count coordinate with
  | none =>
      have hOutside := (rowSelection_none_iff count coordinate).mp hFound
      constructor
      · intro impossible
        cases impossible
      · intro hInside
        omega
  | some found =>
      constructor
      · intro _
        by_cases hInside : coordinate < LocalConstraint.pairCount count
        · exact hInside
        · have hNone := (rowSelection_none_iff count coordinate).mpr (by omega)
          rw [hFound] at hNone
          cases hNone
      · intro _
        rfl

theorem final_tape (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside outside).tape =
      endTape (resultValues count coordinate older) inside
        (BuilderInitialRowLoop.finishOutside (count - 1) 0 1
          (reverseCoordinate count coordinate) outside) := rfl

/-- Strengthen the reused loop's suffix invariant without changing its machine. -/
theorem found_attempt (remaining length width coordinate : Nat)
    (position : Fin remaining) (offset : Nat)
    (hFound : BuilderInitialLengthSelection.locate remaining width coordinate = some (position, offset)) :
    ∃ history : List Nat, history.length = 9 * position.val ∧
      finishValues remaining length width coordinate =
        history ++ attemptValues (length + position.val) (width + position.val)
          offset (remaining - (position.val + 1)) := by
  induction remaining generalizing length width coordinate offset with
  | zero => cases position.isLt
  | succ remaining ih =>
      by_cases hLess : coordinate < width
      · simp only [BuilderInitialLengthSelection.locate, if_pos hLess] at hFound
        have hPair := Option.some.inj hFound
        have hPosition := congrArg Prod.fst hPair
        have hOffset := congrArg Prod.snd hPair
        dsimp only at hPosition hOffset
        subst position
        subst offset
        refine ⟨[], rfl, ?_⟩
        simp only [finishValues, if_pos hLess, Nat.add_zero, Nat.zero_add,
          Nat.add_sub_cancel, List.append_nil, List.nil_append]
      · cases hTail : BuilderInitialLengthSelection.locate remaining (width + 1) (coordinate - width) with
        | none =>
            simp only [BuilderInitialLengthSelection.locate, if_neg hLess, hTail, Option.map_none] at hFound
            cases hFound
        | some found =>
            rcases found with ⟨tailPosition, tailOffset⟩
            have hMap : some (tailPosition.succ, tailOffset) = some (position, offset) := by
              simpa only [BuilderInitialLengthSelection.locate, if_neg hLess, hTail, Option.map_some] using hFound
            have hPair := Option.some.inj hMap
            have hPosition := congrArg Prod.fst hPair
            have hOffset := congrArg Prod.snd hPair
            dsimp only at hPosition hOffset
            subst position
            subst offset
            rcases ih (length + 1) (width + 1) (coordinate - width) tailPosition tailOffset hTail with
              ⟨history, hHistory, hValues⟩
            refine ⟨attemptValues length width coordinate remaining ++ history, ?_, ?_⟩
            · rw [List.length_append, BuilderInitialRowLoop.attemptValues_length, hHistory]
              change 9 + 9 * tailPosition.val = 9 * (tailPosition.val + 1)
              omega
            · have hLength : length + tailPosition.succ.val = (length + 1) + tailPosition.val := by
                change length + (tailPosition.val + 1) = (length + 1) + tailPosition.val
                omega
              have hWidth : width + tailPosition.succ.val = (width + 1) + tailPosition.val := by
                change width + (tailPosition.val + 1) = (width + 1) + tailPosition.val
                omega
              have hRemaining : remaining + 1 - (tailPosition.succ.val + 1) =
                  remaining - (tailPosition.val + 1) := by
                change remaining + 1 - ((tailPosition.val + 1) + 1) = remaining - (tailPosition.val + 1)
                omega
              simp only [finishValues, if_neg hLess, hValues, hLength, hWidth, hRemaining, List.append_assoc]

theorem decodeValues_suffix (history : List Nat) (environment : Fin 9 → Nat) :
    decodeValues (history ++ List.ofFn environment) =
      some (environment ⟨3, by decide⟩,
        environment ⟨3, by decide⟩ + environment ⟨7, by decide⟩ - environment ⟨8, by decide⟩) := by
  have hValues : List.ofFn environment = [
      environment ⟨0, by decide⟩, environment ⟨1, by decide⟩, environment ⟨2, by decide⟩,
      environment ⟨3, by decide⟩, environment ⟨4, by decide⟩, environment ⟨5, by decide⟩,
      environment ⟨6, by decide⟩, environment ⟨7, by decide⟩, environment ⟨8, by decide⟩] := rfl
  unfold decodeValues
  simp only [List.reverse_append, hValues]
  rfl

theorem found_pair_values (count coordinate : Nat) (older : List Nat)
    (position : Fin (count - 1)) (offset : Nat)
    (hFound : rowSelection count coordinate = some (position, offset)) :
    decodeValues (resultValues count coordinate older) = some (reversePair count (position, offset)) := by
  have hBounds := BuilderInitialLengthSelection.locate_some_bounds
    (count - 1) 1 (reverseCoordinate count coordinate) position offset hFound
  have hLess : offset < 1 + position.val := hBounds.1
  have hPosition := position.isLt
  rcases found_attempt (count - 1) 0 1 (reverseCoordinate count coordinate) position offset hFound with
    ⟨history, _, hValues⟩
  have hRemaining : count - 1 - (position.val + 1) = count - 2 - position.val := by omega
  rw [resultValues, hValues, Nat.zero_add, hRemaining, ← BuilderInitialRowLoop.attemptEnvironment_ofFn]
  rw [← List.append_assoc, decodeValues_suffix]
  simp only [attemptEnvironment, BuilderRegisterCompareResidual.resultBoundary_eq,
    BuilderRegisterCompareResidual.resultCoordinate_eq, if_pos hLess, reversePair]
  congr 2
  omega

theorem observedPair_eq_selectedPair (count coordinate : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    observedPair count coordinate older inside outside = selectedPair count coordinate := by
  cases hFound : rowSelection count coordinate with
  | none =>
      have hOutside := (rowSelection_none_iff count coordinate).mp hFound
      have hNotAccept : ¬ (finalConfiguration count coordinate older inside outside).state = machine.acceptState := by
        intro hAccept
        have hInside := (final_accept_iff count coordinate older inside outside).mp hAccept
        omega
      simp only [observedPair, if_neg hNotAccept, selectedPair, hFound, Option.map_none]
  | some found =>
      rcases found with ⟨position, offset⟩
      have hInside : coordinate < LocalConstraint.pairCount count := by
        by_cases hInside : coordinate < LocalConstraint.pairCount count
        · exact hInside
        · have hNone := (rowSelection_none_iff count coordinate).mpr (by omega)
          rw [hFound] at hNone
          cases hNone
      have hAccept := (final_accept_iff count coordinate older inside outside).mpr hInside
      simp only [observedPair, if_pos hAccept, selectedPair, hFound, Option.map_some]
      exact found_pair_values count coordinate older position offset hFound

theorem workRun_observes_canonical {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps variables.length coordinate)
      (initialConfiguration variables.length coordinate older inside outside) =
      some (finalConfiguration variables.length coordinate older inside outside) ∧
    observePair variables (observedPair variables.length coordinate older inside outside) =
      (atMostOneBoundedClauses variables)[coordinate]? := by
  refine ⟨workRunExact variables.length coordinate older inside outside, ?_⟩
  rw [observedPair_eq_selectedPair, selectedPair_observes_canonical]

def preparedSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul bound bound) (.add (.mul (.constant 2) bound) (.constant 5))

def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderInitialRowLoop.spanPolynomial (preparedSpanPolynomial bound)

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderInitialRowLoop.rawTimePolynomial (preparedSpanPolynomial bound)

/-- A size bound on the specified input frame, not a proof of its physical construction. -/
theorem prepared_span_bound (count coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [count, coordinate])).length ≤ bound.eval inputLength) :
    (registerWord (older ++ BuilderInitialRowLoop.frame 0 1
      (reverseCoordinate count coordinate) (count - 1))).length ≤
        (preparedSpanPolynomial bound).eval inputLength := by
  simp only [registerWord_append, List.length_append, registerWord_length,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hSpan
  have hCount : count ≤ bound.eval inputLength := by omega
  have hSquare := Nat.mul_le_mul hCount hCount
  have hTwice := BuilderExactlyOneClauseOccupancy.pairCount_twice count
  have hCoordinate : reverseCoordinate count coordinate ≤ LocalConstraint.pairCount count := by
    unfold reverseCoordinate
    split <;> omega
  simp only [registerWord_append, List.length_append, BuilderInitialRowLoop.frame,
    registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, Nat.zero_add, preparedSpanPolynomial, NatPolynomial.eval_add,
    NatPolynomial.eval_mul, NatPolynomial.eval_constant]
  omega

/-- Complete row-phase time and retained span, excluding the still-separate frame preparation. -/
theorem row_polynomial_bounds (count coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [count, coordinate])).length ≤ bound.eval inputLength) :
    (registerWord (resultValues count coordinate older)).length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps count coordinate ≤ (rawTimePolynomial bound).eval inputLength :=
  BuilderInitialRowLoop.source_polynomial_bounds (count - 1) 0 1 (reverseCoordinate count coordinate)
    older (preparedSpanPolynomial bound) inputLength (prepared_span_bound count coordinate older bound inputLength hSpan)

theorem uniform_polynomial_row_phase {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside outside : List WorkSymbol)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [variables.length, coordinate])).length ≤ bound.eval inputLength) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval inputLength ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (initialConfiguration variables.length coordinate older inside outside)) =
        encodeWorkConfiguration (finalConfiguration variables.length coordinate older inside outside) ∧
      observePair variables (observedPair variables.length coordinate older inside outside) =
        (atMostOneBoundedClauses variables)[coordinate]? := by
  refine ⟨6 * workSteps variables.length coordinate,
    (row_polynomial_bounds variables.length coordinate older bound inputLength hSpan).2,
    run_compile_exact variables.length coordinate older inside outside, ?_⟩
  rw [observedPair_eq_selectedPair, selectedPair_observes_canonical]

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  BuilderInitialRowLoop.rules_pairwise_query_distinct

theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  BuilderInitialRowLoop.noRuleAtAccept

theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderInitialRowLoop.noRuleAtReject

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState :=
  BuilderInitialRowLoop.acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderExclusionPairRow

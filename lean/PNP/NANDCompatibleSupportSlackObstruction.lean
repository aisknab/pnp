/-
Copyright (c) 2026 PNP Labs.

A proper computed cut of a semantically minimum whole word has positive
independent open slack. This obstructs the unrestricted compatible-support
slack law under raw port completeness, not the checked acyclic framed law
or a correctly restricted full/admissible-support law.
-/

import PNP.NANDCompatibleSupportSlackComparison

set_option autoImplicit false
set_option Elab.async false

namespace PNP.DirectWire.CompatibleSupportSlackObstruction

private def openTruth (output : Fin 8) : Nat :=
  match output.val with
  | 0 => 136 | 1 => 95 | 2 => 160 | 3 => 127
  | 4 => 15 | 5 => 245 | 6 => 10 | _ => 247

private def openFree (input : Fin 3) : Nat :=
  match input.val with | 0 => 170 | 1 => 204 | _ => 240

private def openDifference (left right : Nat) : Fin 8 :=
  if (Nat.xor left right).testBit 0 then 0
  else if (Nat.xor left right).testBit 1 then 1
  else if (Nat.xor left right).testBit 2 then 2
  else if (Nat.xor left right).testBit 3 then 3
  else if (Nat.xor left right).testBit 4 then 4
  else if (Nat.xor left right).testBit 5 then 5
  else if (Nat.xor left right).testBit 6 then 6
  else 7

private def openNonconstantPoint (output : Fin 8) : Fin 8 :=
  openDifference (openTruth output) (if (openTruth output).testBit 0 then 255 else 0)

private theorem open_nonconstant : ∀ output : Fin 8, ∃ left right : Fin 8,
    smaller.semantics (openValuation left) output ≠
      smaller.semantics (openValuation right) output := by
  intro output
  refine ⟨0, openNonconstantPoint output, ?_⟩
  simp only [smaller_formula_exact]
  exact (by decide +kernel : ∀ index : Fin 8,
    openFormula (openValuation 0) index ≠
      openFormula (openValuation (openNonconstantPoint index)) index) output

private theorem open_nonprojection : ∀ (output : Fin 8) (input : Fin 3),
    ∃ value : Fin 8,
      smaller.semantics (openValuation value) output ≠ openValuation value input := by
  intro output input
  refine ⟨openDifference (openTruth output) (openFree input), ?_⟩
  simp only [smaller_formula_exact]
  exact (by decide +kernel : ∀ (index : Fin 8) (port : Fin 3),
    openFormula (openValuation (openDifference (openTruth index) (openFree port))) index ≠
      openValuation (openDifference (openTruth index) (openFree port)) port) output input

private theorem open_distinct_0 : ∀ right : Fin 8, (0 : Fin 8) ≠ right →
    openFormula (openValuation (openDifference (openTruth 0) (openTruth right))) 0 ≠
      openFormula (openValuation (openDifference (openTruth 0) (openTruth right))) right := by
  decide +kernel

private theorem open_distinct_1 : ∀ right : Fin 8, (1 : Fin 8) ≠ right →
    openFormula (openValuation (openDifference (openTruth 1) (openTruth right))) 1 ≠
      openFormula (openValuation (openDifference (openTruth 1) (openTruth right))) right := by
  decide +kernel

private theorem open_distinct_2 : ∀ right : Fin 8, (2 : Fin 8) ≠ right →
    openFormula (openValuation (openDifference (openTruth 2) (openTruth right))) 2 ≠
      openFormula (openValuation (openDifference (openTruth 2) (openTruth right))) right := by
  decide +kernel

private theorem open_distinct_3 : ∀ right : Fin 8, (3 : Fin 8) ≠ right →
    openFormula (openValuation (openDifference (openTruth 3) (openTruth right))) 3 ≠
      openFormula (openValuation (openDifference (openTruth 3) (openTruth right))) right := by
  decide +kernel

private theorem open_distinct_4 : ∀ right : Fin 8, (4 : Fin 8) ≠ right →
    openFormula (openValuation (openDifference (openTruth 4) (openTruth right))) 4 ≠
      openFormula (openValuation (openDifference (openTruth 4) (openTruth right))) right := by
  decide +kernel

private theorem open_distinct_5 : ∀ right : Fin 8, (5 : Fin 8) ≠ right →
    openFormula (openValuation (openDifference (openTruth 5) (openTruth right))) 5 ≠
      openFormula (openValuation (openDifference (openTruth 5) (openTruth right))) right := by
  decide +kernel

private theorem open_distinct_6 : ∀ right : Fin 8, (6 : Fin 8) ≠ right →
    openFormula (openValuation (openDifference (openTruth 6) (openTruth right))) 6 ≠
      openFormula (openValuation (openDifference (openTruth 6) (openTruth right))) right := by
  decide +kernel

private theorem open_distinct_7 : ∀ right : Fin 8, (7 : Fin 8) ≠ right →
    openFormula (openValuation (openDifference (openTruth 7) (openTruth right))) 7 ≠
      openFormula (openValuation (openDifference (openTruth 7) (openTruth right))) right := by
  decide +kernel

private theorem open_distinct : ∀ left right : Fin 8, left ≠ right →
    ∃ value : Fin 8,
      smaller.semantics (openValuation value) left ≠
        smaller.semantics (openValuation value) right := by
  intro left right unequal
  refine ⟨openDifference (openTruth left) (openTruth right), ?_⟩
  simp only [smaller_formula_exact]
  have options : left = 0 ∨ left = 1 ∨ left = 2 ∨ left = 3 ∨
      left = 4 ∨ left = 5 ∨ left = 6 ∨ left = 7 := by omega
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact open_distinct_0 right unequal
  · exact open_distinct_1 right unequal
  · exact open_distinct_2 right unequal
  · exact open_distinct_3 right unequal
  · exact open_distinct_4 right unequal
  · exact open_distinct_5 right unequal
  · exact open_distinct_6 right unequal
  · exact open_distinct_7 right unequal

theorem open_baseline : BaselineOutputConditions smaller := by
  constructor
  · intro output
    obtain ⟨left, right, different⟩ := open_nonconstant output
    exact ⟨openValuation left, openValuation right, different⟩
  · intro output input
    obtain ⟨value, different⟩ := open_nonprojection output input
    exact ⟨openValuation value, different⟩
  · intro left right unequal
    obtain ⟨value, different⟩ := open_distinct left right unequal
    exact ⟨openValuation value, different⟩

theorem local_reference_minimum :
    referenceMinimum support.extractedCandidate.toImplementation = 8 :=
  comparison_reference_minimum.trans
    (referenceMinimum_eq_gateCount_of_squareBaseline smaller open_baseline)

private theorem slack_of_values {inputs outputs : Nat}
    (target : Implementation inputs outputs)
    (count : target.gateCount = 9) (minimum : referenceMinimum target = 8) :
    residualSlack target = 1 := by
  unfold residualSlack
  omega

private theorem extracted_slack_of_values
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (selected : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (count : (extractTerminalSupport candidate selected).gateCount = 9)
    (minimum : referenceMinimum
      (extractTerminalSupport candidate selected).extractedCandidate.toImplementation = 8) :
    residualSlack (extractTerminalSupport candidate selected).extractedCandidate.toImplementation = 1 :=
  slack_of_values (extractTerminalSupport candidate selected).extractedCandidate.toImplementation
    count minimum

theorem local_slack_one : residualSlack support.extractedCandidate.toImplementation = 1 :=
  extracted_slack_of_values original records selected_gate_count local_reference_minimum

private theorem one_not_le_zero {left right : Nat}
    (leftExact : left = 1) (rightExact : right = 0) : ¬left ≤ right := by
  omega

theorem global_slack_law_violation :
    ¬ residualSlack support.extractedCandidate.toImplementation ≤
      residualSlack original.toImplementation :=
  one_not_le_zero local_slack_one global_slack_zero

end PNP.DirectWire.CompatibleSupportSlackObstruction

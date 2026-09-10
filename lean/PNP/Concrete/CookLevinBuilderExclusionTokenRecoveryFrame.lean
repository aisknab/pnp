/-
Copyright (c) 2026 PNP Labs.

Recoverable frames for complete exclusion-token lookup. Every valid and invalid
pair request retains its original registers, denotes a blank exterior, and has
a polynomially bounded canonical frame as well as bounded actual storage.
These are derived from the existing execution, not supplied certificates.
Outcome-preserving cursor recovery and the complete formula loop remain open.
-/
import PNP.Concrete.CookLevinBuilderRequestedExclusionTokenLookup
import PNP.Concrete.CookLevinBuilderPayloadSourceSearchBlank

namespace PNP.Concrete.CookLevin.BuilderExclusionTokenRecoveryFrame

open PipelineTape
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Request)
open BuilderPayloadSourceSearchBlank
open WorkMachineProgramGraph (endpointState)

private theorem finishValues_retained {width : Nat} (payload older : List Nat)
    (literals : List (BoundedLiteral width)) (ordinal : Nat) (prior : List Nat) (position : Nat) :
    ∃ scratch, BuilderLiteralListSearch.finishValues payload older literals ordinal prior position =
      older ++ scratch := by
  induction literals generalizing ordinal prior position with
  | nil =>
      simp only [BuilderLiteralListSearch.finishValues, BuilderLiteralSearchComparison.initialValues,
        BuilderLiteralSearchComparison.baseValues, List.append_assoc]
      exact ⟨_, rfl⟩
  | cons item rest ih =>
      simp only [BuilderLiteralListSearch.finishValues]
      split
      · simp only [BuilderLiteralTokenSelector.finalValues, BuilderLiteralSearchSelect.prepareOlder,
          BuilderLiteralSearchSelect.baseValues, List.append_assoc]
        exact ⟨_, rfl⟩
      · exact ih _ _ _

theorem literal_list_values_retained {width : Nat} (literals : List (BoundedLiteral width))
    (position : Nat) (older : List Nat) :
    ∃ scratch, BuilderLiteralListSearch.finalValues literals position older = older ++ scratch :=
  finishValues_retained _ older literals 0 [] position

private theorem comparison_blank (ordinal position value : Nat) (outside : List WorkSymbol)
    (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralSearchComparison.finalOutside ordinal position value outside) :=
  blank_drop _ _ (blank_drop _ _ (blank_drop _ _ (blank_drop outside _ hBlank)))

private theorem select_prepare_blank (ordinal position value : Nat) (positive : Bool)
    (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralSearchSelect.prepareOutside ordinal position value positive outside) :=
  blank_drop _ _ (blank_drop outside _ hBlank)

private theorem advance_blank (ordinal remaining position value : Nat) (outside : List WorkSymbol)
    (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralSearchAdvance.finalOutside ordinal remaining position value outside) :=
  blank_drop _ _ (blank_cons _ (blank_drop _ _ (blank_drop _ _ (blank_drop outside _ hBlank))))

private theorem finishOutside_blank {width : Nat} (literals : List (BoundedLiteral width))
    (ordinal position : Nat) (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralListSearch.finishOutside literals ordinal position outside) := by
  induction literals generalizing ordinal position outside with
  | nil => exact guard_blank 0 outside hBlank
  | cons item rest ih =>
      have hCompared : BlankOutside
          (BuilderLiteralListSearch.comparedOutside ordinal (rest.length + 1) position item.index.val outside) :=
        comparison_blank _ _ _ _ (guard_blank _ outside hBlank)
      simp only [BuilderLiteralListSearch.finishOutside]
      split
      · exact literal_blank _ _ _ _ (select_prepare_blank _ _ _ _ _ hCompared)
      · exact ih _ _ _ (advance_blank _ _ _ _ _ hCompared)

theorem literal_list_outside_blank {width : Nat} (literals : List (BoundedLiteral width))
    (position : Nat) (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralListSearch.finalOutside literals position outside) :=
  finishOutside_blank literals 0 position outside hBlank

theorem selector_values_retained {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) :
    ∃ scratch, BuilderExclusionClauseTokenSelector.finalValues first second position retained older =
      older ++ scratch := by
  unfold BuilderExclusionClauseTokenSelector.finalValues
  split
  · exact ⟨_, rfl⟩
  · split
    · simp only [BuilderExclusionClauseBoundary.finalValues,
        BuilderExclusionPairLiteralTokens.initialValues, List.append_assoc]
      exact ⟨_, rfl⟩
    · unfold BuilderExclusionPairLiteralTokens.finalValues
      obtain ⟨scratch, hScratch⟩ := literal_list_values_retained
        (excludeBoundedPairClause first second) (position - 1)
        (BuilderExclusionPairLiteralTokens.initialValues first.val second.val (position - 1) retained older)
      rw [hScratch]
      exact ⟨_, List.append_assoc _ _ _⟩

private theorem boundary_blank (first second position : Nat) (outside : List WorkSymbol)
    (hBlank : BlankOutside outside) :
    BlankOutside (BuilderExclusionClauseBoundary.finalOutside first second position outside) :=
  blank_drop _ _ (blank_drop _ _ (blank_drop outside _ hBlank))

theorem selector_outside_blank {width : Nat} (first second : Fin width) (position : Nat)
    (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderExclusionClauseTokenSelector.finalOutside first second position outside) := by
  unfold BuilderExclusionClauseTokenSelector.finalOutside
  split
  · exact hBlank
  · split
    · exact boundary_blank _ _ _ outside hBlank
    · exact literal_list_outside_blank _ _ _
        (blank_drop _ _ (blank_cons _ (blank_replicate_append _ _
          (boundary_blank _ _ _ outside hBlank))))

theorem selector_final_no_rule {width : Nat} (first second : Fin width) (position : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    WorkMachineProgramGraph.NoRuleAt BuilderRequestedExclusionTokenLookup.machine
      (BuilderRequestedExclusionTokenLookup.finalConfiguration first second position older inside).state := by
  have hCases : BuilderExclusionClauseTokenSelector.endpoint first second position = .accept ∨
      BuilderExclusionClauseTokenSelector.endpoint first second position = .reject ∨
      BuilderExclusionClauseTokenSelector.endpoint first second position = .dead ∨
      BuilderExclusionClauseTokenSelector.endpoint first second position = .node BuilderExclusionClauseTokenSelector.separatorNode.reference ∨
      BuilderExclusionClauseTokenSelector.endpoint first second position = .node BuilderExclusionClauseTokenSelector.finishNode.reference := by
    unfold BuilderExclusionClauseTokenSelector.endpoint
    by_cases hZero : position = 0
    · rw [if_pos hZero]
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [if_neg hZero]
      by_cases hPast : BuilderExclusionClauseBoundary.boundary first.val second.val < position
      · rw [if_pos hPast]
        exact Or.inr (Or.inr (Or.inl rfl))
      · rw [if_neg hPast]
        by_cases hEnd : position = BuilderExclusionClauseBoundary.boundary first.val second.val
        · rw [if_pos hEnd]
          exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
        · rw [if_neg hEnd]
          rcases BuilderExclusionClauseTokenSelector.body_endpoint_terminal first second position
            (by omega) (by omega) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
  change WorkMachineProgramGraph.NoRuleAt BuilderRequestedExclusionTokenLookup.machine
    (WorkMachineChain.secondState (endpointState (BuilderExclusionClauseTokenSelector.endpoint first second position)))
  rcases hCases with h | h | h | h | h
  · rw [h]
    exact BuilderRequestedExclusionTokenLookup.noRuleAtAccept
  · rw [h]
    exact BuilderRequestedExclusionTokenLookup.noRuleAtReject
  · rw [h]
    exact BuilderRequestedExclusionTokenLookup.noRuleAtPadding
  · rw [h]
    exact BuilderRequestedExclusionTokenLookup.noRuleAtSeparator
  · rw [h]
    exact BuilderRequestedExclusionTokenLookup.noRuleAtFinish

theorem pair_lookup_values_retained {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) :
    ∃ scratch, BuilderRequestedPairVariables.lookupValues variables request older =
      BuilderRequestedPairLookup.initialValues variables request older ++ scratch := by
  unfold BuilderRequestedPairVariables.lookupValues BuilderExclusionPairLookup.resultValues
  split
  · simp only [BuilderExclusionPairRow.resultValues, List.append_assoc]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

def pairSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderExclusionPairLookup.spanPolynomial (BuilderPayloadBodyPreparation.spanPolynomial bound)

/-- This canonical bound also applies to invalid ordinals. It is not inferred
from the storage of a different blank-equivalent tape representation. -/
theorem pair_lookup_values_span {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (BuilderRequestedPairVariables.lookupValues variables request older)).length ≤
      (pairSpanPolynomial bound).eval input := by
  have hPrep := BuilderRequestedPairLookup.preparation_polynomial_bounds
    variables request older outside bound input hSpan
  have hPair := BuilderExclusionPairLookup.source_polynomial_bounds variables.length
    (request.clauseIndex - 1) (BuilderRequestedPairLookup.initialValues variables request older)
    (BuilderPayloadBodyPreparation.spanPolynomial bound) input
    (Nat.le_trans (Nat.le_add_right _ _) hPrep.1)
  exact hPair.1

def canonicalSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRequestedExclusionTokenLookup.canonicalSpanPolynomial bound) (pairSpanPolynomial bound)

/-- The request, canonical blank exterior, terminal state and both kinds of
space bound are all derived from the actual source/request execution. -/
theorem workRun_polynomial_lookup_with_frame {width : Nat} (variables : List (Fin width))
    (request : Request) (older : List Nat) (inside outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat) (hPositive : 0 < request.clauseIndex)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length +
      outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      workRunExact? BuilderRequestedExclusionTokenLookup.machine steps
        (BuilderRequestedExclusionTokenLookup.initialConfiguration variables request older inside outside) = some final ∧
      WorkMachineProgramGraph.NoRuleAt BuilderRequestedExclusionTokenLookup.machine final.state ∧
      BuilderRequestedExclusionTokenLookup.observe final = BuilderRequestedExclusionTokenLookup.canonicalToken variables request ∧
      (∃ scratch, values = BuilderRequestedPairLookup.initialValues variables request older ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values inside resultOutside) ∧
      BlankOutside resultOutside ∧
      (registerWord values).length + resultOutside.length ≤ (canonicalSpanPolynomial bound).eval input ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤
        inside.length + (BuilderRequestedExclusionTokenLookup.spanPolynomial bound).eval input ∧
      6 * steps ≤ (BuilderRequestedExclusionTokenLookup.rawTimePolynomial bound).eval input := by
  by_cases hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length
  · obtain ⟨first, second, steps, preparedOlder, final, _, hRetained, hRun, hEquivalent,
        hObserved, hCanonical, hSpace, hTime⟩ :=
      BuilderRequestedExclusionTokenLookup.workRun_valid_source_lookup variables request older inside outside
        bound input hPositive hBlank hValid hSpan
    refine ⟨steps, BuilderExclusionClauseTokenSelector.finalValues variables[first.val] variables[second.val]
        request.originalPosition BuilderRequestedExclusionInput.Position.retained preparedOlder,
      BuilderExclusionClauseTokenSelector.finalOutside variables[first.val] variables[second.val]
        request.originalPosition [], final, hRun, ?_, hObserved, ?_, hEquivalent.tape,
      selector_outside_blank _ _ _ [] blank_nil, ?_, hSpace, hTime⟩
    · rw [hEquivalent.state]
      exact selector_final_no_rule _ _ _ preparedOlder inside
    · obtain ⟨preparedScratch, hPrepared⟩ := hRetained
      obtain ⟨tokenScratch, hToken⟩ := selector_values_retained variables[first.val] variables[second.val]
        request.originalPosition BuilderRequestedExclusionInput.Position.retained preparedOlder
      refine ⟨preparedScratch ++ tokenScratch, ?_⟩
      rw [hToken, hPrepared, List.append_assoc]
    · simp only [canonicalSpanPolynomial, NatPolynomial.eval_add]
      exact Nat.le_trans hCanonical (Nat.le_add_right _ _)
  · have hInvalid : LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1 := by omega
    obtain ⟨steps, final, hRun, hEquivalent, hObserved, hSpace, hTime⟩ :=
      BuilderRequestedExclusionTokenLookup.workRun_invalid_source_lookup variables request older inside outside
        bound input hPositive hBlank hInvalid hSpan
    refine ⟨steps, BuilderRequestedPairVariables.lookupValues variables request older, [], final,
      hRun, ?_, hObserved, pair_lookup_values_retained variables request older,
      hEquivalent.tape, blank_nil, ?_, hSpace, hTime⟩
    · rw [hEquivalent.state]
      exact BuilderRequestedExclusionTokenLookup.noRuleAtInvalid
    · have hPair := pair_lookup_values_span variables request older outside bound input hSpan
      simp only [List.length_nil, Nat.add_zero, canonicalSpanPolynomial, NatPolynomial.eval_add]
      omega

theorem uniform_polynomial_lookup_with_frame {width : Nat} (variables : List (Fin width))
    (request : Request) (older : List Nat) (inside outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat) (hPositive : 0 < request.clauseIndex)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length +
      outside.length ≤ bound.eval input) :
    ∃ (rawSteps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      rawSteps ≤ (BuilderRequestedExclusionTokenLookup.rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine BuilderRequestedExclusionTokenLookup.machine) rawSteps
        (encodeWorkConfiguration
          (BuilderRequestedExclusionTokenLookup.initialConfiguration variables request older inside outside)) =
        encodeWorkConfiguration final ∧
      WorkMachineProgramGraph.NoRuleAt BuilderRequestedExclusionTokenLookup.machine final.state ∧
      BuilderRequestedExclusionTokenLookup.observe final = BuilderRequestedExclusionTokenLookup.canonicalToken variables request ∧
      (∃ scratch, values = BuilderRequestedPairLookup.initialValues variables request older ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values inside resultOutside) ∧
      BlankOutside resultOutside ∧
      (registerWord values).length + resultOutside.length ≤ (canonicalSpanPolynomial bound).eval input ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤
        inside.length + (BuilderRequestedExclusionTokenLookup.spanPolynomial bound).eval input := by
  obtain ⟨steps, values, resultOutside, final, hRun, hNoRule, hObserved,
      hRetained, hEquivalent, hBlankFinal, hCanonical, hSpace, hTime⟩ :=
    workRun_polynomial_lookup_with_frame variables request older inside outside bound input hPositive hBlank hSpan
  exact ⟨6 * steps, values, resultOutside, final, hTime,
    run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun,
    hNoRule, hObserved, hRetained, hEquivalent, hBlankFinal, hCanonical, hSpace⟩

end PNP.Concrete.CookLevin.BuilderExclusionTokenRecoveryFrame

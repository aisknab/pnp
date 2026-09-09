import PNP.Concrete.CookLevinBuilderRequestedExclusionTokenLookup

namespace PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup

open PipelineTape
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Request)
open BuilderExclusionPairSelection (selectedPair)
open PipelineStateNamespace (renameConfiguration)

example :
    ([trueState, falseState, paddingState, separatorState, finishState, invalidState] : List Nat).Pairwise
      (fun left right => left ≠ right) := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.terminal_states_distinct

example (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderExclusionClauseTokenSelector.observe configuration := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.observe_rename configuration

example {actual canonical : WorkConfiguration}
    (hEquivalent : WorkConfiguration.BlankEquivalent actual canonical) :
    observe actual = observe canonical := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.observe_blankEquivalent hEquivalent

example {width : Nat} (first second : Fin width) (position : Nat) (older : List Nat)
    (inside : List WorkSymbol) :
    observe (finalConfiguration first second position older inside) =
      (encodeClauseTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.final_observation first second position older inside

example (tape : WorkTape) : observe {state := invalidState, tape := tape} = none := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.observe_invalid tape

example {width : Nat} (variables : List (Fin width)) (request : Request) :
    canonicalToken variables request =
      ((LocalConstraint.exactlyOne variables).emit[request.clauseIndex]?).bind
        (fun clause => (encodeClauseTokens (BoundedClause.emit clause))[request.originalPosition]?) := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.canonicalToken_eq_emit variables request

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (first second : Fin variables.length) (hPositive : 0 < request.clauseIndex)
    (hPair : selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val)) :
    canonicalToken variables request =
      (encodeClauseTokens (BoundedClause.emit (excludeBoundedPairClause variables[first.val] variables[second.val])))[request.originalPosition]? := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.canonicalToken_selected variables request first second hPositive hPair

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (hPositive : 0 < request.clauseIndex)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1) :
    canonicalToken variables request = none := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.canonicalToken_invalid variables request hPositive hInvalid

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept machine := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.acceptState_ne_rejectState

example : WorkMachineProgramGraph.NoRuleAt machine paddingState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.noRuleAtPadding

example : WorkMachineProgramGraph.NoRuleAt machine separatorState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.noRuleAtSeparator

example : WorkMachineProgramGraph.NoRuleAt machine finishState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.noRuleAtFinish

example : WorkMachineProgramGraph.NoRuleAt machine invalidState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.noRuleAtInvalid

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (steps : Nat) (preparedOlder : List Nat) (final : WorkConfiguration),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      (∃ suffix, preparedOlder = BuilderRequestedPairLookup.initialValues variables request older ++ suffix) ∧
      workRunExact? machine steps (initialConfiguration variables request older inside outside) = some final ∧
      WorkConfiguration.BlankEquivalent final
        (finalConfiguration variables[first.val] variables[second.val] request.originalPosition preparedOlder inside) ∧
      observe final = canonicalToken variables request ∧
      (registerWord (BuilderExclusionClauseTokenSelector.finalValues variables[first.val] variables[second.val]
        request.originalPosition BuilderRequestedExclusionInput.Position.retained preparedOlder)).length +
        (BuilderExclusionClauseTokenSelector.finalOutside variables[first.val] variables[second.val] request.originalPosition []).length ≤
          (canonicalSpanPolynomial bound).eval input ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.workRun_valid_source_lookup variables request older inside outside bound input hPositive hBlank hValid hSpan

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ steps final,
      workRunExact? machine steps (initialConfiguration variables request older inside outside) = some final ∧
      WorkConfiguration.BlankEquivalent final {
        state := invalidState
        tape := endTape (BuilderRequestedPairVariables.lookupValues variables request older) inside []
      } ∧
      observe final = canonicalToken variables request ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.workRun_invalid_source_lookup variables request older inside outside bound input hPositive hBlank hInvalid hSpan

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ steps final,
      workRunExact? machine steps (initialConfiguration variables request older inside outside) = some final ∧
      observe final = canonicalToken variables request ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.workRun_polynomial_lookup variables request older inside outside bound input hPositive hBlank hSpan

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps final,
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (initialConfiguration variables request older inside outside)) = encodeWorkConfiguration final ∧
      observe final = canonicalToken variables request ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup.uniform_polynomial_lookup variables request older inside outside bound input hPositive hBlank hSpan

-- Independent endpoint meanings, invalid-request boundaries and cost composition.
example (tape : WorkTape) : observe {state := trueState, tape := tape} = some .t := rfl
example (tape : WorkTape) : observe {state := falseState, tape := tape} = some .f := rfl
example (tape : WorkTape) : observe {state := separatorState, tape := tape} = some .sep := rfl
example (tape : WorkTape) : observe {state := finishState, tape := tape} = some .finish := by
  have hTrue : finishState ≠ trueState :=
    fun h => (by decide : BuilderExclusionClauseTokenSelector.finishState ≠ 0) (WorkMachineChain.secondState_injective h)
  have hFalse : finishState ≠ falseState :=
    fun h => (by decide : BuilderExclusionClauseTokenSelector.finishState ≠ 1) (WorkMachineChain.secondState_injective h)
  have hSeparator : finishState ≠ separatorState :=
    fun h => (by decide : BuilderExclusionClauseTokenSelector.finishState ≠ BuilderExclusionClauseTokenSelector.separatorState)
      (WorkMachineChain.secondState_injective h)
  generalize hState : finishState = state
  have hNotTrue : state ≠ trueState := fun h => hTrue (hState.trans h)
  have hNotFalse : state ≠ falseState := fun h => hFalse (hState.trans h)
  have hNotSeparator : state ≠ separatorState := fun h => hSeparator (hState.trans h)
  unfold observe
  rw [if_neg hNotTrue, if_neg hNotFalse, if_neg hNotSeparator, if_pos hState.symm]
example (tape : WorkTape) : observe {state := paddingState, tape := tape} = none := rfl
example (tape : WorkTape) : observe {state := invalidState, tape := tape} = none := rfl
example : invalidState ≠ falseState := WorkMachineChain.firstState_ne_secondState _ _
example : machine =
    WorkMachineChain.machine BuilderRequestedExclusionInput.machine BuilderExclusionClauseTokenSelector.machine := rfl
example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input =
      (BuilderRequestedExclusionInput.rawTimePolynomial bound).eval input + 6 +
      (BuilderExclusionClauseTokenSelector.rawTimePolynomial (BuilderRequestedExclusionInput.canonicalSpanPolynomial bound)).eval input := rfl
example (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial bound).eval input = bound.eval input + (rawTimePolynomial bound).eval input := rfl
example (bound : NatPolynomial) :
    canonicalSpanPolynomial bound =
      BuilderExclusionClauseTokenSelector.spanPolynomial (BuilderRequestedExclusionInput.canonicalSpanPolynomial bound) := rfl
example {width : Nat} (request : Request) (hPositive : 0 < request.clauseIndex) :
    canonicalToken ([] : List (Fin width)) request = none := by
  exact canonicalToken_invalid [] request hPositive (by simp only [List.length_nil, LocalConstraint.pairCount]; omega)
example {width : Nat} (variables : List (Fin width)) (request : Request)
    (hPast : LocalConstraint.pairCount variables.length + 1 ≤ request.clauseIndex) :
    canonicalToken variables request = none := by
  exact canonicalToken_invalid variables request (by omega) (by omega)

end PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup

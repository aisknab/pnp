/-
Copyright (c) 2026 PNP Labs.
Exact contracts and boundary cases for derived exclusion-token recovery frames.
These checks do not supply a selected pair, execution trace or frame certificate.
-/
import PNP.Concrete.CookLevinBuilderExclusionTokenRecoveryFrame

namespace PNP.Concrete.CookLevin.BuilderExclusionTokenRecoveryFrameRegression

open PipelineTape
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Request)
open BuilderPayloadSourceSearchBlank
open BuilderExclusionTokenRecoveryFrame

example {width : Nat} (literals : List (BoundedLiteral width))
    (position : Nat) (older : List Nat) :
    ∃ scratch, BuilderLiteralListSearch.finalValues literals position older = older ++ scratch :=
  BuilderExclusionTokenRecoveryFrame.literal_list_values_retained literals position older

example {width : Nat} (literals : List (BoundedLiteral width))
    (position : Nat) (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralListSearch.finalOutside literals position outside) :=
  BuilderExclusionTokenRecoveryFrame.literal_list_outside_blank literals position outside hBlank

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) :
    ∃ scratch, BuilderExclusionClauseTokenSelector.finalValues first second position retained older =
      older ++ scratch :=
  BuilderExclusionTokenRecoveryFrame.selector_values_retained first second position retained older

example {width : Nat} (first second : Fin width) (position : Nat)
    (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderExclusionClauseTokenSelector.finalOutside first second position outside) :=
  BuilderExclusionTokenRecoveryFrame.selector_outside_blank first second position outside hBlank

example {width : Nat} (first second : Fin width) (position : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    WorkMachineProgramGraph.NoRuleAt BuilderRequestedExclusionTokenLookup.machine
      (BuilderRequestedExclusionTokenLookup.finalConfiguration first second position older inside).state :=
  BuilderExclusionTokenRecoveryFrame.selector_final_no_rule first second position older inside

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) :
    ∃ scratch, BuilderRequestedPairVariables.lookupValues variables request older =
      BuilderRequestedPairLookup.initialValues variables request older ++ scratch :=
  BuilderExclusionTokenRecoveryFrame.pair_lookup_values_retained variables request older

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (BuilderRequestedPairVariables.lookupValues variables request older)).length ≤
      (pairSpanPolynomial bound).eval input :=
  BuilderExclusionTokenRecoveryFrame.pair_lookup_values_span variables request older outside bound input hSpan

example {width : Nat} (variables : List (Fin width))
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
      6 * steps ≤ (BuilderRequestedExclusionTokenLookup.rawTimePolynomial bound).eval input :=
  BuilderExclusionTokenRecoveryFrame.workRun_polynomial_lookup_with_frame variables request older inside outside bound input hPositive hBlank hSpan

example {width : Nat} (variables : List (Fin width))
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
        inside.length + (BuilderRequestedExclusionTokenLookup.spanPolynomial bound).eval input :=
  BuilderExclusionTokenRecoveryFrame.uniform_polynomial_lookup_with_frame variables request older inside outside bound input hPositive hBlank hSpan

example {width : Nat} (position : Nat) (older : List Nat) :
    ∃ scratch, BuilderLiteralListSearch.finalValues ([] : List (BoundedLiteral width)) position older =
      older ++ scratch :=
  literal_list_values_retained [] position older

example {width : Nat} (literals : List (BoundedLiteral width)) (position count : Nat) :
    BlankOutside (BuilderLiteralListSearch.finalOutside literals position (List.replicate count WorkSymbol.blank)) :=
  literal_list_outside_blank literals position _ (BuilderRequestedPairLookup.blankExterior_replicate count)

example {width : Nat} (first second : Fin width) (retained older : List Nat) :
    BuilderExclusionClauseTokenSelector.finalValues first second 0 retained older =
      older ++ BuilderExclusionPairLiteralTokens.frame first.val second.val 0 retained := rfl

example {width : Nat} (first second : Fin width) (position count : Nat) :
    BlankOutside (BuilderExclusionClauseTokenSelector.finalOutside first second position
      (List.replicate count WorkSymbol.blank)) :=
  selector_outside_blank first second position _ (BuilderRequestedPairLookup.blankExterior_replicate count)

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1) :
    BuilderRequestedPairVariables.lookupValues variables request older =
      BuilderRequestedPairLookup.initialValues variables request older ++
        BuilderExclusionPairPreparation.history variables.length (request.clauseIndex - 1) := by
  unfold BuilderRequestedPairVariables.lookupValues BuilderExclusionPairLookup.resultValues
  rw [if_neg (Nat.not_lt.mpr hInvalid)]

example (bound : NatPolynomial) (input : Nat) :
    (canonicalSpanPolynomial bound).eval input =
      (BuilderRequestedExclusionTokenLookup.canonicalSpanPolynomial bound).eval input +
        (pairSpanPolynomial bound).eval input := rfl

example (tape : WorkTape) :
    BuilderRequestedExclusionTokenLookup.observe
      {state := BuilderRequestedExclusionTokenLookup.invalidState, tape := tape} = none :=
  BuilderRequestedExclusionTokenLookup.observe_invalid tape

example (tape : WorkTape) :
    BuilderRequestedExclusionTokenLookup.observe
      {state := BuilderRequestedExclusionTokenLookup.falseState, tape := tape} = some .f := rfl

end PNP.Concrete.CookLevin.BuilderExclusionTokenRecoveryFrameRegression

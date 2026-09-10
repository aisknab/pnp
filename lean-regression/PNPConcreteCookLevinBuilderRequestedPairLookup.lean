import PNP.Concrete.CookLevinBuilderRequestedPairLookup

open PNP PNP.Concrete PNP.Concrete.CookLevin
open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Request requestValues)
open BuilderLocalConstraintPayload (variableValues)
open PipelineStateNamespace (renameConfiguration)
open BuilderRequestedPairLookup

example (request : Request) : (countSuffix request).length = 12 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.countSuffix_length request

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat) :
    initialValues variables request older =
      (older ++ (variableValues variables).reverse) ++ [variables.length] ++ countSuffix request := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.count_layout variables request older

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (hPositive : 0 < request.clauseIndex) :
    workRunExact? preparationMachine (preparationSteps variables request)
      (workStartConfiguration preparationMachine (endTape (initialValues variables request older) inside outside)) =
      some {
        state := preparationMachine.acceptState
        tape := endTape (preparedValues variables request older) inside (preparedOutside variables request outside)
      } := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.preparation_workRunExact variables request older inside outside hPositive

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    (registerWord (preparedValues variables request older)).length + (preparedOutside variables request outside).length ≤
        (BuilderPayloadBodyPreparation.spanPolynomial bound).eval input ∧
      6 * preparationSteps variables request ≤ (BuilderPayloadBodyPreparation.rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.preparation_polynomial_bounds variables request older outside bound input hSpan

example (count : Nat) : BlankExterior (List.replicate count WorkSymbol.blank) := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.blankExterior_replicate count

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (outside : List WorkSymbol) (hBlank : BlankExterior outside) :
    BlankExterior (preparedOutside variables request outside) := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.preparedOutside_blank variables request outside hBlank

example (values : List Nat) (inside outside : List WorkSymbol)
    (hBlank : BlankExterior outside) :
    WorkTape.BlankEquivalent (endTape values inside outside) (endTape values inside []) := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.endTape_blankEquivalent values inside outside hBlank

example (program : WorkMachine) (steps : Nat) (initial final : WorkConfiguration)
    (hRun : workRunExact? program steps initial = some final) :
    storedCells final.tape ≤ storedCells initial.tape + steps := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.workRun_storedCells program steps initial final hRun

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept machine := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.acceptState_ne_rejectState

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside : List WorkSymbol) :
    (canonicalFinal variables request older inside).state = machine.acceptState ↔
      request.clauseIndex - 1 < LocalConstraint.pairCount variables.length := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.canonical_accept_iff variables request older inside

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside : List WorkSymbol) :
    (canonicalFinal variables request older inside).state = machine.rejectState ↔
      LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.canonical_reject_iff variables request older inside

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside : List WorkSymbol) :
    ∃ scratch, (canonicalFinal variables request older inside).tape =
      endTape (requestValues (.exactlyOne variables) request older ++ scratch) inside [] := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.canonical_request_retained variables request older inside

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BlankExterior outside)
    (hSpan : (registerWord (initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ final,
      workRunExact? machine (workSteps variables request) (initialConfiguration variables request older inside outside) = some final ∧
      WorkConfiguration.BlankEquivalent final (canonicalFinal variables request older inside) ∧
      (final.state = machine.acceptState ↔ request.clauseIndex - 1 < LocalConstraint.pairCount variables.length) ∧
      (final.state = machine.rejectState ↔ LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1) ∧
      storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * workSteps variables request ≤ (rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.workRun_polynomial_lookup variables request older inside outside bound input hPositive hBlank hSpan

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BlankExterior outside)
    (hSpan : (registerWord (initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps final,
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps (encodeWorkConfiguration (initialConfiguration variables request older inside outside)) =
        encodeWorkConfiguration final ∧
      WorkConfiguration.BlankEquivalent final (canonicalFinal variables request older inside) ∧
      (final.state = machine.acceptState ↔ request.clauseIndex - 1 < LocalConstraint.pairCount variables.length) ∧
      (final.state = machine.rejectState ↔ LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1) ∧
      storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairLookup.uniform_polynomial_lookup variables request older inside outside bound input hPositive hBlank hSpan

-- Independent checks for fixed addresses, retained request, real exterior and bounds.
example : preparationMachine =
    WorkMachineChain.machine (RegisterCopy.machine 12)
      (WorkMachineChain.machine (RegisterCopy.machine 2) BuilderRegisterCountdownControl.decrement) := rfl
example : BuilderRequestedPairLookup.machine =
    WorkMachineChain.machine preparationMachine BuilderExclusionPairLookup.machine := rfl
example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat) :
    preparedValues variables request older =
      requestValues (.exactlyOne variables) request older ++ [variables.length, request.clauseIndex - 1] := rfl
example {width : Nat} (variables : List (Fin width)) (request : Request) :
    preparedOutside variables request [] = [WorkSymbol.blank] := by
  simp only [preparedOutside, List.drop_nil]
example : ¬ BlankExterior [WorkSymbol.oneOne] := by
  intro h
  have hZero := h 0
  cases hZero
example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input =
      (BuilderPayloadBodyPreparation.rawTimePolynomial bound).eval input + 6 +
      (BuilderExclusionPairLookup.rawTimePolynomial (BuilderPayloadBodyPreparation.spanPolynomial bound)).eval input := rfl
example (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial bound).eval input = bound.eval input + (rawTimePolynomial bound).eval input := rfl

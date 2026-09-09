import PNP.Concrete.CookLevinBuilderPayloadBodyPreparation

open PNP PNP.Concrete PNP.Concrete.CookLevin
open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Family Request family body requestValues)
open BuilderLocalConstraintPayload (literalValues literalListValues variableValues)
open BuilderPayloadBodyPreparation

example (tag : Nat) (request : Request) :
    (countSuffix tag request).length = 13 := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.countSuffix_length tag request

example {width : Nat} (premises : List (BoundedLiteral width))
    (conclusion : BoundedLiteral width) (request : Request) (older : List Nat) :
    initialValues (.implication premises conclusion) request older ++ [0] =
      (older ++ (literalValues conclusion ++ literalListValues premises).reverse) ++
        [premises.length] ++ countSuffix 3 request := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.implication_count_layout premises conclusion request older

example {width : Nat} (variables : List (Fin width))
    (request : Request) (older : List Nat) :
    initialValues (.exactlyOne variables) request older ++ [0] =
      (older ++ (variableValues variables).reverse) ++ [variables.length] ++ countSuffix 4 request := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.positive_count_layout variables request older

example {width : Nat} (constraint : LocalConstraint width)
    (request : Request) (older : List Nat) :
    finalValues constraint request older =
      BuilderPayloadClauseTokenSelector.initialValues constraint request request.originalPosition older := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.final_values_search_input constraint request older

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (countMachine (family constraint)) (countSteps constraint request)
      (workStartConfiguration (countMachine (family constraint))
        (endTape (initialValues constraint request older ++ [0]) inside outside)) =
      some {
        state := (countMachine (family constraint)).acceptState
        tape := endTape (initialValues constraint request older ++ [0, (body constraint).length])
          inside (outside.drop ((body constraint).length + 1))
      } := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.count_workRunExact constraint request older inside outside

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine (family constraint)) (workSteps constraint request)
      (initialConfiguration constraint request older inside outside) =
      some (finalConfiguration constraint request older inside outside) := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.workRunExact constraint request older inside outside

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine (family constraint))) (6 * workSteps constraint request)
      (encodeWorkConfiguration (initialConfiguration constraint request older inside outside)) =
      encodeWorkConfiguration (finalConfiguration constraint request older inside outside) := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.run_compile_exact constraint request older inside outside

example {width : Nat} (constraint : LocalConstraint width)
    (request : Request) (older : List Nat) :
    finalValues constraint request older =
      requestValues constraint request older ++ [0, (body constraint).length, request.originalPosition] := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.original_request_preserved constraint request older

example {width : Nat} (constraint : LocalConstraint width)
    (request : Request) (outside : List WorkSymbol) :
    (finalOutside constraint request outside).length ≤ outside.length := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.finalOutside_length_le constraint request outside

example (route : Family) :
    (machine route).rules.Pairwise WorkMachineChain.QueryDistinct := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.rules_pairwise_query_distinct route

example (route : Family) : WorkMachineChain.NoRuleAtAccept (machine route) := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.noRuleAtAccept route

example (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) (machine route).rejectState := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.noRuleAtReject route

example (route : Family) :
    (machine route).acceptState ≠ (machine route).rejectState := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.acceptState_ne_rejectState route

example {width : Nat} (constraint : LocalConstraint width)
    (request : Request) (older : List Nat) (bound : Nat)
    (hSpan : (registerWord (initialValues constraint request older)).length ≤ bound) :
    (body constraint).length ≤ bound + 1 ∧ request.originalPosition ≤ bound ∧
      request.gap.length + request.gap.sum + request.clauseIndex + request.originalPosition ≤ bound := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.initial_scalar_bounds constraint request older bound hSpan

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (outside : List WorkSymbol) (bound : Nat)
    (hSpan : (registerWord (initialValues constraint request older)).length + outside.length ≤ bound) :
    (registerWord (finalValues constraint request older)).length +
        (finalOutside constraint request outside).length ≤ spanBound bound ∧
      workSteps constraint request ≤ workBound bound := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.space_time_bounds constraint request older outside bound hSpan

example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.rawTimePolynomial_eval bound input

example (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial bound).eval input = spanBound (bound.eval input) := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.spanPolynomial_eval bound input

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request older)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues constraint request older)).length +
        (finalOutside constraint request outside).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps constraint request ≤ (rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.source_polynomial_bounds constraint request older outside bound input hSpan

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine (machine (family constraint))) rawSteps
        (encodeWorkConfiguration (initialConfiguration constraint request older inside outside)) =
        encodeWorkConfiguration (finalConfiguration constraint request older inside outside) ∧
      (finalConfiguration constraint request older inside outside).tape =
        endTape (BuilderPayloadClauseTokenSelector.initialValues constraint request request.originalPosition older)
          inside (finalOutside constraint request outside) ∧
      (registerWord (finalValues constraint request older)).length +
        (finalOutside constraint request outside).length ≤ (spanPolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyPreparation.uniform_body_preparation constraint request older inside outside bound input hSpan

-- Independent finite control and polynomial-shape expectations.
example : countMachine .required = RegisterConstant.machine 1 := rfl
example : countMachine .implication =
    WorkMachineChain.machine (RegisterCopy.machine 13) BuilderConstraintRegionAssembly.Increment.machine := rfl
example : countMachine .positive = RegisterCopy.machine 13 := rfl
example (route : Family) : machine route =
    WorkMachineChain.machine (RegisterConstant.machine 0)
      (WorkMachineChain.machine (countMachine route) (RegisterCopy.machine 2)) := rfl
example (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial bound).eval input = 3 * bound.eval input + 4 := rfl

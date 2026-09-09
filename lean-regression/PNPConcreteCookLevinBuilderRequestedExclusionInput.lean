import PNP.Concrete.CookLevinBuilderRequestedExclusionInput

namespace PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Request requestValues)
open BuilderRequestedPairVariables (lookupValues)
open BuilderRequestedPairVariables.First (rowWidth)
open BuilderRegisterExpression (Expr)

example (first second : Nat) (firstWritten secondWritten : List Nat)
    (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    (after first second firstWritten secondWritten).length = 20 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.after_length first second firstWritten secondWritten hFirst hSecond

example (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.values expression environment = scratch environment := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.expression_values environment

example (environment : Fin 9 → Nat) : (scratch environment).length = 5 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.scratch_length environment

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length) :
    lookupValues variables request older =
      BuilderRequestedPairLookup.initialValues variables request older ++ pairSuffix variables request := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.lookup_suffix variables request older hValid

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat) :
    BuilderRequestedPairLookup.initialValues variables request older =
      requestPrefix variables request older ++ [request.originalPosition] := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.request_prefix variables request older

example {width : Nat} (variables : List (Fin width)) (request : Request) (older history : List Nat)
    (environment : Fin 9 → Nat) (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hLayout : lookupValues variables request older =
      BuilderRequestedPairVariables.First.initialValues (BuilderLocalConstraintPayload.variableValues variables) older history environment) :
    (pairSuffix variables request).length = 25 + 9 * rowWidth environment := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.pairSuffix_length variables request older history environment hValid hHistory hLayout

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat) :
    (reader variables request older first second firstWritten secondWritten environment).reverse ++ [address environment] =
      initialValues variables request older first second firstWritten secondWritten ++ scratch environment := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.reader_layout variables request older first second firstWritten secondWritten environment

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat)
    (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSuffix : (pairSuffix variables request).length = 25 + 9 * rowWidth environment) :
    address environment < (reader variables request older first second firstWritten secondWritten environment).length := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.reader_address_lt variables request older first second firstWritten secondWritten environment hFirst hSecond hValid hSuffix

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat)
    (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSuffix : (pairSuffix variables request).length = 25 + 9 * rowWidth environment) :
    (reader variables request older first second firstWritten secondWritten environment)[address environment]'
      (reader_address_lt variables request older first second firstWritten secondWritten environment hFirst hSecond hValid hSuffix) =
      request.originalPosition := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.reader_address_value variables request older first second firstWritten secondWritten environment hFirst hSecond hValid hSuffix

example {width : Nat} (variables : List (Fin width)) (request : Request) (older history : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat) (inside : List WorkSymbol)
    (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hLayout : lookupValues variables request older =
      BuilderRequestedPairVariables.First.initialValues (BuilderLocalConstraintPayload.variableValues variables) older history environment) :
    workRunExact? positionMachine (positionSteps variables request older first second firstWritten secondWritten environment)
      (workStartConfiguration positionMachine
        (endTape (initialValues variables request older first second firstWritten secondWritten) inside [])) =
      some {
        state := positionMachine.acceptState
        tape := endTape (positionValues variables request older first second firstWritten secondWritten environment) inside []
      } := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.position_workRunExact variables request older history first second firstWritten secondWritten environment inside hFirst hSecond hValid hHistory hLayout

example {width : Nat} (variables : List (Fin width)) (request : Request) (older history : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat)
    (bound : NatPolynomial) (input : Nat)
    (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hLayout : lookupValues variables request older =
      BuilderRequestedPairVariables.First.initialValues (BuilderLocalConstraintPayload.variableValues variables) older history environment)
    (hSpan : (registerWord (initialValues variables request older first second firstWritten secondWritten)).length ≤ bound.eval input) :
    (registerWord (positionValues variables request older first second firstWritten secondWritten environment)).length ≤
      (positionSpanPolynomial bound).eval input ∧
    6 * positionSteps variables request older first second firstWritten secondWritten environment ≤
      (positionRawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.position_polynomial_bounds variables request older history first second firstWritten secondWritten environment bound input hFirst hSecond hValid hHistory hLayout hSpan

example (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    (packingSource environment first second position firstWritten secondWritten).length = 26 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.packingSource_length environment first second position firstWritten secondWritten hFirst hSecond

example (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    List.ofFn (packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond) =
      packingSource environment first second position firstWritten secondWritten := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.packingEnvironment_values environment first second position firstWritten secondWritten hFirst hSecond

example (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond ⟨7, by decide⟩ = first := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.packingEnvironment_first environment first second position firstWritten secondWritten hFirst hSecond

example (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond ⟨19, by decide⟩ = second := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.packingEnvironment_second environment first second position firstWritten secondWritten hFirst hSecond

example (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond ⟨25, by decide⟩ = position := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.packingEnvironment_position environment first second position firstWritten secondWritten hFirst hSecond

example : retained.length = 11 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.retained_length

example : fields.length = 14 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.fields_length

example (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    BuilderRegisterPack.values fields
      (packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond) =
      BuilderExclusionPairLiteralTokens.frame first second position retained := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.packed_values environment first second position firstWritten secondWritten hFirst hSecond

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat) :
    positionValues variables request older first second firstWritten secondWritten environment =
      lookupValues variables request older ++
        packingSource environment first second request.originalPosition firstWritten secondWritten := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.position_values_layout variables request older first second firstWritten secondWritten environment

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length) :
    positionValues variables request older first second firstWritten secondWritten environment =
      BuilderRequestedPairLookup.initialValues variables request older ++
        (pairSuffix variables request ++ after first second firstWritten secondWritten ++
          scratch environment ++ [request.originalPosition]) := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.position_values_preserve_request variables request older first second firstWritten secondWritten environment hValid

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.acceptState_ne_rejectState

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (inside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (initialValues variables request older first second firstWritten secondWritten)).length ≤ bound.eval input) :
    ∃ (steps : Nat) (newOlder : List Nat),
      (∃ suffix, newOlder = BuilderRequestedPairLookup.initialValues variables request older ++ suffix) ∧
      workRunExact? machine steps
        (workStartConfiguration machine
          (endTape (initialValues variables request older first second firstWritten secondWritten) inside [])) =
        some {
          state := machine.acceptState
          tape := endTape (BuilderExclusionPairLiteralTokens.initialValues first second request.originalPosition retained newOlder) inside []
        } ∧
      (registerWord (BuilderExclusionPairLiteralTokens.initialValues first second request.originalPosition retained newOlder)).length ≤
        (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position.canonical_source_prepare variables request older first second firstWritten secondWritten inside bound input hFirst hSecond hValid hSpan

end PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position

namespace PNP.Concrete.CookLevin.BuilderRequestedExclusionInput

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Request)
open BuilderExclusionPairSelection (selectedPair)
open WorkMachineProgramGraph (Node Graph)
open WorkMachineProgramPath (AcceptPath)

example : graph.nodes.length = 2 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.graph_nodes_length

example : graph.WellFormed := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.graph_wellFormed

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.acceptState_ne_rejectState

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (steps : Nat) (newOlder : List Nat) (final : WorkConfiguration),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      (∃ suffix, newOlder = BuilderRequestedPairLookup.initialValues variables request older ++ suffix) ∧
      workRunExact? machine steps
        (workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)) = some final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.acceptState
        tape := endTape (BuilderExclusionPairLiteralTokens.initialValues variables[first.val].val variables[second.val].val
          request.originalPosition Position.retained newOlder) inside []
      } ∧
      (registerWord (BuilderExclusionPairLiteralTokens.initialValues variables[first.val].val variables[second.val].val
        request.originalPosition Position.retained newOlder)).length ≤ (canonicalSpanPolynomial bound).eval input ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.workRun_source_prepare variables request older inside outside bound input hPositive hBlank hValid hSpan

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (rawSteps : Nat) (newOlder : List Nat) (final : WorkConfiguration),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      (∃ suffix, newOlder = BuilderRequestedPairLookup.initialValues variables request older ++ suffix) ∧
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (workStartConfiguration machine
          (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside))) =
        encodeWorkConfiguration final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.acceptState
        tape := endTape (BuilderExclusionPairLiteralTokens.initialValues variables[first.val].val variables[second.val].val
          request.originalPosition Position.retained newOlder) inside []
      } ∧
      (registerWord (BuilderExclusionPairLiteralTokens.initialValues variables[first.val].val variables[second.val].val
        request.originalPosition Position.retained newOlder)).length ≤ (canonicalSpanPolynomial bound).eval input ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.uniform_source_prepare variables request older inside outside bound input hPositive hBlank hValid hSpan

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ steps final,
      workRunExact? machine steps
        (workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)) =
        some final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.rejectState
        tape := endTape (BuilderRequestedPairVariables.lookupValues variables request older) inside []
      } ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.workRun_invalid_source_prepare variables request older inside outside bound input hPositive hBlank hInvalid hSpan

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps final,
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (workStartConfiguration machine
          (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside))) =
        encodeWorkConfiguration final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.rejectState
        tape := endTape (BuilderRequestedPairVariables.lookupValues variables request older) inside []
      } ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.uniform_invalid_source_prepare variables request older inside outside bound input hPositive hBlank hInvalid hSpan

end PNP.Concrete.CookLevin.BuilderRequestedExclusionInput

open PNP PNP.Concrete PNP.Concrete.CookLevin
open BuilderRequestedExclusionInput
open BuilderUnaryPolynomial (registerWord)

-- Independent physical address, fixed schema, rejection and cost contracts.
example (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.eval Position.expression environment =
      9 * environment ⟨7, by decide⟩ + 49 := rfl
example : BuilderRegisterExpression.nodeCount Position.expression = 5 := rfl
example : Position.fields =
    [BuilderRegisterPack.Field.argument ⟨7, by decide⟩] ++
      List.replicate 11 (.constant 0) ++ [.argument ⟨19, by decide⟩, .argument ⟨25, by decide⟩] := rfl
example : Position.retained = List.replicate 11 0 := rfl
example : lookupNode.onReject = .reject := rfl
example : lookupNode.program = BuilderRequestedPairVariables.machine := rfl
example : prepareNode.program = Position.machine := rfl
example : prepareNode.onAccept = .accept := rfl
example : prepareNode.onReject = .dead := rfl
example (bound : NatPolynomial) :
    canonicalInputSpanPolynomial bound =
      BuilderRequestedPairVariables.Second.pairSpanPolynomial (BuilderRequestedPairVariables.canonicalSpanPolynomial bound) := rfl
example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input =
      (BuilderRequestedPairVariables.rawTimePolynomial bound).eval input + 12 +
      (Position.rawTimePolynomial (canonicalInputSpanPolynomial bound)).eval input := rfl
example (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial bound).eval input = bound.eval input + (rawTimePolynomial bound).eval input := rfl
example (bound : NatPolynomial) :
    canonicalSpanPolynomial bound = Position.spanPolynomial (canonicalInputSpanPolynomial bound) := rfl
example (bound : NatPolynomial) (input : Nat) :
    (Position.positionRawTimePolynomial bound).eval input =
      (BuilderRegisterExpression.rawTimePolynomial Position.expression bound).eval input + 6 +
      (BuilderRegisterIndexedCopy.rawTimePolynomial (Position.middleSpanPolynomial bound)).eval input := rfl
example (bound : NatPolynomial) (input : Nat) :
    (Position.rawTimePolynomial bound).eval input =
      (Position.positionRawTimePolynomial bound).eval input + 6 +
      (BuilderRegisterPack.rawTimePolynomial Position.fields (Position.positionSpanPolynomial bound)).eval input := rfl

import PNP.Concrete.CookLevinBuilderLiteralSearchComparison

open PNP.Concrete PNP.Concrete.CookLevin
open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (literalListValues)
open BuilderLiteralSearchFrame (fieldStride valueHistory widthExpression widthHistory
  valueEnvironment valueEnvironment_values widthExpression_values chunk comparisonResult comparisonHistory)
open BuilderLiteralSearchComparison

-- Independent operand, address-history and exact boundary fixtures.
example : List.ofFn (packedEnvironment 1 2 5 3) = [1,2,5,19,1,19,8,27,3,3,2,5] := rfl
example : BuilderRegisterPack.values argumentFields (packedEnvironment 1 2 5 3) = [5,5] := rfl
example : (preparationHistory 1 2 5 3).length = 12 := rfl
example : initialValues [4,1,7,0] [9] [] 0 2 3 = [9,0,7,1,4,0,2,3] := rfl
example : (finalValues [4,1,7,0] [9] [] 0 2 3 7).length = 22 := by
  simp only [finalValues, baseValues, List.length_append, List.length_reverse, BuilderLiteralSearchFrame.chunk_length]
  rfl
example : BuilderLiteralSearchFrame.residual 4 3 = 4 := rfl
example : BuilderLiteralSearchFrame.residual 5 3 = 0 := rfl
example : BuilderLiteralSearchFrame.residual 8 3 = 3 := rfl
example (payload older prior : List Nat) (ordinal count value : Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration payload older prior ordinal count (value + 1) value inside outside).state = machine.acceptState :=
  (final_accept_iff _ _ _ _ _ _ _ _ _).2 (by omega)
example (payload older prior : List Nat) (ordinal count value : Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration payload older prior ordinal count (value + 2) value inside outside).state = machine.rejectState :=
  (final_reject_iff _ _ _ _ _ _ _ _ _).2 (Nat.le_refl _)
example (payload older prior : List Nat) (ordinal count value : Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration payload older prior ordinal count (value + 3) value inside outside).state = machine.rejectState :=
  (final_reject_iff _ _ _ _ _ _ _ _ _).2 (by omega)
example (ordinal position value : Nat) : finalOutside ordinal position value [] = [] := by
  simp only [finalOutside, prepareOutside, widthOutside, valueOutside, List.drop_nil]

example (ordinal count position value : Nat) :
    List.ofFn (packedEnvironment ordinal count position value) =
      preparationHistory ordinal count position value :=
  environment_values ordinal count position value

example (ordinal count position value : Nat) :
    BuilderRegisterPack.values argumentFields (packedEnvironment ordinal count position value) =
      [position, value + 2] :=
  packed_values ordinal count position value

example (ordinal count position value : Nat) :
    (preparationHistory ordinal count position value).length = 12 :=
  preparationHistory_length ordinal count position value

example (ordinal count position value : Nat) :
    chunk ordinal count position value =
      preparationHistory ordinal count position value ++ comparisonHistory position value :=
  chunk_eq ordinal count position value

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? prepareMachine
      (prepareSteps (literalListValues literals) prior index.val count position literals[index.val].index.val)
      (workStartConfiguration prepareMachine
        (endTape (initialValues (literalListValues literals) older prior index.val count position) inside outside)) =
      some {state := prepareMachine.acceptState,
            tape := prepareTape (literalListValues literals) older prior index.val count position
              literals[index.val].index.val inside outside} :=
  prepare_workRunExact literals index prior hPrior count position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine
      (workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val)
      (initialConfiguration (literalListValues literals) older prior index.val count position inside outside) =
      some (finalConfiguration (literalListValues literals) older prior index.val count position
        literals[index.val].index.val inside outside) :=
  workRunExact literals index prior hPrior count position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine)
      (6 * workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val)
      (encodeWorkConfiguration (initialConfiguration (literalListValues literals) older prior index.val count position inside outside)) =
      encodeWorkConfiguration (finalConfiguration (literalListValues literals) older prior index.val count position
        literals[index.val].index.val inside outside) :=
  run_compile_exact literals index prior hPrior count position older inside outside

example (payload older prior : List Nat) (ordinal count position value : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration payload older prior ordinal count position value inside outside).state = machine.acceptState ↔
      position < value + 2 :=
  final_accept_iff payload older prior ordinal count position value inside outside

example (payload older prior : List Nat) (ordinal count position value : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration payload older prior ordinal count position value inside outside).state = machine.rejectState ↔
      value + 2 ≤ position :=
  final_reject_iff payload older prior ordinal count position value inside outside

example (payload older prior : List Nat) (ordinal count position value : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration payload older prior ordinal count position value inside outside).tape =
      endTape (finalValues payload older prior ordinal count position value) inside
        (finalOutside ordinal position value outside) :=
  final_tape payload older prior ordinal count position value inside outside

example (ordinal position value : Nat) (outside : List WorkSymbol) :
    (finalOutside ordinal position value outside).length ≤ outside.length :=
  finalOutside_length_le ordinal position value outside

example (payload older prior : List Nat) (ordinal count position value : Nat)
    (outside : List WorkSymbol) :
    (registerWord (finalValues payload older prior ordinal count position value)).length +
      (finalOutside ordinal position value outside).length ≤
      (registerWord (initialValues payload older prior ordinal count position)).length + outside.length +
        (registerWord (chunk ordinal count position value)).length :=
  final_span_le_initial_add_chunk payload older prior ordinal count position value outside

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderLiteralSearchComparison.rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept machine :=
  BuilderLiteralSearchComparison.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderLiteralSearchComparison.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState :=
  BuilderLiteralSearchComparison.acceptState_ne_rejectState

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues (literalListValues literals) older prior index.val count position)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (prepareOlder (literalListValues literals) older prior index.val count position literals[index.val].index.val ++
      [position, literals[index.val].index.val + 2])).length +
      (prepareOutside index.val position literals[index.val].index.val outside).length ≤
      (prepareSpanPolynomial bound).eval input ∧
    6 * prepareSteps (literalListValues literals) prior index.val count position literals[index.val].index.val ≤
      (prepareRawTimePolynomial bound).eval input :=
  prepare_source_polynomial_bounds literals index prior hPrior count position older outside bound input hSpan

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues (literalListValues literals) older prior index.val count position)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (finalValues (literalListValues literals) older prior index.val count position literals[index.val].index.val)).length +
      (finalOutside index.val position literals[index.val].index.val outside).length ≤ (spanPolynomial bound).eval input ∧
    6 * workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val ≤
      (rawTimePolynomial bound).eval input :=
  source_polynomial_bounds literals index prior hPrior count position older outside bound input hSpan

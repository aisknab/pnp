import PNP.Concrete.CookLevinBuilderLiteralSearchSelect

open PNP.Concrete PNP.Concrete.CookLevin
open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (literalListValues signValue)
open PipelineStateNamespace (renameConfiguration)
open BuilderLiteralSearchSelect

-- Independent addresses, post-comparison environment and three-way outcomes.
example : signHistory 1 false = [19,1,19,21,40,0] := rfl
example : List.ofFn (argumentEnvironment 1 2 5 3 false) =
    [1,2,5,19,1,19,8,27,3,3,2,5,5,0,5,5,0,19,1,19,21,40,0] := rfl
example : BuilderRegisterPack.values argumentFields (argumentEnvironment 1 2 5 3 false) = [0,3,5] := rfl
example : (history 1 2 5 3 false).length = 23 := history_length _ _ _ _ _
example (tape : WorkTape) :
    observe {state := WorkMachineChain.secondState 0, tape := tape} = some .t := rfl
example (tape : WorkTape) :
    observe {state := WorkMachineChain.secondState 1, tape := tape} = some .f := rfl
example (tape : WorkTape) :
    observe {state := WorkMachineChain.secondState 2, tape := tape} = none := rfl
example (payload older prior : List Nat) (ordinal count value : Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration payload older prior ordinal count 0 value true inside outside) = some .t := rfl
example (payload older prior : List Nat) (ordinal count value : Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration payload older prior ordinal count 0 value false inside outside) = some .f := rfl
example (payload older prior : List Nat) (ordinal count : Nat) (positive : Bool) (inside outside : List WorkSymbol) :
    observe (finalConfiguration payload older prior ordinal count 1 0 positive inside outside) = some .f := rfl
example (payload older prior : List Nat) (ordinal count : Nat) (positive : Bool) (inside outside : List WorkSymbol) :
    observe (finalConfiguration payload older prior ordinal count 2 0 positive inside outside) = none := rfl
example (ordinal position value : Nat) (positive : Bool) : prepareOutside ordinal position value positive [] = [] := by
  simp only [prepareOutside, signOutside, List.drop_nil]

example (ordinal : Nat) (positive : Bool) : (signHistory ordinal positive).length = 6 :=
  BuilderLiteralSearchSelect.signHistory_length ordinal positive

example (ordinal count position value : Nat) (positive : Bool) :
    (history ordinal count position value positive).length = 23 :=
  BuilderLiteralSearchSelect.history_length ordinal count position value positive

example (ordinal count position value : Nat) (positive : Bool) :
    List.ofFn (argumentEnvironment ordinal count position value positive) =
      history ordinal count position value positive :=
  BuilderLiteralSearchSelect.environment_values ordinal count position value positive

example (ordinal count position value : Nat) (positive : Bool) :
    BuilderRegisterPack.values argumentFields (argumentEnvironment ordinal count position value positive) =
      BuilderLiteralTokenSelector.frame positive value position :=
  BuilderLiteralSearchSelect.packed_values ordinal count position value positive

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? prepareMachine
      (prepareSteps (literalListValues literals) prior index.val count position literals[index.val].index.val literals[index.val].positive)
      (workStartConfiguration prepareMachine
        (endTape (initialValues (literalListValues literals) older prior index.val count position literals[index.val].index.val) inside outside)) =
      some {state := prepareMachine.acceptState,
            tape := prepareTape (literalListValues literals) older prior index.val count position
              literals[index.val].index.val literals[index.val].positive inside outside} :=
  BuilderLiteralSearchSelect.prepare_workRunExact literals index prior hPrior count position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine
      (workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val literals[index.val].positive)
      (initialConfiguration (literalListValues literals) older prior index.val count position literals[index.val].index.val inside outside) =
      some (finalConfiguration (literalListValues literals) older prior index.val count position
        literals[index.val].index.val literals[index.val].positive inside outside) :=
  BuilderLiteralSearchSelect.workRunExact literals index prior hPrior count position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine)
      (6 * workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val literals[index.val].positive)
      (encodeWorkConfiguration (initialConfiguration (literalListValues literals) older prior index.val count position literals[index.val].index.val inside outside)) =
      encodeWorkConfiguration (finalConfiguration (literalListValues literals) older prior index.val count position
        literals[index.val].index.val literals[index.val].positive inside outside) :=
  BuilderLiteralSearchSelect.run_compile_exact literals index prior hPrior count position older inside outside

example (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderLiteralTokenSelector.observe configuration :=
  BuilderLiteralSearchSelect.observe_renamed configuration

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior older : List Nat) (count position : Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration (literalListValues literals) older prior index.val count position
      literals[index.val].index.val literals[index.val].positive inside outside) =
      DirectToken.literalSlot literals[index.val].emit position :=
  BuilderLiteralSearchSelect.canonical_result literals index prior older count position inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun machine
      (workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val literals[index.val].positive)
      (initialConfiguration (literalListValues literals) older prior index.val count position literals[index.val].index.val inside outside)) =
      DirectToken.literalSlot literals[index.val].emit position :=
  BuilderLiteralSearchSelect.workRun_observes_literal literals index prior hPrior count position older inside outside

example (payload older prior : List Nat) (ordinal count position value : Nat) (positive : Bool)
    (inside outside : List WorkSymbol) (hHit : position < value + 2) :
    (finalConfiguration payload older prior ordinal count position value positive inside outside).state = machine.acceptState ∨
    (finalConfiguration payload older prior ordinal count position value positive inside outside).state = machine.rejectState :=
  BuilderLiteralSearchSelect.hit_terminal payload older prior ordinal count position value positive inside outside hHit

example (payload older prior : List Nat) (ordinal count position value : Nat) (positive : Bool)
    (inside outside : List WorkSymbol) :
    (finalConfiguration payload older prior ordinal count position value positive inside outside).tape =
      endTape (BuilderLiteralTokenSelector.finalValues positive value position
        (prepareOlder payload older prior ordinal count position value positive))
        inside (BuilderLiteralTokenSelector.finalOutside positive value position
          (prepareOutside ordinal position value positive outside)) :=
  BuilderLiteralSearchSelect.final_tape payload older prior ordinal count position value positive inside outside

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderLiteralSearchSelect.rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept machine :=
  BuilderLiteralSearchSelect.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderLiteralSearchSelect.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState :=
  BuilderLiteralSearchSelect.acceptState_ne_rejectState

example : WorkMachineProgramGraph.NoRuleAt machine (WorkMachineChain.secondState 2) :=
  BuilderLiteralSearchSelect.noRuleAtPadding

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues (literalListValues literals) older prior index.val count position literals[index.val].index.val)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (prepareOlder (literalListValues literals) older prior index.val count position literals[index.val].index.val literals[index.val].positive ++
      BuilderLiteralTokenSelector.frame literals[index.val].positive literals[index.val].index.val position)).length +
      (prepareOutside index.val position literals[index.val].index.val literals[index.val].positive outside).length ≤
      (prepareSpanPolynomial bound).eval input ∧
    6 * prepareSteps (literalListValues literals) prior index.val count position literals[index.val].index.val literals[index.val].positive ≤
      (prepareRawTimePolynomial bound).eval input :=
  BuilderLiteralSearchSelect.prepare_source_polynomial_bounds literals index prior hPrior count position older outside bound input hSpan

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues (literalListValues literals) older prior index.val count position literals[index.val].index.val)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (BuilderLiteralTokenSelector.finalValues literals[index.val].positive literals[index.val].index.val position
      (prepareOlder (literalListValues literals) older prior index.val count position literals[index.val].index.val literals[index.val].positive))).length +
      (BuilderLiteralTokenSelector.finalOutside literals[index.val].positive literals[index.val].index.val position
        (prepareOutside index.val position literals[index.val].index.val literals[index.val].positive outside)).length ≤
      (spanPolynomial bound).eval input ∧
    6 * workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val literals[index.val].positive ≤
      (rawTimePolynomial bound).eval input :=
  BuilderLiteralSearchSelect.source_polynomial_bounds literals index prior hPrior count position older outside bound input hSpan

import PNP.Concrete.CookLevinBuilderLiteralClauseTokenSelector

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderLiteralClauseTokenSelector PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

example : graph.nodes.length = 6 :=
  BuilderLiteralClauseTokenSelector.graph_nodes_length

example :
    ([trueState,1,2,separatorState,finishState] : List Nat).Pairwise (fun left right => left ≠ right) :=
  BuilderLiteralClauseTokenSelector.terminal_states_distinct

example : graph.WellFormed :=
  BuilderLiteralClauseTokenSelector.graph_wellFormed

example : WorkMachineChain.NoRuleAtAccept machine :=
  BuilderLiteralClauseTokenSelector.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderLiteralClauseTokenSelector.noRuleAtReject

example : WorkMachineProgramGraph.NoRuleAt machine 2 :=
  BuilderLiteralClauseTokenSelector.noRuleAtPadding

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderLiteralClauseTokenSelector.rules_pairwise_query_distinct

example : machine.acceptState ≠ machine.rejectState :=
  BuilderLiteralClauseTokenSelector.acceptState_ne_rejectState

example : WorkMachineProgramGraph.NoRuleAt machine separatorState :=
  BuilderLiteralClauseTokenSelector.noRuleAtSeparator

example : WorkMachineProgramGraph.NoRuleAt machine finishState :=
  BuilderLiteralClauseTokenSelector.noRuleAtFinish

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat) :
    initialValues literals position older = entryOlder literals older ++ [position] :=
  BuilderLiteralClauseTokenSelector.initial_values_suffix literals position older

example (position : Nat) : BuilderUnaryTagMatch.workSteps 0 position = 3 :=
  BuilderLiteralClauseTokenSelector.zero_test_steps position

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (hBody : position < DirectToken.boundedLiteralListWidth literals) :
    BuilderLiteralListSearch.endpoint literals position = .accept ∨
      BuilderLiteralListSearch.endpoint literals position = .reject :=
  BuilderLiteralClauseTokenSelector.search_body_endpoint literals position hBody

example {width : Nat} (literals : List (BoundedLiteral width))
    (payload older prior : List Nat) (ordinal position : Nat)
    (hPast : DirectToken.boundedLiteralListWidth literals ≤ position) :
    BuilderLiteralListSearch.endpoint literals position = .dead ∧
      ∃ before, BuilderLiteralListSearch.finishValues payload older literals ordinal prior position =
        before ++ [position - DirectToken.boundedLiteralListWidth literals] :=
  BuilderLiteralClauseTokenSelector.search_exhausted_frame literals payload older prior ordinal position hPast

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps literals position) (initialConfiguration literals position older inside outside) =
      some (finalConfiguration literals position older inside outside) :=
  BuilderLiteralClauseTokenSelector.workRunExact literals position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps literals position)
      (encodeWorkConfiguration (initialConfiguration literals position older inside outside)) =
      encodeWorkConfiguration (finalConfiguration literals position older inside outside) :=
  BuilderLiteralClauseTokenSelector.run_compile_exact literals position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration literals position older inside outside).tape =
      endTape (finalValues literals position older) inside (finalOutside literals position outside) :=
  BuilderLiteralClauseTokenSelector.final_tape literals position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) :
    DirectToken.clauseSlot literals position =
      if position = 0 then some .sep
      else if position - 1 < DirectToken.boundedLiteralListWidth literals then
        DirectToken.boundedLiteralListSlot literals (position - 1)
      else if position - 1 - DirectToken.boundedLiteralListWidth literals = 0 then some .finish else none :=
  BuilderLiteralClauseTokenSelector.clause_cases literals position

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration literals position older inside outside) =
      (encodeClauseTokens (BoundedClause.emit literals))[position]? :=
  BuilderLiteralClauseTokenSelector.canonical_result literals position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps literals position) (initialConfiguration literals position older inside outside)) =
      (encodeClauseTokens (BoundedClause.emit literals))[position]? :=
  BuilderLiteralClauseTokenSelector.workRun_observes_encoding literals position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (outside : List WorkSymbol) (hPositive : 0 < position) :
    (registerWord (BuilderLiteralListSearch.initialValues literals (position - 1) older)).length +
        (bodyOutside outside).length =
      (registerWord (initialValues literals position older)).length + outside.length :=
  BuilderLiteralClauseTokenSelector.body_input_span literals position older outside hPositive

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) :
    afterSteps literals position ≤ 5 :=
  BuilderLiteralClauseTokenSelector.after_steps_le literals position

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues literals position older)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues literals position older)).length +
        (finalOutside literals position outside).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps literals position ≤ (rawTimePolynomial bound).eval input :=
  BuilderLiteralClauseTokenSelector.source_polynomial_bounds literals position older outside bound input hSpan

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues literals position older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (initialConfiguration literals position older inside outside)) =
        encodeWorkConfiguration (finalConfiguration literals position older inside outside) ∧
      observe (finalConfiguration literals position older inside outside) =
        (encodeClauseTokens (BoundedClause.emit literals))[position]? ∧
      (registerWord (finalValues literals position older)).length +
        (finalOutside literals position outside).length ≤ (spanPolynomial bound).eval input :=
  BuilderLiteralClauseTokenSelector.uniform_polynomial_lookup literals position older inside outside bound input hSpan

/- Independent grammar, physical frame and terminal-boundary expectations. -/
private def positiveZero : BoundedLiteral 4 := {positive := true, index := ⟨0, by decide⟩}
private def negativeZero : BoundedLiteral 4 := {positive := false, index := ⟨0, by decide⟩}
private def positiveTwo : BoundedLiteral 4 := {positive := true, index := ⟨2, by decide⟩}
private def negativeTwo : BoundedLiteral 4 := {positive := false, index := ⟨2, by decide⟩}
private def mixed : List (BoundedLiteral 4) := [positiveZero, negativeTwo]

example : encodeClauseTokens (BoundedClause.emit ([] : List (BoundedLiteral 0))) = [.sep, .finish] := by decide
example : encodeClauseTokens (BoundedClause.emit [positiveZero]) = [.sep, .t, .f, .finish] := by decide
example : encodeClauseTokens (BoundedClause.emit [negativeZero]) = [.sep, .f, .f, .finish] := by decide
example : encodeClauseTokens (BoundedClause.emit [positiveTwo]) = [.sep, .t, .t, .t, .f, .finish] := by decide
example : encodeClauseTokens (BoundedClause.emit mixed) = [.sep, .t, .f, .f, .t, .t, .f, .finish] := by decide
example : DirectToken.boundedLiteralListWidth mixed = 6 := by decide
example : initialValues mixed 7 [9] = [9,2,0,0,1,0,2,7] := by decide
example : initialValues mixed 0 [] = [2,0,0,1,0,2,0] := by decide
example : workSteps mixed 0 = 4 := rfl
example : workSteps ([] : List (BoundedLiteral 0)) 0 = 4 := rfl
example : machine.acceptState = trueState := rfl
example : machine.rejectState = 1 := rfl
example : searchMachine.acceptState = 2 := rfl
example : searchMachine.rejectState = 1 := rfl
example : searchMachine.rules = BuilderLiteralListSearch.machine.rules := rfl
example : machine.rules = (WorkMachineProgramGraph.machine graph).rules := rfl
example : (trueState, separatorState, finishState) = (6,18,34) := rfl
example : bodyOutside [.blank, .blank] = [.blank, .blank, .blank] := rfl

example : (List.range 10).map (fun position => observe (finalConfiguration mixed position [] [] [])) =
    [some .sep, some .t, some .f, some .f, some .t, some .t, some .f, some .finish, none, none] := by decide
example : (List.range 4).map (fun position =>
    observe (finalConfiguration ([] : List (BoundedLiteral 0)) position [] [] [])) =
    [some .sep, some .finish, none, none] := by decide
example : observe (finalConfiguration [negativeZero] 1 [] [] []) = some .f := by decide
example : observe (finalConfiguration [negativeZero] 2 [] [] []) = some .f := by decide
example : observe (finalConfiguration [negativeZero] 3 [] [] []) = some .finish := by decide
example : observe (finalConfiguration [negativeZero] 4 [] [] []) = none := by decide
example : afterSteps mixed 0 = 0 := by decide
example : afterSteps mixed 1 = 1 := by decide
example : afterSteps mixed 6 = 5 := by decide
example : afterSteps mixed 99 = 5 := by decide

example (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine 4
      (initialConfiguration ([] : List (BoundedLiteral 0)) 0 older inside outside) =
      some (finalConfiguration ([] : List (BoundedLiteral 0)) 0 older inside outside) :=
  BuilderLiteralClauseTokenSelector.workRunExact [] 0 older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps literals position) (initialConfiguration literals position older inside outside) =
      some (finalConfiguration literals position older inside outside) ∧
    observe (finalConfiguration literals position older inside outside) =
      (encodeClauseTokens (BoundedClause.emit literals))[position]? :=
  ⟨BuilderLiteralClauseTokenSelector.workRunExact literals position older inside outside,
   BuilderLiteralClauseTokenSelector.canonical_result literals position older inside outside⟩

example (position : Nat) :
    BuilderLiteralListSearch.endpoint ([] : List (BoundedLiteral 0)) position = .dead := rfl
example (ordinal position : Nat) (payload older prior : List Nat) :
    BuilderLiteralListSearch.finishValues payload older ([] : List (BoundedLiteral 0)) ordinal prior position =
      BuilderLiteralSearchComparison.baseValues payload older prior ++ [ordinal,0,position] := rfl

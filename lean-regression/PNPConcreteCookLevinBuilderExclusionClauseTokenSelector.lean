import PNP.Concrete.CookLevinBuilderExclusionClauseTokenSelector

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderExclusionClauseTokenSelector
open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderExclusionPairLiteralTokens (initialValues)
open BuilderExclusionClauseBoundary (boundary)

example : graph.nodes.length = 8 :=
  BuilderExclusionClauseTokenSelector.graph_nodes_length

example :
    ([0,1,2,separatorState,finishState] : List Nat).Pairwise (fun left right => left ≠ right) :=
  BuilderExclusionClauseTokenSelector.terminal_states_distinct

example : graph.WellFormed :=
  BuilderExclusionClauseTokenSelector.graph_wellFormed

example (position : Nat) : BuilderUnaryTagMatch.workSteps 0 position = 3 :=
  BuilderExclusionClauseTokenSelector.zero_test_steps position

example {width : Nat} (first second : Fin width) :
    DirectToken.boundedLiteralListWidth (excludeBoundedPairClause first second) = first.val + second.val + 4 :=
  BuilderExclusionClauseTokenSelector.body_width first second

example {width : Nat} (first second : Fin width) (position : Nat) :
    DirectToken.clauseSlot (excludeBoundedPairClause first second) position =
      if position = 0 then some .sep
      else if boundary first.val second.val < position then none
      else if position = boundary first.val second.val then some .finish
      else DirectToken.boundedLiteralListSlot (excludeBoundedPairClause first second) (position - 1) :=
  BuilderExclusionClauseTokenSelector.clause_cases first second position

example {width : Nat} (first second : Fin width) (position : Nat)
    (hPositive : 0 < position) (hBody : position < boundary first.val second.val) :
    bodyEndpoint first second position = .accept ∨ bodyEndpoint first second position = .reject :=
  BuilderExclusionClauseTokenSelector.body_endpoint_terminal first second position hPositive hBody

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps first second position retained hRetained)
      (initialConfiguration first.val second.val position retained older inside outside) =
      some (finalConfiguration first second position retained older inside outside) :=
  BuilderExclusionClauseTokenSelector.workRunExact first second position retained older hRetained inside outside

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps first second position retained hRetained)
      (encodeWorkConfiguration (initialConfiguration first.val second.val position retained older inside outside)) =
      encodeWorkConfiguration (finalConfiguration first second position retained older inside outside) :=
  BuilderExclusionClauseTokenSelector.run_compile_exact first second position retained older hRetained inside outside

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration first second position retained older inside outside).tape =
      endTape (finalValues first second position retained older) inside (finalOutside first second position outside) :=
  BuilderExclusionClauseTokenSelector.final_tape first second position retained older inside outside

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration first second position retained older inside outside) =
      (encodeClauseTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? :=
  BuilderExclusionClauseTokenSelector.canonical_result first second position retained older inside outside

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps first second position retained hRetained)
      (initialConfiguration first.val second.val position retained older inside outside)) =
      (encodeClauseTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? :=
  BuilderExclusionClauseTokenSelector.workRun_observes_encoding first second position retained older hRetained inside outside

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderExclusionClauseTokenSelector.rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept machine :=
  BuilderExclusionClauseTokenSelector.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderExclusionClauseTokenSelector.noRuleAtReject

example : WorkMachineProgramGraph.NoRuleAt machine 2 :=
  BuilderExclusionClauseTokenSelector.noRuleAtPadding

example : machine.acceptState ≠ machine.rejectState :=
  BuilderExclusionClauseTokenSelector.acceptState_ne_rejectState

example : WorkMachineProgramGraph.NoRuleAt machine separatorState :=
  BuilderExclusionClauseTokenSelector.noRuleAtSeparator

example : WorkMachineProgramGraph.NoRuleAt machine finishState :=
  BuilderExclusionClauseTokenSelector.noRuleAtFinish

example (first second position : Nat) (retained older : List Nat) (outside : List WorkSymbol)
    (hPositive : 0 < position) :
    (registerWord (initialValues first second (position - 1) retained older)).length +
        (bodyOutside first second position outside).length =
      (registerWord (BuilderExclusionClauseBoundary.finalValues first second position retained older)).length +
        (BuilderExclusionClauseBoundary.finalOutside first second position outside).length :=
  BuilderExclusionClauseTokenSelector.body_input_span first second position retained older outside hPositive

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues first.val second.val position retained older)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (finalValues first second position retained older)).length +
        (finalOutside first second position outside).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps first second position retained hRetained ≤ (rawTimePolynomial bound).eval input :=
  BuilderExclusionClauseTokenSelector.source_polynomial_bounds first second position retained older hRetained outside bound input hSpan

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues first.val second.val position retained older)).length +
      outside.length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (initialConfiguration first.val second.val position retained older inside outside)) =
        encodeWorkConfiguration (finalConfiguration first second position retained older inside outside) ∧
      observe (finalConfiguration first second position retained older inside outside) =
        (encodeClauseTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? ∧
      (registerWord (finalValues first second position retained older)).length +
        (finalOutside first second position outside).length ≤ (spanPolynomial bound).eval input :=
  BuilderExclusionClauseTokenSelector.uniform_polynomial_lookup first second position retained older hRetained inside outside bound input hSpan

example : DirectToken.clauseSlot (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 1) ⟨0, by decide⟩) 0 = some .sep := rfl
example : DirectToken.clauseSlot (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 1) ⟨0, by decide⟩) 1 = some .f := rfl
example : DirectToken.clauseSlot (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 1) ⟨0, by decide⟩) 2 = some .f := rfl
example : DirectToken.clauseSlot (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 1) ⟨0, by decide⟩) 3 = some .f := rfl
example : DirectToken.clauseSlot (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 1) ⟨0, by decide⟩) 4 = some .f := rfl
example : DirectToken.clauseSlot (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 1) ⟨0, by decide⟩) 5 = some .finish := rfl
example : DirectToken.clauseSlot (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 1) ⟨0, by decide⟩) 6 = none := rfl
example : (encodeClauseTokens (BoundedClause.emit (excludeBoundedPairClause
    (⟨2, by decide⟩ : Fin 4) ⟨3, by decide⟩))) =
    [.sep, .f, .t, .t, .f, .f, .t, .t, .t, .f, .finish] := rfl
example : endpoint (⟨2, by decide⟩ : Fin 4) ⟨3, by decide⟩ 0 = .node separatorNode.reference := rfl
example : endpoint (⟨2, by decide⟩ : Fin 4) ⟨3, by decide⟩ 1 = .reject := rfl
example : endpoint (⟨2, by decide⟩ : Fin 4) ⟨3, by decide⟩ 2 = .accept := rfl
example : endpoint (⟨2, by decide⟩ : Fin 4) ⟨3, by decide⟩ 4 = .reject := rfl
example : endpoint (⟨2, by decide⟩ : Fin 4) ⟨3, by decide⟩ 5 = .reject := rfl
example : endpoint (⟨2, by decide⟩ : Fin 4) ⟨3, by decide⟩ 6 = .accept := rfl
example : endpoint (⟨2, by decide⟩ : Fin 4) ⟨3, by decide⟩ 9 = .reject := rfl
example : endpoint (⟨2, by decide⟩ : Fin 4) ⟨3, by decide⟩ 10 = .node finishNode.reference := rfl
example : endpoint (⟨2, by decide⟩ : Fin 4) ⟨3, by decide⟩ 11 = .dead := rfl
example : endpoint (⟨2, by decide⟩ : Fin 4) ⟨3, by decide⟩ 10000 = .dead := rfl
example : endpoint (⟨0, by decide⟩ : Fin 1) ⟨0, by decide⟩ 1 = .reject := rfl
example : endpoint (⟨0, by decide⟩ : Fin 1) ⟨0, by decide⟩ 4 = .reject := rfl
example : endpoint (⟨0, by decide⟩ : Fin 1) ⟨0, by decide⟩ 5 = .node finishNode.reference := rfl
example : endpoint (⟨0, by decide⟩ : Fin 1) ⟨0, by decide⟩ 6 = .dead := rfl
example : endpoint (⟨3, by decide⟩ : Fin 4) ⟨3, by decide⟩ 6 = .reject := rfl
example : endpoint (⟨3, by decide⟩ : Fin 4) ⟨3, by decide⟩ 11 = .node finishNode.reference := rfl
example : separatorState ≠ finishState := by decide
example : separatorState ≠ 0 ∧ separatorState ≠ 1 ∧ separatorState ≠ 2 := by decide
example : finishState ≠ 0 ∧ finishState ≠ 1 ∧ finishState ≠ 2 := by decide

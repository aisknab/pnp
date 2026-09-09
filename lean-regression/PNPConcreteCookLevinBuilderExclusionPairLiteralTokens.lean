import PNP.Concrete.CookLevinBuilderExclusionPairLiteralTokens

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (literalListValues)
open PipelineStateNamespace (renameConfiguration)
open BuilderExclusionPairLiteralTokens

example (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) :
    (frame first second position retained).length = 14 := by
  apply BuilderExclusionPairLiteralTokens.frame_length <;> assumption

example (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) :
    List.ofFn (environment first second position retained hRetained) =
      frame first second position retained := by
  apply BuilderExclusionPairLiteralTokens.environment_values <;> assumption

example (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) :
    environment first second position retained hRetained ⟨0, by decide⟩ = first := by
  apply BuilderExclusionPairLiteralTokens.environment_first <;> assumption

example (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) :
    environment first second position retained hRetained ⟨12, by decide⟩ = second := by
  apply BuilderExclusionPairLiteralTokens.environment_second <;> assumption

example (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) :
    environment first second position retained hRetained ⟨13, by decide⟩ = position := by
  apply BuilderExclusionPairLiteralTokens.environment_position <;> assumption

example : fields.length = 7 := by
  apply BuilderExclusionPairLiteralTokens.fields_length <;> assumption

example (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) :
    BuilderRegisterPack.values fields (environment first second position retained hRetained) =
      [second, 0, first, 0, 0, 2, position] := by
  apply BuilderExclusionPairLiteralTokens.packed_values <;> assumption

example {width : Nat} (first second : Fin width) :
    literalListValues (excludeBoundedPairClause first second) =
      [0, first.val, 0, second.val] := by
  apply BuilderExclusionPairLiteralTokens.literal_payload <;> assumption

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) :
    older ++ List.ofFn (environment first.val second.val position retained hRetained) ++
        BuilderRegisterPack.values fields (environment first.val second.val position retained hRetained) =
      BuilderLiteralListSearch.initialValues (excludeBoundedPairClause first second) position
        (initialValues first.val second.val position retained older) := by
  apply BuilderExclusionPairLiteralTokens.lookup_layout <;> assumption

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    workRunExact? prepareMachine (prepareSteps first.val second.val position retained hRetained)
      (workStartConfiguration prepareMachine
        (endTape (initialValues first.val second.val position retained older) inside outside)) =
      some {state := prepareMachine.acceptState,
            tape := endTape (BuilderLiteralListSearch.initialValues (excludeBoundedPairClause first second) position
              (initialValues first.val second.val position retained older)) inside
              (prepareOutside first.val second.val position outside)} := by
  apply BuilderExclusionPairLiteralTokens.prepare_workRunExact <;> assumption

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps first second position retained hRetained)
      (initialConfiguration first.val second.val position retained older inside outside) =
      some (finalConfiguration first second position retained older inside outside) := by
  apply BuilderExclusionPairLiteralTokens.workRunExact <;> assumption

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps first second position retained hRetained)
      (encodeWorkConfiguration (initialConfiguration first.val second.val position retained older inside outside)) =
      encodeWorkConfiguration (finalConfiguration first second position retained older inside outside) := by
  apply BuilderExclusionPairLiteralTokens.run_compile_exact <;> assumption

example (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderLiteralListSearch.observe configuration := by
  apply BuilderExclusionPairLiteralTokens.observe_renamed <;> assumption

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration first second position retained older inside outside) =
      (encodeLiteralListTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? := by
  apply BuilderExclusionPairLiteralTokens.canonical_result <;> assumption

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps first second position retained hRetained)
      (initialConfiguration first.val second.val position retained older inside outside)) =
      (encodeLiteralListTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? := by
  apply BuilderExclusionPairLiteralTokens.workRun_observes_encoding <;> assumption

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration first second position retained older inside outside).tape =
      endTape (finalValues first second position retained older) inside (finalOutside first second position outside) := by
  apply BuilderExclusionPairLiteralTokens.final_tape <;> assumption

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := by
  apply BuilderExclusionPairLiteralTokens.rules_pairwise_query_distinct <;> assumption

example : WorkMachineChain.NoRuleAtAccept machine := by
  apply BuilderExclusionPairLiteralTokens.noRuleAtAccept <;> assumption

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := by
  apply BuilderExclusionPairLiteralTokens.noRuleAtReject <;> assumption

example : WorkMachineProgramGraph.NoRuleAt machine (WorkMachineChain.secondState 2) := by
  apply BuilderExclusionPairLiteralTokens.noRuleAtPadding <;> assumption

example : machine.acceptState ≠ machine.rejectState := by
  apply BuilderExclusionPairLiteralTokens.acceptState_ne_rejectState <;> assumption

example {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues first.val second.val position retained older)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (finalValues first second position retained older)).length +
        (finalOutside first second position outside).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps first second position retained hRetained ≤ (rawTimePolynomial bound).eval input := by
  apply BuilderExclusionPairLiteralTokens.source_polynomial_bounds <;> assumption

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
        (encodeLiteralListTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? := by
  apply BuilderExclusionPairLiteralTokens.uniform_polynomial_lookup <;> assumption

example (payload older history : List Nat) (row : Fin 9 → Nat)
    (first second position : Nat) :
    initialValues first second position (BuilderExclusionPairSecondVariable.scratch row)
      (BuilderExclusionPairFirstVariable.initialValues payload older history row ++
        BuilderExclusionPairFirstVariable.scratch row) =
      BuilderExclusionPairSecondVariable.finalValues payload older history row first second ++ [position] := by
  apply BuilderExclusionPairLiteralTokens.reader_output_frame <;> assumption

example {width : Nat} (first second : Fin width) (position : Nat)
    (payload older history : List Nat) (row : Fin 9 → Nat) (inside outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (BuilderExclusionPairSecondVariable.finalValues
      payload older history row first.val second.val ++ [position])).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (workStartConfiguration machine
          (endTape (BuilderExclusionPairSecondVariable.finalValues
            payload older history row first.val second.val ++ [position]) inside outside))) =
        encodeWorkConfiguration (finalConfiguration first second position
          (BuilderExclusionPairSecondVariable.scratch row)
          (BuilderExclusionPairFirstVariable.initialValues payload older history row ++
            BuilderExclusionPairFirstVariable.scratch row) inside outside) ∧
      observe (finalConfiguration first second position (BuilderExclusionPairSecondVariable.scratch row)
        (BuilderExclusionPairFirstVariable.initialValues payload older history row ++
          BuilderExclusionPairFirstVariable.scratch row) inside outside) =
        (encodeLiteralListTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? := by
  apply BuilderExclusionPairLiteralTokens.reader_body_lookup <;> assumption

example : frame 7 2 6 [0,1,2,3,4,5,6,7,8,9,10] =
    [7,0,1,2,3,4,5,6,7,8,9,10,2,6] := rfl
example : frame 2 7 6 [0,1,2,3,4,5,6,7,8,9,10] ≠
    frame 7 2 6 [0,1,2,3,4,5,6,7,8,9,10] := by decide
example : environment 7 2 6 (List.replicate 11 99) (by decide) ⟨0, by decide⟩ = 7 := rfl
example : environment 7 2 6 (List.replicate 11 99) (by decide) ⟨11, by decide⟩ = 99 := rfl
example : environment 7 2 6 (List.replicate 11 99) (by decide) ⟨12, by decide⟩ = 2 := rfl
example : environment 7 2 6 (List.replicate 11 99) (by decide) ⟨13, by decide⟩ = 6 := rfl
example : BuilderRegisterPack.values fields (environment 7 2 6 (List.replicate 11 99) (by decide)) =
    [2,0,7,0,0,2,6] := rfl
example : BuilderRegisterPack.values fields (environment 2 2 6 (List.replicate 11 99) (by decide)) =
    [2,0,2,0,0,2,6] := rfl
example : literalListValues (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) =
    [0,0,0,2] := rfl
example : encodeLiteralListTokens (BoundedClause.emit
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩)) =
    [.f,.f,.f,.t,.t,.f] := rfl
example : DirectToken.boundedLiteralListSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 0 = some .f := rfl
example : DirectToken.boundedLiteralListSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 1 = some .f := rfl
example : DirectToken.boundedLiteralListSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 2 = some .f := rfl
example : DirectToken.boundedLiteralListSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 3 = some .t := rfl
example : DirectToken.boundedLiteralListSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 4 = some .t := rfl
example : DirectToken.boundedLiteralListSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 5 = some .f := rfl
example : DirectToken.boundedLiteralListSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 6 = none := rfl
example : DirectToken.boundedLiteralListSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 19 = none := rfl
example : DirectToken.boundedLiteralListSlot
    (excludeBoundedPairClause (⟨2, by decide⟩ : Fin 3) ⟨2, by decide⟩) 4 = some .f := rfl
example : DirectToken.boundedLiteralListSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 1) ⟨0, by decide⟩) 4 = none := rfl
example : DirectToken.clauseSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 0 = some .sep := rfl
example : DirectToken.clauseSlot
    (excludeBoundedPairClause (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩) 7 = some .finish := rfl
example : (List.replicate 10 0).length ≠ 11 := by decide
example : (List.replicate 12 0).length ≠ 11 := by decide

/-
Copyright (c) 2026 PNP Labs.

Universal source-reading contracts and independent sign, order and frame checks.
This regression does not award a complete-builder or unconditional checkpoint.
-/
import PNP.Concrete.CookLevinBuilderPayloadLiteralTokenSelector

open PNP.Concrete PNP.Concrete.CookLevin
open PNP.Concrete.CookLevin.BuilderPayloadLiteralTokenSelector
open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (signValue)

example {ordinal : Nat} (context : Context ordinal) :
    (readerPrefix context).length = 17 * ordinal + 11 := by
  apply BuilderPayloadLiteralTokenSelector.readerPrefix_length <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) :
    initialValues source context older =
      older ++ BuilderLocalConstraintPayload.values source.slot ++ context.gap ++
        [context.clauseIndex, context.originalPosition] ++ context.prior ++
          [source.ordinal, context.remaining, context.position] := by
  apply BuilderPayloadLiteralTokenSelector.initial_values_layout <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal) :
    stride source.kind * source.ordinal + valueSlot source.kind < (reader source context).length := by
  apply BuilderPayloadLiteralTokenSelector.value_field_lt <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal) :
    (reader source context)[stride source.kind * source.ordinal + valueSlot source.kind]'
      (value_field_lt source context) = source.originalLiteral.index.val := by
  apply BuilderPayloadLiteralTokenSelector.value_field <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (hKind : source.kind ≠ .positive) :
    stride source.kind * source.ordinal + signSlot source.kind < (reader source context).length := by
  apply BuilderPayloadLiteralTokenSelector.sign_field_lt <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (hKind : source.kind ≠ .positive) :
    (reader source context)[stride source.kind * source.ordinal + signSlot source.kind]'
      (sign_field_lt source context hKind) = signValue source.originalLiteral.positive := by
  apply BuilderPayloadLiteralTokenSelector.sign_field <;> assumption

example (positive : Bool) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? signFlipMachine 4
      (workStartConfiguration signFlipMachine (endTape (older ++ [signValue positive]) inside outside)) =
      some {state := signFlipMachine.acceptState, tape := endTape (older ++ [signValue (!positive)]) inside (flipOutside positive outside)} := by
  apply BuilderPayloadLiteralTokenSelector.sign_flip_workRunExact <;> assumption

example (kind : Kind) (ordinal value : Nat) : (valueHistory kind ordinal value).length = 6 := by
  apply BuilderPayloadLiteralTokenSelector.valueHistory_length <;> assumption

example (kind : Kind) (ordinal : Nat) : (signPrefix kind ordinal).length = 5 := by
  apply BuilderPayloadLiteralTokenSelector.signPrefix_length <;> assumption

example (kind : Kind) (ordinal remaining position value : Nat) (positive : Bool) :
    (history kind ordinal remaining position value positive).length = 15 := by
  apply BuilderPayloadLiteralTokenSelector.history_length <;> assumption

example (kind : Kind) (ordinal remaining position value : Nat) (positive : Bool) :
    List.ofFn (argumentEnvironment kind ordinal remaining position value positive) =
      history kind ordinal remaining position value positive := by
  apply BuilderPayloadLiteralTokenSelector.environment_values <;> assumption

example (kind : Kind) (ordinal remaining position value : Nat) (positive : Bool) :
    BuilderRegisterPack.values argumentFields (argumentEnvironment kind ordinal remaining position value positive) =
      BuilderLiteralTokenSelector.frame positive value position := by
  apply BuilderPayloadLiteralTokenSelector.packed_values <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (prepareMachine source.kind) (prepareSteps source context)
      (workStartConfiguration (prepareMachine source.kind) (endTape (initialValues source context older) inside outside)) =
      some {state := (prepareMachine source.kind).acceptState, tape := prepareTape source context older inside outside} := by
  apply BuilderPayloadLiteralTokenSelector.prepare_workRunExact <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine source.kind) (workSteps source context)
      (initialConfiguration source context older inside outside) =
      some (finalConfiguration source context older inside outside) := by
  apply BuilderPayloadLiteralTokenSelector.workRunExact <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine source.kind)) (6 * workSteps source context)
      (encodeWorkConfiguration (initialConfiguration source context older inside outside)) =
      encodeWorkConfiguration (finalConfiguration source context older inside outside) := by
  apply BuilderPayloadLiteralTokenSelector.run_compile_exact <;> assumption

example {width : Nat} (source : Source width) :
    source.selectedLiteral.index = source.originalLiteral.index := by
  apply BuilderPayloadLiteralTokenSelector.selected_index <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration source context older inside outside) =
      DirectToken.literalSlot source.selectedLiteral.emit context.position := by
  apply BuilderPayloadLiteralTokenSelector.canonical_result <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun (machine source.kind) (workSteps source context)
      (initialConfiguration source context older inside outside)) =
      DirectToken.literalSlot source.selectedLiteral.emit context.position := by
  apply BuilderPayloadLiteralTokenSelector.workRun_observes_literal <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration source context older inside outside).tape =
      endTape (BuilderLiteralTokenSelector.finalValues source.selectedLiteral.positive source.originalLiteral.index.val
        context.position (prepareOlder source context older)) inside
          (BuilderLiteralTokenSelector.finalOutside source.selectedLiteral.positive source.originalLiteral.index.val
            context.position (prepareOutside source context outside)) := by
  apply BuilderPayloadLiteralTokenSelector.final_tape <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) :
    ∃ scratch, BuilderLiteralTokenSelector.finalValues source.selectedLiteral.positive source.originalLiteral.index.val
      context.position (prepareOlder source context older) = initialValues source context older ++ scratch := by
  apply BuilderPayloadLiteralTokenSelector.original_frame_preserved <;> assumption

example (kind : Kind) : (machine kind).rules.Pairwise WorkMachineChain.QueryDistinct := by
  apply BuilderPayloadLiteralTokenSelector.rules_pairwise_query_distinct <;> assumption

example (kind : Kind) : WorkMachineChain.NoRuleAtAccept (machine kind) := by
  apply BuilderPayloadLiteralTokenSelector.noRuleAtAccept <;> assumption

example (kind : Kind) : WorkMachineProgramGraph.NoRuleAt (machine kind) (machine kind).rejectState := by
  apply BuilderPayloadLiteralTokenSelector.noRuleAtReject <;> assumption

example (kind : Kind) : (machine kind).acceptState ≠ (machine kind).rejectState := by
  apply BuilderPayloadLiteralTokenSelector.acceptState_ne_rejectState <;> assumption

example (kind : Kind) : WorkMachineProgramGraph.NoRuleAt (machine kind) (WorkMachineChain.secondState 2) := by
  apply BuilderPayloadLiteralTokenSelector.noRuleAtPadding <;> assumption

example {width : Nat} (premises : List (BoundedLiteral width))
    (conclusion : BoundedLiteral width) (index : Fin premises.length) :
    (Source.premise premises conclusion index).selectedLiteral =
      (BoundedClause.negated premises ++ [conclusion])[index.val]'(by
        simp only [BoundedClause.negated, List.length_append, List.length_map, List.length_cons, List.length_nil]
        have h := index.isLt
        omega) := by
  apply BuilderPayloadLiteralTokenSelector.premise_canonical_order <;> assumption

example {width : Nat} (premises : List (BoundedLiteral width))
    (conclusion : BoundedLiteral width) :
    (Source.conclusion premises conclusion).selectedLiteral =
      (BoundedClause.negated premises ++ [conclusion])[premises.length]'(by
        simp only [BoundedClause.negated, List.length_append, List.length_map, List.length_cons, List.length_nil]
        omega) := by
  apply BuilderPayloadLiteralTokenSelector.conclusion_canonical_order <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues source context older)).length + outside.length ≤ bound.eval input) :
    (registerWord (prepareOlder source context older ++
      BuilderLiteralTokenSelector.frame source.selectedLiteral.positive source.originalLiteral.index.val context.position)).length +
        (prepareOutside source context outside).length ≤ (prepareSpanPolynomial source.kind bound).eval input ∧
    6 * prepareSteps source context ≤ (prepareRawTimePolynomial source.kind bound).eval input := by
  apply BuilderPayloadLiteralTokenSelector.prepare_source_polynomial_bounds <;> assumption

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues source context older)).length + outside.length ≤ bound.eval input) :
    (registerWord (BuilderLiteralTokenSelector.finalValues source.selectedLiteral.positive source.originalLiteral.index.val
      context.position (prepareOlder source context older))).length +
        (BuilderLiteralTokenSelector.finalOutside source.selectedLiteral.positive source.originalLiteral.index.val
          context.position (prepareOutside source context outside)).length ≤ (spanPolynomial source.kind bound).eval input ∧
    6 * workSteps source context ≤ (rawTimePolynomial source.kind bound).eval input := by
  apply BuilderPayloadLiteralTokenSelector.source_polynomial_bounds <;> assumption

example : (stride .required, valueSlot .required, signSlot .required) = (17,13,12) := rfl
example : (stride .premise, valueSlot .premise, signSlot .premise) = (19,16,15) := rfl
example : (stride .conclusion, valueSlot .conclusion, signSlot .conclusion) = (17,14,13) := rfl
example : (stride .positive, valueSlot .positive) = (18,13) := rfl

example {width : Nat} (literal : BoundedLiteral width) :
    (Source.required literal).selectedLiteral = literal := rfl
example {width : Nat} (premises : List (BoundedLiteral width)) (conclusion : BoundedLiteral width)
    (index : Fin premises.length) :
    (Source.premise premises conclusion index).selectedLiteral.positive = !premises[index.val].positive := rfl
example {width : Nat} (premises : List (BoundedLiteral width)) (conclusion : BoundedLiteral width)
    (index : Fin premises.length) :
    (Source.premise premises conclusion index).selectedLiteral.index = premises[index.val].index := rfl
example {width : Nat} (premises : List (BoundedLiteral width)) (conclusion : BoundedLiteral width) :
    (Source.conclusion premises conclusion).selectedLiteral = conclusion := rfl
example {width : Nat} (variables : List (Fin width)) (index : Fin variables.length) :
    (Source.positive variables index).selectedLiteral.positive = true := rfl
example {width : Nat} (variables : List (Fin width)) (index : Fin variables.length) :
    (Source.positive variables index).selectedLiteral.index = variables[index.val] := rfl
example {width : Nat} (premises : List (BoundedLiteral width)) (conclusion : BoundedLiteral width) :
    (Source.conclusion premises conclusion).ordinal = premises.length := rfl

example {width : Nat} (conclusion : BoundedLiteral width) :
    (Source.conclusion [] conclusion).selectedLiteral = conclusion := rfl
example {width : Nat} (conclusion : BoundedLiteral width) :
    (Source.conclusion [] conclusion).ordinal = 0 := rfl

example :
    (Source.premise [⟨true, ⟨2, by decide⟩⟩, ⟨false, ⟨4, by decide⟩⟩]
      ⟨false, ⟨1, by decide⟩⟩ ⟨0, by decide⟩ : Source 5).selectedLiteral.emit =
      {positive := false, variableIndex := 2} := rfl
example :
    (Source.premise [⟨true, ⟨2, by decide⟩⟩, ⟨false, ⟨4, by decide⟩⟩]
      ⟨false, ⟨1, by decide⟩⟩ ⟨1, by decide⟩ : Source 5).selectedLiteral.emit =
      {positive := true, variableIndex := 4} := rfl
example :
    (Source.conclusion [⟨true, ⟨2, by decide⟩⟩, ⟨false, ⟨4, by decide⟩⟩]
      ⟨false, ⟨1, by decide⟩⟩ : Source 5).selectedLiteral.emit =
      {positive := false, variableIndex := 1} := rfl

example : DirectToken.literalSlot (BoundedLiteral.emit (⟨false, ⟨0, by decide⟩⟩ : BoundedLiteral 1)) 0 = some .f := rfl
example : DirectToken.literalSlot (BoundedLiteral.emit (⟨true, ⟨0, by decide⟩⟩ : BoundedLiteral 1)) 0 = some .t := rfl
example : DirectToken.literalSlot (BoundedLiteral.emit (⟨false, ⟨0, by decide⟩⟩ : BoundedLiteral 1)) 1 = some .f := rfl
example : DirectToken.literalSlot (BoundedLiteral.emit (⟨true, ⟨0, by decide⟩⟩ : BoundedLiteral 1)) 2 = none := rfl
example : DirectToken.literalSlot (BoundedLiteral.emit (⟨false, ⟨3, by decide⟩⟩ : BoundedLiteral 4)) 1 = some .t := rfl
example : DirectToken.literalSlot (BoundedLiteral.emit (⟨false, ⟨3, by decide⟩⟩ : BoundedLiteral 4)) 4 = some .f := rfl
example : DirectToken.literalSlot (BoundedLiteral.emit (⟨false, ⟨3, by decide⟩⟩ : BoundedLiteral 4)) 5 = none := rfl

example : flipOutside false ([] : List WorkSymbol) = [] := rfl
example (outside : List WorkSymbol) : flipOutside true outside = WorkSymbol.blank :: outside := rfl
example (outside : List WorkSymbol) : flipOutside false outside = outside.drop 1 := rfl
example : (signFlipMachine.startState, signFlipMachine.acceptState, signFlipMachine.rejectState) = (0,6,7) := rfl

example :
    initialValues (Source.required (⟨false, ⟨5, by decide⟩⟩ : BoundedLiteral 6))
      {gap := List.replicate 9 0, gap_length := rfl, clauseIndex := 0, originalPosition := 7,
       prior := [], prior_length := rfl, remaining := 1, position := 6} [99] =
      [99,5,0,2] ++ List.replicate 9 0 ++ [0,7,0,1,6] := rfl

example :
    reader (Source.premise [⟨true, ⟨2, by decide⟩⟩, ⟨false, ⟨4, by decide⟩⟩]
      ⟨false, ⟨1, by decide⟩⟩ ⟨1, by decide⟩ : Source 5)
      {gap := List.replicate 9 0, gap_length := rfl, clauseIndex := 0, originalPosition := 10,
       prior := List.replicate 17 8, prior_length := rfl, remaining := 1, position := 0} =
      List.replicate 17 8 ++ [10,0] ++ List.replicate 9 0 ++ [3,2,0,1,1,2,0,4] := rfl

example :
    reader (Source.conclusion [⟨true, ⟨2, by decide⟩⟩, ⟨false, ⟨4, by decide⟩⟩]
      ⟨false, ⟨1, by decide⟩⟩ : Source 5)
      {gap := List.replicate 9 0, gap_length := rfl, clauseIndex := 0, originalPosition := 10,
       prior := List.replicate 34 8, prior_length := rfl, remaining := 0, position := 1} =
      List.replicate 34 8 ++ [10,0] ++ List.replicate 9 0 ++ [3,2,0,1,1,2,0,4] := rfl

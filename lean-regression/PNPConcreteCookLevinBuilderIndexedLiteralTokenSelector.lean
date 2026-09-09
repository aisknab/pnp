import PNP.Concrete.CookLevinBuilderIndexedLiteralTokenSelector

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderIndexedLiteralTokenSelector
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (literalListValues)
open PipelineStateNamespace (renameConfiguration)

-- Structural offsets and values are independently specified.
example : valueHistory 1 4 = [2, 1, 2, 7, 9, 4] := rfl
example : signHistory 1 false = [2, 1, 2, 12, 14, 0] := rfl
example : afterValue 1 8 4 = [8, 2, 1, 2, 7, 9, 4] := rfl
example : history 1 8 true 4 = [1, 8, 2, 1, 2, 7, 9, 4, 2, 1, 2, 12, 14, 1] := rfl
example (ordinal position value : Nat) : (afterValue ordinal position value).length = 7 :=
  afterValue_length ordinal position value
example (ordinal position value : Nat) (positive : Bool) : (history ordinal position positive value).length = 14 :=
  history_length ordinal position positive value
example (ordinal position value : Nat) (positive : Bool) :
    BuilderRegisterPack.values argumentFields (argumentEnvironment ordinal position positive value) =
      [BuilderLocalConstraintPayload.signValue positive, value, position] :=
  packed_values ordinal position positive value
example : initialValues [1, 2, 0, 3] [7] 1 4 = [7, 3, 0, 2, 1, 1, 4] := rfl

-- Check all outcomes independently, including padding versus a false bit.
example (tape : WorkTape) :
    observe {state := WorkMachineChain.secondState 0, tape := tape} = some .t := rfl
example (tape : WorkTape) :
    observe {state := WorkMachineChain.secondState 1, tape := tape} = some .f := rfl
example (tape : WorkTape) :
    observe {state := WorkMachineChain.secondState 2, tape := tape} = none := rfl
example (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderLiteralTokenSelector.observe configuration := observe_renamed configuration

def sample : List (BoundedLiteral 4) := [⟨true, ⟨0, by decide⟩⟩, ⟨false, ⟨2, by decide⟩⟩]
example (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps (literalListValues sample) 0 0 true 0)
      (initialConfiguration (literalListValues sample) [] 0 0 inside outside)) = some .t :=
  workRun_observes_literal sample ⟨0, by decide⟩ 0 [] inside outside
example (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps (literalListValues sample) 1 0 false 2)
      (initialConfiguration (literalListValues sample) [] 1 0 inside outside)) = some .f :=
  workRun_observes_literal sample ⟨1, by decide⟩ 0 [] inside outside
example (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps (literalListValues sample) 1 1 false 2)
      (initialConfiguration (literalListValues sample) [] 1 1 inside outside)) = some .t :=
  workRun_observes_literal sample ⟨1, by decide⟩ 1 [] inside outside
example (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps (literalListValues sample) 1 3 false 2)
      (initialConfiguration (literalListValues sample) [] 1 3 inside outside)) = some .f :=
  workRun_observes_literal sample ⟨1, by decide⟩ 3 [] inside outside
example (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps (literalListValues sample) 1 4 false 2)
      (initialConfiguration (literalListValues sample) [] 1 4 inside outside)) = none :=
  workRun_observes_literal sample ⟨1, by decide⟩ 4 [] inside outside
example (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps (literalListValues sample) 0 1 true 0)
      (initialConfiguration (literalListValues sample) [] 0 1 inside outside)) = some .f :=
  workRun_observes_literal sample ⟨0, by decide⟩ 1 [] inside outside
example (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps (literalListValues sample) 0 2 true 0)
      (initialConfiguration (literalListValues sample) [] 0 2 inside outside)) = none :=
  workRun_observes_literal sample ⟨0, by decide⟩ 2 [] inside outside

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : WorkMachineProgramGraph.NoRuleAt machine (WorkMachineChain.secondState 2) := noRuleAtPadding
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? prepareMachine
      (prepareSteps (literalListValues literals) index.val position literals[index.val].positive literals[index.val].index.val)
      (workStartConfiguration prepareMachine (endTape (initialValues (literalListValues literals) older index.val position) inside outside)) =
      some {state := prepareMachine.acceptState,
            tape := prepareTape (literalListValues literals) older index.val position
              literals[index.val].positive literals[index.val].index.val inside outside} :=
  prepare_workRunExact literals index position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine
      (workSteps (literalListValues literals) index.val position literals[index.val].positive literals[index.val].index.val)
      (initialConfiguration (literalListValues literals) older index.val position inside outside) =
      some (finalConfiguration (literalListValues literals) older index.val position
        literals[index.val].positive literals[index.val].index.val inside outside) :=
  workRunExact literals index position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine)
      (6 * workSteps (literalListValues literals) index.val position literals[index.val].positive literals[index.val].index.val)
      (encodeWorkConfiguration (initialConfiguration (literalListValues literals) older index.val position inside outside)) =
      encodeWorkConfiguration (finalConfiguration (literalListValues literals) older index.val position
        literals[index.val].positive literals[index.val].index.val inside outside) :=
  run_compile_exact literals index position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun machine
      (workSteps (literalListValues literals) index.val position literals[index.val].positive literals[index.val].index.val)
      (initialConfiguration (literalListValues literals) older index.val position inside outside)) =
      DirectToken.literalSlot literals[index.val].emit position :=
  workRun_observes_literal literals index position older inside outside

example (payload older : List Nat) (ordinal position : Nat) (positive : Bool) (value : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration payload older ordinal position positive value inside outside).tape =
      endTape (BuilderLiteralTokenSelector.finalValues positive value position (prepareOlder payload older ordinal position positive value))
        inside (BuilderLiteralTokenSelector.finalOutside positive value position (prepareOutside ordinal position positive value outside)) :=
  final_tape payload older ordinal position positive value inside outside

example (payload older : List Nat) (ordinal position : Nat) (positive : Bool) (value : Nat) :
    ∃ scratch, BuilderLiteralTokenSelector.finalValues positive value position (prepareOlder payload older ordinal position positive value) =
      initialValues payload older ordinal position ++ scratch :=
  original_frame_preserved payload older ordinal position positive value

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues (literalListValues literals) older index.val position)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (prepareOlder (literalListValues literals) older index.val position literals[index.val].positive literals[index.val].index.val ++
      BuilderLiteralTokenSelector.frame literals[index.val].positive literals[index.val].index.val position)).length +
      (prepareOutside index.val position literals[index.val].positive literals[index.val].index.val outside).length ≤
      (prepareSpanPolynomial bound).eval input ∧
    6 * prepareSteps (literalListValues literals) index.val position literals[index.val].positive literals[index.val].index.val ≤
      (prepareRawTimePolynomial bound).eval input :=
  prepare_source_polynomial_bounds literals index position older outside bound input hSpan

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues (literalListValues literals) older index.val position)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (BuilderLiteralTokenSelector.finalValues literals[index.val].positive literals[index.val].index.val position
      (prepareOlder (literalListValues literals) older index.val position literals[index.val].positive literals[index.val].index.val))).length +
      (BuilderLiteralTokenSelector.finalOutside literals[index.val].positive literals[index.val].index.val position
        (prepareOutside index.val position literals[index.val].positive literals[index.val].index.val outside)).length ≤
      (spanPolynomial bound).eval input ∧
    6 * workSteps (literalListValues literals) index.val position literals[index.val].positive literals[index.val].index.val ≤
      (rawTimePolynomial bound).eval input :=
  source_polynomial_bounds literals index position older outside bound input hSpan

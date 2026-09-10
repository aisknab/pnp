/-
Copyright (c) 2026 PNP Labs.

Recover the original token position after actual exclusion-variable lookup,
then pack the actual values and that position into the existing selector frame.
The fixed schema and runtime-computed address never use a supplied answer.
Canonical bounds are kept separate from real blank-tail execution bounds.

This prepares the complete negative-clause selector input. The outer tag/index
dispatcher, token selection, recovery and full formula loop remain separate.
-/
import PNP.Concrete.CookLevinBuilderRequestedPairVariables
import PNP.Concrete.CookLevinBuilderExclusionClauseTokenSelector

namespace PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Request requestValues)
open BuilderRequestedPairVariables (lookupValues)
open BuilderRequestedPairVariables.First (rowWidth)
open BuilderRegisterExpression (Expr)

/-- The pair-value readers leave seven and eleven scratch registers plus two values. -/
def after (first second : Nat) (firstWritten secondWritten : List Nat) : List Nat :=
  firstWritten ++ [first] ++ secondWritten ++ [second]
def initialValues {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) : List Nat :=
  lookupValues variables request older ++ after first second firstWritten secondWritten
def pairSuffix {width : Nat} (variables : List (Fin width)) (request : Request) : List Nat :=
  BuilderExclusionPairPreparation.history variables.length (request.clauseIndex - 1) ++
    BuilderInitialRowLoop.finishValues (variables.length - 1) 0 1
      (BuilderExclusionPairSelection.reverseCoordinate variables.length (request.clauseIndex - 1))
def requestPrefix {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat) : List Nat :=
  older ++ BuilderLocalConstraintPayload.values (some (some (.exactlyOne variables))) ++
    request.gap ++ [request.clauseIndex]

def expression : Expr 9 :=
  .binary .add (.binary .mul (.constant 9) (.argument ⟨7, by decide⟩)) (.constant 49)
def address (environment : Fin 9 → Nat) : Nat := 9 * rowWidth environment + 49
def scratchPrefix (environment : Fin 9 → Nat) : List Nat := [9, rowWidth environment, 9 * rowWidth environment, 49]
def scratch (environment : Fin 9 → Nat) : List Nat := scratchPrefix environment ++ [address environment]
def reader {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat) : List Nat :=
  (scratchPrefix environment).reverse ++ (initialValues variables request older first second firstWritten secondWritten).reverse
def positionMachine : WorkMachine :=
  WorkMachineChain.machine (BuilderRegisterExpression.machine expression 20) BuilderRegisterIndexedCopy.machine
def positionSteps {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat) : Nat :=
  BuilderRegisterExpression.workSteps expression environment (after first second firstWritten secondWritten) + 1 +
    BuilderRegisterIndexedCopy.workSteps
      ((reader variables request older first second firstWritten secondWritten environment).take (address environment))
      request.originalPosition
def positionValues {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat) : List Nat :=
  initialValues variables request older first second firstWritten secondWritten ++ scratch environment ++ [request.originalPosition]

theorem after_length (first second : Nat) (firstWritten secondWritten : List Nat)
    (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    (after first second firstWritten secondWritten).length = 20 := by
  simp only [after, List.length_append, List.length_cons, List.length_nil, hFirst, hSecond]
theorem expression_values (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.values expression environment = scratch environment := rfl
theorem scratch_length (environment : Fin 9 → Nat) : (scratch environment).length = 5 := rfl
theorem lookup_suffix {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length) :
    lookupValues variables request older =
      BuilderRequestedPairLookup.initialValues variables request older ++ pairSuffix variables request := by
  simp only [lookupValues, BuilderExclusionPairLookup.resultValues, if_pos hValid,
    BuilderExclusionPairRow.resultValues, pairSuffix, List.append_assoc]
theorem request_prefix {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat) :
    BuilderRequestedPairLookup.initialValues variables request older =
      requestPrefix variables request older ++ [request.originalPosition] := by
  simp only [BuilderRequestedPairLookup.initialValues, requestValues, requestPrefix,
    List.append_assoc, List.cons_append, List.nil_append]

theorem pairSuffix_length {width : Nat} (variables : List (Fin width)) (request : Request) (older history : List Nat)
    (environment : Fin 9 → Nat) (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hLayout : lookupValues variables request older =
      BuilderRequestedPairVariables.First.initialValues (BuilderLocalConstraintPayload.variableValues variables) older history environment) :
    (pairSuffix variables request).length = 25 + 9 * rowWidth environment := by
  have hLength := congrArg List.length hLayout
  rw [lookup_suffix variables request older hValid, BuilderRequestedPairVariables.input_layout] at hLength
  simp only [BuilderRequestedPairVariables.First.initialValues, List.length_append, List.length_reverse,
    List.length_ofFn, List.length_cons, List.length_nil, request.gap_length, hHistory,
    BuilderRequestedPairVariables.First.requestLength] at hLength
  omega

theorem reader_layout {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat) :
    (reader variables request older first second firstWritten secondWritten environment).reverse ++ [address environment] =
      initialValues variables request older first second firstWritten secondWritten ++ scratch environment := by
  simp only [reader, scratch, List.reverse_append, List.reverse_reverse, List.append_assoc]

private def near {width : Nat} (variables : List (Fin width)) (request : Request)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat) : List Nat :=
  (scratchPrefix environment).reverse ++ (after first second firstWritten secondWritten).reverse ++ (pairSuffix variables request).reverse
private theorem reader_request_layout {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length) :
    reader variables request older first second firstWritten secondWritten environment =
      near variables request first second firstWritten secondWritten environment ++
        (request.originalPosition :: (requestPrefix variables request older).reverse) := by
  simp only [reader, initialValues, lookup_suffix variables request older hValid, request_prefix,
    List.reverse_append, List.reverse_cons, List.cons_append, List.nil_append, List.append_assoc, near]
private theorem near_length {width : Nat} (variables : List (Fin width)) (request : Request)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat)
    (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11)
    (hSuffix : (pairSuffix variables request).length = 25 + 9 * rowWidth environment) :
    (near variables request first second firstWritten secondWritten environment).length = address environment := by
  simp only [near, List.length_append, List.length_reverse, scratchPrefix, List.length_cons,
    List.length_nil, after_length first second firstWritten secondWritten hFirst hSecond, hSuffix, address]
  omega

theorem reader_address_lt {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat)
    (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSuffix : (pairSuffix variables request).length = 25 + 9 * rowWidth environment) :
    address environment < (reader variables request older first second firstWritten secondWritten environment).length := by
  rw [reader_request_layout variables request older first second firstWritten secondWritten environment hValid]
  simp only [List.length_append, List.length_cons,
    near_length variables request first second firstWritten secondWritten environment hFirst hSecond hSuffix]
  omega

theorem reader_address_value {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat)
    (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSuffix : (pairSuffix variables request).length = 25 + 9 * rowWidth environment) :
    (reader variables request older first second firstWritten secondWritten environment)[address environment]'
      (reader_address_lt variables request older first second firstWritten secondWritten environment hFirst hSecond hValid hSuffix) =
      request.originalPosition := by
  have hNear := near_length variables request first second firstWritten secondWritten environment hFirst hSecond hSuffix
  simp only [reader_request_layout variables request older first second firstWritten secondWritten environment hValid]
  rw [List.getElem_append_right (by omega)]
  simp only [hNear, Nat.sub_self, List.getElem_cons_zero]

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem position_workRunExact {width : Nat} (variables : List (Fin width)) (request : Request) (older history : List Nat)
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
  have hSuffix := pairSuffix_length variables request older history environment hValid hHistory hLayout
  have hExpression := BuilderRegisterExpression.workRunExact expression 20
    (older ++ (BuilderLocalConstraintPayload.variableValues variables).reverse ++ history) environment
    (after first second firstWritten secondWritten) inside [] (after_length first second firstWritten secondWritten hFirst hSecond)
  have hFirstRun : workRunExact? (BuilderRegisterExpression.machine expression 20)
      (BuilderRegisterExpression.workSteps expression environment (after first second firstWritten secondWritten))
      (workStartConfiguration (BuilderRegisterExpression.machine expression 20)
        (endTape (initialValues variables request older first second firstWritten secondWritten) inside [])) =
      some {
        state := (BuilderRegisterExpression.machine expression 20).acceptState
        tape := endTape (initialValues variables request older first second firstWritten secondWritten ++ scratch environment) inside []
      } := by
    simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
      expression_values, List.drop_nil, initialValues, hLayout, BuilderRequestedPairVariables.First.initialValues,
      List.append_assoc] using hExpression
  have hCopy := BuilderRegisterIndexedCopy.workRun_select_getElem
    (reader variables request older first second firstWritten secondWritten environment) []
    ⟨address environment, reader_address_lt variables request older first second firstWritten secondWritten environment
      hFirst hSecond hValid hSuffix⟩ inside []
  have hEnd : (reader variables request older first second firstWritten secondWritten environment).reverse ++
      [address environment, request.originalPosition] =
      positionValues variables request older first second firstWritten secondWritten environment := by
    rw [show [address environment, request.originalPosition] = [address environment] ++ [request.originalPosition] from rfl,
      ← List.append_assoc, reader_layout]
    rfl
  simp only [List.nil_append, reader_address_value variables request older first second firstWritten secondWritten environment
    hFirst hSecond hValid hSuffix, reader_layout, hEnd, List.drop_nil] at hCopy
  exact chain_run _ _ _ _ _ _ _ hFirstRun hCopy

def middleSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial expression bound
def positionSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterIndexedCopy.spanPolynomial (middleSpanPolynomial bound)
def positionRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRegisterExpression.rawTimePolynomial expression bound) (.constant 6))
    (BuilderRegisterIndexedCopy.rawTimePolynomial (middleSpanPolynomial bound))

theorem position_polynomial_bounds {width : Nat} (variables : List (Fin width)) (request : Request) (older history : List Nat)
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
  have hSuffix := pairSuffix_length variables request older history environment hValid hHistory hLayout
  have hExpression := BuilderRegisterExpression.source_polynomial_bounds expression bound input
    (older ++ (BuilderLocalConstraintPayload.variableValues variables).reverse ++ history) environment
    (after first second firstWritten secondWritten) (by
      simpa only [initialValues, hLayout, BuilderRequestedPairVariables.First.initialValues] using hSpan)
  simp only [expression_values] at hExpression
  have hMiddle : (registerWord ([] ++ (reader variables request older first second firstWritten secondWritten environment).reverse ++
      [address environment])).length + ([] : List WorkSymbol).length ≤ (middleSpanPolynomial bound).eval input := by
    simpa only [List.nil_append, reader_layout, List.length_nil, Nat.add_zero, middleSpanPolynomial,
      initialValues, hLayout, BuilderRequestedPairVariables.First.initialValues, List.append_assoc] using hExpression.1
  have hCopy := BuilderRegisterIndexedCopy.selected_source_polynomial_bounds
    (reader variables request older first second firstWritten secondWritten environment) []
    ⟨address environment, reader_address_lt variables request older first second firstWritten secondWritten environment
      hFirst hSecond hValid hSuffix⟩ [] (middleSpanPolynomial bound) input hMiddle
  have hEnd : (reader variables request older first second firstWritten secondWritten environment).reverse ++
      [address environment, request.originalPosition] =
      positionValues variables request older first second firstWritten secondWritten environment := by
    rw [show [address environment, request.originalPosition] = [address environment] ++ [request.originalPosition] from rfl,
      ← List.append_assoc, reader_layout]
    rfl
  simp only [List.nil_append, reader_address_value variables request older first second firstWritten secondWritten environment
    hFirst hSecond hValid hSuffix, hEnd, List.drop_nil, List.length_nil, Nat.add_zero] at hCopy
  refine ⟨hCopy.1, ?_⟩
  have hExpressionTime := hExpression.2
  have hCopyTime := hCopy.2
  simp only [positionSteps, positionRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  omega


/-- The fixed environment is the pair-reader suffix followed by the position read. -/
def packingSource (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) : List Nat :=
  after first second firstWritten secondWritten ++ scratch environment ++ [position]

theorem packingSource_length (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    (packingSource environment first second position firstWritten secondWritten).length = 26 := by
  simp only [packingSource, List.length_append, after_length first second firstWritten secondWritten hFirst hSecond,
    scratch_length, List.length_cons, List.length_nil]

def packingEnvironment (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11)
    (index : Fin 26) : Nat :=
  (packingSource environment first second position firstWritten secondWritten)[index.val]'(by
    rw [packingSource_length environment first second position firstWritten secondWritten hFirst hSecond]
    exact index.isLt)

theorem packingEnvironment_values (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    List.ofFn (packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond) =
      packingSource environment first second position firstWritten secondWritten := by
  apply List.ext_getElem
  · rw [List.length_ofFn, packingSource_length environment first second position firstWritten secondWritten hFirst hSecond]
  · intro index hLeft hRight
    simp only [List.getElem_ofFn]
    rfl

theorem packingEnvironment_first (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond ⟨7, by decide⟩ = first := by
  simp only [packingEnvironment, packingSource, after, List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  simp only [hFirst]
  rfl

theorem packingEnvironment_second (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond ⟨19, by decide⟩ = second := by
  simp only [packingEnvironment, packingSource, after, List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  simp only [hFirst, List.cons_append, List.nil_append, List.getElem_cons_succ]
  rw [List.getElem_append_right (by omega)]
  simp only [hSecond]
  rfl

theorem packingEnvironment_position (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond ⟨25, by decide⟩ = position := by
  simp only [packingEnvironment, packingSource, after, List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  simp only [hFirst, List.cons_append, List.nil_append, List.getElem_cons_succ]
  rw [List.getElem_append_right (by omega)]
  simp only [hSecond, List.getElem_cons_succ]
  rw [List.getElem_append_right (by rw [scratch_length]; decide)]
  simp only [scratch_length]
  rfl

/-- The selector treats these eleven registers only as retained context. -/
def retained : List Nat := List.replicate 11 0
def fields : List (BuilderRegisterPack.Field 26) :=
  [.argument ⟨7, by decide⟩] ++ List.replicate 11 (.constant 0) ++
    [.argument ⟨19, by decide⟩, .argument ⟨25, by decide⟩]
theorem retained_length : retained.length = 11 := rfl
theorem fields_length : fields.length = 14 := rfl

theorem packed_values (environment : Fin 9 → Nat) (first second position : Nat)
    (firstWritten secondWritten : List Nat) (hFirst : firstWritten.length = 7) (hSecond : secondWritten.length = 11) :
    BuilderRegisterPack.values fields
      (packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond) =
      BuilderExclusionPairLiteralTokens.frame first second position retained := by
  change [packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond ⟨7, by decide⟩,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond ⟨19, by decide⟩,
    packingEnvironment environment first second position firstWritten secondWritten hFirst hSecond ⟨25, by decide⟩] = _
  rw [packingEnvironment_first, packingEnvironment_second, packingEnvironment_position]
  rfl

theorem position_values_layout {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat) :
    positionValues variables request older first second firstWritten secondWritten environment =
      lookupValues variables request older ++
        packingSource environment first second request.originalPosition firstWritten secondWritten := by
  simp only [positionValues, initialValues, packingSource, List.append_assoc]


theorem position_values_preserve_request {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (first second : Nat) (firstWritten secondWritten : List Nat) (environment : Fin 9 → Nat)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length) :
    positionValues variables request older first second firstWritten secondWritten environment =
      BuilderRequestedPairLookup.initialValues variables request older ++
        (pairSuffix variables request ++ after first second firstWritten secondWritten ++
          scratch environment ++ [request.originalPosition]) := by
  simp only [positionValues, initialValues, lookup_suffix variables request older hValid, List.append_assoc]

def packingMachine : WorkMachine := BuilderRegisterPack.machine fields 0
private theorem packing_machine_projection : BuilderRegisterPack.machine fields 0 = packingMachine := rfl
def machine : WorkMachine := WorkMachineChain.machine positionMachine packingMachine
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial fields (positionSpanPolynomial bound)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (positionRawTimePolynomial bound) (.constant 6))
    (BuilderRegisterPack.rawTimePolynomial fields (positionSpanPolynomial bound))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState
private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
    WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
    WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
    WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩
private theorem position_good : Good positionMachine :=
  chain_good _ _
    ⟨BuilderRegisterExpression.rules_pairwise_query_distinct expression 20,
      BuilderRegisterExpression.noRuleAtAccept expression 20, BuilderRegisterExpression.noRuleAtReject expression 20,
      BuilderRegisterExpression.acceptState_ne_rejectState expression 20⟩
    ⟨BuilderRegisterIndexedCopy.rules_pairwise_query_distinct, BuilderRegisterIndexedCopy.noRuleAtAccept,
      BuilderRegisterIndexedCopy.noRuleAtReject, BuilderRegisterIndexedCopy.acceptState_ne_rejectState⟩
private theorem machine_good : Good machine :=
  chain_good _ _ position_good
    ⟨BuilderRegisterPack.rules_pairwise_query_distinct fields 0, BuilderRegisterPack.noRuleAtAccept fields 0,
      BuilderRegisterPack.noRuleAtReject fields 0, BuilderRegisterPack.acceptState_ne_rejectState fields 0⟩

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := machine_good.1
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := machine_good.2.1
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := machine_good.2.2.1
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := machine_good.2.2.2

/-- Geometry is derived from the actual request and complete row lookup. The
original token position is read physically and packed with the two reader values. -/
theorem canonical_source_prepare {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
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
  rcases BuilderRequestedPairVariables.source_layout variables request older hValid with
    ⟨_, _, environment, history, _, _, _, _, hHistory, hLayout⟩
  have hPosition := position_workRunExact variables request older history first second firstWritten secondWritten environment inside
    hFirst hSecond hValid hHistory hLayout
  have hPositionBounds := position_polynomial_bounds variables request older history first second firstWritten secondWritten
    environment bound input hFirst hSecond hValid hHistory hLayout hSpan
  let packing := packingEnvironment environment first second request.originalPosition firstWritten secondWritten hFirst hSecond
  let newOlder := positionValues variables request older first second firstWritten secondWritten environment
  have hPack := BuilderRegisterPack.workRunExact fields 0 (lookupValues variables request older) packing [] inside [] rfl
  have hPacked : workRunExact? packingMachine (BuilderRegisterPack.workSteps fields packing [])
      (workStartConfiguration packingMachine (endTape newOlder inside [])) =
      some {
        state := packingMachine.acceptState
        tape := endTape (BuilderExclusionPairLiteralTokens.initialValues first second request.originalPosition retained newOlder) inside []
      } := by
    simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration, packing_machine_projection, packing,
      packingEnvironment_values, packed_values, List.append_nil, List.drop_nil,
      BuilderExclusionPairLiteralTokens.initialValues, newOlder, position_values_layout] using hPack
  have hPackBounds := BuilderRegisterPack.source_polynomial_bounds fields (positionSpanPolynomial bound) input
    (lookupValues variables request older) packing [] (by
      simpa only [packing, packingEnvironment_values, List.append_nil, position_values_layout] using hPositionBounds.1)
  have hRun := chain_run _ _ _ _ _ _ _ hPosition hPacked
  let steps := positionSteps variables request older first second firstWritten secondWritten environment + 1 +
    BuilderRegisterPack.workSteps fields packing []
  refine ⟨steps, newOlder, ⟨_, position_values_preserve_request variables request older first second firstWritten secondWritten
    environment hValid⟩, hRun, ?_, ?_⟩
  · simpa only [spanPolynomial, packing, packingEnvironment_values, packed_values, List.append_nil,
      BuilderExclusionPairLiteralTokens.initialValues, newOlder, position_values_layout] using hPackBounds.1
  · have hPositionTime := hPositionBounds.2
    have hPackTime := hPackBounds.2
    simp only [steps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderRequestedExclusionInput.Position

namespace PNP.Concrete.CookLevin.BuilderRequestedExclusionInput

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Request)
open BuilderExclusionPairSelection (selectedPair)
open WorkMachineProgramGraph (Node Graph)
open WorkMachineProgramPath (AcceptPath)

def prepareNode : Node := {name := 1, program := Position.machine, onAccept := .accept, onReject := .dead}
private theorem prepare_program : prepareNode.program = Position.machine := rfl
def lookupNode : Node :=
  {name := 0, program := BuilderRequestedPairVariables.machine, onAccept := .node prepareNode.reference, onReject := .reject}
def graph : Graph := {nodes := [lookupNode, prepareNode], entry := lookupNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph
private theorem machine_projection : WorkMachineProgramGraph.machine graph = machine := rfl
private theorem lookup_mem : lookupNode ∈ graph.nodes := List.Mem.head _
private theorem prepare_mem : prepareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)

theorem graph_nodes_length : graph.nodes.length = 2 := rfl
theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact ⟨BuilderRequestedPairVariables.rules_pairwise_query_distinct,
        BuilderRequestedPairVariables.noRuleAtAccept, BuilderRequestedPairVariables.noRuleAtReject,
        BuilderRequestedPairVariables.acceptState_ne_rejectState⟩
    · exact ⟨Position.rules_pairwise_query_distinct, Position.noRuleAtAccept,
        Position.noRuleAtReject, Position.acceptState_ne_rejectState⟩
  · exact ⟨lookupNode, lookup_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact ⟨⟨prepareNode, prepare_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

def canonicalInputSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRequestedPairVariables.Second.pairSpanPolynomial (BuilderRequestedPairVariables.canonicalSpanPolynomial bound)
def canonicalSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  Position.spanPolynomial (canonicalInputSpanPolynomial bound)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRequestedPairVariables.rawTimePolynomial bound) (.constant 12))
    (Position.rawTimePolynomial (canonicalInputSpanPolynomial bound))
def spanPolynomial (bound : NatPolynomial) : NatPolynomial := .add bound (rawTimePolynomial bound)

private theorem configuration_eq_of_state (configuration : WorkConfiguration) (state : Nat)
    (hState : configuration.state = state) : configuration = {state := state, tape := configuration.tape} := by
  cases configuration
  cases hState
  rfl
private theorem start_configuration (tape : WorkTape) :
    WorkMachineProgramGraph.endpointConfiguration (.node lookupNode.reference) tape =
      workStartConfiguration machine tape := rfl
private theorem accept_configuration (tape : WorkTape) :
    WorkMachineProgramGraph.endpointConfiguration .accept tape = {state := machine.acceptState, tape := tape} := rfl
private theorem reject_configuration (tape : WorkTape) :
    WorkMachineProgramGraph.endpointConfiguration .reject tape = {state := machine.rejectState, tape := tape} := rfl

/-- The selector's two values and position all come from the original request.
The canonical register span and actual finite tape window are bounded separately. -/
theorem workRun_source_prepare {width : Nat} (variables : List (Fin width)) (request : Request)
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
  obtain ⟨first, second, firstWritten, secondWritten, lookupSteps, middle, hPair, hFirst, hSecond,
      hLookup, hMiddleEquivalent, hCanonicalSpan, _, hLookupTime⟩ :=
    BuilderRequestedPairVariables.workRun_source_lookup_with_canonical_span variables request older inside outside bound input
      hPositive hBlank hValid hSpan
  obtain ⟨prepareSteps, newOlder, hPrefix, hPrepare, hPreparedSpan, hPrepareTime⟩ :=
    Position.canonical_source_prepare variables request older variables[first.val].val variables[second.val].val firstWritten secondWritten
      inside (canonicalInputSpanPolynomial bound) input hFirst hSecond hValid (by
        simpa only [Position.initialValues, Position.after, List.append_assoc, canonicalInputSpanPolynomial] using hCanonicalSpan)
  have hPrepareInitial : WorkConfiguration.BlankEquivalent
      (workStartConfiguration Position.machine middle.tape)
      (workStartConfiguration Position.machine
        (endTape (Position.initialValues variables request older variables[first.val].val variables[second.val].val firstWritten secondWritten)
          inside [])) := by
    refine ⟨rfl, ?_⟩
    simpa only [workStartConfiguration, Position.initialValues, Position.after, List.append_assoc] using hMiddleEquivalent.tape
  obtain ⟨prepareFinal, hPrepareActual, hPrepareEquivalent⟩ :=
    workRunExact?_transport Position.machine prepareSteps hPrepareInitial hPrepare
  have hLookupEnd : middle = {state := BuilderRequestedPairVariables.machine.acceptState, tape := middle.tape} :=
    configuration_eq_of_state middle BuilderRequestedPairVariables.machine.acceptState hMiddleEquivalent.state
  have hPrepareState := hPrepareEquivalent.state
  have hPrepareEnd := configuration_eq_of_state prepareFinal _ hPrepareState
  rw [hLookupEnd] at hLookup
  rw [hPrepareEnd] at hPrepareActual
  have hPrepareLocal : WorkMachineProgramPath.LocalAcceptRun prepareNode prepareSteps middle.tape prepareFinal.tape := by
    simp only [WorkMachineProgramPath.LocalAcceptRun, prepare_program]
    simpa only [workStartConfiguration] using hPrepareActual
  have hPreparePath := AcceptPath.step prepareNode .accept prepareSteps 0 middle.tape prepareFinal.tape prepareFinal.tape
    prepare_mem hPrepareLocal (.terminal .accept _)
  have hPath := AcceptPath.step lookupNode .accept _ _ _ _ _ lookup_mem hLookup hPreparePath
  have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
  rw [machine_projection, start_configuration, accept_configuration] at hRun
  let steps := lookupSteps + 1 + (prepareSteps + 1)
  have hExecution : workRunExact? machine steps
      (workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)) =
      some {state := machine.acceptState, tape := prepareFinal.tape} := by
    simpa only [Nat.add_zero, steps] using hRun
  have hTime : 6 * steps ≤ (rawTimePolynomial bound).eval input := by
    simp only [steps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega
  refine ⟨first, second, steps, newOlder, _, hPair, hPrefix, hExecution,
    ⟨rfl, hPrepareEquivalent.tape⟩, hPreparedSpan, ?_, hTime⟩
  have hCells := BuilderRequestedPairLookup.workRun_storedCells machine steps _ _ hExecution
  simp only [BuilderRequestedPairLookup.storedCells, workStartConfiguration, endTape,
    List.length_append, List.length_reverse] at hCells ⊢
  simp only [spanPolynomial, NatPolynomial.eval_add]
  omega

theorem uniform_source_prepare {width : Nat} (variables : List (Fin width)) (request : Request)
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
  obtain ⟨first, second, steps, newOlder, final, hPair, hPrefix, hRun, hEquivalent, hCanonicalSpan, hSpace, hTime⟩ :=
    workRun_source_prepare variables request older inside outside bound input hPositive hBlank hValid hSpan
  exact ⟨first, second, 6 * steps, newOlder, final, hPair, hPrefix, hTime,
    run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun, hEquivalent, hCanonicalSpan, hSpace⟩

/-- Invalid pair ordinals leave both position reading and packing unexecuted. -/
theorem workRun_invalid_source_prepare {width : Nat} (variables : List (Fin width)) (request : Request)
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
  obtain ⟨lookupSteps, middle, hLookup, hEquivalent, _, hLookupTime⟩ :=
    BuilderRequestedPairVariables.workRun_invalid_source_lookup variables request older inside outside bound input hPositive hBlank hInvalid hSpan
  have hEnd : middle = {state := BuilderRequestedPairVariables.machine.rejectState, tape := middle.tape} :=
    configuration_eq_of_state middle _ hEquivalent.state
  rw [hEnd] at hLookup
  have hPath := AcceptPath.stepReject lookupNode .reject _ 0 _ _ _ lookup_mem hLookup (.terminal .reject _)
  have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
  rw [machine_projection, start_configuration, reject_configuration] at hRun
  let steps := lookupSteps + 1
  have hExecution : workRunExact? machine steps
      (workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)) =
      some {state := machine.rejectState, tape := middle.tape} := by
    simpa only [Nat.add_zero, steps] using hRun
  have hTime : 6 * steps ≤ (rawTimePolynomial bound).eval input := by
    simp only [steps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega
  refine ⟨steps, _, hExecution, ⟨rfl, hEquivalent.tape⟩, ?_, hTime⟩
  have hCells := BuilderRequestedPairLookup.workRun_storedCells machine steps _ _ hExecution
  simp only [BuilderRequestedPairLookup.storedCells, workStartConfiguration, endTape,
    List.length_append, List.length_reverse] at hCells ⊢
  simp only [spanPolynomial, NatPolynomial.eval_add]
  omega

theorem uniform_invalid_source_prepare {width : Nat} (variables : List (Fin width)) (request : Request)
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
  obtain ⟨steps, final, hRun, hEquivalent, hSpace, hTime⟩ :=
    workRun_invalid_source_prepare variables request older inside outside bound input hPositive hBlank hInvalid hSpan
  exact ⟨6 * steps, final, hTime, run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun, hEquivalent, hSpace⟩

end PNP.Concrete.CookLevin.BuilderRequestedExclusionInput

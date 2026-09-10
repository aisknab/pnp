/-
Copyright (c) 2026 PNP Labs.

Read the exclusion count and ordinal from the actual source/request frame.
The fixed machine copies the payload count and clause index, decrements the
positive clause index, and runs the complete pair-index lookup. Blank-tail
transport preserves the real materialized exterior; it does not erase data.

This is the negative-clause entry, not the outer tag/index dispatcher. Its
caller must derive the positive-index and blank-exterior invariants. Reading
the two selected variable fields through the retained request, selecting their
token, cleanup and the complete formula loop remain downstream.
-/
import PNP.Concrete.CookLevinBuilderPayloadBodyPreparation
import PNP.Concrete.CookLevinBuilderExclusionPairLookup
import PNP.Concrete.WorkMachineBlankEquivalence

namespace PNP.Concrete.CookLevin.BuilderRequestedPairLookup

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Request requestValues)
open BuilderLocalConstraintPayload (variableValues)
open PipelineStateNamespace (renameConfiguration)

def preparationMachine : WorkMachine :=
  WorkMachineChain.machine (RegisterCopy.machine 12)
    (WorkMachineChain.machine (RegisterCopy.machine 2) BuilderRegisterCountdownControl.decrement)
def machine : WorkMachine :=
  WorkMachineChain.machine preparationMachine BuilderExclusionPairLookup.machine
def initialValues {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat) : List Nat :=
  requestValues (.exactlyOne variables) request older
def countSuffix (request : Request) : List Nat :=
  [4] ++ request.gap ++ [request.clauseIndex, request.originalPosition]
def preparationSteps {width : Nat} (variables : List (Fin width)) (request : Request) : Nat :=
  RegisterCopy.steps (countSuffix request) variables.length + 1 +
    (RegisterCopy.steps [request.originalPosition, variables.length] request.clauseIndex + 1 + 2)
def preparedValues {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat) : List Nat :=
  initialValues variables request older ++ [variables.length, request.clauseIndex - 1]
def preparedOutside {width : Nat} (variables : List (Fin width)) (request : Request)
    (outside : List WorkSymbol) : List WorkSymbol :=
  WorkSymbol.blank :: (outside.drop (variables.length + 1)).drop (request.clauseIndex + 1)
def initialConfiguration {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues variables request older) inside outside)
def canonicalFinal {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderExclusionPairLookup.finalConfiguration variables.length (request.clauseIndex - 1)
      (initialValues variables request older) inside)
def workSteps {width : Nat} (variables : List (Fin width)) (request : Request) : Nat :=
  preparationSteps variables request + 1 +
    BuilderExclusionPairLookup.workSteps variables.length (request.clauseIndex - 1)

/-- A finite representation invariant, not a supplied pair or execution. -/
def BlankExterior (outside : List WorkSymbol) : Prop :=
  ∀ index, WorkTape.blankCellAt outside index = WorkSymbol.blank
/-- Stored cells excluding the focused head cell. -/
def storedCells (tape : WorkTape) : Nat := tape.left.length + tape.right.length

theorem countSuffix_length (request : Request) : (countSuffix request).length = 12 := by
  simp only [countSuffix, List.length_append, List.length_cons, List.length_nil, request.gap_length]

theorem count_layout {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat) :
    initialValues variables request older =
      (older ++ (variableValues variables).reverse) ++ [variables.length] ++ countSuffix request := by
  simp only [initialValues, requestValues, BuilderLocalConstraintPayload.values,
    BuilderLocalConstraintPayload.front, List.reverse_cons, List.append_assoc,
    List.cons_append, List.nil_append, countSuffix]

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem preparation_workRunExact {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (hPositive : 0 < request.clauseIndex) :
    workRunExact? preparationMachine (preparationSteps variables request)
      (workStartConfiguration preparationMachine (endTape (initialValues variables request older) inside outside)) =
      some {
        state := preparationMachine.acceptState
        tape := endTape (preparedValues variables request older) inside (preparedOutside variables request outside)
      } := by
  have hCount := BuilderRegionComparisonOperands.copy_workRunExact 12
    (older ++ (variableValues variables).reverse) (countSuffix request) variables.length
    inside outside (countSuffix_length request)
  rw [← count_layout variables request older] at hCount
  have hClause := BuilderRegionComparisonOperands.copy_workRunExact 2
    (older ++ BuilderLocalConstraintPayload.values (some (some (.exactlyOne variables))) ++ request.gap)
    [request.originalPosition, variables.length] request.clauseIndex
    inside (outside.drop (variables.length + 1)) rfl
  have hClauseRun : workRunExact? (RegisterCopy.machine 2)
      (RegisterCopy.steps [request.originalPosition, variables.length] request.clauseIndex)
      (workStartConfiguration (RegisterCopy.machine 2)
        (endTape (initialValues variables request older ++ [variables.length]) inside
          (outside.drop (variables.length + 1)))) =
      some {
        state := (RegisterCopy.machine 2).acceptState
        tape := endTape (initialValues variables request older ++ [variables.length, request.clauseIndex])
          inside ((outside.drop (variables.length + 1)).drop (request.clauseIndex + 1))
      } := by
    simpa only [initialValues, requestValues, List.append_assoc, List.cons_append, List.nil_append] using hClause
  have hSuccessor : request.clauseIndex - 1 + 1 = request.clauseIndex := by omega
  have hDecrement := BuilderRegisterLessThan.decrement_workRunExact (request.clauseIndex - 1)
    (initialValues variables request older ++ [variables.length]) inside
    ((outside.drop (variables.length + 1)).drop (request.clauseIndex + 1))
  rw [hSuccessor] at hDecrement
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hDecrement
  exact chain_run _ _ _ _ _ _ _ hCount (chain_run _ _ _ _ _ _ _ hClauseRun hDecrement)

theorem preparation_polynomial_bounds {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    (registerWord (preparedValues variables request older)).length + (preparedOutside variables request outside).length ≤
        (BuilderPayloadBodyPreparation.spanPolynomial bound).eval input ∧
      6 * preparationSteps variables request ≤ (BuilderPayloadBodyPreparation.rawTimePolynomial bound).eval input := by
  have hScalars := BuilderPayloadBodyPreparation.initial_scalar_bounds (.exactlyOne variables) request older
    (bound.eval input) (by exact Nat.le_trans (Nat.le_add_right _ _) hSpan)
  rw [BuilderPayloadSearchSource.body_positive_length] at hScalars
  have hCountSuffix : (countSuffix request).length + (countSuffix request).sum ≤ 2 * bound.eval input + 20 := by
    simp only [countSuffix, List.length_append, List.sum_append, List.length_cons, List.length_nil,
      List.sum_cons, List.sum_nil]
    omega
  have hClauseSuffix : ([request.originalPosition, variables.length] : List Nat).length +
      [request.originalPosition, variables.length].sum ≤ 2 * bound.eval input + 20 := by
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  have hCount := RegisterCopy.steps_le (countSuffix request) variables.length (2 * bound.eval input + 20)
    (by omega) hCountSuffix
  have hClause := RegisterCopy.steps_le [request.originalPosition, variables.length] request.clauseIndex
    (2 * bound.eval input + 20) (by omega) hClauseSuffix
  constructor
  · simp only [preparedValues, registerWord_append, List.length_append, registerWord_length,
      List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, preparedOutside, List.length_drop,
      BuilderPayloadBodyPreparation.spanPolynomial_eval, BuilderPayloadBodyPreparation.spanBound]
    rw [registerWord_length] at hSpan
    omega
  · rw [BuilderPayloadBodyPreparation.rawTimePolynomial_eval]
    have hSteps : preparationSteps variables request ≤ BuilderPayloadBodyPreparation.workBound (bound.eval input) := by
      simp only [preparationSteps, BuilderPayloadBodyPreparation.workBound, BuilderPayloadBodyPreparation.copyBound]
      omega
    exact Nat.mul_le_mul_left 6 hSteps

theorem blankExterior_replicate (count : Nat) : BlankExterior (List.replicate count WorkSymbol.blank) :=
  WorkTape.blankCellAt_replicate_blank count

private theorem blankCellAt_drop (outside : List WorkSymbol) (count index : Nat) :
    WorkTape.blankCellAt (outside.drop count) index = WorkTape.blankCellAt outside (count + index) := by
  induction count generalizing outside with
  | zero => simp only [List.drop_zero, Nat.zero_add]
  | succ count ih =>
      cases outside with
      | nil => rfl
      | cons head tail =>
          simpa only [List.drop_succ_cons, WorkTape.blankCellAt_cons_succ, Nat.succ_add] using ih tail

theorem preparedOutside_blank {width : Nat} (variables : List (Fin width)) (request : Request)
    (outside : List WorkSymbol) (hBlank : BlankExterior outside) :
    BlankExterior (preparedOutside variables request outside) := by
  intro index
  cases index with
  | zero => rfl
  | succ index =>
      simp only [preparedOutside, WorkTape.blankCellAt_cons_succ, blankCellAt_drop]
      exact hBlank _

theorem endTape_blankEquivalent (values : List Nat) (inside outside : List WorkSymbol)
    (hBlank : BlankExterior outside) :
    WorkTape.BlankEquivalent (endTape values inside outside) (endTape values inside []) := by
  refine ⟨rfl, ?_, fun _ => rfl⟩
  intro index
  exact hBlank index

private theorem move_storedCells (tape : WorkTape) (direction : HeadMove) :
    storedCells (tape.move direction) ≤ storedCells tape + 1 := by
  cases direction with
  | stay => simp only [WorkTape.move]; omega
  | left =>
      cases hLeft : tape.left with
      | nil => simp only [WorkTape.move, WorkTape.moveLeft, hLeft, storedCells, List.length_nil, List.length_cons]; omega
      | cons head tail =>
          simp only [WorkTape.move, WorkTape.moveLeft, hLeft, storedCells, List.length_cons]
          omega
  | right =>
      cases hRight : tape.right with
      | nil => simp only [WorkTape.move, WorkTape.moveRight, hRight, storedCells, List.length_nil, List.length_cons]; omega
      | cons head tail =>
          simp only [WorkTape.move, WorkTape.moveRight, hRight, storedCells, List.length_cons]
          omega

private theorem step_storedCells (program : WorkMachine) (initial final : WorkConfiguration)
    (hStep : workStep? program initial = some final) :
    storedCells final.tape ≤ storedCells initial.tape + 1 := by
  unfold workStep? at hStep
  split at hStep
  · cases hStep
  · cases hFind : findWorkRule program.rules initial.state initial.tape.head with
    | none => simp only [hFind] at hStep; cases hStep
    | some rule =>
        simp only [hFind, Option.some.injEq] at hStep
        subst final
        exact move_storedCells (initial.tape.write rule.writeSymbol) rule.move

/-- Every real transition allocates at most one stored work cell. This bounds
the transported finite window rather than inferring space from equivalence. -/
theorem workRun_storedCells (program : WorkMachine) (steps : Nat) (initial final : WorkConfiguration)
    (hRun : workRunExact? program steps initial = some final) :
    storedCells final.tape ≤ storedCells initial.tape + steps := by
  induction steps generalizing initial with
  | zero =>
      have hEq : initial = final := Option.some.inj hRun
      subst initial
      omega
  | succ steps ih =>
      cases hStep : workStep? program initial with
      | none =>
          simp only [workRunExact?, hStep] at hRun
          cases hRun
      | some next =>
          have hTail : workRunExact? program steps next = some final := by
            simpa only [workRunExact?, hStep] using hRun
          have hFirst := step_storedCells program initial next hStep
          have hRest := ih next hTail
          omega

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧ WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem copy_good (depth : Nat) : Good (RegisterCopy.machine depth) := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct depth, ?_, ?_,
    RegisterCopy.machine_acceptState_ne_rejectState depth⟩
  · intro rule hRule
    exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState depth rule hRule)
  · intro rule hRule
    have h := RegisterCopy.rule_source_lt_acceptState depth rule hRule
    rw [RegisterCopy.machine_acceptState] at h
    rw [RegisterCopy.machine_rejectState]
    omega
private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
   WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
   WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩
private theorem good : Good machine :=
  chain_good _ _
    (chain_good _ _ (copy_good 12) (chain_good _ _ (copy_good 2) BuilderRegisterCountdownControl.decrement_control))
    ⟨BuilderExclusionPairLookup.rules_pairwise_query_distinct, BuilderExclusionPairLookup.noRuleAtAccept,
      BuilderExclusionPairLookup.noRuleAtReject, BuilderExclusionPairLookup.acceptState_ne_rejectState⟩

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct := good.1
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := good.2.1
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := good.2.2.1
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := good.2.2.2

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderPayloadBodyPreparation.rawTimePolynomial bound) (.constant 6))
    (BuilderExclusionPairLookup.rawTimePolynomial (BuilderPayloadBodyPreparation.spanPolynomial bound))
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add bound (rawTimePolynomial bound)

private theorem machine_projection :
    WorkMachineChain.machine preparationMachine BuilderExclusionPairLookup.machine = machine := rfl
private theorem initial_projection (tape : WorkTape) :
    renameConfiguration WorkMachineChain.firstState (workStartConfiguration preparationMachine tape) =
      workStartConfiguration machine tape := rfl

theorem canonical_accept_iff {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside : List WorkSymbol) :
    (canonicalFinal variables request older inside).state = machine.acceptState ↔
      request.clauseIndex - 1 < LocalConstraint.pairCount variables.length := by
  change WorkMachineChain.secondState
      (BuilderExclusionPairLookup.finalConfiguration variables.length (request.clauseIndex - 1)
        (initialValues variables request older) inside).state =
    WorkMachineChain.secondState BuilderExclusionPairLookup.machine.acceptState ↔ _
  rw [WorkMachineChain.secondState_injective.eq_iff]
  exact BuilderExclusionPairLookup.final_accept_iff _ _ _ _

theorem canonical_reject_iff {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside : List WorkSymbol) :
    (canonicalFinal variables request older inside).state = machine.rejectState ↔
      LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1 := by
  change WorkMachineChain.secondState
      (BuilderExclusionPairLookup.finalConfiguration variables.length (request.clauseIndex - 1)
        (initialValues variables request older) inside).state =
    WorkMachineChain.secondState BuilderExclusionPairLookup.machine.rejectState ↔ _
  rw [WorkMachineChain.secondState_injective.eq_iff]
  exact BuilderExclusionPairLookup.final_reject_iff _ _ _ _

theorem canonical_request_retained {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside : List WorkSymbol) :
    ∃ scratch, (canonicalFinal variables request older inside).tape =
      endTape (requestValues (.exactlyOne variables) request older ++ scratch) inside [] := by
  by_cases hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length
  · refine ⟨BuilderExclusionPairPreparation.history variables.length (request.clauseIndex - 1) ++
      BuilderInitialRowLoop.finishValues (variables.length - 1) 0 1
        (BuilderExclusionPairSelection.reverseCoordinate variables.length (request.clauseIndex - 1)), ?_⟩
    simp only [canonicalFinal, renameConfiguration, BuilderExclusionPairLookup.finalConfiguration,
      WorkMachineProgramGraph.endpointConfiguration, BuilderExclusionPairLookup.resultValues, if_pos hValid,
      BuilderExclusionPairRow.resultValues, initialValues, List.append_assoc]
  · refine ⟨BuilderExclusionPairPreparation.history variables.length (request.clauseIndex - 1), ?_⟩
    simp only [canonicalFinal, renameConfiguration, BuilderExclusionPairLookup.finalConfiguration,
      WorkMachineProgramGraph.endpointConfiguration, BuilderExclusionPairLookup.resultValues, if_neg hValid,
      initialValues]

/-- A real execution from the original frame, including invalid pair ordinals.
Its witness is constructed here; callers supply only input geometry and span. -/
theorem workRun_polynomial_lookup {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BlankExterior outside)
    (hSpan : (registerWord (initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ final,
      workRunExact? machine (workSteps variables request) (initialConfiguration variables request older inside outside) = some final ∧
      WorkConfiguration.BlankEquivalent final (canonicalFinal variables request older inside) ∧
      (final.state = machine.acceptState ↔ request.clauseIndex - 1 < LocalConstraint.pairCount variables.length) ∧
      (final.state = machine.rejectState ↔ LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1) ∧
      storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * workSteps variables request ≤ (rawTimePolynomial bound).eval input := by
  have hPrep := preparation_workRunExact variables request older inside outside hPositive
  have hPrepBounds := preparation_polynomial_bounds variables request older outside bound input hSpan
  have hLookupBounds := BuilderExclusionPairLookup.source_polynomial_bounds variables.length (request.clauseIndex - 1)
    (initialValues variables request older) (BuilderPayloadBodyPreparation.spanPolynomial bound) input (by
      exact Nat.le_trans (Nat.le_add_right _ _) hPrepBounds.1)
  have hEquivalent : WorkConfiguration.BlankEquivalent
      (workStartConfiguration BuilderExclusionPairLookup.machine
        (endTape (preparedValues variables request older) inside (preparedOutside variables request outside)))
      (BuilderExclusionPairLookup.initialConfiguration variables.length (request.clauseIndex - 1)
        (initialValues variables request older) inside) :=
    ⟨rfl, endTape_blankEquivalent _ _ _ (preparedOutside_blank variables request outside hBlank)⟩
  obtain ⟨pairFinal, hPair, hFinalEquivalent⟩ := workRunExact?_transport BuilderExclusionPairLookup.machine
    (BuilderExclusionPairLookup.workSteps variables.length (request.clauseIndex - 1)) hEquivalent
    (BuilderExclusionPairLookup.workRunExact variables.length (request.clauseIndex - 1)
      (initialValues variables request older) inside)
  have hChain := WorkMachineChain.workRunExact preparationMachine BuilderExclusionPairLookup.machine
    (preparationSteps variables request) (BuilderExclusionPairLookup.workSteps variables.length (request.clauseIndex - 1))
    _ _ _ hPrep rfl hPair
  rw [machine_projection] at hChain
  have hRun : workRunExact? machine (workSteps variables request)
      (initialConfiguration variables request older inside outside) =
      some (renameConfiguration WorkMachineChain.secondState pairFinal) := by
    simpa only [initial_projection, initialConfiguration, workSteps] using hChain
  have hRenamed : WorkConfiguration.BlankEquivalent (renameConfiguration WorkMachineChain.secondState pairFinal)
      (canonicalFinal variables request older inside) :=
    ⟨congrArg WorkMachineChain.secondState hFinalEquivalent.state, hFinalEquivalent.tape⟩
  have hTime : 6 * workSteps variables request ≤ (rawTimePolynomial bound).eval input := by
    have hFirst := hPrepBounds.2
    have hSecond := hLookupBounds.2
    simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega
  refine ⟨_, hRun, hRenamed, ?_, ?_, ?_, hTime⟩
  · rw [hRenamed.state]
    exact canonical_accept_iff variables request older inside
  · rw [hRenamed.state]
    exact canonical_reject_iff variables request older inside
  · have hCells := workRun_storedCells machine _ _ _ hRun
    simp only [storedCells, initialConfiguration, workStartConfiguration, endTape,
      List.length_append, List.length_reverse] at hCells
    simp only [storedCells, spanPolynomial, NatPolynomial.eval_add]
    omega

theorem uniform_polynomial_lookup {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BlankExterior outside)
    (hSpan : (registerWord (initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps final,
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps (encodeWorkConfiguration (initialConfiguration variables request older inside outside)) =
        encodeWorkConfiguration final ∧
      WorkConfiguration.BlankEquivalent final (canonicalFinal variables request older inside) ∧
      (final.state = machine.acceptState ↔ request.clauseIndex - 1 < LocalConstraint.pairCount variables.length) ∧
      (final.state = machine.rejectState ↔ LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1) ∧
      storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input := by
  obtain ⟨final, hRun, hEquivalent, hAccept, hReject, hSpace, hTime⟩ :=
    workRun_polynomial_lookup variables request older inside outside bound input hPositive hBlank hSpan
  exact ⟨6 * workSteps variables request, final, hTime,
    run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun, hEquivalent, hAccept, hReject, hSpace⟩

end PNP.Concrete.CookLevin.BuilderRequestedPairLookup

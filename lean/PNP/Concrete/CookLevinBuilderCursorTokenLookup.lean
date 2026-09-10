/-
Copyright (c) 2026 PNP Labs.

Complete body-token lookup from the actual formula-builder cursor. The source
program derives the local payload, clause index and token position; the fixed
dispatcher then executes the exact canonical token lookup. Real cleared and
dropped blank exteriors are proved blank, not replaced by empty lists.

The only cursor premises are the existing body-branch and cursor-balance
invariants. No source payload, request, family, selected pair, blank-exterior
certificate or polynomial bound is supplied. Cleanup/root recovery and the
complete output loop remain downstream obligations.
-/
import PNP.Concrete.CookLevinBuilderSourceTokenRequest
import PNP.Concrete.CookLevinBuilderRequestTokenLookup

namespace PNP.Concrete.CookLevin.BuilderCursorTokenLookup

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape inside count width)
open BuilderClauseDividerOperands (quotient clauseWidth)
open BuilderClauseDividerExecution (clauseIndex constraintIndex)
open BuilderConstraintRegionRegisters (Region)
open BuilderRequestedPairLookup (BlankExterior)
open PipelineStateNamespace (renameConfiguration)

private theorem blank_nil : BlankExterior ([] : List WorkSymbol) := fun _ => rfl

private theorem blank_cons (outside : List WorkSymbol) (hBlank : BlankExterior outside) :
    BlankExterior (WorkSymbol.blank :: outside) := by
  intro index
  cases index with
  | zero => rfl
  | succ index => exact hBlank index

private theorem blank_drop (outside : List WorkSymbol) (amount : Nat) (hBlank : BlankExterior outside) :
    BlankExterior (outside.drop amount) := by
  induction amount generalizing outside with
  | zero => exact hBlank
  | succ amount ih =>
      cases outside with
      | nil => exact blank_nil
      | cons symbol rest =>
          exact ih rest (fun index => hBlank (index + 1))

private theorem blank_append (left right : List WorkSymbol) (hLeft : BlankExterior left) (hRight : BlankExterior right) :
    BlankExterior (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons symbol rest ih =>
      have hSymbol : symbol = WorkSymbol.blank := hLeft 0
      have hRest : BlankExterior rest := fun index => hLeft (index + 1)
      change BlankExterior (symbol :: (rest ++ right))
      rw [hSymbol]
      exact blank_cons _ (ih hRest)

private theorem head_move_blank (width position : Nat) (move : HeadMove)
    (outside : List WorkSymbol) (hBlank : BlankExterior outside) :
    BlankExterior (BuilderRegisterHeadMove.finalOutside width position move outside) := by
  have hCopy : BlankExterior (BuilderRegisterHeadMove.copiedOutside position outside) := blank_drop _ _ hBlank
  have hCompared : BlankExterior (BuilderRegisterHeadMove.comparedOutside width position outside) := by
    rw [BuilderRegisterHeadMove.comparedOutside_eq]
    exact blank_append _ _ (BuilderRequestedPairLookup.blankExterior_replicate _) (blank_drop _ _ hBlank)
  cases move with
  | stay => exact hCopy
  | left =>
      change BlankExterior (if position = 0 then BuilderRegisterHeadMove.copiedOutside position outside
        else WorkSymbol.blank :: BuilderRegisterHeadMove.copiedOutside position outside)
      split
      · exact hCopy
      · exact blank_cons _ hCopy
  | right =>
      change BlankExterior (if position + 1 < width then BuilderRegisterHeadMove.comparedOutside width position outside
        else WorkSymbol.blank :: BuilderRegisterHeadMove.comparedOutside width position outside)
      split
      · exact hCompared
      · exact blank_cons _ hCompared

/-- All five actual providers leave a blank exterior, including nonempty
cleared scratch tails. This is derived from their physical output definitions. -/
theorem family_exterior_blank {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    BlankExterior (BuilderFamilyPayload.exterior problem index remaining region hRegion) := by
  cases region with
  | shape =>
      change BlankExterior (BuilderShapeBranchPayload.exteriorWithOutside problem index remaining 0 []
        (BuilderShapePayload.selectedKind problem index) (BuilderShapePayload.comparisonBlanks problem index))
      unfold BuilderShapeBranchPayload.exteriorWithOutside BuilderRegisterExactlyOnePayload.exteriorFrom
        BuilderRegisterDescendingRange.exteriorFrom
      apply blank_drop
      apply blank_append
      · exact BuilderRequestedPairLookup.blankExterior_replicate _
      · apply blank_drop
        apply blank_drop
        exact BuilderRequestedPairLookup.blankExterior_replicate _
  | initial =>
      change BlankExterior (BuilderInitialPayload.exterior problem index)
      unfold BuilderInitialPayload.exterior
      cases BuilderInitialPayload.selectedRole problem index with
      | state => exact blank_nil
      | head => exact blank_nil
      | length =>
          unfold BuilderInitialPayload.branchExterior BuilderInitialLengthPayload.exterior
          apply blank_drop
          exact BuilderRequestedPairLookup.blankExterior_replicate _
      | pairedCells => exact blank_nil
      | inputCells => exact blank_nil
  | control =>
      change BlankExterior (BuilderControlPayload.finalOutside problem index remaining [] hRegion)
      unfold BuilderControlPayload.finalOutside BuilderControlImplicationPayload.finalOutside
        BuilderControlLiteralSources.finalOutside
      apply blank_drop
      apply blank_drop
      unfold BuilderControlHeadSource.finalOutside
      apply head_move_blank
      unfold BuilderControlHeadSource.packOutside BuilderControlActionSource.finalOutside
      apply blank_drop
      apply blank_drop
      simp only [BuilderControlPayload.restoredOutside,List.drop_nil,List.append_nil]
      exact BuilderRequestedPairLookup.blankExterior_replicate _
  | preservation =>
      change BlankExterior ((BuilderPreservationPayload.comparisonBlanks problem index).drop
        (registerWord (BuilderPreservationPayload.retainedValues problem index ++
          BuilderPreservationPayload.payloadValues problem index remaining)).length)
      apply blank_drop
      exact BuilderRequestedPairLookup.blankExterior_replicate _
  | accepting => exact blank_nil

private theorem phase_exterior_blank {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (outside : List WorkSymbol) (hBlank : BlankExterior outside) (phase : Nat) :
    BlankExterior (BuilderSourceTokenRequest.phaseOutside problem index outside phase) := by
  induction phase with
  | zero => exact hBlank
  | succ phase ih => exact blank_drop _ _ ih

theorem source_exterior_blank {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem) :
    BlankExterior (BuilderSourceTokenRequest.exterior problem index remaining hBody) := by
  unfold BuilderSourceTokenRequest.exterior
  apply phase_exterior_blank
  unfold BuilderSourceClauseCoordinate.exterior
  apply blank_drop
  unfold BuilderSourcePayload.exterior
  apply family_exterior_blank

def request {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    BuilderPayloadSearchSource.Request :=
  {gap := BuilderSourceTokenRequest.gap problem index,
   gap_length := BuilderSourceTokenRequest.gap_length problem index,
   clauseIndex := clauseIndex problem index,
   originalPosition := BuilderSourceTokenRequest.tokenPosition problem index}

theorem request_coordinates {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (request problem index).clauseIndex = (index / width problem) % clauseWidth problem ∧
      (request problem index).originalPosition = index % width problem := ⟨rfl,rfl⟩

theorem source_request_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem) :
    BuilderSourceTokenRequest.finalValues problem index remaining hBody =
      BuilderRequestDispatch.requestValues (problem.formulaConstraintSlotDirect (constraintIndex problem index))
        (request problem index) (BuilderSourcePayload.history problem index remaining hBody) := by
  rw [BuilderSourceTokenRequest.final_request_layout]
  rfl

def canonicalResult {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option CNFToken) :=
  BuilderRequestTokenLookup.canonicalResult (problem.formulaConstraintSlotDirect (constraintIndex problem index)) (request problem index)

theorem canonical_result_eq_emit {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    canonicalResult problem index =
      (problem.formulaConstraintSlotDirect (constraintIndex problem index)).map
        (fun source => source.bind (fun constraint =>
          (constraint.emit[(index / width problem) % clauseWidth problem]?).bind
            (fun clause => (encodeClauseTokens (BoundedClause.emit clause))[index % width problem]?))) := rfl

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderSourceTokenRequest.machine verifier) BuilderRequestDispatch.machine

theorem second_state_code (state : Nat) : WorkMachineChain.secondState state = 3 * state + 1 := by
  induction state with
  | zero => rfl
  | succ state ih =>
      change WorkMachineChain.secondState state + 3 = 3 * (state + 1) + 1
      rw [ih]
      omega

/-- Observe only the token-stage state namespace. -/
def observe (configuration : WorkConfiguration) : Option (Option CNFToken) :=
  if configuration.state % 3 = 1 then
    BuilderRequestTokenLookup.observe {state := configuration.state / 3,tape := configuration.tape}
  else none

theorem token_stage_tag (configuration : WorkConfiguration) :
    (renameConfiguration WorkMachineChain.secondState configuration).state % 3 = 1 := by
  simp only [renameConfiguration,second_state_code]
  omega

theorem observe_rename (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderRequestTokenLookup.observe configuration := by
  have hTag : WorkMachineChain.secondState configuration.state % 3 = 1 := token_stage_tag configuration
  have hPayload : WorkMachineChain.secondState configuration.state / 3 = configuration.state := by
    rw [second_state_code]
    omega
  cases configuration
  simp only [observe,renameConfiguration,hTag,ite_true,hPayload]

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderSourceTokenRequest.rules_pairwise_query_distinct verifier)
    BuilderRequestDispatch.rules_pairwise_query_distinct (BuilderSourceTokenRequest.noRuleAtAccept verifier)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineChain.noRuleAtAccept _ _ BuilderRequestDispatch.noRuleAtAccept

private theorem no_rule_at_second (first second : WorkMachine) (state : Nat)
    (hNo : WorkMachineProgramGraph.NoRuleAt second state) :
    WorkMachineProgramGraph.NoRuleAt (WorkMachineChain.machine first second) (WorkMachineChain.secondState state) :=
  WorkMachineChain.noRuleAtAccept first {second with acceptState := state} hNo

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  no_rule_at_second _ _ _ BuilderRequestDispatch.noRuleAtReject

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ BuilderRequestDispatch.acceptState_ne_rejectState

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (BuilderCursorSource.cursorTape problem index remaining output)

def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRequestTokenLookup.spanPolynomial (BuilderSourceTokenRequest.spanBound verifier)
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderSourceTokenRequest.rawTimeBound verifier) (.constant 6))
    (BuilderRequestTokenLookup.rawTimePolynomial (BuilderSourceTokenRequest.spanBound verifier))

private theorem machine_projection {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.machine (BuilderSourceTokenRequest.machine verifier) BuilderRequestDispatch.machine = machine verifier := rfl
private theorem initial_projection {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    renameConfiguration WorkMachineChain.firstState (BuilderSourceTokenRequest.initialConfiguration problem index remaining output) =
      initialConfiguration problem index remaining output := rfl

/-- The actual cursor produces its source, request, blank invariant and input-size
bounds internally, then executes the complete fixed token program. -/
theorem workRun_polynomial_lookup {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ steps final,
      workRunExact? (machine problem.verifier) steps (initialConfiguration problem index remaining output) = some final ∧
      final.state % 3 = 1 ∧
      WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) final.state ∧
      observe final = canonicalResult problem index ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤
        (inside problem.input output).length + (spanBound problem.verifier).eval problem.input.length ∧
      6 * steps ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hSourceBounds := BuilderSourceTokenRequest.source_polynomial_bounds problem index remaining hBody hBalance
  have hSpan : (registerWord (BuilderRequestDispatch.requestValues
      (problem.formulaConstraintSlotDirect (constraintIndex problem index)) (request problem index)
      (BuilderSourcePayload.history problem index remaining hBody))).length +
      (BuilderSourceTokenRequest.exterior problem index remaining hBody).length ≤
        (BuilderSourceTokenRequest.spanBound problem.verifier).eval problem.input.length := by
    rw [← source_request_layout problem index remaining hBody]
    exact hSourceBounds.1
  obtain ⟨lookupSteps,child,hLookup,hNo,hObserve,hSpace,hTime⟩ :=
    BuilderRequestTokenLookup.workRun_polynomial_lookup
      (problem.formulaConstraintSlotDirect (constraintIndex problem index)) (request problem index)
      (BuilderSourcePayload.history problem index remaining hBody) (inside problem.input output)
      (BuilderSourceTokenRequest.exterior problem index remaining hBody)
      (BuilderSourceTokenRequest.spanBound problem.verifier) problem.input.length
      (source_exterior_blank problem index remaining hBody) hSpan
  have hPrepared : workRunExact? BuilderRequestDispatch.machine lookupSteps
      (workStartConfiguration BuilderRequestDispatch.machine
        (BuilderSourceTokenRequest.finalConfiguration problem index remaining output hBody).tape) = some child := by
    rw [BuilderSourceTokenRequest.final_tape,source_request_layout problem index remaining hBody]
    exact hLookup
  have hSource := BuilderSourceTokenRequest.workRunExact problem index remaining output hBody
  have hChain := WorkMachineChain.workRunExact (BuilderSourceTokenRequest.machine problem.verifier)
    BuilderRequestDispatch.machine (BuilderSourceTokenRequest.workSteps problem index remaining hBody)
    lookupSteps _ _ _ hSource rfl hPrepared
  rw [machine_projection,initial_projection] at hChain
  let steps := BuilderSourceTokenRequest.workSteps problem index remaining hBody + 1 + lookupSteps
  let final := renameConfiguration WorkMachineChain.secondState child
  refine ⟨steps,final,hChain,token_stage_tag child,?_,?_,hSpace,?_⟩
  · exact no_rule_at_second _ _ _ hNo
  · rw [observe_rename]
    exact hObserve
  · have hPrepareTime := hSourceBounds.2
    simp only [steps,rawTimeBound,NatPolynomial.eval_add,NatPolynomial.eval_constant]
    omega

theorem uniform_polynomial_lookup {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ rawSteps final,
      rawSteps ≤ (rawTimeBound problem.verifier).eval problem.input.length ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) = encodeWorkConfiguration final ∧
      final.state % 3 = 1 ∧
      WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) final.state ∧
      observe final = canonicalResult problem index ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤
        (inside problem.input output).length + (spanBound problem.verifier).eval problem.input.length := by
  obtain ⟨steps,final,hRun,hTag,hNo,hObserve,hSpace,hTime⟩ :=
    workRun_polynomial_lookup problem index remaining output hBody hBalance
  exact ⟨6 * steps,final,hTime,run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun,hTag,hNo,hObserve,hSpace⟩

end PNP.Concrete.CookLevin.BuilderCursorTokenLookup

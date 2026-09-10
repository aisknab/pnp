/-
Copyright (c) 2026 PNP Labs.

Execute clause-occupancy division on the actual source-derived operand tape.
Reuse the fixed layout converter and mirrored unary divider. The clause width
is positive by its source definition, and the quotient/remainder become the
constraint and local-clause coordinates. The original workspace is preserved.

The body guard is the actual first quotient comparison. This is not yet a
clause-occupancy selector, emitter, Finish path or complete formula-builder loop.
-/

import PNP.Concrete.CookLevinBuilderClauseDividerOperands

namespace PNP.Concrete.CookLevin.BuilderClauseDividerExecution

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count width)
open BuilderClauseDividerOperands (clauseWidth quotient dividerOlder)
open BuilderDividerSourceExecution (sourceSpan dividerMachine)
open BuilderPhysicalClassifierFinishMirroredDispatch
  (mirrorTape mirrorRule workRunExact?_mirror_of_some mirrorRules_pairwise_query_distinct
    mirrorMachine_acceptState_ne_rejectState)

/-- The same fixed converter and divider; no input-dependent control generation. -/
def divisionMachine : WorkMachine :=
  WorkMachineChain.machine BuilderDividerLayout.machine dividerMachine

def divisionExterior (count : Nat) (older : List Nat) (workspace : List WorkSymbol) : List WorkSymbol :=
  leftMarker :: (List.replicate count unitSymbol ++ scratchEndSymbol ::
    ((registerWord older).reverse ++ workspace))

def divisionInitial (count dividend divisor : Nat) (older : List Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration divisionMachine (endTape (older ++ [count, 0, dividend, divisor]) workspace [])

def divisionFinal (count dividend divisor : Nat) (older : List Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  {
    state := divisionMachine.acceptState
    tape := mirrorTape (BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration
      dividend divisor (divisionExterior count older workspace)).tape
  }

def divisionSteps (count dividend divisor : Nat) : Nat :=
  BuilderDividerLayout.workSteps count dividend divisor + 1 +
    BuilderPostHeaderRawDivider.workSteps dividend divisor

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat)
    (tape : WorkTape) (hState : config.state = state) (hTape : config.tape = tape) :
    config = { state := state, tape := tape } := by
  cases config with
  | mk currentState currentTape =>
    change currentState = state at hState
    change currentTape = tape at hTape
    subst currentState
    subst currentTape
    rfl

private theorem chain_run (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some { state := first.acceptState, tape := middle })
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some { state := second.acceptState, tape := final }) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
        (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some { state := (WorkMachineChain.machine first second).acceptState, tape := final } :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

theorem division_workRunExact (count dividend divisor : Nat) (older : List Nat)
    (workspace : List WorkSymbol) (hPositive : 0 < divisor) :
    workRunExact? divisionMachine (divisionSteps count dividend divisor)
        (divisionInitial count dividend divisor older workspace) =
      some (divisionFinal count dividend divisor older workspace) := by
  have hLayout := BuilderDividerLayout.workRunExact count dividend divisor older workspace []
  have hEnd : BuilderDividerLayout.finalConfiguration count dividend divisor older workspace [] =
      {
        state := BuilderDividerLayout.machine.acceptState
        tape := mirrorTape (BuilderPostHeaderRawTapeBridge.shieldedDividerInputTape dividend divisor
          (divisionExterior count older workspace))
      } :=
    configuration_eq_of_fields _ _ _ rfl
      (BuilderDividerSourceExecution.convertedTape_eq_mirroredDividerInput count dividend divisor
        ((registerWord older).reverse ++ workspace))
  rw [hEnd] at hLayout
  have hDivider := workRunExact?_mirror_of_some BuilderPostHeaderRawTapeBridge.dividerMachine
    (BuilderPostHeaderRawDivider.workSteps dividend divisor)
    (BuilderPostHeaderRawTapeBridge.shieldedDividerStartConfiguration dividend divisor
      (divisionExterior count older workspace))
    (BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration dividend divisor
      (divisionExterior count older workspace))
    (BuilderPostHeaderRawTapeBridge.shielded_divider_workRunExact dividend divisor
      (divisionExterior count older workspace) hPositive)
  exact chain_run BuilderDividerLayout.machine dividerMachine
    (BuilderDividerLayout.workSteps count dividend divisor)
    (BuilderPostHeaderRawDivider.workSteps dividend divisor) _ _ _ hLayout hDivider

theorem division_final_tape_layout (count dividend divisor : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    (divisionFinal count dividend divisor older workspace).tape =
      {
        left := List.replicate (dividend / divisor) BuilderPostHeaderRawDivider.quotientMark
        head := scratchEndSymbol
        right := List.replicate divisor unitSymbol ++ separatorSymbol ::
          (List.replicate (dividend % divisor) unitSymbol ++
            List.replicate ((dividend / divisor) * divisor) BuilderPostHeaderRawDivider.consumedDividend ++
            leftMarker :: leftMarker :: (List.replicate count unitSymbol ++
              scratchEndSymbol :: ((registerWord older).reverse ++ workspace)))
      } := by
  simp only [divisionFinal, mirrorTape, BuilderPhysicalClassifierFinishWorkspaceOrientation.mirrorTape,
    BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration,
    BuilderPostHeaderRawTapeBridge.appendExteriorConfiguration,
    BuilderPostHeaderRawTapeBridge.appendExteriorTape,
    BuilderPostHeaderRawDivider.finalConfiguration, BuilderPostHeaderRawDivider.terminalConfiguration,
    BuilderPostHeaderRawDivider.terminalTape, divisionExterior,
    List.append_assoc, List.cons_append, List.nil_append]
  rfl

private theorem divider_noRule : WorkMachineChain.NoRuleAtAccept dividerMachine := by
  intro selected hMem
  change selected ∈ BuilderPostHeaderRawDivider.machine.rules.map mirrorRule at hMem
  rcases List.mem_map.mp hMem with ⟨original, hOriginal, hEqual⟩
  subst selected
  exact BuilderPostHeaderRawDivider.rule_source_ne_acceptState original hOriginal

theorem division_rules_pairwise_query_distinct :
    divisionMachine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct BuilderDividerLayout.machine dividerMachine
    BuilderDividerLayout.rules_pairwise_query_distinct
    (mirrorRules_pairwise_query_distinct BuilderPostHeaderRawDivider.machine
      BuilderPostHeaderRawDivider.rules_pairwise_query_distinct)
    BuilderDividerLayout.noRuleAtAccept

theorem division_noRuleAtAccept : WorkMachineChain.NoRuleAtAccept divisionMachine :=
  WorkMachineChain.noRuleAtAccept BuilderDividerLayout.machine dividerMachine divider_noRule

theorem division_acceptState_ne_rejectState : divisionMachine.acceptState ≠ divisionMachine.rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _
    (mirrorMachine_acceptState_ne_rejectState BuilderPostHeaderRawDivider.machine
      BuilderPostHeaderRawDivider.machine_acceptState_ne_rejectState)

theorem divisionSteps_le (count dividend divisor bound : Nat)
    (hCount : count ≤ bound) (hDividend : dividend ≤ bound) (hDivisor : divisor ≤ bound)
    (hPositive : 0 < divisor) :
    divisionSteps count dividend divisor ≤ 4 * bound + 8 + 20 * (2 * bound + 1) * (2 * bound + 1) := by
  have hLayout := BuilderDividerLayout.workSteps_le count dividend divisor bound hCount hDividend hDivisor
  have hSize : dividend + divisor + 1 ≤ 2 * bound + 1 := by omega
  have hSquare := Nat.mul_le_mul (Nat.mul_le_mul_left 20 hSize) hSize
  have hDivider := Nat.le_trans
    (BuilderPostHeaderRawDivider.workSteps_le_quadratic dividend divisor hPositive) hSquare
  unfold divisionSteps
  omega

def constraintIndex {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  quotient problem index / clauseWidth problem

def clauseIndex {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  quotient problem index % clauseWidth problem

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (divisionFinal (count problem) (quotient problem index) (clauseWidth problem)
      (dividerOlder problem index remaining) (inside problem.input output))

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderClauseDividerOperands.machine verifier) divisionMachine

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (BuilderSourceRegisterRestore.restorationFinal problem index remaining output).tape

def workSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  BuilderClauseDividerOperands.workSteps problem index remaining + 1 +
    divisionSteps (count problem) (quotient problem index) (clauseWidth problem)

theorem operand_division_handoff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderClauseDividerOperands.finalConfiguration problem index remaining output).tape =
      (divisionInitial (count problem) (quotient problem index) (clauseWidth problem)
        (dividerOlder problem index remaining) (inside problem.input output)).tape :=
  BuilderClauseDividerOperands.final_tape_layout problem index remaining output

private theorem source_division_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? divisionMachine (divisionSteps (count problem) (quotient problem index) (clauseWidth problem))
      (workStartConfiguration divisionMachine
        (BuilderClauseDividerOperands.finalConfiguration problem index remaining output).tape) =
      some (divisionFinal (count problem) (quotient problem index) (clauseWidth problem)
        (dividerOlder problem index remaining) (inside problem.input output)) := by
  have h := division_workRunExact (count problem) (quotient problem index) (clauseWidth problem)
    (dividerOlder problem index remaining) (inside problem.input output)
    (BuilderClauseDividerOperands.clauseWidth_pos problem)
  have hInitial : divisionInitial (count problem) (quotient problem index) (clauseWidth problem)
      (dividerOlder problem index remaining) (inside problem.input output) =
    workStartConfiguration divisionMachine
      (BuilderClauseDividerOperands.finalConfiguration problem index remaining output).tape :=
    congrArg (workStartConfiguration divisionMachine)
      (operand_division_handoff problem index remaining output).symm
  rw [hInitial] at h
  exact h

private theorem initial_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    initialConfiguration problem index remaining output =
      renameConfiguration WorkMachineChain.firstState
        (BuilderClauseDividerOperands.initialConfiguration problem index remaining output) := rfl

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  have h := WorkMachineChain.workRunExact (BuilderClauseDividerOperands.machine problem.verifier)
    divisionMachine (BuilderClauseDividerOperands.workSteps problem index remaining)
    (divisionSteps (count problem) (quotient problem index) (clauseWidth problem))
    (BuilderClauseDividerOperands.initialConfiguration problem index remaining output)
    (BuilderClauseDividerOperands.finalConfiguration problem index remaining output)
    (divisionFinal (count problem) (quotient problem index) (clauseWidth problem)
      (dividerOlder problem index remaining) (inside problem.input output))
    (BuilderClauseDividerOperands.workRunExact problem index remaining output)
    (BuilderClauseDividerOperands.finalConfiguration_state problem index remaining output)
    (source_division_run problem index remaining output)
  simpa only [machine, workSteps, finalConfiguration, initial_eq] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output)

theorem finalConfiguration_state {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState := rfl

theorem final_tape_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      {
        left := List.replicate (constraintIndex problem index) BuilderPostHeaderRawDivider.quotientMark
        head := scratchEndSymbol
        right := List.replicate (clauseWidth problem) unitSymbol ++ separatorSymbol ::
          (List.replicate (clauseIndex problem index) unitSymbol ++
            List.replicate (constraintIndex problem index * clauseWidth problem)
              BuilderPostHeaderRawDivider.consumedDividend ++ leftMarker :: leftMarker ::
                (List.replicate (count problem) unitSymbol ++ scratchEndSymbol ::
                  ((registerWord (dividerOlder problem index remaining)).reverse ++ inside problem.input output)))
      } :=
  division_final_tape_layout (count problem) (quotient problem index) (clauseWidth problem)
    (dividerOlder problem index remaining) (inside problem.input output)

theorem constraint_mark_count {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape.left.length = constraintIndex problem index := by
  rw [final_tape_layout]
  exact List.length_replicate

theorem clauseIndex_lt {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    clauseIndex problem index < problem.formulaClauseSlotsPerConstraint := by
  rw [← BuilderClauseDividerOperands.clauseWidth_value]
  exact BuilderPostHeaderRawDivider.remainder_lt_width (quotient problem index) (clauseWidth problem)
    (BuilderClauseDividerOperands.clauseWidth_pos problem)

theorem coordinate_reconstruction {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    constraintIndex problem index * clauseWidth problem + clauseIndex problem index = quotient problem index :=
  BuilderPostHeaderRawDivider.quotient_remainder_reconstruct (quotient problem index) (clauseWidth problem)

theorem constraintIndex_lt {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hBody : quotient problem index < count problem) :
    constraintIndex problem index < problem.formulaConstraintSlotCount := by
  by_cases hLess : constraintIndex problem index < problem.formulaConstraintSlotCount
  · exact hLess
  · have hLe : problem.formulaConstraintSlotCount ≤ constraintIndex problem index := by omega
    have hProduct := Nat.mul_le_mul_right (clauseWidth problem) hLe
    have hReconstruct := coordinate_reconstruction problem index
    rw [BuilderClauseDividerOperands.clauseCount_product] at hBody
    omega

theorem source_coordinate_reconstruction {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) :
    (constraintIndex problem index * clauseWidth problem + clauseIndex problem index) * width problem +
      index % width problem = index := by
  rw [coordinate_reconstruction]
  exact BuilderDividerSourceExecution.quotient_remainder_reconstruct problem index

def divisionRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let span := sourceSpan verifier
  let larger := NatPolynomial.add (.mul (.constant 2) span) (.constant 1)
  .mul (.constant 6)
    (.add (.add (.mul (.constant 4) span) (.constant 8))
      (.mul (.mul (.constant 20) larger) larger))

theorem divisionRawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * divisionSteps (count problem) (quotient problem index) (clauseWidth problem) ≤
      (divisionRawTimeBound problem.verifier).eval problem.input.length := by
  let span := (sourceSpan problem.verifier).eval problem.input.length
  have hC : count problem ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .clauseCount index remaining hBalance
  have hI : index ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .index index remaining hBalance
  have hQ : quotient problem index ≤ span := Nat.le_trans (Nat.div_le_self index (width problem)) hI
  have hD : clauseWidth problem ≤ span :=
    (BuilderClauseDividerOperands.source_selection_bounds problem index remaining hBalance).1
  have h := Nat.mul_le_mul_left 6 (divisionSteps_le (count problem) (quotient problem index)
    (clauseWidth problem) span hC hQ hD (BuilderClauseDividerOperands.clauseWidth_pos problem))
  simpa only [divisionRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant] using h

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderClauseDividerOperands.rawTimeBound verifier) (.constant 6)) (divisionRawTimeBound verifier)

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hOperands := BuilderClauseDividerOperands.rawTimeBound_le problem index remaining hBalance
  have hDivision := divisionRawTimeBound_le problem index remaining hBalance
  simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  unfold workSteps
  omega

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct (BuilderClauseDividerOperands.machine verifier) divisionMachine
    (BuilderClauseDividerOperands.rules_pairwise_query_distinct verifier)
    division_rules_pairwise_query_distinct (BuilderClauseDividerOperands.noRuleAtAccept verifier)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineChain.noRuleAtAccept (BuilderClauseDividerOperands.machine verifier)
    divisionMachine division_noRuleAtAccept

theorem machine_acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ division_acceptState_ne_rejectState

def bodyMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderClauseDividerOperands.bodyMachine verifier) divisionMachine

def bodyInitial {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (bodyMachine problem.verifier)
    (BuilderCursorSource.cursorTape problem index remaining output)

def bodySteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderClauseDividerOperands.bodySteps problem index remaining + 1 +
    divisionSteps (count problem) (quotient problem index) (clauseWidth problem)

private theorem body_initial_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    bodyInitial problem index remaining output =
      renameConfiguration WorkMachineChain.firstState
        (BuilderClauseDividerOperands.bodyInitial problem index remaining output) := rfl

/-- Copy the operands once, then continue the actual body endpoint through the divider. -/
theorem body_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (bodyMachine problem.verifier) (bodySteps problem index remaining)
        (bodyInitial problem index remaining output) = some (finalConfiguration problem index remaining output) := by
  have h := WorkMachineChain.workRunExact (BuilderClauseDividerOperands.bodyMachine problem.verifier)
    divisionMachine (BuilderClauseDividerOperands.bodySteps problem index remaining)
    (divisionSteps (count problem) (quotient problem index) (clauseWidth problem))
    (BuilderClauseDividerOperands.bodyInitial problem index remaining output)
    (BuilderClauseDividerOperands.bodyFinal problem index remaining output)
    (divisionFinal (count problem) (quotient problem index) (clauseWidth problem)
      (dividerOlder problem index remaining) (inside problem.input output))
    (BuilderClauseDividerOperands.body_workRunExact problem index remaining output hBody)
    (BuilderClauseDividerOperands.body_finalConfiguration_state problem index remaining output)
    (source_division_run problem index remaining output)
  simpa only [bodyMachine, bodySteps, finalConfiguration, body_initial_eq] using h

theorem body_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (bodyMachine problem.verifier)) (6 * bodySteps problem index remaining)
        (encodeWorkConfiguration (bodyInitial problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (body_workRunExact problem index remaining output hBody)

theorem body_finalConfiguration_state {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (bodyMachine problem.verifier).acceptState := rfl

def bodyRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderClauseDividerOperands.bodyRawTimeBound verifier) (.constant 6)) (divisionRawTimeBound verifier)

theorem body_rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * bodySteps problem index remaining ≤ (bodyRawTimeBound problem.verifier).eval problem.input.length := by
  have hOperands := BuilderClauseDividerOperands.body_rawTimeBound_le problem index remaining hBalance
  have hDivision := divisionRawTimeBound_le problem index remaining hBalance
  simp only [bodyRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  unfold bodySteps
  omega

theorem body_rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct (BuilderClauseDividerOperands.bodyMachine verifier)
    divisionMachine (BuilderClauseDividerOperands.body_rules_pairwise_query_distinct verifier)
    division_rules_pairwise_query_distinct (BuilderClauseDividerOperands.body_noRuleAtAccept verifier)

theorem body_noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (bodyMachine verifier) :=
  WorkMachineChain.noRuleAtAccept (BuilderClauseDividerOperands.bodyMachine verifier)
    divisionMachine division_noRuleAtAccept

theorem body_acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).acceptState ≠ (bodyMachine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ division_acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderClauseDividerExecution

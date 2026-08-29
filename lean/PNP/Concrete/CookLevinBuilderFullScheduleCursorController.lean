/-
Copyright (c) 2026 PNP Labs.

Uniform full-schedule control for the concrete Cook--Levin builder.

This module replaces fixed-slot cursor extension as the control architecture:
it computes the complete body opportunity count from the verifier and raw
input, traverses that arbitrary count with one literal finite countdown loop,
and materializes the exact terminal token coordinate.  The semantic token
cursor is run over the same complete schedule and proved exact.

The raw loop intentionally does not yet decode or emit each visited token
opportunity.  It is therefore not the complete dynamic slot decoder, formula
builder, RawRefinement, or PolynomialReduction.
-/

import PNP.Concrete.CookLevinBuilderFirstClausePaddingRun

namespace PNP.Concrete

namespace CookLevin

namespace BuilderFullScheduleCursorController

open PipelineTape PipelineStateNamespace PipelineStageBridges
  BuilderFirstClausePaddingRun

/-! ## Exact polynomial schedule coordinates -/

/-- The first body opportunity, immediately after the padded unary header. -/
def firstBodySlotPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (formulaVariableCountPolynomial verifier) (.constant 1)

/-- Every rectangular clause-token opportunity plus the final `Finish`. -/
def bodySlotCountPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add
    (.mul (formulaClauseCountPolynomial verifier)
      (formulaClauseTokenPolynomial verifier))
    (.constant 1)

/-- The unique coordinate immediately outside the complete token schedule. -/
def terminalSlotPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (firstBodySlotPolynomial verifier)
    (bodySlotCountPolynomial verifier)

def firstBodySlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (firstBodySlotPolynomial problem.verifier).eval problem.input.length

def bodySlotCount {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (bodySlotCountPolynomial problem.verifier).eval problem.input.length

def terminalSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (terminalSlotPolynomial problem.verifier).eval problem.input.length

theorem firstBodySlot_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    firstBodySlot problem = problem.formulaVariableSlotBound + 1 := by
  rfl

set_option maxHeartbeats 1000000 in
theorem bodySlotCount_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    bodySlotCount problem =
      problem.formulaClauseSlotCount * problem.formulaTokensPerClause + 1 := by
  unfold bodySlotCount bodySlotCountPolynomial
  rw [NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant]
  have clauseCount := problem.formulaClauseCountPolynomial_eval
  have clauseTokens := problem.formulaClauseTokenPolynomial_eval
  simp only [BitString.size] at clauseCount clauseTokens
  rw [clauseCount, clauseTokens]
  unfold VerifierTableauProblem.formulaClauseSlotCount
    VerifierTableauProblem.formulaConstraintSlotCount
    VerifierTableauProblem.formulaClauseSlotsPerConstraint
    VerifierTableauProblem.formulaTokensPerClause
    VerifierTableauProblem.formulaVariableSlotBound
  have constraints := problem.formulaConstraintCountPolynomial_eval
  simp only [BitString.size] at constraints ⊢

theorem bodySlotCount_positive {language : Language}
    (problem : VerifierTableauProblem language) :
    0 < bodySlotCount problem := by
  rw [bodySlotCount_eq]
  omega

theorem terminalSlot_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    terminalSlot problem = problem.formulaTokenSlotCountDirect := by
  unfold terminalSlot terminalSlotPolynomial
  rw [NatPolynomial.eval_add]
  change firstBodySlot problem + bodySlotCount problem =
    problem.formulaTokenSlotCountDirect
  rw [firstBodySlot_eq, bodySlotCount_eq]
  unfold VerifierTableauProblem.formulaTokenSlotCountDirect
  omega

theorem firstBodySlot_add_bodySlotCount {language : Language}
    (problem : VerifierTableauProblem language) :
    firstBodySlot problem + bodySlotCount problem = terminalSlot problem := by
  unfold firstBodySlot bodySlotCount terminalSlot terminalSlotPolynomial
  rw [NatPolynomial.eval_add]

/-! ## Complete semantic token-cursor traversal -/

namespace TokenCursor

abbrev Cursor := VerifierTableauProblem.FormulaTokenCursor

/-- Consume at most `fuel` token opportunities, preserving valid padding. -/
def run {language : Language} (problem : VerifierTableauProblem language) :
    Nat -> Cursor -> List (Option CNFToken) × Cursor
  | 0, cursor => ([], cursor)
  | fuel + 1, cursor =>
      match VerifierTableauProblem.FormulaTokenCursor.step problem cursor with
      | none => ([], cursor)
      | some (entry, next) =>
          let tail := run problem fuel next
          (entry :: tail.1, tail.2)

theorem run_of_done {language : Language}
    (problem : VerifierTableauProblem language)
    (cursor : Cursor)
    (done : VerifierTableauProblem.FormulaTokenCursor.done problem cursor)
    (fuel : Nat) :
    run problem fuel cursor = ([], cursor) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp [run,
        VerifierTableauProblem.FormulaTokenCursor.step_of_done
          problem cursor done]

theorem run_prefix {language : Language}
    (problem : VerifierTableauProblem language)
    (start fuel : Nat)
    (bound : start + fuel <= problem.formulaTokenSlotCountDirect) :
    run problem fuel ⟨start⟩ =
      ((problem.formulaTokenSchedule.drop start).take fuel,
        ⟨start + fuel⟩) := by
  induction fuel generalizing start with
  | zero => simp [run]
  | succ fuel inductionHypothesis =>
      have startInRange :
          start < problem.formulaTokenSlotCountDirect := by omega
      have tailInRange :
          start + 1 + fuel <= problem.formulaTokenSlotCountDirect := by omega
      rw [run,
        VerifierTableauProblem.FormulaTokenCursor.step_of_lt
          problem ⟨start⟩ startInRange]
      simp only
      rw [inductionHypothesis (start := start + 1) tailInRange]
      have scheduleInRange : start < problem.formulaTokenSchedule.length := by
        rw [← problem.formulaTokenSlotCountDirect_eq]
        exact startInRange
      rw [List.drop_eq_getElem_cons scheduleInRange]
      simp only [List.take_succ_cons]
      congr 2 <;> omega

theorem run_to_end {language : Language}
    (problem : VerifierTableauProblem language)
    (start fuel : Nat)
    (startBound : start <= problem.formulaTokenSlotCountDirect)
    (fuelBound : problem.formulaTokenSlotCountDirect - start <= fuel) :
    run problem fuel ⟨start⟩ =
      (problem.formulaTokenSchedule.drop start,
        ⟨problem.formulaTokenSlotCountDirect⟩) := by
  induction fuel generalizing start with
  | zero =>
      have equal : start = problem.formulaTokenSlotCountDirect := by omega
      subst start
      rw [run]
      rw [problem.formulaTokenSlotCountDirect_eq]
      simp
  | succ fuel inductionHypothesis =>
      by_cases atEnd : problem.formulaTokenSlotCountDirect <= start
      · have equal : start = problem.formulaTokenSlotCountDirect := by omega
        subst start
        rw [run,
          VerifierTableauProblem.FormulaTokenCursor.step_of_done problem
            ⟨problem.formulaTokenSlotCountDirect⟩ (Nat.le_refl _)]
        rw [problem.formulaTokenSlotCountDirect_eq]
        simp
      · have inRange : start < problem.formulaTokenSlotCountDirect := by omega
        have nextBound : start + 1 <=
            problem.formulaTokenSlotCountDirect := by omega
        have nextFuel : problem.formulaTokenSlotCountDirect - (start + 1) <=
            fuel := by omega
        rw [run,
          VerifierTableauProblem.FormulaTokenCursor.step_of_lt
            problem ⟨start⟩ inRange]
        simp only
        rw [inductionHypothesis (start := start + 1) nextBound nextFuel]
        have scheduleInRange : start < problem.formulaTokenSchedule.length := by
          rw [← problem.formulaTokenSlotCountDirect_eq]
          exact inRange
        rw [List.drop_eq_getElem_cons scheduleInRange]
        simp only
        congr

theorem run_body {language : Language}
    (problem : VerifierTableauProblem language) :
    run problem (bodySlotCount problem) ⟨firstBodySlot problem⟩ =
      (problem.formulaTokenSchedule.drop (firstBodySlot problem),
        ⟨problem.formulaTokenSlotCountDirect⟩) := by
  apply run_to_end
  · rw [← terminalSlot_eq problem, ← firstBodySlot_add_bodySlotCount problem]
    omega
  · rw [← terminalSlot_eq problem, ← firstBodySlot_add_bodySlotCount problem]
    omega

theorem run_full {language : Language}
    (problem : VerifierTableauProblem language) :
    run problem problem.formulaTokenSlotCountDirect
        VerifierTableauProblem.FormulaTokenCursor.initial =
      (problem.formulaTokenSchedule,
        ⟨problem.formulaTokenSlotCountDirect⟩) := by
  have hPrefix := run_prefix problem 0 problem.formulaTokenSlotCountDirect
    (by omega)
  simpa [VerifierTableauProblem.FormulaTokenCursor.initial,
    problem.formulaTokenSlotCountDirect_eq] using hPrefix

theorem run_excess {language : Language}
    (problem : VerifierTableauProblem language) (extra : Nat) :
    run problem (problem.formulaTokenSlotCountDirect + extra)
        VerifierTableauProblem.FormulaTokenCursor.initial =
      (problem.formulaTokenSchedule,
        ⟨problem.formulaTokenSlotCountDirect⟩) := by
  have complete := run_to_end problem 0
    (problem.formulaTokenSlotCountDirect + extra) (by omega) (by omega)
  simpa [VerifierTableauProblem.FormulaTokenCursor.initial] using complete

theorem run_full_emit_eq_encodeCNFTokens {language : Language}
    (problem : VerifierTableauProblem language) :
    FormulaSchedule.emit
        (run problem problem.formulaTokenSlotCountDirect
          VerifierTableauProblem.FormulaTokenCursor.initial).1 =
      encodeCNFTokens problem.formula := by
  rw [run_full]
  exact problem.formulaTokenSchedule_emit_eq_encodeCNFTokens

end TokenCursor

/-! ## Literal raw full-schedule controller -/

def countEvaluator {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderUnaryPolynomial.machine
    (bodySlotCountPolynomial problem.verifier)

def targetEvaluator {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderUnaryPolynomial.machine
    (terminalSlotPolynomial problem.verifier)

def countdownTargetMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePaddingRun.PaddingCountdown.machine
    (targetEvaluator problem)

def scheduleSuffixMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine (countEvaluator problem)
    (countdownTargetMachine problem)

/-- One finite literal table that computes and consumes the entire
input-dependent token-opportunity count.  The table controls the complete
schedule but intentionally does not yet decode or emit the body entries. -/
def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (BuilderCompleteHeader.machine problem)
    (scheduleSuffixMachine problem)

private theorem header_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (BuilderCompleteHeader.machine problem) := by
  exact BuilderCompleteHeader.rule_source_ne_acceptState problem

private theorem countEvaluator_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (countEvaluator problem) := by
  intro rule hRule
  exact Nat.ne_of_lt (BuilderUnaryPolynomial.rule_source_lt_acceptState
    (bodySlotCountPolynomial problem.verifier) rule hRule)

private theorem countdown_noRuleAtAccept :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      BuilderFirstClausePaddingRun.PaddingCountdown.machine := by
  exact
    BuilderFirstClausePaddingRun.PaddingCountdown.rule_source_ne_acceptState

private theorem targetEvaluator_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (targetEvaluator problem) := by
  intro rule hRule
  exact Nat.ne_of_lt (BuilderUnaryPolynomial.rule_source_lt_acceptState
    (terminalSlotPolynomial problem.verifier) rule hRule)

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.length =
      415 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial problem) +
        BuilderUnaryPolynomial.ruleCount
          (bodySlotCountPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (terminalSlotPolynomial problem.verifier) := by
  have hHeader := BuilderCompleteHeader.rules_length problem
  have hHeaderMachine :
      (BuilderCompleteHeader.machine problem).rules.length =
        363 + BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial problem) := by
    simpa [BuilderCompleteHeader.machine] using hHeader
  have hCount := BuilderUnaryPolynomial.rules_length
    (bodySlotCountPolynomial problem.verifier)
  have hTarget := BuilderUnaryPolynomial.rules_length
    (terminalSlotPolynomial problem.verifier)
  have hCountdown :=
    BuilderFirstClausePaddingRun.PaddingCountdown.rules_length
  have hCountMachine :
      (BuilderUnaryPolynomial.machine
        (bodySlotCountPolynomial problem.verifier)).rules.length =
      BuilderUnaryPolynomial.ruleCount
        (bodySlotCountPolynomial problem.verifier) := by
    simpa [BuilderUnaryPolynomial.machine] using hCount
  have hTargetMachine :
      (BuilderUnaryPolynomial.machine
        (terminalSlotPolynomial problem.verifier)).rules.length =
      BuilderUnaryPolynomial.ruleCount
        (terminalSlotPolynomial problem.verifier) := by
    simpa [BuilderUnaryPolynomial.machine] using hTarget
  have hCountdownMachine :
      BuilderFirstClausePaddingRun.PaddingCountdown.machine.rules.length =
        25 := by
    simpa [BuilderFirstClausePaddingRun.PaddingCountdown.machine] using
      hCountdown
  have hLaunch : ∀ source target,
      (launchRules source target).length = 9 := by
    intro source target
    rfl
  unfold machine scheduleSuffixMachine countdownTargetMachine countEvaluator
    targetEvaluator BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePrefix.WorkChain.rules
    BuilderFirstClausePrefix.WorkChain.bridgeRules
  simp only [List.length_append, List.length_map]
  rw [hHeaderMachine, hCountMachine, hTargetMachine, hCountdownMachine,
    hLaunch, hLaunch, hLaunch]
  omega

theorem rules_pairwise_query_distinct {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  have hCountdownTarget :=
    BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
      BuilderFirstClausePaddingRun.PaddingCountdown.machine
      (targetEvaluator problem)
      BuilderFirstClausePaddingRun.PaddingCountdown.rules_pairwise_query_distinct
      (BuilderUnaryPolynomial.rules_pairwise_query_distinct
        (terminalSlotPolynomial problem.verifier))
      countdown_noRuleAtAccept
  have hSuffix :=
    BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
      (countEvaluator problem) (countdownTargetMachine problem)
      (BuilderUnaryPolynomial.rules_pairwise_query_distinct
        (bodySlotCountPolynomial problem.verifier))
      hCountdownTarget (countEvaluator_noRuleAtAccept problem)
  exact BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    (BuilderCompleteHeader.machine problem)
    (scheduleSuffixMachine problem)
    (BuilderCompleteHeader.rules_pairwise_query_distinct problem)
    hSuffix (header_noRuleAtAccept problem)

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  exact BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
    (BuilderCompleteHeader.machine problem)
    (scheduleSuffixMachine problem)
    (BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
      (countEvaluator problem) (countdownTargetMachine problem)
      (BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
        BuilderFirstClausePaddingRun.PaddingCountdown.machine
        (targetEvaluator problem)
        (BuilderUnaryPolynomial.machine_acceptState_ne_rejectState
          (terminalSlotPolynomial problem.verifier))))

theorem rule_source_ne_acceptState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hRule : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).acceptState := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (BuilderCompleteHeader.machine problem)
    (scheduleSuffixMachine problem)
    (BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
      (countEvaluator problem) (countdownTargetMachine problem)
      (BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
        BuilderFirstClausePaddingRun.PaddingCountdown.machine
        (targetEvaluator problem) (targetEvaluator_noRuleAtAccept problem)))
    rule hRule

/-! ### Exact endpoint geometry -/

def countWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.scratchWord
    (bodySlotCountPolynomial problem.verifier) problem.input.length

def countRootPrefixLength {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (BuilderUnaryPolynomial.rootPrefixPolynomial
    (bodySlotCountPolynomial problem.verifier)).eval problem.input.length

def countControllerPrefixLength {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  countRootPrefixLength problem - 1

def countOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (bodySlotCountPolynomial problem.verifier) problem.input
    (BuilderCompleteHeader.finalOutside problem)

def countTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (countOutside problem)
    (BuilderCompleteHeader.headerTokens problem)

def countdownFinalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (countWord problem).take (countRootPrefixLength problem) ++
    List.replicate (bodySlotCount problem + 1)
      BuilderUnaryPolynomial.scratchEndSymbol ++
    (BuilderCompleteHeader.finalOutside problem).drop
      ((countWord problem).length + 1)

def countdownFinalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input
    (countdownFinalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (terminalSlotPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (finalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

def countdownWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  PaddingCountdown.loopSteps (countControllerPrefixLength problem)
    (bodySlotCount problem)

def suffixWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderUnaryPolynomial.workSteps
      (bodySlotCountPolynomial problem.verifier) problem.input + 1 +
    countdownWorkSteps problem + 1 +
    BuilderUnaryPolynomial.workSteps
      (terminalSlotPolynomial problem.verifier) problem.input

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderCompleteHeader.workSteps problem + 1 + suffixWorkSteps problem

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem) (BuilderCompleteHeader.headerTokens problem)

theorem countEvaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (countEvaluator problem)
        (BuilderUnaryPolynomial.workSteps
          (bodySlotCountPolynomial problem.verifier) problem.input)
        (BuilderUnaryPolynomial.initialConfiguration
          (bodySlotCountPolynomial problem.verifier) problem.input
          (BuilderCompleteHeader.finalOutside problem)
          (BuilderCompleteHeader.headerTokens problem)) =
      some
        (BuilderUnaryPolynomial.finalConfiguration
          (bodySlotCountPolynomial problem.verifier) problem.input
          (BuilderCompleteHeader.finalOutside problem)
          (BuilderCompleteHeader.headerTokens problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (bodySlotCountPolynomial problem.verifier) problem.input
    (BuilderCompleteHeader.finalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)

private theorem take_prefix_separator
    (wordPrefix suffix : List WorkSymbol) :
    (wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol :: suffix).take
        (wordPrefix.length + 1) =
      wordPrefix ++ [BuilderUnaryPolynomial.separatorSymbol] := by
  induction wordPrefix with
  | nil => rfl
  | cons first rest ih => simp [ih]

private theorem replicate_succ_append {alpha : Type}
    (count : Nat) (item : alpha) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change item :: List.replicate (count + 1) item =
        (item :: List.replicate count item) ++ [item]
      rw [ih]
      simp only [List.cons_append]

theorem countdown_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? PaddingCountdown.machine (countdownWorkSteps problem)
        (workStartConfiguration PaddingCountdown.machine
          (countTape problem)) =
      some
        { state := PaddingCountdown.machine.acceptState,
          tape := countdownFinalTape problem } := by
  let polynomial := bodySlotCountPolynomial problem.verifier
  let scratch := countWord problem
  let outside := BuilderCompleteHeader.finalOutside problem
  rcases BuilderUnaryPolynomial.root_register_length polynomial
      problem.input.length with ⟨wordPrefix, hScratch, hPrefixLength⟩
  have hCountEval : polynomial.eval problem.input.length =
      bodySlotCount problem := by rfl
  rw [hCountEval] at hScratch
  have hPrefixLength' : wordPrefix.length + 1 =
      countRootPrefixLength problem := by
    simpa [polynomial, countRootPrefixLength] using hPrefixLength
  have hScratch' : scratch =
      wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
        List.replicate (bodySlotCount problem)
          BuilderUnaryPolynomial.unitSymbol := by
    simpa [scratch, countWord, polynomial] using hScratch
  have hPositive := bodySlotCount_positive problem
  cases hCount : bodySlotCount problem with
  | zero => omega
  | succ remaining =>
      have hScratchLength : scratch.length + 1 =
          wordPrefix.length + (remaining + 1 + 1) + 1 := by
        rw [hScratch']
        simp [hCount]
      let tail := outside.drop
        (wordPrefix.length + (remaining + 1 + 1) + 1)
      have hCountOutside : countOutside problem =
          BuilderCompleteHeader.HeaderController.outsideBefore wordPrefix
            remaining tail := by
        change scratch ++ BuilderUnaryPolynomial.scratchEndSymbol ::
            outside.drop (scratch.length + 1) = _
        rw [hScratchLength]
        rw [hScratch']
        simp [BuilderCompleteHeader.HeaderController.outsideBefore,
          tail, hCount, replicate_succ_append,
          List.append_assoc]
      have hPrefixSymbols : ∀ symbol ∈ wordPrefix,
          symbol = BuilderUnaryPolynomial.unitSymbol ∨
          symbol = BuilderUnaryPolynomial.separatorSymbol := by
        intro symbol hMem
        have hInScratch : symbol ∈ scratch := by
          rw [hScratch']
          exact List.mem_append_left _ hMem
        exact BuilderUnaryPolynomial.scratchWord_symbol polynomial
          problem.input.length symbol (by
            simpa [scratch, countWord, polynomial] using hInScratch)
      have hLoop := PaddingCountdown.loop_workRunExact problem.input
        wordPrefix remaining tail
        (BuilderCompleteHeader.headerTokens problem) hPrefixSymbols
      have hFinalOutside : countdownFinalOutside problem =
          PaddingCountdown.finalOutside wordPrefix (remaining + 1) tail := by
        change scratch.take (countRootPrefixLength problem) ++
            List.replicate (bodySlotCount problem + 1)
            BuilderUnaryPolynomial.scratchEndSymbol ++
            outside.drop (scratch.length + 1) = _
        rw [hScratchLength]
        rw [hScratch', ← hPrefixLength', hCount]
        rw [take_prefix_separator]
        simp [PaddingCountdown.finalOutside, tail, List.append_assoc]
      simpa [countdownWorkSteps, countControllerPrefixLength,
        ← hPrefixLength', hCount, countTape,
        countdownFinalTape, hCountOutside, hFinalOutside,
        PaddingCountdown.initialConfiguration,
        PaddingCountdown.finalConfiguration,
        PaddingCountdown.finalOutside,
        PaddingCountdown.machine,
        BuilderCompleteHeader.HeaderController.initialConfiguration,
        workStartConfiguration] using hLoop

theorem targetEvaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (targetEvaluator problem)
        (BuilderUnaryPolynomial.workSteps
          (terminalSlotPolynomial problem.verifier) problem.input)
        (BuilderUnaryPolynomial.initialConfiguration
          (terminalSlotPolynomial problem.verifier) problem.input
          (countdownFinalOutside problem)
          (BuilderCompleteHeader.headerTokens problem)) =
      some
        (BuilderUnaryPolynomial.finalConfiguration
          (terminalSlotPolynomial problem.verifier) problem.input
          (countdownFinalOutside problem)
          (BuilderCompleteHeader.headerTokens problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (terminalSlotPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)

private theorem countdownTarget_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (countdownTargetMachine problem)
        (countdownWorkSteps problem + 1 +
          BuilderUnaryPolynomial.workSteps
            (terminalSlotPolynomial problem.verifier) problem.input)
        (workStartConfiguration (countdownTargetMachine problem)
          (countTape problem)) =
      some
        { state := (countdownTargetMachine problem).acceptState,
          tape := finalTape problem } := by
  let countdownInitial := workStartConfiguration PaddingCountdown.machine
    (countTape problem)
  let countdownFinal : WorkConfiguration :=
    { state := PaddingCountdown.machine.acceptState,
      tape := countdownFinalTape problem }
  let targetInitial := BuilderUnaryPolynomial.initialConfiguration
    (terminalSlotPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)
  let targetFinal := BuilderUnaryPolynomial.finalConfiguration
    (terminalSlotPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)
  have hCountdown : workRunExact? PaddingCountdown.machine
      (countdownWorkSteps problem) countdownInitial =
        some countdownFinal := by
    simpa [countdownInitial, countdownFinal] using
      countdown_workRunExact problem
  have hTarget : workRunExact? (targetEvaluator problem)
      (BuilderUnaryPolynomial.workSteps
        (terminalSlotPolynomial problem.verifier) problem.input)
      targetInitial = some targetFinal := by
    simpa [targetInitial, targetFinal] using
      targetEvaluator_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    PaddingCountdown.machine (targetEvaluator problem)
    (countdownWorkSteps problem)
    (BuilderUnaryPolynomial.workSteps
      (terminalSlotPolynomial problem.verifier) problem.input)
    countdownInitial countdownFinal targetFinal hCountdown
    (by simp [countdownFinal]) hTarget
  simpa [countdownTargetMachine, targetEvaluator, countdownInitial,
    targetFinal, finalTape, finalOutside,
    BuilderUnaryPolynomial.finalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine, workStartConfiguration,
    renameConfiguration, Nat.add_assoc] using hCombined

private theorem scheduleSuffix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (scheduleSuffixMachine problem) (suffixWorkSteps problem)
        (workStartConfiguration (scheduleSuffixMachine problem)
          (BuilderCompleteHeader.finalTape problem)) =
      some
        { state := (scheduleSuffixMachine problem).acceptState,
          tape := finalTape problem } := by
  let countInitial := BuilderUnaryPolynomial.initialConfiguration
    (bodySlotCountPolynomial problem.verifier) problem.input
    (BuilderCompleteHeader.finalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)
  let countFinal := BuilderUnaryPolynomial.finalConfiguration
    (bodySlotCountPolynomial problem.verifier) problem.input
    (BuilderCompleteHeader.finalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)
  let suffixFinal : WorkConfiguration :=
    { state := (countdownTargetMachine problem).acceptState,
      tape := finalTape problem }
  have hCount : workRunExact? (countEvaluator problem)
      (BuilderUnaryPolynomial.workSteps
        (bodySlotCountPolynomial problem.verifier) problem.input)
      countInitial = some countFinal := by
    simpa [countInitial, countFinal] using countEvaluator_workRunExact problem
  have hTail : workRunExact? (countdownTargetMachine problem)
      (countdownWorkSteps problem + 1 +
        BuilderUnaryPolynomial.workSteps
          (terminalSlotPolynomial problem.verifier) problem.input)
      { state := (countdownTargetMachine problem).startState,
        tape := countFinal.tape } = some suffixFinal := by
    simpa [countFinal, suffixFinal, countTape, countOutside,
      BuilderUnaryPolynomial.finalConfiguration,
      workStartConfiguration] using countdownTarget_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (countEvaluator problem) (countdownTargetMachine problem)
    (BuilderUnaryPolynomial.workSteps
      (bodySlotCountPolynomial problem.verifier) problem.input)
    (countdownWorkSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (terminalSlotPolynomial problem.verifier) problem.input)
    countInitial countFinal suffixFinal hCount rfl hTail
  simpa [scheduleSuffixMachine, countdownTargetMachine, targetEvaluator,
    countEvaluator, suffixWorkSteps, countInitial, suffixFinal,
    BuilderCompleteHeader.finalTape,
    BuilderCompleteHeader.finalOutside,
    BuilderUnaryPolynomial.initialConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine, workStartConfiguration,
    renameConfiguration, Nat.add_assoc] using hCombined

theorem prefix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderCompleteHeader.workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState
        (BuilderCompleteHeader.finalConfiguration problem)) := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    (BuilderCompleteHeader.machine problem) (machine problem)
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      (BuilderCompleteHeader.machine problem)
      (scheduleSuffixMachine problem))
    (BuilderCompleteHeader.workSteps problem)
    (workStartConfiguration (BuilderCompleteHeader.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderCompleteHeader.finalConfiguration problem)
    (BuilderCompleteHeader.workRunExact problem)
  simpa [machine, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hTransport

theorem launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderCompleteHeader.finalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration (scheduleSuffixMachine problem)
          (BuilderCompleteHeader.finalTape problem))) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    (BuilderCompleteHeader.machine problem)
    (scheduleSuffixMachine problem)
    (BuilderCompleteHeader.finalTape problem)
  simpa [machine, BuilderCompleteHeader.finalConfiguration,
    workStartConfiguration] using hLaunch

set_option maxRecDepth 1000000 in
/-- Every raw input follows the complete header trace, computes the full body
opportunity count, executes the input-dependent countdown exactly, and
materializes the unique terminal schedule coordinate. -/
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  let headerInitial := workStartConfiguration
    (BuilderCompleteHeader.machine problem)
    (rawInputWorkTape problem.input)
  let headerFinal := BuilderCompleteHeader.finalConfiguration problem
  let suffixFinal : WorkConfiguration :=
    { state := (scheduleSuffixMachine problem).acceptState,
      tape := finalTape problem }
  have hHeader : workRunExact? (BuilderCompleteHeader.machine problem)
      (BuilderCompleteHeader.workSteps problem) headerInitial =
        some headerFinal := by
    simpa [headerInitial, headerFinal] using
      BuilderCompleteHeader.workRunExact problem
  have hSuffix : workRunExact? (scheduleSuffixMachine problem)
      (suffixWorkSteps problem)
      { state := (scheduleSuffixMachine problem).startState,
        tape := headerFinal.tape } = some suffixFinal := by
    simpa [headerFinal, suffixFinal,
      BuilderCompleteHeader.finalConfiguration,
      workStartConfiguration] using scheduleSuffix_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (BuilderCompleteHeader.machine problem)
    (scheduleSuffixMachine problem)
    (BuilderCompleteHeader.workSteps problem)
    (suffixWorkSteps problem) headerInitial headerFinal suffixFinal
    hHeader rfl hSuffix
  simpa [machine, workSteps, headerInitial, suffixFinal,
    finalConfiguration, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hCombined

theorem finalTokenSlot_eq_complete_schedule {language : Language}
    (problem : VerifierTableauProblem language) :
    terminalSlot problem = problem.formulaTokenSchedule.length := by
  rw [terminalSlot_eq, ← problem.formulaTokenSlotCountDirect_eq]

theorem finalOutside_contains_terminalSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix tail,
      finalOutside problem =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (terminalSlot problem)
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail := by
  rcases BuilderUnaryPolynomial.root_register_length
      (terminalSlotPolynomial problem.verifier) problem.input.length with
    ⟨wordPrefix, hScratch, _hPrefixLength⟩
  refine ⟨wordPrefix,
    (countdownFinalOutside problem).drop
      ((BuilderUnaryPolynomial.scratchWord
        (terminalSlotPolynomial problem.verifier)
        problem.input.length).length + 1), ?_⟩
  unfold finalOutside BuilderUnaryPolynomial.finalOutsideLeft
    BuilderUnaryPolynomial.overlayScratch terminalSlot
  rw [hScratch]

theorem finalConfiguration_state {language : Language}
    (problem : VerifierTableauProblem language) :
    (finalConfiguration problem).state = (machine problem).acceptState := rfl

set_option maxRecDepth 100000 in
private theorem finalConfiguration_isHalted {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (finalConfiguration problem) = true := by
  unfold WorkMachine.isHalted
  rw [finalConfiguration_state]
  rw [(nat_beq_true_iff _ _).mpr rfl]
  rfl

/-! ### External compiled-time polynomial -/

private def scalePolynomial (coefficient : Nat)
    (polynomial : NatPolynomial) : NatPolynomial :=
  .mul (.constant coefficient) polynomial

def countdownBoundPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let count := bodySlotCountPolynomial verifier
  let rootPrefix := BuilderUnaryPolynomial.rootPrefixPolynomial count
  .add
    (.mul count
      (.add (scalePolynomial 2 rootPrefix) (.constant 8)))
    (.mul count count)

/-- External raw-transition bound for the header, three composition bridges,
both unary evaluators, and the complete input-dependent countdown. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let count := bodySlotCountPolynomial verifier
  let target := terminalSlotPolynomial verifier
  .add (BuilderCompleteHeader.rawTimeBound verifier)
    (.add (.constant 18)
      (.add
        (scalePolynomial 6
          (BuilderUnaryPolynomial.workTimePolynomial count))
        (.add
          (scalePolynomial 6 (countdownBoundPolynomial verifier))
          (scalePolynomial 6
            (BuilderUnaryPolynomial.workTimePolynomial target)))))

theorem countdownBoundPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (countdownBoundPolynomial problem.verifier).eval problem.input.length =
      bodySlotCount problem *
          (2 * countRootPrefixLength problem + 8) +
        bodySlotCount problem * bodySlotCount problem := by
  simp [countdownBoundPolynomial, scalePolynomial,
    NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, bodySlotCount,
    countRootPrefixLength]

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderCompleteHeader.rawTimeBound problem.verifier).eval
          problem.input.length + 18 +
        6 * BuilderUnaryPolynomial.workSteps
          (bodySlotCountPolynomial problem.verifier) problem.input +
        6 *
          (bodySlotCount problem *
              (2 * countRootPrefixLength problem + 8) +
            bodySlotCount problem * bodySlotCount problem) +
        6 * BuilderUnaryPolynomial.workSteps
          (terminalSlotPolynomial problem.verifier) problem.input := by
  rw [rawTimeBound]
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, scalePolynomial,
    BuilderUnaryPolynomial.workTimePolynomial_eval]
  rw [countdownBoundPolynomial_eval]
  omega

private theorem countdownWorkSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    countdownWorkSteps problem ≤
      bodySlotCount problem *
          (2 * countRootPrefixLength problem + 8) +
        bodySlotCount problem * bodySlotCount problem := by
  have hLoop := PaddingCountdown.loopSteps_le
    (countControllerPrefixLength problem) (bodySlotCount problem)
  rcases BuilderUnaryPolynomial.root_register_length
      (bodySlotCountPolynomial problem.verifier) problem.input.length with
    ⟨wordPrefix, _hScratch, hRootLength⟩
  have hRootPositive : 0 < countRootPrefixLength problem := by
    unfold countRootPrefixLength
    rw [← hRootLength]
    omega
  have hPrefix : countControllerPrefixLength problem + 1 ≤
      countRootPrefixLength problem := by
    unfold countControllerPrefixLength
    omega
  have hInside :
      2 * (countControllerPrefixLength problem + 1) + 8 ≤
        2 * countRootPrefixLength problem + 8 := by omega
  have hScaled := Nat.mul_le_mul_left
    (bodySlotCount problem) hInside
  unfold countdownWorkSteps
  exact Nat.le_trans hLoop (Nat.add_le_add_right hScaled _)

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hHeader := BuilderCompleteHeader.rawTimeBound_le problem
  have hCountdown := countdownWorkSteps_le problem
  have hCountdownScaled := Nat.mul_le_mul_left 6 hCountdown
  rw [rawTimeBound_eval]
  unfold workSteps suffixWorkSteps
  omega

/-! ### Compiled execution -/

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (machine problem)) (6 * workSteps problem)
        (encodeWorkConfiguration
          (workStartConfiguration (machine problem)
            (rawInputWorkTape problem.input))) =
      encodeWorkConfiguration (finalConfiguration problem) := by
  exact run_compileWorkMachine_mul_of_workRunExact
    (machine problem) (workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)

theorem run_compile_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        (encodeWorkConfiguration
          (workStartConfiguration (machine problem)
            (rawInputWorkTape problem.input))) =
      encodeWorkConfiguration (finalConfiguration problem) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    (machine problem) (workSteps problem)
    ((rawTimeBound problem.verifier).eval problem.input.length)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)
    (finalConfiguration_isHalted problem) (rawTimeBound_le problem)

theorem run_compile_rawTimeBound_blankEquivalent {language : Language}
    (problem : VerifierTableauProblem language) :
    Configuration.BlankEquivalent
      (run (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        (startConfig (compileWorkMachine (machine problem)) problem.input))
      (encodeWorkConfiguration (finalConfiguration problem)) := by
  have hStart := startConfig_compileWorkMachine_blankEquivalent
    (machine problem) problem.input
  have hRun := run_blankEquivalent (compileWorkMachine (machine problem))
    ((rawTimeBound problem.verifier).eval problem.input.length) hStart
  rw [run_compile_rawTimeBound problem] at hRun
  exact hRun

private theorem blankEquivalent_state (first second : Configuration)
    (hEquivalent : Configuration.BlankEquivalent first second) :
    first.state = second.state :=
  hEquivalent.1

private theorem blankEquivalent_accept_of_encoded
    (localMachine : WorkMachine) (first : Configuration)
    (final : WorkConfiguration)
    (hEquivalent : Configuration.BlankEquivalent first
      (encodeWorkConfiguration final))
    (hFinal : final.state = localMachine.acceptState) :
    first.state = (compileWorkMachine localMachine).acceptState := by
  have hState := blankEquivalent_state first
    (encodeWorkConfiguration final) hEquivalent
  have hEncoded := (encodeWorkConfiguration_accept_iff
    localMachine final).mpr hFinal
  exact hState.trans hEncoded

set_option maxRecDepth 100000 in
theorem boundedDecide_compile_accept {language : Language}
    (problem : VerifierTableauProblem language) :
    boundedDecide (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        problem.input = .accept := by
  apply (boundedDecide_accept_iff_final
    (compileWorkMachine (machine problem))
    ((rawTimeBound problem.verifier).eval problem.input.length)
    problem.input).mpr
  exact blankEquivalent_accept_of_encoded (machine problem) _
    (finalConfiguration problem)
    (run_compile_rawTimeBound_blankEquivalent problem)
    (finalConfiguration_state problem)

theorem boundedDecide_compile_ne_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    boundedDecide (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        problem.input ≠ .timeout := by
  rw [boundedDecide_compile_accept]
  intro impossible
  contradiction

theorem workBoundedDecide_accept {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem) (workSteps problem)
      (rawInputWorkTape problem.input) = .accept := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem) (workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)]
  dsimp only
  rw [finalConfiguration_state]
  rw [(nat_beq_true_iff _ _).mpr rfl]
  rfl

/-! ### Fail-closed trace boundaries -/

def malformedCountdownScratchConfiguration
    (left right : List WorkSymbol) : WorkConfiguration :=
  { state := BuilderCompleteHeader.HeaderController.seekEndState
    tape :=
      { left := left
        head := BuilderUnaryPolynomial.registerMarkSymbol
        right := right } }

def malformedCountdownRootConfiguration
    (left right : List WorkSymbol) : WorkConfiguration :=
  { state := BuilderCompleteHeader.HeaderController.consumeState
    tape :=
      { left := left
        head := BuilderUnaryPolynomial.separatorSymbol
        right := right } }

/-- A non-scratch symbol in the schedule-count scan is stuck and remains a
local timeout for every fuel budget. -/
theorem malformedCountdownScratch_timeout (fuel : Nat)
    (left right : List WorkSymbol) :
    (let config := malformedCountdownScratchConfiguration left right
     let result := workRun PaddingCountdown.machine fuel config
     if result.state == PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state == PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let config := malformedCountdownScratchConfiguration left right
  have hStep : workStep? PaddingCountdown.machine config = none := by
    rfl
  have hRun := workRun_eq_self_of_workStep?_eq_none
    PaddingCountdown.machine config fuel hStep
  change
    (if (workRun PaddingCountdown.machine fuel config).state ==
          PaddingCountdown.machine.acceptState then WorkVerdict.accept
     else if (workRun PaddingCountdown.machine fuel config).state ==
          PaddingCountdown.machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  rfl

/-- A separator where the root decrement requires a unit is also stuck and
cannot fall through to either countdown halt. -/
theorem malformedCountdownRoot_timeout (fuel : Nat)
    (left right : List WorkSymbol) :
    (let config := malformedCountdownRootConfiguration left right
     let result := workRun PaddingCountdown.machine fuel config
     if result.state == PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state == PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let config := malformedCountdownRootConfiguration left right
  have hStep : workStep? PaddingCountdown.machine config = none := by
    rfl
  have hRun := workRun_eq_self_of_workStep?_eq_none
    PaddingCountdown.machine config fuel hStep
  change
    (if (workRun PaddingCountdown.machine fuel config).state ==
          PaddingCountdown.machine.acceptState then WorkVerdict.accept
     else if (workRun PaddingCountdown.machine fuel config).state ==
          PaddingCountdown.machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  rfl

private theorem verdict_timeout_of_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration)
    (hHalted : (machine problem).isHalted config = false) :
    (if config.state == (machine problem).acceptState then WorkVerdict.accept
     else if config.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  unfold WorkMachine.isHalted at hHalted
  cases hAccept : (config.state == (machine problem).acceptState) with
  | true =>
      rw [hAccept] at hHalted
      contradiction
  | false =>
      cases hReject : (config.state == (machine problem).rejectState) with
      | true =>
          rw [hAccept, hReject] at hHalted
          contradiction
      | false => rfl

private theorem machine_isHalted_prefix_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          config) = false := by
  have hHalted :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
      (BuilderCompleteHeader.machine problem)
      (scheduleSuffixMachine problem) config
  simpa [machine] using hHalted

/-- The complete header endpoint is globally nonhalting until the outer
bridge launches the full-schedule count evaluator. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderCompleteHeader.workSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderCompleteHeader.workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (BuilderCompleteHeader.finalConfiguration problem))
    (prefix_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_prefix_false problem
      (BuilderCompleteHeader.finalConfiguration problem))

private theorem workRunExact_succ_split_last {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? (machine problem) (steps + 1) initial = some final →
      ∃ before,
        workRunExact? (machine problem) steps initial = some before ∧
        workStep? (machine problem) before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final hRun
      cases hStep : workStep? (machine problem) initial with
      | none =>
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next => some next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hNext : next = final := by
            change
              (match workStep? (machine problem) initial with
               | none => none
               | some result => some result) = some final at hRun
            rw [hStep] at hRun
            exact Option.some.inj hRun
          subst final
          exact ⟨initial, rfl, hStep⟩
  | succ steps ih =>
      intro initial final hRun
      cases hStep : workStep? (machine problem) initial with
      | none =>
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next =>
                 workRunExact? (machine problem) (steps + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? (machine problem) (steps + 1) next =
              some final := by
            change
              (match workStep? (machine problem) initial with
               | none => none
               | some result =>
                   workRunExact? (machine problem) (steps + 1) result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases ih next final hTail with ⟨before, hPrefix, hLast⟩
          refine ⟨before, ?_, hLast⟩
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some result =>
                 workRunExact? (machine problem) steps result) = some before
          rw [hStep]
          exact hPrefix

private theorem isHalted_false_of_workStep_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? (machine problem) config = some next) :
    (machine problem).isHalted config = false := by
  cases hHalted : (machine problem).isHalted config with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

private theorem workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language) : 0 < workSteps problem := by
  unfold workSteps
  omega

/-- Removing the final target-evaluator transition leaves a nonhalting state;
the exact full-schedule trace cannot accept one work step early. -/
theorem work_one_step_short_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem) (workSteps problem - 1)
        (rawInputWorkTape problem.input) = .timeout := by
  let short := workSteps problem - 1
  let initial := workStartConfiguration (machine problem)
    (rawInputWorkTape problem.input)
  let final := finalConfiguration problem
  have hSucc : short + 1 = workSteps problem := by
    dsimp [short]
    have hPositive := workSteps_positive problem
    omega
  have hExact := workRunExact problem
  change workRunExact? (machine problem) (workSteps problem) initial =
    some final at hExact
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last problem short initial final hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun (machine problem) short initial = before :=
    workRun_eq_of_workRunExact (machine problem) short initial before hPrefix
  have hNotHalted := isHalted_false_of_workStep_some
    problem before final hLast
  unfold workBoundedDecide
  change
    (let result := workRun (machine problem) short initial
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  exact verdict_timeout_of_not_halted problem before hNotHalted

/-! ### Public earned endpoint -/

/-- The M208 endpoint: the semantic cursor covers the complete generated
schedule, while one literal deterministic raw controller computes and
consumes the same input-dependent opportunity count within an explicit
polynomial bound.  The theorem does not claim that the raw loop decodes or
emits the visited body entries. -/
theorem cook_levin_full_schedule_cursor_controller_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    TokenCursor.run problem problem.formulaTokenSlotCountDirect
        VerifierTableauProblem.FormulaTokenCursor.initial =
          (problem.formulaTokenSchedule,
            ⟨problem.formulaTokenSlotCountDirect⟩) ∧
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
          some (finalConfiguration problem) ∧
    terminalSlot problem = problem.formulaTokenSchedule.length ∧
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length ∧
    boundedDecide (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        problem.input = .accept ∧
    workBoundedDecide (machine problem)
        (BuilderCompleteHeader.workSteps problem)
        (rawInputWorkTape problem.input) = .timeout ∧
    workBoundedDecide (machine problem) (workSteps problem - 1)
        (rawInputWorkTape problem.input) = .timeout := by
  exact ⟨TokenCursor.run_full problem, workRunExact problem,
    finalTokenSlot_eq_complete_schedule problem, rawTimeBound_le problem,
    boundedDecide_compile_accept problem,
    prefixEndpoint_before_launch_timeout problem,
    work_one_step_short_timeout problem⟩

end BuilderFullScheduleCursorController

end CookLevin

end PNP.Concrete

/-
Copyright (c) 2026 PNP Labs.

Exact canonical output of the complete physical Cook-Levin builder.
Every source-derived body request agrees with the fixed clause-token schedule.
The complete emitting loop therefore produces the canonical formula in its
original token order, preserving padding and the unique final Finish token.

The actual machine and its original-input polynomial bounds are reused.
The final external FunctionProgram input/output adapter and packaged reduction
remain separate obligations. The canonical bit word includes its framing bit.
-/
import PNP.Concrete.CookLevinBuilderRawInputLoop

namespace PNP.Concrete.CookLevin.BuilderCanonicalOutput

open BuilderDividerOperands (count width)
open BuilderClauseDividerOperands (quotient clauseWidth)
open BuilderClauseDividerExecution (constraintIndex)
open BuilderCursorOutputAdvance (nextOutput)
open BuilderFullScheduleCursorController (bodySlotCount)

private theorem rectangle_at (count width : Nat)
    (blockSlot : Fin count → Nat → Option α) (index : Nat)
    (hWidth : 0 < width) (hBound : index / width < count) :
    DirectSlot.rectangle count width blockSlot index =
      blockSlot ⟨index / width, hBound⟩ (index % width) := by
  rw [BuilderArbitrarySlotPostHeaderDecoder.rectangle_eq_coordinate?]
  cases hCoordinate : BuilderArbitrarySlotPostHeaderDecoder.rectangleCoordinate? count width index with
  | none =>
      have hOutside := (BuilderArbitrarySlotPostHeaderDecoder.rectangleCoordinate?_eq_none_iff
        count width index).mp hCoordinate
      have hInside := (Nat.div_lt_iff_lt_mul hWidth).mp hBound
      omega
  | some coordinate =>
      have hReconstruct := BuilderArbitrarySlotPostHeaderDecoder.rectangleCoordinate?_reconstruct hCoordinate
      have hLower : coordinate.1.val * width ≤ index := by omega
      have hUpper : index < (coordinate.1.val + 1) * width := by
        rw [Nat.succ_mul]
        have hRemainderBound := coordinate.2.isLt
        omega
      have hQuotient : index / width = coordinate.1.val := Nat.div_eq_of_lt_le hLower hUpper
      have hNatural := BuilderPostHeaderRawDivider.quotient_remainder_reconstruct index width
      have hRemainder : index % width = coordinate.2.val := by
        rw [hQuotient] at hNatural
        omega
      have hOuter : coordinate.1 = ⟨index / width, hBound⟩ := Fin.ext hQuotient.symm
      change blockSlot coordinate.1 coordinate.2.val = _
      rw [hOuter, hRemainder]

private theorem clause_result {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    problem.formulaClauseSlotDirect (quotient problem index) =
      (problem.formulaConstraintSlotDirect (constraintIndex problem index)).map
        (fun selected => selected.bind
          (fun constraint => constraint.emit[(quotient problem index) % clauseWidth problem]?)) := by
  have hIndex := BuilderClauseDividerExecution.constraintIndex_lt problem index hBody
  have hWidth : 0 < problem.formulaClauseSlotsPerConstraint :=
    BuilderClauseDividerOperands.clauseWidth_pos problem
  have hRemainder : (quotient problem index) % problem.formulaClauseSlotsPerConstraint < problem.formulaClauseSlotsPerConstraint :=
    Nat.mod_lt _ hWidth
  unfold VerifierTableauProblem.formulaClauseSlotDirect
  rw [rectangle_at _ _ _ _ hWidth hIndex]
  unfold VerifierTableauProblem.constraintClauseBlockSlotDirect
  simp only [constraintIndex, BuilderClauseDividerOperands.clauseWidth_value]
  cases hSelected : problem.formulaConstraintSlotDirect
      ((quotient problem index) / problem.formulaClauseSlotsPerConstraint) with
  | none => rfl
  | some selected =>
      cases selected with
      | none =>
          simp only [DirectSlot.pad, if_pos hRemainder]
          rfl
      | some constraint =>
          simp only [DirectSlot.pad, if_pos hRemainder]
          rw [LocalConstraint.clauseSlotDirect_eq_emit_getElem?]
          rfl

private theorem token_block_result {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Fin problem.formulaClauseSlotCount) (position : Nat)
    (hPosition : position < problem.formulaTokensPerClause) :
    problem.clauseTokenBlockSlotDirect coordinate position =
      (problem.formulaClauseSlotDirect coordinate.val).map
        (fun selected => selected.bind
          (fun clause => (encodeClauseTokens (BoundedClause.emit clause))[position]?)) := by
  unfold VerifierTableauProblem.clauseTokenBlockSlotDirect
  cases hSelected : problem.formulaClauseSlotDirect coordinate.val with
  | none => rfl
  | some selected =>
      cases selected with
      | none =>
          simp only [DirectSlot.pad, if_pos hPosition]
          rfl
      | some clause =>
          simp only [DirectSlot.pad, if_pos hPosition]
          rw [DirectToken.clauseSlot_eq_encodeClauseTokens_getElem?]
          rfl

/-- Exact optional token value at every original body coordinate. Outer
missing lookup and inner empty/padding emission remain different values. -/
theorem canonical_result_eq_direct {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    BuilderCursorTokenLookup.canonicalResult problem index = problem.formulaClauseTokenSlotDirect index := by
  have hWidth : 0 < problem.formulaTokensPerClause := BuilderDividerSourceExecution.width_pos problem
  have hPosition : index % problem.formulaTokensPerClause < problem.formulaTokensPerClause := Nat.mod_lt _ hWidth
  have hBodyDirect : index / problem.formulaTokensPerClause < problem.formulaClauseSlotCount := hBody
  unfold VerifierTableauProblem.formulaClauseTokenSlotDirect
  rw [rectangle_at problem.formulaClauseSlotCount problem.formulaTokensPerClause
    problem.clauseTokenBlockSlotDirect index hWidth hBodyDirect, token_block_result _ _ _ hPosition]
  change BuilderCursorTokenLookup.canonicalResult problem index =
    (problem.formulaClauseSlotDirect (quotient problem index)).map
      (fun selected => selected.bind
        (fun clause => (encodeClauseTokens (BoundedClause.emit clause))[index % width problem]?))
  rw [clause_result problem index hBody, BuilderCursorTokenLookup.canonical_result_eq_emit]
  cases hSource : problem.formulaConstraintSlotDirect (constraintIndex problem index) with
  | none => rfl
  | some source => cases source <;> rfl

def bodySchedule {language : Language} (problem : VerifierTableauProblem language) : List (Option CNFToken) :=
  problem.formulaClauseSchedule.flatMap problem.scheduledClauseTokens

theorem bodySchedule_length {language : Language} (problem : VerifierTableauProblem language) :
    (bodySchedule problem).length + 1 = bodySlotCount problem := by
  rw [bodySchedule, problem.formulaClauseTokensSchedule_length,
    BuilderFullScheduleCursorController.bodySlotCount_eq]

theorem canonical_result_eq_getElem {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    BuilderCursorTokenLookup.canonicalResult problem index = (bodySchedule problem)[index]? := by
  rw [canonical_result_eq_direct problem index hBody, problem.formulaClauseTokenSlotDirect_eq]
  rfl

/-- The complete remaining output, not a fixed fixture or a supplied schedule
certificate. The final opportunity contributes exactly one Finish token. -/
theorem completeOutput_eq_suffix {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBalance : index + (remaining + 1) = bodySlotCount problem) :
    BuilderCursorLoop.completeOutput problem index remaining output =
      (output ++ FormulaSchedule.emit ((bodySchedule problem).drop index)) ++ [CNFToken.finish] := by
  have hLength := bodySchedule_length problem
  induction remaining generalizing index output with
  | zero =>
      have hIndex : index = (bodySchedule problem).length := by omega
      simp [BuilderCursorLoop.completeOutput, hIndex, FormulaSchedule.emit]
  | succ remaining ih =>
      have hIn : index < (bodySchedule problem).length := by omega
      have hBody := BuilderCursorLoop.body_domain_of_balance problem index remaining hBalance
      obtain ⟨request, hCanonical⟩ :=
        BuilderCursorOutputAdvance.canonical_some_of_body problem index hBody
      have hGet := (canonical_result_eq_getElem problem index hBody).symm.trans hCanonical
      have hRequest : (bodySchedule problem)[index] = request := by
        rw [List.getElem?_eq_getElem hIn] at hGet
        exact Option.some.inj hGet
      rw [BuilderCursorLoop.completeOutput, hCanonical]
      change BuilderCursorLoop.completeOutput problem (index + 1) remaining (nextOutput output request) = _
      rw [ih (index + 1) (nextOutput output request) (by omega),
        List.drop_eq_getElem_cons hIn, hRequest]
      cases request <;>
        simp only [nextOutput, FormulaSchedule.emit_none, FormulaSchedule.emit_some,
          List.append_assoc, List.cons_append, List.nil_append]

/-- The one actual source-derived token stream equals the original canonical
formula encoding, not merely an equisatisfiable alternative. -/
theorem outputTokens_eq_encodeCNFTokens {language : Language} (problem : VerifierTableauProblem language) :
    BuilderRawInputLoop.outputTokens problem = encodeCNFTokens problem.formula := by
  have hPositive := BuilderFullScheduleCursorController.bodySlotCount_positive problem
  unfold BuilderRawInputLoop.outputTokens
  rw [completeOutput_eq_suffix problem 0 (bodySlotCount problem - 1)
    (encodeUnaryTokens problem.FormulaWidth) (by omega), List.drop_zero]
  unfold bodySchedule
  rw [problem.formulaClauseTokensSchedule_emit_eq]
  rfl

/-- The canonical raw word includes the existing trailing false framing bit.
This equality does not replace the required physical external-output adapter. -/
theorem encoded_output_eq_encodedFormula {language : Language} (problem : VerifierTableauProblem language) :
    encodeTokenPairs (BuilderRawInputLoop.outputTokens problem) ++ [false] = problem.encodedFormula := by
  rw [outputTokens_eq_encodeCNFTokens]
  rfl

def encodedSizeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.mul (.constant 2) (BuilderRawInputLoop.outputBound verifier)) (.constant 1)

theorem encodedFormula_length_le {language : Language} (problem : VerifierTableauProblem language) :
    problem.encodedFormula.length ≤ (encodedSizeBound problem.verifier).eval problem.input.length := by
  rw [← encoded_output_eq_encodedFormula]
  simp only [List.length_append, encodeTokenPairs_length, List.length_cons, List.length_nil,
    encodedSizeBound, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
  have hTokens := BuilderRawInputLoop.outputTokens_length_le problem
  omega

theorem workRun_canonical_from_raw {language : Language} (problem : VerifierTableauProblem language) :
    ∃ (steps : Nat) (final : WorkConfiguration),
      workRunExact? (BuilderRawInputLoop.machine problem.verifier) steps
        (BuilderRawInputLoop.initialConfiguration problem) = some final ∧
      final.state = (BuilderRawInputLoop.machine problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (bodySlotCount problem) 0 (encodeCNFTokens problem.formula)) ∧
      6 * steps ≤ (BuilderRawInputLoop.rawTimeBound problem.verifier).eval problem.input.length := by
  simpa only [outputTokens_eq_encodeCNFTokens] using BuilderRawInputLoop.workRun_from_raw problem

theorem uniform_raw_canonical_output {language : Language} (problem : VerifierTableauProblem language) :
    ∃ (rawSteps : Nat) (final : WorkConfiguration),
      rawSteps ≤ (BuilderRawInputLoop.rawTimeBound problem.verifier).eval problem.input.length ∧
      run (compileWorkMachine (BuilderRawInputLoop.machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (BuilderRawInputLoop.initialConfiguration problem)) = encodeWorkConfiguration final ∧
      final.state = (BuilderRawInputLoop.machine problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (bodySlotCount problem) 0 (encodeCNFTokens problem.formula)) ∧
      problem.encodedFormula.length ≤ (encodedSizeBound problem.verifier).eval problem.input.length := by
  obtain ⟨rawSteps, final, hTime, hRun, hAccept, hTape, _⟩ := BuilderRawInputLoop.uniform_raw_from_input problem
  rw [outputTokens_eq_encodeCNFTokens] at hTape
  exact ⟨rawSteps, final, hTime, hRun, hAccept, hTape, encodedFormula_length_le problem⟩

end PNP.Concrete.CookLevin.BuilderCanonicalOutput

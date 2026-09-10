/-
Copyright (c) 2026 PNP Labs.

Source-derived cursor geometry for the complete Cook-Levin builder.
The canonical prefix names a slice of the registers already physically built
by the initializer. It is not supplied workspace or an additional host oracle.
The cursor preserves arbitrary existing output, and its complete scan is bounded
in encoded source-input size under the index-plus-remaining invariant.

This does not select or emit a clause, process coordinate zero, or close the
complete formula-building loop or packaged polynomial reduction.
-/

import PNP.Concrete.CookLevinBuilderBalancedCursor

namespace PNP.Concrete.CookLevin.BuilderCursorSource

open PipelineTape
open BuilderUnaryPolynomial

/-- Name the part of the materialized word before the last two registers. -/
def prefixWord (counter width : NatPolynomial) (inputLength : Nat) : List WorkSymbol :=
  let encoded := scratchWord (BuilderDimensionRegisters.preparationPolynomial counter width)
    inputLength
  encoded.take (encoded.length - (counter.eval inputLength + 2))

theorem prefixWord_layout (counter width : NatPolynomial) (inputLength : Nat) :
    scratchWord (BuilderDimensionRegisters.preparationPolynomial counter width) inputLength =
      BuilderBalancedCursor.word (prefixWord counter width inputLength) 0
        (counter.eval inputLength) := by
  obtain ⟨wordPrefix, hScratch⟩ :=
    BuilderDimensionRegisters.scratchWord_layout counter width inputLength
  let beforeWidth := wordPrefix ++ separatorSymbol ::
    List.replicate (width.eval inputLength) unitSymbol
  have hLayout :
      scratchWord (BuilderDimensionRegisters.preparationPolynomial counter width) inputLength =
        BuilderBalancedCursor.word beforeWidth 0 (counter.eval inputLength) := by
    simpa only [BuilderBalancedCursor.word, beforeWidth,
      BuilderDimensionRegisters.dimensionWord_eq, List.replicate_zero,
      List.nil_append, List.append_assoc, List.cons_append] using hScratch
  have hLength :
      (scratchWord (BuilderDimensionRegisters.preparationPolynomial counter width)
        inputLength).length - (counter.eval inputLength + 2) = beforeWidth.length := by
    rw [hLayout, BuilderBalancedCursor.word_length]
    omega
  have hPrefix : prefixWord counter width inputLength = beforeWidth := by
    dsimp only [prefixWord]
    rw [hLength, hLayout]
    exact List.take_left
  rw [hPrefix]
  exact hLayout

theorem prefixWord_symbols (counter width : NatPolynomial) (inputLength : Nat) :
    BuilderBalancedCursor.RegisterSymbols (prefixWord counter width inputLength) := by
  intro symbol hMem
  exact scratchWord_symbol
    (BuilderDimensionRegisters.preparationPolynomial counter width) inputLength symbol
    (List.mem_of_mem_take hMem)

def registerPrefix {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  prefixWord (BuilderFullScheduleCursorController.bodySlotCountPolynomial problem.verifier)
    (BuilderDimensionRegisters.widthPolynomial problem.verifier) problem.input.length

theorem sourceWord_layout {language : Language}
    (problem : VerifierTableauProblem language) :
    scratchWord (BuilderDimensionRegisters.polynomial problem.verifier) problem.input.length =
      BuilderBalancedCursor.word (registerPrefix problem) 0
        (BuilderFullScheduleCursorController.bodySlotCount problem) := by
  simpa only [registerPrefix, BuilderDimensionRegisters.polynomial,
    BuilderFullScheduleCursorController.bodySlotCount] using
    prefixWord_layout
      (BuilderFullScheduleCursorController.bodySlotCountPolynomial problem.verifier)
      (BuilderDimensionRegisters.widthPolynomial problem.verifier) problem.input.length

theorem registerPrefix_symbols {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderBalancedCursor.RegisterSymbols (registerPrefix problem) :=
  prefixWord_symbols
    (BuilderFullScheduleCursorController.bodySlotCountPolynomial problem.verifier)
    (BuilderDimensionRegisters.widthPolynomial problem.verifier) problem.input.length

/-- Exterior beyond the active register end, exactly as left by initialization. -/
def preservedTail {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (BuilderCompleteHeader.finalOutside problem).drop
    ((scratchWord (BuilderDimensionRegisters.polynomial problem.verifier)
      problem.input.length).length + 1)

private def inputFrame (input : BitString) (output : List CNFToken) : WorkTape :=
  BuilderTokenAppender.workspaceTape input [] output

private theorem inputFrame_head_valid (input : BitString) (output : List CNFToken) :
    (inputFrame input output).head = .blank ∨
      (inputFrame input output).head = .zeroBlank ∨
      (inputFrame input output).head = .oneBlank := by
  cases input with
  | nil => exact Or.inl rfl
  | cons bit rest =>
    cases bit with
    | false => exact Or.inr (Or.inl rfl)
    | true => exact Or.inr (Or.inr rfl)

private theorem workspaceTape_shape (input : BitString)
    (outside : List WorkSymbol) (output : List CNFToken) :
    BuilderTokenAppender.workspaceTape input outside output =
      { left := leftMarker :: outside
        head := (inputFrame input output).head
        right := (inputFrame input output).right } := by
  cases input <;> rfl

def cursorTape {language : Language}
    (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : WorkTape :=
  BuilderBalancedCursor.sourceTape (inputFrame problem.input output).head
    (inputFrame problem.input output).right (registerPrefix problem)
    index remaining (preservedTail problem)

theorem cursorTape_eq_workspace {language : Language}
    (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    cursorTape problem index remaining output =
      BuilderTokenAppender.workspaceTape problem.input
        (BuilderBalancedCursor.outside (registerPrefix problem) index remaining
          (preservedTail problem)) output :=
  (workspaceTape_shape problem.input
    (BuilderBalancedCursor.outside (registerPrefix problem) index remaining
      (preservedTail problem)) output).symm

theorem cursorTape_represents {language : Language}
    (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    Represents (Tape.ofInput problem.input) (cursorTape problem index remaining output) := by
  rw [cursorTape_eq_workspace]
  exact BuilderTokenAppender.workspaceTape_represents _ _ _

private theorem initializer_tape_shape {language : Language}
    (problem : VerifierTableauProblem language) :
    (BuilderInitialization.finalConfiguration problem).tape =
      BuilderTokenAppender.workspaceTape problem.input
        (overlayScratch
          (scratchWord (BuilderDimensionRegisters.polynomial problem.verifier)
            problem.input.length)
          (BuilderCompleteHeader.finalOutside problem))
        (BuilderCompleteHeader.headerTokens problem) := by
  rfl

/-- This equality derives the entry tape; no prepared register prefix is a premise. -/
theorem initializer_tape_handoff {language : Language}
    (problem : VerifierTableauProblem language) :
    (BuilderInitialization.finalConfiguration problem).tape =
      cursorTape problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)
        (encodeUnaryTokens problem.FormulaWidth) := by
  rw [initializer_tape_shape, BuilderCompleteHeader.headerTokens_eq_encodeUnaryTokens,
    cursorTape_eq_workspace]
  exact congrArg
    (fun encoded => BuilderTokenAppender.workspaceTape problem.input
      (encoded ++ scratchEndSymbol :: preservedTail problem)
      (encodeUnaryTokens problem.FormulaWidth))
    (sourceWord_layout problem)

def initialConfiguration {language : Language}
    (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : WorkConfiguration :=
  { state := BuilderBalancedCursor.machine.startState
    tape := cursorTape problem index remaining output }

def advancedConfiguration {language : Language}
    (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : WorkConfiguration :=
  { state := BuilderBalancedCursor.machine.acceptState
    tape := cursorTape problem (index + 1) remaining output }

def exhaustedConfiguration {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat)
    (output : List CNFToken) : WorkConfiguration :=
  { state := BuilderBalancedCursor.machine.rejectState
    tape := cursorTape problem index 0 output }

theorem advance_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    workRunExact? BuilderBalancedCursor.machine
        (BuilderBalancedCursor.steps (registerPrefix problem).length index (remaining + 1))
        (initialConfiguration problem index (remaining + 1) output) =
      some (advancedConfiguration problem index remaining output) :=
  BuilderBalancedCursor.advance_workRunExact
    (inputFrame problem.input output).head (inputFrame problem.input output).right
    (registerPrefix problem) index remaining (preservedTail problem)
    (inputFrame_head_valid problem.input output) (registerPrefix_symbols problem)

theorem exhausted_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat)
    (output : List CNFToken) :
    workRunExact? BuilderBalancedCursor.machine
        (BuilderBalancedCursor.steps (registerPrefix problem).length index 0)
        (initialConfiguration problem index 0 output) =
      some (exhaustedConfiguration problem index output) :=
  BuilderBalancedCursor.exhausted_workRunExact
    (inputFrame problem.input output).head (inputFrame problem.input output).right
    (registerPrefix problem) index (preservedTail problem)
    (inputFrame_head_valid problem.input output) (registerPrefix_symbols problem)

theorem compiled_advance {language : Language}
    (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    run (compileWorkMachine BuilderBalancedCursor.machine)
        (6 * BuilderBalancedCursor.steps (registerPrefix problem).length index (remaining + 1))
        (encodeWorkConfiguration (initialConfiguration problem index (remaining + 1) output)) =
      encodeWorkConfiguration (advancedConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (advance_workRunExact problem index remaining output)

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.mul (.constant 12)
    (registerSpanPolynomial (BuilderDimensionRegisters.polynomial verifier))) (.constant 36)

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      12 * (scratchWord (BuilderDimensionRegisters.polynomial problem.verifier)
        problem.input.length).length + 36 := by
  rw [scratchWord_length]
  rfl

theorem invariant_span {language : Language}
    (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (BuilderBalancedCursor.word (registerPrefix problem) index remaining).length =
      (scratchWord (BuilderDimensionRegisters.polynomial problem.verifier)
        problem.input.length).length := by
  have hLength := congrArg List.length (sourceWord_layout problem)
  rw [BuilderBalancedCursor.word_length] at hLength
  rw [BuilderBalancedCursor.word_length]
  omega

/-- Charge the entire compiled scan, for every balanced coordinate and counter. -/
theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * BuilderBalancedCursor.steps (registerPrefix problem).length index remaining ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hBound := BuilderBalancedCursor.compiled_steps_le
    (registerPrefix problem).length index remaining
  have hSpan := invariant_span problem index remaining hBalance
  rw [BuilderBalancedCursor.word_length] at hSpan
  rw [rawTimeBound_eval]
  omega

end PNP.Concrete.CookLevin.BuilderCursorSource

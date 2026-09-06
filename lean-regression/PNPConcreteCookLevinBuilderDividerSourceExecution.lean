import PNP.Concrete.CookLevinBuilderDividerSourceExecution

namespace PNP.Concrete.CookLevinBuilderDividerSourceExecutionRegression

open CookLevin CookLevin.BuilderDividerSourceExecution PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (count width)
open BuilderPhysicalClassifierFinishMirroredDispatch (mirrorTape mirrorConfiguration)

example : dividerMachine.rules.length = 99 := divider_rules_length

example :
    BuilderDividerLayout.convertedTape 0 0 0 [leftMarker, rightMarker] [] =
      {
        left := [scratchEndSymbol]
        head := separatorSymbol
        right := [leftMarker, leftMarker, scratchEndSymbol, leftMarker, rightMarker]
      } := by decide

example :
    BuilderDividerLayout.convertedTape 2 3 2 [rightMarker] [] =
      {
        left := [unitSymbol, unitSymbol, separatorSymbol, unitSymbol, unitSymbol, scratchEndSymbol]
        head := unitSymbol
        right := [leftMarker, leftMarker, unitSymbol, unitSymbol, scratchEndSymbol, rightMarker]
      } := by decide

example :
    workRunExact? dividerMachine (BuilderPostHeaderRawDivider.workSteps 3 2)
      (workStartConfiguration dividerMachine
        (BuilderDividerLayout.convertedTape 2 3 2 [leftMarker, rightMarker] [])) =
    some (mirrorConfiguration (BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration
      3 2 [leftMarker, unitSymbol, unitSymbol, scratchEndSymbol, leftMarker, rightMarker])) := by decide

example :
    workRunExact? dividerMachine (BuilderPostHeaderRawDivider.workSteps 0 2)
      (workStartConfiguration dividerMachine
        (BuilderDividerLayout.convertedTape 0 0 2 [rightMarker] [])) =
    some (mirrorConfiguration (BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration
      0 2 [leftMarker, scratchEndSymbol, rightMarker])) := by decide

example (count index width : Nat) (workspace : List WorkSymbol) :
    BuilderDividerLayout.convertedTape count index width workspace [] =
      mirrorTape (BuilderPostHeaderRawTapeBridge.shieldedDividerInputTape index width
        (leftMarker :: (List.replicate count unitSymbol ++ scratchEndSymbol :: workspace))) :=
  convertedTape_eq_mirroredDividerInput count index width workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderDividerOperands.finalConfiguration problem index remaining output).tape =
      (layoutInitial problem index remaining output).tape :=
  operand_layout_handoff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (layoutFinal problem index remaining output).tape =
      mirrorTape (BuilderPostHeaderRawTapeBridge.shieldedDividerInputTape index (width problem)
        (exterior problem index remaining output)) :=
  layout_divider_handoff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) :
    0 < width problem := width_pos problem

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (preparedMachine problem.verifier) (preparedSteps problem index remaining)
        (workStartConfiguration (preparedMachine problem.verifier)
          (BuilderCursorSource.cursorTape problem index remaining output)) =
      some {
        state := (preparedMachine problem.verifier).acceptState
        tape := mirrorTape (BuilderPostHeaderRawTapeBridge.shieldedDividerInputTape index
          (width problem) (exterior problem index remaining output))
      } := prepared_workRunExact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) :=
  workRunExact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compile_exact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState :=
  finalConfiguration_state problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      {
        left := List.replicate (index / width problem) BuilderPostHeaderRawDivider.quotientMark
        head := scratchEndSymbol
        right := List.replicate (width problem) unitSymbol ++ separatorSymbol ::
          (List.replicate (index % width problem) unitSymbol ++
            List.replicate ((index / width problem) * width problem) BuilderPostHeaderRawDivider.consumedDividend ++
            leftMarker :: leftMarker :: (List.replicate (count problem) unitSymbol ++
              scratchEndSymbol :: preservedWorkspace problem index remaining output))
      } := final_tape_layout problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape.left.length = index / width problem :=
  quotient_mark_count problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    index % width problem < width problem := remainder_lt_width problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (index / width problem) * width problem + index % width problem = index :=
  quotient_remainder_reconstruct problem index

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  machine_acceptState_ne_rejectState verifier

example {language : Language} (problem : VerifierTableauProblem language)
    (operand : BuilderOperandRegisters.Operand) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    BuilderOperandRegisters.copiedValue problem index operand ≤
      (sourceSpan problem.verifier).eval problem.input.length :=
  operand_le_sourceSpan problem operand index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  rawTimeBound_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language) :
    workRunExact? (fromRawMachine problem.verifier) (fromRawSteps problem)
        (fromRawInitial problem) = some (fromRawFinal problem) := fromRaw_workRunExact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (fromRawMachine problem.verifier)) (6 * fromRawSteps problem)
        (encodeWorkConfiguration (fromRawInitial problem)) =
      encodeWorkConfiguration (fromRawFinal problem) := fromRaw_run_compile_exact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    6 * fromRawSteps problem ≤ (fromRawTimeBound problem.verifier).eval problem.input.length :=
  fromRawTimeBound_le problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (fromRawInitial problem).tape = rawInputWorkTape problem.input := rfl

/-- The first physical body coordinate is zero, not a skipped positive slot. -/
example {language : Language} (problem : VerifierTableauProblem language) :
    (fromRawFinal problem).tape.left = [] := by
  change (finalConfiguration problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)
    (encodeUnaryTokens problem.FormulaWidth)).tape.left = []
  rw [final_tape_layout]
  simp only [Nat.zero_div, List.replicate_zero]

end PNP.Concrete.CookLevinBuilderDividerSourceExecutionRegression

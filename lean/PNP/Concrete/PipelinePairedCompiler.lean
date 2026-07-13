/-
Copyright (c) 2026 PNP Labs.

Uniform polynomial bounds for the literal four-stage pipeline on canonical
paired inputs.

This module closes the caller-supplied-trace gap for proof-bearing target
machines: the target's bounded execution supplies its own exact successful
prefix, which is then framed, simulated, handed off, and packed by one finite
raw machine.  The result is deliberately stated only for canonical
`BitString.pair` inputs.  It does not yet provide malformed-input behavior or
an all-bitstring `RawRefinement`, CNF-SAT in P, CNF-SAT NP-completeness, or
P = NP.
-/

import PNP.Concrete.PipelineTerminalBridge

namespace PNP.Concrete

namespace Tape

/-- Number of represented cells visible from the current head to the right.
This is a conservative bound on blank-delimited observable output. -/
def outputWindowSize (tape : Tape) : Nat :=
  1 + tape.right.length

/-- Decoding a blank-delimited prefix cannot create more bits than cells. -/
theorem decodeOutputCells_length_le (cells : List TapeSymbol) :
    (decodeOutputCells cells).length ≤ cells.length := by
  induction cells with
  | nil => exact Nat.le_refl 0
  | cons symbol rest ih =>
      cases symbol with
      | blank => exact Nat.zero_le _
      | zero => exact Nat.succ_le_succ ih
      | one => exact Nat.succ_le_succ ih

/-- Observable output fits in the represented window at and right of the
head. -/
theorem outputBits_length_le_outputWindowSize (tape : Tape) :
    tape.outputBits.length ≤ tape.outputWindowSize := by
  unfold outputBits outputWindowSize
  simpa only [List.length_cons, Nat.succ_eq_add_one, Nat.add_comm] using
    (decodeOutputCells_length_le (tape.head :: tape.right))

/-- A canonical input tape initially exposes at most input length plus its
implicit blank delimiter. -/
theorem outputWindowSize_ofInput_le (input : BitString) :
    (ofInput input).outputWindowSize ≤ input.length + 1 := by
  cases input with
  | nil => exact Nat.le_refl 1
  | cons bit rest =>
      unfold ofInput outputWindowSize
      rw [length_map_ofBool]
      simpa only [List.length_cons, Nat.one_add] using
        (Nat.le_add_right (Nat.succ rest.length) 1)

/-- Writing does not change the represented output window. -/
theorem outputWindowSize_write (tape : Tape) (symbol : TapeSymbol) :
    (tape.write symbol).outputWindowSize = tape.outputWindowSize := by
  rfl

/-- Moving left materializes exactly one additional cell on the right. -/
theorem outputWindowSize_moveLeft (tape : Tape) :
    tape.moveLeft.outputWindowSize = tape.outputWindowSize + 1 := by
  cases tape with
  | mk left head right =>
      cases left <;> rfl

/-- Moving right never increases the represented output window. -/
theorem outputWindowSize_moveRight_le (tape : Tape) :
    tape.moveRight.outputWindowSize ≤ tape.outputWindowSize := by
  cases tape with
  | mk left head right =>
      cases right with
      | nil => exact Nat.le_refl 1
      | cons symbol rest =>
          change 1 + rest.length ≤ 1 + Nat.succ rest.length
          exact Nat.add_le_add_left (Nat.le_succ rest.length) 1

/-- One head movement grows the output window by at most one cell. -/
theorem outputWindowSize_move_le (tape : Tape) (movement : HeadMove) :
    (tape.move movement).outputWindowSize ≤ tape.outputWindowSize + 1 := by
  cases movement with
  | left =>
      unfold move
      rw [outputWindowSize_moveLeft]
      exact Nat.le_refl _
  | stay =>
      unfold move
      exact Nat.le_add_right tape.outputWindowSize 1
  | right =>
      unfold move
      exact Nat.le_trans (outputWindowSize_moveRight_le tape)
        (Nat.le_add_right tape.outputWindowSize 1)

end Tape

namespace PipelinePairedCompiler

open PipelineStateNamespace PipelineTerminalBridge

/-- The literal raw machine obtained by compiling the complete four-stage
work rule table. -/
def pairedPipelineMachine (target : Machine) : Machine :=
  compileWorkMachine (terminalBridgeMachine target)

/-- A target using `p(m)` raw transitions on an input of length `m` can
expose at most `m + p(m) + 1` blank-delimited output bits. -/
def pairedPipelineOutputSizeBound (targetBound : NatPolynomial) :
    NatPolynomial :=
  .add (.add .variable targetBound) (.constant 1)

/-- Complete raw transition bound for framing, both stage launches, target
simulation, represented-output handoff, terminal launch, and packing.

The two local output-dependent polynomials are composed with the conservative
target-output bound, so this expression depends only on external encoded
input length. -/
def pairedPipelineRawTimeBound (targetBound : NatPolynomial) :
    NatPolynomial :=
  .add
    (.add
      (.add
        (.add
          (.add PipelineInputFramer.pairedInputFramerRawTimeBound
            (.constant 6))
          (.mul (.constant 18) targetBound))
        (.constant 6))
      (NatPolynomial.substitute
        PipelineOutputHandoff.framedOutputHandoffRawTimeBound
        (pairedPipelineOutputSizeBound targetBound)))
    (NatPolynomial.substitute terminalBridgeRawTimeBound
      (pairedPipelineOutputSizeBound targetBound))

private theorem mulAssocSafe (left middle right : Nat) :
    (left * middle) * right = left * (middle * right) := by
  induction right with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ right ih =>
      calc
        (left * middle) * Nat.succ right =
            (left * middle) * right + left * middle :=
          Nat.mul_succ _ _
        _ = left * (middle * right) + left * middle :=
          congrArg (fun value => value + left * middle) ih
        _ = left * (middle * right + middle) :=
          (Nat.mul_add _ _ _).symm
        _ = left * (middle * Nat.succ right) :=
          congrArg (Nat.mul left) (Nat.mul_succ middle right).symm

/-- The represented-output handoff's advertised polynomial is exactly six
times its literal work cost. -/
theorem framedOutputHandoffRawTimeBound_exact (tape : Tape) :
    PipelineOutputHandoff.framedOutputHandoffRawTimeBound.eval
        tape.outputBits.length =
      6 * PipelineOutputHandoff.framedOutputHandoffWorkSteps tape := by
  unfold PipelineOutputHandoff.framedOutputHandoffRawTimeBound
    PipelineOutputHandoff.framedOutputHandoffWorkSteps BitString.size
  rw [NatPolynomial.eval_linear, Nat.mul_add, ← mulAssocSafe]

/-- The exact supplied-trace cost decomposes into the already-audited local
raw costs.  This equality is used only as arithmetic bookkeeping; the
execution itself remains the one literal compiled machine. -/
theorem suppliedTraceTerminalRawSteps_eq_components
    (left right : BitString) (steps : Nat) (finalTape : Tape) :
    suppliedTraceTerminalRawSteps left right steps finalTape =
      ((((PipelineInputFramer.pairedInputFramerRawTimeBound.eval
              (BitString.size (BitString.pair left right)) + 6) +
            18 * steps) + 6) +
          PipelineOutputHandoff.framedOutputHandoffRawTimeBound.eval
            finalTape.outputBits.length) +
        terminalBridgeRawSteps finalTape.outputBits := by
  unfold suppliedTraceTerminalRawSteps suppliedTraceTerminalWorkSteps
    PipelineStageBridges.bridgedWorkSteps
    PipelineStageBridges.simulationPrefixWorkSteps
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add,
    Nat.mul_add, ← mulAssocSafe 6 3 steps,
    ← PipelineInputFramer.pairedInputFramerRawTimeBound_exact left right,
    ← framedOutputHandoffRawTimeBound_exact finalTape]
  change _ + 6 * 1 + (6 * 3) * steps + 6 * 1 + _ +
      6 * terminalBridgeWorkSteps finalTape.outputBits = _
  rw [Nat.mul_one]
  change _ + 6 + 18 * steps + 6 + _ +
      terminalBridgeRawSteps finalTape.outputBits = _
  rfl

/-- Evaluation of the external output-size polynomial has the displayed
closed form. -/
theorem pairedPipelineOutputSizeBound_eval (targetBound : NatPolynomial)
    (inputSize : Nat) :
    (pairedPipelineOutputSizeBound targetBound).eval inputSize =
      inputSize + targetBound.eval inputSize + 1 := by
  rfl

/-- The exact four-stage trace is bounded by one polynomial evaluated only at
the external encoded paired-input length. -/
theorem suppliedTraceTerminalRawSteps_le_pairedPipelineRawTimeBound
    (targetBound : NatPolynomial) (left right : BitString)
    (steps : Nat) (finalTape : Tape)
    (hSteps : steps ≤
      targetBound.eval (BitString.size (BitString.pair left right)))
    (hOutput : finalTape.outputBits.length ≤
      (pairedPipelineOutputSizeBound targetBound).eval
        (BitString.size (BitString.pair left right))) :
    suppliedTraceTerminalRawSteps left right steps finalTape ≤
      (pairedPipelineRawTimeBound targetBound).eval
        (BitString.size (BitString.pair left right)) := by
  let inputSize := BitString.size (BitString.pair left right)
  have hSimulation : 18 * steps ≤ 18 * targetBound.eval inputSize :=
    Nat.mul_le_mul_left 18 hSteps
  have hHandoff := NatPolynomial.eval_mono
    PipelineOutputHandoff.framedOutputHandoffRawTimeBound hOutput
  have hTerminalLocal := terminalBridge_runtime_le finalTape.outputBits
  have hTerminalMonotone := NatPolynomial.eval_mono
    terminalBridgeRawTimeBound hOutput
  have hTerminal : terminalBridgeRawSteps finalTape.outputBits ≤
      terminalBridgeRawTimeBound.eval
        ((pairedPipelineOutputSizeBound targetBound).eval inputSize) :=
    Nat.le_trans hTerminalLocal hTerminalMonotone
  rw [suppliedTraceTerminalRawSteps_eq_components]
  unfold pairedPipelineRawTimeBound
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, NatPolynomial.eval_substitute]
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (Nat.le_refl _) (Nat.le_refl 6)) hSimulation)
        (Nat.le_refl 6))
      hHandoff)
    hTerminal

/-- Applying one raw rule grows the observable output window by at most one
represented cell. -/
theorem outputWindowSize_applyRule_le (rule : Rule)
    (config : Configuration) :
    (applyRule rule config).tape.outputWindowSize ≤
      config.tape.outputWindowSize + 1 := by
  unfold applyRule
  exact Tape.outputWindowSize_move_le
    (config.tape.write rule.writeSymbol) rule.move

/-- Every successful raw step grows the observable output window by at most
one represented cell. -/
theorem outputWindowSize_step_le (machine : Machine)
    (config next : Configuration)
    (hStep : step? machine config = some next) :
    next.tape.outputWindowSize ≤ config.tape.outputWindowSize + 1 := by
  unfold step? at hStep
  split at hStep
  · contradiction
  · split at hStep
    · contradiction
    · rename_i rule hRule
      have hNext : next = applyRule rule config := Option.some.inj hStep.symm
      rw [hNext]
      exact outputWindowSize_applyRule_le rule config

/-- An at-most run of `fuel` transitions grows the observable output window
by at most `fuel`. -/
theorem outputWindowSize_run_le (machine : Machine) (fuel : Nat)
    (config : Configuration) :
    (run machine fuel config).tape.outputWindowSize ≤
      config.tape.outputWindowSize + fuel := by
  induction fuel generalizing config with
  | zero => exact Nat.le_refl config.tape.outputWindowSize
  | succ fuel ih =>
      cases hStep : step? machine config with
      | none =>
          rw [run_succ, hStep]
          change config.tape.outputWindowSize ≤
            config.tape.outputWindowSize + Nat.succ fuel
          exact Nat.le_add_right _ _
      | some next =>
          rw [run_succ, hStep]
          change (run machine fuel next).tape.outputWindowSize ≤
            config.tape.outputWindowSize + Nat.succ fuel
          have hRun := ih next
          have hStepLe := outputWindowSize_step_le machine config next hStep
          calc
            (run machine fuel next).tape.outputWindowSize ≤
                next.tape.outputWindowSize + fuel := hRun
            _ ≤ (config.tape.outputWindowSize + 1) + fuel :=
              Nat.add_le_add_right hStepLe fuel
            _ = config.tape.outputWindowSize + Nat.succ fuel := by
              rw [Nat.add_assoc, Nat.one_add]

/-- A raw machine run cannot expose more than `input.length + fuel + 1`
blank-delimited output bits. -/
theorem machineOutput_length_le_input_add_fuel (machine : Machine)
    (fuel : Nat) (input : BitString) :
    (machineOutput machine fuel input).length ≤ input.length + fuel + 1 := by
  have hOutput := Tape.outputBits_length_le_outputWindowSize
    (run machine fuel (startConfig machine input)).tape
  have hRun := outputWindowSize_run_le machine fuel
    (startConfig machine input)
  have hInitial := Tape.outputWindowSize_ofInput_le input
  calc
    (machineOutput machine fuel input).length ≤
        (run machine fuel (startConfig machine input)).tape.outputWindowSize :=
      hOutput
    _ ≤ (startConfig machine input).tape.outputWindowSize + fuel := hRun
    _ ≤ (input.length + 1) + fuel := Nat.add_le_add_right hInitial fuel
    _ = input.length + fuel + 1 := by
      rw [Nat.add_assoc, Nat.add_comm 1 fuel, ← Nat.add_assoc]

/-- An exact target prefix no longer needs a caller-supplied output bound: its
length follows from the same external fuel bound used for simulation. -/
theorem outputBits_length_le_pairedPipelineOutputSizeBound_of_rawRunExact
    (machine : Machine) (targetBound : NatPolynomial)
    (steps : Nat) (left right : BitString) (final : Configuration)
    (hSteps : steps ≤
      targetBound.eval (BitString.size (BitString.pair left right)))
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final) :
    final.tape.outputBits.length ≤
      (pairedPipelineOutputSizeBound targetBound).eval
        (BitString.size (BitString.pair left right)) := by
  have hRun := PipelineMachineSimulation.run_eq_of_rawRunExact
    machine steps (startConfig machine (BitString.pair left right)) final hRaw
  have hOutput := machineOutput_length_le_input_add_fuel machine steps
    (BitString.pair left right)
  unfold machineOutput at hOutput
  rw [hRun] at hOutput
  rw [pairedPipelineOutputSizeBound_eval]
  exact Nat.le_trans hOutput
    (Nat.add_le_add_right
      (Nat.add_le_add_left hSteps
        (BitString.size (BitString.pair left right))) 1)

/-- Every exact prefix extracted below from the target's bounded run fits the
external four-stage raw polynomial. -/
theorem suppliedTraceTerminalRawSteps_le_of_rawRunExact
    (machine : Machine) (targetBound : NatPolynomial)
    (steps : Nat) (left right : BitString) (final : Configuration)
    (hSteps : steps ≤
      targetBound.eval (BitString.size (BitString.pair left right)))
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final) :
    suppliedTraceTerminalRawSteps left right steps final.tape ≤
      (pairedPipelineRawTimeBound targetBound).eval
        (BitString.size (BitString.pair left right)) := by
  exact suppliedTraceTerminalRawSteps_le_pairedPipelineRawTimeBound
    targetBound left right steps final.tape hSteps
    (outputBits_length_le_pairedPipelineOutputSizeBound_of_rawRunExact
      machine targetBound steps left right final hSteps hRaw)

/-- A target accepting exact prefix reaches the compiled pipeline's terminal
accept configuration even when padded to the external polynomial budget. -/
theorem run_pairedPipeline_accept_at_bound_of_rawRunExact
    (machine : Machine) (targetBound : NatPolynomial)
    (steps : Nat) (left right : BitString) (final : Configuration)
    (hSteps : steps ≤
      targetBound.eval (BitString.size (BitString.pair left right)))
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hAccept : final.state = machine.acceptState) :
    ∃ outsideLeft outsideRight,
      run (pairedPipelineMachine machine)
          ((pairedPipelineRawTimeBound targetBound).eval
            (BitString.size (BitString.pair left right)))
          (startConfig (pairedPipelineMachine machine)
            (BitString.pair left right)) =
        encodeWorkConfiguration
          (renameConfiguration acceptingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              final.tape.outputBits outsideLeft outsideRight)) := by
  rcases acceptingSuppliedTrace_workRunExact_of_rawRunExact
      machine steps left right final hRaw hAccept with
    ⟨_, _, outsideLeft, outsideRight, _, _, _, hExact⟩
  have hCost := suppliedTraceTerminalRawSteps_le_of_rawRunExact
    machine targetBound steps left right final hSteps hRaw
  change 6 * suppliedTraceTerminalWorkSteps left right steps final.tape ≤
    (pairedPipelineRawTimeBound targetBound).eval
      (BitString.size (BitString.pair left right)) at hCost
  have hCompiled := run_compileWorkMachine_of_workRunExact_halted_le
    (terminalBridgeMachine machine)
    (suppliedTraceTerminalWorkSteps left right steps final.tape)
    ((pairedPipelineRawTimeBound targetBound).eval
      (BitString.size (BitString.pair left right)))
    (workStartConfiguration (terminalBridgeMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration acceptingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight))
    hExact
    (acceptingTerminalFinal_isHalted machine final.tape.outputBits
      outsideLeft outsideRight)
    hCost
  rw [← startConfig_compileWorkMachine_paired
    (terminalBridgeMachine machine) left right] at hCompiled
  exact ⟨outsideLeft, outsideRight, by
    simpa [pairedPipelineMachine] using hCompiled⟩

/-- A target rejecting exact prefix uses the disjoint rejecting namespace and
remains rejected through polynomial padding. -/
theorem run_pairedPipeline_reject_at_bound_of_rawRunExact
    (machine : Machine) (targetBound : NatPolynomial)
    (steps : Nat) (left right : BitString) (final : Configuration)
    (hDistinct : machine.rejectState ≠ machine.acceptState)
    (hSteps : steps ≤
      targetBound.eval (BitString.size (BitString.pair left right)))
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hReject : final.state = machine.rejectState) :
    ∃ outsideLeft outsideRight,
      run (pairedPipelineMachine machine)
          ((pairedPipelineRawTimeBound targetBound).eval
            (BitString.size (BitString.pair left right)))
          (startConfig (pairedPipelineMachine machine)
            (BitString.pair left right)) =
        encodeWorkConfiguration
          (renameConfiguration rejectingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              final.tape.outputBits outsideLeft outsideRight)) := by
  rcases rejectingSuppliedTrace_workRunExact_of_rawRunExact
      machine steps left right final hDistinct hRaw hReject with
    ⟨_, _, outsideLeft, outsideRight, _, _, _, hExact⟩
  have hCost := suppliedTraceTerminalRawSteps_le_of_rawRunExact
    machine targetBound steps left right final hSteps hRaw
  change 6 * suppliedTraceTerminalWorkSteps left right steps final.tape ≤
    (pairedPipelineRawTimeBound targetBound).eval
      (BitString.size (BitString.pair left right)) at hCost
  have hCompiled := run_compileWorkMachine_of_workRunExact_halted_le
    (terminalBridgeMachine machine)
    (suppliedTraceTerminalWorkSteps left right steps final.tape)
    ((pairedPipelineRawTimeBound targetBound).eval
      (BitString.size (BitString.pair left right)))
    (workStartConfiguration (terminalBridgeMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration rejectingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight))
    hExact
    (rejectingTerminalFinal_isHalted machine final.tape.outputBits
      outsideLeft outsideRight)
    hCost
  rw [← startConfig_compileWorkMachine_paired
    (terminalBridgeMachine machine) left right] at hCompiled
  exact ⟨outsideLeft, outsideRight, by
    simpa [pairedPipelineMachine] using hCompiled⟩

/-- The target's proof-bearing bounded execution supplies the exact prefix
internally.  At the external polynomial budget, the one compiled raw machine
has exactly the target verdict and exactly the target blank-delimited output
on every canonical pair. -/
theorem pairedPipeline_correct_on_pair
    (machine : Machine) (targetBound : NatPolynomial)
    (left right : BitString)
    (hHalts : boundedDecide machine
      (targetBound.eval (BitString.size (BitString.pair left right)))
      (BitString.pair left right) ≠ .timeout) :
    boundedDecide (pairedPipelineMachine machine)
        ((pairedPipelineRawTimeBound targetBound).eval
          (BitString.size (BitString.pair left right)))
        (BitString.pair left right) =
        boundedDecide machine
          (targetBound.eval (BitString.size (BitString.pair left right)))
          (BitString.pair left right) ∧
      machineOutput (pairedPipelineMachine machine)
        ((pairedPipelineRawTimeBound targetBound).eval
          (BitString.size (BitString.pair left right)))
        (BitString.pair left right) =
        machineOutput machine
          (targetBound.eval (BitString.size (BitString.pair left right)))
          (BitString.pair left right) := by
  let input := BitString.pair left right
  let fuel := targetBound.eval (BitString.size input)
  let final := run machine fuel (startConfig machine input)
  rcases PipelineMachineSimulation.rawRunExact?_exists_le_run
      machine fuel (startConfig machine input) with
    ⟨steps, hSteps, hRaw⟩
  have hRaw' : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final := by
    simpa [input, fuel, final] using hRaw
  have hSteps' : steps ≤
      targetBound.eval (BitString.size (BitString.pair left right)) := by
    simpa [input, fuel] using hSteps
  cases hVerdict : boundedDecide machine fuel input with
  | accept =>
      have hAccept : final.state = machine.acceptState := by
        apply (boundedDecide_accept_iff_final machine fuel input).1
        exact hVerdict
      rcases run_pairedPipeline_accept_at_bound_of_rawRunExact
          machine targetBound steps left right final hSteps' hRaw' hAccept with
        ⟨outsideLeft, outsideRight, hRun⟩
      have hPipelineAccept :
          boundedDecide (pairedPipelineMachine machine)
              ((pairedPipelineRawTimeBound targetBound).eval
                (BitString.size (BitString.pair left right)))
              (BitString.pair left right) = .accept := by
        apply (boundedDecide_accept_iff_final
          (pairedPipelineMachine machine)
          ((pairedPipelineRawTimeBound targetBound).eval
            (BitString.size (BitString.pair left right)))
          (BitString.pair left right)).2
        rw [hRun]
        apply (encodeWorkConfiguration_accept_iff
          (terminalBridgeMachine machine)
          (renameConfiguration acceptingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              final.tape.outputBits outsideLeft outsideRight))).2
        exact acceptingTerminalFinal_state_eq_accept machine
          final.tape.outputBits outsideLeft outsideRight
      constructor
      · rw [hPipelineAccept]
      · unfold machineOutput
        rw [hRun]
        unfold encodeWorkConfiguration
        have hOutput := acceptingTerminal_output_eq final.tape.outputBits
          outsideLeft outsideRight
        simpa [input, fuel, final] using hOutput
  | reject =>
      have hRejectFinal :=
        (boundedDecide_reject_iff_final machine fuel input).1 hVerdict
      have hReject : final.state = machine.rejectState := hRejectFinal.2
      have hDistinct : machine.rejectState ≠ machine.acceptState := by
        intro hEqual
        exact hRejectFinal.1 (hReject.trans hEqual)
      rcases run_pairedPipeline_reject_at_bound_of_rawRunExact
          machine targetBound steps left right final hDistinct hSteps' hRaw'
            hReject with
        ⟨outsideLeft, outsideRight, hRun⟩
      let packedFinal := renameConfiguration rejectingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          final.tape.outputBits outsideLeft outsideRight)
      have hPackedReject : packedFinal.state =
          (terminalBridgeMachine machine).rejectState := by
        exact rejectingTerminalFinal_state_eq_reject machine
          final.tape.outputBits outsideLeft outsideRight
      have hPackedNotAccept : packedFinal.state ≠
          (terminalBridgeMachine machine).acceptState := by
        intro hPackedAccept
        exact terminalBridgeMachine_acceptState_ne_rejectState machine
          (hPackedAccept.symm.trans hPackedReject)
      have hPipelineReject :
          boundedDecide (pairedPipelineMachine machine)
              ((pairedPipelineRawTimeBound targetBound).eval
                (BitString.size (BitString.pair left right)))
              (BitString.pair left right) = .reject := by
        apply (boundedDecide_reject_iff_final
          (pairedPipelineMachine machine)
          ((pairedPipelineRawTimeBound targetBound).eval
            (BitString.size (BitString.pair left right)))
          (BitString.pair left right)).2
        constructor
        · rw [hRun]
          intro hEncodedAccept
          have hWorkAccept := (encodeWorkConfiguration_accept_iff
            (terminalBridgeMachine machine) packedFinal).1 hEncodedAccept
          exact hPackedNotAccept hWorkAccept
        · rw [hRun]
          exact (encodeWorkConfiguration_reject_iff
            (terminalBridgeMachine machine) packedFinal).2 hPackedReject
      constructor
      · rw [hPipelineReject]
      · unfold machineOutput
        rw [hRun]
        unfold encodeWorkConfiguration
        have hOutput := rejectingTerminal_output_eq final.tape.outputBits
          outsideLeft outsideRight
        simpa [input, fuel, final, packedFinal] using hOutput
  | timeout =>
      exact False.elim (hHalts (by simpa [input, fuel] using hVerdict))

/-- A proof-bearing polynomial-time target has exactly the same verdict after
literal four-stage compilation on every canonical pair. -/
theorem pairedPipeline_boundedDecide_eq
    {language : BitString → Prop}
    (target : PolynomialTimeMachine language) (left right : BitString) :
    boundedDecide (pairedPipelineMachine target.machine)
        ((pairedPipelineRawTimeBound target.timeBound).eval
          (BitString.size (BitString.pair left right)))
        (BitString.pair left right) =
      boundedDecide target.machine
        (target.timeBound.eval
          (BitString.size (BitString.pair left right)))
        (BitString.pair left right) := by
  exact (pairedPipeline_correct_on_pair target.machine target.timeBound
    left right (target.haltsWithin (BitString.pair left right))).1

/-- The same compiled run preserves the target's exact ordinary raw output. -/
theorem pairedPipeline_machineOutput_eq
    {language : BitString → Prop}
    (target : PolynomialTimeMachine language) (left right : BitString) :
    machineOutput (pairedPipelineMachine target.machine)
        ((pairedPipelineRawTimeBound target.timeBound).eval
          (BitString.size (BitString.pair left right)))
        (BitString.pair left right) =
      machineOutput target.machine
        (target.timeBound.eval
          (BitString.size (BitString.pair left right)))
        (BitString.pair left right) := by
  exact (pairedPipeline_correct_on_pair target.machine target.timeBound
    left right (target.haltsWithin (BitString.pair left right))).2

/-- The compiled paired-input pipeline cannot time out at its external
polynomial budget. -/
theorem pairedPipeline_ne_timeout
    {language : BitString → Prop}
    (target : PolynomialTimeMachine language) (left right : BitString) :
    boundedDecide (pairedPipelineMachine target.machine)
        ((pairedPipelineRawTimeBound target.timeBound).eval
          (BitString.size (BitString.pair left right)))
        (BitString.pair left right) ≠ .timeout := by
  rw [pairedPipeline_boundedDecide_eq target left right]
  exact target.haltsWithin (BitString.pair left right)

/-- Acceptance by the compiled pipeline on a canonical pair is exactly the
target language, with no host-interpreted composition. -/
theorem pairedPipeline_accepts_iff
    {language : BitString → Prop}
    (target : PolynomialTimeMachine language) (left right : BitString) :
    boundedDecide (pairedPipelineMachine target.machine)
        ((pairedPipelineRawTimeBound target.timeBound).eval
          (BitString.size (BitString.pair left right)))
        (BitString.pair left right) = .accept ↔
      language (BitString.pair left right) := by
  rw [pairedPipeline_boundedDecide_eq target left right]
  exact target.accepts_iff (BitString.pair left right)

end PipelinePairedCompiler

end PNP.Concrete

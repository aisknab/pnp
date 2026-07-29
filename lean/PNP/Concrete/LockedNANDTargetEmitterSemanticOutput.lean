/-
Copyright (c) 2026 PNP Labs.

Pure token semantics of the fixed locked-NAND target-emitter output loop.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerOutputTrace

namespace PNP.Concrete.LockedNAND.TargetEmitterSemanticOutput

open PNP.Concrete

abbrev Runtime := TargetEmitterProgramSemantics.Runtime

def outputTailTokens
    (scratch remaining baseline : Nat) : List Token :=
  encodeSourceListTokens
      ((List.range' scratch remaining).map RawSource.gate) ++
    encodeSourceTokens (.gate (scratch + remaining + 3)) ++
    [.outputsEnd, .threshold] ++
    encodeNatTokens baseline ++ [.instanceEnd]

/-- The proof-side recursion used to verify the literal comparison loop emits
exactly the increasing gate-coordinate suffix selected by its current unary
scratch value. -/
theorem outputLoopResult_targetTokens
    (remaining : Nat) (runtime : Runtime) :
    (TargetEmitterControllerOutputTrace.outputLoopResult
      remaining runtime).targetTokens =
        runtime.targetTokens ++
          outputTailTokens runtime.scratch remaining
            runtime.registers.baseline := by
  induction remaining generalizing runtime with
  | zero =>
      simp [TargetEmitterControllerOutputTrace.outputLoopResult,
        outputTailTokens,
        TargetEmitterProgramSemantics.outputLoopFinishResult,
        encodeSourceListTokens, List.append_assoc]
  | succ remaining inductionHypothesis =>
      rw [TargetEmitterControllerOutputTrace.outputLoopResult]
      rw [inductionHypothesis]
      simp [outputTailTokens,
        TargetEmitterProgramSemantics.outputLoopItemResult,
        encodeSourceListTokens, List.range',
        Nat.add_assoc, List.append_assoc]
      congr 2
      omega

theorem outputLoopResult_registers
    (remaining : Nat) (runtime : Runtime) :
    (TargetEmitterControllerOutputTrace.outputLoopResult
      remaining runtime).registers = runtime.registers := by
  induction remaining generalizing runtime with
  | zero =>
      rfl
  | succ remaining inductionHypothesis =>
      rw [TargetEmitterControllerOutputTrace.outputLoopResult]
      rw [inductionHypothesis]
      rfl

theorem outputLoopResult_checks
    (remaining : Nat) (runtime : Runtime) :
    (TargetEmitterControllerOutputTrace.outputLoopResult
      remaining runtime).checks = runtime.checks := by
  induction remaining generalizing runtime with
  | zero =>
      rfl
  | succ remaining inductionHypothesis =>
      rw [TargetEmitterControllerOutputTrace.outputLoopResult]
      rw [inductionHypothesis]
      rfl

theorem outputLoopResult_scratch
    (remaining : Nat) (runtime : Runtime) :
    (TargetEmitterControllerOutputTrace.outputLoopResult
      remaining runtime).scratch =
        runtime.registers.baseline := by
  induction remaining generalizing runtime with
  | zero =>
      rfl
  | succ remaining inductionHypothesis =>
      rw [TargetEmitterControllerOutputTrace.outputLoopResult]
      rw [inductionHypothesis]
      rfl

def completeOutputResult (runtime : Runtime) : Runtime :=
  TargetEmitterControllerOutputTrace.outputLoopResult
    runtime.registers.baseline
    (TargetEmitterProgramSemantics.beginOutputResult runtime)

/-- Starting at `beginOutputRef`, the logical output phase serializes every
baseline gate in increasing order, then the final gate, threshold, and
instance terminator. -/
theorem completeOutputResult_targetTokens
    (runtime : Runtime) :
    (completeOutputResult runtime).targetTokens =
      runtime.targetTokens ++ [.programEnd] ++
        encodeSourceListTokens
          ((List.range runtime.registers.baseline).map
            RawSource.gate) ++
        encodeSourceTokens
          (.gate (runtime.registers.baseline + 3)) ++
        [.outputsEnd, .threshold] ++
        encodeNatTokens runtime.registers.baseline ++
        [.instanceEnd] := by
  rw [completeOutputResult,
    outputLoopResult_targetTokens]
  rw [List.range_eq_range']
  simp [TargetEmitterProgramSemantics.beginOutputResult,
    outputTailTokens, List.append_assoc]

theorem completeOutputResult_registers
    (runtime : Runtime) :
    (completeOutputResult runtime).registers =
      runtime.registers := by
  simpa [completeOutputResult,
    TargetEmitterProgramSemantics.beginOutputResult] using
    (outputLoopResult_registers
      runtime.registers.baseline
      (TargetEmitterProgramSemantics.beginOutputResult runtime))

theorem completeOutputResult_checks
    (runtime : Runtime) :
    (completeOutputResult runtime).checks =
      runtime.checks := by
  simpa [completeOutputResult,
    TargetEmitterProgramSemantics.beginOutputResult] using
    (outputLoopResult_checks
      runtime.registers.baseline
      (TargetEmitterProgramSemantics.beginOutputResult runtime))

theorem completeOutputResult_scratch
    (runtime : Runtime) :
    (completeOutputResult runtime).scratch =
      runtime.registers.baseline := by
  simpa [completeOutputResult,
    TargetEmitterProgramSemantics.beginOutputResult] using
    (outputLoopResult_scratch
      runtime.registers.baseline
      (TargetEmitterProgramSemantics.beginOutputResult runtime))

private theorem encodeSourceListTokens_append
    (first second : List RawSource) :
    encodeSourceListTokens (first ++ second) =
      encodeSourceListTokens first ++
        encodeSourceListTokens second := by
  induction first with
  | nil =>
      rfl
  | cons source rest inductionHypothesis =>
      simp [encodeSourceListTokens,
        inductionHypothesis, List.append_assoc]

/-- Once the gate-producing phase has reached the exact candidate prefix, the
fixed output loop closes it to the independent raw builder's complete token
encoding. -/
theorem completeOutputResult_eq_rawLockedInstanceTokens
    (raw : RawCircuit) (runtime : Runtime)
    (prefixEq :
      runtime.targetTokens =
        [.version0] ++
          encodeNatTokens
            (RawBuilder.rawLockedInstance raw).candidate.inputCount ++
          encodeNatTokens
            (RawBuilder.rawLockedInstance raw).candidate.gates.length ++
          encodeNatTokens
            (RawBuilder.rawLockedInstance raw).candidate.outputs.length ++
          encodeGateListTokens
            (RawBuilder.rawLockedInstance raw).candidate.gates)
    (baseline :
      runtime.registers.baseline =
        (RawBuilder.rawLockedInstance raw).baseline) :
    (completeOutputResult runtime).targetTokens =
      encodeLockedInstanceTokens
        (RawBuilder.rawLockedInstance raw) := by
  rw [completeOutputResult_targetTokens, prefixEq, baseline]
  unfold encodeLockedInstanceTokens
  rw [RawBuilder.rawLockedInstance_outputs]
  rw [encodeSourceListTokens_append]
  simp [encodeSourceListTokens,
    List.append_assoc]

end PNP.Concrete.LockedNAND.TargetEmitterSemanticOutput

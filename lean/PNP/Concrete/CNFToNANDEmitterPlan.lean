/-
Copyright (c) 2026 PNP Labs.

Closed primitive blocks for a future physical compiler from canonical CNF
bytes to the strict version-zero NAND-circuit encoding.

This module deliberately stops below the grammar scanner and finite
controller.  It fixes the reusable output vocabulary, the interpretation of
the retained unary registers, and the exact primitive order for emitting
headers, sources, NAND gates, stack coordinates, and the circuit suffix.  No
definition decodes a formula or consults an external emission schedule.
-/

import PNP.Concrete.CNFToNAND
import PNP.Concrete.LockedNANDTargetEmitterPrimitiveCompiler
import PNP.Concrete.LockedNANDTargetEmitterProgramSemantics

namespace PNP.Concrete.CNFToNANDEmitterPlan

open PNP.Concrete.LockedNAND
open PNP.Concrete.LockedNAND.TargetEmitterPlan
open PNP.Concrete.LockedNAND.TargetEmitterProgramSemantics

abbrev Primitive :=
  PNP.Concrete.LockedNAND.TargetEmitterPlan.Primitive

abbrev CursorMode :=
  PNP.Concrete.LockedNAND.TargetEmitterPlan.CursorMode

abbrev Runtime :=
  PNP.Concrete.LockedNAND.TargetEmitterProgramSemantics.Runtime

local notation "programRun" =>
  PNP.Concrete.LockedNAND.TargetEmitterProgramSemantics.run

/-! ## Retained-coordinate contract

The future controller reuses the six-slot target-emitter ledger.  Only three
slots have a meaning at this boundary:

* `inputCount` is the decoded CNF assignment width;
* `currentGate` is repurposed as the exact number of emitted NAND gates and
  is also the stack sentinel (every real gate coordinate is strictly
  smaller);
* `outputIndex` is the controller's current gate coordinate.

`captured` holds the current in-range literal index.  `scratch` is the
transient natural used by emitters and stack pop.  The remaining retained
slots are reserved for later controller bookkeeping and are not consulted by
the blocks below.
-/

/-- Source-width coordinate retained in the `inputCount` slot. -/
def sourceWidth : NatExpression :=
  NatExpression.counter .inputCount

/-- Exact gate-count coordinate and distinguished stack sentinel. -/
def totalGateCount : NatExpression :=
  NatExpression.counter .currentGate

/-- Current controller gate coordinate retained in `outputIndex`. -/
def outputIndex : NatExpression :=
  NatExpression.counter .outputIndex

/-- Current valid literal index retained in the runtime capture field. -/
def capturedLiteralIndex : NatExpression :=
  NatExpression.counter .captured

/-- Coordinate most recently removed from the physical LIFO stack. -/
def poppedCoordinate : NatExpression :=
  NatExpression.counter .scratch

/-- A gate coordinate at a fixed forward bias from `outputIndex`. -/
def gateAt (bias : Nat) : NatExpression :=
  NatExpression.addOffset outputIndex bias

theorem sourceWidth_evaluated
    (runtime : Runtime) :
    sourceWidth.evaluate runtime.registers
        runtime.captured runtime.scratch =
      runtime.registers.inputCount := by
  exact NatExpression.evaluate_counter
    runtime.registers runtime.captured runtime.scratch
      .inputCount

theorem totalGateCount_evaluated
    (runtime : Runtime) :
    totalGateCount.evaluate runtime.registers
        runtime.captured runtime.scratch =
      runtime.registers.currentGate := by
  exact NatExpression.evaluate_counter
    runtime.registers runtime.captured runtime.scratch
      .currentGate

theorem outputIndex_evaluated
    (runtime : Runtime) :
    outputIndex.evaluate runtime.registers
        runtime.captured runtime.scratch =
      runtime.registers.outputIndex := by
  exact NatExpression.evaluate_counter
    runtime.registers runtime.captured runtime.scratch
      .outputIndex

theorem capturedLiteralIndex_evaluated
    (runtime : Runtime) :
    capturedLiteralIndex.evaluate runtime.registers
        runtime.captured runtime.scratch =
      runtime.captured := by
  exact NatExpression.evaluate_counter
    runtime.registers runtime.captured runtime.scratch
      .captured

theorem poppedCoordinate_evaluated
    (runtime : Runtime) :
    poppedCoordinate.evaluate runtime.registers
        runtime.captured runtime.scratch =
      runtime.scratch := by
  exact NatExpression.evaluate_counter
    runtime.registers runtime.captured runtime.scratch
      .scratch

theorem gateAt_evaluated
    (runtime : Runtime) (bias : Nat) :
    (gateAt bias).evaluate runtime.registers
        runtime.captured runtime.scratch =
      runtime.registers.outputIndex + bias := by
  simp [gateAt, outputIndex, NatExpression.evaluate,
    NatExpression.addOffset, NatExpression.counter,
    NatExpression.evaluateCounter]
  omega

/-! ## Closed natural emitters -/

inductive RetainedCoordinate where
  | sourceWidth
  | totalGateCount
deriving BEq, DecidableEq, Repr

namespace RetainedCoordinate

def counter : RetainedCoordinate → Counter
  | .sourceWidth => .inputCount
  | .totalGateCount => .currentGate

def value (coordinate : RetainedCoordinate)
    (runtime : Runtime) : Nat :=
  match coordinate with
  | .sourceWidth => runtime.registers.inputCount
  | .totalGateCount =>
      runtime.registers.currentGate

end RetainedCoordinate

/-- Emit the unary encoding of one retained header coordinate. -/
def emitRetainedNatProgram (mode : CursorMode)
    (coordinate : RetainedCoordinate) : List Primitive :=
  [ .resetScratch
  , .addRegister coordinate.counter
  , .emitScratchNat mode
  ]

/-- Emit the unary encoding of the current captured literal index. -/
def emitCapturedNatProgram (mode : CursorMode) : List Primitive :=
  [ .resetScratch
  , .reloadCaptured
  , .emitScratchNat mode
  ]

/-- Emit the unary encoding already held in scratch, without changing it. -/
def emitScratchNatProgram (mode : CursorMode) : List Primitive :=
  [.emitScratchNat mode]

/-- Compute `outputIndex + bias` in scratch without emitting it. -/
def computeGateAtProgram (bias : Nat) : List Primitive :=
  [.resetScratch, .addRegister .outputIndex] ++
    repeatPrimitive bias .incrementScratch

/-- Emit the unary encoding of `outputIndex + bias`. -/
def emitGateAtNatProgram (mode : CursorMode)
    (bias : Nat) : List Primitive :=
  computeGateAtProgram bias ++ [.emitScratchNat mode]

def emittedNatResult (runtime : Runtime) (value : Nat) : Runtime :=
  { runtime with
    scratch := value
    targetTokens :=
      runtime.targetTokens ++ encodeNatTokens value }

theorem emitRetainedNatProgram_correct
    (mode : CursorMode) (coordinate : RetainedCoordinate)
    (runtime : Runtime) :
    programRun (emitRetainedNatProgram mode coordinate) runtime =
      some (.accepted
        (emittedNatResult runtime (coordinate.value runtime))) := by
  cases coordinate <;>
    simp [emitRetainedNatProgram, emittedNatResult,
      RetainedCoordinate.counter, RetainedCoordinate.value,
      TargetEmitterProgramSemantics.run,
      step, addCounter, registerValue]

theorem emitCapturedNatProgram_correct
    (mode : CursorMode) (runtime : Runtime) :
    programRun (emitCapturedNatProgram mode) runtime =
      some (.accepted
        (emittedNatResult runtime runtime.captured)) := by
  simp [emitCapturedNatProgram, emittedNatResult,
    TargetEmitterProgramSemantics.run, step]

theorem emitScratchNatProgram_correct
    (mode : CursorMode) (runtime : Runtime) :
    programRun (emitScratchNatProgram mode) runtime =
      some (.accepted
        (emittedNatResult runtime runtime.scratch)) := by
  simp [emitScratchNatProgram, emittedNatResult,
    TargetEmitterProgramSemantics.run, step]

theorem computeGateAtProgram_correct
    (bias : Nat) (runtime : Runtime) :
    programRun (computeGateAtProgram bias) runtime =
      some (.accepted
        { runtime with
          scratch := runtime.registers.outputIndex + bias }) := by
  let prepared : Runtime :=
    { runtime with
      scratch := runtime.registers.outputIndex }
  have prepare :
      programRun [.resetScratch, .addRegister .outputIndex] runtime =
        some (.accepted prepared) := by
    simp [prepared, TargetEmitterProgramSemantics.run,
      step, addCounter, registerValue]
  rw [computeGateAtProgram, run_append_of_accepted
    [.resetScratch, .addRegister .outputIndex]
    (repeatPrimitive bias .incrementScratch)
    runtime prepared prepare]
  simpa [prepared, Nat.add_assoc] using
    run_repeat_incrementScratch bias prepared

theorem emitGateAtNatProgram_correct
    (mode : CursorMode) (bias : Nat) (runtime : Runtime) :
    programRun (emitGateAtNatProgram mode bias) runtime =
      some (.accepted
        (emittedNatResult runtime
          (runtime.registers.outputIndex + bias))) := by
  let computed : Runtime :=
    { runtime with
      scratch := runtime.registers.outputIndex + bias }
  have computation :
      programRun (computeGateAtProgram bias) runtime =
        some (.accepted computed) := by
    simpa [computed] using
      computeGateAtProgram_correct bias runtime
  rw [emitGateAtNatProgram,
    run_append_of_accepted
      (computeGateAtProgram bias)
      [.emitScratchNat mode] runtime computed computation]
  simp [computed, emittedNatResult,
    TargetEmitterProgramSemantics.run, step]

/-! ## Exact source and gate fragments -/

/-- Source forms required by the direct CNF compiler.

`gateScratch` is the popped stack coordinate.  It is deliberately emitted
directly because the generic addition-only expression compiler resets
scratch before evaluating an expression.
-/
inductive EmissionSource where
  | constant (value : Bool)
  | inputCaptured
  | inputScratch
  | gateScratch
  | gateAt (bias : Nat)
deriving BEq, DecidableEq, Repr

namespace EmissionSource

def evaluate (source : EmissionSource)
    (runtime : Runtime) : RawSource :=
  match source with
  | .constant value => .constant value
  | .inputCaptured => .input runtime.captured
  | .inputScratch => .input runtime.scratch
  | .gateScratch => .gate runtime.scratch
  | .gateAt bias =>
      .gate (runtime.registers.outputIndex + bias)

def finalScratch (source : EmissionSource)
    (runtime : Runtime) : Nat :=
  match source with
  | .constant _ => runtime.scratch
  | .inputCaptured => runtime.captured
  | .inputScratch => runtime.scratch
  | .gateScratch => runtime.scratch
  | .gateAt bias =>
      runtime.registers.outputIndex + bias

end EmissionSource

def emitSourceProgram (mode : CursorMode) :
    EmissionSource → List Primitive
  | .constant false => [.append mode .constantFalse]
  | .constant true => [.append mode .constantTrue]
  | .inputCaptured =>
      .append mode .input :: emitCapturedNatProgram mode
  | .inputScratch =>
      .append mode .input :: emitScratchNatProgram mode
  | .gateScratch =>
      .append mode .gate :: emitScratchNatProgram mode
  | .gateAt bias =>
      .append mode .gate :: emitGateAtNatProgram mode bias

def emitSourceResult
    (runtime : Runtime) (source : EmissionSource) : Runtime :=
  { runtime with
    scratch := source.finalScratch runtime
    targetTokens :=
      runtime.targetTokens ++
        encodeSourceTokens (source.evaluate runtime) }

theorem emitSourceProgram_correct
    (mode : CursorMode) (source : EmissionSource)
    (runtime : Runtime) :
    programRun (emitSourceProgram mode source) runtime =
      some (.accepted (emitSourceResult runtime source)) := by
  cases source with
  | constant value =>
      cases value <;> rfl
  | inputCaptured =>
      simp only [emitSourceProgram,
        TargetEmitterProgramSemantics.run, step]
      simpa [emitSourceResult, EmissionSource.finalScratch,
        EmissionSource.evaluate, emittedNatResult,
        encodeSourceTokens, List.append_assoc] using
        emitCapturedNatProgram_correct mode
          { runtime with
            targetTokens :=
              runtime.targetTokens ++ [.input] }
  | inputScratch =>
      simp [emitSourceProgram, emitScratchNatProgram,
        emitSourceResult, EmissionSource.finalScratch,
        EmissionSource.evaluate, encodeSourceTokens,
        TargetEmitterProgramSemantics.run,
        step, List.append_assoc]
  | gateScratch =>
      simp [emitSourceProgram, emitScratchNatProgram,
        emitSourceResult, EmissionSource.finalScratch,
        EmissionSource.evaluate, encodeSourceTokens,
        TargetEmitterProgramSemantics.run,
        step, List.append_assoc]
  | gateAt bias =>
      simp only [emitSourceProgram,
        TargetEmitterProgramSemantics.run, step]
      simpa [emitSourceResult, EmissionSource.finalScratch,
        EmissionSource.evaluate, emittedNatResult,
        encodeSourceTokens, List.append_assoc] using
        emitGateAtNatProgram_correct mode bias
          { runtime with
            targetTokens :=
              runtime.targetTokens ++ [.gate] }

theorem EmissionSource.evaluate_after_emit
    (source : EmissionSource) (runtime : Runtime) :
    source.evaluate (emitSourceResult runtime source) =
      source.evaluate runtime := by
  cases source <;> rfl

def emitGateProgram (mode : CursorMode)
    (left right : EmissionSource) : List Primitive :=
  emitSourceProgram mode left ++
    emitSourceProgram mode right ++
    [.append mode .gateEnd]

def emitGateResult (runtime : Runtime)
    (left right : EmissionSource) : Runtime :=
  let afterLeft := emitSourceResult runtime left
  let afterRight := emitSourceResult afterLeft right
  { afterRight with
    targetTokens := afterRight.targetTokens ++ [.gateEnd] }

theorem emitGateProgram_correct
    (mode : CursorMode) (left right : EmissionSource)
    (runtime : Runtime) :
    programRun (emitGateProgram mode left right) runtime =
      some (.accepted (emitGateResult runtime left right)) := by
  let afterLeft := emitSourceResult runtime left
  let afterRight := emitSourceResult afterLeft right
  have leftRun :
      programRun (emitSourceProgram mode left) runtime =
        some (.accepted afterLeft) := by
    simpa [afterLeft] using
      emitSourceProgram_correct mode left runtime
  have rightRun :
      programRun (emitSourceProgram mode right) afterLeft =
        some (.accepted afterRight) := by
    simpa [afterRight] using
      emitSourceProgram_correct mode right afterLeft
  simp only [emitGateProgram, List.append_assoc]
  calc
    programRun
        (emitSourceProgram mode left ++
          (emitSourceProgram mode right ++
            [.append mode .gateEnd]))
        runtime =
      programRun
        (emitSourceProgram mode right ++
          [.append mode .gateEnd])
        afterLeft :=
      run_append_of_accepted _ _ runtime
        afterLeft leftRun
    _ =
      programRun [.append mode .gateEnd]
        afterRight :=
      run_append_of_accepted _ _ afterLeft
        afterRight rightRun
    _ = some (.accepted
        (emitGateResult runtime left right)) := by
      simp [emitGateResult, afterLeft, afterRight,
        TargetEmitterProgramSemantics.run, step]

theorem emitGateResult_targetTokens
    (runtime : Runtime) (left right : EmissionSource) :
    (emitGateResult runtime left right).targetTokens =
      runtime.targetTokens ++
        encodeGateTokens
          { left := left.evaluate runtime
            right :=
              right.evaluate
                (emitSourceResult runtime left) } := by
  simp [emitGateResult, emitSourceResult,
    encodeGateTokens, List.append_assoc]

def emitSelfNANDProgram (mode : CursorMode)
    (source : EmissionSource) : List Primitive :=
  emitGateProgram mode source source

theorem emitSelfNANDProgram_correct
    (mode : CursorMode) (source : EmissionSource)
    (runtime : Runtime) :
    programRun (emitSelfNANDProgram mode source) runtime =
      some (.accepted
        (emitGateResult runtime source source)) := by
  exact emitGateProgram_correct mode source source runtime

theorem emitSelfNANDResult_targetTokens
    (runtime : Runtime) (source : EmissionSource) :
    (emitGateResult runtime source source).targetTokens =
      runtime.targetTokens ++
        encodeGateTokens
          { left := source.evaluate runtime
            right := source.evaluate runtime } := by
  rw [emitGateResult_targetTokens,
    EmissionSource.evaluate_after_emit]

/-! ## Gate-coordinate advancement -/

def advanceOutputIndexProgram (count : Nat) : List Primitive :=
  repeatPrimitive count
    (.incrementRegister .outputIndex)

def advanceOutputIndexResult
    (runtime : Runtime) (count : Nat) : Runtime :=
  { runtime with
    registers :=
      { runtime.registers with
        outputIndex :=
          runtime.registers.outputIndex + count } }

theorem advanceOutputIndexProgram_correct
    (count : Nat) (runtime : Runtime) :
    programRun (advanceOutputIndexProgram count) runtime =
      some (.accepted
        (advanceOutputIndexResult runtime count)) := by
  simpa [advanceOutputIndexProgram,
    advanceOutputIndexResult] using
    run_repeat_incrementOutputIndex count runtime

/-- Emit one NAND gate and advance the next-gate coordinate once. -/
def emitGateAndAdvanceProgram (mode : CursorMode)
    (left right : EmissionSource) : List Primitive :=
  emitGateProgram mode left right ++
    advanceOutputIndexProgram 1

def emitGateAndAdvanceResult
    (runtime : Runtime) (left right : EmissionSource) : Runtime :=
  advanceOutputIndexResult
    (emitGateResult runtime left right) 1

theorem emitGateAndAdvanceProgram_correct
    (mode : CursorMode) (left right : EmissionSource)
    (runtime : Runtime) :
    programRun (emitGateAndAdvanceProgram mode left right) runtime =
      some (.accepted
        (emitGateAndAdvanceResult runtime left right)) := by
  rw [emitGateAndAdvanceProgram,
    run_append_of_accepted
      (emitGateProgram mode left right)
      (advanceOutputIndexProgram 1)
      runtime (emitGateResult runtime left right)
      (emitGateProgram_correct mode left right runtime)]
  exact advanceOutputIndexProgram_correct 1
    (emitGateResult runtime left right)

/-- Emit one self-NAND gate and advance the next-gate coordinate once. -/
def emitSelfNANDAndAdvanceProgram (mode : CursorMode)
    (source : EmissionSource) : List Primitive :=
  emitGateAndAdvanceProgram mode source source

theorem emitSelfNANDAndAdvanceProgram_correct
    (mode : CursorMode) (source : EmissionSource)
    (runtime : Runtime) :
    programRun (emitSelfNANDAndAdvanceProgram mode source) runtime =
      some (.accepted
        (emitGateAndAdvanceResult runtime source source)) := by
  exact emitGateAndAdvanceProgram_correct
    mode source source runtime

/-! ## Stack-coordinate helpers -/

/-- Push the carrier-width coordinate as the formula-stack marker and restore
zero scratch.  The workspace proof establishes that every compiler gate
coordinate and the empty-clause sentinel are strictly below this marker. -/
def pushFormulaMarkerProgram : List Primitive :=
  [ .resetScratch
  , .addRegister .carrierWidth
  , .pushCheck
  , .resetScratch
  ]

/-- Push the exact total-gate sentinel and restore zero scratch. -/
def pushTotalGateSentinelProgram : List Primitive :=
  [ .resetScratch
  , .addRegister .currentGate
  , .pushCheck
  , .resetScratch
  ]

/-- Compute and push `outputIndex + bias`, then restore zero scratch. -/
def pushGateAtProgram (bias : Nat) : List Primitive :=
  computeGateAtProgram bias ++
    [.pushCheck, .resetScratch]

/-- Clear scratch and remove the newest coordinate.

The pop primitive rejects when the stack is empty; that ordinary reject
endpoint is the fixed controller's branch condition.
-/
def popCoordinateProgram : List Primitive :=
  [.resetScratch, .popCheck]

theorem pushFormulaMarkerProgram_correct
    (runtime : Runtime) :
    programRun pushFormulaMarkerProgram runtime =
      some (.accepted
        { runtime with
          scratch := 0
          checks :=
            runtime.checks ++
              [runtime.registers.carrierWidth] }) := by
  simp [pushFormulaMarkerProgram,
    TargetEmitterProgramSemantics.run, step,
    addCounter, registerValue]

theorem pushTotalGateSentinelProgram_correct
    (runtime : Runtime) :
    programRun pushTotalGateSentinelProgram runtime =
      some (.accepted
        { runtime with
          scratch := 0
          checks :=
            runtime.checks ++
              [runtime.registers.currentGate] }) := by
  simp [pushTotalGateSentinelProgram,
    TargetEmitterProgramSemantics.run, step,
    addCounter, registerValue]

theorem pushGateAtProgram_correct
    (bias : Nat) (runtime : Runtime) :
    programRun (pushGateAtProgram bias) runtime =
      some (.accepted
        { runtime with
          scratch := 0
          checks :=
            runtime.checks ++
              [runtime.registers.outputIndex + bias] }) := by
  let computed : Runtime :=
    { runtime with
      scratch := runtime.registers.outputIndex + bias }
  have computation :
      programRun (computeGateAtProgram bias) runtime =
        some (.accepted computed) := by
    simpa [computed] using
      computeGateAtProgram_correct bias runtime
  rw [pushGateAtProgram,
    run_append_of_accepted
      (computeGateAtProgram bias)
      [.pushCheck, .resetScratch]
      runtime computed computation]
  simp [computed, TargetEmitterProgramSemantics.run, step]

theorem popCoordinateProgram_nonempty_correct
    (runtime : Runtime) (prior : List Nat) (value : Nat)
    (checks : runtime.checks = prior ++ [value]) :
    programRun popCoordinateProgram runtime =
      some (.accepted
        { runtime with
          scratch := value
          checks := prior }) := by
  simp [popCoordinateProgram,
    TargetEmitterProgramSemantics.run, step, checks,
    popNewest_append_singleton]

theorem popCoordinateProgram_empty_rejects
    (runtime : Runtime)
    (checks : runtime.checks = []) :
    programRun popCoordinateProgram runtime =
      some (.rejected { runtime with scratch := 0 }) := by
  simp [popCoordinateProgram,
    TargetEmitterProgramSemantics.run, step, checks,
    popNewest]

/-! ## Exact strict-v0 circuit framing -/

/-- Exact circuit header: version, input width, and total gate count. -/
def circuitHeaderProgram (mode : CursorMode) : List Primitive :=
  [.append mode .version0] ++
    emitRetainedNatProgram mode .sourceWidth ++
    emitRetainedNatProgram mode .totalGateCount

def circuitHeaderResult (runtime : Runtime) : Runtime :=
  { runtime with
    scratch := runtime.registers.currentGate
    targetTokens :=
      runtime.targetTokens ++ [.version0] ++
        encodeNatTokens runtime.registers.inputCount ++
        encodeNatTokens
          runtime.registers.currentGate }

theorem circuitHeaderProgram_correct
    (mode : CursorMode) (runtime : Runtime) :
    programRun (circuitHeaderProgram mode) runtime =
      some (.accepted (circuitHeaderResult runtime)) := by
  let afterVersion : Runtime :=
    { runtime with
      targetTokens :=
        runtime.targetTokens ++ [.version0] }
  let afterWidth :=
    emittedNatResult afterVersion
      runtime.registers.inputCount
  have versionRun :
      programRun [.append mode .version0] runtime =
        some (.accepted afterVersion) := by
    simp [afterVersion,
      TargetEmitterProgramSemantics.run, step]
  have widthRun :
      programRun
          (emitRetainedNatProgram mode
            .sourceWidth)
          afterVersion =
        some (.accepted afterWidth) := by
    simpa [afterWidth, afterVersion,
      RetainedCoordinate.value] using
      emitRetainedNatProgram_correct mode
        .sourceWidth afterVersion
  have gateRun :
      programRun
          (emitRetainedNatProgram mode
            .totalGateCount)
          afterWidth =
        some (.accepted
          (emittedNatResult afterWidth
            runtime.registers.currentGate)) := by
    simpa [afterWidth, afterVersion,
      emittedNatResult, RetainedCoordinate.value] using
      emitRetainedNatProgram_correct mode
        .totalGateCount afterWidth
  simp only [circuitHeaderProgram, List.append_assoc]
  calc
    programRun
        ([.append mode .version0] ++
          (emitRetainedNatProgram mode .sourceWidth ++
            emitRetainedNatProgram mode .totalGateCount))
        runtime =
      programRun
        (emitRetainedNatProgram mode .sourceWidth ++
          emitRetainedNatProgram mode .totalGateCount)
        afterVersion :=
      run_append_of_accepted _ _ runtime
        afterVersion versionRun
    _ =
      programRun
        (emitRetainedNatProgram mode .totalGateCount)
        afterWidth :=
      run_append_of_accepted _ _ afterVersion
        afterWidth widthRun
    _ = some (.accepted (circuitHeaderResult runtime)) := by
      simpa [circuitHeaderResult, emittedNatResult,
        afterWidth, afterVersion, List.append_assoc] using
        gateRun

/-- Exact circuit suffix at a runtime whose `outputIndex` is the final gate. -/
def circuitSuffixProgram (mode : CursorMode) : List Primitive :=
  [.append mode .programEnd] ++
    emitSourceProgram mode (.gateAt 0) ++
    [ .append mode .outputsEnd
    , .append mode .instanceEnd
    ]

def circuitSuffixResult (runtime : Runtime) : Runtime :=
  { runtime with
    scratch := runtime.registers.outputIndex
    targetTokens :=
      runtime.targetTokens ++ [.programEnd] ++
        encodeSourceTokens
          (.gate runtime.registers.outputIndex) ++
        [.outputsEnd, .instanceEnd] }

theorem circuitSuffixProgram_correct
    (mode : CursorMode) (runtime : Runtime) :
    programRun (circuitSuffixProgram mode) runtime =
      some (.accepted (circuitSuffixResult runtime)) := by
  let afterProgram : Runtime :=
    { runtime with
      targetTokens :=
        runtime.targetTokens ++ [.programEnd] }
  let afterOutput :=
    emitSourceResult afterProgram (.gateAt 0)
  have programTokenRun :
      programRun [.append mode .programEnd] runtime =
        some (.accepted afterProgram) := by
    simp [afterProgram,
      TargetEmitterProgramSemantics.run, step]
  have outputRun :
      programRun (emitSourceProgram mode (.gateAt 0))
          afterProgram =
        some (.accepted afterOutput) := by
    simpa [afterOutput] using
      emitSourceProgram_correct mode (.gateAt 0)
        afterProgram
  simp only [circuitSuffixProgram, List.append_assoc]
  calc
    programRun
        ([.append mode .programEnd] ++
          (emitSourceProgram mode (.gateAt 0) ++
            [.append mode .outputsEnd,
              .append mode .instanceEnd]))
        runtime =
      programRun
        (emitSourceProgram mode (.gateAt 0) ++
          [.append mode .outputsEnd,
            .append mode .instanceEnd])
        afterProgram :=
      run_append_of_accepted _ _ runtime
        afterProgram programTokenRun
    _ =
      programRun
        [.append mode .outputsEnd,
          .append mode .instanceEnd]
        afterOutput :=
      run_append_of_accepted _ _ afterProgram
        afterOutput outputRun
    _ = some (.accepted (circuitSuffixResult runtime)) := by
      simp [afterOutput, afterProgram, emitSourceResult,
        EmissionSource.finalScratch,
        EmissionSource.evaluate,
        circuitSuffixResult, encodeSourceTokens,
        TargetEmitterProgramSemantics.run,
        step, List.append_assoc]

/-! ## Literal-machine closure

`MachineClosed` states that the primitive compiler materializes a literal
finite list of work machines.  These proofs are independent of every future
scanner state, runtime invariant, and controller branch.
-/

def MachineClosed (program : List Primitive) : Prop :=
  ∃ machines,
    PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.compileProgram
        program =
      some machines

private theorem primitiveClosed_append
    (mode : CursorMode) (token : Token) :
    ∃ machine,
      PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.primitiveMachine
          (.append mode token) =
        some machine := by
  cases mode <;> exact ⟨_, rfl⟩

private theorem primitiveClosed_reset :
    ∃ machine,
      PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.primitiveMachine
          .resetScratch =
        some machine :=
  ⟨_, rfl⟩

private theorem primitiveClosed_add
    (coordinate : RetainedCoordinate) :
    ∃ machine,
      PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.primitiveMachine
          (.addRegister coordinate.counter) =
        some machine := by
  cases coordinate <;> exact ⟨_, rfl⟩

private theorem primitiveClosed_addOutput :
    ∃ machine,
      PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.primitiveMachine
          (.addRegister .outputIndex) =
        some machine :=
  ⟨_, rfl⟩

private theorem primitiveClosed_reload :
    ∃ machine,
      PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.primitiveMachine
          .reloadCaptured =
        some machine :=
  ⟨_, rfl⟩

private theorem primitiveClosed_incrementScratch :
    ∃ machine,
      PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.primitiveMachine
          .incrementScratch =
        some machine :=
  ⟨_, rfl⟩

private theorem primitiveClosed_emit
    (mode : CursorMode) :
    ∃ machine,
      PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.primitiveMachine
          (.emitScratchNat mode) =
        some machine := by
  cases mode <;> exact ⟨_, rfl⟩

private theorem primitiveClosed_push :
    ∃ machine,
      PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.primitiveMachine
          .pushCheck =
        some machine :=
  ⟨_, rfl⟩

private theorem primitiveClosed_pop :
    ∃ machine,
      PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.primitiveMachine
          .popCheck =
        some machine :=
  ⟨_, rfl⟩

private theorem primitiveClosed_incrementOutput :
    ∃ machine,
      PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.primitiveMachine
          (.incrementRegister .outputIndex) =
        some machine :=
  ⟨_, rfl⟩

private theorem MachineClosed.nil :
    MachineClosed [] :=
  ⟨[], rfl⟩

private theorem MachineClosed.cons
    {primitive : Primitive} {rest : List Primitive}
    (head :
      ∃ machine,
        PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.primitiveMachine
            primitive =
          some machine)
    (tail : MachineClosed rest) :
    MachineClosed (primitive :: rest) := by
  rcases head with ⟨machine, headEq⟩
  rcases tail with ⟨machines, tailEq⟩
  refine ⟨machine :: machines, ?_⟩
  simp [PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.compileProgram,
    headEq, tailEq]

private theorem MachineClosed.append
    {first second : List Primitive}
    (firstClosed : MachineClosed first)
    (secondClosed : MachineClosed second) :
    MachineClosed (first ++ second) := by
  rcases firstClosed with ⟨firstMachines, firstEq⟩
  rcases secondClosed with ⟨secondMachines, secondEq⟩
  exact
    ⟨firstMachines ++ secondMachines,
      PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.compileProgram_append
        first second firstMachines secondMachines
        firstEq secondEq⟩

private theorem repeatIncrementScratch_closed
    (count : Nat) :
    MachineClosed
      (repeatPrimitive count .incrementScratch) := by
  induction count with
  | zero =>
      exact MachineClosed.nil
  | succ count inductionHypothesis =>
      rw [repeatPrimitive, List.replicate_succ]
      exact MachineClosed.cons
        primitiveClosed_incrementScratch
        inductionHypothesis

private theorem repeatIncrementOutput_closed
    (count : Nat) :
    MachineClosed
      (advanceOutputIndexProgram count) := by
  induction count with
  | zero =>
      exact MachineClosed.nil
  | succ count inductionHypothesis =>
      rw [advanceOutputIndexProgram, repeatPrimitive,
        List.replicate_succ]
      exact MachineClosed.cons
        primitiveClosed_incrementOutput
        inductionHypothesis

theorem emitRetainedNatProgram_closed
    (mode : CursorMode) (coordinate : RetainedCoordinate) :
    MachineClosed (emitRetainedNatProgram mode coordinate) := by
  unfold emitRetainedNatProgram
  exact MachineClosed.cons primitiveClosed_reset <|
    MachineClosed.cons (primitiveClosed_add coordinate) <|
      MachineClosed.cons (primitiveClosed_emit mode)
        MachineClosed.nil

theorem emitCapturedNatProgram_closed
    (mode : CursorMode) :
    MachineClosed (emitCapturedNatProgram mode) := by
  unfold emitCapturedNatProgram
  exact MachineClosed.cons primitiveClosed_reset <|
    MachineClosed.cons primitiveClosed_reload <|
      MachineClosed.cons (primitiveClosed_emit mode)
        MachineClosed.nil

theorem emitScratchNatProgram_closed
    (mode : CursorMode) :
    MachineClosed (emitScratchNatProgram mode) := by
  exact MachineClosed.cons (primitiveClosed_emit mode)
    MachineClosed.nil

theorem computeGateAtProgram_closed
    (bias : Nat) :
    MachineClosed (computeGateAtProgram bias) := by
  unfold computeGateAtProgram
  apply MachineClosed.append
  · exact MachineClosed.cons primitiveClosed_reset <|
      MachineClosed.cons primitiveClosed_addOutput
        MachineClosed.nil
  · exact repeatIncrementScratch_closed bias

theorem emitGateAtNatProgram_closed
    (mode : CursorMode) (bias : Nat) :
    MachineClosed (emitGateAtNatProgram mode bias) := by
  unfold emitGateAtNatProgram
  exact MachineClosed.append
    (computeGateAtProgram_closed bias)
    (MachineClosed.cons (primitiveClosed_emit mode)
      MachineClosed.nil)

theorem emitSourceProgram_closed
    (mode : CursorMode) (source : EmissionSource) :
    MachineClosed (emitSourceProgram mode source) := by
  cases source with
  | constant value =>
      cases value <;>
        exact MachineClosed.cons
          (primitiveClosed_append mode _)
          MachineClosed.nil
  | inputCaptured =>
      exact MachineClosed.cons
        (primitiveClosed_append mode .input)
        (emitCapturedNatProgram_closed mode)
  | inputScratch =>
      exact MachineClosed.cons
        (primitiveClosed_append mode .input)
        (emitScratchNatProgram_closed mode)
  | gateScratch =>
      exact MachineClosed.cons
        (primitiveClosed_append mode .gate)
        (emitScratchNatProgram_closed mode)
  | gateAt bias =>
      exact MachineClosed.cons
        (primitiveClosed_append mode .gate)
        (emitGateAtNatProgram_closed mode bias)

theorem emitGateProgram_closed
    (mode : CursorMode) (left right : EmissionSource) :
    MachineClosed (emitGateProgram mode left right) := by
  unfold emitGateProgram
  exact MachineClosed.append
    (MachineClosed.append
      (emitSourceProgram_closed mode left)
      (emitSourceProgram_closed mode right))
    (MachineClosed.cons
      (primitiveClosed_append mode .gateEnd)
      MachineClosed.nil)

theorem emitSelfNANDProgram_closed
    (mode : CursorMode) (source : EmissionSource) :
    MachineClosed (emitSelfNANDProgram mode source) :=
  emitGateProgram_closed mode source source

theorem advanceOutputIndexProgram_closed
    (count : Nat) :
    MachineClosed (advanceOutputIndexProgram count) :=
  repeatIncrementOutput_closed count

theorem emitGateAndAdvanceProgram_closed
    (mode : CursorMode) (left right : EmissionSource) :
    MachineClosed
      (emitGateAndAdvanceProgram mode left right) := by
  unfold emitGateAndAdvanceProgram
  exact MachineClosed.append
    (emitGateProgram_closed mode left right)
    (advanceOutputIndexProgram_closed 1)

theorem emitSelfNANDAndAdvanceProgram_closed
    (mode : CursorMode) (source : EmissionSource) :
    MachineClosed
      (emitSelfNANDAndAdvanceProgram mode source) :=
  emitGateAndAdvanceProgram_closed mode source source

theorem pushTotalGateSentinelProgram_closed :
    MachineClosed pushTotalGateSentinelProgram := by
  unfold pushTotalGateSentinelProgram
  exact MachineClosed.cons primitiveClosed_reset <|
    MachineClosed.cons
      (primitiveClosed_add .totalGateCount) <|
      MachineClosed.cons primitiveClosed_push <|
        MachineClosed.cons primitiveClosed_reset
          MachineClosed.nil

theorem pushFormulaMarkerProgram_closed :
    MachineClosed pushFormulaMarkerProgram := by
  unfold pushFormulaMarkerProgram
  exact MachineClosed.cons primitiveClosed_reset <|
    MachineClosed.cons
      (show
        ∃ machine,
          PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.primitiveMachine
              (.addRegister .carrierWidth) =
            some machine from ⟨_, rfl⟩) <|
      MachineClosed.cons primitiveClosed_push <|
        MachineClosed.cons primitiveClosed_reset
          MachineClosed.nil

theorem pushGateAtProgram_closed
    (bias : Nat) :
    MachineClosed (pushGateAtProgram bias) := by
  unfold pushGateAtProgram
  exact MachineClosed.append
    (computeGateAtProgram_closed bias)
    (MachineClosed.cons primitiveClosed_push <|
      MachineClosed.cons primitiveClosed_reset
        MachineClosed.nil)

theorem popCoordinateProgram_closed :
    MachineClosed popCoordinateProgram := by
  exact MachineClosed.cons primitiveClosed_reset <|
    MachineClosed.cons primitiveClosed_pop
      MachineClosed.nil

theorem circuitHeaderProgram_closed
    (mode : CursorMode) :
    MachineClosed (circuitHeaderProgram mode) := by
  unfold circuitHeaderProgram
  exact MachineClosed.append
    (MachineClosed.append
      (MachineClosed.cons
        (primitiveClosed_append mode .version0)
        MachineClosed.nil)
      (emitRetainedNatProgram_closed mode .sourceWidth))
    (emitRetainedNatProgram_closed mode .totalGateCount)

theorem circuitSuffixProgram_closed
    (mode : CursorMode) :
    MachineClosed (circuitSuffixProgram mode) := by
  unfold circuitSuffixProgram
  exact MachineClosed.append
    (MachineClosed.append
      (MachineClosed.cons
        (primitiveClosed_append mode .programEnd)
        MachineClosed.nil)
      (emitSourceProgram_closed mode (.gateAt 0)))
    (MachineClosed.cons
      (primitiveClosed_append mode .outputsEnd) <|
      MachineClosed.cons
        (primitiveClosed_append mode .instanceEnd)
        MachineClosed.nil)

end PNP.Concrete.CNFToNANDEmitterPlan

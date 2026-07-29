/-
Copyright (c) 2026 PNP Labs.

Constructive work bounds for exact locked-NAND target-emitter programs.

The bound is derived from the literal primitive traces.  Its inputs are only
the physical capacity, retained-source length, initial logical target and
check-stack sizes, and the closed primitive-list length.  In particular, it
contains no decoded circuit, host-side schedule, or caller-supplied trace
certificate.
-/

import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgram

namespace PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramBound

open PNP.Concrete
open TargetEmitterPlan
open TargetEmitterPrimitiveCompiler
open TargetEmitterBlockCompiler
open TargetEmitterProgramSemantics
open TargetEmitterRuntimeProgram

abbrev Slot := TargetEmitterLedger.Slot

/-- Physical check-record payload occupied by a logical stack. -/
def checkCells (checks : List Nat) : Nat :=
  (TargetEmitterCheckStack.recordsWord checks).length

/-- A monotone size which dominates every variable tape scan during one
closed primitive program.  The final summand pays in advance for every token
or stack cell that any of the remaining primitives can add. -/
def runtimeFootprint (capacity : Nat) (source : List WorkSymbol)
    (initial : Runtime) (programLength : Nat) : Nat :=
  capacity + source.length +
    2 * initial.targetTokens.length +
    checkCells initial.checks +
    programLength * (3 * capacity + 3) + 1

/-- Uniform quadratic envelope for one literal primitive trace. -/
def primitiveWorkEnvelope (size : Nat) : Nat :=
  100 * (size * size) + 100

/-- Current-runtime specialization used by the one-primitive theorem. -/
def localSize (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime) : Nat :=
  runtimeFootprint capacity source runtime 0

/-- Exact controller work envelope, including the materialized bridge after
each primitive used by `LinearAcceptRuns`. -/
def programWorkEnvelope (capacity : Nat) (source : List WorkSymbol)
    (initial : Runtime) (primitives : List Primitive) : Nat :=
  primitives.length *
    (primitiveWorkEnvelope
      (runtimeFootprint capacity source initial primitives.length) + 1)

private theorem checkCells_push (checks : List Nat) (value : Nat) :
    checkCells (checks ++ [value]) =
      checkCells checks + value + 1 := by
  rw [checkCells, checkCells,
    TargetEmitterCheckStack.recordsWord_push, List.length_append,
    TargetEmitterCheckStack.recordWord_length]
  omega

private theorem checkCells_prior_le
    (prior : List Nat) (value : Nat) :
    checkCells prior ≤ checkCells (prior ++ [value]) := by
  rw [checkCells_push]
  omega

private theorem localSize_positive (capacity : Nat)
    (source : List WorkSymbol) (runtime : Runtime) :
    1 ≤ localSize capacity source runtime := by
  unfold localSize runtimeFootprint
  omega

private theorem localSize_le_square (capacity : Nat)
    (source : List WorkSymbol) (runtime : Runtime) :
    localSize capacity source runtime ≤
      localSize capacity source runtime *
        localSize capacity source runtime := by
  have multiplied :=
    Nat.mul_le_mul_left
      (localSize capacity source runtime)
      (localSize_positive capacity source runtime)
  simpa using multiplied

private theorem capacity_le_localSize (capacity : Nat)
    (source : List WorkSymbol) (runtime : Runtime) :
    capacity ≤ localSize capacity source runtime := by
  unfold localSize runtimeFootprint
  omega

private theorem sourceLength_le_localSize (capacity : Nat)
    (source : List WorkSymbol) (runtime : Runtime) :
    source.length ≤ localSize capacity source runtime := by
  unfold localSize runtimeFootprint
  omega

private theorem doubleTargetLength_le_localSize (capacity : Nat)
    (source : List WorkSymbol) (runtime : Runtime) :
    2 * runtime.targetTokens.length ≤
      localSize capacity source runtime := by
  unfold localSize runtimeFootprint
  omega

private theorem checkCells_le_localSize (capacity : Nat)
    (source : List WorkSymbol) (runtime : Runtime) :
    checkCells runtime.checks ≤ localSize capacity source runtime := by
  unfold localSize runtimeFootprint
  omega

theorem PrimitiveSafe.scratch_le
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitive : Primitive} {initial final : Runtime}
    (safe :
      PrimitiveSafe capacity source context primitive initial final)
    (initialBound : initial.scratch ≤ capacity) :
    final.scratch ≤ capacity := by
  cases safe <;> simp_all
  all_goals omega

private theorem encodeNatTokens_length (value : Nat) :
    (encodeNatTokens value).length = value + 1 := by
  induction value with
  | zero =>
      rfl
  | succ value ih =>
      simp [encodeNatTokens, ih]

/-- A primitive can add at most `capacity + 1` logical target tokens. -/
theorem PrimitiveSafe.target_length_le
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitive : Primitive} {initial final : Runtime}
    (safe :
      PrimitiveSafe capacity source context primitive initial final) :
    final.targetTokens.length ≤
      initial.targetTokens.length + capacity + 1 := by
  cases safe with
  | appendPlain runtime token sourcePacked =>
      simp
  | appendMarked runtime token layout =>
      simp
  | emitScratchNatPlain runtime countBound sourcePacked =>
      simp [encodeNatTokens_length]
      omega
  | emitScratchNatMarked runtime countBound layout =>
      simp [encodeNatTokens_length]
      omega
  | resetScratch | addRegister | reloadCaptured |
      incrementScratch | pushCheck | popCheck |
      compareRegister | incrementRegister =>
      change initial.targetTokens.length ≤
        initial.targetTokens.length + capacity + 1
      omega

/-- A primitive can add at most one bounded check record.  Popping only
shrinks the occupied stack word. -/
theorem PrimitiveSafe.checkCells_le
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitive : Primitive} {initial final : Runtime}
    (safe :
      PrimitiveSafe capacity source context primitive initial final) :
    checkCells final.checks ≤
      checkCells initial.checks + capacity + 1 := by
  cases safe with
  | pushCheck runtime fits valueBound =>
      rw [checkCells_push]
      omega
  | popCheck runtime prior value fits scratchZero checksEq valueBound =>
      change
        checkCells prior ≤
          checkCells initial.checks + capacity + 1
      rw [checksEq]
      have := checkCells_prior_le prior value
      omega
  | appendPlain | appendMarked | resetScratch | addRegister |
      reloadCaptured | incrementScratch | emitScratchNatPlain |
      emitScratchNatMarked | compareRegister | incrementRegister =>
      change
        checkCells initial.checks ≤
          checkCells initial.checks + capacity + 1
      omega

/-- A complete safe primitive list grows the logical target by at most one
capacity-sized charge per literal primitive. -/
theorem ProgramSafe.target_length_le
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitives : List Primitive} {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context primitives initial final) :
    final.targetTokens.length ≤
      initial.targetTokens.length +
        primitives.length * (capacity + 1) := by
  induction safe with
  | nil =>
      simp
  | cons primitive rest initial middle final head tail
      inductionHypothesis =>
      have headBound :=
        PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramBound.PrimitiveSafe.target_length_le
          head
      simp only [List.length_cons, Nat.succ_mul]
      omega

/-- The same complete safe list grows occupied check-stack cells by at most
one capacity-sized charge per literal primitive. -/
theorem ProgramSafe.checkCells_le
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitives : List Primitive} {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context primitives initial final) :
    checkCells final.checks ≤
      checkCells initial.checks +
        primitives.length * (capacity + 1) := by
  induction safe with
  | nil =>
      simp
  | cons primitive rest initial middle final head tail
      inductionHypothesis =>
      have headBound :=
        PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramBound.PrimitiveSafe.checkCells_le
          head
      simp only [List.length_cons, Nat.succ_mul]
      omega

private theorem represents_at_state
    {oldState newState capacity scratch : Nat}
    {registers : TargetEmitter.UnaryRegisters}
    {checks : List Nat} {source : List WorkSymbol}
    {target : List Token} {actual : WorkConfiguration}
    (represents :
      TargetEmitterRuntime.Represents oldState capacity scratch
        registers checks source target actual) :
    TargetEmitterRuntime.Represents newState capacity scratch
      registers checks source target
      { state := newState, tape := actual.tape } := by
  refine ⟨?_, ?_⟩
  · simpa using
      (TargetEmitterRuntime.logicalConfiguration_state
        newState capacity scratch registers checks source target).symm
  · simpa only [TargetEmitterRuntime.logicalConfiguration_tape] using
      represents.tape

private theorem configuration_eq_of_state
    {configuration : WorkConfiguration} {state : Nat}
    (stateEq : configuration.state = state) :
    configuration =
      { state := state, tape := configuration.tape } := by
  cases configuration with
  | mk actualState tape =>
      simp only at stateEq
      subst actualState
      rfl

private theorem primitiveWorkEnvelope_mono
    {first second : Nat} (bounded : first ≤ second) :
    primitiveWorkEnvelope first ≤ primitiveWorkEnvelope second := by
  have squareBound :
      first * first ≤ second * second :=
    Nat.mul_le_mul bounded bounded
  unfold primitiveWorkEnvelope
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 100 squareBound) 100

private theorem localSize_le_runtimeFootprint
    (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime) (programLength : Nat) :
    localSize capacity source runtime ≤
      runtimeFootprint capacity source runtime programLength := by
  unfold localSize runtimeFootprint
  omega

private theorem PrimitiveSafe.remainingFootprint_le
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitive : Primitive} {initial final : Runtime}
    (safe :
      PrimitiveSafe capacity source context primitive initial final)
    (remaining : Nat) :
    runtimeFootprint capacity source final remaining ≤
      runtimeFootprint capacity source initial (remaining + 1) := by
  have targetLe :=
    PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramBound.PrimitiveSafe.target_length_le
      safe
  have checksLe :=
    PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramBound.PrimitiveSafe.checkCells_le
      safe
  unfold runtimeFootprint
  rw [Nat.add_mul]
  simp only [Nat.one_mul]
  omega

/-- Exact realization of one safe primitive, with its literal work count
bounded by a common quadratic expression in the current physical footprint.
-/
theorem PrimitiveSafe.exact_bounded
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitive : Primitive} {initial final : Runtime}
    (safe :
      PrimitiveSafe capacity source context primitive initial final)
    (initialScratchBound : initial.scratch ≤ capacity)
    (program : WorkMachine)
    (compiled : primitiveMachine primitive = some program)
    (actual : WorkConfiguration)
    (represents :
      TargetEmitterRuntime.Represents program.startState
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens actual) :
    ∃ steps actualFinal,
      workRunExact? program steps actual = some actualFinal ∧
      TargetEmitterRuntime.Represents program.acceptState
        capacity final.scratch final.registers final.checks
        source final.targetTokens actualFinal ∧
      steps ≤ primitiveWorkEnvelope (localSize capacity source initial) := by
  cases safe with
  | appendPlain runtime token sourcePacked =>
      have programEq :
          program = TargetEmitter.machineFor token := by
        simpa [primitiveMachine] using compiled.symm
      subst program
      rcases
          TargetEmitterRuntimePrimitives.appendPlain_exact
            capacity initial.scratch initial.registers
            initial.checks source initial.targetTokens token actual
            sourcePacked represents with
        ⟨actualFinal, exactRun, finalRepresents⟩
      refine
        ⟨TargetEmitter.packedAppendWorkSteps source
            (SourceParser.packedTokenCells initial.targetTokens),
          actualFinal, exactRun, finalRepresents, ?_⟩
      unfold TargetEmitter.packedAppendWorkSteps
      rw [SourceParser.packedTokenCells_length]
      have sourceLe :=
        sourceLength_le_localSize capacity source initial
      have targetLe :=
        doubleTargetLength_le_localSize capacity source initial
      have sizeLe :=
        localSize_le_square capacity source initial
      unfold primitiveWorkEnvelope
      omega
  | appendMarked runtime token layout =>
      have programEq :
          program =
            TargetEmitterCursorAppender.machineFor token := by
        simpa [primitiveMachine] using compiled.symm
      subst program
      have inputRepresents :
          TargetEmitterRuntime.Represents
            (TargetEmitter.seekSourceState token)
            capacity initial.scratch initial.registers initial.checks
            (TargetEmitterCursorAppender.sourceWithCursor
              layout.cursorBefore layout.cursorOriginal
              layout.cursorAfter)
            initial.targetTokens actual := by
        simpa only [TargetEmitterCursorAppender.machineFor,
          layout.cursorSource] using represents
      rcases
          TargetEmitterRuntimePrimitives.appendMarked_exact
            capacity initial.scratch initial.registers
            initial.checks layout.cursorBefore layout.cursorOriginal
            layout.cursorAfter initial.targetTokens token actual
            layout.originalPacked inputRepresents with
        ⟨actualFinal, exactRun, finalRepresents⟩
      refine
        ⟨TargetEmitterCursorAppender.workSteps
            layout.cursorBefore layout.cursorAfter
            (SourceParser.packedTokenCells initial.targetTokens),
          actualFinal, exactRun, ?_, ?_⟩
      · simpa only [TargetEmitterCursorAppender.machineFor,
          ← layout.cursorSource] using finalRepresents
      · have sourceLength := congrArg List.length layout.cursorSource
        simp only [TargetEmitterCursorAppender.sourceWithCursor,
          List.length_append, List.length_cons] at sourceLength
        rw [TargetEmitterCursorAppender.workSteps_evaluated,
          SourceParser.packedTokenCells_length]
        have sourceLe :=
          sourceLength_le_localSize capacity source initial
        have targetLe :=
          doubleTargetLength_le_localSize capacity source initial
        have sizeLe :=
          localSize_le_square capacity source initial
        unfold primitiveWorkEnvelope
        omega
  | resetScratch runtime scratchBound =>
      have programEq :
          program = TargetEmitterScratchReset.machine := by
        simpa [primitiveMachine] using compiled.symm
      subst program
      have inputRepresents :
          TargetEmitterRuntime.Represents
            TargetEmitterScratchReset.startState
            capacity initial.scratch initial.registers initial.checks
            (context.head :: context.tail)
            initial.targetTokens actual := by
        simpa only [TargetEmitterScratchReset.machine,
          context.source_eq] using represents
      rcases
          TargetEmitterRuntimePrimitives.resetScratch_exact
            capacity initial.scratch initial.registers initial.checks
            context.head context.tail initial.targetTokens actual
            scratchBound context.allowed inputRepresents with
        ⟨actualFinal, exactRun, finalRepresents⟩
      refine
        ⟨TargetEmitterScratchReset.workSteps initial.scratch,
          actualFinal, exactRun, ?_, ?_⟩
      · simpa only [TargetEmitterScratchReset.machine,
          ← context.source_eq] using finalRepresents
      · have scratchLe :
            initial.scratch ≤ localSize capacity source initial := by
          have capacityLe :=
            capacity_le_localSize capacity source initial
          omega
        have sizeLe :=
          localSize_le_square capacity source initial
        unfold TargetEmitterScratchReset.workSteps primitiveWorkEnvelope
        omega
  | addRegister runtime counter slot slotEq fits enough =>
      have programEq :
          program =
            TargetEmitterScratchAddSlot.machineFor slot := by
        simpa [primitiveMachine, slotEq] using compiled.symm
      subst program
      have inputRepresents :
          TargetEmitterRuntime.Represents
            (TargetEmitterScratchAddSlot.startState slot)
            capacity initial.scratch initial.registers initial.checks
            (context.head :: context.tail)
            initial.targetTokens actual := by
        simpa only [TargetEmitterScratchAddSlot.machineFor,
          context.source_eq] using represents
      rcases
          TargetEmitterRuntimePrimitives.addRegister_exact
            slot capacity initial.scratch initial.registers
            initial.checks context.head context.tail
            initial.targetTokens actual fits.toPrimitive enough
            context.addAllowed inputRepresents with
        ⟨actualFinal, exactRun, finalRepresents⟩
      let value :=
        TargetEmitterLedger.slotValue initial.registers slot
      refine
        ⟨TargetEmitterScratchAddSlot.workSteps slot capacity
            initial.scratch value,
          actualFinal, exactRun, ?_, ?_⟩
      · simpa only [TargetEmitterScratchAddSlot.machineFor,
          ← context.source_eq] using finalRepresents
      · have capacityLe :=
          capacity_le_localSize capacity source initial
        have scratchCapacity : initial.scratch ≤ capacity := by
          omega
        have valueCapacity : value ≤ capacity := by
          dsimp [value]
          omega
        have scratchLe :
            initial.scratch ≤ localSize capacity source initial :=
          Nat.le_trans scratchCapacity capacityLe
        have valueLe :
            value ≤ localSize capacity source initial :=
          Nat.le_trans valueCapacity capacityLe
        have sizeLe :=
          localSize_le_square capacity source initial
        have valueCapacityProduct :
            value * capacity ≤
              localSize capacity source initial *
                localSize capacity source initial :=
          Nat.mul_le_mul valueLe capacityLe
        have valueScratchProduct :
            value * initial.scratch ≤
              localSize capacity source initial *
                localSize capacity source initial :=
          Nat.mul_le_mul valueLe scratchLe
        have valueSquare :
            value * value ≤
              localSize capacity source initial *
                localSize capacity source initial :=
          Nat.mul_le_mul valueLe valueLe
        apply Nat.le_trans
          (TargetEmitterScratchAddSlot.workSteps_le_polynomialWorkBound
            slot capacity initial.scratch value)
        unfold TargetEmitterScratchAddSlot.polynomialWorkBound
          primitiveWorkEnvelope
        have expand :
            value * (12 * capacity + 2 * initial.scratch + 37) =
              12 * (value * capacity) +
                2 * (value * initial.scratch) + 37 * value := by
          simp only [Nat.mul_add]
          ac_rfl
        rw [expand]
        simp only [Nat.mul_assoc]
        omega
  | reloadCaptured runtime layout scratchZero capturedEq valueBound =>
      have programEq :
          program = TargetEmitterMarkedSourceReload.machine := by
        simpa [primitiveMachine] using compiled.symm
      subst program
      have inputRepresents :
          TargetEmitterRuntime.Represents
            TargetEmitterMarkedSourceReload.startState
            capacity 0 initial.registers initial.checks
            (TargetEmitterMarkedSourceReload.packedWord
                layout.reloadBefore ++
              TargetEmitterMarkedSourceReload.markedSourceCells
                layout.kind layout.value ++
              layout.reloadAfter)
            initial.targetTokens actual := by
        simpa only [TargetEmitterMarkedSourceReload.machine,
          scratchZero, layout.reloadSource] using represents
      rcases
          TargetEmitterRuntimePrimitives.reloadCaptured_exact
            layout.kind capacity layout.value initial.registers
            initial.checks layout.reloadBefore layout.reloadAfter
            initial.targetTokens actual valueBound inputRepresents with
        ⟨actualFinal, exactRun, finalRepresents⟩
      refine
        ⟨TargetEmitterMarkedSourceReload.workSteps
            layout.reloadBefore.length layout.value,
          actualFinal, exactRun, ?_, ?_⟩
      · simpa [TargetEmitterMarkedSourceReload.machine,
          scratchZero, capturedEq, ← layout.reloadSource] using
          finalRepresents
      · have capacityLe :=
          capacity_le_localSize capacity source initial
        have valueCapacity : layout.value ≤ capacity := by omega
        have valueLe :
            layout.value ≤ localSize capacity source initial :=
          Nat.le_trans valueCapacity capacityLe
        have sourceLength := congrArg List.length layout.reloadSource
        have beforeSource :
            layout.reloadBefore.length ≤ source.length := by
          simp only [List.length_append] at sourceLength
          have packedLength :
              layout.reloadBefore.length ≤
                (TargetEmitterMarkedSourceReload.packedWord
                  layout.reloadBefore).length := by
            simp [TargetEmitterMarkedSourceReload.packedWord]
          omega
        have beforeLe :
            layout.reloadBefore.length ≤
              localSize capacity source initial :=
          Nat.le_trans beforeSource
            (sourceLength_le_localSize capacity source initial)
        let size := localSize capacity source initial
        have sumLe :
            layout.reloadBefore.length + layout.value ≤ 2 * size := by
          dsimp [size]
          omega
        have squareLe :
            (layout.reloadBefore.length + layout.value) *
                (layout.reloadBefore.length + layout.value) ≤
              4 * (size * size) := by
          have multiplied := Nat.mul_le_mul sumLe sumLe
          have normalized : (2 * size) * (2 * size) =
              4 * (size * size) := by ac_rfl
          simpa only [normalized] using multiplied
        have sizeLe :
            size ≤ size * size := by
          exact localSize_le_square capacity source initial
        have quadraticLe :
            5 * (layout.reloadBefore.length + layout.value) *
                (layout.reloadBefore.length + layout.value) ≤
              20 * (size * size) := by
          have scaled := Nat.mul_le_mul_left 5 squareLe
          have normalized :
              5 * (4 * (size * size)) =
                20 * (size * size) := by omega
          rw [normalized] at scaled
          simpa only [Nat.mul_assoc] using scaled
        have linearLe :
            15 * (layout.reloadBefore.length + layout.value) ≤
              30 * (size * size) := by
          have first := Nat.mul_le_mul_left 15 sumLe
          have second := Nat.mul_le_mul_left 30 sizeLe
          omega
        apply Nat.le_trans
          (TargetEmitterMarkedSourceReload.workSteps_le_polynomialWorkBound
            layout.reloadBefore.length layout.value)
        unfold TargetEmitterMarkedSourceReload.polynomialWorkBound
          primitiveWorkEnvelope
        rw [TargetEmitterMarkedSourceReload.workPolynomial_eval]
        dsimp [size] at sumLe squareLe sizeLe quadraticLe linearLe ⊢
        omega
  | incrementScratch runtime scratchBound =>
      have programEq :
          program = TargetEmitterScratchIncrement.machine := by
        simpa [primitiveMachine] using compiled.symm
      subst program
      have inputRepresents :
          TargetEmitterRuntime.Represents
            TargetEmitterScratchIncrement.startState
            capacity initial.scratch initial.registers initial.checks
            (context.head :: context.tail)
            initial.targetTokens actual := by
        simpa only [TargetEmitterScratchIncrement.machine,
          context.source_eq] using represents
      rcases
          TargetEmitterRuntimePrimitives.incrementScratch_exact
            capacity initial.scratch initial.registers initial.checks
            context.head context.tail initial.targetTokens actual
            scratchBound context.allowed inputRepresents with
        ⟨actualFinal, exactRun, finalRepresents⟩
      refine
        ⟨TargetEmitterScratchIncrement.workSteps initial.scratch,
          actualFinal, exactRun, ?_, ?_⟩
      · simpa only [TargetEmitterScratchIncrement.machine,
          ← context.source_eq] using finalRepresents
      · have scratchLe :
            initial.scratch ≤ localSize capacity source initial := by
          have capacityLe :=
            capacity_le_localSize capacity source initial
          omega
        have sizeLe :=
          localSize_le_square capacity source initial
        unfold TargetEmitterScratchIncrement.workSteps
          primitiveWorkEnvelope
        omega
  | emitScratchNatPlain runtime countBound sourcePacked =>
      have programEq :
          program = TargetEmitterNatLoop.machine := by
        simpa [primitiveMachine] using compiled.symm
      subst program
      have inputRepresents :
          TargetEmitterRuntime.Represents
            TargetEmitterNatLoop.startState
            capacity initial.scratch initial.registers initial.checks
            (context.head :: context.tail)
            initial.targetTokens actual := by
        simpa only [TargetEmitterNatLoop.machine,
          context.source_eq] using represents
      have sourcePacked' :
          ∀ symbol, symbol ∈ context.head :: context.tail →
            TargetEmitter.PackedSymbol symbol := by
        intro symbol member
        apply sourcePacked symbol
        simpa only [context.source_eq] using member
      rcases
          TargetEmitterRuntimePrimitives.emitScratchNatPlain_exact
            capacity initial.scratch initial.registers initial.checks
            context.head context.tail initial.targetTokens actual
            countBound sourcePacked' inputRepresents with
        ⟨actualFinal, exactRun, finalRepresents⟩
      let targetCells :=
        SourceParser.packedTokenCells initial.targetTokens
      refine
        ⟨TargetEmitterNatLoop.loopWorkSteps source
            targetCells 0 initial.scratch,
          actualFinal, ?_, ?_, ?_⟩
      · simpa only [context.source_eq, targetCells] using exactRun
      · simpa only [TargetEmitterNatLoop.machine,
          ← context.source_eq] using finalRepresents
      · let size := localSize capacity source initial
        have countLe : initial.scratch ≤ size :=
          Nat.le_trans countBound
            (capacity_le_localSize capacity source initial)
        have sourceLe : source.length ≤ size :=
          sourceLength_le_localSize capacity source initial
        have targetLe :
            targetCells.length ≤ size := by
          dsimp [targetCells]
          rw [SourceParser.packedTokenCells_length]
          exact doubleTargetLength_le_localSize
            capacity source initial
        have sizeLe : size ≤ size * size :=
          localSize_le_square capacity source initial
        have countSource :
            initial.scratch * source.length ≤ size * size :=
          Nat.mul_le_mul countLe sourceLe
        have countTarget :
            initial.scratch * targetCells.length ≤ size * size :=
          Nat.mul_le_mul countLe targetLe
        have countSquare :
            initial.scratch * initial.scratch ≤ size * size :=
          Nat.mul_le_mul countLe countLe
        have triangularLe :
            TargetEmitterNatLoop.triangular initial.scratch ≤
              size * size :=
          Nat.le_trans
            (TargetEmitterNatLoop.triangular_le_square
              initial.scratch)
            countSquare
        have countLeSquare :
            initial.scratch ≤ size * size :=
          Nat.le_trans countLe sizeLe
        have sourceLeSquare :
            source.length ≤ size * size :=
          Nat.le_trans sourceLe sizeLe
        have targetLeSquare :
            targetCells.length ≤ size * size :=
          Nat.le_trans targetLe sizeLe
        unfold TargetEmitterNatLoop.loopWorkSteps
          primitiveWorkEnvelope
        have expand :
            initial.scratch *
                (2 * source.length + 2 * targetCells.length +
                  2 * 0 + 10) =
              2 * (initial.scratch * source.length) +
                2 * (initial.scratch * targetCells.length) +
                10 * initial.scratch := by
          simp only [Nat.mul_add, Nat.mul_zero, Nat.add_zero]
          ac_rfl
        rw [expand]
        dsimp [size] at *
        omega
  | emitScratchNatMarked runtime countBound layout =>
      have programEq :
          program = TargetEmitterCursorNatLoop.machine := by
        simpa [primitiveMachine] using compiled.symm
      subst program
      have cursorSource :
          source =
            TargetEmitterCursorNatLoop.markedSource
              layout.cursorBefore layout.cursorAfter := by
        simpa only [TargetEmitterCursorNatLoop.markedSource,
          TargetEmitterCursorNatLoop.cursorMarker,
          TargetEmitterCursorAppender.sourceWithCursor] using
          layout.cursorSource
      have inputRepresents :
          TargetEmitterRuntime.Represents
            TargetEmitterCursorNatLoop.startState
            capacity initial.scratch initial.registers initial.checks
            (TargetEmitterCursorNatLoop.markedSource
              layout.cursorBefore layout.cursorAfter)
            initial.targetTokens actual := by
        simpa only [TargetEmitterCursorNatLoop.machine,
          cursorSource] using represents
      rcases
          TargetEmitterRuntimePrimitives.emitScratchNatMarked_exact
            capacity initial.scratch initial.registers initial.checks
            layout.cursorBefore layout.cursorAfter
            initial.targetTokens actual countBound
            layout.beforePacked layout.afterPacked inputRepresents with
        ⟨actualFinal, exactRun, finalRepresents⟩
      refine
        ⟨TargetEmitterCursorNatLoop.workSteps
            layout.cursorBefore layout.cursorAfter
            initial.targetTokens initial.scratch,
          actualFinal, exactRun, ?_, ?_⟩
      · simpa only [TargetEmitterCursorNatLoop.machine,
          ← cursorSource] using finalRepresents
      · let size := localSize capacity source initial
        have countLe : initial.scratch ≤ size :=
          Nat.le_trans countBound
            (capacity_le_localSize capacity source initial)
        have sourceLength := congrArg List.length cursorSource
        have partsSource :
            layout.cursorBefore.length +
                layout.cursorAfter.length ≤ source.length := by
          simp [TargetEmitterCursorNatLoop.markedSource] at sourceLength
          omega
        have partsLe :
            layout.cursorBefore.length +
                layout.cursorAfter.length ≤ size :=
          Nat.le_trans partsSource
            (sourceLength_le_localSize capacity source initial)
        have targetLe :
            2 * initial.targetTokens.length ≤ size :=
          doubleTargetLength_le_localSize capacity source initial
        have sizeLe : size ≤ size * size :=
          localSize_le_square capacity source initial
        have countParts :
            initial.scratch *
                (layout.cursorBefore.length +
                  layout.cursorAfter.length) ≤ size * size :=
          Nat.mul_le_mul countLe partsLe
        have countTarget :
            initial.scratch *
                (2 * initial.targetTokens.length) ≤ size * size :=
          Nat.mul_le_mul countLe targetLe
        have countSquare :
            initial.scratch * initial.scratch ≤ size * size :=
          Nat.mul_le_mul countLe countLe
        apply Nat.le_trans
          (TargetEmitterCursorNatLoop.workSteps_le_polynomialWorkBound
            layout.cursorBefore layout.cursorAfter
            initial.targetTokens initial.scratch)
        unfold TargetEmitterCursorNatLoop.polynomialWorkBound
          primitiveWorkEnvelope
        have expand :
            initial.scratch *
                (2 * layout.cursorBefore.length +
                  2 * layout.cursorAfter.length +
                  4 * initial.targetTokens.length + 12) =
              2 *
                  (initial.scratch *
                    (layout.cursorBefore.length +
                      layout.cursorAfter.length)) +
                2 *
                  (initial.scratch *
                    (2 * initial.targetTokens.length)) +
                12 * initial.scratch := by
          simp only [Nat.mul_add]
          ac_rfl
        rw [expand]
        dsimp [size] at *
        omega
  | pushCheck runtime fits valueBound =>
      have programEq :
          program = TargetEmitterCheckStack.Push.machine := by
        simpa [primitiveMachine] using compiled.symm
      subst program
      have inputRepresents :
          TargetEmitterRuntime.Represents
            TargetEmitterCheckStack.Push.startState
            capacity initial.scratch initial.registers initial.checks
            (context.head :: context.tail)
            initial.targetTokens actual := by
        simpa only [TargetEmitterCheckStack.Push.machine,
          TargetEmitterCheckStack.machineOf,
          context.source_eq] using represents
      rcases
          TargetEmitterRuntimeCheckStack.CheckStack.push_exact
            capacity initial.scratch initial.registers initial.checks
            context.head context.tail initial.targetTokens actual
            fits.toCheckStack valueBound context.stackAllowed
            inputRepresents with
        ⟨actualFinal, exactRun, finalRepresents⟩
      refine
        ⟨TargetEmitterCheckStack.Push.workSteps capacity
            (TargetEmitterCheckStack.recordsWord
              initial.checks).length initial.scratch,
          actualFinal, exactRun, ?_, ?_⟩
      · simpa only [TargetEmitterCheckStack.Push.machine,
          TargetEmitterCheckStack.machineOf,
          ← context.source_eq] using finalRepresents
      · let size := localSize capacity source initial
        let records :=
          (TargetEmitterCheckStack.recordsWord
            initial.checks).length
        have capacityLe : capacity ≤ size :=
          capacity_le_localSize capacity source initial
        have valueLe : initial.scratch ≤ size :=
          Nat.le_trans valueBound capacityLe
        have recordsLe : records ≤ size := by
          exact checkCells_le_localSize capacity source initial
        have sizeLe : size ≤ size * size :=
          localSize_le_square capacity source initial
        have valueCapacity :
            initial.scratch * capacity ≤ size * size :=
          Nat.mul_le_mul valueLe capacityLe
        have valueRecords :
            initial.scratch * records ≤ size * size :=
          Nat.mul_le_mul valueLe recordsLe
        apply Nat.le_trans
          (TargetEmitterCheckStack.Push.workSteps_le_polynomialWorkBound
            capacity records initial.scratch)
        unfold TargetEmitterCheckStack.Push.polynomialWorkBound
          primitiveWorkEnvelope
        have expand :
            initial.scratch * (14 * capacity + 2 * records + 38) =
              14 * (initial.scratch * capacity) +
                2 * (initial.scratch * records) +
                38 * initial.scratch := by
          simp only [Nat.mul_add]
          ac_rfl
        rw [expand]
        dsimp [size, records] at *
        omega
  | popCheck runtime prior value fits scratchZero checksEq valueBound =>
      have programEq :
          program = TargetEmitterCheckStack.Pop.machine := by
        simpa [primitiveMachine] using compiled.symm
      subst program
      have inputRepresents :
          TargetEmitterRuntime.Represents
            TargetEmitterCheckStack.Pop.startState
            capacity 0 initial.registers (prior ++ [value])
            (context.head :: context.tail)
            initial.targetTokens actual := by
        simpa only [TargetEmitterCheckStack.Pop.machine,
          TargetEmitterCheckStack.machineOf,
          scratchZero, checksEq, context.source_eq] using
          represents
      rcases
          TargetEmitterRuntimeCheckStack.CheckStack.pop_nonempty_exact
            capacity value initial.registers prior context.head
            context.tail initial.targetTokens actual
            fits.toCheckStack valueBound context.stackAllowed
            inputRepresents with
        ⟨actualFinal, exactRun, finalRepresents⟩
      let records :=
        (TargetEmitterCheckStack.recordsWord prior).length
      refine
        ⟨TargetEmitterCheckStack.Pop.nonemptyWorkSteps
            capacity records value,
          actualFinal, exactRun, ?_, ?_⟩
      · simpa only [TargetEmitterCheckStack.Pop.machine,
          TargetEmitterCheckStack.machineOf,
          ← context.source_eq] using finalRepresents
      · let size := localSize capacity source initial
        have capacityLe : capacity ≤ size :=
          capacity_le_localSize capacity source initial
        have valueLe : value ≤ size :=
          Nat.le_trans valueBound capacityLe
        have recordsInitial :
            records ≤ checkCells initial.checks := by
          dsimp [records]
          rw [checksEq]
          exact checkCells_prior_le prior value
        have recordsLe : records ≤ size :=
          Nat.le_trans recordsInitial
            (checkCells_le_localSize capacity source initial)
        have sizeLe : size ≤ size * size :=
          localSize_le_square capacity source initial
        have valueCapacity : value * capacity ≤ size * size :=
          Nat.mul_le_mul valueLe capacityLe
        have valueRecords : value * records ≤ size * size :=
          Nat.mul_le_mul valueLe recordsLe
        have valueSquare : value * value ≤ size * size :=
          Nat.mul_le_mul valueLe valueLe
        apply Nat.le_trans
          (TargetEmitterCheckStack.Pop.nonemptyWorkSteps_le_polynomialWorkBound
            capacity records value)
        unfold
          TargetEmitterCheckStack.Pop.nonemptyPolynomialWorkBound
          primitiveWorkEnvelope
        have expand :
            value *
                (14 * capacity + 2 * records + 2 * value + 43) =
              14 * (value * capacity) +
                2 * (value * records) +
                2 * (value * value) + 43 * value := by
          simp only [Nat.mul_add]
          ac_rfl
        rw [expand]
        dsimp [size, records] at *
        omega
  | compareRegister runtime counter slot slotEq fits equal =>
      have programEq :
          program =
            TargetEmitterScratchCompareSlot.machineFor slot := by
        simpa [primitiveMachine, slotEq] using compiled.symm
      subst program
      have inputRepresents :
          TargetEmitterRuntime.Represents
            (TargetEmitterScratchCompareSlot.startState slot)
            capacity initial.scratch initial.registers initial.checks
            (context.head :: context.tail)
            initial.targetTokens actual := by
        simpa only [TargetEmitterScratchCompareSlot.machineFor,
          context.source_eq] using represents
      rcases
          TargetEmitterRuntimePrimitives.compareRegisterEqual_exact
            slot capacity initial.scratch initial.registers
            initial.checks context.head context.tail
            initial.targetTokens actual fits.toPrimitive equal
            context.compareAllowed inputRepresents with
        ⟨actualFinal, exactRun, finalRepresents⟩
      refine
        ⟨TargetEmitterScratchCompareSlot.workSteps
            slot capacity initial.scratch,
          actualFinal, exactRun, ?_, ?_⟩
      · simpa only [TargetEmitterScratchCompareSlot.machineFor,
          ← context.source_eq] using finalRepresents
      · let size := localSize capacity source initial
        have capacityLe : capacity ≤ size :=
          capacity_le_localSize capacity source initial
        have scratchLe : initial.scratch ≤ size :=
          Nat.le_trans initialScratchBound capacityLe
        have sizeLe : size ≤ size * size :=
          localSize_le_square capacity source initial
        have scratchCapacity :
            initial.scratch * capacity ≤ size * size :=
          Nat.mul_le_mul scratchLe capacityLe
        apply Nat.le_trans
          (TargetEmitterScratchCompareSlot.workSteps_le_polynomialWorkBound
            slot capacity initial.scratch)
        unfold TargetEmitterScratchCompareSlot.polynomialWorkBound
          primitiveWorkEnvelope
        have expand :
            initial.scratch * (14 * capacity + 31) =
              14 * (initial.scratch * capacity) +
                31 * initial.scratch := by
          simp only [Nat.mul_add]
          ac_rfl
        rw [expand]
        dsimp [size] at *
        omega
  | incrementRegister runtime counter slot slotEq fits available =>
      have programEq :
          program =
            TargetEmitterSlotIncrement.machineFor slot := by
        simpa [primitiveMachine, slotEq] using compiled.symm
      subst program
      have inputRepresents :
          TargetEmitterRuntime.Represents
            (TargetEmitterSlotIncrement.startState slot)
            capacity initial.scratch initial.registers initial.checks
            (context.head :: context.tail)
            initial.targetTokens actual := by
        simpa only [TargetEmitterSlotIncrement.machineFor,
          context.source_eq] using represents
      rcases
          TargetEmitterRuntimePrimitives.incrementRegister_exact
            slot capacity initial.scratch initial.registers
            initial.checks context.head context.tail
            initial.targetTokens actual fits.toPrimitive available
            context.allowed inputRepresents with
        ⟨actualFinal, exactRun, finalRepresents⟩
      let bank :=
        TargetEmitterRuntimePrimitives.slotBankOfRegisters
          capacity initial.registers
      refine
        ⟨TargetEmitterSlotIncrement.workSteps slot initial.scratch
            (capacity - initial.scratch) bank,
          actualFinal, exactRun, ?_, ?_⟩
      · simpa only [TargetEmitterSlotIncrement.machineFor,
          ← context.source_eq] using finalRepresents
      · let size := localSize capacity source initial
        have capacityLe : capacity ≤ size :=
          capacity_le_localSize capacity source initial
        have scratchLe : initial.scratch ≤ size :=
          Nat.le_trans initialScratchBound capacityLe
        have reserveCapacity :
            capacity - initial.scratch ≤ capacity :=
          Nat.sub_le capacity initial.scratch
        have reserveLe :
            capacity - initial.scratch ≤ size :=
          Nat.le_trans reserveCapacity capacityLe
        have selectedCapacity :
            TargetEmitterLedger.slotValue initial.registers slot ≤
              capacity := by
          cases slot <;>
            simp [TargetEmitterLedger.slotValue] at available ⊢ <;>
            omega
        have selectedLe :
            (bank.selected slot).value ≤ size := by
          rw [TargetEmitterRuntimePrimitives.slotBankOfRegisters_selected_value]
          exact Nat.le_trans selectedCapacity capacityLe
        have bankWord :
            bank.word =
              TargetEmitterLedger.slotBank
                capacity initial.registers := by
          exact
            TargetEmitterRuntimePrimitives.slotBankOfRegisters_word
              capacity initial.registers fits.toPrimitive
        have bankLength :
            bank.word.length = 6 * (capacity + 2) := by
          rw [bankWord]
          exact
            TargetEmitterCheckStack.slotBank_length
              capacity initial.registers fits.toCheckStack
        have sizeLe : size ≤ size * size :=
          localSize_le_square capacity source initial
        apply Nat.le_trans
          (TargetEmitterSlotIncrement.workSteps_le_polynomialWorkBound
            slot initial.scratch (capacity - initial.scratch) bank)
        unfold TargetEmitterSlotIncrement.polynomialWorkBound
          primitiveWorkEnvelope
        rw [bankLength]
        dsimp [size] at *
        omega

private theorem compileProgram_cons_inv
    {primitive : Primitive} {rest : List Primitive}
    {programs : List WorkMachine}
    (compiled :
      compileProgram (primitive :: rest) = some programs) :
    ∃ program tailPrograms,
      primitiveMachine primitive = some program ∧
      compileProgram rest = some tailPrograms ∧
      programs = program :: tailPrograms := by
  cases machineEq : primitiveMachine primitive with
  | none =>
      simp [compileProgram, machineEq] at compiled
  | some program =>
      cases tailEq : compileProgram rest with
      | none =>
          simp [compileProgram, machineEq, tailEq] at compiled
      | some tailPrograms =>
          refine ⟨program, tailPrograms, rfl, rfl, ?_⟩
          simp only [compileProgram, machineEq, tailEq] at compiled
          exact (Option.some.inj compiled).symm

/-- Constructive exact lifting of a safe closed program with a single
polynomial-style work envelope. -/
theorem ProgramSafe.linearAcceptRuns_bounded
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitives : List Primitive} {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context primitives initial final)
    (initialScratchBound : initial.scratch ≤ capacity)
    (programs : List WorkMachine)
    (compiled : compileProgram primitives = some programs)
    (fallback : Nat)
    (actual : WorkConfiguration)
    (represents :
      TargetEmitterRuntime.Represents
        (entryState fallback programs)
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens actual) :
    ∃ steps actualFinal,
      LinearAcceptRuns programs steps
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        (exitState fallback programs)
        capacity final.scratch final.registers final.checks
        source final.targetTokens actualFinal ∧
      steps ≤
        programWorkEnvelope capacity source initial primitives := by
  induction safe generalizing programs fallback actual with
  | nil runtime =>
      change some [] = some programs at compiled
      have programsEq : programs = [] :=
        (Option.some.inj compiled).symm
      subst programs
      exact
        ⟨0, actual, LinearAcceptRuns.terminal actual.tape,
          represents, by simp [programWorkEnvelope]⟩
  | cons primitive rest initial middle final head tail
      inductionHypothesis =>
      rcases compileProgram_cons_inv compiled with
        ⟨program, tailPrograms, headCompiled,
          tailCompiled, programsEq⟩
      subst programs
      rcases
          PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramBound.PrimitiveSafe.exact_bounded
            head initialScratchBound program
            headCompiled actual represents with
        ⟨localSteps, middleActual, localRun,
          middleRepresents, localBound⟩
      let tailActual : WorkConfiguration :=
        { state := entryState program.acceptState tailPrograms
          tape := middleActual.tape }
      have tailRepresents :
          TargetEmitterRuntime.Represents
            (entryState program.acceptState tailPrograms)
            capacity middle.scratch middle.registers middle.checks
            source middle.targetTokens tailActual := by
        exact represents_at_state middleRepresents
      have middleScratchBound : middle.scratch ≤ capacity :=
        PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramBound.PrimitiveSafe.scratch_le
          head initialScratchBound
      rcases
          inductionHypothesis middleScratchBound tailPrograms
            tailCompiled program.acceptState tailActual tailRepresents with
        ⟨tailSteps, actualFinal, tailRuns,
          finalRepresents, tailBound⟩
      have actualShape :
          actual =
            { state := program.startState
              tape := actual.tape } := by
        exact configuration_eq_of_state
          (TargetEmitterRuntime.Represents.state_eq represents)
      have middleShape :
          middleActual =
            { state := program.acceptState
              tape := middleActual.tape } := by
        exact configuration_eq_of_state
          (TargetEmitterRuntime.Represents.state_eq
            middleRepresents)
      have localRun' :
          workRunExact? program localSteps
              { state := program.startState
                tape := actual.tape } =
            some
              { state := program.acceptState
                tape := middleActual.tape } := by
        simpa only [← actualShape, ← middleShape] using localRun
      refine
        ⟨localSteps + 1 + tailSteps, actualFinal, ?_,
          finalRepresents, ?_⟩
      · exact
          LinearAcceptRuns.step program tailPrograms
            localSteps tailSteps actual.tape middleActual.tape
            actualFinal.tape localRun' tailRuns
      · let totalSize :=
          runtimeFootprint capacity source initial (rest.length + 1)
        have localSizeLe :
            localSize capacity source initial ≤ totalSize := by
          exact localSize_le_runtimeFootprint
            capacity source initial (rest.length + 1)
        have localEnvelopeLe :
            primitiveWorkEnvelope
                (localSize capacity source initial) ≤
              primitiveWorkEnvelope totalSize :=
          primitiveWorkEnvelope_mono localSizeLe
        have localBound' :
            localSteps ≤ primitiveWorkEnvelope totalSize :=
          Nat.le_trans localBound localEnvelopeLe
        have tailSizeLe :
            runtimeFootprint capacity source middle rest.length ≤
              totalSize := by
          exact
            PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramBound.PrimitiveSafe.remainingFootprint_le
              head rest.length
        have tailEnvelopeLe :
            primitiveWorkEnvelope
                (runtimeFootprint capacity source middle rest.length) ≤
              primitiveWorkEnvelope totalSize :=
          primitiveWorkEnvelope_mono tailSizeLe
        have tailBound' :
            tailSteps ≤
              rest.length *
                (primitiveWorkEnvelope totalSize + 1) := by
          apply Nat.le_trans tailBound
          unfold programWorkEnvelope
          exact Nat.mul_le_mul_left rest.length
            (Nat.add_le_add_right tailEnvelopeLe 1)
        unfold programWorkEnvelope
        simp only [List.length_cons]
        dsimp [totalSize] at localBound' tailBound' ⊢
        rw [Nat.add_mul]
        simp only [Nat.one_mul]
        omega

/-- Drop-in bounded form of `ProgramSafe.descriptor_acceptPath_exact`.
The only extra premise is the logical scratch-capacity invariant propagated
constructively through the safe program. -/
theorem ProgramSafe.descriptor_acceptPath_bounded
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (descriptor : TargetEmitterController.BlockDescriptor)
    (descriptorMember :
      descriptor ∈ TargetEmitterController.blockDescriptors)
    {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context
        descriptor.primitives initial final)
    (initialScratchBound : initial.scratch ≤ capacity)
    (programs : List WorkMachine)
    (compiled :
      compileProgram descriptor.primitives = some programs)
    (programsNonempty : programs ≠ [])
    (fallback : Nat)
    (actual : WorkConfiguration)
    (represents :
      TargetEmitterRuntime.Represents
        (entryState fallback programs)
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens actual) :
    ∃ steps actualFinal,
      WorkMachineProgramPath.AcceptPath
          TargetEmitterController.graph
          (.node
            (blockEntry descriptor.code descriptor.primitives))
          descriptor.continuation steps
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        (exitState fallback programs)
        capacity final.scratch final.registers final.checks
        source final.targetTokens actualFinal ∧
      steps ≤
        programWorkEnvelope capacity source initial
          descriptor.primitives := by
  rcases
      PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramBound.ProgramSafe.linearAcceptRuns_bounded
        safe initialScratchBound
        programs compiled fallback actual represents with
    ⟨steps, actualFinal, runs, finalRepresents, stepsBound⟩
  exact
    ⟨steps, actualFinal,
      TargetEmitterController.descriptor_acceptPath_of_compiled
        descriptor descriptorMember programs compiled programsNonempty
        steps actual.tape actualFinal.tape runs,
      finalRepresents, stepsBound⟩

end PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramBound

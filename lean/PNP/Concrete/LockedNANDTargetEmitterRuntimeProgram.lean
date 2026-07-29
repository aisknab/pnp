/-
Copyright (c) 2026 PNP Labs.

Exact runtime lifting for compiled locked-NAND target-emitter programs.

`ProgramSafe` is a proof-only relation.  It records the capacity, source
layout, stack shape, and accepting comparison facts needed by the literal
primitive machines.  Neither it nor the pure semantic runtime is embedded in
the compiled work-machine graph.
-/

import PNP.Concrete.LockedNANDTargetEmitterBlockCompiler
import PNP.Concrete.LockedNANDTargetEmitterProgramSemantics
import PNP.Concrete.LockedNANDTargetEmitterRuntimePrimitives
import PNP.Concrete.LockedNANDTargetEmitterRuntimeCheckStack

namespace PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgram

open PNP.Concrete
open TargetEmitterPlan
open TargetEmitterPrimitiveCompiler
open TargetEmitterBlockCompiler
open TargetEmitterProgramSemantics

abbrev Slot := TargetEmitterLedger.Slot

/-! ### Proof-only source and capacity witnesses -/

structure LedgerFits (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters) : Prop where
  inputCount : registers.inputCount ≤ capacity
  normalizedGateCount : registers.normalizedGateCount ≤ capacity
  carrierWidth : registers.carrierWidth ≤ capacity
  baseline : registers.baseline ≤ capacity
  currentGate : registers.currentGate ≤ capacity
  outputIndex : registers.outputIndex ≤ capacity

def LedgerFits.toPrimitive
    {capacity : Nat}
    {registers : TargetEmitter.UnaryRegisters}
    (fits : LedgerFits capacity registers) :
    TargetEmitterRuntimePrimitives.LedgerFits
      capacity registers :=
  { inputCount := fits.inputCount
    normalizedGateCount := fits.normalizedGateCount
    carrierWidth := fits.carrierWidth
    baseline := fits.baseline
    currentGate := fits.currentGate
    outputIndex := fits.outputIndex }

def LedgerFits.toCheckStack
    {capacity : Nat}
    {registers : TargetEmitter.UnaryRegisters}
    (fits : LedgerFits capacity registers) :
    TargetEmitterRuntimeCheckStack.CheckStack.LedgerFits
      capacity registers :=
  { inputCount := fits.inputCount
    normalizedGateCount := fits.normalizedGateCount
    carrierWidth := fits.carrierWidth
    baseline := fits.baseline
    currentGate := fits.currentGate
    outputIndex := fits.outputIndex }

/-- Common nonempty source view used by primitives that only inspect the
first source cell. -/
structure SourceContext (source : List WorkSymbol) where
  head : WorkSymbol
  tail : List WorkSymbol
  source_eq : source = head :: tail
  allowed :
    TargetEmitter.PackedSymbol head ∨
      head = TargetEmitterCursorAppender.cursorMarker

/-- Exact cursor split used by marked appenders and marked natural emitters.

This view applies to all four source kinds, including constants.  It is kept
separate from `ReloadLayout` because constants have a cursor but deliberately
carry no unary coordinate to reload. -/
structure CursorLayout (source : List WorkSymbol) where
  cursorBefore : List WorkSymbol
  cursorOriginal : WorkSymbol
  cursorAfter : List WorkSymbol
  cursorSource :
    source =
      TargetEmitterCursorAppender.sourceWithCursor
        cursorBefore cursorOriginal cursorAfter
  originalPacked :
    ∀ symbol,
      symbol ∈
        TargetEmitterCursorAppender.originalSource
          cursorBefore cursorOriginal cursorAfter →
        TargetEmitter.PackedSymbol symbol
  beforePacked :
    ∀ symbol, symbol ∈ cursorBefore →
      TargetEmitter.PackedSymbol symbol
  afterPacked :
    ∀ symbol, symbol ∈ cursorAfter →
      TargetEmitter.PackedSymbol symbol

/-- Exact input/gate unary view used only by `reloadCaptured`.

The literal reload machine accepts precisely cursor-marked input and gate
fields.  Keeping this witness separate prevents the proof interface from
inventing a unary reload shape for Boolean constants. -/
structure ReloadLayout (source : List WorkSymbol) where
  kind : TargetEmitterMarkedSourceReload.NatKind
  value : Nat
  reloadBefore :
    List TargetEmitterMarkedSourceReload.PackedCell
  reloadAfter : List WorkSymbol
  reloadSource :
    source =
      TargetEmitterMarkedSourceReload.packedWord reloadBefore ++
        TargetEmitterMarkedSourceReload.markedSourceCells kind value ++
        reloadAfter

theorem SourceContext.addAllowed
    {source : List WorkSymbol}
    (context : SourceContext source) :
    TargetEmitterScratchAddSlot.sourceAllowed context.head := by
  exact context.allowed

theorem SourceContext.compareAllowed
    {source : List WorkSymbol}
    (context : SourceContext source) :
    TargetEmitterScratchCompareSlot.SourceAllowed context.head := by
  exact context.allowed

private theorem packed_checkStackAllowed
    {symbol : WorkSymbol}
    (packed : TargetEmitter.PackedSymbol symbol) :
    TargetEmitterCheckStack.sourceAllowed symbol := by
  cases packed <;>
    simp [TargetEmitterCheckStack.sourceAllowed]

theorem SourceContext.stackAllowed
    {source : List WorkSymbol}
    (context : SourceContext source) :
    TargetEmitterCheckStack.sourceAllowed context.head := by
  rcases context.allowed with packed | cursor
  · exact packed_checkStackAllowed packed
  · simp [TargetEmitterCheckStack.sourceAllowed, cursor,
      TargetEmitterCheckStack.cursorMarker,
      TargetEmitterCursorAppender.cursorMarker]

/-! ### Register correspondence -/

theorem registerValue_eq_slotValue
    (registers : TargetEmitter.UnaryRegisters)
    (counter : Counter) (slot : Slot)
    (slotEq : counterSlot counter = some slot) :
    registerValue registers counter =
      some (TargetEmitterLedger.slotValue registers slot) := by
  cases counter <;> cases slot <;>
    simp [counterSlot, registerValue,
      TargetEmitterLedger.slotValue] at slotEq ⊢

theorem incrementRegister_eq_incrementRegisters
    (registers : TargetEmitter.UnaryRegisters)
    (counter : Counter) (slot : Slot)
    (slotEq : counterSlot counter = some slot) :
    incrementRegister registers counter =
      some
        (TargetEmitterRuntimePrimitives.incrementRegisters
          slot registers) := by
  cases counter <;> cases slot <;>
    simp [counterSlot, incrementRegister,
      TargetEmitterRuntimePrimitives.incrementRegisters]
      at slotEq ⊢

/-! ### Accept-only primitive safety -/

inductive PrimitiveSafe
    (capacity : Nat) (source : List WorkSymbol)
    (context : SourceContext source) :
    Primitive → Runtime → Runtime → Prop where
  | appendPlain
      (runtime : Runtime) (token : Token)
      (sourcePacked :
        ∀ symbol, symbol ∈ source →
          TargetEmitter.PackedSymbol symbol) :
      PrimitiveSafe capacity source context
        (.append .plain token) runtime
        { runtime with
          targetTokens := runtime.targetTokens ++ [token] }
  | appendMarked
      (runtime : Runtime) (token : Token)
      (layout : CursorLayout source) :
      PrimitiveSafe capacity source context
        (.append .marked token) runtime
        { runtime with
          targetTokens := runtime.targetTokens ++ [token] }
  | resetScratch
      (runtime : Runtime)
      (scratchBound : runtime.scratch < capacity) :
      PrimitiveSafe capacity source context .resetScratch runtime
        { runtime with scratch := 0 }
  | addRegister
      (runtime : Runtime) (counter : Counter) (slot : Slot)
      (slotEq : counterSlot counter = some slot)
      (fits : LedgerFits capacity runtime.registers)
      (enough :
        runtime.scratch +
            TargetEmitterLedger.slotValue runtime.registers slot ≤
          capacity) :
      PrimitiveSafe capacity source context
        (.addRegister counter) runtime
        { runtime with
          scratch :=
            runtime.scratch +
              TargetEmitterLedger.slotValue runtime.registers slot }
  | reloadCaptured
      (runtime : Runtime) (layout : ReloadLayout source)
      (scratchZero : runtime.scratch = 0)
      (capturedEq : runtime.captured = layout.value)
      (valueBound : layout.value + 1 ≤ capacity) :
      PrimitiveSafe capacity source context .reloadCaptured runtime
        { runtime with
          scratch := runtime.scratch + runtime.captured }
  | incrementScratch
      (runtime : Runtime)
      (scratchBound : runtime.scratch < capacity) :
      PrimitiveSafe capacity source context .incrementScratch runtime
        { runtime with scratch := runtime.scratch + 1 }
  | emitScratchNatPlain
      (runtime : Runtime)
      (countBound : runtime.scratch ≤ capacity)
      (sourcePacked :
        ∀ symbol, symbol ∈ source →
          TargetEmitter.PackedSymbol symbol) :
      PrimitiveSafe capacity source context
        (.emitScratchNat .plain) runtime
        { runtime with
          targetTokens :=
            runtime.targetTokens ++
              encodeNatTokens runtime.scratch }
  | emitScratchNatMarked
      (runtime : Runtime)
      (countBound : runtime.scratch ≤ capacity)
      (layout : CursorLayout source) :
      PrimitiveSafe capacity source context
        (.emitScratchNat .marked) runtime
        { runtime with
          targetTokens :=
            runtime.targetTokens ++
              encodeNatTokens runtime.scratch }
  | pushCheck
      (runtime : Runtime)
      (fits : LedgerFits capacity runtime.registers)
      (valueBound : runtime.scratch ≤ capacity) :
      PrimitiveSafe capacity source context .pushCheck runtime
        { runtime with
          checks := runtime.checks ++ [runtime.scratch] }
  | popCheck
      (runtime : Runtime) (prior : List Nat) (value : Nat)
      (fits : LedgerFits capacity runtime.registers)
      (scratchZero : runtime.scratch = 0)
      (checksEq : runtime.checks = prior ++ [value])
      (valueBound : value ≤ capacity) :
      PrimitiveSafe capacity source context .popCheck runtime
        { runtime with scratch := value, checks := prior }
  | compareRegister
      (runtime : Runtime) (counter : Counter) (slot : Slot)
      (slotEq : counterSlot counter = some slot)
      (fits : LedgerFits capacity runtime.registers)
      (equal :
        runtime.scratch =
          TargetEmitterLedger.slotValue runtime.registers slot) :
      PrimitiveSafe capacity source context
        (.compareRegister counter) runtime runtime
  | incrementRegister
      (runtime : Runtime) (counter : Counter) (slot : Slot)
      (slotEq : counterSlot counter = some slot)
      (fits : LedgerFits capacity runtime.registers)
      (available :
        TargetEmitterLedger.slotValue runtime.registers slot <
          capacity) :
      PrimitiveSafe capacity source context
        (.incrementRegister counter) runtime
        { runtime with
          registers :=
            TargetEmitterRuntimePrimitives.incrementRegisters
              slot runtime.registers }

theorem PrimitiveSafe.step_eq
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitive : Primitive} {initial final : Runtime}
    (safe :
      PrimitiveSafe capacity source context
        primitive initial final) :
    TargetEmitterProgramSemantics.step primitive initial =
      some (.accepted final) := by
  cases safe with
  | appendPlain =>
      rfl
  | appendMarked =>
      rfl
  | resetScratch =>
      rfl
  | addRegister runtime counter slot slotEq _fits _enough =>
      simp only [TargetEmitterProgramSemantics.step]
      cases counter <;> cases slot <;>
        simp [addCounter, counterSlot, registerValue,
          TargetEmitterLedger.slotValue] at slotEq ⊢
  | reloadCaptured =>
      rfl
  | incrementScratch =>
      rfl
  | emitScratchNatPlain =>
      rfl
  | emitScratchNatMarked =>
      rfl
  | pushCheck =>
      rfl
  | popCheck runtime prior value _fits _scratchZero checksEq =>
      simp [step, checksEq, popNewest_append_singleton]
  | compareRegister runtime counter slot slotEq _fits equal =>
      simp only [TargetEmitterProgramSemantics.step]
      rw [registerValue_eq_slotValue
        _ _ _ slotEq]
      simp [equal]
  | incrementRegister
      runtime counter slot slotEq _fits _available =>
      simp only [TargetEmitterProgramSemantics.step]
      rw [incrementRegister_eq_incrementRegisters
        _ _ _ slotEq]

inductive ProgramSafe
    (capacity : Nat) (source : List WorkSymbol)
    (context : SourceContext source) :
    List Primitive → Runtime → Runtime → Prop where
  | nil (runtime : Runtime) :
      ProgramSafe capacity source context [] runtime runtime
  | cons
      (primitive : Primitive) (rest : List Primitive)
      (initial middle final : Runtime)
      (head :
        PrimitiveSafe capacity source context
          primitive initial middle)
      (tail :
        ProgramSafe capacity source context rest middle final) :
      ProgramSafe capacity source context
        (primitive :: rest) initial final

theorem ProgramSafe.run_eq
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitives : List Primitive} {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context
        primitives initial final) :
    TargetEmitterProgramSemantics.run primitives initial =
      some (.accepted final) := by
  induction safe with
  | nil =>
      rfl
  | cons primitive rest initial middle final head tail ih =>
      simp only [TargetEmitterProgramSemantics.run,
        PrimitiveSafe.step_eq head]
      exact ih

/-! ### Exact lifting of compiled primitives -/

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

/-- Every safe primitive is realized by the exact literal machine selected
by `primitiveMachine`.  The witnesses are step counts and finite tape
windows only; no safety evidence is compiled into the machine. -/
theorem PrimitiveSafe.exact
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitive : Primitive} {initial final : Runtime}
    (safe :
      PrimitiveSafe capacity source context
        primitive initial final)
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
        source final.targetTokens actualFinal := by
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
      exact ⟨_, actualFinal, exactRun, finalRepresents⟩
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
      refine ⟨_, actualFinal, exactRun, ?_⟩
      simpa only [TargetEmitterCursorAppender.machineFor,
        ← layout.cursorSource] using finalRepresents
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
      refine ⟨_, actualFinal, exactRun, ?_⟩
      simpa only [TargetEmitterScratchReset.machine,
        ← context.source_eq] using finalRepresents
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
      refine ⟨_, actualFinal, exactRun, ?_⟩
      simpa only [TargetEmitterScratchAddSlot.machineFor,
        ← context.source_eq] using finalRepresents
  | reloadCaptured
      runtime layout scratchZero capturedEq valueBound =>
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
      refine ⟨_, actualFinal, exactRun, ?_⟩
      simpa [TargetEmitterMarkedSourceReload.machine,
        scratchZero, capturedEq, ← layout.reloadSource] using
        finalRepresents
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
      refine ⟨_, actualFinal, exactRun, ?_⟩
      simpa only [TargetEmitterScratchIncrement.machine,
        ← context.source_eq] using finalRepresents
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
      refine ⟨_, actualFinal, exactRun, ?_⟩
      simpa only [TargetEmitterNatLoop.machine,
        ← context.source_eq] using finalRepresents
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
      refine ⟨_, actualFinal, exactRun, ?_⟩
      simpa only [TargetEmitterCursorNatLoop.machine,
        ← cursorSource] using finalRepresents
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
      refine ⟨_, actualFinal, exactRun, ?_⟩
      simpa only [TargetEmitterCheckStack.Push.machine,
        TargetEmitterCheckStack.machineOf,
        ← context.source_eq] using finalRepresents
  | popCheck
      runtime prior value fits scratchZero checksEq valueBound =>
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
      refine ⟨_, actualFinal, exactRun, ?_⟩
      simpa only [TargetEmitterCheckStack.Pop.machine,
        TargetEmitterCheckStack.machineOf,
        ← context.source_eq] using finalRepresents
  | compareRegister
      runtime counter slot slotEq fits equal =>
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
      refine ⟨_, actualFinal, exactRun, ?_⟩
      simpa only [TargetEmitterScratchCompareSlot.machineFor,
        ← context.source_eq] using finalRepresents
  | incrementRegister
      runtime counter slot slotEq fits available =>
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
      refine ⟨_, actualFinal, exactRun, ?_⟩
      simpa only [TargetEmitterSlotIncrement.machineFor,
        ← context.source_eq] using finalRepresents

/-! ### Exact compiled program runs -/

/-- State at which the first compiled primitive starts.  `fallback` is used
only for the empty program. -/
def entryState (fallback : Nat) : List WorkMachine → Nat
  | [] => fallback
  | program :: _ => program.startState

/-- Accept state of the last compiled primitive.  For an empty program the
supplied state is retained. -/
def exitState (fallback : Nat) : List WorkMachine → Nat
  | [] => fallback
  | program :: rest => exitState program.acceptState rest

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
          refine
            ⟨program, tailPrograms, rfl, rfl, ?_⟩
          simp only [compileProgram, machineEq, tailEq] at compiled
          exact (Option.some.inj compiled).symm

/-- A safe pure program and a successful primitive compilation determine one
exact accepting run through every literal machine in order.  The single step
between adjacent local runs is the already-materialized graph bridge counted
by `LinearAcceptRuns`; it is not a host-side primitive dispatch. -/
theorem ProgramSafe.linearAcceptRuns_exact
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitives : List Primitive} {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context
        primitives initial final)
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
        source final.targetTokens actualFinal := by
  induction safe generalizing programs fallback actual with
  | nil runtime =>
      change some [] = some programs at compiled
      have programsEq : programs = [] :=
        (Option.some.inj compiled).symm
      subst programs
      exact
        ⟨0, actual, LinearAcceptRuns.terminal actual.tape,
          represents⟩
  | cons primitive rest initial middle final head tail
      inductionHypothesis =>
      rcases compileProgram_cons_inv compiled with
        ⟨program, tailPrograms, headCompiled,
          tailCompiled, programsEq⟩
      subst programs
      rcases
          head.exact program headCompiled actual represents with
        ⟨localSteps, middleActual, localRun,
          middleRepresents⟩
      let tailActual : WorkConfiguration :=
        { state := entryState program.acceptState tailPrograms
          tape := middleActual.tape }
      have tailRepresents :
          TargetEmitterRuntime.Represents
            (entryState program.acceptState tailPrograms)
            capacity middle.scratch middle.registers middle.checks
            source middle.targetTokens tailActual := by
        exact represents_at_state middleRepresents
      rcases
          inductionHypothesis tailPrograms tailCompiled
            program.acceptState tailActual tailRepresents with
        ⟨tailSteps, actualFinal, tailRuns, finalRepresents⟩
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
          finalRepresents⟩
      exact
        LinearAcceptRuns.step program tailPrograms
          localSteps tailSteps actual.tape middleActual.tape
          actualFinal.tape localRun' tailRuns

/-- Feed a safe compiled program directly into one fixed materialized
controller descriptor.  Descriptor membership and nonemptiness remain
explicit structural premises. -/
theorem ProgramSafe.descriptor_acceptPath_exact
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (descriptor : TargetEmitterController.BlockDescriptor)
    (descriptorMember :
      descriptor ∈ TargetEmitterController.blockDescriptors)
    {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context
        descriptor.primitives initial final)
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
        source final.targetTokens actualFinal := by
  rcases
      safe.linearAcceptRuns_exact programs compiled fallback actual
        represents with
    ⟨steps, actualFinal, runs, finalRepresents⟩
  exact
    ⟨steps, actualFinal,
      TargetEmitterController.descriptor_acceptPath_of_compiled
        descriptor descriptorMember programs compiled programsNonempty
        steps actual.tape actualFinal.tape runs,
      finalRepresents⟩

end PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgram

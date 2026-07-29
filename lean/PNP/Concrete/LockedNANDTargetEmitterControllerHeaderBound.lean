/-
Copyright (c) 2026 PNP Labs.

Constructive work bounds for the closed header phase of the grammar-only
locked-NAND target emitter.

This module is the first bounded controller layer above
`LockedNANDTargetEmitterRuntimeProgramBound`.  It deliberately rebuilds the
small header descriptor wrapper rather than changing the exact trace module.
The executable graph remains fixed, and no caller schedule or decoder
certificate is introduced.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerHeaderTrace
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramBound

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerHeaderBound

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController
open TargetEmitterPrimitiveCompiler
open TargetEmitterBlockCompiler
open TargetEmitterPlan

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev TapeRepresents :=
  TargetEmitterControllerHeaderTrace.TapeRepresents

private def headerDescriptor : BlockDescriptor :=
  { code := Block.header
    primitives := Plan.header
    continuation := .node headerNavigatorRef }

private def headerPrograms : List WorkMachine :=
  (compileProgram Plan.header).getD []

private theorem headerDescriptor_member :
    headerDescriptor ∈ blockDescriptors := by
  simp [headerDescriptor, blockDescriptors, fixedBlockDescriptors]

private theorem header_compiled :
    compileProgram Plan.header = some headerPrograms := by
  rfl

private theorem headerPrograms_nonempty :
    headerPrograms ≠ [] := by
  decide

private theorem header_startState :
    headerRef.startState =
      TargetEmitterRuntimeProgram.entryState 0 headerPrograms := by
  rfl

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

private def canonicalSourceContext
    (raw : RawCircuit) :
    TargetEmitterRuntimeProgram.SourceContext
      (SourceParser.circuitCells raw) := by
  cases sourceEq : SourceParser.circuitCells raw with
  | nil =>
      exact False.elim
        (SourceParser.circuitCells_ne_empty raw sourceEq)
  | cons head tail =>
      exact
        { head := head
          tail := tail
          source_eq := rfl
          allowed := Or.inl <|
            TargetEmitter.circuitCells_packed raw head <| by
              rw [sourceEq]
              exact List.Mem.head tail }

private theorem initial_captured_bound
    (raw : RawCircuit) :
    (TargetEmitterControllerHeaderTrace.initialRuntime raw).captured + 1 ≤
      (SourceParser.circuitCells raw).length := by
  have cells :=
    TargetEmitterCapacity.fourteen_le_circuitCells_length raw
  simp only [TargetEmitterControllerHeaderTrace.initialRuntime]
  omega

private theorem initial_scratch_bound
    (raw : RawCircuit) :
    (TargetEmitterControllerHeaderTrace.initialRuntime raw).scratch <
      TargetEmitterLedger.slotCapacity raw := by
  have reserve :=
    TargetEmitterCapacity.baseline_add_sixtyFour_le_slotCapacity raw
  simp only [TargetEmitterControllerHeaderTrace.initialRuntime]
  omega

private theorem header_program_length :
    Plan.header.length = 15 := by
  decide

/-- Quadratic primitive-program envelope for the one fixed header block. -/
def headerBlockEnvelope (raw : RawCircuit) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (TargetEmitterLedger.slotCapacity raw)
    (SourceParser.circuitCells raw)
    (TargetEmitterControllerHeaderTrace.initialRuntime raw)
    Plan.header

/-- The initialized stack phase plus the bounded header block. -/
def stackHeaderEnvelope (raw : RawCircuit) : Nat :=
  TargetEmitterCheckStack.Initialize.workSteps
      (TargetEmitterLedger.slotCapacity raw) + 1 +
    headerBlockEnvelope raw

/-- Linear footprint majorant for the header block, expressed directly in
the encoded bit length. -/
def headerFootprintPolynomial : NatPolynomial :=
  NatPolynomial.linear 2945 2990

/-- Quadratic work polynomial for the fixed header primitive program. -/
def headerBlockTimePolynomial : NatPolynomial :=
  .mul (.constant 15)
    (.add
      (.mul (.constant 100)
        (.mul headerFootprintPolynomial headerFootprintPolynomial))
      (.constant 101))

/-- Polynomial for empty-stack initialization, its bridge, and the complete
header primitive program. -/
def stackHeaderTimePolynomial : NatPolynomial :=
  .add (NatPolynomial.linear 896 931) headerBlockTimePolynomial

theorem headerFootprintPolynomial_eval (bitLength : Nat) :
    headerFootprintPolynomial.eval bitLength =
      2945 * bitLength + 2990 := by
  simp [headerFootprintPolynomial, NatPolynomial.linear]

theorem headerBlockTimePolynomial_eval (bitLength : Nat) :
    headerBlockTimePolynomial.eval bitLength =
      15 *
        (100 *
          ((2945 * bitLength + 2990) *
            (2945 * bitLength + 2990)) +
          101) := by
  simp [headerBlockTimePolynomial, headerFootprintPolynomial_eval]

theorem stackHeaderTimePolynomial_eval (bitLength : Nat) :
    stackHeaderTimePolynomial.eval bitLength =
      896 * bitLength + 931 +
        15 *
          (100 *
            ((2945 * bitLength + 2990) *
              (2945 * bitLength + 2990)) +
            101) := by
  simp [stackHeaderTimePolynomial, NatPolynomial.linear,
    headerBlockTimePolynomial_eval]

private theorem runtimeFootprint_le_headerPolynomial
    (raw : RawCircuit) :
    TargetEmitterRuntimeProgramBound.runtimeFootprint
        (TargetEmitterLedger.slotCapacity raw)
        (SourceParser.circuitCells raw)
        (TargetEmitterControllerHeaderTrace.initialRuntime raw)
        Plan.header.length ≤
      headerFootprintPolynomial.eval (encodeCircuit raw).length := by
  have encodedLength := SourceParser.encodeCircuit_length_eq raw
  simp only [TargetEmitterRuntimeProgramBound.runtimeFootprint,
    TargetEmitterControllerHeaderTrace.initialRuntime,
    List.length_nil, Nat.mul_zero,
    TargetEmitterRuntimeProgramBound.checkCells,
    TargetEmitterCheckStack.recordsWord, List.flatMap_nil,
    TargetEmitterLedger.slotCapacity, header_program_length,
    headerFootprintPolynomial_eval]
  omega

theorem headerBlockEnvelope_le_timePolynomial
    (raw : RawCircuit) :
    headerBlockEnvelope raw ≤
      headerBlockTimePolynomial.eval (encodeCircuit raw).length := by
  have footprintBound :=
    runtimeFootprint_le_headerPolynomial raw
  have squareBound :
      TargetEmitterRuntimeProgramBound.runtimeFootprint
          (TargetEmitterLedger.slotCapacity raw)
          (SourceParser.circuitCells raw)
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)
          Plan.header.length *
        TargetEmitterRuntimeProgramBound.runtimeFootprint
          (TargetEmitterLedger.slotCapacity raw)
          (SourceParser.circuitCells raw)
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)
          Plan.header.length ≤
      headerFootprintPolynomial.eval (encodeCircuit raw).length *
        headerFootprintPolynomial.eval (encodeCircuit raw).length :=
    Nat.mul_le_mul footprintBound footprintBound
  have primitiveBound :
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
          (TargetEmitterRuntimeProgramBound.runtimeFootprint
            (TargetEmitterLedger.slotCapacity raw)
            (SourceParser.circuitCells raw)
            (TargetEmitterControllerHeaderTrace.initialRuntime raw)
            Plan.header.length) + 1 ≤
        100 *
            (headerFootprintPolynomial.eval (encodeCircuit raw).length *
              headerFootprintPolynomial.eval
                (encodeCircuit raw).length) +
          101 := by
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    have scaled := Nat.mul_le_mul_left 100 squareBound
    omega
  have blockBound :=
    Nat.mul_le_mul_left Plan.header.length primitiveBound
  simpa [headerBlockEnvelope,
    TargetEmitterRuntimeProgramBound.programWorkEnvelope,
    headerBlockTimePolynomial, header_program_length] using blockBound

theorem stackHeaderEnvelope_le_timePolynomial
    (raw : RawCircuit) :
    stackHeaderEnvelope raw ≤
      stackHeaderTimePolynomial.eval (encodeCircuit raw).length := by
  have encodedLength := SourceParser.encodeCircuit_length_eq raw
  have stackBound :
      TargetEmitterCheckStack.Initialize.workSteps
          (TargetEmitterLedger.slotCapacity raw) + 1 ≤
        (NatPolynomial.linear 896 931).eval
          (encodeCircuit raw).length := by
    simp only [TargetEmitterCheckStack.Initialize.workSteps,
      TargetEmitterLedger.slotCapacity, NatPolynomial.linear,
      NatPolynomial.eval_add, NatPolynomial.eval_mul,
      NatPolynomial.eval_constant, NatPolynomial.eval_variable]
    omega
  have headerBound := headerBlockEnvelope_le_timePolynomial raw
  simpa [stackHeaderEnvelope, stackHeaderTimePolynomial] using
    Nat.add_le_add stackBound headerBound

/-- Drop-in bounded form of the exact header block trace from any represented
header-entry tape. -/
theorem headerBlock_path_of_represents_bounded
    (raw : RawCircuit) (initialTape : WorkTape)
    (represents :
      TapeRepresents headerRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterControllerHeaderTrace.initialRuntime raw).scratch
        (TargetEmitterControllerHeaderTrace.initialRuntime raw).registers
        (TargetEmitterControllerHeaderTrace.initialRuntime raw).checks
        (SourceParser.circuitCells raw)
        (TargetEmitterControllerHeaderTrace.initialRuntime raw).targetTokens
        initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node headerRef)
          (.node headerNavigatorRef) steps initialTape finalTape ∧
      TapeRepresents headerNavigatorRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).scratch
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).registers
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks
        (SourceParser.circuitCells raw)
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens
        finalTape ∧
      steps ≤ headerBlockEnvelope raw := by
  let initial : WorkConfiguration :=
    { state :=
        TargetEmitterRuntimeProgram.entryState 0 headerPrograms
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initial.state
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterControllerHeaderTrace.initialRuntime raw).scratch
        (TargetEmitterControllerHeaderTrace.initialRuntime raw).registers
        (TargetEmitterControllerHeaderTrace.initialRuntime raw).checks
        (SourceParser.circuitCells raw)
        (TargetEmitterControllerHeaderTrace.initialRuntime raw).targetTokens
        initial := by
    have atEntry :
        TapeRepresents
          (TargetEmitterRuntimeProgram.entryState 0 headerPrograms)
          (TargetEmitterLedger.slotCapacity raw)
          (TargetEmitterControllerHeaderTrace.initialRuntime raw).scratch
          (TargetEmitterControllerHeaderTrace.initialRuntime raw).registers
          (TargetEmitterControllerHeaderTrace.initialRuntime raw).checks
          (SourceParser.circuitCells raw)
          (TargetEmitterControllerHeaderTrace.initialRuntime raw).targetTokens
          initialTape := by
      rw [← header_startState]
      exact represents
    exact atEntry
  have safe :=
    TargetEmitterRuntimeProgramSafety.header_safe
      (canonicalSourceContext raw)
      (TargetEmitter.circuitCells_packed raw)
      (TargetEmitterCapacity.initialControllerRange raw)
      (initial_captured_bound raw)
      (initial_scratch_bound raw)
  have scratchBound :
      (TargetEmitterControllerHeaderTrace.initialRuntime raw).scratch ≤
        TargetEmitterLedger.slotCapacity raw := by
    have strict := initial_scratch_bound raw
    omega
  rcases
      TargetEmitterRuntimeProgramBound.ProgramSafe.descriptor_acceptPath_bounded
        headerDescriptor headerDescriptor_member safe scratchBound
        headerPrograms
        (by simpa [headerDescriptor] using header_compiled)
        headerPrograms_nonempty 0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents, bound⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_, ?_⟩
  · simpa [headerDescriptor, headerRef] using path
  · exact
      represents_at_state
        (newState := headerNavigatorRef.startState)
        finalRepresents
  · simpa [headerBlockEnvelope, headerDescriptor] using bound

/-- Closed bounded header phase from the canonical stack-initialization
endpoint. -/
theorem stack_header_path_bounded
    (raw : RawCircuit) :
    ∃ steps finalTape,
      AcceptPath graph (.node stackInitializeRef)
          (.node headerNavigatorRef) steps
          (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      TapeRepresents headerNavigatorRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).scratch
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).registers
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks
        (SourceParser.circuitCells raw)
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens
        finalTape ∧
      steps ≤ stackHeaderEnvelope raw := by
  rcases
      TargetEmitterControllerInitialTrace.stack_initialize_path raw with
    ⟨entryActual, stackPath, entryRepresents⟩
  have atHeader :
      TapeRepresents headerRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterControllerHeaderTrace.initialRuntime raw).scratch
        (TargetEmitterControllerHeaderTrace.initialRuntime raw).registers
        (TargetEmitterControllerHeaderTrace.initialRuntime raw).checks
        (SourceParser.circuitCells raw)
        (TargetEmitterControllerHeaderTrace.initialRuntime raw).targetTokens
        entryActual.tape := by
    change TargetEmitterRuntime.Represents headerRef.startState
      (TargetEmitterLedger.slotCapacity raw)
      (TargetEmitterControllerHeaderTrace.initialRuntime raw).scratch
      (TargetEmitterControllerHeaderTrace.initialRuntime raw).registers
      (TargetEmitterControllerHeaderTrace.initialRuntime raw).checks
      (SourceParser.circuitCells raw)
      (TargetEmitterControllerHeaderTrace.initialRuntime raw).targetTokens
      { state := headerRef.startState, tape := entryActual.tape }
    exact
      (represents_at_state
        (newState := headerRef.startState) entryRepresents)
  rcases
      headerBlock_path_of_represents_bounded
        raw entryActual.tape atHeader with
    ⟨blockSteps, finalTape, blockPath, finalRepresents, blockBound⟩
  let steps :=
    TargetEmitterCheckStack.Initialize.workSteps
        (TargetEmitterLedger.slotCapacity raw) + 1 +
      blockSteps
  refine ⟨steps, finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node stackInitializeRef)
        (.node headerRef) (.node headerNavigatorRef)
        (TargetEmitterCheckStack.Initialize.workSteps
          (TargetEmitterLedger.slotCapacity raw) + 1)
        blockSteps _ _ _ stackPath blockPath
  · unfold steps stackHeaderEnvelope
    omega

/-- Closed header execution with its bound stated directly as a polynomial in
the encoded input length. -/
theorem stack_header_path_polynomial
    (raw : RawCircuit) :
    ∃ steps finalTape,
      AcceptPath graph (.node stackInitializeRef)
          (.node headerNavigatorRef) steps
          (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      TapeRepresents headerNavigatorRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).scratch
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).registers
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks
        (SourceParser.circuitCells raw)
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens
        finalTape ∧
      steps ≤
        stackHeaderTimePolynomial.eval (encodeCircuit raw).length := by
  rcases stack_header_path_bounded raw with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape, path, finalRepresents,
      Nat.le_trans bound (stackHeaderEnvelope_le_timePolynomial raw)⟩

/-! ### Bounded literal header navigation -/

/-- Closed envelope for initialization, the header primitive block, and the
literal header navigator. -/
def stackHeaderNavigatorEnvelope (raw : RawCircuit) : Nat :=
  stackHeaderEnvelope raw +
    (TargetEmitterNavigator.headerWorkSteps
      raw.inputCount raw.gates.length + 1)

private theorem represented_tape_blankEquivalent
    {state capacity scratch : Nat}
    {registers : TargetEmitter.UnaryRegisters}
    {checks : List Nat} {source : List WorkSymbol}
    {target : List Token} {tape : WorkTape}
    (represents :
      TapeRepresents state capacity scratch registers checks
        source target tape) :
    WorkTape.BlankEquivalent tape
      (TargetEmitterRuntime.logicalTape capacity scratch registers
        checks source target) := by
  simpa only [TapeRepresents,
    TargetEmitterRuntime.logicalConfiguration_tape] using
    represents.tape

/-- Bounded initialized header path for a nonempty literal gate list. -/
theorem stack_header_nonempty_path_bounded
    (inputs : Nat) (gate : RawGate)
    (gates : List RawGate) (output : RawSource) :
    let raw : RawCircuit :=
      { inputCount := inputs
        gates := gate :: gates
        output := output }
    let afterHeader :=
      TargetEmitterProgramSemantics.headerResult
        (TargetEmitterControllerHeaderTrace.initialRuntime raw)
    ∃ steps finalTape,
      AcceptPath graph (.node stackInitializeRef) (.node leftFirstRef)
          steps
          (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      WorkTape.BlankEquivalent finalTape
        (TargetEmitterControllerTrace.sourceFocusTape
          ((TargetEmitterControllerTrace.circuitHeaderCells
                inputs (gate :: gates).length).reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              (TargetEmitterLedger.slotCapacity raw)
              afterHeader.scratch afterHeader.registers
              afterHeader.checks)
          gate.left
          (SourceParser.sourceCells gate.right ++
            [SourceParser.cell01, SourceParser.cell11] ++
            SourceParser.gateListCells gates ++
            TargetEmitterControllerTrace.circuitFooterCells output ++
            TargetEmitter.sourceTargetBoundary ::
              SourceParser.packedTokenCells
                afterHeader.targetTokens)) ∧
      steps ≤ stackHeaderNavigatorEnvelope raw := by
  dsimp only
  let raw : RawCircuit :=
    { inputCount := inputs
      gates := gate :: gates
      output := output }
  let afterHeader :=
    TargetEmitterProgramSemantics.headerResult
      (TargetEmitterControllerHeaderTrace.initialRuntime raw)
  rcases stack_header_path_bounded raw with
    ⟨headerSteps, headerTape, headerPath,
      represents, headerBound⟩
  have canonicalPath :=
    TargetEmitterControllerTrace.header_nonempty_path
      (TargetEmitterLedger.slotCapacity raw)
      afterHeader.scratch afterHeader.registers afterHeader.checks
      afterHeader.targetTokens inputs gate gates output
  have inputEquivalent :
      WorkTape.BlankEquivalent headerTape
        (TargetEmitterRuntime.logicalTape
          (TargetEmitterLedger.slotCapacity raw)
          afterHeader.scratch afterHeader.registers
          afterHeader.checks
          (SourceParser.circuitCells raw)
          afterHeader.targetTokens) := by
    exact represented_tape_blankEquivalent represents
  rcases canonicalPath.transport inputEquivalent with
    ⟨finalTape, navigationPath, finalEquivalent⟩
  let navigationSteps :=
    TargetEmitterNavigator.headerWorkSteps
      inputs (gate :: gates).length + 1
  refine
    ⟨headerSteps + navigationSteps, finalTape, ?_,
      finalEquivalent, ?_⟩
  · exact
      AcceptPath.trans graph (.node stackInitializeRef)
        (.node headerNavigatorRef) (.node leftFirstRef)
        headerSteps navigationSteps _ _ _
        headerPath (by simpa [navigationSteps] using navigationPath)
  · unfold stackHeaderNavigatorEnvelope navigationSteps
    simpa [raw] using
      Nat.add_le_add_right headerBound
        (TargetEmitterNavigator.headerWorkSteps
          inputs (gate :: gates).length + 1)

/-- Bounded initialized header path for an empty literal gate list. -/
theorem stack_header_empty_path_bounded
    (inputs : Nat) (output : RawSource) :
    let raw : RawCircuit :=
      { inputCount := inputs
        gates := []
        output := output }
    let afterHeader :=
      TargetEmitterProgramSemantics.headerResult
        (TargetEmitterControllerHeaderTrace.initialRuntime raw)
    ∃ steps finalTape,
      AcceptPath graph (.node stackInitializeRef) (.node programEndRef)
          steps
          (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      WorkTape.BlankEquivalent finalTape
        (TargetEmitterControllerTrace.programEndFocusTape
          ((TargetEmitterControllerTrace.circuitHeaderCells
                inputs 0).reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              (TargetEmitterLedger.slotCapacity raw)
              afterHeader.scratch afterHeader.registers
              afterHeader.checks)
          output afterHeader.targetTokens) ∧
      steps ≤ stackHeaderNavigatorEnvelope raw := by
  dsimp only
  let raw : RawCircuit :=
    { inputCount := inputs
      gates := []
      output := output }
  let afterHeader :=
    TargetEmitterProgramSemantics.headerResult
      (TargetEmitterControllerHeaderTrace.initialRuntime raw)
  rcases stack_header_path_bounded raw with
    ⟨headerSteps, headerTape, headerPath,
      represents, headerBound⟩
  have canonicalPath :=
    TargetEmitterControllerTrace.header_empty_path
      (TargetEmitterLedger.slotCapacity raw)
      afterHeader.scratch afterHeader.registers afterHeader.checks
      afterHeader.targetTokens inputs output
  have inputEquivalent :
      WorkTape.BlankEquivalent headerTape
        (TargetEmitterRuntime.logicalTape
          (TargetEmitterLedger.slotCapacity raw)
          afterHeader.scratch afterHeader.registers
          afterHeader.checks
          (SourceParser.circuitCells raw)
          afterHeader.targetTokens) := by
    exact represented_tape_blankEquivalent represents
  rcases canonicalPath.transport inputEquivalent with
    ⟨finalTape, navigationPath, finalEquivalent⟩
  let navigationSteps :=
    TargetEmitterNavigator.headerWorkSteps inputs 0 + 1
  refine
    ⟨headerSteps + navigationSteps, finalTape, ?_,
      finalEquivalent, ?_⟩
  · exact
      AcceptPath.trans graph (.node stackInitializeRef)
        (.node headerNavigatorRef) (.node programEndRef)
        headerSteps navigationSteps _ _ _
        headerPath (by simpa [navigationSteps] using navigationPath)
  · unfold stackHeaderNavigatorEnvelope navigationSteps
    simpa [raw] using
      Nat.add_le_add_right headerBound
        (TargetEmitterNavigator.headerWorkSteps inputs 0 + 1)

end PNP.Concrete.LockedNAND.TargetEmitterControllerHeaderBound

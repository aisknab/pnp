/-
Copyright (c) 2026 PNP Labs.

Exact accepting traces for the fixed canonical CNF-to-NAND controller.

The executable graph is the one materialized in `CNFToNANDController`.
Formulae, source splits, semantic runtimes, and path witnesses in this file
are proof-only indices.  They are never supplied to the work machine and are
not used to select a rule or a successor at runtime.
-/

import PNP.Concrete.CNFToNANDController
import PNP.Concrete.CNFToNANDWorkspace
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgram
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramSafety
import PNP.Concrete.WorkMachineProgramPathBlankEquivalence

namespace PNP.Concrete.CNFToNANDControllerCanonicalTrace

open PNP.Concrete
open PNP.Concrete.LockedNAND
open PNP.Concrete.LockedNAND.TargetEmitterPlan
open PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler
open PNP.Concrete.LockedNAND.TargetEmitterBlockCompiler
open PNP.Concrete.LockedNAND.TargetEmitterProgramSemantics
open PNP.Concrete.WorkMachineProgramGraph
open PNP.Concrete.WorkMachineProgramPath
open PNP.Concrete.CNFToNANDController
open PNP.Concrete.CNFToNANDControllerBlocks

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Runtime :=
  PNP.Concrete.LockedNAND.TargetEmitterProgramSemantics.Runtime

abbrev SourceContext :=
  PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgram.SourceContext

abbrev CursorLayout :=
  PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgram.CursorLayout

abbrev ProgramSafe :=
  PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgram.ProgramSafe

def TapeRepresents (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (tape : WorkTape) : Prop :=
  TargetEmitterRuntime.Represents state capacity scratch registers
    checks source target { state := state, tape := tape }

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

/-! ## Literal graph-node lifting -/

private theorem controlNode_member
    (code : Nat) (program : WorkMachine)
    (onAccept onReject : Endpoint)
    (member :
      controlNode code program onAccept onReject ∈ controlNodes) :
    controlNode code program onAccept onReject ∈ graph.nodes := by
  exact controlNode_member_nodes _ member

private theorem localAccept_path
    (code : Nat) (program : WorkMachine)
    (onAccept onReject finalEndpoint : Endpoint)
    (localSteps tailSteps : Nat)
    (initialTape middleTape finalTape : WorkTape)
    (member :
      controlNode code program onAccept onReject ∈ controlNodes)
    (run :
      workRunExact? program localSteps
          { state := program.startState, tape := initialTape } =
        some
          { state := program.acceptState, tape := middleTape })
    (tail :
      AcceptPath graph onAccept finalEndpoint tailSteps
        middleTape finalTape) :
    AcceptPath graph
      (.node (controlRef code program)) finalEndpoint
      (localSteps + 1 + tailSteps) initialTape finalTape := by
  have path :=
    AcceptPath.step
      (controlNode code program onAccept onReject)
      finalEndpoint localSteps tailSteps initialTape middleTape
      finalTape (controlNode_member code program onAccept onReject member)
      (by simpa [LocalAcceptRun, controlNode] using run) tail
  simpa [controlNode, controlRef, Node.reference] using path

private theorem localReject_path
    (code : Nat) (program : WorkMachine)
    (onAccept onReject finalEndpoint : Endpoint)
    (localSteps tailSteps : Nat)
    (initialTape middleTape finalTape : WorkTape)
    (member :
      controlNode code program onAccept onReject ∈ controlNodes)
    (run :
      workRunExact? program localSteps
          { state := program.startState, tape := initialTape } =
        some
          { state := program.rejectState, tape := middleTape })
    (tail :
      AcceptPath graph onReject finalEndpoint tailSteps
        middleTape finalTape) :
    AcceptPath graph
      (.node (controlRef code program)) finalEndpoint
      (localSteps + 1 + tailSteps) initialTape finalTape := by
  have path :=
    AcceptPath.stepReject
      (controlNode code program onAccept onReject)
      finalEndpoint localSteps tailSteps initialTape middleTape
      finalTape (controlNode_member code program onAccept onReject member)
      (by simpa [LocalRejectRun, controlNode] using run) tail
  simpa [controlNode, controlRef, Node.reference] using path

/-! ## Closed-block lifting for this controller graph -/

theorem materializedBlock_path
    (descriptor : BlockDescriptor)
    (descriptorMember : descriptor ∈ blockDescriptors)
    (programs : List WorkMachine)
    (compiled :
      compileProgram descriptor.primitives = some programs)
    (programsNonempty : programs ≠ [])
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context
        descriptor.primitives initial final)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents
        (TargetEmitterRuntimeProgram.entryState 0 programs)
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
          (.node
            (blockEntry descriptor.code descriptor.primitives))
          descriptor.continuation steps initialTape finalTape ∧
      TargetEmitterRuntime.Represents
        (TargetEmitterRuntimeProgram.exitState 0 programs)
        capacity final.scratch final.registers final.checks
        source final.targetTokens
        { state :=
            TargetEmitterRuntimeProgram.exitState 0 programs
          tape := finalTape } := by
  let initialActual : WorkConfiguration :=
    { state := TargetEmitterRuntimeProgram.entryState 0 programs
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initialActual.state
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens initialActual := by
    exact represents
  rcases
      safe.linearAcceptRuns_exact programs compiled 0 initialActual
        inputRepresents with
    ⟨steps, actualFinal, runs, finalRepresents⟩
  have included :
      ∀ node,
        node ∈
            blockNodes descriptor.code descriptor.primitives
              descriptor.continuation →
          node ∈ graph.nodes := by
    intro node nodeMember
    exact descriptorBlockNode_member_nodes descriptor descriptorMember
      node nodeMember
  have rawPath :=
    blockNodes_acceptPath_of_compiled graph descriptor.code
      descriptor.primitives programs descriptor.continuation steps
      initialTape actualFinal.tape compiled included runs
  have entryEq :=
    blockEntry_eq_entryEndpoint_of_compiled descriptor.code
      descriptor.primitives programs descriptor.continuation
      compiled programsNonempty
  refine ⟨steps, actualFinal.tape, ?_, ?_⟩
  · rw [← entryEq] at rawPath
    exact rawPath
  · exact represents_at_state finalRepresents

/-! ## Scanner and ledger prefix -/

private theorem scannerNode_member :
    scannerNode ∈ graph.nodes := by
  change scannerNode ∈ nodes
  apply controlNode_member_nodes scannerNode
  exact List.Mem.head _

private theorem ledgerNode_member :
    ledgerNode ∈ graph.nodes := by
  change ledgerNode ∈ nodes
  apply controlNode_member_nodes ledgerNode
  exact List.Mem.tail _ (List.Mem.head _)

/-- Exact grammar-scanner segment for the canonical inert carrier. -/
theorem scanner_path (formula : CNFFormula) :
    AcceptPath graph (.node scannerRef) (.node ledgerRef)
      (TargetEmitterGrammarScanner.canonicalSteps
          (CNFToNANDWorkspace.carrierCircuit formula) + 1)
      (rawInputWorkTape
        (encodeCircuit
          (CNFToNANDWorkspace.carrierCircuit formula)))
      (TargetEmitterGrammarScanner.acceptedConfiguration
        (CNFToNANDWorkspace.carrierCircuit formula)).tape := by
  let raw := CNFToNANDWorkspace.carrierCircuit formula
  have localRun :
      LocalAcceptRun scannerNode
        (TargetEmitterGrammarScanner.canonicalSteps raw)
        (rawInputWorkTape (encodeCircuit raw))
        (TargetEmitterGrammarScanner.acceptedConfiguration raw).tape := by
    simpa [LocalAcceptRun, scannerNode, controlNode,
      workStartConfiguration,
      TargetEmitterGrammarScanner.acceptedConfiguration] using
      TargetEmitterGrammarScanner.canonical_exact raw
  have tail :
      AcceptPath graph (.node ledgerRef) (.node ledgerRef) 0
        (TargetEmitterGrammarScanner.acceptedConfiguration raw).tape
        (TargetEmitterGrammarScanner.acceptedConfiguration raw).tape :=
    .terminal _ _
  have path :=
    AcceptPath.step scannerNode (.node ledgerRef)
      (TargetEmitterGrammarScanner.canonicalSteps raw) 0
      _ _ _ scannerNode_member localRun tail
  simpa [raw, scannerNode, scannerRef, controlNode, controlRef,
    Node.reference] using path

/-- Exact source-ledger segment, retaining the complete canonical carrier. -/
theorem ledger_path (formula : CNFFormula) :
    AcceptPath graph (.node ledgerRef) (.node stackInitializeRef)
      (TargetEmitterLedger.workSteps
          (CNFToNANDWorkspace.carrierCircuit formula) + 1)
      (TargetEmitterGrammarScanner.acceptedConfiguration
        (CNFToNANDWorkspace.carrierCircuit formula)).tape
      (CNFToNANDWorkspace.postLedgerConfiguration formula).tape := by
  let raw := CNFToNANDWorkspace.carrierCircuit formula
  have localRun :
      LocalAcceptRun ledgerNode
        (TargetEmitterLedger.workSteps raw)
        (TargetEmitterGrammarScanner.acceptedConfiguration raw).tape
        (TargetEmitterLedger.finalConfiguration raw).tape := by
    unfold LocalAcceptRun
    change
      workRunExact? TargetEmitterLedger.machine
          (TargetEmitterLedger.workSteps raw)
          { state := TargetEmitterLedger.machine.startState
            tape :=
              (TargetEmitterGrammarScanner.acceptedConfiguration raw).tape } =
        some
          { state := TargetEmitterLedger.machine.acceptState
            tape := (TargetEmitterLedger.finalConfiguration raw).tape }
    rw [← TargetEmitterLedger.entryConfiguration_is_scanner_tape]
    simpa [TargetEmitterLedger.entryConfiguration,
      TargetEmitterLedger.finalConfiguration] using
      TargetEmitterLedger.exact_execution raw
  have tail :
      AcceptPath graph (.node stackInitializeRef)
        (.node stackInitializeRef) 0
        (TargetEmitterLedger.finalConfiguration raw).tape
        (TargetEmitterLedger.finalConfiguration raw).tape :=
    .terminal _ _
  have path :=
    AcceptPath.step ledgerNode (.node stackInitializeRef)
      (TargetEmitterLedger.workSteps raw) 0 _ _ _
      ledgerNode_member localRun tail
  simpa [raw, CNFToNANDWorkspace.postLedgerConfiguration,
    ledgerNode, ledgerRef, controlNode, controlRef,
    Node.reference] using path

def prefixSteps (formula : CNFFormula) : Nat :=
  TargetEmitterGrammarScanner.canonicalSteps
      (CNFToNANDWorkspace.carrierCircuit formula) + 1 +
    (TargetEmitterLedger.workSteps
      (CNFToNANDWorkspace.carrierCircuit formula) + 1)

theorem scanner_ledger_path (formula : CNFFormula) :
    AcceptPath graph (.node scannerRef) (.node stackInitializeRef)
      (prefixSteps formula)
      (rawInputWorkTape
        (encodeCircuit
          (CNFToNANDWorkspace.carrierCircuit formula)))
      (CNFToNANDWorkspace.postLedgerConfiguration formula).tape := by
  exact
    AcceptPath.trans graph (.node scannerRef) (.node ledgerRef)
      (.node stackInitializeRef)
      (TargetEmitterGrammarScanner.canonicalSteps
          (CNFToNANDWorkspace.carrierCircuit formula) + 1)
      (TargetEmitterLedger.workSteps
          (CNFToNANDWorkspace.carrierCircuit formula) + 1)
      _ _ _ (scanner_path formula) (ledger_path formula)

/-! ## Dynamic-stack initialization -/

def ledgerHandoffConfiguration (formula : CNFFormula) :
    WorkConfiguration :=
  { state := TargetEmitterCheckStack.Initialize.startState
    tape := (CNFToNANDWorkspace.postLedgerConfiguration formula).tape }

private theorem ledgerHandoff_initializeRepresents
    (formula : CNFFormula) :
    TargetEmitterRuntimeCheckStack.CheckStack.InitializeRepresents
      (CNFToNANDWorkspace.capacity formula) 0
      (CNFToNANDWorkspace.postLedgerRegisters formula)
      SourceParser.cell00
      (SourceParser.circuitCells
        (CNFToNANDWorkspace.carrierCircuit formula)).tail []
      (ledgerHandoffConfiguration formula) := by
  let raw := CNFToNANDWorkspace.carrierCircuit formula
  change
    TargetEmitterRuntimeCheckStack.CheckStack.InitializeRepresents
      (TargetEmitterLedger.slotCapacity raw) 0
      (TargetEmitterLedger.ledgerRegisters raw)
      SourceParser.cell00 (SourceParser.circuitCells raw).tail []
      { state := TargetEmitterCheckStack.Initialize.startState
        tape := (TargetEmitterLedger.finalConfiguration raw).tape }
  unfold
    TargetEmitterRuntimeCheckStack.CheckStack.InitializeRepresents
    TargetEmitterRuntimeCheckStack.CheckStack.initializeLogicalConfiguration
  refine ⟨rfl, ?_⟩
  cases raw with
  | mk inputs gates output =>
      have padded :=
        WorkTape.blankEquivalent_of_padding
          (TargetEmitterCheckStack.Initialize.entryConfiguration
            (TargetEmitterLedger.slotCapacity
              { inputCount := inputs, gates := gates, output := output })
            0
            (TargetEmitterLedger.ledgerRegisters
              { inputCount := inputs, gates := gates, output := output })
            SourceParser.cell00
            (SourceParser.circuitCells
              { inputCount := inputs, gates := gates, output := output }).tail
            (TargetEmitterRuntimeCheckStack.CheckStack.targetSuffix [])
            []).tape
          0 3
      simpa [TargetEmitterLedger.finalConfiguration,
        TargetEmitterLedger.finalTape,
        TargetEmitterLedger.ledgerLeftWorkspace,
        TargetEmitterLedger.zeroScratchReserve,
        TargetEmitterLedger.ledgerWord,
        TargetEmitterCheckStack.Initialize.entryConfiguration,
        TargetEmitterCheckStack.scratchWord,
        TargetEmitterCheckStack.configAtWord,
        TargetEmitterCheckStack.sourceLeftBoundary,
        TargetEmitterCheckStack.unarySeparator,
        TargetEmitterCheckStack.ledgerBoundary,
        TargetEmitterCheckStack.stackBoundary,
        TargetEmitterCheckStack.cellBlank,
        TargetEmitterLedger.sourceLeftBoundary,
        TargetEmitterLedger.sourceTargetBoundary,
        TargetEmitterLedger.unarySeparator,
        TargetEmitterLedger.ledgerBoundary,
        TargetEmitterLedger.stackBoundary,
        TargetEmitterLedger.cellBlank,
        TargetEmitter.sourceLeftBoundary,
        TargetEmitter.sourceTargetBoundary,
        TargetEmitter.unarySeparator,
        TargetEmitterRuntimeCheckStack.CheckStack.targetSuffix,
        TargetEmitter.configAtWord,
        SourceParser.circuitCells, SourceParser.gateListCells,
        SourceParser.packedTokenCells,
        List.append_assoc] using padded

private theorem ledgerHandoff_fits (formula : CNFFormula) :
    TargetEmitterRuntimeCheckStack.CheckStack.LedgerFits
      (CNFToNANDWorkspace.capacity formula)
      (CNFToNANDWorkspace.postLedgerRegisters formula) := by
  let shape := CNFToNANDWorkspace.postLedgerShape formula
  exact
    { inputCount := shape.inputBound
      normalizedGateCount := shape.normalizedGateBound
      carrierWidth := shape.carrierWidthBound
      baseline := shape.baselineBound
      currentGate := shape.currentGateBound
      outputIndex := shape.outputIndexBound }

private theorem ledgerHandoff_sourceAllowed :
    TargetEmitterCheckStack.sourceAllowed SourceParser.cell00 := by
  simp [TargetEmitterCheckStack.sourceAllowed, SourceParser.cell00]

private theorem stackInitializeNode_member :
    stackInitializeNode ∈ graph.nodes := by
  change stackInitializeNode ∈ nodes
  apply controlNode_member_nodes stackInitializeNode
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

def stackInitializeSteps (formula : CNFFormula) : Nat :=
  TargetEmitterCheckStack.Initialize.workSteps
      (CNFToNANDWorkspace.capacity formula) + 1

/-- Install the unique far stack marker omitted by the source ledger and
return at the first retained carrier cell. -/
theorem stack_initialize_path (formula : CNFFormula) :
    ∃ finalTape,
      AcceptPath graph (.node stackInitializeRef)
        (.node resetWorkspaceRef)
        (stackInitializeSteps formula)
        (CNFToNANDWorkspace.postLedgerConfiguration formula).tape
        finalTape ∧
      TapeRepresents resetWorkspaceRef.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (SourceParser.circuitCells
          (CNFToNANDWorkspace.carrierCircuit formula)) []
        finalTape := by
  let actual := ledgerHandoffConfiguration formula
  rcases
      TargetEmitterRuntimeCheckStack.CheckStack.initialize_exact
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula)
        SourceParser.cell00
        (SourceParser.circuitCells
          (CNFToNANDWorkspace.carrierCircuit formula)).tail
        [] actual
        (ledgerHandoff_fits formula) (by omega)
        ledgerHandoff_sourceAllowed
        (ledgerHandoff_initializeRepresents formula) with
    ⟨actualFinal, exactRun, finalRepresents⟩
  have sourceEq :
      SourceParser.cell00 ::
          (SourceParser.circuitCells
            (CNFToNANDWorkspace.carrierCircuit formula)).tail =
        SourceParser.circuitCells
          (CNFToNANDWorkspace.carrierCircuit formula) := by
    rfl
  rw [sourceEq] at finalRepresents
  have tail :
      AcceptPath graph (.node resetWorkspaceRef)
        (.node resetWorkspaceRef) 0 actualFinal.tape actualFinal.tape :=
    .terminal _ _
  have localRun :
      workRunExact? TargetEmitterCheckStack.Initialize.machine
          (TargetEmitterCheckStack.Initialize.workSteps
            (CNFToNANDWorkspace.capacity formula))
          { state := TargetEmitterCheckStack.Initialize.machine.startState
            tape :=
              (CNFToNANDWorkspace.postLedgerConfiguration formula).tape } =
        some
          { state := TargetEmitterCheckStack.Initialize.machine.acceptState
            tape := actualFinal.tape } := by
    have actualShape :
        actual =
          { state := TargetEmitterCheckStack.Initialize.machine.startState
            tape :=
              (CNFToNANDWorkspace.postLedgerConfiguration formula).tape } := by
      rfl
    have finalState :=
      TargetEmitterRuntime.Represents.state_eq finalRepresents
    cases actualFinal with
    | mk state tape =>
        simp only at finalState
        subst state
        simpa [actualShape, TargetEmitterCheckStack.Initialize.machine,
          TargetEmitterCheckStack.machineOf] using exactRun
  have path :=
    localAccept_path Address.stackInitialize
      TargetEmitterCheckStack.Initialize.machine
      (.node resetWorkspaceRef) .reject (.node resetWorkspaceRef)
      (TargetEmitterCheckStack.Initialize.workSteps
        (CNFToNANDWorkspace.capacity formula))
      0 _ _ _ (by
        exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      localRun tail
  refine ⟨actualFinal.tape, ?_, ?_⟩
  · simpa [stackInitializeSteps, stackInitializeRef] using path
  · exact
      represents_at_state
        (newState := resetWorkspaceRef.startState) finalRepresents

def initializedPrefixSteps (formula : CNFFormula) : Nat :=
  prefixSteps formula + stackInitializeSteps formula

theorem scanner_ledger_stack_path (formula : CNFFormula) :
    ∃ finalTape,
      AcceptPath graph (.node scannerRef) (.node resetWorkspaceRef)
        (initializedPrefixSteps formula)
        (rawInputWorkTape
          (encodeCircuit
            (CNFToNANDWorkspace.carrierCircuit formula)))
        finalTape ∧
      TapeRepresents resetWorkspaceRef.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (SourceParser.circuitCells
          (CNFToNANDWorkspace.carrierCircuit formula)) []
        finalTape := by
  rcases stack_initialize_path formula with
    ⟨finalTape, stackPath, represents⟩
  refine ⟨finalTape, ?_, represents⟩
  exact
    AcceptPath.trans graph (.node scannerRef)
      (.node stackInitializeRef) (.node resetWorkspaceRef)
      (prefixSteps formula) (stackInitializeSteps formula)
      _ _ _ (scanner_ledger_path formula) stackPath

/-! ## Workspace reset and zero-carrier check -/

def canonicalSource (formula : CNFFormula) : List WorkSymbol :=
  SourceParser.circuitCells
    (CNFToNANDWorkspace.carrierCircuit formula)

theorem canonicalSource_eq_cons (formula : CNFFormula) :
    canonicalSource formula =
      SourceParser.cell00 :: (canonicalSource formula).tail := by
  rfl

def canonicalSourceContext (formula : CNFFormula) :
    SourceContext (canonicalSource formula) :=
  { head := SourceParser.cell00
    tail := (canonicalSource formula).tail
    source_eq := canonicalSource_eq_cons formula
    allowed := Or.inl TargetEmitter.PackedSymbol.zeroZero }

def postLedgerFits (formula : CNFFormula) :
    TargetEmitterRuntimeProgram.LedgerFits
      (CNFToNANDWorkspace.capacity formula)
      (CNFToNANDWorkspace.postLedgerRegisters formula) := by
  let shape := CNFToNANDWorkspace.postLedgerShape formula
  exact
    { inputCount := shape.inputBound
      normalizedGateCount := shape.normalizedGateBound
      carrierWidth := shape.carrierWidthBound
      baseline := shape.baselineBound
      currentGate := shape.currentGateBound
      outputIndex := shape.outputIndexBound }

private def resetWorkspaceDescriptor : BlockDescriptor :=
  { code := Block.resetWorkspace
    primitives := resetLiteralIndexProgram
    continuation := .node workspaceZeroRef
    closed := resetLiteralIndexProgram_closed
    nonempty := by decide }

private theorem resetWorkspaceDescriptor_member :
    resetWorkspaceDescriptor ∈ blockDescriptors := by
  simp [resetWorkspaceDescriptor, blockDescriptors]

private def resetWorkspaceNode : Node :=
  { name := blockNodeName Block.resetWorkspace 0
    program := TargetEmitterScratchReset.machine
    onAccept := .node workspaceZeroRef
    onReject := .reject }

private theorem resetWorkspaceNode_member :
    resetWorkspaceNode ∈ graph.nodes := by
  apply descriptorBlockNode_member_nodes resetWorkspaceDescriptor
    resetWorkspaceDescriptor_member
  change resetWorkspaceNode ∈
    resetWorkspaceDescriptor.materialize
  exact List.Mem.head _

private theorem resetWorkspaceRef_eq :
    resetWorkspaceRef = resetWorkspaceNode.reference := by
  rfl

private theorem resetWorkspaceRef_startState :
    resetWorkspaceRef.startState =
      TargetEmitterScratchReset.startState := by
  rfl

def resetSteps : Nat :=
  TargetEmitterScratchReset.workSteps 0 + 1

theorem reset_path_of_represents
    (formula : CNFFormula) (initialTape : WorkTape)
    (represents :
      TapeRepresents resetWorkspaceRef.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (canonicalSource formula) [] initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node resetWorkspaceRef)
        (.node workspaceZeroRef) resetSteps
        initialTape finalTape ∧
      TapeRepresents workspaceZeroRef.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (canonicalSource formula) [] finalTape := by
  let actual : WorkConfiguration :=
    { state := TargetEmitterScratchReset.startState
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents
        TargetEmitterScratchReset.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (canonicalSource formula) [] actual := by
    rw [resetWorkspaceRef_startState] at represents
    exact represents
  have capacityPositive :
      0 < CNFToNANDWorkspace.capacity formula := by
    unfold CNFToNANDWorkspace.capacity TargetEmitterLedger.slotCapacity
    omega
  rcases
      TargetEmitterRuntimePrimitives.resetScratch_exact
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        SourceParser.cell00 (canonicalSource formula).tail []
        actual capacityPositive
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        (by
          rw [canonicalSource_eq_cons formula] at inputRepresents
          exact inputRepresents) with
    ⟨actualFinal, exactRun, finalRepresents⟩
  have finalState :=
    TargetEmitterRuntime.Represents.state_eq finalRepresents
  have localRun :
      LocalAcceptRun resetWorkspaceNode
        (TargetEmitterScratchReset.workSteps 0)
        initialTape actualFinal.tape := by
    unfold LocalAcceptRun
    change
      workRunExact? TargetEmitterScratchReset.machine
          (TargetEmitterScratchReset.workSteps 0)
          { state := TargetEmitterScratchReset.startState
            tape := initialTape } =
        some
          { state := TargetEmitterScratchReset.acceptState
            tape := actualFinal.tape }
    cases actualFinal with
    | mk state tape =>
        simp only at finalState
        subst state
        simpa [actual] using exactRun
  have tail :
      AcceptPath graph (.node workspaceZeroRef)
        (.node workspaceZeroRef) 0 actualFinal.tape actualFinal.tape :=
    .terminal _ _
  have path :=
    AcceptPath.step resetWorkspaceNode (.node workspaceZeroRef)
      (TargetEmitterScratchReset.workSteps 0) 0
      initialTape actualFinal.tape actualFinal.tape
      resetWorkspaceNode_member localRun tail
  refine ⟨actualFinal.tape, ?_, ?_⟩
  · rw [resetWorkspaceRef_eq]
    simpa [resetSteps] using path
  · exact
      represents_at_state
        (newState := workspaceZeroRef.startState) finalRepresents

private theorem workspaceZeroNode_member :
    workspaceZeroNode ∈ graph.nodes := by
  change workspaceZeroNode ∈ nodes
  apply controlNode_member_nodes workspaceZeroNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.head _

private theorem workspaceZeroRef_startState :
    workspaceZeroRef.startState =
      TargetEmitterScratchCompareSlot.startState .inputCount := by
  rfl

def workspaceZeroSteps (formula : CNFFormula) : Nat :=
  TargetEmitterScratchCompareSlot.workSteps .inputCount
      (CNFToNANDWorkspace.capacity formula) 0 + 1

theorem workspace_zero_path_of_represents
    (formula : CNFFormula) (initialTape : WorkTape)
    (represents :
      TapeRepresents workspaceZeroRef.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (canonicalSource formula) [] initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node workspaceZeroRef)
        (.node validationHeaderRef) (workspaceZeroSteps formula)
        initialTape finalTape ∧
      TapeRepresents validationHeaderRef.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (canonicalSource formula) [] finalTape := by
  let actual : WorkConfiguration :=
    { state :=
        TargetEmitterScratchCompareSlot.startState .inputCount
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents
        (TargetEmitterScratchCompareSlot.startState .inputCount)
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (canonicalSource formula) [] actual := by
    rw [workspaceZeroRef_startState] at represents
    exact represents
  rcases
      TargetEmitterRuntimePrimitives.compareRegisterEqual_exact
        .inputCount (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        SourceParser.cell00 (canonicalSource formula).tail []
        actual (postLedgerFits formula).toPrimitive
        (by
          change
            0 =
              (CNFToNANDWorkspace.postLedgerRegisters formula).inputCount
          exact
            (CNFToNANDWorkspace.postLedgerRegisters_inputCount formula).symm)
        (canonicalSourceContext formula).compareAllowed
        (by
          rw [canonicalSource_eq_cons formula] at inputRepresents
          exact inputRepresents) with
    ⟨actualFinal, exactRun, finalRepresents⟩
  have finalState :=
    TargetEmitterRuntime.Represents.state_eq finalRepresents
  have localRun :
      LocalAcceptRun workspaceZeroNode
        (TargetEmitterScratchCompareSlot.workSteps
          .inputCount (CNFToNANDWorkspace.capacity formula) 0)
        initialTape actualFinal.tape := by
    unfold LocalAcceptRun
    change
      workRunExact?
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          (TargetEmitterScratchCompareSlot.workSteps
            .inputCount (CNFToNANDWorkspace.capacity formula) 0)
          { state :=
              (TargetEmitterScratchCompareSlot.machineFor
                .inputCount).startState
            tape := initialTape } =
        some
          { state :=
              (TargetEmitterScratchCompareSlot.machineFor
                .inputCount).acceptState
            tape := actualFinal.tape }
    cases actualFinal with
    | mk state tape =>
        simp only at finalState
        subst state
        simpa [actual, TargetEmitterScratchCompareSlot.machineFor] using
          exactRun
  have tail :
      AcceptPath graph (.node validationHeaderRef)
        (.node validationHeaderRef) 0
        actualFinal.tape actualFinal.tape := .terminal _ _
  have path :=
    AcceptPath.step workspaceZeroNode (.node validationHeaderRef)
      (TargetEmitterScratchCompareSlot.workSteps
        .inputCount (CNFToNANDWorkspace.capacity formula) 0)
      0 initialTape actualFinal.tape actualFinal.tape
      workspaceZeroNode_member localRun tail
  refine ⟨actualFinal.tape, ?_, ?_⟩
  · simpa [workspaceZeroSteps, workspaceZeroNode,
      workspaceZeroRef, controlNode, controlRef,
      Node.reference] using path
  · exact
      represents_at_state
        (newState := validationHeaderRef.startState)
        finalRepresents

def initializedResetSteps (formula : CNFFormula) : Nat :=
  initializedPrefixSteps formula + resetSteps +
    workspaceZeroSteps formula

theorem scanner_ledger_stack_reset_path (formula : CNFFormula) :
    ∃ finalTape,
      AcceptPath graph (.node scannerRef) (.node validationHeaderRef)
        (initializedResetSteps formula)
        (rawInputWorkTape
          (encodeCircuit
            (CNFToNANDWorkspace.carrierCircuit formula)))
        finalTape ∧
      TapeRepresents validationHeaderRef.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (canonicalSource formula) [] finalTape := by
  rcases scanner_ledger_stack_path formula with
    ⟨stackTape, prefixPath, stackRepresents⟩
  rcases reset_path_of_represents formula stackTape stackRepresents with
    ⟨resetTape, resetPath, resetRepresents⟩
  rcases
      workspace_zero_path_of_represents formula resetTape resetRepresents with
    ⟨finalTape, zeroPath, finalRepresents⟩
  have first :=
    AcceptPath.trans graph (.node scannerRef)
      (.node resetWorkspaceRef) (.node workspaceZeroRef)
      (initializedPrefixSteps formula) resetSteps _ _ _
      prefixPath resetPath
  refine ⟨finalTape, ?_, finalRepresents⟩
  exact
    AcceptPath.trans graph (.node scannerRef)
      (.node workspaceZeroRef) (.node validationHeaderRef)
      (initializedPrefixSteps formula + resetSteps)
      (workspaceZeroSteps formula) _ _ _ first zeroPath

/-! ## Canonical carrier validation -/

def focusTape (left word : List WorkSymbol) : WorkTape :=
  (TargetEmitter.configAtWord 0 left word).tape

private theorem targetEmitter_configAtWord_eq
    (state : Nat) (left word : List WorkSymbol) :
    { state := state, tape := focusTape left word } =
      TargetEmitter.configAtWord state left word := by
  cases word <;> rfl

private theorem navigator_configAtWord_eq
    (state : Nat) (left word : List WorkSymbol) :
    { state := state, tape := focusTape left word } =
      TargetEmitterNavigator.configAtWord state left word := by
  cases word <;> rfl

private theorem carrierReader_configAtWord_eq
    (state : Nat) (left word : List WorkSymbol) :
    { state := state, tape := focusTape left word } =
      CNFToNANDCarrierTokenReader.configAtWord state left word := by
  cases word <;> rfl

private theorem validationHeaderNode_member :
    validationHeaderNode ∈ graph.nodes := by
  change validationHeaderNode ∈ nodes
  apply controlNode_member_nodes validationHeaderNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.head _

private theorem validationFirstNode_member :
    validationFirstNode ∈ graph.nodes := by
  change validationFirstNode ∈ nodes
  apply controlNode_member_nodes validationFirstNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _

private theorem validationFirstNonInputNode_member :
    validationFirstNonInputNode ∈ graph.nodes := by
  change validationFirstNonInputNode ∈ nodes
  apply controlNode_member_nodes validationFirstNonInputNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.head _

private theorem validationFirstConstantNode_member :
    validationFirstConstantNode ∈ graph.nodes := by
  change validationFirstConstantNode ∈ nodes
  apply controlNode_member_nodes validationFirstConstantNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _

private theorem validationFirstReaderNode_member :
    validationFirstReaderNode ∈ graph.nodes := by
  change validationFirstReaderNode ∈ nodes
  apply controlNode_member_nodes validationFirstReaderNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _

private theorem validationSecondNode_member :
    validationSecondNode ∈ graph.nodes := by
  change validationSecondNode ∈ nodes
  apply controlNode_member_nodes validationSecondNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.head _

private theorem validationSecondNonInputNode_member :
    validationSecondNonInputNode ∈ graph.nodes := by
  change validationSecondNonInputNode ∈ nodes
  apply controlNode_member_nodes validationSecondNonInputNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.head _

private theorem validationSecondConstantNode_member :
    validationSecondConstantNode ∈ graph.nodes := by
  change validationSecondConstantNode ∈ nodes
  apply controlNode_member_nodes validationSecondConstantNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _

private theorem validationSecondReaderNode_member :
    validationSecondReaderNode ∈ graph.nodes := by
  change validationSecondReaderNode ∈ nodes
  apply controlNode_member_nodes validationSecondReaderNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
            List.Mem.head _

private theorem validationAdvanceNode_member :
    validationAdvanceNode ∈ graph.nodes := by
  change validationAdvanceNode ∈ nodes
  apply controlNode_member_nodes validationAdvanceNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
            List.Mem.tail _ <| List.Mem.head _

private theorem validationProgramEndNode_member :
    validationProgramEndNode ∈ graph.nodes := by
  change validationProgramEndNode ∈ nodes
  apply controlNode_member_nodes validationProgramEndNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
            List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _

private theorem validationOutputFirstNode_member :
    validationOutputFirstNode ∈ graph.nodes := by
  change validationOutputFirstNode ∈ nodes
  apply controlNode_member_nodes validationOutputFirstNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
            List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
              List.Mem.head _

private theorem validationOutputNonInputNode_member :
    validationOutputNonInputNode ∈ graph.nodes := by
  change validationOutputNonInputNode ∈ nodes
  apply controlNode_member_nodes validationOutputNonInputNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
            List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
              List.Mem.tail _ <| List.Mem.head _

private theorem validationOutputNode_member :
    validationOutputNode ∈ graph.nodes := by
  change validationOutputNode ∈ nodes
  apply controlNode_member_nodes validationOutputNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
            List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
              List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _

private theorem validationRewindNode_member :
    validationRewindNode ∈ graph.nodes := by
  change validationRewindNode ∈ nodes
  apply controlNode_member_nodes validationRewindNode
  exact
    List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
            List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
              List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
                List.Mem.head _

def constantSecondCell (value : Bool) : WorkSymbol :=
  if value then SourceParser.cell01 else SourceParser.cell00

theorem sourceCells_constant (value : Bool) :
    SourceParser.sourceCells (.constant value) =
      [SourceParser.cell01, constantSecondCell value] := by
  cases value <;> rfl

def validationSourceSteps : Nat := 11

private theorem validation_first_source_path
    (value : Bool) (left rest : List WorkSymbol) :
    AcceptPath graph (.node validationFirstRef)
      (.node validationSecondRef) validationSourceSteps
      (focusTape left
        (SourceParser.sourceCells (.constant value) ++ rest))
      (focusTape
        (constantSecondCell value :: SourceParser.cell01 :: left)
        rest) := by
  have firstRun :
      LocalRejectRun validationFirstNode 1
        (focusTape left
          (SourceParser.sourceCells (.constant value) ++ rest))
        (focusTape left
          (SourceParser.sourceCells (.constant value) ++ rest)) := by
    unfold LocalRejectRun
    change
      workRunExact? TargetEmitterNavigator.sourceFirstMachine 1
          { state := TargetEmitterNavigator.State.sourceFirst
            tape :=
              focusTape left
                (SourceParser.sourceCells (.constant value) ++ rest) } =
        some
          { state := TargetEmitterNavigator.State.reject
            tape :=
              focusTape left
                (SourceParser.sourceCells (.constant value) ++ rest) }
    rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
    simpa [sourceCells_constant, SourceParser.cell01,
      TargetEmitterNavigator.cell01] using
      TargetEmitterNavigator.sourceFirst_noninput_exact left
        (constantSecondCell value :: rest)
  have nonInputRun :
      LocalRejectRun validationFirstNonInputNode 2
        (focusTape left
          (SourceParser.sourceCells (.constant value) ++ rest))
        (focusTape left
          (SourceParser.sourceCells (.constant value) ++ rest)) := by
    unfold LocalRejectRun
    cases value with
    | false =>
        change
          workRunExact? TargetEmitterNavigator.nonInputMachine 2
              { state := TargetEmitterNavigator.State.nonInputFirst
                tape :=
                  focusTape left
                    (SourceParser.sourceCells (.constant false) ++ rest) } =
            some
              { state := TargetEmitterNavigator.State.reject
                tape :=
                  focusTape left
                    (SourceParser.sourceCells (.constant false) ++ rest) }
        rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
        simpa [sourceCells_constant, constantSecondCell,
          SourceParser.cell00, SourceParser.cell01,
          TargetEmitterNavigator.cell00,
          TargetEmitterNavigator.cell01] using
          TargetEmitterNavigator.nonInput_constantFalse_exact left rest
    | true =>
        change
          workRunExact? TargetEmitterNavigator.nonInputMachine 2
              { state := TargetEmitterNavigator.State.nonInputFirst
                tape :=
                  focusTape left
                    (SourceParser.sourceCells (.constant true) ++ rest) } =
            some
              { state := TargetEmitterNavigator.State.reject
                tape :=
                  focusTape left
                    (SourceParser.sourceCells (.constant true) ++ rest) }
        rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
        simpa [sourceCells_constant, constantSecondCell,
          SourceParser.cell01, TargetEmitterNavigator.cell01] using
          TargetEmitterNavigator.nonInput_constantTrue_exact left rest
  have constantPath :
      AcceptPath graph (.node validationFirstConstantRef)
        (.node validationSecondRef) 6
        (focusTape left
          (SourceParser.sourceCells (.constant value) ++ rest))
        (focusTape
          (constantSecondCell value :: SourceParser.cell01 :: left)
          rest) := by
    cases value with
    | false =>
        have constantRun :
            LocalAcceptRun validationFirstConstantNode 2
              (focusTape left
                (SourceParser.sourceCells (.constant false) ++ rest))
              (focusTape left
                (SourceParser.sourceCells (.constant false) ++ rest)) := by
          unfold LocalAcceptRun
          change
            workRunExact? TargetEmitterNavigator.constantMachine 2
                { state := TargetEmitterNavigator.State.constantFirst
                  tape :=
                    focusTape left
                      (SourceParser.sourceCells (.constant false) ++ rest) } =
              some
                { state := TargetEmitterNavigator.State.accept
                  tape :=
                    focusTape left
                      (SourceParser.sourceCells (.constant false) ++ rest) }
          rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
          simpa [sourceCells_constant, constantSecondCell,
            SourceParser.cell00, SourceParser.cell01,
            TargetEmitterNavigator.cell00,
            TargetEmitterNavigator.cell01] using
            TargetEmitterNavigator.constantFalse_exact left rest
        have readerRun :
            LocalAcceptRun validationFirstReaderNode 2
              (focusTape left
                (SourceParser.sourceCells (.constant false) ++ rest))
              (focusTape
                (constantSecondCell false ::
                  SourceParser.cell01 :: left) rest) := by
          unfold LocalAcceptRun
          change
            workRunExact? (CNFToNANDCarrierTokenReader.machine true) 2
                { state := CNFToNANDCarrierTokenReader.State.start
                  tape :=
                    focusTape left
                      (SourceParser.sourceCells (.constant false) ++ rest) } =
              some
                { state := CNFToNANDCarrierTokenReader.State.accept
                  tape :=
                    focusTape
                      (constantSecondCell false ::
                        SourceParser.cell01 :: left) rest }
          rw [carrierReader_configAtWord_eq,
            carrierReader_configAtWord_eq]
          simpa [sourceCells_constant, constantSecondCell,
            SourceParser.cell00, SourceParser.cell01,
            CNFToNANDCarrierTokenReader.cell00,
            CNFToNANDCarrierTokenReader.cell01] using
            CNFToNANDCarrierTokenReader.false_exact true left rest
        have terminal :
            AcceptPath graph (.node validationSecondRef)
              (.node validationSecondRef) 0
              (focusTape
                (constantSecondCell false ::
                  SourceParser.cell01 :: left) rest)
              (focusTape
                (constantSecondCell false ::
                  SourceParser.cell01 :: left) rest) := .terminal _ _
        have readerPath :=
          AcceptPath.step validationFirstReaderNode
            (.node validationSecondRef) 2 0 _ _ _
            validationFirstReaderNode_member readerRun terminal
        have path :=
          AcceptPath.step validationFirstConstantNode
            (.node validationSecondRef) 2 3 _ _ _
            validationFirstConstantNode_member constantRun readerPath
        simpa [validationFirstConstantNode,
          validationFirstReaderNode, validationFirstConstantRef,
          validationFirstReaderRef, validationSecondRef,
          controlNode, controlRef, Node.reference] using path
    | true =>
        have constantRun :
            LocalRejectRun validationFirstConstantNode 2
              (focusTape left
                (SourceParser.sourceCells (.constant true) ++ rest))
              (focusTape left
                (SourceParser.sourceCells (.constant true) ++ rest)) := by
          unfold LocalRejectRun
          change
            workRunExact? TargetEmitterNavigator.constantMachine 2
                { state := TargetEmitterNavigator.State.constantFirst
                  tape :=
                    focusTape left
                      (SourceParser.sourceCells (.constant true) ++ rest) } =
              some
                { state := TargetEmitterNavigator.State.reject
                  tape :=
                    focusTape left
                      (SourceParser.sourceCells (.constant true) ++ rest) }
          rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
          simpa [sourceCells_constant, constantSecondCell,
            SourceParser.cell01, TargetEmitterNavigator.cell01] using
            TargetEmitterNavigator.constantTrue_exact left rest
        have readerRun :
            LocalRejectRun validationFirstReaderNode 2
              (focusTape left
                (SourceParser.sourceCells (.constant true) ++ rest))
              (focusTape
                (constantSecondCell true ::
                  SourceParser.cell01 :: left) rest) := by
          unfold LocalRejectRun
          change
            workRunExact? (CNFToNANDCarrierTokenReader.machine true) 2
                { state := CNFToNANDCarrierTokenReader.State.start
                  tape :=
                    focusTape left
                      (SourceParser.sourceCells (.constant true) ++ rest) } =
              some
                { state := CNFToNANDCarrierTokenReader.State.reject
                  tape :=
                    focusTape
                      (constantSecondCell true ::
                        SourceParser.cell01 :: left) rest }
          rw [carrierReader_configAtWord_eq,
            carrierReader_configAtWord_eq]
          simpa [sourceCells_constant, constantSecondCell,
            SourceParser.cell01,
            CNFToNANDCarrierTokenReader.cell01] using
            CNFToNANDCarrierTokenReader.true_exact true left rest
        have terminal :
            AcceptPath graph (.node validationSecondRef)
              (.node validationSecondRef) 0
              (focusTape
                (constantSecondCell true ::
                  SourceParser.cell01 :: left) rest)
              (focusTape
                (constantSecondCell true ::
                  SourceParser.cell01 :: left) rest) := .terminal _ _
        have readerPath :=
          AcceptPath.stepReject validationFirstReaderNode
            (.node validationSecondRef) 2 0 _ _ _
            validationFirstReaderNode_member readerRun terminal
        have path :=
          AcceptPath.stepReject validationFirstConstantNode
            (.node validationSecondRef) 2 3 _ _ _
            validationFirstConstantNode_member constantRun readerPath
        simpa [validationFirstConstantNode,
          validationFirstReaderNode, validationFirstConstantRef,
          validationFirstReaderRef, validationSecondRef,
          controlNode, controlRef, Node.reference] using path
  have nonInputPath :=
    AcceptPath.stepReject validationFirstNonInputNode
      (.node validationSecondRef) 2 6 _ _ _
      validationFirstNonInputNode_member nonInputRun constantPath
  have path :=
    AcceptPath.stepReject validationFirstNode
      (.node validationSecondRef) 1 9 _ _ _
      validationFirstNode_member firstRun nonInputPath
  simpa [validationSourceSteps, validationFirstNode,
    validationFirstNonInputNode, validationFirstRef,
    validationFirstNonInputRef, controlNode, controlRef,
    Node.reference] using path

private theorem validation_second_source_path
    (value : Bool) (left rest : List WorkSymbol) :
    AcceptPath graph (.node validationSecondRef)
      (.node validationAdvanceRef) validationSourceSteps
      (focusTape left
        (SourceParser.sourceCells (.constant value) ++ rest))
      (focusTape
        (constantSecondCell value :: SourceParser.cell01 :: left)
        rest) := by
  have firstRun :
      LocalRejectRun validationSecondNode 1
        (focusTape left
          (SourceParser.sourceCells (.constant value) ++ rest))
        (focusTape left
          (SourceParser.sourceCells (.constant value) ++ rest)) := by
    unfold LocalRejectRun
    change
      workRunExact? TargetEmitterNavigator.sourceFirstMachine 1
          { state := TargetEmitterNavigator.State.sourceFirst
            tape :=
              focusTape left
                (SourceParser.sourceCells (.constant value) ++ rest) } =
        some
          { state := TargetEmitterNavigator.State.reject
            tape :=
              focusTape left
                (SourceParser.sourceCells (.constant value) ++ rest) }
    rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
    simpa [sourceCells_constant, SourceParser.cell01,
      TargetEmitterNavigator.cell01] using
      TargetEmitterNavigator.sourceFirst_noninput_exact left
        (constantSecondCell value :: rest)
  have nonInputRun :
      LocalRejectRun validationSecondNonInputNode 2
        (focusTape left
          (SourceParser.sourceCells (.constant value) ++ rest))
        (focusTape left
          (SourceParser.sourceCells (.constant value) ++ rest)) := by
    unfold LocalRejectRun
    cases value with
    | false =>
        change
          workRunExact? TargetEmitterNavigator.nonInputMachine 2
              { state := TargetEmitterNavigator.State.nonInputFirst
                tape :=
                  focusTape left
                    (SourceParser.sourceCells (.constant false) ++ rest) } =
            some
              { state := TargetEmitterNavigator.State.reject
                tape :=
                  focusTape left
                    (SourceParser.sourceCells (.constant false) ++ rest) }
        rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
        simpa [sourceCells_constant, constantSecondCell,
          SourceParser.cell00, SourceParser.cell01,
          TargetEmitterNavigator.cell00,
          TargetEmitterNavigator.cell01] using
          TargetEmitterNavigator.nonInput_constantFalse_exact left rest
    | true =>
        change
          workRunExact? TargetEmitterNavigator.nonInputMachine 2
              { state := TargetEmitterNavigator.State.nonInputFirst
                tape :=
                  focusTape left
                    (SourceParser.sourceCells (.constant true) ++ rest) } =
            some
              { state := TargetEmitterNavigator.State.reject
                tape :=
                  focusTape left
                    (SourceParser.sourceCells (.constant true) ++ rest) }
        rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
        simpa [sourceCells_constant, constantSecondCell,
          SourceParser.cell01, TargetEmitterNavigator.cell01] using
          TargetEmitterNavigator.nonInput_constantTrue_exact left rest
  have constantPath :
      AcceptPath graph (.node validationSecondConstantRef)
        (.node validationAdvanceRef) 6
        (focusTape left
          (SourceParser.sourceCells (.constant value) ++ rest))
        (focusTape
          (constantSecondCell value :: SourceParser.cell01 :: left)
          rest) := by
    cases value with
    | false =>
        have constantRun :
            LocalAcceptRun validationSecondConstantNode 2
              (focusTape left
                (SourceParser.sourceCells (.constant false) ++ rest))
              (focusTape left
                (SourceParser.sourceCells (.constant false) ++ rest)) := by
          unfold LocalAcceptRun
          change
            workRunExact? TargetEmitterNavigator.constantMachine 2
                { state := TargetEmitterNavigator.State.constantFirst
                  tape :=
                    focusTape left
                      (SourceParser.sourceCells (.constant false) ++ rest) } =
              some
                { state := TargetEmitterNavigator.State.accept
                  tape :=
                    focusTape left
                      (SourceParser.sourceCells (.constant false) ++ rest) }
          rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
          simpa [sourceCells_constant, constantSecondCell,
            SourceParser.cell00, SourceParser.cell01,
            TargetEmitterNavigator.cell00,
            TargetEmitterNavigator.cell01] using
            TargetEmitterNavigator.constantFalse_exact left rest
        have readerRun :
            LocalAcceptRun validationSecondReaderNode 2
              (focusTape left
                (SourceParser.sourceCells (.constant false) ++ rest))
              (focusTape
                (constantSecondCell false ::
                  SourceParser.cell01 :: left) rest) := by
          unfold LocalAcceptRun
          change
            workRunExact? (CNFToNANDCarrierTokenReader.machine true) 2
                { state := CNFToNANDCarrierTokenReader.State.start
                  tape :=
                    focusTape left
                      (SourceParser.sourceCells (.constant false) ++ rest) } =
              some
                { state := CNFToNANDCarrierTokenReader.State.accept
                  tape :=
                    focusTape
                      (constantSecondCell false ::
                        SourceParser.cell01 :: left) rest }
          rw [carrierReader_configAtWord_eq,
            carrierReader_configAtWord_eq]
          simpa [sourceCells_constant, constantSecondCell,
            SourceParser.cell00, SourceParser.cell01,
            CNFToNANDCarrierTokenReader.cell00,
            CNFToNANDCarrierTokenReader.cell01] using
            CNFToNANDCarrierTokenReader.false_exact true left rest
        have terminal :
            AcceptPath graph (.node validationAdvanceRef)
              (.node validationAdvanceRef) 0
              (focusTape
                (constantSecondCell false ::
                  SourceParser.cell01 :: left) rest)
              (focusTape
                (constantSecondCell false ::
                  SourceParser.cell01 :: left) rest) := .terminal _ _
        have readerPath :=
          AcceptPath.step validationSecondReaderNode
            (.node validationAdvanceRef) 2 0 _ _ _
            validationSecondReaderNode_member readerRun terminal
        have path :=
          AcceptPath.step validationSecondConstantNode
            (.node validationAdvanceRef) 2 3 _ _ _
            validationSecondConstantNode_member constantRun readerPath
        simpa [validationSecondConstantNode,
          validationSecondReaderNode, validationSecondConstantRef,
          validationSecondReaderRef, validationAdvanceRef,
          controlNode, controlRef, Node.reference] using path
    | true =>
        have constantRun :
            LocalRejectRun validationSecondConstantNode 2
              (focusTape left
                (SourceParser.sourceCells (.constant true) ++ rest))
              (focusTape left
                (SourceParser.sourceCells (.constant true) ++ rest)) := by
          unfold LocalRejectRun
          change
            workRunExact? TargetEmitterNavigator.constantMachine 2
                { state := TargetEmitterNavigator.State.constantFirst
                  tape :=
                    focusTape left
                      (SourceParser.sourceCells (.constant true) ++ rest) } =
              some
                { state := TargetEmitterNavigator.State.reject
                  tape :=
                    focusTape left
                      (SourceParser.sourceCells (.constant true) ++ rest) }
          rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
          simpa [sourceCells_constant, constantSecondCell,
            SourceParser.cell01, TargetEmitterNavigator.cell01] using
            TargetEmitterNavigator.constantTrue_exact left rest
        have readerRun :
            LocalRejectRun validationSecondReaderNode 2
              (focusTape left
                (SourceParser.sourceCells (.constant true) ++ rest))
              (focusTape
                (constantSecondCell true ::
                  SourceParser.cell01 :: left) rest) := by
          unfold LocalRejectRun
          change
            workRunExact? (CNFToNANDCarrierTokenReader.machine true) 2
                { state := CNFToNANDCarrierTokenReader.State.start
                  tape :=
                    focusTape left
                      (SourceParser.sourceCells (.constant true) ++ rest) } =
              some
                { state := CNFToNANDCarrierTokenReader.State.reject
                  tape :=
                    focusTape
                      (constantSecondCell true ::
                        SourceParser.cell01 :: left) rest }
          rw [carrierReader_configAtWord_eq,
            carrierReader_configAtWord_eq]
          simpa [sourceCells_constant, constantSecondCell,
            SourceParser.cell01,
            CNFToNANDCarrierTokenReader.cell01] using
            CNFToNANDCarrierTokenReader.true_exact true left rest
        have terminal :
            AcceptPath graph (.node validationAdvanceRef)
              (.node validationAdvanceRef) 0
              (focusTape
                (constantSecondCell true ::
                  SourceParser.cell01 :: left) rest)
              (focusTape
                (constantSecondCell true ::
                  SourceParser.cell01 :: left) rest) := .terminal _ _
        have readerPath :=
          AcceptPath.stepReject validationSecondReaderNode
            (.node validationAdvanceRef) 2 0 _ _ _
            validationSecondReaderNode_member readerRun terminal
        have path :=
          AcceptPath.stepReject validationSecondConstantNode
            (.node validationAdvanceRef) 2 3 _ _ _
            validationSecondConstantNode_member constantRun readerPath
        simpa [validationSecondConstantNode,
          validationSecondReaderNode, validationSecondConstantRef,
          validationSecondReaderRef, validationAdvanceRef,
          controlNode, controlRef, Node.reference] using path
  have nonInputPath :=
    AcceptPath.stepReject validationSecondNonInputNode
      (.node validationAdvanceRef) 2 6 _ _ _
      validationSecondNonInputNode_member nonInputRun constantPath
  have path :=
    AcceptPath.stepReject validationSecondNode
      (.node validationAdvanceRef) 1 9 _ _ _
      validationSecondNode_member firstRun nonInputPath
  simpa [validationSourceSteps, validationSecondNode,
    validationSecondNonInputNode, validationSecondRef,
    validationSecondNonInputRef, controlNode, controlRef,
    Node.reference] using path

def validationGateSourceSteps : Nat :=
  validationSourceSteps + validationSourceSteps

private theorem validation_gate_sources_path
    (token : CNFToken) (left rest : List WorkSymbol) :
    AcceptPath graph (.node validationFirstRef)
      (.node validationAdvanceRef) validationGateSourceSteps
      (focusTape left
        (SourceParser.gateCells
          (CNFToNANDCarrierEncoder.Source.tokenGate token) ++ rest))
      (focusTape
        (constantSecondCell
            (CNFToNANDCarrierEncoder.Source.secondBit token) ::
          SourceParser.cell01 ::
          constantSecondCell
              (CNFToNANDCarrierEncoder.Source.firstBit token) ::
            SourceParser.cell01 :: left)
        (SourceParser.cell01 :: SourceParser.cell11 :: rest)) := by
  have firstPath :=
    validation_first_source_path
      (CNFToNANDCarrierEncoder.Source.firstBit token) left
      (SourceParser.sourceCells
          (.constant
            (CNFToNANDCarrierEncoder.Source.secondBit token)) ++
        SourceParser.cell01 :: SourceParser.cell11 :: rest)
  have secondPath :=
    validation_second_source_path
      (CNFToNANDCarrierEncoder.Source.secondBit token)
      (constantSecondCell
          (CNFToNANDCarrierEncoder.Source.firstBit token) ::
        SourceParser.cell01 :: left)
      (SourceParser.cell01 :: SourceParser.cell11 :: rest)
  have path :=
    AcceptPath.trans graph (.node validationFirstRef)
      (.node validationSecondRef) (.node validationAdvanceRef)
      validationSourceSteps validationSourceSteps _ _ _
      firstPath secondPath
  simpa [validationGateSourceSteps,
    SourceParser.gateCells,
    CNFToNANDCarrierEncoder.Source.tokenGate,
    CNFToNANDCarrierEncoder.Source.asConstant,
    List.append_assoc] using path

def validationAdvanceSteps : Nat := 4

private theorem validation_advance_next_path
    (first : WorkSymbol) (rest left : List WorkSymbol)
    (sourceFirst :
      first = SourceParser.cell00 ∨ first = SourceParser.cell01) :
    AcceptPath graph (.node validationAdvanceRef)
      (.node validationFirstRef) validationAdvanceSteps
      (focusTape left
        (SourceParser.cell01 :: SourceParser.cell11 ::
          first :: rest))
      (focusTape
        (SourceParser.cell11 :: SourceParser.cell01 :: left)
        (first :: rest)) := by
  have localRun :
      LocalAcceptRun validationAdvanceNode 3
        (focusTape left
          (SourceParser.cell01 :: SourceParser.cell11 ::
            first :: rest))
        (focusTape
          (SourceParser.cell11 :: SourceParser.cell01 :: left)
          (first :: rest)) := by
    unfold LocalAcceptRun
    change
      workRunExact? TargetEmitterNavigator.gateAdvanceMachine 3
          { state := TargetEmitterNavigator.State.gateEndFirst
            tape :=
              focusTape left
                (SourceParser.cell01 :: SourceParser.cell11 ::
                  first :: rest) } =
        some
          { state := TargetEmitterNavigator.State.accept
            tape :=
              focusTape
                (SourceParser.cell11 :: SourceParser.cell01 :: left)
                (first :: rest) }
    rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
    have sourceFirst' :
        first = TargetEmitterNavigator.cell00 ∨
          first = TargetEmitterNavigator.cell01 := by
      rcases sourceFirst with equality | equality
      · exact Or.inl (by
          simpa [SourceParser.cell00,
            TargetEmitterNavigator.cell00] using equality)
      · exact Or.inr (by
          simpa [SourceParser.cell01,
            TargetEmitterNavigator.cell01] using equality)
    simpa [SourceParser.cell01, SourceParser.cell11,
      TargetEmitterNavigator.cell01,
      TargetEmitterNavigator.cell11] using
        TargetEmitterNavigator.gateAdvance_next_exact
          left rest first sourceFirst'
  have tail :
      AcceptPath graph (.node validationFirstRef)
        (.node validationFirstRef) 0
        (focusTape
          (SourceParser.cell11 :: SourceParser.cell01 :: left)
          (first :: rest))
        (focusTape
          (SourceParser.cell11 :: SourceParser.cell01 :: left)
          (first :: rest)) := .terminal _ _
  have path :=
    AcceptPath.step validationAdvanceNode
      (.node validationFirstRef) 3 0 _ _ _
      validationAdvanceNode_member localRun tail
  simpa [validationAdvanceSteps, validationAdvanceNode,
    validationAdvanceRef, validationFirstRef,
    controlNode, controlRef, Node.reference] using path

private theorem validation_advance_programEnd_path
    (rest left : List WorkSymbol) :
    AcceptPath graph (.node validationAdvanceRef)
      (.node validationProgramEndRef) validationAdvanceSteps
      (focusTape left
        (SourceParser.cell01 :: SourceParser.cell11 ::
          SourceParser.cell10 :: rest))
      (focusTape
        (SourceParser.cell11 :: SourceParser.cell01 :: left)
        (SourceParser.cell10 :: rest)) := by
  have localRun :
      LocalRejectRun validationAdvanceNode 3
        (focusTape left
          (SourceParser.cell01 :: SourceParser.cell11 ::
            SourceParser.cell10 :: rest))
        (focusTape
          (SourceParser.cell11 :: SourceParser.cell01 :: left)
          (SourceParser.cell10 :: rest)) := by
    unfold LocalRejectRun
    change
      workRunExact? TargetEmitterNavigator.gateAdvanceMachine 3
          { state := TargetEmitterNavigator.State.gateEndFirst
            tape :=
              focusTape left
                (SourceParser.cell01 :: SourceParser.cell11 ::
                  SourceParser.cell10 :: rest) } =
        some
          { state := TargetEmitterNavigator.State.reject
            tape :=
              focusTape
                (SourceParser.cell11 :: SourceParser.cell01 :: left)
                (SourceParser.cell10 :: rest) }
    rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
    simpa [SourceParser.cell01, SourceParser.cell10,
      SourceParser.cell11, TargetEmitterNavigator.cell01,
      TargetEmitterNavigator.cell10,
      TargetEmitterNavigator.cell11] using
        TargetEmitterNavigator.gateAdvance_programEnd_exact left rest
  have tail :
      AcceptPath graph (.node validationProgramEndRef)
        (.node validationProgramEndRef) 0
        (focusTape
          (SourceParser.cell11 :: SourceParser.cell01 :: left)
          (SourceParser.cell10 :: rest))
        (focusTape
          (SourceParser.cell11 :: SourceParser.cell01 :: left)
          (SourceParser.cell10 :: rest)) := .terminal _ _
  have path :=
    AcceptPath.stepReject validationAdvanceNode
      (.node validationProgramEndRef) 3 0 _ _ _
      validationAdvanceNode_member localRun tail
  simpa [validationAdvanceSteps, validationAdvanceNode,
    validationAdvanceRef, validationProgramEndRef,
    controlNode, controlRef, Node.reference] using path

def carrierGateCellsFor (token : CNFToken) :
    List WorkSymbol :=
  [ SourceParser.cell01
  , constantSecondCell
      (CNFToNANDCarrierEncoder.Source.firstBit token)
  , SourceParser.cell01
  , constantSecondCell
      (CNFToNANDCarrierEncoder.Source.secondBit token)
  , SourceParser.cell01
  , SourceParser.cell11
  ]

def carrierGateCells : List CNFToken → List WorkSymbol
  | [] => []
  | token :: rest =>
      carrierGateCellsFor token ++ carrierGateCells rest

private theorem gateCells_tokenGate_eq
    (token : CNFToken) :
    SourceParser.gateCells
        (CNFToNANDCarrierEncoder.Source.tokenGate token) =
      carrierGateCellsFor token := by
  cases token <;> rfl

theorem carrierGateCells_eq_gateListCells
    (tokens : List CNFToken) :
    carrierGateCells tokens =
      SourceParser.gateListCells
        (tokens.map CNFToNANDCarrierEncoder.Source.tokenGate) := by
  induction tokens with
  | nil =>
      rfl
  | cons token rest inductionHypothesis =>
      rw [carrierGateCells, List.map_cons,
        SourceParser.gateListCells, inductionHypothesis,
        gateCells_tokenGate_eq]

def carrierHeaderCells (tokens : List CNFToken) :
    List WorkSymbol :=
  [SourceParser.cell00, SourceParser.cell00] ++
    SourceParser.natCells 0 ++
    SourceParser.natCells tokens.length

def carrierFooterCells : List WorkSymbol :=
  [SourceParser.cell10, SourceParser.cell00] ++
    SourceParser.sourceCells (.constant false) ++
    [SourceParser.cell10, SourceParser.cell01,
      SourceParser.cell10, SourceParser.cell11]

theorem canonicalSource_eq_carrier_layout
    (formula : CNFFormula) :
    canonicalSource formula =
      carrierHeaderCells (CNFToNANDWorkspace.formulaTokens formula) ++
        carrierGateCells
          (CNFToNANDWorkspace.formulaTokens formula) ++
        carrierFooterCells := by
  unfold canonicalSource CNFToNANDWorkspace.carrierCircuit
    CNFToNANDCarrierEncoder.Source.carrierCircuit
    SourceParser.circuitCells carrierHeaderCells carrierFooterCells
  simp only [List.length_map]
  rw [carrierGateCells_eq_gateListCells]
  simp [List.append_assoc]

def validationHeaderSteps (tokens : List CNFToken) : Nat :=
  TargetEmitterNavigator.headerWorkSteps 0 tokens.length + 1

private theorem validation_header_layout_path
    (first : CNFToken) (rest : List CNFToken)
    (left suffix : List WorkSymbol) :
    AcceptPath graph (.node validationHeaderRef)
      (.node validationFirstRef)
      (validationHeaderSteps (first :: rest))
      (focusTape left
        (carrierHeaderCells (first :: rest) ++
          carrierGateCells (first :: rest) ++ suffix))
      (focusTape
        ((carrierHeaderCells (first :: rest)).reverse ++ left)
        (carrierGateCells (first :: rest) ++ suffix)) := by
  have localRun :
      LocalAcceptRun validationHeaderNode
        (TargetEmitterNavigator.headerWorkSteps
          0 (first :: rest).length)
        (focusTape left
          (carrierHeaderCells (first :: rest) ++
            carrierGateCells (first :: rest) ++ suffix))
        (focusTape
          ((carrierHeaderCells (first :: rest)).reverse ++ left)
          (carrierGateCells (first :: rest) ++ suffix)) := by
    unfold LocalAcceptRun
    change
      workRunExact? TargetEmitterNavigator.headerMachine
          (TargetEmitterNavigator.headerWorkSteps
            0 (first :: rest).length)
          { state := TargetEmitterNavigator.State.headerStart
            tape :=
              focusTape left
                (carrierHeaderCells (first :: rest) ++
                  carrierGateCells (first :: rest) ++ suffix) } =
        some
          { state := TargetEmitterNavigator.State.accept
            tape :=
              focusTape
                ((carrierHeaderCells
                    (first :: rest)).reverse ++ left)
                (carrierGateCells (first :: rest) ++ suffix) }
    rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
    simpa [carrierHeaderCells, carrierGateCells,
      carrierGateCellsFor, TargetEmitterNavigator.pushCrossed,
      SourceParser.cell00, SourceParser.cell01,
      TargetEmitterNavigator.cell00,
      TargetEmitterNavigator.cell01,
      List.reverse_append, List.append_assoc] using
        TargetEmitterNavigator.header_nonempty_exact
          0 (first :: rest).length SourceParser.cell01
          (constantSecondCell
              (CNFToNANDCarrierEncoder.Source.firstBit first) ::
            SourceParser.cell01 ::
            constantSecondCell
                (CNFToNANDCarrierEncoder.Source.secondBit first) ::
              SourceParser.cell01 :: SourceParser.cell11 ::
                carrierGateCells rest ++ suffix)
          left (Or.inr (by
            simp [SourceParser.cell01,
              TargetEmitterNavigator.cell01]))
  have tail :
      AcceptPath graph (.node validationFirstRef)
        (.node validationFirstRef) 0
        (focusTape
          ((carrierHeaderCells (first :: rest)).reverse ++ left)
          (carrierGateCells (first :: rest) ++ suffix))
        (focusTape
          ((carrierHeaderCells (first :: rest)).reverse ++ left)
          (carrierGateCells (first :: rest) ++ suffix)) := .terminal _ _
  have path :=
    AcceptPath.step validationHeaderNode
      (.node validationFirstRef)
      (TargetEmitterNavigator.headerWorkSteps
        0 (first :: rest).length)
      0 _ _ _ validationHeaderNode_member localRun tail
  simpa [validationHeaderSteps, validationHeaderNode,
    validationHeaderRef, validationFirstRef,
    controlNode, controlRef, Node.reference] using path

def validationGateSteps : Nat :=
  validationGateSourceSteps + validationAdvanceSteps

def validationGatesSteps : List CNFToken → Nat
  | [] => 0
  | _ :: rest =>
      validationGateSteps + validationGatesSteps rest

theorem validationGatesSteps_eq (tokens : List CNFToken) :
    validationGatesSteps tokens = 26 * tokens.length := by
  induction tokens with
  | nil =>
      rfl
  | cons token rest inductionHypothesis =>
      simp [validationGatesSteps, validationGateSteps,
        validationGateSourceSteps, validationSourceSteps,
        validationAdvanceSteps, inductionHypothesis]
      omega

private theorem validation_gates_path
    (first : CNFToken) (rest : List CNFToken)
    (left suffix : List WorkSymbol) :
    AcceptPath graph (.node validationFirstRef)
      (.node validationProgramEndRef)
      (validationGatesSteps (first :: rest))
      (focusTape left
        (carrierGateCells (first :: rest) ++
          SourceParser.cell10 :: suffix))
      (focusTape
        ((carrierGateCells (first :: rest)).reverse ++ left)
        (SourceParser.cell10 :: suffix)) := by
  induction rest generalizing first left with
  | nil =>
      have sources :=
        validation_gate_sources_path first left
          (SourceParser.cell10 :: suffix)
      have advance :=
        validation_advance_programEnd_path suffix
          (constantSecondCell
              (CNFToNANDCarrierEncoder.Source.secondBit first) ::
            SourceParser.cell01 ::
            constantSecondCell
                (CNFToNANDCarrierEncoder.Source.firstBit first) ::
              SourceParser.cell01 :: left)
      have path :=
        AcceptPath.trans graph (.node validationFirstRef)
          (.node validationAdvanceRef)
          (.node validationProgramEndRef)
          validationGateSourceSteps validationAdvanceSteps _ _ _
          sources advance
      simpa [validationGatesSteps, validationGateSteps,
        carrierGateCells, carrierGateCellsFor,
        gateCells_tokenGate_eq,
        sourceCells_constant, List.reverse_append,
        List.append_assoc] using path
  | cons next tail inductionHypothesis =>
      let remaining := carrierGateCells (next :: tail)
      let afterSourcesLeft :=
        constantSecondCell
            (CNFToNANDCarrierEncoder.Source.secondBit first) ::
          SourceParser.cell01 ::
          constantSecondCell
              (CNFToNANDCarrierEncoder.Source.firstBit first) ::
            SourceParser.cell01 :: left
      let afterGateLeft :=
        SourceParser.cell11 :: SourceParser.cell01 ::
          afterSourcesLeft
      have sources :=
        validation_gate_sources_path first left
          (remaining ++ SourceParser.cell10 :: suffix)
      have advance :
          AcceptPath graph (.node validationAdvanceRef)
            (.node validationFirstRef) validationAdvanceSteps
            (focusTape afterSourcesLeft
              (SourceParser.cell01 :: SourceParser.cell11 ::
                remaining ++ SourceParser.cell10 :: suffix))
            (focusTape afterGateLeft
              (remaining ++ SourceParser.cell10 :: suffix)) := by
        have nextPath :=
          validation_advance_next_path SourceParser.cell01
            (constantSecondCell
                (CNFToNANDCarrierEncoder.Source.firstBit next) ::
              SourceParser.cell01 ::
              constantSecondCell
                  (CNFToNANDCarrierEncoder.Source.secondBit next) ::
                SourceParser.cell01 :: SourceParser.cell11 ::
                  carrierGateCells tail ++
                    SourceParser.cell10 :: suffix)
            afterSourcesLeft (Or.inr rfl)
        simpa [remaining, carrierGateCells,
          carrierGateCellsFor, List.append_assoc] using nextPath
      have firstGate :=
        AcceptPath.trans graph (.node validationFirstRef)
          (.node validationAdvanceRef) (.node validationFirstRef)
          validationGateSourceSteps validationAdvanceSteps _ _ _
          sources advance
      have tailPath :=
        inductionHypothesis next afterGateLeft
      have path :=
        AcceptPath.trans graph (.node validationFirstRef)
          (.node validationFirstRef)
          (.node validationProgramEndRef)
          (validationGateSourceSteps + validationAdvanceSteps)
          (validationGatesSteps (next :: tail)) _ _ _
          firstGate tailPath
      simpa [validationGatesSteps, validationGateSteps,
        carrierGateCells, carrierGateCellsFor,
        gateCells_tokenGate_eq,
        sourceCells_constant, remaining,
        afterSourcesLeft, afterGateLeft,
        List.reverse_append, List.append_assoc] using path

def validationFooterSteps : Nat := 11

private theorem validation_footer_path
    (left suffix : List WorkSymbol) :
    AcceptPath graph (.node validationProgramEndRef)
      (.node validationRewindRef) validationFooterSteps
      (focusTape left (carrierFooterCells ++ suffix))
      (focusTape
        (SourceParser.cell00 :: SourceParser.cell10 :: left)
        (SourceParser.sourceCells (.constant false) ++
          [SourceParser.cell10, SourceParser.cell01,
            SourceParser.cell10, SourceParser.cell11] ++ suffix)) := by
  let outputTape :=
    focusTape
      (SourceParser.cell00 :: SourceParser.cell10 :: left)
      (SourceParser.sourceCells (.constant false) ++
        [SourceParser.cell10, SourceParser.cell01,
          SourceParser.cell10, SourceParser.cell11] ++ suffix)
  have programRun :
      LocalAcceptRun validationProgramEndNode 2
        (focusTape left (carrierFooterCells ++ suffix))
        outputTape := by
    unfold LocalAcceptRun
    change
      workRunExact? TargetEmitterNavigator.programEndMachine 2
          { state := TargetEmitterNavigator.State.programFirst
            tape := focusTape left (carrierFooterCells ++ suffix) } =
        some
          { state := TargetEmitterNavigator.State.accept
            tape := outputTape }
    rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
    simpa [carrierFooterCells, outputTape,
      SourceParser.sourceCells,
      SourceParser.cell00, SourceParser.cell01,
      SourceParser.cell10, SourceParser.cell11,
      TargetEmitterNavigator.cell00,
      TargetEmitterNavigator.cell01,
      TargetEmitterNavigator.cell10,
      List.append_assoc] using
        TargetEmitterNavigator.programEnd_exact left
          (SourceParser.cell00 ::
            SourceParser.cell10 :: SourceParser.cell01 ::
              SourceParser.cell10 :: SourceParser.cell11 :: suffix)
          SourceParser.cell01
  have outputFirstRun :
      LocalRejectRun validationOutputFirstNode 1
        outputTape outputTape := by
    unfold LocalRejectRun
    change
      workRunExact? TargetEmitterNavigator.sourceFirstMachine 1
          { state := TargetEmitterNavigator.State.sourceFirst
            tape := outputTape } =
        some
          { state := TargetEmitterNavigator.State.reject
            tape := outputTape }
    change
      workRunExact? TargetEmitterNavigator.sourceFirstMachine 1
          { state := TargetEmitterNavigator.State.sourceFirst
            tape :=
              focusTape
                (SourceParser.cell00 :: SourceParser.cell10 :: left)
                (SourceParser.cell01 :: SourceParser.cell00 ::
                  SourceParser.cell10 :: SourceParser.cell01 ::
                    SourceParser.cell10 :: SourceParser.cell11 ::
                      suffix) } =
        some
          { state := TargetEmitterNavigator.State.reject
            tape :=
              focusTape
                (SourceParser.cell00 :: SourceParser.cell10 :: left)
                (SourceParser.cell01 :: SourceParser.cell00 ::
                  SourceParser.cell10 :: SourceParser.cell01 ::
                    SourceParser.cell10 :: SourceParser.cell11 ::
                      suffix) }
    rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
    simpa [SourceParser.cell01,
      TargetEmitterNavigator.cell01] using
        TargetEmitterNavigator.sourceFirst_noninput_exact
          (SourceParser.cell00 :: SourceParser.cell10 :: left)
          (SourceParser.cell00 ::
            SourceParser.cell10 :: SourceParser.cell01 ::
              SourceParser.cell10 :: SourceParser.cell11 :: suffix)
  have outputNonInputRun :
      LocalRejectRun validationOutputNonInputNode 2
        outputTape outputTape := by
    unfold LocalRejectRun
    change
      workRunExact? TargetEmitterNavigator.nonInputMachine 2
          { state := TargetEmitterNavigator.State.nonInputFirst
            tape := outputTape } =
        some
          { state := TargetEmitterNavigator.State.reject
            tape := outputTape }
    change
      workRunExact? TargetEmitterNavigator.nonInputMachine 2
          { state := TargetEmitterNavigator.State.nonInputFirst
            tape :=
              focusTape
                (SourceParser.cell00 :: SourceParser.cell10 :: left)
                (SourceParser.cell01 :: SourceParser.cell00 ::
                  SourceParser.cell10 :: SourceParser.cell01 ::
                    SourceParser.cell10 :: SourceParser.cell11 ::
                      suffix) } =
        some
          { state := TargetEmitterNavigator.State.reject
            tape :=
              focusTape
                (SourceParser.cell00 :: SourceParser.cell10 :: left)
                (SourceParser.cell01 :: SourceParser.cell00 ::
                  SourceParser.cell10 :: SourceParser.cell01 ::
                    SourceParser.cell10 :: SourceParser.cell11 ::
                      suffix) }
    rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
    simpa [SourceParser.cell00, SourceParser.cell01,
      TargetEmitterNavigator.cell00,
      TargetEmitterNavigator.cell01] using
        TargetEmitterNavigator.nonInput_constantFalse_exact
          (SourceParser.cell00 :: SourceParser.cell10 :: left)
          (SourceParser.cell10 :: SourceParser.cell01 ::
            SourceParser.cell10 :: SourceParser.cell11 :: suffix)
  have outputRun :
      LocalAcceptRun validationOutputNode 2
        outputTape outputTape := by
    unfold LocalAcceptRun
    change
      workRunExact? TargetEmitterNavigator.constantMachine 2
          { state := TargetEmitterNavigator.State.constantFirst
            tape := outputTape } =
        some
          { state := TargetEmitterNavigator.State.accept
            tape := outputTape }
    change
      workRunExact? TargetEmitterNavigator.constantMachine 2
          { state := TargetEmitterNavigator.State.constantFirst
            tape :=
              focusTape
                (SourceParser.cell00 :: SourceParser.cell10 :: left)
                (SourceParser.cell01 :: SourceParser.cell00 ::
                  SourceParser.cell10 :: SourceParser.cell01 ::
                    SourceParser.cell10 :: SourceParser.cell11 ::
                      suffix) } =
        some
          { state := TargetEmitterNavigator.State.accept
            tape :=
              focusTape
                (SourceParser.cell00 :: SourceParser.cell10 :: left)
                (SourceParser.cell01 :: SourceParser.cell00 ::
                  SourceParser.cell10 :: SourceParser.cell01 ::
                    SourceParser.cell10 :: SourceParser.cell11 ::
                      suffix) }
    rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
    simpa [SourceParser.cell00, SourceParser.cell01,
      TargetEmitterNavigator.cell00,
      TargetEmitterNavigator.cell01] using
        TargetEmitterNavigator.constantFalse_exact
          (SourceParser.cell00 :: SourceParser.cell10 :: left)
          (SourceParser.cell10 :: SourceParser.cell01 ::
            SourceParser.cell10 :: SourceParser.cell11 :: suffix)
  have terminal :
      AcceptPath graph (.node validationRewindRef)
        (.node validationRewindRef) 0 outputTape outputTape :=
    .terminal _ _
  have outputPath :=
    AcceptPath.step validationOutputNode
      (.node validationRewindRef) 2 0 _ _ _
      validationOutputNode_member outputRun terminal
  have nonInputPath :=
    AcceptPath.stepReject validationOutputNonInputNode
      (.node validationRewindRef) 2 3 _ _ _
      validationOutputNonInputNode_member outputNonInputRun outputPath
  have firstPath :=
    AcceptPath.stepReject validationOutputFirstNode
      (.node validationRewindRef) 1 6 _ _ _
      validationOutputFirstNode_member outputFirstRun nonInputPath
  have path :=
    AcceptPath.step validationProgramEndNode
      (.node validationRewindRef) 2 8 _ _ _
      validationProgramEndNode_member programRun firstPath
  simpa [validationFooterSteps, carrierFooterCells, outputTape,
    validationProgramEndNode, validationOutputFirstNode,
    validationOutputNonInputNode, validationOutputNode,
    validationProgramEndRef, validationOutputFirstRef,
    validationOutputNonInputRef, validationOutputRef,
    validationRewindRef, controlNode, controlRef,
    Node.reference, List.append_assoc] using path

private theorem workRunExact?_append
    (machine : WorkMachine) (first second : Nat)
    (initial middle final : WorkConfiguration)
    (firstRun :
      workRunExact? machine first initial = some middle)
    (secondRun :
      workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial = some final :=
  PipelineMachineSimulation.workRunExact?_compose
    machine first second initial middle final firstRun secondRun

private theorem validationRewind_scan_exact
    (nearest outsideLeft right : List WorkSymbol)
    (packed :
      ∀ symbol, symbol ∈ nearest →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? CNFToNANDCarrierTokenReader.Rewind.machine
        nearest.length
        (TargetEmitter.configAtLeftWord
          CNFToNANDCarrierTokenReader.Rewind.State.scan
          (nearest ++
            CNFToNANDCarrierTokenReader.Rewind.sourceLeftBoundary ::
              outsideLeft)
          right) =
      some
        (TargetEmitter.configAtLeftWord
          CNFToNANDCarrierTokenReader.Rewind.State.scan
          (CNFToNANDCarrierTokenReader.Rewind.sourceLeftBoundary ::
            outsideLeft)
          (nearest.reverse ++ right)) := by
  induction nearest generalizing right with
  | nil =>
      rfl
  | cons symbol rest inductionHypothesis =>
      have symbolPacked :=
        packed symbol (List.Mem.head rest)
      have restPacked :
          ∀ item, item ∈ rest →
            TargetEmitter.PackedSymbol item := by
        intro item member
        exact packed item (List.Mem.tail symbol member)
      have first :
          workRunExact?
              CNFToNANDCarrierTokenReader.Rewind.machine 1
              (TargetEmitter.configAtLeftWord
                CNFToNANDCarrierTokenReader.Rewind.State.scan
                (symbol :: rest ++
                  CNFToNANDCarrierTokenReader.Rewind.sourceLeftBoundary ::
                    outsideLeft)
                right) =
            some
              (TargetEmitter.configAtLeftWord
                CNFToNANDCarrierTokenReader.Rewind.State.scan
                (rest ++
                  CNFToNANDCarrierTokenReader.Rewind.sourceLeftBoundary ::
                    outsideLeft)
                (symbol :: right)) := by
        unfold workRunExact?
        cases rest <;> cases symbolPacked <;> rfl
      have tail :=
        inductionHypothesis (symbol :: right) restPacked
      have combined :=
        workRunExact?_append
          CNFToNANDCarrierTokenReader.Rewind.machine
          1 rest.length _ _ _ first tail
      simpa [List.reverse_cons, List.append_assoc,
        Nat.add_comm] using combined

private theorem validationRewind_exact
    (nearest outsideLeft right : List WorkSymbol)
    (packed :
      ∀ symbol, symbol ∈ nearest →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? CNFToNANDCarrierTokenReader.Rewind.machine
        (nearest.length + 1)
        (TargetEmitter.configAtLeftWord
          CNFToNANDCarrierTokenReader.Rewind.State.scan
          (nearest ++
            CNFToNANDCarrierTokenReader.Rewind.sourceLeftBoundary ::
              outsideLeft)
          right) =
      some
        (TargetEmitter.configAtWord
          CNFToNANDCarrierTokenReader.Rewind.State.accept
          (CNFToNANDCarrierTokenReader.Rewind.sourceLeftBoundary ::
            outsideLeft)
          (nearest.reverse ++ right)) := by
  have scanned :=
    validationRewind_scan_exact nearest outsideLeft right packed
  have boundary :
      workRunExact? CNFToNANDCarrierTokenReader.Rewind.machine 1
          (TargetEmitter.configAtLeftWord
            CNFToNANDCarrierTokenReader.Rewind.State.scan
            (CNFToNANDCarrierTokenReader.Rewind.sourceLeftBoundary ::
              outsideLeft)
            (nearest.reverse ++ right)) =
        some
          (TargetEmitter.configAtWord
            CNFToNANDCarrierTokenReader.Rewind.State.accept
            (CNFToNANDCarrierTokenReader.Rewind.sourceLeftBoundary ::
              outsideLeft)
            (nearest.reverse ++ right)) := by
    simp only [TargetEmitter.configAtLeftWord]
    unfold workRunExact?
    rw [CNFToNANDCarrierTokenReader.Rewind.boundary_step]
    cases equality : nearest.reverse ++ right <;>
      simp [workRunExact?, WorkTape.move, WorkTape.moveRight,
        TargetEmitter.configAtWord]
  exact
    workRunExact?_append
      CNFToNANDCarrierTokenReader.Rewind.machine
      nearest.length 1 _ _ _ scanned boundary

def validationScannedPrefix (tokens : List CNFToken) :
    List WorkSymbol :=
  carrierHeaderCells tokens ++ carrierGateCells tokens ++
    [SourceParser.cell10, SourceParser.cell00,
      SourceParser.cell01]

def validationRewindWorkSteps (tokens : List CNFToken) : Nat :=
  (validationScannedPrefix tokens).length + 1

def validationRewindSteps (tokens : List CNFToken) : Nat :=
  validationRewindWorkSteps tokens + 1

private theorem validation_rewind_layout_path
    (tokens : List CNFToken)
    (outsideLeft suffix : List WorkSymbol)
    (packed :
      ∀ symbol, symbol ∈ validationScannedPrefix tokens →
        TargetEmitter.PackedSymbol symbol) :
    AcceptPath graph (.node validationRewindRef)
      (.node (passHeaderRef .count))
      (validationRewindSteps tokens)
      (focusTape
        (SourceParser.cell00 :: SourceParser.cell10 ::
          (carrierGateCells tokens).reverse ++
            (carrierHeaderCells tokens).reverse ++
              TargetEmitter.sourceLeftBoundary :: outsideLeft)
        (SourceParser.sourceCells (.constant false) ++
          [SourceParser.cell10, SourceParser.cell01,
            SourceParser.cell10, SourceParser.cell11,
            TargetEmitter.sourceTargetBoundary] ++ suffix))
      (focusTape
        (TargetEmitter.sourceLeftBoundary :: outsideLeft)
        (carrierHeaderCells tokens ++ carrierGateCells tokens ++
          carrierFooterCells ++
            TargetEmitter.sourceTargetBoundary :: suffix)) := by
  have reversePacked :
      ∀ symbol,
        symbol ∈ (validationScannedPrefix tokens).reverse →
          TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    exact packed symbol (List.mem_reverse.mp member)
  have localRun :
      LocalAcceptRun validationRewindNode
        (validationRewindWorkSteps tokens)
        (focusTape
          (SourceParser.cell00 :: SourceParser.cell10 ::
            (carrierGateCells tokens).reverse ++
              (carrierHeaderCells tokens).reverse ++
                TargetEmitter.sourceLeftBoundary :: outsideLeft)
          (SourceParser.sourceCells (.constant false) ++
            [SourceParser.cell10, SourceParser.cell01,
              SourceParser.cell10, SourceParser.cell11,
              TargetEmitter.sourceTargetBoundary] ++ suffix))
        (focusTape
          (TargetEmitter.sourceLeftBoundary :: outsideLeft)
          (carrierHeaderCells tokens ++ carrierGateCells tokens ++
            carrierFooterCells ++
              TargetEmitter.sourceTargetBoundary :: suffix)) := by
    unfold LocalAcceptRun
    change
      workRunExact? CNFToNANDCarrierTokenReader.Rewind.machine
          (validationRewindWorkSteps tokens)
          { state := CNFToNANDCarrierTokenReader.Rewind.State.scan
            tape :=
              focusTape
                (SourceParser.cell00 :: SourceParser.cell10 ::
                  (carrierGateCells tokens).reverse ++
                    (carrierHeaderCells tokens).reverse ++
                      TargetEmitter.sourceLeftBoundary :: outsideLeft)
                (SourceParser.sourceCells (.constant false) ++
                  [SourceParser.cell10, SourceParser.cell01,
                    SourceParser.cell10, SourceParser.cell11,
                    TargetEmitter.sourceTargetBoundary] ++ suffix) } =
        some
          { state := CNFToNANDCarrierTokenReader.Rewind.State.accept
            tape :=
              focusTape
                (TargetEmitter.sourceLeftBoundary :: outsideLeft)
                (carrierHeaderCells tokens ++
                  carrierGateCells tokens ++ carrierFooterCells ++
                    TargetEmitter.sourceTargetBoundary :: suffix) }
    have exactRun :=
      validationRewind_exact
        (validationScannedPrefix tokens).reverse outsideLeft
        (SourceParser.cell00 ::
          SourceParser.cell10 :: SourceParser.cell01 ::
            SourceParser.cell10 :: SourceParser.cell11 ::
              TargetEmitter.sourceTargetBoundary :: suffix)
        reversePacked
    have stepsEq :
        ((validationScannedPrefix tokens).reverse).length + 1 =
          validationRewindWorkSteps tokens := by
      simp [validationRewindWorkSteps]
    rw [stepsEq] at exactRun
    rw [targetEmitter_configAtWord_eq,
      targetEmitter_configAtWord_eq]
    simpa [validationScannedPrefix,
      carrierFooterCells, focusTape,
      SourceParser.sourceCells,
      CNFToNANDCarrierTokenReader.Rewind.sourceLeftBoundary,
      TargetEmitter.configAtLeftWord,
      TargetEmitter.configAtWord,
      List.reverse_append, List.append_assoc] using exactRun
  have terminal :
      AcceptPath graph (.node (passHeaderRef .count))
        (.node (passHeaderRef .count)) 0
        (focusTape
          (TargetEmitter.sourceLeftBoundary :: outsideLeft)
          (carrierHeaderCells tokens ++ carrierGateCells tokens ++
            carrierFooterCells ++
              TargetEmitter.sourceTargetBoundary :: suffix))
        (focusTape
          (TargetEmitter.sourceLeftBoundary :: outsideLeft)
          (carrierHeaderCells tokens ++ carrierGateCells tokens ++
            carrierFooterCells ++
              TargetEmitter.sourceTargetBoundary :: suffix)) :=
    .terminal _ _
  have path :=
    AcceptPath.step validationRewindNode
      (.node (passHeaderRef .count))
      (validationRewindWorkSteps tokens) 0 _ _ _
      validationRewindNode_member localRun terminal
  simpa [validationRewindSteps, validationRewindNode,
    validationRewindRef, controlNode, controlRef,
    Node.reference] using path

theorem carrierGateCells_length (tokens : List CNFToken) :
    (carrierGateCells tokens).length = 6 * tokens.length := by
  induction tokens with
  | nil =>
      rfl
  | cons token rest inductionHypothesis =>
      simp [carrierGateCells, carrierGateCellsFor,
        inductionHypothesis]
      omega

theorem carrierHeaderCells_length (tokens : List CNFToken) :
    (carrierHeaderCells tokens).length =
      2 * tokens.length + 6 := by
  simp [carrierHeaderCells, SourceParser.natCells_length]
  omega

theorem validationHeaderSteps_eq (tokens : List CNFToken) :
    validationHeaderSteps tokens = 2 * tokens.length + 8 := by
  unfold validationHeaderSteps TargetEmitterNavigator.headerWorkSteps
  omega

theorem validationRewindSteps_eq (tokens : List CNFToken) :
    validationRewindSteps tokens = 8 * tokens.length + 11 := by
  simp [validationRewindSteps, validationRewindWorkSteps,
    validationScannedPrefix, carrierHeaderCells_length,
    carrierGateCells_length]
  omega

def validationSteps (formula : CNFFormula) : Nat :=
  validationHeaderSteps (CNFToNANDWorkspace.formulaTokens formula) +
    validationGatesSteps (CNFToNANDWorkspace.formulaTokens formula) +
    validationFooterSteps +
    validationRewindSteps
      (CNFToNANDWorkspace.formulaTokens formula)

theorem validationSteps_eq (formula : CNFFormula) :
    validationSteps formula =
      36 * (CNFToNANDWorkspace.formulaTokens formula).length + 30 := by
  rw [validationSteps, validationHeaderSteps_eq,
    validationGatesSteps_eq, validationRewindSteps_eq]
  unfold validationFooterSteps
  omega

def validationOutsideLeft (formula : CNFFormula) :
    List WorkSymbol :=
  (TargetEmitterRuntime.logicalLeftWorkspace
    (CNFToNANDWorkspace.capacity formula) 0
    (CNFToNANDWorkspace.postLedgerRegisters formula) []).tail

theorem validationLeftWorkspace_eq (formula : CNFFormula) :
    TargetEmitterRuntime.logicalLeftWorkspace
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) [] =
      TargetEmitter.sourceLeftBoundary ::
        validationOutsideLeft formula := by
  rfl

private theorem canonicalSource_eq_scannedPrefix_append
    (formula : CNFFormula) :
    canonicalSource formula =
      validationScannedPrefix
          (CNFToNANDWorkspace.formulaTokens formula) ++
        [SourceParser.cell00, SourceParser.cell10,
          SourceParser.cell01, SourceParser.cell10,
          SourceParser.cell11] := by
  rw [canonicalSource_eq_carrier_layout]
  simp [validationScannedPrefix, carrierFooterCells,
    SourceParser.sourceCells, List.append_assoc]

private theorem validationScannedPrefix_packed
    (formula : CNFFormula) :
    ∀ symbol,
      symbol ∈ validationScannedPrefix
          (CNFToNANDWorkspace.formulaTokens formula) →
        TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  apply
    TargetEmitter.circuitCells_packed
      (CNFToNANDWorkspace.carrierCircuit formula) symbol
  change symbol ∈ canonicalSource formula
  rw [canonicalSource_eq_scannedPrefix_append]
  exact List.mem_append_left _ member

/-- Exact certificate-free carrier validation: after checking the canonical
header, every inert token gate, the fixed false output, and the retained
terminators, the controller has restored the head to the first carrier cell
and entered the count-pass header. -/
theorem canonical_validation_path (formula : CNFFormula) :
    AcceptPath graph (.node validationHeaderRef)
      (.node (passHeaderRef .count)) (validationSteps formula)
      (TargetEmitterRuntime.logicalTape
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (canonicalSource formula) [])
      (TargetEmitterRuntime.logicalTape
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (canonicalSource formula) []) := by
  cases tokensEq :
      CNFToNANDWorkspace.formulaTokens formula with
  | nil =>
      exact
        False.elim
          (CNFToNANDWorkspace.formulaTokens_ne_nil formula tokensEq)
  | cons first rest =>
      let outsideLeft := validationOutsideLeft formula
      let workspaceLeft :=
        TargetEmitter.sourceLeftBoundary :: outsideLeft
      let footerTail :=
        SourceParser.cell00 ::
          SourceParser.sourceCells (.constant false) ++
            [SourceParser.cell10, SourceParser.cell01,
              SourceParser.cell10, SourceParser.cell11,
              TargetEmitter.sourceTargetBoundary]
      have headerPath :=
        validation_header_layout_path first rest workspaceLeft
          (carrierFooterCells ++
            [TargetEmitter.sourceTargetBoundary])
      have gatesPath :=
        validation_gates_path first rest
          ((carrierHeaderCells (first :: rest)).reverse ++
            workspaceLeft)
          footerTail
      have gatesPath' :
          AcceptPath graph (.node validationFirstRef)
            (.node validationProgramEndRef)
            (validationGatesSteps (first :: rest))
            (focusTape
              ((carrierHeaderCells (first :: rest)).reverse ++
                workspaceLeft)
              (carrierGateCells (first :: rest) ++
                (carrierFooterCells ++
                  [TargetEmitter.sourceTargetBoundary])))
            (focusTape
              ((carrierGateCells (first :: rest)).reverse ++
                (carrierHeaderCells (first :: rest)).reverse ++
                  workspaceLeft)
              (carrierFooterCells ++
                [TargetEmitter.sourceTargetBoundary])) := by
        simpa [footerTail, carrierFooterCells,
          SourceParser.sourceCells, List.append_assoc] using gatesPath
      have footerPath :=
        validation_footer_path
          ((carrierGateCells (first :: rest)).reverse ++
            (carrierHeaderCells (first :: rest)).reverse ++
              workspaceLeft)
          [TargetEmitter.sourceTargetBoundary]
      have rewindPath :=
        validation_rewind_layout_path (first :: rest)
          outsideLeft [] (by
            intro symbol member
            have packed :=
              validationScannedPrefix_packed formula symbol
            rw [tokensEq] at packed
            exact packed member)
      have headerGates :=
        AcceptPath.trans graph (.node validationHeaderRef)
          (.node validationFirstRef)
          (.node validationProgramEndRef)
          (validationHeaderSteps (first :: rest))
          (validationGatesSteps (first :: rest)) _ _ _
          headerPath gatesPath'
      have throughFooter :=
        AcceptPath.trans graph (.node validationHeaderRef)
          (.node validationProgramEndRef)
          (.node validationRewindRef)
          (validationHeaderSteps (first :: rest) +
            validationGatesSteps (first :: rest))
          validationFooterSteps _ _ _ headerGates footerPath
      have path :=
        AcceptPath.trans graph (.node validationHeaderRef)
          (.node validationRewindRef)
          (.node (passHeaderRef .count))
          (validationHeaderSteps (first :: rest) +
            validationGatesSteps (first :: rest) +
              validationFooterSteps)
          (validationRewindSteps (first :: rest)) _ _ _
          throughFooter rewindPath
      simpa [validationSteps, tokensEq, footerTail,
        outsideLeft, workspaceLeft, focusTape,
        validationLeftWorkspace_eq,
        TargetEmitterRuntime.logicalTape,
        TargetEmitterRuntime.logicalConfiguration,
        TargetEmitterRuntime.logicalWord,
        canonicalSource_eq_carrier_layout,
        SourceParser.sourceCells, SourceParser.packedTokenCells,
        List.append_assoc] using path

/-- Transport the canonical finite-window validation trace to any physical
workspace carrying the same infinite blank tape. -/
theorem validation_path_of_represents
    (formula : CNFFormula) (initialTape : WorkTape)
    (represents :
      TapeRepresents validationHeaderRef.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (canonicalSource formula) [] initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node validationHeaderRef)
        (.node (passHeaderRef .count)) (validationSteps formula)
        initialTape finalTape ∧
      TapeRepresents (passHeaderRef .count).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (canonicalSource formula) [] finalTape := by
  rcases
      AcceptPath.transport (canonical_validation_path formula)
        represents.tape with
    ⟨finalTape, path, finalEquivalent⟩
  refine ⟨finalTape, path, ?_⟩
  exact
    { state := by
        simpa using
          (TargetEmitterRuntime.logicalConfiguration_state
            (passHeaderRef .count).startState
            (CNFToNANDWorkspace.capacity formula) 0
            (CNFToNANDWorkspace.postLedgerRegisters formula) []
            (canonicalSource formula) []).symm
      tape := finalEquivalent }

def canonicalPrefixSteps (formula : CNFFormula) : Nat :=
  initializedResetSteps formula + validationSteps formula

/-- The complete owned prefix, from the raw canonical carrier input through
stack initialization, reset, carrier validation, and the launch of the
count-pass header. -/
theorem canonical_prefix_path (formula : CNFFormula) :
    ∃ finalTape,
      AcceptPath graph (.node scannerRef)
        (.node (passHeaderRef .count))
        (canonicalPrefixSteps formula)
        (rawInputWorkTape
          (encodeCircuit
            (CNFToNANDWorkspace.carrierCircuit formula)))
        finalTape ∧
      TapeRepresents (passHeaderRef .count).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.postLedgerRegisters formula) []
        (canonicalSource formula) [] finalTape := by
  rcases scanner_ledger_stack_reset_path formula with
    ⟨validationTape, prefixPath, validationRepresents⟩
  rcases
      validation_path_of_represents formula validationTape
        validationRepresents with
    ⟨finalTape, validationPath, finalRepresents⟩
  refine ⟨finalTape, ?_, finalRepresents⟩
  exact
    AcceptPath.trans graph (.node scannerRef)
      (.node validationHeaderRef)
      (.node (passHeaderRef .count))
      (initializedResetSteps formula) (validationSteps formula)
      _ _ _ prefixPath validationPath

end PNP.Concrete.CNFToNANDControllerCanonicalTrace

/-
Copyright (c) 2026 PNP Labs.

Exact graph paths for the fixed source-capture and cursor-restoration control
nodes.

This layer lifts only one already-materialized local controller at a time
and its fixed graph bridge.  Execution of the source-template blocks between
capture and restoration is intentionally outside this module.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerTrace
import PNP.Concrete.LockedNANDTargetEmitterRuntimeSourceControl

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerSourceTrace

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController

abbrev SourceKind := TargetEmitterPlan.SourceKind

/-- Natural carried by a classified source.  Constants carry no unary
natural even though the uniform interface retains a value parameter. -/
def capturedValue : SourceKind → Nat → Nat
  | .input, value => value
  | .constantFalse, _ => 0
  | .constantTrue, _ => 0
  | .gate, value => value

def captureSourceCells (kind : SourceKind) (value : Nat) :
    List WorkSymbol :=
  TargetEmitterSourceCapture.sourceCells
    (Plan.captureKind kind) (capturedValue kind value)

def captureMarkedSourceCells (kind : SourceKind) (value : Nat) :
    List WorkSymbol :=
  TargetEmitterSourceCapture.markedSourceCells
    (Plan.captureKind kind) (capturedValue kind value)

def captureWorkSteps (kind : SourceKind)
    (beforeLength scratch value : Nat) : Nat :=
  match kind with
  | .input | .gate =>
      TargetEmitterSourceCapture.naturalWorkSteps
        beforeLength scratch value
  | .constantFalse | .constantTrue =>
      TargetEmitterSourceCapture.constantWorkSteps beforeLength

def capturePathSteps (kind : SourceKind)
    (beforeLength scratch value : Nat) : Nat :=
  captureWorkSteps kind beforeLength scratch value + 1

def restorePathSteps (beforeLength : Nat) : Nat :=
  beforeLength + 2

private theorem localAcceptRun_of_exact
    (node : Node) (steps : Nat)
    (initial final : WorkConfiguration)
    (initialState :
      initial.state = node.program.startState)
    (finalState :
      final.state = node.program.acceptState)
    (exactRun :
      workRunExact? node.program steps initial = some final) :
    LocalAcceptRun node steps initial.tape final.tape := by
  rcases initial with ⟨initialStateValue, initialTape⟩
  rcases final with ⟨finalStateValue, finalTape⟩
  change initialStateValue = node.program.startState at initialState
  change finalStateValue = node.program.acceptState at finalState
  subst initialStateValue
  subst finalStateValue
  exact exactRun

private theorem capture_exact
    (kind : SourceKind)
    (capacity scratch value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (capacityBound :
      scratch + capturedValue kind value + 1 ≤ capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents
        TargetEmitterSourceCapture.startState
        capacity scratch registers checks before
        (captureSourceCells kind value ++ afterSource)
        target actual) :
    ∃ actualFinal,
      workRunExact?
          (TargetEmitterSourceCapture.machine
            (Plan.captureKind kind))
          (captureWorkSteps kind before.length scratch value)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterSourceCapture.acceptState
        capacity (scratch + capturedValue kind value)
        registers checks
        (before ++ captureMarkedSourceCells kind value ++
          afterSource)
        target actualFinal := by
  cases kind with
  | input =>
      simpa [capturedValue, captureSourceCells,
        captureMarkedSourceCells, captureWorkSteps,
        Plan.captureKind,
        TargetEmitterSourceCapture.NatKind.sourceKind] using
        (TargetEmitterRuntimeSourceControl.captureNatural_exact
          TargetEmitterSourceCapture.NatKind.input
          capacity scratch value registers checks
          before afterSource target actual
          (by simpa [capturedValue] using capacityBound)
          beforePacked
          (by simpa [captureSourceCells, capturedValue,
            Plan.captureKind,
            TargetEmitterSourceCapture.NatKind.sourceKind]
            using represents))
  | constantFalse =>
      simpa [capturedValue, captureSourceCells,
        captureMarkedSourceCells, captureWorkSteps,
        Plan.captureKind] using
        (TargetEmitterRuntimeSourceControl.captureConstantFalse_exact
          capacity scratch registers checks
          before afterSource target actual
          (by simpa [capturedValue] using capacityBound)
          beforePacked
          (by simpa [captureSourceCells, capturedValue,
            Plan.captureKind,
            TargetEmitterSourceCapture.NatKind.sourceKind]
            using represents))
  | constantTrue =>
      simpa [capturedValue, captureSourceCells,
        captureMarkedSourceCells, captureWorkSteps,
        Plan.captureKind] using
        (TargetEmitterRuntimeSourceControl.captureConstantTrue_exact
          capacity scratch registers checks
          before afterSource target actual
          (by simpa [capturedValue] using capacityBound)
          beforePacked
          (by simpa [captureSourceCells, capturedValue,
            Plan.captureKind,
            TargetEmitterSourceCapture.NatKind.sourceKind]
            using represents))
  | gate =>
      simpa [capturedValue, captureSourceCells,
        captureMarkedSourceCells, captureWorkSteps,
        Plan.captureKind,
        TargetEmitterSourceCapture.NatKind.sourceKind] using
        (TargetEmitterRuntimeSourceControl.captureNatural_exact
          TargetEmitterSourceCapture.NatKind.gate
          capacity scratch value registers checks
          before afterSource target actual
          (by simpa [capturedValue] using capacityBound)
          beforePacked
          (by simpa [captureSourceCells, capturedValue,
            Plan.captureKind,
            TargetEmitterSourceCapture.NatKind.sourceKind]
            using represents))

private theorem capture_path_of_node
    (node : Node) (continuation : NodeRef)
    (kind : SourceKind)
    (member : node ∈ graph.nodes)
    (programEq :
      node.program =
        TargetEmitterSourceCapture.machine (Plan.captureKind kind))
    (acceptEq : node.onAccept = .node continuation)
    (capacity scratch value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (capacityBound :
      scratch + capturedValue kind value + 1 ≤ capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents
        TargetEmitterSourceCapture.startState
        capacity scratch registers checks before
        (captureSourceCells kind value ++ afterSource)
        target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node node.reference) (.node continuation)
          (capturePathSteps kind before.length scratch value)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterSourceCapture.acceptState
        capacity (scratch + capturedValue kind value)
        registers checks
        (before ++ captureMarkedSourceCells kind value ++
          afterSource)
        target actualFinal := by
  rcases capture_exact kind capacity scratch value registers checks
      before afterSource target actual capacityBound beforePacked
      represents with
    ⟨actualFinal, exactRun, finalRepresents⟩
  have initialState :
      actual.state = node.program.startState := by
    rw [programEq]
    exact
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents.state_eq
        represents
  have finalState :
      actualFinal.state = node.program.acceptState := by
    rw [programEq]
    exact TargetEmitterRuntime.Represents.state_eq finalRepresents
  have nodeRun :
      workRunExact? node.program
          (captureWorkSteps kind before.length scratch value)
          actual =
        some actualFinal := by
    rw [programEq]
    exact exactRun
  have localRun :
      LocalAcceptRun node
        (captureWorkSteps kind before.length scratch value)
        actual.tape actualFinal.tape :=
    localAcceptRun_of_exact node
      (captureWorkSteps kind before.length scratch value)
      actual actualFinal initialState finalState nodeRun
  have tail :
      AcceptPath graph (.node continuation) (.node continuation) 0
        actualFinal.tape actualFinal.tape :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.step node (.node continuation)
      (captureWorkSteps kind before.length scratch value) 0
      actual.tape actualFinal.tape actualFinal.tape
      member localRun (by simpa [acceptEq] using tail)
  refine ⟨actualFinal, ?_, finalRepresents⟩
  simpa [capturePathSteps] using path

private theorem leftCaptureNode_member (kind : SourceKind) :
    leftCaptureNode kind ∈ graph.nodes := by
  apply controlNode_member_nodes
  cases kind <;>
    simp [controlNodes, leftControlNodes, Plan.sourceKinds]

private theorem rightCaptureNode_member (kind : SourceKind) :
    rightCaptureNode kind ∈ graph.nodes := by
  apply controlNode_member_nodes
  cases kind <;>
    simp [controlNodes, rightControlNodes, Plan.sourceKinds]

private theorem outputCaptureNode_member (kind : SourceKind) :
    outputCaptureNode kind ∈ graph.nodes := by
  apply controlNode_member_nodes
  cases kind <;>
    simp [controlNodes, outputControlNodes, Plan.sourceKinds]

/-- One left-source capture node followed by its fixed bridge into the
materialized left source block. -/
theorem leftCapture_path
    (kind : SourceKind)
    (capacity scratch value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (capacityBound :
      scratch + capturedValue kind value + 1 ≤ capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents
        TargetEmitterSourceCapture.startState
        capacity scratch registers checks before
        (captureSourceCells kind value ++ afterSource)
        target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node (leftCaptureRef kind))
          (.node (leftSourceRef kind))
          (capturePathSteps kind before.length scratch value)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterSourceCapture.acceptState
        capacity (scratch + capturedValue kind value)
        registers checks
        (before ++ captureMarkedSourceCells kind value ++
          afterSource)
        target actualFinal := by
  simpa [leftCaptureNode, leftCaptureRef, controlNode,
    controlRef, Node.reference] using
    (capture_path_of_node (leftCaptureNode kind)
      (leftSourceRef kind) kind
      (leftCaptureNode_member kind) rfl rfl
      capacity scratch value registers checks
      before afterSource target actual capacityBound
      beforePacked represents)

/-- One right-source capture node followed by its fixed bridge into the
materialized right source block. -/
theorem rightCapture_path
    (kind : SourceKind)
    (capacity scratch value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (capacityBound :
      scratch + capturedValue kind value + 1 ≤ capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents
        TargetEmitterSourceCapture.startState
        capacity scratch registers checks before
        (captureSourceCells kind value ++ afterSource)
        target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node (rightCaptureRef kind))
          (.node (rightSourceRef kind))
          (capturePathSteps kind before.length scratch value)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterSourceCapture.acceptState
        capacity (scratch + capturedValue kind value)
        registers checks
        (before ++ captureMarkedSourceCells kind value ++
          afterSource)
        target actualFinal := by
  simpa [rightCaptureNode, rightCaptureRef, controlNode,
    controlRef, Node.reference] using
    (capture_path_of_node (rightCaptureNode kind)
      (rightSourceRef kind) kind
      (rightCaptureNode_member kind) rfl rfl
      capacity scratch value registers checks
      before afterSource target actual capacityBound
      beforePacked represents)

/-- One output-source capture node followed by its source-kind-specific fixed
normalization continuation. -/
theorem outputCapture_path
    (kind : SourceKind)
    (capacity scratch value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (capacityBound :
      scratch + capturedValue kind value + 1 ≤ capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents
        TargetEmitterSourceCapture.startState
        capacity scratch registers checks before
        (captureSourceCells kind value ++ afterSource)
        target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node (outputCaptureRef kind))
          (.node (outputCaptureContinuation kind))
          (capturePathSteps kind before.length scratch value)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterSourceCapture.acceptState
        capacity (scratch + capturedValue kind value)
        registers checks
        (before ++ captureMarkedSourceCells kind value ++
          afterSource)
        target actualFinal := by
  simpa [outputCaptureNode, outputCaptureRef, controlNode,
    controlRef, Node.reference] using
    (capture_path_of_node (outputCaptureNode kind)
      (outputCaptureContinuation kind) kind
      (outputCaptureNode_member kind) rfl rfl
      capacity scratch value registers checks
      before afterSource target actual capacityBound
      beforePacked represents)

private theorem restore_path_of_node
    (node : Node) (continuation : NodeRef)
    (original : WorkSymbol)
    (member : node ∈ graph.nodes)
    (programEq :
      node.program =
        TargetEmitterCursorControl.restoreMachine original)
    (acceptEq : node.onAccept = .node continuation)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (prefixPacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCursorControl.restoreState
        capacity scratch registers checks
        (before ++ TargetEmitterCursorControl.cursorMark :: afterSource)
        target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node node.reference) (.node continuation)
          (restorePathSteps before.length)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents
        TargetEmitterCursorControl.restoredState
        capacity scratch registers checks
        (before ++ [original]) afterSource target actualFinal := by
  rcases
      TargetEmitterRuntimeSourceControl.restoreCursor_exact
        original capacity scratch registers checks
        before afterSource target actual prefixPacked represents with
    ⟨actualFinal, exactRun, finalRepresents⟩
  have initialState :
      actual.state = node.program.startState := by
    rw [programEq]
    exact TargetEmitterRuntime.Represents.state_eq represents
  have finalState :
      actualFinal.state = node.program.acceptState := by
    rw [programEq]
    exact
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents.state_eq
        finalRepresents
  have nodeRun :
      workRunExact? node.program (before.length + 1) actual =
        some actualFinal := by
    rw [programEq]
    exact exactRun
  have localRun :
      LocalAcceptRun node (before.length + 1)
        actual.tape actualFinal.tape :=
    localAcceptRun_of_exact node (before.length + 1)
      actual actualFinal initialState finalState nodeRun
  have tail :
      AcceptPath graph (.node continuation) (.node continuation) 0
        actualFinal.tape actualFinal.tape :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.step node (.node continuation)
      (before.length + 1) 0
      actual.tape actualFinal.tape actualFinal.tape
      member localRun (by simpa [acceptEq] using tail)
  refine ⟨actualFinal, ?_, finalRepresents⟩
  simpa [restorePathSteps] using path

private theorem leftRestoreNode_member (kind : SourceKind) :
    leftRestoreNode kind ∈ graph.nodes := by
  apply controlNode_member_nodes
  cases kind <;>
    simp [controlNodes, leftControlNodes, Plan.sourceKinds]

private theorem rightRestoreNode_member (kind : SourceKind) :
    rightRestoreNode kind ∈ graph.nodes := by
  apply controlNode_member_nodes
  cases kind <;>
    simp [controlNodes, rightControlNodes, Plan.sourceKinds]

/-- One left-source restoration node followed by its fixed bridge to the
right-source classifier. -/
theorem leftRestore_path
    (kind : SourceKind)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (prefixPacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCursorControl.restoreState
        capacity scratch registers checks
        (before ++ TargetEmitterCursorControl.cursorMark :: afterSource)
        target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node (leftRestoreRef kind))
          (.node rightFirstRef)
          (restorePathSteps before.length)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents
        TargetEmitterCursorControl.restoredState
        capacity scratch registers checks
        (before ++ [Plan.originalCell kind])
        afterSource target actualFinal := by
  simpa [leftRestoreNode, leftRestoreRef, controlNode,
    controlRef, Node.reference] using
    (restore_path_of_node (leftRestoreNode kind) rightFirstRef
      (Plan.originalCell kind)
      (leftRestoreNode_member kind) rfl rfl
      capacity scratch registers checks before afterSource
      target actual prefixPacked represents)

/-- One right-source restoration node followed by its fixed bridge to the
gate-advance navigator. -/
theorem rightRestore_path
    (kind : SourceKind)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (prefixPacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCursorControl.restoreState
        capacity scratch registers checks
        (before ++ TargetEmitterCursorControl.cursorMark :: afterSource)
        target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node (rightRestoreRef kind))
          (.node gateAdvanceRef)
          (restorePathSteps before.length)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents
        TargetEmitterCursorControl.restoredState
        capacity scratch registers checks
        (before ++ [Plan.originalCell kind])
        afterSource target actualFinal := by
  simpa [rightRestoreNode, rightRestoreRef, controlNode,
    controlRef, Node.reference] using
    (restore_path_of_node (rightRestoreNode kind) gateAdvanceRef
      (Plan.originalCell kind)
      (rightRestoreNode_member kind) rfl rfl
      capacity scratch registers checks before afterSource
      target actual prefixPacked represents)

end PNP.Concrete.LockedNAND.TargetEmitterControllerSourceTrace

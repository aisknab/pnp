/-
Copyright (c) 2026 PNP Labs.

Exact semantic paths through the fixed grammar-only locked-NAND target
emitter controller.

This proof layer follows only references already materialized in
`TargetEmitterController.graph`.  It may use the decoded raw circuit to prove
which literal branch the fixed machine takes; no decoded value, schedule, or
execution certificate is an input to the executable machine.
-/

import PNP.Concrete.LockedNANDTargetEmitterController
import PNP.Concrete.LockedNANDTargetEmitterRuntime
import PNP.Concrete.LockedNANDTargetEmitterSchedule

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerTrace

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController

private theorem scannerNode_member :
    scannerNode ∈ graph.nodes := by
  change scannerNode ∈ TargetEmitterController.nodes
  apply controlNode_member_nodes scannerNode
  exact List.Mem.head _

/-- Exact first graph segment on every canonical grammar-decodable source. -/
theorem scanner_path (raw : RawCircuit) :
    AcceptPath graph (.node scannerRef) (.node ledgerRef)
      (TargetEmitterGrammarScanner.canonicalSteps raw + 1)
      (rawInputWorkTape (encodeCircuit raw))
      (TargetEmitterGrammarScanner.acceptedConfiguration raw).tape := by
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
    AcceptPath.terminal (.node ledgerRef) _
  have path :=
    AcceptPath.step scannerNode (.node ledgerRef)
      (TargetEmitterGrammarScanner.canonicalSteps raw) 0
      (rawInputWorkTape (encodeCircuit raw))
      (TargetEmitterGrammarScanner.acceptedConfiguration raw).tape
      (TargetEmitterGrammarScanner.acceptedConfiguration raw).tape
      scannerNode_member localRun tail
  simpa [scannerNode, scannerRef, controlNode, controlRef,
    Node.reference] using path

private theorem ledgerNode_member :
    ledgerNode ∈ graph.nodes := by
  change ledgerNode ∈ TargetEmitterController.nodes
  apply controlNode_member_nodes ledgerNode
  simp [controlNodes]

/-- Exact ledger construction segment after the grammar scanner. -/
theorem ledger_path (raw : RawCircuit) :
    AcceptPath graph (.node ledgerRef)
      (.node stackInitializeRef)
      (TargetEmitterLedger.workSteps raw + 1)
      (TargetEmitterGrammarScanner.acceptedConfiguration raw).tape
      (TargetEmitterLedger.finalConfiguration raw).tape := by
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
    AcceptPath.terminal (.node stackInitializeRef) _
  have path :=
    AcceptPath.step ledgerNode (.node stackInitializeRef)
      (TargetEmitterLedger.workSteps raw) 0
      _ _ _ ledgerNode_member localRun tail
  simpa [ledgerNode, ledgerRef, controlNode, controlRef,
    Node.reference] using path

theorem scanner_ledger_path (raw : RawCircuit) :
    AcceptPath graph (.node scannerRef)
      (.node stackInitializeRef)
      (TargetEmitterGrammarScanner.canonicalSteps raw + 1 +
        (TargetEmitterLedger.workSteps raw + 1))
      (rawInputWorkTape (encodeCircuit raw))
      (TargetEmitterLedger.finalConfiguration raw).tape := by
  exact AcceptPath.trans graph (.node scannerRef)
    (.node ledgerRef) (.node stackInitializeRef)
    (TargetEmitterGrammarScanner.canonicalSteps raw + 1)
    (TargetEmitterLedger.workSteps raw + 1)
    _ _ _ (scanner_path raw) (ledger_path raw)

/-! ### Literal source classifiers -/

def sourceFocusTape (left : List WorkSymbol)
    (source : RawSource) (rest : List WorkSymbol) : WorkTape :=
  (TargetEmitter.configAtWord 0 left
    (SourceParser.sourceCells source ++ rest)).tape

private theorem leftFirstNode_member :
    leftFirstNode ∈ graph.nodes := by
  change leftFirstNode ∈ TargetEmitterController.nodes
  apply controlNode_member_nodes leftFirstNode
  simp [controlNodes, leftControlNodes]

private theorem leftNonInputNode_member :
    leftNonInputNode ∈ graph.nodes := by
  change leftNonInputNode ∈ TargetEmitterController.nodes
  apply controlNode_member_nodes leftNonInputNode
  simp [controlNodes, leftControlNodes]

private theorem leftConstantNode_member :
    leftConstantNode ∈ graph.nodes := by
  change leftConstantNode ∈ TargetEmitterController.nodes
  apply controlNode_member_nodes leftConstantNode
  simp [controlNodes, leftControlNodes]

private theorem left_first_input_path
    (left rest : List WorkSymbol) (index : Nat) :
    AcceptPath graph (.node leftFirstRef)
      (.node (leftCaptureRef .input)) 2
      (sourceFocusTape left (.input index) rest)
      (sourceFocusTape left (.input index) rest) := by
  have localRun :
      LocalAcceptRun leftFirstNode 1
        (sourceFocusTape left (.input index) rest)
        (sourceFocusTape left (.input index) rest) := by
    change
      workRunExact? TargetEmitterNavigator.sourceFirstMachine 1
          (TargetEmitterNavigator.configAtWord
            TargetEmitterNavigator.State.sourceFirst left
            (TargetEmitterNavigator.cell00 ::
              TargetEmitterNavigator.cell11 ::
                (SourceParser.natCells index ++ rest))) =
        some
          (TargetEmitterNavigator.configAtWord
            TargetEmitterNavigator.State.accept left
            (TargetEmitterNavigator.cell00 ::
              TargetEmitterNavigator.cell11 ::
                (SourceParser.natCells index ++ rest)))
    exact TargetEmitterNavigator.sourceFirst_input_exact left
      (TargetEmitterNavigator.cell11 ::
        SourceParser.natCells index ++ rest)
  have tail :
      AcceptPath graph (.node (leftCaptureRef .input))
        (.node (leftCaptureRef .input)) 0
        (sourceFocusTape left (.input index) rest)
        (sourceFocusTape left (.input index) rest) :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.step leftFirstNode
      (.node (leftCaptureRef .input)) 1 0
      (sourceFocusTape left (.input index) rest)
      (sourceFocusTape left (.input index) rest)
      (sourceFocusTape left (.input index) rest)
      leftFirstNode_member localRun tail
  simpa [leftFirstNode, leftFirstRef, controlNode, controlRef,
    Node.reference] using path

private theorem left_first_noninput_path
    (left rest : List WorkSymbol) (source : RawSource)
    (noninput :
      ∃ value : Bool, source = .constant value ∨
        ∃ index, source = .gate index) :
    AcceptPath graph (.node leftFirstRef)
      (.node leftNonInputRef) 2
      (sourceFocusTape left source rest)
      (sourceFocusTape left source rest) := by
  rcases noninput with ⟨value, constant | ⟨index, gate⟩⟩
  · subst source
    have localRun :
        LocalRejectRun leftFirstNode 1
          (sourceFocusTape left (.constant value) rest)
          (sourceFocusTape left (.constant value) rest) := by
      cases value with
      | false =>
          change
            workRunExact?
                TargetEmitterNavigator.sourceFirstMachine 1
                (TargetEmitterNavigator.configAtWord
                  TargetEmitterNavigator.State.sourceFirst left
                  (TargetEmitterNavigator.cell01 ::
                    TargetEmitterNavigator.cell00 :: rest)) =
              some
                (TargetEmitterNavigator.configAtWord
                  TargetEmitterNavigator.State.reject left
                  (TargetEmitterNavigator.cell01 ::
                    TargetEmitterNavigator.cell00 :: rest))
          exact
            TargetEmitterNavigator.sourceFirst_noninput_exact left
              (TargetEmitterNavigator.cell00 :: rest)
      | true =>
          change
            workRunExact?
                TargetEmitterNavigator.sourceFirstMachine 1
                (TargetEmitterNavigator.configAtWord
                  TargetEmitterNavigator.State.sourceFirst left
                  (TargetEmitterNavigator.cell01 ::
                    TargetEmitterNavigator.cell01 :: rest)) =
              some
                (TargetEmitterNavigator.configAtWord
                  TargetEmitterNavigator.State.reject left
                  (TargetEmitterNavigator.cell01 ::
                    TargetEmitterNavigator.cell01 :: rest))
          exact
            TargetEmitterNavigator.sourceFirst_noninput_exact left
              (TargetEmitterNavigator.cell01 :: rest)
    have tail :
        AcceptPath graph (.node leftNonInputRef)
          (.node leftNonInputRef) 0
          (sourceFocusTape left (.constant value) rest)
          (sourceFocusTape left (.constant value) rest) :=
      AcceptPath.terminal _ _
    have path :=
      AcceptPath.stepReject leftFirstNode
        (.node leftNonInputRef) 1 0
        (sourceFocusTape left (.constant value) rest)
        (sourceFocusTape left (.constant value) rest)
        (sourceFocusTape left (.constant value) rest)
        leftFirstNode_member localRun tail
    simpa [leftFirstNode, leftFirstRef, controlNode, controlRef,
      Node.reference] using path
  · subst source
    have localRun :
        LocalRejectRun leftFirstNode 1
          (sourceFocusTape left (.gate index) rest)
          (sourceFocusTape left (.gate index) rest) := by
      change
        workRunExact? TargetEmitterNavigator.sourceFirstMachine 1
            (TargetEmitterNavigator.configAtWord
              TargetEmitterNavigator.State.sourceFirst left
              (TargetEmitterNavigator.cell01 ::
                TargetEmitterNavigator.cell10 ::
                  (SourceParser.natCells index ++ rest))) =
          some
            (TargetEmitterNavigator.configAtWord
              TargetEmitterNavigator.State.reject left
              (TargetEmitterNavigator.cell01 ::
                TargetEmitterNavigator.cell10 ::
                  (SourceParser.natCells index ++ rest)))
      exact TargetEmitterNavigator.sourceFirst_noninput_exact left
        (TargetEmitterNavigator.cell10 ::
          SourceParser.natCells index ++ rest)
    have tail :
        AcceptPath graph (.node leftNonInputRef)
          (.node leftNonInputRef) 0
          (sourceFocusTape left (.gate index) rest)
          (sourceFocusTape left (.gate index) rest) :=
      AcceptPath.terminal _ _
    have path :=
      AcceptPath.stepReject leftFirstNode
        (.node leftNonInputRef) 1 0
        (sourceFocusTape left (.gate index) rest)
        (sourceFocusTape left (.gate index) rest)
        (sourceFocusTape left (.gate index) rest)
        leftFirstNode_member localRun tail
    simpa [leftFirstNode, leftFirstRef, controlNode, controlRef,
      Node.reference] using path

def sourceKind : RawSource → TargetEmitterPlan.SourceKind
  | .input _ => .input
  | .constant false => .constantFalse
  | .constant true => .constantTrue
  | .gate _ => .gate

def classifierSteps : RawSource → Nat
  | .input _ => 2
  | .gate _ => 5
  | .constant _ => 8

private theorem left_noninput_gate_path
    (left rest : List WorkSymbol) (index : Nat) :
    AcceptPath graph (.node leftNonInputRef)
      (.node (leftCaptureRef .gate)) 3
      (sourceFocusTape left (.gate index) rest)
      (sourceFocusTape left (.gate index) rest) := by
  have localRun :
      LocalAcceptRun leftNonInputNode 2
        (sourceFocusTape left (.gate index) rest)
        (sourceFocusTape left (.gate index) rest) := by
    change
      workRunExact? TargetEmitterNavigator.nonInputMachine 2
          (TargetEmitterNavigator.configAtWord
            TargetEmitterNavigator.State.nonInputFirst left
            (TargetEmitterNavigator.cell01 ::
              TargetEmitterNavigator.cell10 ::
                (SourceParser.natCells index ++ rest))) =
        some
          (TargetEmitterNavigator.configAtWord
            TargetEmitterNavigator.State.accept left
            (TargetEmitterNavigator.cell01 ::
              TargetEmitterNavigator.cell10 ::
                (SourceParser.natCells index ++ rest)))
    exact TargetEmitterNavigator.nonInput_gate_exact left
      (SourceParser.natCells index ++ rest)
  have tail :
      AcceptPath graph (.node (leftCaptureRef .gate))
        (.node (leftCaptureRef .gate)) 0
        (sourceFocusTape left (.gate index) rest)
        (sourceFocusTape left (.gate index) rest) :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.step leftNonInputNode
      (.node (leftCaptureRef .gate)) 2 0
      (sourceFocusTape left (.gate index) rest)
      (sourceFocusTape left (.gate index) rest)
      (sourceFocusTape left (.gate index) rest)
      leftNonInputNode_member localRun tail
  simpa [leftNonInputNode, leftNonInputRef, controlNode,
    controlRef, Node.reference] using path

private theorem left_noninput_constant_path
    (left rest : List WorkSymbol) (value : Bool) :
    AcceptPath graph (.node leftNonInputRef)
      (.node leftConstantRef) 3
      (sourceFocusTape left (.constant value) rest)
      (sourceFocusTape left (.constant value) rest) := by
  have localRun :
      LocalRejectRun leftNonInputNode 2
        (sourceFocusTape left (.constant value) rest)
        (sourceFocusTape left (.constant value) rest) := by
    cases value with
    | false =>
        change
          workRunExact? TargetEmitterNavigator.nonInputMachine 2
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.nonInputFirst left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell00 :: rest)) =
            some
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.reject left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell00 :: rest))
        exact TargetEmitterNavigator.nonInput_constantFalse_exact
          left rest
    | true =>
        change
          workRunExact? TargetEmitterNavigator.nonInputMachine 2
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.nonInputFirst left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell01 :: rest)) =
            some
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.reject left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell01 :: rest))
        exact TargetEmitterNavigator.nonInput_constantTrue_exact
          left rest
  have tail :
      AcceptPath graph (.node leftConstantRef)
        (.node leftConstantRef) 0
        (sourceFocusTape left (.constant value) rest)
        (sourceFocusTape left (.constant value) rest) :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.stepReject leftNonInputNode
      (.node leftConstantRef) 2 0
      (sourceFocusTape left (.constant value) rest)
      (sourceFocusTape left (.constant value) rest)
      (sourceFocusTape left (.constant value) rest)
      leftNonInputNode_member localRun tail
  simpa [leftNonInputNode, leftNonInputRef, controlNode,
    controlRef, Node.reference] using path

private theorem left_constant_path
    (left rest : List WorkSymbol) (value : Bool) :
    AcceptPath graph (.node leftConstantRef)
      (.node (leftCaptureRef
        (if value then .constantTrue else .constantFalse))) 3
      (sourceFocusTape left (.constant value) rest)
      (sourceFocusTape left (.constant value) rest) := by
  cases value with
  | false =>
      have localRun :
          LocalAcceptRun leftConstantNode 2
            (sourceFocusTape left (.constant false) rest)
            (sourceFocusTape left (.constant false) rest) := by
        change
          workRunExact? TargetEmitterNavigator.constantMachine 2
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.constantFirst left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell00 :: rest)) =
            some
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.accept left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell00 :: rest))
        exact TargetEmitterNavigator.constantFalse_exact left rest
      have tail :
          AcceptPath graph (.node (leftCaptureRef .constantFalse))
            (.node (leftCaptureRef .constantFalse)) 0
            (sourceFocusTape left (.constant false) rest)
            (sourceFocusTape left (.constant false) rest) :=
        AcceptPath.terminal _ _
      have path :=
        AcceptPath.step leftConstantNode
          (.node (leftCaptureRef .constantFalse)) 2 0
          (sourceFocusTape left (.constant false) rest)
          (sourceFocusTape left (.constant false) rest)
          (sourceFocusTape left (.constant false) rest)
          leftConstantNode_member localRun tail
      simpa [leftConstantNode, leftConstantRef, controlNode,
        controlRef, Node.reference] using path
  | true =>
      have localRun :
          LocalRejectRun leftConstantNode 2
            (sourceFocusTape left (.constant true) rest)
            (sourceFocusTape left (.constant true) rest) := by
        change
          workRunExact? TargetEmitterNavigator.constantMachine 2
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.constantFirst left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell01 :: rest)) =
            some
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.reject left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell01 :: rest))
        exact TargetEmitterNavigator.constantTrue_exact left rest
      have tail :
          AcceptPath graph (.node (leftCaptureRef .constantTrue))
            (.node (leftCaptureRef .constantTrue)) 0
            (sourceFocusTape left (.constant true) rest)
            (sourceFocusTape left (.constant true) rest) :=
        AcceptPath.terminal _ _
      have path :=
        AcceptPath.stepReject leftConstantNode
          (.node (leftCaptureRef .constantTrue)) 2 0
          (sourceFocusTape left (.constant true) rest)
          (sourceFocusTape left (.constant true) rest)
          (sourceFocusTape left (.constant true) rest)
          leftConstantNode_member localRun tail
      simpa [leftConstantNode, leftConstantRef, controlNode,
        controlRef, Node.reference] using path

theorem left_classifier_path
    (left rest : List WorkSymbol) (source : RawSource) :
    AcceptPath graph (.node leftFirstRef)
      (.node (leftCaptureRef (sourceKind source)))
      (classifierSteps source)
      (sourceFocusTape left source rest)
      (sourceFocusTape left source rest) := by
  cases source with
  | input index =>
      exact left_first_input_path left rest index
  | gate index =>
      have first := left_first_noninput_path left rest (.gate index)
        ⟨false, Or.inr ⟨index, rfl⟩⟩
      have second := left_noninput_gate_path left rest index
      simpa [classifierSteps, sourceKind] using
        AcceptPath.trans graph (.node leftFirstRef)
          (.node leftNonInputRef)
          (.node (leftCaptureRef .gate))
          2 3 _ _ _ first second
  | constant value =>
      have first := left_first_noninput_path left rest
        (.constant value) ⟨value, Or.inl rfl⟩
      have second := left_noninput_constant_path left rest value
      have third := left_constant_path left rest value
      have firstTwo :=
        AcceptPath.trans graph (.node leftFirstRef)
          (.node leftNonInputRef) (.node leftConstantRef)
          2 3 _ _ _ first second
      cases value with
      | false =>
          simpa [classifierSteps, sourceKind] using
            AcceptPath.trans graph (.node leftFirstRef)
              (.node leftConstantRef)
              (.node (leftCaptureRef .constantFalse))
              5 3 _ _ _ firstTwo third
      | true =>
          simpa [classifierSteps, sourceKind] using
            AcceptPath.trans graph (.node leftFirstRef)
              (.node leftConstantRef)
              (.node (leftCaptureRef .constantTrue))
              5 3 _ _ _ firstTwo third

/-! The same literal classifier occurs at the right source and output
positions.  The helper below is parameterized only by graph nodes and their
already-materialized successor endpoints; it does not synthesize or look up
control at runtime. -/

private theorem classifier_first_input_step
    (node : Node) (capture : NodeRef)
    (member : node ∈ graph.nodes)
    (programEq :
      node.program = TargetEmitterNavigator.sourceFirstMachine)
    (acceptEq : node.onAccept = .node capture)
    (left rest : List WorkSymbol) (index : Nat) :
    AcceptPath graph (.node node.reference) (.node capture) 2
      (sourceFocusTape left (.input index) rest)
      (sourceFocusTape left (.input index) rest) := by
  have localRun :
      LocalAcceptRun node 1
        (sourceFocusTape left (.input index) rest)
        (sourceFocusTape left (.input index) rest) := by
    unfold LocalAcceptRun
    rw [programEq]
    change
      workRunExact? TargetEmitterNavigator.sourceFirstMachine 1
          (TargetEmitterNavigator.configAtWord
            TargetEmitterNavigator.State.sourceFirst left
            (TargetEmitterNavigator.cell00 ::
              TargetEmitterNavigator.cell11 ::
                (SourceParser.natCells index ++ rest))) =
        some
          (TargetEmitterNavigator.configAtWord
            TargetEmitterNavigator.State.accept left
            (TargetEmitterNavigator.cell00 ::
              TargetEmitterNavigator.cell11 ::
                (SourceParser.natCells index ++ rest)))
    exact TargetEmitterNavigator.sourceFirst_input_exact left
      (TargetEmitterNavigator.cell11 ::
        SourceParser.natCells index ++ rest)
  have tail :
      AcceptPath graph (.node capture) (.node capture) 0
        (sourceFocusTape left (.input index) rest)
        (sourceFocusTape left (.input index) rest) :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.step node (.node capture) 1 0
      (sourceFocusTape left (.input index) rest)
      (sourceFocusTape left (.input index) rest)
      (sourceFocusTape left (.input index) rest)
      member localRun (by simpa [acceptEq] using tail)
  simpa using path

private theorem classifier_first_noninput_step
    (node : Node) (nonInput : NodeRef)
    (member : node ∈ graph.nodes)
    (programEq :
      node.program = TargetEmitterNavigator.sourceFirstMachine)
    (rejectEq : node.onReject = .node nonInput)
    (left rest : List WorkSymbol) (source : RawSource)
    (noninput :
      ∃ value : Bool, source = .constant value ∨
        ∃ index, source = .gate index) :
    AcceptPath graph (.node node.reference) (.node nonInput) 2
      (sourceFocusTape left source rest)
      (sourceFocusTape left source rest) := by
  rcases noninput with ⟨value, constant | ⟨index, gate⟩⟩
  · subst source
    have localRun :
        LocalRejectRun node 1
          (sourceFocusTape left (.constant value) rest)
          (sourceFocusTape left (.constant value) rest) := by
      unfold LocalRejectRun
      rw [programEq]
      cases value with
      | false =>
          change
            workRunExact?
                TargetEmitterNavigator.sourceFirstMachine 1
                (TargetEmitterNavigator.configAtWord
                  TargetEmitterNavigator.State.sourceFirst left
                  (TargetEmitterNavigator.cell01 ::
                    TargetEmitterNavigator.cell00 :: rest)) =
              some
                (TargetEmitterNavigator.configAtWord
                  TargetEmitterNavigator.State.reject left
                  (TargetEmitterNavigator.cell01 ::
                    TargetEmitterNavigator.cell00 :: rest))
          exact
            TargetEmitterNavigator.sourceFirst_noninput_exact left
              (TargetEmitterNavigator.cell00 :: rest)
      | true =>
          change
            workRunExact?
                TargetEmitterNavigator.sourceFirstMachine 1
                (TargetEmitterNavigator.configAtWord
                  TargetEmitterNavigator.State.sourceFirst left
                  (TargetEmitterNavigator.cell01 ::
                    TargetEmitterNavigator.cell01 :: rest)) =
              some
                (TargetEmitterNavigator.configAtWord
                  TargetEmitterNavigator.State.reject left
                  (TargetEmitterNavigator.cell01 ::
                    TargetEmitterNavigator.cell01 :: rest))
          exact
            TargetEmitterNavigator.sourceFirst_noninput_exact left
              (TargetEmitterNavigator.cell01 :: rest)
    have tail :
        AcceptPath graph (.node nonInput) (.node nonInput) 0
          (sourceFocusTape left (.constant value) rest)
          (sourceFocusTape left (.constant value) rest) :=
      AcceptPath.terminal _ _
    have path :=
      AcceptPath.stepReject node (.node nonInput) 1 0
        (sourceFocusTape left (.constant value) rest)
        (sourceFocusTape left (.constant value) rest)
        (sourceFocusTape left (.constant value) rest)
        member localRun (by simpa [rejectEq] using tail)
    simpa using path
  · subst source
    have localRun :
        LocalRejectRun node 1
          (sourceFocusTape left (.gate index) rest)
          (sourceFocusTape left (.gate index) rest) := by
      unfold LocalRejectRun
      rw [programEq]
      change
        workRunExact? TargetEmitterNavigator.sourceFirstMachine 1
            (TargetEmitterNavigator.configAtWord
              TargetEmitterNavigator.State.sourceFirst left
              (TargetEmitterNavigator.cell01 ::
                TargetEmitterNavigator.cell10 ::
                  (SourceParser.natCells index ++ rest))) =
          some
            (TargetEmitterNavigator.configAtWord
              TargetEmitterNavigator.State.reject left
              (TargetEmitterNavigator.cell01 ::
                TargetEmitterNavigator.cell10 ::
                  (SourceParser.natCells index ++ rest)))
      exact TargetEmitterNavigator.sourceFirst_noninput_exact left
        (TargetEmitterNavigator.cell10 ::
          SourceParser.natCells index ++ rest)
    have tail :
        AcceptPath graph (.node nonInput) (.node nonInput) 0
          (sourceFocusTape left (.gate index) rest)
          (sourceFocusTape left (.gate index) rest) :=
      AcceptPath.terminal _ _
    have path :=
      AcceptPath.stepReject node (.node nonInput) 1 0
        (sourceFocusTape left (.gate index) rest)
        (sourceFocusTape left (.gate index) rest)
        (sourceFocusTape left (.gate index) rest)
        member localRun (by simpa [rejectEq] using tail)
    simpa using path

private theorem classifier_noninput_gate_step
    (node : Node) (capture : NodeRef)
    (member : node ∈ graph.nodes)
    (programEq :
      node.program = TargetEmitterNavigator.nonInputMachine)
    (acceptEq : node.onAccept = .node capture)
    (left rest : List WorkSymbol) (index : Nat) :
    AcceptPath graph (.node node.reference) (.node capture) 3
      (sourceFocusTape left (.gate index) rest)
      (sourceFocusTape left (.gate index) rest) := by
  have localRun :
      LocalAcceptRun node 2
        (sourceFocusTape left (.gate index) rest)
        (sourceFocusTape left (.gate index) rest) := by
    unfold LocalAcceptRun
    rw [programEq]
    change
      workRunExact? TargetEmitterNavigator.nonInputMachine 2
          (TargetEmitterNavigator.configAtWord
            TargetEmitterNavigator.State.nonInputFirst left
            (TargetEmitterNavigator.cell01 ::
              TargetEmitterNavigator.cell10 ::
                (SourceParser.natCells index ++ rest))) =
        some
          (TargetEmitterNavigator.configAtWord
            TargetEmitterNavigator.State.accept left
            (TargetEmitterNavigator.cell01 ::
              TargetEmitterNavigator.cell10 ::
                (SourceParser.natCells index ++ rest)))
    exact TargetEmitterNavigator.nonInput_gate_exact left
      (SourceParser.natCells index ++ rest)
  have tail :
      AcceptPath graph (.node capture) (.node capture) 0
        (sourceFocusTape left (.gate index) rest)
        (sourceFocusTape left (.gate index) rest) :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.step node (.node capture) 2 0
      (sourceFocusTape left (.gate index) rest)
      (sourceFocusTape left (.gate index) rest)
      (sourceFocusTape left (.gate index) rest)
      member localRun (by simpa [acceptEq] using tail)
  simpa using path

private theorem classifier_noninput_constant_step
    (node : Node) (constant : NodeRef)
    (member : node ∈ graph.nodes)
    (programEq :
      node.program = TargetEmitterNavigator.nonInputMachine)
    (rejectEq : node.onReject = .node constant)
    (left rest : List WorkSymbol) (value : Bool) :
    AcceptPath graph (.node node.reference) (.node constant) 3
      (sourceFocusTape left (.constant value) rest)
      (sourceFocusTape left (.constant value) rest) := by
  have localRun :
      LocalRejectRun node 2
        (sourceFocusTape left (.constant value) rest)
        (sourceFocusTape left (.constant value) rest) := by
    unfold LocalRejectRun
    rw [programEq]
    cases value with
    | false =>
        change
          workRunExact? TargetEmitterNavigator.nonInputMachine 2
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.nonInputFirst left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell00 :: rest)) =
            some
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.reject left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell00 :: rest))
        exact TargetEmitterNavigator.nonInput_constantFalse_exact
          left rest
    | true =>
        change
          workRunExact? TargetEmitterNavigator.nonInputMachine 2
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.nonInputFirst left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell01 :: rest)) =
            some
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.reject left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell01 :: rest))
        exact TargetEmitterNavigator.nonInput_constantTrue_exact
          left rest
  have tail :
      AcceptPath graph (.node constant) (.node constant) 0
        (sourceFocusTape left (.constant value) rest)
        (sourceFocusTape left (.constant value) rest) :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.stepReject node (.node constant) 2 0
      (sourceFocusTape left (.constant value) rest)
      (sourceFocusTape left (.constant value) rest)
      (sourceFocusTape left (.constant value) rest)
      member localRun (by simpa [rejectEq] using tail)
  simpa using path

private theorem classifier_constant_step
    (node : Node) (falseCapture trueCapture : NodeRef)
    (member : node ∈ graph.nodes)
    (programEq :
      node.program = TargetEmitterNavigator.constantMachine)
    (acceptEq : node.onAccept = .node falseCapture)
    (rejectEq : node.onReject = .node trueCapture)
    (left rest : List WorkSymbol) (value : Bool) :
    AcceptPath graph (.node node.reference)
      (.node (if value then trueCapture else falseCapture)) 3
      (sourceFocusTape left (.constant value) rest)
      (sourceFocusTape left (.constant value) rest) := by
  cases value with
  | false =>
      have localRun :
          LocalAcceptRun node 2
            (sourceFocusTape left (.constant false) rest)
            (sourceFocusTape left (.constant false) rest) := by
        unfold LocalAcceptRun
        rw [programEq]
        change
          workRunExact? TargetEmitterNavigator.constantMachine 2
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.constantFirst left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell00 :: rest)) =
            some
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.accept left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell00 :: rest))
        exact TargetEmitterNavigator.constantFalse_exact left rest
      have tail :
          AcceptPath graph (.node falseCapture) (.node falseCapture) 0
            (sourceFocusTape left (.constant false) rest)
            (sourceFocusTape left (.constant false) rest) :=
        AcceptPath.terminal _ _
      have path :=
        AcceptPath.step node (.node falseCapture) 2 0
          (sourceFocusTape left (.constant false) rest)
          (sourceFocusTape left (.constant false) rest)
          (sourceFocusTape left (.constant false) rest)
          member localRun (by simpa [acceptEq] using tail)
      simpa using path
  | true =>
      have localRun :
          LocalRejectRun node 2
            (sourceFocusTape left (.constant true) rest)
            (sourceFocusTape left (.constant true) rest) := by
        unfold LocalRejectRun
        rw [programEq]
        change
          workRunExact? TargetEmitterNavigator.constantMachine 2
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.constantFirst left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell01 :: rest)) =
            some
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.reject left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell01 :: rest))
        exact TargetEmitterNavigator.constantTrue_exact left rest
      have tail :
          AcceptPath graph (.node trueCapture) (.node trueCapture) 0
            (sourceFocusTape left (.constant true) rest)
            (sourceFocusTape left (.constant true) rest) :=
        AcceptPath.terminal _ _
      have path :=
        AcceptPath.stepReject node (.node trueCapture) 2 0
          (sourceFocusTape left (.constant true) rest)
          (sourceFocusTape left (.constant true) rest)
          (sourceFocusTape left (.constant true) rest)
          member localRun (by simpa [rejectEq] using tail)
      simpa using path

private theorem classifier_path_of_nodes
    (firstNode nonInputNode constantNode : Node)
    (capture : TargetEmitterPlan.SourceKind → NodeRef)
    (firstMember : firstNode ∈ graph.nodes)
    (nonInputMember : nonInputNode ∈ graph.nodes)
    (constantMember : constantNode ∈ graph.nodes)
    (firstProgram :
      firstNode.program =
        TargetEmitterNavigator.sourceFirstMachine)
    (nonInputProgram :
      nonInputNode.program =
        TargetEmitterNavigator.nonInputMachine)
    (constantProgram :
      constantNode.program =
        TargetEmitterNavigator.constantMachine)
    (firstAccept :
      firstNode.onAccept = .node (capture .input))
    (firstReject :
      firstNode.onReject = .node nonInputNode.reference)
    (nonInputAccept :
      nonInputNode.onAccept = .node (capture .gate))
    (nonInputReject :
      nonInputNode.onReject = .node constantNode.reference)
    (constantAccept :
      constantNode.onAccept = .node (capture .constantFalse))
    (constantReject :
      constantNode.onReject = .node (capture .constantTrue))
    (left rest : List WorkSymbol) (source : RawSource) :
    AcceptPath graph (.node firstNode.reference)
      (.node (capture (sourceKind source)))
      (classifierSteps source)
      (sourceFocusTape left source rest)
      (sourceFocusTape left source rest) := by
  cases source with
  | input index =>
      exact classifier_first_input_step firstNode
        (capture .input) firstMember firstProgram firstAccept
        left rest index
  | gate index =>
      have first :=
        classifier_first_noninput_step firstNode
          nonInputNode.reference firstMember firstProgram
          firstReject left rest (.gate index)
          ⟨false, Or.inr ⟨index, rfl⟩⟩
      have second :=
        classifier_noninput_gate_step nonInputNode
          (capture .gate) nonInputMember nonInputProgram
          nonInputAccept left rest index
      simpa [classifierSteps, sourceKind] using
        AcceptPath.trans graph (.node firstNode.reference)
          (.node nonInputNode.reference)
          (.node (capture .gate))
          2 3 _ _ _ first second
  | constant value =>
      have first :=
        classifier_first_noninput_step firstNode
          nonInputNode.reference firstMember firstProgram
          firstReject left rest (.constant value)
          ⟨value, Or.inl rfl⟩
      have second :=
        classifier_noninput_constant_step nonInputNode
          constantNode.reference nonInputMember nonInputProgram
          nonInputReject left rest value
      have third :=
        classifier_constant_step constantNode
          (capture .constantFalse) (capture .constantTrue)
          constantMember constantProgram
          constantAccept constantReject left rest value
      have firstTwo :=
        AcceptPath.trans graph (.node firstNode.reference)
          (.node nonInputNode.reference)
          (.node constantNode.reference)
          2 3 _ _ _ first second
      cases value with
      | false =>
          simpa [classifierSteps, sourceKind] using
            AcceptPath.trans graph (.node firstNode.reference)
              (.node constantNode.reference)
              (.node (capture .constantFalse))
              5 3 _ _ _ firstTwo third
      | true =>
          simpa [classifierSteps, sourceKind] using
            AcceptPath.trans graph (.node firstNode.reference)
              (.node constantNode.reference)
              (.node (capture .constantTrue))
              5 3 _ _ _ firstTwo third

private theorem rightFirstNode_member :
    rightFirstNode ∈ graph.nodes := by
  apply controlNode_member_nodes rightFirstNode
  simp [controlNodes, rightControlNodes]

private theorem rightNonInputNode_member :
    rightNonInputNode ∈ graph.nodes := by
  apply controlNode_member_nodes rightNonInputNode
  simp [controlNodes, rightControlNodes]

private theorem rightConstantNode_member :
    rightConstantNode ∈ graph.nodes := by
  apply controlNode_member_nodes rightConstantNode
  simp [controlNodes, rightControlNodes]

theorem right_classifier_path
    (left rest : List WorkSymbol) (source : RawSource) :
    AcceptPath graph (.node rightFirstRef)
      (.node (rightCaptureRef (sourceKind source)))
      (classifierSteps source)
      (sourceFocusTape left source rest)
      (sourceFocusTape left source rest) := by
  have path :=
    classifier_path_of_nodes
      rightFirstNode rightNonInputNode rightConstantNode
      rightCaptureRef
      rightFirstNode_member rightNonInputNode_member
      rightConstantNode_member
      (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl)
      left rest source
  simpa [rightFirstNode, rightNonInputNode, rightConstantNode,
    rightFirstRef, rightNonInputRef, rightConstantRef,
    controlNode, controlRef, Node.reference] using path

private theorem outputFirstNode_member :
    outputFirstNode ∈ graph.nodes := by
  apply controlNode_member_nodes outputFirstNode
  simp [controlNodes, outputControlNodes]

private theorem outputNonInputNode_member :
    outputNonInputNode ∈ graph.nodes := by
  apply controlNode_member_nodes outputNonInputNode
  simp [controlNodes, outputControlNodes]

private theorem outputConstantNode_member :
    outputConstantNode ∈ graph.nodes := by
  apply controlNode_member_nodes outputConstantNode
  simp [controlNodes, outputControlNodes]

theorem output_classifier_path
    (left rest : List WorkSymbol) (source : RawSource) :
    AcceptPath graph (.node outputFirstRef)
      (.node (outputCaptureRef (sourceKind source)))
      (classifierSteps source)
      (sourceFocusTape left source rest)
      (sourceFocusTape left source rest) := by
  have path :=
    classifier_path_of_nodes
      outputFirstNode outputNonInputNode outputConstantNode
      outputCaptureRef
      outputFirstNode_member outputNonInputNode_member
      outputConstantNode_member
      (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl)
      left rest source
  simpa [outputFirstNode, outputNonInputNode, outputConstantNode,
    outputFirstRef, outputNonInputRef, outputConstantRef,
    controlNode, controlRef, Node.reference] using path

/-! ### Header and gate-list navigation -/

def circuitHeaderCells (inputs gates : Nat) : List WorkSymbol :=
  [SourceParser.cell00, SourceParser.cell00] ++
    SourceParser.natCells inputs ++
    SourceParser.natCells gates

def circuitFooterCells (output : RawSource) : List WorkSymbol :=
  [SourceParser.cell10, SourceParser.cell00] ++
    SourceParser.sourceCells output ++
    [SourceParser.cell10, SourceParser.cell01,
      SourceParser.cell10, SourceParser.cell11]

private theorem headerNavigatorNode_member :
    headerNavigatorNode ∈ graph.nodes := by
  apply controlNode_member_nodes headerNavigatorNode
  simp [controlNodes]

private theorem programEndNode_member :
    programEndNode ∈ graph.nodes := by
  apply controlNode_member_nodes programEndNode
  simp [controlNodes]

private theorem gateAdvanceNode_member :
    gateAdvanceNode ∈ graph.nodes := by
  apply controlNode_member_nodes gateAdvanceNode
  simp [controlNodes]

theorem header_nonempty_path
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (target : List Token)
    (inputs : Nat) (gate : RawGate)
    (gates : List RawGate) (output : RawSource) :
    AcceptPath graph (.node headerNavigatorRef)
      (.node leftFirstRef)
      (TargetEmitterNavigator.headerWorkSteps
        inputs (gate :: gates).length + 1)
      (TargetEmitterRuntime.logicalTape capacity scratch registers
        checks
        (SourceParser.circuitCells
          { inputCount := inputs
            gates := gate :: gates
            output := output })
        target)
      (sourceFocusTape
        ((circuitHeaderCells inputs (gate :: gates).length).reverse ++
          TargetEmitterRuntime.logicalLeftWorkspace
            capacity scratch registers checks)
        gate.left
        (SourceParser.sourceCells gate.right ++
          [SourceParser.cell01, SourceParser.cell11] ++
          SourceParser.gateListCells gates ++
          circuitFooterCells output ++
          TargetEmitter.sourceTargetBoundary ::
            SourceParser.packedTokenCells target)) := by
  have sourceFirst :
      (SourceParser.sourceCells gate.left).head?.getD
          WorkSymbol.blank =
        SourceParser.cell00 ∨
      (SourceParser.sourceCells gate.left).head?.getD
          WorkSymbol.blank =
        SourceParser.cell01 := by
    cases gate with
    | mk left right =>
        cases left with
        | input index => exact Or.inl rfl
        | gate index => exact Or.inr rfl
        | constant value =>
            cases value <;> exact Or.inr rfl
  have localRun :
      LocalAcceptRun headerNavigatorNode
        (TargetEmitterNavigator.headerWorkSteps
          inputs (gate :: gates).length)
        (TargetEmitterRuntime.logicalTape capacity scratch registers
          checks
          (SourceParser.circuitCells
            { inputCount := inputs
              gates := gate :: gates
              output := output })
          target)
        (sourceFocusTape
          ((circuitHeaderCells inputs (gate :: gates).length).reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              capacity scratch registers checks)
          gate.left
          (SourceParser.sourceCells gate.right ++
            [SourceParser.cell01, SourceParser.cell11] ++
            SourceParser.gateListCells gates ++
            circuitFooterCells output ++
            TargetEmitter.sourceTargetBoundary ::
              SourceParser.packedTokenCells target)) := by
    rcases gate with ⟨leftSource, rightSource⟩
    unfold LocalAcceptRun
    let suffix :=
      SourceParser.sourceCells rightSource ++
        [SourceParser.cell01, SourceParser.cell11] ++
        SourceParser.gateListCells gates ++
        circuitFooterCells output ++
        TargetEmitter.sourceTargetBoundary ::
          SourceParser.packedTokenCells target
    let leftCells := SourceParser.sourceCells leftSource
    let actualInitial :=
      TargetEmitterNavigator.configAtWord
        TargetEmitterNavigator.State.headerStart
        (TargetEmitterRuntime.logicalLeftWorkspace
          capacity scratch registers checks)
        (TargetEmitterNavigator.cell00 ::
          TargetEmitterNavigator.cell00 ::
            (SourceParser.natCells inputs ++
              (SourceParser.natCells
                ({ left := leftSource, right := rightSource } ::
                  gates).length ++
                leftCells.head?.getD WorkSymbol.blank ::
                  (leftCells.tail ++ suffix))))
    let actualFinal :=
      TargetEmitterNavigator.configAtWord
        TargetEmitterNavigator.State.accept
        (TargetEmitterNavigator.pushCrossed
          ([TargetEmitterNavigator.cell00,
              TargetEmitterNavigator.cell00] ++
            SourceParser.natCells inputs ++
            SourceParser.natCells
              ({ left := leftSource, right := rightSource } ::
                gates).length)
          (TargetEmitterRuntime.logicalLeftWorkspace
            capacity scratch registers checks))
        (leftCells.head?.getD WorkSymbol.blank ::
          (leftCells.tail ++ suffix))
    have exactRun :
        workRunExact? TargetEmitterNavigator.headerMachine
            (TargetEmitterNavigator.headerWorkSteps inputs
              ({ left := leftSource, right := rightSource } ::
                gates).length)
            actualInitial =
          some actualFinal :=
      TargetEmitterNavigator.header_nonempty_exact
        inputs
        ({ left := leftSource, right := rightSource } :: gates).length
        (leftCells.head?.getD WorkSymbol.blank)
        (leftCells.tail ++ suffix)
        (TargetEmitterRuntime.logicalLeftWorkspace
          capacity scratch registers checks)
        sourceFirst
    let expectedInitial : WorkConfiguration :=
      { state := headerNavigatorNode.program.startState
        tape :=
          TargetEmitterRuntime.logicalTape capacity scratch registers
            checks
            (SourceParser.circuitCells
              { inputCount := inputs
                gates :=
                  { left := leftSource, right := rightSource } ::
                    gates
                output := output })
            target }
    let expectedFinal : WorkConfiguration :=
      { state := headerNavigatorNode.program.acceptState
        tape :=
          sourceFocusTape
            ((circuitHeaderCells inputs
                ({ left := leftSource, right := rightSource } ::
                  gates).length).reverse ++
              TargetEmitterRuntime.logicalLeftWorkspace
                capacity scratch registers checks)
            leftSource suffix }
    have initialEq : actualInitial = expectedInitial := by
      cases leftSource with
      | input index =>
          simp [actualInitial, expectedInitial, leftCells, suffix,
            headerNavigatorNode, controlNode,
            TargetEmitterNavigator.headerMachine,
            TargetEmitterNavigator.machineFrom,
            TargetEmitterNavigator.cell00, SourceParser.cell00,
            TargetEmitterRuntime.logicalTape,
            TargetEmitterRuntime.logicalConfiguration,
            TargetEmitterRuntime.logicalWord,
            TargetEmitterNavigator.configAtWord,
            TargetEmitter.configAtWord,
            SourceParser.circuitCells, SourceParser.gateListCells,
            SourceParser.gateCells, SourceParser.sourceCells,
            circuitFooterCells, List.append_assoc]
      | gate index =>
          simp [actualInitial, expectedInitial, leftCells, suffix,
            headerNavigatorNode, controlNode,
            TargetEmitterNavigator.headerMachine,
            TargetEmitterNavigator.machineFrom,
            TargetEmitterNavigator.cell00, SourceParser.cell00,
            TargetEmitterRuntime.logicalTape,
            TargetEmitterRuntime.logicalConfiguration,
            TargetEmitterRuntime.logicalWord,
            TargetEmitterNavigator.configAtWord,
            TargetEmitter.configAtWord,
            SourceParser.circuitCells, SourceParser.gateListCells,
            SourceParser.gateCells, SourceParser.sourceCells,
            circuitFooterCells, List.append_assoc]
      | constant value =>
          cases value <;>
            simp [actualInitial, expectedInitial, leftCells, suffix,
              headerNavigatorNode, controlNode,
              TargetEmitterNavigator.headerMachine,
              TargetEmitterNavigator.machineFrom,
              TargetEmitterNavigator.cell00, SourceParser.cell00,
              TargetEmitterRuntime.logicalTape,
              TargetEmitterRuntime.logicalConfiguration,
              TargetEmitterRuntime.logicalWord,
              TargetEmitterNavigator.configAtWord,
              TargetEmitter.configAtWord,
              SourceParser.circuitCells, SourceParser.gateListCells,
              SourceParser.gateCells, SourceParser.sourceCells,
              circuitFooterCells, List.append_assoc]
    have finalEq : actualFinal = expectedFinal := by
      cases leftSource with
      | input index =>
          simp [actualFinal, expectedFinal, leftCells, suffix,
            headerNavigatorNode, controlNode,
            TargetEmitterNavigator.headerMachine,
            TargetEmitterNavigator.machineFrom,
            TargetEmitterNavigator.cell00, SourceParser.cell00,
            TargetEmitterNavigator.configAtWord,
            TargetEmitterNavigator.pushCrossed,
            TargetEmitter.configAtWord,
            SourceParser.sourceCells, circuitHeaderCells,
            sourceFocusTape, List.append_assoc]
      | gate index =>
          simp [actualFinal, expectedFinal, leftCells, suffix,
            headerNavigatorNode, controlNode,
            TargetEmitterNavigator.headerMachine,
            TargetEmitterNavigator.machineFrom,
            TargetEmitterNavigator.cell00, SourceParser.cell00,
            TargetEmitterNavigator.configAtWord,
            TargetEmitterNavigator.pushCrossed,
            TargetEmitter.configAtWord,
            SourceParser.sourceCells, circuitHeaderCells,
            sourceFocusTape, List.append_assoc]
      | constant value =>
          cases value <;>
            simp [actualFinal, expectedFinal, leftCells, suffix,
              headerNavigatorNode, controlNode,
              TargetEmitterNavigator.headerMachine,
              TargetEmitterNavigator.machineFrom,
              TargetEmitterNavigator.cell00, SourceParser.cell00,
              TargetEmitterNavigator.configAtWord,
              TargetEmitterNavigator.pushCrossed,
              TargetEmitter.configAtWord,
              SourceParser.sourceCells, circuitHeaderCells,
              sourceFocusTape, List.append_assoc]
    change
      workRunExact? headerNavigatorNode.program
          (TargetEmitterNavigator.headerWorkSteps inputs
            ({ left := leftSource, right := rightSource } ::
              gates).length)
          expectedInitial =
        some expectedFinal
    rw [← initialEq, ← finalEq]
    simpa [headerNavigatorNode, controlNode] using exactRun
  have tail :
      AcceptPath graph (.node leftFirstRef) (.node leftFirstRef) 0
        (sourceFocusTape
          ((circuitHeaderCells inputs (gate :: gates).length).reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              capacity scratch registers checks)
          gate.left
          (SourceParser.sourceCells gate.right ++
            [SourceParser.cell01, SourceParser.cell11] ++
            SourceParser.gateListCells gates ++
            circuitFooterCells output ++
            TargetEmitter.sourceTargetBoundary ::
              SourceParser.packedTokenCells target))
        (sourceFocusTape
          ((circuitHeaderCells inputs (gate :: gates).length).reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              capacity scratch registers checks)
          gate.left
          (SourceParser.sourceCells gate.right ++
            [SourceParser.cell01, SourceParser.cell11] ++
            SourceParser.gateListCells gates ++
            circuitFooterCells output ++
            TargetEmitter.sourceTargetBoundary ::
              SourceParser.packedTokenCells target)) :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.step headerNavigatorNode (.node leftFirstRef)
      (TargetEmitterNavigator.headerWorkSteps
        inputs (gate :: gates).length) 0
      _ _ _ headerNavigatorNode_member localRun tail
  simpa [headerNavigatorNode, headerNavigatorRef,
    controlNode, controlRef, Node.reference] using path

def programEndFocusTape (left : List WorkSymbol)
    (output : RawSource) (target : List Token) : WorkTape :=
  (TargetEmitter.configAtWord 0 left
    (circuitFooterCells output ++
      TargetEmitter.sourceTargetBoundary ::
        SourceParser.packedTokenCells target)).tape

def circuitTerminatorCells : List WorkSymbol :=
  [SourceParser.cell10, SourceParser.cell01,
    SourceParser.cell10, SourceParser.cell11]

theorem header_empty_path
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (target : List Token)
    (inputs : Nat) (output : RawSource) :
    AcceptPath graph (.node headerNavigatorRef)
      (.node programEndRef)
      (TargetEmitterNavigator.headerWorkSteps inputs 0 + 1)
      (TargetEmitterRuntime.logicalTape capacity scratch registers
        checks
        (SourceParser.circuitCells
          { inputCount := inputs
            gates := []
            output := output })
        target)
      (programEndFocusTape
        ((circuitHeaderCells inputs 0).reverse ++
          TargetEmitterRuntime.logicalLeftWorkspace
            capacity scratch registers checks)
        output target) := by
  have localRun :
      LocalRejectRun headerNavigatorNode
        (TargetEmitterNavigator.headerWorkSteps inputs 0)
        (TargetEmitterRuntime.logicalTape capacity scratch registers
          checks
          (SourceParser.circuitCells
            { inputCount := inputs
              gates := []
              output := output })
          target)
        (programEndFocusTape
          ((circuitHeaderCells inputs 0).reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              capacity scratch registers checks)
          output target) := by
    change
      workRunExact? TargetEmitterNavigator.headerMachine
          (TargetEmitterNavigator.headerWorkSteps inputs 0)
          (TargetEmitterNavigator.configAtWord
            TargetEmitterNavigator.State.headerStart
            (TargetEmitterRuntime.logicalLeftWorkspace
              capacity scratch registers checks)
            (SourceParser.circuitCells
              { inputCount := inputs
                gates := []
                output := output } ++
              TargetEmitter.sourceTargetBoundary ::
                SourceParser.packedTokenCells target)) =
        some
          (TargetEmitterNavigator.configAtWord
            TargetEmitterNavigator.State.reject
            ((circuitHeaderCells inputs 0).reverse ++
              TargetEmitterRuntime.logicalLeftWorkspace
                capacity scratch registers checks)
            (circuitFooterCells output ++
              TargetEmitter.sourceTargetBoundary ::
                SourceParser.packedTokenCells target))
    simpa [TargetEmitterNavigator.cell00,
      TargetEmitterNavigator.cell10,
      SourceParser.circuitCells, SourceParser.gateListCells,
      SourceParser.cell00, SourceParser.cell10,
      circuitHeaderCells, circuitFooterCells,
      TargetEmitterNavigator.pushCrossed, List.append_assoc] using
        (TargetEmitterNavigator.header_empty_exact inputs
          (SourceParser.cell00 ::
            (SourceParser.sourceCells output ++
              [SourceParser.cell10, SourceParser.cell01,
                SourceParser.cell10, SourceParser.cell11] ++
              TargetEmitter.sourceTargetBoundary ::
                SourceParser.packedTokenCells target))
          (TargetEmitterRuntime.logicalLeftWorkspace
            capacity scratch registers checks))
  have tail :
      AcceptPath graph (.node programEndRef) (.node programEndRef) 0
        (programEndFocusTape
          ((circuitHeaderCells inputs 0).reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              capacity scratch registers checks)
          output target)
        (programEndFocusTape
          ((circuitHeaderCells inputs 0).reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              capacity scratch registers checks)
          output target) :=
    AcceptPath.terminal (.node programEndRef) _
  have path :=
    AcceptPath.stepReject headerNavigatorNode
      (.node programEndRef)
      (TargetEmitterNavigator.headerWorkSteps inputs 0) 0
      _ _ _ headerNavigatorNode_member localRun tail
  simpa [headerNavigatorNode, headerNavigatorRef,
    controlNode, controlRef, Node.reference] using path

theorem program_end_path
    (left : List WorkSymbol) (output : RawSource)
    (target : List Token) :
    AcceptPath graph (.node programEndRef)
      (.node outputFirstRef) 3
      (programEndFocusTape left output target)
      (sourceFocusTape
        (SourceParser.cell00 :: SourceParser.cell10 :: left)
        output
        (circuitTerminatorCells ++
          TargetEmitter.sourceTargetBoundary ::
            SourceParser.packedTokenCells target)) := by
  have localRun :
      LocalAcceptRun programEndNode 2
        (programEndFocusTape left output target)
        (sourceFocusTape
          (SourceParser.cell00 :: SourceParser.cell10 :: left)
          output
          (circuitTerminatorCells ++
            TargetEmitter.sourceTargetBoundary ::
              SourceParser.packedTokenCells target)) := by
    unfold LocalAcceptRun
    let suffix :=
      circuitTerminatorCells ++
        TargetEmitter.sourceTargetBoundary ::
          SourceParser.packedTokenCells target
    cases output with
    | input index =>
        simp only [programEndNode, controlNode,
          programEndFocusTape, sourceFocusTape,
          circuitFooterCells, circuitTerminatorCells,
          SourceParser.sourceCells, List.append_assoc]
        change
          workRunExact? TargetEmitterNavigator.programEndMachine 2
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.programFirst left
                (TargetEmitterNavigator.cell10 ::
                  TargetEmitterNavigator.cell00 ::
                    TargetEmitterNavigator.cell00 ::
                      TargetEmitterNavigator.cell11 ::
                        (SourceParser.natCells index ++ suffix))) =
            some
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.accept
                (TargetEmitterNavigator.cell00 ::
                  TargetEmitterNavigator.cell10 :: left)
                (TargetEmitterNavigator.cell00 ::
                  TargetEmitterNavigator.cell11 ::
                    (SourceParser.natCells index ++ suffix)))
        exact
          TargetEmitterNavigator.programEnd_exact left
            (TargetEmitterNavigator.cell11 ::
              (SourceParser.natCells index ++ suffix))
            TargetEmitterNavigator.cell00
    | gate index =>
        simp only [programEndNode, controlNode,
          programEndFocusTape, sourceFocusTape,
          circuitFooterCells, circuitTerminatorCells,
          SourceParser.sourceCells, List.append_assoc]
        change
          workRunExact? TargetEmitterNavigator.programEndMachine 2
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.programFirst left
                (TargetEmitterNavigator.cell10 ::
                  TargetEmitterNavigator.cell00 ::
                    TargetEmitterNavigator.cell01 ::
                      TargetEmitterNavigator.cell10 ::
                        (SourceParser.natCells index ++ suffix))) =
            some
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.accept
                (TargetEmitterNavigator.cell00 ::
                  TargetEmitterNavigator.cell10 :: left)
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell10 ::
                    (SourceParser.natCells index ++ suffix)))
        exact
          TargetEmitterNavigator.programEnd_exact left
            (TargetEmitterNavigator.cell10 ::
              (SourceParser.natCells index ++ suffix))
            TargetEmitterNavigator.cell01
    | constant value =>
        cases value with
        | false =>
            change
              workRunExact? TargetEmitterNavigator.programEndMachine 2
                  (TargetEmitterNavigator.configAtWord
                    TargetEmitterNavigator.State.programFirst left
                    (TargetEmitterNavigator.cell10 ::
                      TargetEmitterNavigator.cell00 ::
                        TargetEmitterNavigator.cell01 ::
                          TargetEmitterNavigator.cell00 :: suffix)) =
                some
                  (TargetEmitterNavigator.configAtWord
                    TargetEmitterNavigator.State.accept
                    (TargetEmitterNavigator.cell00 ::
                      TargetEmitterNavigator.cell10 :: left)
                    (TargetEmitterNavigator.cell01 ::
                      TargetEmitterNavigator.cell00 :: suffix))
            exact
              TargetEmitterNavigator.programEnd_exact left
                (TargetEmitterNavigator.cell00 :: suffix)
                TargetEmitterNavigator.cell01
        | true =>
            change
              workRunExact? TargetEmitterNavigator.programEndMachine 2
                  (TargetEmitterNavigator.configAtWord
                    TargetEmitterNavigator.State.programFirst left
                    (TargetEmitterNavigator.cell10 ::
                      TargetEmitterNavigator.cell00 ::
                        TargetEmitterNavigator.cell01 ::
                          TargetEmitterNavigator.cell01 :: suffix)) =
                some
                  (TargetEmitterNavigator.configAtWord
                    TargetEmitterNavigator.State.accept
                    (TargetEmitterNavigator.cell00 ::
                      TargetEmitterNavigator.cell10 :: left)
                    (TargetEmitterNavigator.cell01 ::
                      TargetEmitterNavigator.cell01 :: suffix))
            exact
              TargetEmitterNavigator.programEnd_exact left
                (TargetEmitterNavigator.cell01 :: suffix)
                TargetEmitterNavigator.cell01
  have tail :
      AcceptPath graph (.node outputFirstRef)
        (.node outputFirstRef) 0
        (sourceFocusTape
          (SourceParser.cell00 :: SourceParser.cell10 :: left)
          output
          (circuitTerminatorCells ++
            TargetEmitter.sourceTargetBoundary ::
              SourceParser.packedTokenCells target))
        (sourceFocusTape
          (SourceParser.cell00 :: SourceParser.cell10 :: left)
          output
          (circuitTerminatorCells ++
            TargetEmitter.sourceTargetBoundary ::
              SourceParser.packedTokenCells target)) :=
    AcceptPath.terminal (.node outputFirstRef) _
  have path :=
    AcceptPath.step programEndNode (.node outputFirstRef)
      2 0 _ _ _ programEndNode_member localRun tail
  simpa [programEndNode, programEndRef,
    controlNode, controlRef, Node.reference] using path

def gateEndFocusTape (left rest : List WorkSymbol) : WorkTape :=
  (TargetEmitter.configAtWord 0 left
    ([SourceParser.cell01, SourceParser.cell11] ++ rest)).tape

theorem gate_advance_next_path
    (left : List WorkSymbol) (source : RawSource)
    (rest : List WorkSymbol) :
    AcceptPath graph (.node gateAdvanceRef)
      (.node leftFirstRef) 4
      (gateEndFocusTape left
        (SourceParser.sourceCells source ++ rest))
      (sourceFocusTape
        (SourceParser.cell11 :: SourceParser.cell01 :: left)
        source rest) := by
  have localRun :
      LocalAcceptRun gateAdvanceNode 3
        (gateEndFocusTape left
          (SourceParser.sourceCells source ++ rest))
        (sourceFocusTape
          (SourceParser.cell11 :: SourceParser.cell01 :: left)
          source rest) := by
    unfold LocalAcceptRun
    cases source with
    | input index =>
        simp only [gateAdvanceNode, controlNode,
          gateEndFocusTape, sourceFocusTape,
          SourceParser.sourceCells]
        change
          workRunExact? TargetEmitterNavigator.gateAdvanceMachine 3
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.gateEndFirst left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell11 ::
                    TargetEmitterNavigator.cell00 ::
                      TargetEmitterNavigator.cell11 ::
                        (SourceParser.natCells index ++ rest))) =
            some
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.accept
                (TargetEmitterNavigator.cell11 ::
                  TargetEmitterNavigator.cell01 :: left)
                (TargetEmitterNavigator.cell00 ::
                  TargetEmitterNavigator.cell11 ::
                    (SourceParser.natCells index ++ rest)))
        exact
          TargetEmitterNavigator.gateAdvance_next_exact left
            (TargetEmitterNavigator.cell11 ::
              (SourceParser.natCells index ++ rest))
            TargetEmitterNavigator.cell00 (Or.inl rfl)
    | gate index =>
        simp only [gateAdvanceNode, controlNode,
          gateEndFocusTape, sourceFocusTape,
          SourceParser.sourceCells]
        change
          workRunExact? TargetEmitterNavigator.gateAdvanceMachine 3
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.gateEndFirst left
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell11 ::
                    TargetEmitterNavigator.cell01 ::
                      TargetEmitterNavigator.cell10 ::
                        (SourceParser.natCells index ++ rest))) =
            some
              (TargetEmitterNavigator.configAtWord
                TargetEmitterNavigator.State.accept
                (TargetEmitterNavigator.cell11 ::
                  TargetEmitterNavigator.cell01 :: left)
                (TargetEmitterNavigator.cell01 ::
                  TargetEmitterNavigator.cell10 ::
                    (SourceParser.natCells index ++ rest)))
        exact
          TargetEmitterNavigator.gateAdvance_next_exact left
            (TargetEmitterNavigator.cell10 ::
              (SourceParser.natCells index ++ rest))
            TargetEmitterNavigator.cell01 (Or.inr rfl)
    | constant value =>
        cases value with
        | false =>
            change
              workRunExact? TargetEmitterNavigator.gateAdvanceMachine 3
                  (TargetEmitterNavigator.configAtWord
                    TargetEmitterNavigator.State.gateEndFirst left
                    (TargetEmitterNavigator.cell01 ::
                      TargetEmitterNavigator.cell11 ::
                        TargetEmitterNavigator.cell01 ::
                          TargetEmitterNavigator.cell00 :: rest)) =
                some
                  (TargetEmitterNavigator.configAtWord
                    TargetEmitterNavigator.State.accept
                    (TargetEmitterNavigator.cell11 ::
                      TargetEmitterNavigator.cell01 :: left)
                    (TargetEmitterNavigator.cell01 ::
                      TargetEmitterNavigator.cell00 :: rest))
            exact
              TargetEmitterNavigator.gateAdvance_next_exact left
                (TargetEmitterNavigator.cell00 :: rest)
                TargetEmitterNavigator.cell01 (Or.inr rfl)
        | true =>
            change
              workRunExact? TargetEmitterNavigator.gateAdvanceMachine 3
                  (TargetEmitterNavigator.configAtWord
                    TargetEmitterNavigator.State.gateEndFirst left
                    (TargetEmitterNavigator.cell01 ::
                      TargetEmitterNavigator.cell11 ::
                        TargetEmitterNavigator.cell01 ::
                          TargetEmitterNavigator.cell01 :: rest)) =
                some
                  (TargetEmitterNavigator.configAtWord
                    TargetEmitterNavigator.State.accept
                    (TargetEmitterNavigator.cell11 ::
                      TargetEmitterNavigator.cell01 :: left)
                    (TargetEmitterNavigator.cell01 ::
                      TargetEmitterNavigator.cell01 :: rest))
            exact
              TargetEmitterNavigator.gateAdvance_next_exact left
                (TargetEmitterNavigator.cell01 :: rest)
                TargetEmitterNavigator.cell01 (Or.inr rfl)
  have tail :
      AcceptPath graph (.node leftFirstRef) (.node leftFirstRef) 0
        (sourceFocusTape
          (SourceParser.cell11 :: SourceParser.cell01 :: left)
          source rest)
        (sourceFocusTape
          (SourceParser.cell11 :: SourceParser.cell01 :: left)
          source rest) :=
    AcceptPath.terminal (.node leftFirstRef) _
  have path :=
    AcceptPath.step gateAdvanceNode (.node leftFirstRef)
      3 0 _ _ _ gateAdvanceNode_member localRun tail
  simpa [gateAdvanceNode, gateAdvanceRef,
    controlNode, controlRef, Node.reference] using path

theorem gate_advance_program_end_path
    (left : List WorkSymbol) (output : RawSource)
    (target : List Token) :
    AcceptPath graph (.node gateAdvanceRef)
      (.node programEndRef) 4
      (gateEndFocusTape left
        (circuitFooterCells output ++
          TargetEmitter.sourceTargetBoundary ::
            SourceParser.packedTokenCells target))
      (programEndFocusTape
        (SourceParser.cell11 :: SourceParser.cell01 :: left)
        output target) := by
  have localRun :
      LocalRejectRun gateAdvanceNode 3
        (gateEndFocusTape left
          (circuitFooterCells output ++
            TargetEmitter.sourceTargetBoundary ::
              SourceParser.packedTokenCells target))
        (programEndFocusTape
          (SourceParser.cell11 :: SourceParser.cell01 :: left)
          output target) := by
    change
      workRunExact? TargetEmitterNavigator.gateAdvanceMachine 3
          (TargetEmitterNavigator.configAtWord
            TargetEmitterNavigator.State.gateEndFirst left
            (TargetEmitterNavigator.cell01 ::
              TargetEmitterNavigator.cell11 ::
                (circuitFooterCells output ++
                  TargetEmitter.sourceTargetBoundary ::
                    SourceParser.packedTokenCells target))) =
        some
          (TargetEmitterNavigator.configAtWord
            TargetEmitterNavigator.State.reject
            (TargetEmitterNavigator.cell11 ::
              TargetEmitterNavigator.cell01 :: left)
            (circuitFooterCells output ++
              TargetEmitter.sourceTargetBoundary ::
                SourceParser.packedTokenCells target))
    simpa [circuitFooterCells, circuitTerminatorCells,
      TargetEmitterNavigator.cell00,
      TargetEmitterNavigator.cell01,
      TargetEmitterNavigator.cell10,
      TargetEmitterNavigator.cell11,
      SourceParser.cell00, SourceParser.cell01,
      SourceParser.cell10, SourceParser.cell11,
      List.append_assoc] using
        (TargetEmitterNavigator.gateAdvance_programEnd_exact left
          (SourceParser.cell00 ::
            (SourceParser.sourceCells output ++
              circuitTerminatorCells ++
              TargetEmitter.sourceTargetBoundary ::
                SourceParser.packedTokenCells target)))
  have tail :
      AcceptPath graph (.node programEndRef)
        (.node programEndRef) 0
        (programEndFocusTape
          (SourceParser.cell11 :: SourceParser.cell01 :: left)
          output target)
        (programEndFocusTape
          (SourceParser.cell11 :: SourceParser.cell01 :: left)
          output target) :=
    AcceptPath.terminal (.node programEndRef) _
  have path :=
    AcceptPath.stepReject gateAdvanceNode
      (.node programEndRef) 3 0 _ _ _
      gateAdvanceNode_member localRun tail
  simpa [gateAdvanceNode, gateAdvanceRef,
    controlNode, controlRef, Node.reference] using path

theorem header_empty_to_output_path
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (target : List Token)
    (inputs : Nat) (output : RawSource) :
    AcceptPath graph (.node headerNavigatorRef)
      (.node outputFirstRef)
      (TargetEmitterNavigator.headerWorkSteps inputs 0 + 4)
      (TargetEmitterRuntime.logicalTape capacity scratch registers
        checks
        (SourceParser.circuitCells
          { inputCount := inputs
            gates := []
            output := output })
        target)
      (sourceFocusTape
        (SourceParser.cell00 :: SourceParser.cell10 ::
          ((circuitHeaderCells inputs 0).reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              capacity scratch registers checks))
        output
        (circuitTerminatorCells ++
          TargetEmitter.sourceTargetBoundary ::
            SourceParser.packedTokenCells target)) := by
  have first :=
    header_empty_path capacity scratch registers checks target
      inputs output
  have second :=
    program_end_path
      ((circuitHeaderCells inputs 0).reverse ++
        TargetEmitterRuntime.logicalLeftWorkspace
          capacity scratch registers checks)
      output target
  have combined :=
    AcceptPath.trans graph (.node headerNavigatorRef)
      (.node programEndRef) (.node outputFirstRef)
      (TargetEmitterNavigator.headerWorkSteps inputs 0 + 1) 3
      _ _ _ first second
  simpa [Nat.add_assoc] using combined

theorem gate_advance_to_output_path
    (left : List WorkSymbol) (output : RawSource)
    (target : List Token) :
    AcceptPath graph (.node gateAdvanceRef)
      (.node outputFirstRef) 7
      (gateEndFocusTape left
        (circuitFooterCells output ++
          TargetEmitter.sourceTargetBoundary ::
            SourceParser.packedTokenCells target))
      (sourceFocusTape
        (SourceParser.cell00 :: SourceParser.cell10 ::
          SourceParser.cell11 :: SourceParser.cell01 :: left)
        output
        (circuitTerminatorCells ++
          TargetEmitter.sourceTargetBoundary ::
            SourceParser.packedTokenCells target)) := by
  have first :=
    gate_advance_program_end_path left output target
  have second :=
    program_end_path
      (SourceParser.cell11 :: SourceParser.cell01 :: left)
      output target
  have combined :=
    AcceptPath.trans graph (.node gateAdvanceRef)
      (.node programEndRef) (.node outputFirstRef)
      4 3 _ _ _ first second
  simpa using combined

end PNP.Concrete.LockedNAND.TargetEmitterControllerTrace

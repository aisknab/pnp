/-
Copyright (c) 2026 PNP Labs.

Fixed program graph for the grammar-only strict-v0 locked-NAND target emitter.

The graph begins with the literal grammar scanner, constructs the unary
ledger, traverses source syntax with fixed classifier/capture nodes, emits the
six legacy templates, folds the check stack, appends the final/output section,
and performs cursor-aware cleanup.  Every branch destination is embedded in a
literal graph bridge.  No executable definition below accepts a decoded
circuit, target word, semantic schedule, or caller-provided certificate.
-/

import PNP.Concrete.LockedNANDTargetEmitterBlockCompiler
import PNP.Concrete.LockedNANDTargetEmitterNavigator
import PNP.Concrete.LockedNANDTargetEmitterSourceCapture
import PNP.Concrete.LockedNANDTargetEmitterCursorControl
import PNP.Concrete.LockedNANDTargetEmitterCursorFinalizer

namespace PNP.Concrete.LockedNAND.TargetEmitterController

open PNP.Concrete
open WorkMachineProgramGraph
open TargetEmitterBlockCompiler
open TargetEmitterPrimitiveCompiler

namespace Plan

abbrev Primitive :=
  TargetEmitterPlan.Primitive

abbrev SourceKind :=
  TargetEmitterPlan.SourceKind

def sourceKinds : List SourceKind :=
  [.input, .constantFalse, .constantTrue, .gate]

def sourceKindCode : SourceKind → Nat
  | .input => 0
  | .constantFalse => 1
  | .constantTrue => 2
  | .gate => 3

def captureKind : SourceKind →
    TargetEmitterSourceCapture.SourceKind
  | .input => .input
  | .constantFalse => .constantFalse
  | .constantTrue => .constantTrue
  | .gate => .gate

def originalCell : SourceKind → WorkSymbol
  | .input => WorkSymbol.oneZero
  | .constantFalse => WorkSymbol.zeroZero
  | .constantTrue => WorkSymbol.zeroOne
  | .gate => WorkSymbol.oneZero

def optionProgram (program : Option (List Primitive)) :
    List Primitive :=
  program.getD []

def header : List Primitive :=
  optionProgram TargetEmitterPlan.headerProgram

def source (kind : SourceKind) (side : Nat) :
    List Primitive :=
  optionProgram (TargetEmitterPlan.sourceProgram kind side)

def trace : List Primitive :=
  optionProgram TargetEmitterPlan.traceProgram

def rightTrace : List Primitive :=
  trace ++ [.incrementRegister .currentGate]

def inputNormalization : List Primitive :=
  optionProgram TargetEmitterPlan.inputNormalizationProgram

def constantNormalization (value : Bool) : List Primitive :=
  optionProgram
    (TargetEmitterPlan.constantNormalizationProgram value)

def outputGateReset : List Primitive :=
  [.resetScratch]

def firstPrefix : List Primitive :=
  optionProgram TargetEmitterPlan.firstPrefixProgram

def nextPrefix : List Primitive :=
  optionProgram TargetEmitterPlan.nextPrefixTailProgram

def finalRaw : List Primitive :=
  optionProgram
    (TargetEmitterPlan.finalPositiveProgram
      TargetEmitterPlan.rawGateTrace)

def finalZero : List Primitive :=
  optionProgram TargetEmitterPlan.finalZeroProgram

def finalNormalized : List Primitive :=
  optionProgram
    (TargetEmitterPlan.finalPositiveProgram
      TargetEmitterPlan.traceCoordinate)

def beginOutput : List Primitive :=
  TargetEmitterPlan.beginOutputProgram

def outputItem : List Primitive :=
  TargetEmitterPlan.outputLoopItemProgram

def outputFinish : List Primitive :=
  TargetEmitterPlan.outputLoopFinishProgram

end Plan

/-! ### Structural addresses -/

/-- Even node names are reserved for explicit control nodes. -/
def controlNodeName (code : Nat) : Nat :=
  2 * code

theorem controlNodeName_even (code : Nat) :
    controlNodeName code % 2 = 0 := by
  unfold controlNodeName
  omega

theorem control_ne_block
    (controlCode blockCode index : Nat) :
    controlNodeName controlCode ≠
      blockNodeName blockCode index := by
  intro equality
  have parity := congrArg (fun value => value % 2) equality
  rw [controlNodeName_even, blockNodeName_odd] at parity
  contradiction

def controlRef (code : Nat) (program : WorkMachine) : NodeRef :=
  { name := controlNodeName code
    startState := program.startState }

def controlNode (code : Nat) (program : WorkMachine)
    (onAccept onReject : Endpoint) : Node :=
  { name := controlNodeName code
    program := program
    onAccept := onAccept
    onReject := onReject }

namespace Address

def scanner : Nat := 1
def ledger : Nat := 2
def stackInitialize : Nat := 3
def headerNavigator : Nat := 4
def programEnd : Nat := 5
def gateAdvance : Nat := 6

def leftFirst : Nat := 10
def leftNonInput : Nat := 11
def leftConstant : Nat := 12
def leftCapture (kind : Plan.SourceKind) : Nat :=
  20 + Plan.sourceKindCode kind
def leftRestore (kind : Plan.SourceKind) : Nat :=
  30 + Plan.sourceKindCode kind

def rightFirst : Nat := 40
def rightNonInput : Nat := 41
def rightConstant : Nat := 42
def rightCapture (kind : Plan.SourceKind) : Nat :=
  50 + Plan.sourceKindCode kind
def rightRestore (kind : Plan.SourceKind) : Nat :=
  60 + Plan.sourceKindCode kind

def outputFirst : Nat := 70
def outputNonInput : Nat := 71
def outputConstant : Nat := 72
def outputCapture (kind : Plan.SourceKind) : Nat :=
  80 + Plan.sourceKindCode kind

def rawInitialPop : Nat := 90
def rawLoopPop : Nat := 91
def normalizedInitialPop : Nat := 92
def normalizedLoopPop : Nat := 93
def outputCompare : Nat := 94
def finalizer : Nat := 95

end Address

namespace Block

def header : Nat := 1
def leftSource (kind : Plan.SourceKind) : Nat :=
  10 + Plan.sourceKindCode kind
def rightSource (kind : Plan.SourceKind) : Nat :=
  20 + Plan.sourceKindCode kind
def rightTrace (kind : Plan.SourceKind) : Nat :=
  30 + Plan.sourceKindCode kind
def inputNormalization : Nat := 50
def constantFalseNormalization : Nat := 51
def constantTrueNormalization : Nat := 52
def outputGateReset : Nat := 53
def rawFirstPrefix : Nat := 60
def rawNextPrefix : Nat := 61
def rawFinal : Nat := 62
def rawFinalZero : Nat := 63
def normalizedFirstPrefix : Nat := 70
def normalizedNextPrefix : Nat := 71
def normalizedFinal : Nat := 72
def beginOutput : Nat := 80
def outputItem : Nat := 81
def outputFinish : Nat := 82

end Block

/-! ### Closed references -/

def scannerRef : NodeRef :=
  controlRef Address.scanner TargetEmitterGrammarScanner.machine

def ledgerRef : NodeRef :=
  controlRef Address.ledger TargetEmitterLedger.machine

def stackInitializeRef : NodeRef :=
  controlRef Address.stackInitialize
    TargetEmitterCheckStack.Initialize.machine

def headerRef : NodeRef :=
  blockEntry Block.header Plan.header

def headerNavigatorRef : NodeRef :=
  controlRef Address.headerNavigator
    TargetEmitterNavigator.headerMachine

def programEndRef : NodeRef :=
  controlRef Address.programEnd
    TargetEmitterNavigator.programEndMachine

def gateAdvanceRef : NodeRef :=
  controlRef Address.gateAdvance
    TargetEmitterNavigator.gateAdvanceMachine

def leftFirstRef : NodeRef :=
  controlRef Address.leftFirst
    TargetEmitterNavigator.sourceFirstMachine

def leftNonInputRef : NodeRef :=
  controlRef Address.leftNonInput
    TargetEmitterNavigator.nonInputMachine

def leftConstantRef : NodeRef :=
  controlRef Address.leftConstant
    TargetEmitterNavigator.constantMachine

def leftCaptureRef (kind : Plan.SourceKind) : NodeRef :=
  controlRef (Address.leftCapture kind)
    (TargetEmitterSourceCapture.machine (Plan.captureKind kind))

def leftRestoreRef (kind : Plan.SourceKind) : NodeRef :=
  controlRef (Address.leftRestore kind)
    (TargetEmitterCursorControl.restoreMachine
      (Plan.originalCell kind))

def leftSourceRef (kind : Plan.SourceKind) : NodeRef :=
  blockEntry (Block.leftSource kind) (Plan.source kind 0)

def rightFirstRef : NodeRef :=
  controlRef Address.rightFirst
    TargetEmitterNavigator.sourceFirstMachine

def rightNonInputRef : NodeRef :=
  controlRef Address.rightNonInput
    TargetEmitterNavigator.nonInputMachine

def rightConstantRef : NodeRef :=
  controlRef Address.rightConstant
    TargetEmitterNavigator.constantMachine

def rightCaptureRef (kind : Plan.SourceKind) : NodeRef :=
  controlRef (Address.rightCapture kind)
    (TargetEmitterSourceCapture.machine (Plan.captureKind kind))

def rightRestoreRef (kind : Plan.SourceKind) : NodeRef :=
  controlRef (Address.rightRestore kind)
    (TargetEmitterCursorControl.restoreMachine
      (Plan.originalCell kind))

def rightSourceRef (kind : Plan.SourceKind) : NodeRef :=
  blockEntry (Block.rightSource kind) (Plan.source kind 1)

def rightTraceRef (kind : Plan.SourceKind) : NodeRef :=
  blockEntry (Block.rightTrace kind) Plan.rightTrace

def outputFirstRef : NodeRef :=
  controlRef Address.outputFirst
    TargetEmitterNavigator.sourceFirstMachine

def outputNonInputRef : NodeRef :=
  controlRef Address.outputNonInput
    TargetEmitterNavigator.nonInputMachine

def outputConstantRef : NodeRef :=
  controlRef Address.outputConstant
    TargetEmitterNavigator.constantMachine

def outputCaptureRef (kind : Plan.SourceKind) : NodeRef :=
  controlRef (Address.outputCapture kind)
    (TargetEmitterSourceCapture.machine (Plan.captureKind kind))

def inputNormalizationRef : NodeRef :=
  blockEntry Block.inputNormalization
    Plan.inputNormalization

def constantFalseNormalizationRef : NodeRef :=
  blockEntry Block.constantFalseNormalization
    (Plan.constantNormalization false)

def constantTrueNormalizationRef : NodeRef :=
  blockEntry Block.constantTrueNormalization
    (Plan.constantNormalization true)

def outputGateResetRef : NodeRef :=
  blockEntry Block.outputGateReset Plan.outputGateReset

def rawInitialPopRef : NodeRef :=
  controlRef Address.rawInitialPop
    TargetEmitterCheckStack.Pop.machine

def rawFirstPrefixRef : NodeRef :=
  blockEntry Block.rawFirstPrefix Plan.firstPrefix

def rawLoopPopRef : NodeRef :=
  controlRef Address.rawLoopPop
    TargetEmitterCheckStack.Pop.machine

def rawNextPrefixRef : NodeRef :=
  blockEntry Block.rawNextPrefix Plan.nextPrefix

def rawFinalRef : NodeRef :=
  blockEntry Block.rawFinal Plan.finalRaw

def rawFinalZeroRef : NodeRef :=
  blockEntry Block.rawFinalZero Plan.finalZero

def normalizedInitialPopRef : NodeRef :=
  controlRef Address.normalizedInitialPop
    TargetEmitterCheckStack.Pop.machine

def normalizedFirstPrefixRef : NodeRef :=
  blockEntry Block.normalizedFirstPrefix Plan.firstPrefix

def normalizedLoopPopRef : NodeRef :=
  controlRef Address.normalizedLoopPop
    TargetEmitterCheckStack.Pop.machine

def normalizedNextPrefixRef : NodeRef :=
  blockEntry Block.normalizedNextPrefix Plan.nextPrefix

def normalizedFinalRef : NodeRef :=
  blockEntry Block.normalizedFinal Plan.finalNormalized

def beginOutputRef : NodeRef :=
  blockEntry Block.beginOutput Plan.beginOutput

def outputCompareRef : NodeRef :=
  controlRef Address.outputCompare
    (TargetEmitterScratchCompareSlot.machineFor .baseline)

def outputItemRef : NodeRef :=
  blockEntry Block.outputItem Plan.outputItem

def outputFinishRef : NodeRef :=
  blockEntry Block.outputFinish Plan.outputFinish

def finalizerRef : NodeRef :=
  controlRef Address.finalizer
    TargetEmitterCursorFinalizer.machine

/-! ### Explicit control nodes -/

def scannerNode : Node :=
  controlNode Address.scanner
    TargetEmitterGrammarScanner.machine
    (.node ledgerRef) .reject

def ledgerNode : Node :=
  controlNode Address.ledger
    TargetEmitterLedger.machine
    (.node stackInitializeRef) .reject

def stackInitializeNode : Node :=
  controlNode Address.stackInitialize
    TargetEmitterCheckStack.Initialize.machine
    (.node headerRef) .reject

def headerNavigatorNode : Node :=
  controlNode Address.headerNavigator
    TargetEmitterNavigator.headerMachine
    (.node leftFirstRef) (.node programEndRef)

def programEndNode : Node :=
  controlNode Address.programEnd
    TargetEmitterNavigator.programEndMachine
    (.node outputFirstRef) .reject

def gateAdvanceNode : Node :=
  controlNode Address.gateAdvance
    TargetEmitterNavigator.gateAdvanceMachine
    (.node leftFirstRef) (.node programEndRef)

def leftFirstNode : Node :=
  controlNode Address.leftFirst
    TargetEmitterNavigator.sourceFirstMachine
    (.node (leftCaptureRef .input))
    (.node leftNonInputRef)

def leftNonInputNode : Node :=
  controlNode Address.leftNonInput
    TargetEmitterNavigator.nonInputMachine
    (.node (leftCaptureRef .gate))
    (.node leftConstantRef)

def leftConstantNode : Node :=
  controlNode Address.leftConstant
    TargetEmitterNavigator.constantMachine
    (.node (leftCaptureRef .constantFalse))
    (.node (leftCaptureRef .constantTrue))

def leftCaptureNode (kind : Plan.SourceKind) : Node :=
  controlNode (Address.leftCapture kind)
    (TargetEmitterSourceCapture.machine (Plan.captureKind kind))
    (.node (leftSourceRef kind)) .reject

def leftRestoreNode (kind : Plan.SourceKind) : Node :=
  controlNode (Address.leftRestore kind)
    (TargetEmitterCursorControl.restoreMachine
      (Plan.originalCell kind))
    (.node rightFirstRef) .reject

def rightFirstNode : Node :=
  controlNode Address.rightFirst
    TargetEmitterNavigator.sourceFirstMachine
    (.node (rightCaptureRef .input))
    (.node rightNonInputRef)

def rightNonInputNode : Node :=
  controlNode Address.rightNonInput
    TargetEmitterNavigator.nonInputMachine
    (.node (rightCaptureRef .gate))
    (.node rightConstantRef)

def rightConstantNode : Node :=
  controlNode Address.rightConstant
    TargetEmitterNavigator.constantMachine
    (.node (rightCaptureRef .constantFalse))
    (.node (rightCaptureRef .constantTrue))

def rightCaptureNode (kind : Plan.SourceKind) : Node :=
  controlNode (Address.rightCapture kind)
    (TargetEmitterSourceCapture.machine (Plan.captureKind kind))
    (.node (rightSourceRef kind)) .reject

def rightRestoreNode (kind : Plan.SourceKind) : Node :=
  controlNode (Address.rightRestore kind)
    (TargetEmitterCursorControl.restoreMachine
      (Plan.originalCell kind))
    (.node gateAdvanceRef) .reject

def outputFirstNode : Node :=
  controlNode Address.outputFirst
    TargetEmitterNavigator.sourceFirstMachine
    (.node (outputCaptureRef .input))
    (.node outputNonInputRef)

def outputNonInputNode : Node :=
  controlNode Address.outputNonInput
    TargetEmitterNavigator.nonInputMachine
    (.node (outputCaptureRef .gate))
    (.node outputConstantRef)

def outputConstantNode : Node :=
  controlNode Address.outputConstant
    TargetEmitterNavigator.constantMachine
    (.node (outputCaptureRef .constantFalse))
    (.node (outputCaptureRef .constantTrue))

def outputCaptureContinuation : Plan.SourceKind → NodeRef
  | .input => inputNormalizationRef
  | .constantFalse => constantFalseNormalizationRef
  | .constantTrue => constantTrueNormalizationRef
  | .gate => outputGateResetRef

def outputCaptureNode (kind : Plan.SourceKind) : Node :=
  controlNode (Address.outputCapture kind)
    (TargetEmitterSourceCapture.machine (Plan.captureKind kind))
    (.node (outputCaptureContinuation kind)) .reject

def rawInitialPopNode : Node :=
  controlNode Address.rawInitialPop
    TargetEmitterCheckStack.Pop.machine
    (.node rawFirstPrefixRef) (.node rawFinalZeroRef)

def rawLoopPopNode : Node :=
  controlNode Address.rawLoopPop
    TargetEmitterCheckStack.Pop.machine
    (.node rawNextPrefixRef) (.node rawFinalRef)

def normalizedInitialPopNode : Node :=
  controlNode Address.normalizedInitialPop
    TargetEmitterCheckStack.Pop.machine
    (.node normalizedFirstPrefixRef) .reject

def normalizedLoopPopNode : Node :=
  controlNode Address.normalizedLoopPop
    TargetEmitterCheckStack.Pop.machine
    (.node normalizedNextPrefixRef) (.node normalizedFinalRef)

def outputCompareNode : Node :=
  controlNode Address.outputCompare
    (TargetEmitterScratchCompareSlot.machineFor .baseline)
    (.node outputFinishRef) (.node outputItemRef)

def finalizerNode : Node :=
  controlNode Address.finalizer
    TargetEmitterCursorFinalizer.machine
    .accept .reject

/-! ### Local well-formedness certificates -/

private theorem nodeWellFormed_of_interfaces
    (name : Nat) (program : WorkMachine)
    (onAccept onReject : Endpoint)
    (pairwise :
      program.rules.Pairwise
        WorkMachineProgramGraph.QueryDistinct)
    (noAccept :
      ∀ symbol,
        findWorkRule program.rules
          program.acceptState symbol = none)
    (noReject :
      ∀ symbol,
        findWorkRule program.rules
          program.rejectState symbol = none)
    (acceptNeReject :
      program.acceptState ≠ program.rejectState) :
    Node.WellFormed
      { name := name
        program := program
        onAccept := onAccept
        onReject := onReject } := by
  exact
    ⟨pairwise,
      noRuleAt_of_findWorkRule_none
        program program.acceptState noAccept,
      noRuleAt_of_findWorkRule_none
        program program.rejectState noReject,
      acceptNeReject⟩

private theorem scannerNode_wellFormed :
    scannerNode.WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      TargetEmitterGrammarScanner.rules.Pairwise
        TargetEmitterGrammarScanner.QueryDistinct
    exact
      TargetEmitterGrammarScanner.rules_pairwise_query_distinct
  · exact TargetEmitterGrammarScanner.no_rule_at_accept
  · exact TargetEmitterGrammarScanner.no_rule_at_reject
  · exact
      TargetEmitterGrammarScanner.machine_acceptState_ne_rejectState

private theorem ledgerNode_wellFormed :
    ledgerNode.WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      TargetEmitterLedger.rules.Pairwise
        TargetEmitterLedger.QueryDistinct
    exact TargetEmitterLedger.rules_pairwise_query_distinct
  · exact TargetEmitterLedger.no_rule_at_accept
  · exact TargetEmitterLedger.no_rule_at_reject
  · exact TargetEmitterLedger.machine_accept_ne_reject

private theorem stackInitializeNode_wellFormed :
    stackInitializeNode.WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      TargetEmitterCheckStack.Initialize.rules.Pairwise
        TargetEmitterCheckStack.QueryDistinct
    exact TargetEmitterCheckStack.Initialize.rules_pairwise
  · exact TargetEmitterCheckStack.Initialize.no_rule_at_accept
  · exact TargetEmitterCheckStack.Initialize.no_rule_at_reject
  · exact TargetEmitterCheckStack.Initialize.accept_ne_reject

private theorem headerNavigatorNode_wellFormed :
    headerNavigatorNode.WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      TargetEmitterNavigator.rules.Pairwise
        TargetEmitterNavigator.QueryDistinct
    exact TargetEmitterNavigator.rules_pairwise
  · exact TargetEmitterNavigator.no_rule_at_accept
  · exact TargetEmitterNavigator.no_rule_at_reject
  · exact TargetEmitterNavigator.machineFrom_accept_ne_reject _

private theorem programEndNode_wellFormed :
    programEndNode.WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      TargetEmitterNavigator.rules.Pairwise
        TargetEmitterNavigator.QueryDistinct
    exact TargetEmitterNavigator.rules_pairwise
  · exact TargetEmitterNavigator.no_rule_at_accept
  · exact TargetEmitterNavigator.no_rule_at_reject
  · exact TargetEmitterNavigator.machineFrom_accept_ne_reject _

private theorem gateAdvanceNode_wellFormed :
    gateAdvanceNode.WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      TargetEmitterNavigator.rules.Pairwise
        TargetEmitterNavigator.QueryDistinct
    exact TargetEmitterNavigator.rules_pairwise
  · exact TargetEmitterNavigator.no_rule_at_accept
  · exact TargetEmitterNavigator.no_rule_at_reject
  · exact TargetEmitterNavigator.machineFrom_accept_ne_reject _

private theorem sourceFirstNode_wellFormed
    (code : Nat) (onAccept onReject : Endpoint) :
    (controlNode code TargetEmitterNavigator.sourceFirstMachine
      onAccept onReject).WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      TargetEmitterNavigator.rules.Pairwise
        TargetEmitterNavigator.QueryDistinct
    exact TargetEmitterNavigator.rules_pairwise
  · exact TargetEmitterNavigator.no_rule_at_accept
  · exact TargetEmitterNavigator.no_rule_at_reject
  · exact TargetEmitterNavigator.machineFrom_accept_ne_reject _

private theorem nonInputNode_wellFormed
    (code : Nat) (onAccept onReject : Endpoint) :
    (controlNode code TargetEmitterNavigator.nonInputMachine
      onAccept onReject).WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      TargetEmitterNavigator.rules.Pairwise
        TargetEmitterNavigator.QueryDistinct
    exact TargetEmitterNavigator.rules_pairwise
  · exact TargetEmitterNavigator.no_rule_at_accept
  · exact TargetEmitterNavigator.no_rule_at_reject
  · exact TargetEmitterNavigator.machineFrom_accept_ne_reject _

private theorem constantNode_wellFormed
    (code : Nat) (onAccept onReject : Endpoint) :
    (controlNode code TargetEmitterNavigator.constantMachine
      onAccept onReject).WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      TargetEmitterNavigator.rules.Pairwise
        TargetEmitterNavigator.QueryDistinct
    exact TargetEmitterNavigator.rules_pairwise
  · exact TargetEmitterNavigator.no_rule_at_accept
  · exact TargetEmitterNavigator.no_rule_at_reject
  · exact TargetEmitterNavigator.machineFrom_accept_ne_reject _

private theorem sourceCaptureNode_wellFormed
    (code : Nat) (kind :
      TargetEmitterSourceCapture.SourceKind)
    (onAccept : Endpoint) :
    (controlNode code (TargetEmitterSourceCapture.machine kind)
      onAccept .reject).WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      (TargetEmitterSourceCapture.rules kind).Pairwise
        TargetEmitterSourceCapture.QueryDistinct
    exact TargetEmitterSourceCapture.rules_pairwise kind
  · exact TargetEmitterSourceCapture.no_rule_at_accept kind
  · exact TargetEmitterSourceCapture.no_rule_at_reject kind
  · exact TargetEmitterSourceCapture.accept_ne_reject kind

private theorem cursorRestoreNode_wellFormed
    (code : Nat) (original : WorkSymbol)
    (onAccept : Endpoint) :
    (controlNode code
      (TargetEmitterCursorControl.restoreMachine original)
      onAccept .reject).WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      (TargetEmitterCursorControl.rules original).Pairwise
        TargetEmitterCursorControl.QueryDistinct
    exact TargetEmitterCursorControl.rules_pairwise original
  · exact TargetEmitterCursorControl.no_rule_at_restored original
  · exact TargetEmitterCursorControl.no_rule_at_reject original
  · exact TargetEmitterCursorControl.restore_accept_ne_reject original

private theorem stackPopNode_wellFormed
    (code : Nat) (onAccept onReject : Endpoint) :
    (controlNode code TargetEmitterCheckStack.Pop.machine
      onAccept onReject).WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      TargetEmitterCheckStack.Pop.rules.Pairwise
        TargetEmitterCheckStack.QueryDistinct
    exact TargetEmitterCheckStack.Pop.rules_pairwise
  · exact TargetEmitterCheckStack.Pop.no_rule_at_accept
  · exact TargetEmitterCheckStack.Pop.no_rule_at_reject
  · exact TargetEmitterCheckStack.Pop.accept_ne_reject

private theorem outputCompareNode_wellFormed :
    outputCompareNode.WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      TargetEmitterScratchCompareSlot.rules.Pairwise
        TargetEmitterScratchCompareSlot.QueryDistinct
    exact TargetEmitterScratchCompareSlot.rules_pairwise
  · exact TargetEmitterScratchCompareSlot.no_rule_at_accept
  · exact TargetEmitterScratchCompareSlot.no_rule_at_reject
  · exact TargetEmitterScratchCompareSlot.accept_ne_reject _

private theorem finalizerNode_wellFormed :
    finalizerNode.WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change
      TargetEmitterCursorFinalizer.rules.Pairwise
        (fun left right =>
          (left.sourceState, left.readSymbol) ≠
            (right.sourceState, right.readSymbol))
    exact TargetEmitterCursorFinalizer.rules_pairwise
  · exact TargetEmitterCursorFinalizer.no_rule_at_accept
  · exact TargetEmitterCursorFinalizer.no_rule_at_reject
  · exact TargetEmitterCursorFinalizer.accept_ne_reject

/-! ### Linear blocks and the complete finite graph -/

def headerNodes : List Node :=
  blockNodes Block.header Plan.header
    (.node headerNavigatorRef)

def leftSourceNodes (kind : Plan.SourceKind) : List Node :=
  blockNodes (Block.leftSource kind) (Plan.source kind 0)
    (.node (leftRestoreRef kind))

def rightSourceNodes (kind : Plan.SourceKind) : List Node :=
  blockNodes (Block.rightSource kind) (Plan.source kind 1)
    (.node (rightTraceRef kind))

def rightTraceNodes (kind : Plan.SourceKind) : List Node :=
  blockNodes (Block.rightTrace kind) Plan.rightTrace
    (.node (rightRestoreRef kind))

def inputNormalizationNodes : List Node :=
  blockNodes Block.inputNormalization Plan.inputNormalization
    (.node normalizedInitialPopRef)

def constantFalseNormalizationNodes : List Node :=
  blockNodes Block.constantFalseNormalization
    (Plan.constantNormalization false)
    (.node normalizedInitialPopRef)

def constantTrueNormalizationNodes : List Node :=
  blockNodes Block.constantTrueNormalization
    (Plan.constantNormalization true)
    (.node normalizedInitialPopRef)

def outputGateResetNodes : List Node :=
  blockNodes Block.outputGateReset Plan.outputGateReset
    (.node rawInitialPopRef)

def rawFirstPrefixNodes : List Node :=
  blockNodes Block.rawFirstPrefix Plan.firstPrefix
    (.node rawLoopPopRef)

def rawNextPrefixNodes : List Node :=
  blockNodes Block.rawNextPrefix Plan.nextPrefix
    (.node rawLoopPopRef)

def rawFinalNodes : List Node :=
  blockNodes Block.rawFinal Plan.finalRaw
    (.node beginOutputRef)

def rawFinalZeroNodes : List Node :=
  blockNodes Block.rawFinalZero Plan.finalZero
    (.node beginOutputRef)

def normalizedFirstPrefixNodes : List Node :=
  blockNodes Block.normalizedFirstPrefix Plan.firstPrefix
    (.node normalizedLoopPopRef)

def normalizedNextPrefixNodes : List Node :=
  blockNodes Block.normalizedNextPrefix Plan.nextPrefix
    (.node normalizedLoopPopRef)

def normalizedFinalNodes : List Node :=
  blockNodes Block.normalizedFinal Plan.finalNormalized
    (.node beginOutputRef)

def beginOutputNodes : List Node :=
  blockNodes Block.beginOutput Plan.beginOutput
    (.node outputCompareRef)

def outputItemNodes : List Node :=
  blockNodes Block.outputItem Plan.outputItem
    (.node outputCompareRef)

def outputFinishNodes : List Node :=
  blockNodes Block.outputFinish Plan.outputFinish
    (.node finalizerRef)

structure BlockDescriptor where
  code : Nat
  primitives : List TargetEmitterPlan.Primitive
  continuation : Endpoint

def BlockDescriptor.materialize
    (descriptor : BlockDescriptor) : List Node :=
  blockNodes descriptor.code descriptor.primitives
    descriptor.continuation

def fixedBlockDescriptors : List BlockDescriptor :=
  [ { code := Block.header
      primitives := Plan.header
      continuation := .node headerNavigatorRef }
  , { code := Block.inputNormalization
      primitives := Plan.inputNormalization
      continuation := .node normalizedInitialPopRef }
  , { code := Block.constantFalseNormalization
      primitives := Plan.constantNormalization false
      continuation := .node normalizedInitialPopRef }
  , { code := Block.constantTrueNormalization
      primitives := Plan.constantNormalization true
      continuation := .node normalizedInitialPopRef }
  , { code := Block.outputGateReset
      primitives := Plan.outputGateReset
      continuation := .node rawInitialPopRef }
  , { code := Block.rawFirstPrefix
      primitives := Plan.firstPrefix
      continuation := .node rawLoopPopRef }
  , { code := Block.rawNextPrefix
      primitives := Plan.nextPrefix
      continuation := .node rawLoopPopRef }
  , { code := Block.rawFinal
      primitives := Plan.finalRaw
      continuation := .node beginOutputRef }
  , { code := Block.rawFinalZero
      primitives := Plan.finalZero
      continuation := .node beginOutputRef }
  , { code := Block.normalizedFirstPrefix
      primitives := Plan.firstPrefix
      continuation := .node normalizedLoopPopRef }
  , { code := Block.normalizedNextPrefix
      primitives := Plan.nextPrefix
      continuation := .node normalizedLoopPopRef }
  , { code := Block.normalizedFinal
      primitives := Plan.finalNormalized
      continuation := .node beginOutputRef }
  , { code := Block.beginOutput
      primitives := Plan.beginOutput
      continuation := .node outputCompareRef }
  , { code := Block.outputItem
      primitives := Plan.outputItem
      continuation := .node outputCompareRef }
  , { code := Block.outputFinish
      primitives := Plan.outputFinish
      continuation := .node finalizerRef } ]

def leftBlockDescriptors : List BlockDescriptor :=
  Plan.sourceKinds.map fun kind =>
    { code := Block.leftSource kind
      primitives := Plan.source kind 0
      continuation := .node (leftRestoreRef kind) }

def rightBlockDescriptors : List BlockDescriptor :=
  Plan.sourceKinds.flatMap fun kind =>
    [ { code := Block.rightSource kind
        primitives := Plan.source kind 1
        continuation := .node (rightTraceRef kind) }
    , { code := Block.rightTrace kind
        primitives := Plan.rightTrace
        continuation := .node (rightRestoreRef kind) } ]

def blockDescriptors : List BlockDescriptor :=
  fixedBlockDescriptors ++
    leftBlockDescriptors ++ rightBlockDescriptors

def allBlockNodes : List Node :=
  blockDescriptors.flatMap BlockDescriptor.materialize

def leftControlNodes : List Node :=
  [leftFirstNode, leftNonInputNode, leftConstantNode] ++
    (Plan.sourceKinds.map leftCaptureNode ++
      Plan.sourceKinds.map leftRestoreNode)

def rightControlNodes : List Node :=
  [rightFirstNode, rightNonInputNode, rightConstantNode] ++
    (Plan.sourceKinds.map rightCaptureNode ++
      Plan.sourceKinds.map rightRestoreNode)

def outputControlNodes : List Node :=
  [outputFirstNode, outputNonInputNode, outputConstantNode] ++
  Plan.sourceKinds.map outputCaptureNode

def controlNodes : List Node :=
  [scannerNode, ledgerNode, stackInitializeNode,
    headerNavigatorNode, programEndNode, gateAdvanceNode] ++
    (leftControlNodes ++
      (rightControlNodes ++
        (outputControlNodes ++
          [rawInitialPopNode, rawLoopPopNode,
            normalizedInitialPopNode, normalizedLoopPopNode,
            outputCompareNode, finalizerNode])))

def nodes : List Node :=
  controlNodes ++ allBlockNodes

private theorem leftControlNodes_wellFormed :
    ∀ node, node ∈ leftControlNodes → node.WellFormed := by
  intro node member
  rcases List.mem_append.mp member with initialMember | restMember
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
      at initialMember
    rcases initialMember with nodeEq | nodeEq | nodeEq
    · subst node
      exact sourceFirstNode_wellFormed _ _ _
    · subst node
      exact nonInputNode_wellFormed _ _ _
    · subst node
      exact constantNode_wellFormed _ _ _
  · rcases List.mem_append.mp restMember with
      captureMember | restoreMember
    · rcases List.mem_map.mp captureMember with
        ⟨kind, _kindMember, nodeEq⟩
      subst node
      exact sourceCaptureNode_wellFormed
        _ (Plan.captureKind kind) _
    · rcases List.mem_map.mp restoreMember with
        ⟨kind, _kindMember, nodeEq⟩
      subst node
      exact cursorRestoreNode_wellFormed
        _ (Plan.originalCell kind) _

private theorem rightControlNodes_wellFormed :
    ∀ node, node ∈ rightControlNodes → node.WellFormed := by
  intro node member
  rcases List.mem_append.mp member with initialMember | restMember
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
      at initialMember
    rcases initialMember with nodeEq | nodeEq | nodeEq
    · subst node
      exact sourceFirstNode_wellFormed _ _ _
    · subst node
      exact nonInputNode_wellFormed _ _ _
    · subst node
      exact constantNode_wellFormed _ _ _
  · rcases List.mem_append.mp restMember with
      captureMember | restoreMember
    · rcases List.mem_map.mp captureMember with
        ⟨kind, _kindMember, nodeEq⟩
      subst node
      exact sourceCaptureNode_wellFormed
        _ (Plan.captureKind kind) _
    · rcases List.mem_map.mp restoreMember with
        ⟨kind, _kindMember, nodeEq⟩
      subst node
      exact cursorRestoreNode_wellFormed
        _ (Plan.originalCell kind) _

private theorem outputControlNodes_wellFormed :
    ∀ node, node ∈ outputControlNodes → node.WellFormed := by
  intro node member
  rcases List.mem_append.mp member with
    initialMember | captureMember
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
      at initialMember
    rcases initialMember with nodeEq | nodeEq | nodeEq
    · subst node
      exact sourceFirstNode_wellFormed _ _ _
    · subst node
      exact nonInputNode_wellFormed _ _ _
    · subst node
      exact constantNode_wellFormed _ _ _
  · rcases List.mem_map.mp captureMember with
      ⟨kind, _kindMember, nodeEq⟩
    subst node
    exact sourceCaptureNode_wellFormed
      _ (Plan.captureKind kind) _

private theorem controlNodes_wellFormed :
    ∀ node, node ∈ controlNodes → node.WellFormed := by
  intro node member
  rcases List.mem_append.mp member with initialMember | member
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
      at initialMember
    rcases initialMember with
      nodeEq | nodeEq | nodeEq | nodeEq | nodeEq | nodeEq
    · subst node
      exact scannerNode_wellFormed
    · subst node
      exact ledgerNode_wellFormed
    · subst node
      exact stackInitializeNode_wellFormed
    · subst node
      exact headerNavigatorNode_wellFormed
    · subst node
      exact programEndNode_wellFormed
    · subst node
      exact gateAdvanceNode_wellFormed
  · rcases List.mem_append.mp member with leftMember | member
    · exact leftControlNodes_wellFormed node leftMember
    · rcases List.mem_append.mp member with
        rightMember | member
      · exact rightControlNodes_wellFormed node rightMember
      · rcases List.mem_append.mp member with
          outputMember | finalMember
        · exact outputControlNodes_wellFormed node outputMember
        · simp only [List.mem_cons, List.not_mem_nil, or_false]
            at finalMember
          rcases finalMember with
            nodeEq | nodeEq | nodeEq | nodeEq | nodeEq | nodeEq
          · subst node
            exact stackPopNode_wellFormed _ _ _
          · subst node
            exact stackPopNode_wellFormed _ _ _
          · subst node
            exact stackPopNode_wellFormed _ _ _
          · subst node
            exact stackPopNode_wellFormed _ _ _
          · subst node
            exact outputCompareNode_wellFormed
          · subst node
            exact finalizerNode_wellFormed

private theorem nodeNames_pairwise_of_nodup
    (items : List Node)
    (nodup : (items.map (fun node => node.name)).Nodup) :
    items.Pairwise (fun left right => left.name ≠ right.name) := by
  induction items with
  | nil =>
      exact List.Pairwise.nil
  | cons first rest inductionHypothesis =>
      have parts := List.nodup_cons.mp nodup
      apply List.pairwise_cons.mpr
      constructor
      · intro right rightMember nameEq
        apply parts.1
        apply List.mem_map.mpr
        exact ⟨right, rightMember, nameEq.symm⟩
      · exact inductionHypothesis parts.2

set_option maxRecDepth 300000 in
private theorem controlNodeNames_nodup :
    (controlNodes.map (fun node => node.name)).Nodup := by
  decide

private theorem controlNodes_names_pairwise :
    controlNodes.Pairwise
      (fun left right => left.name ≠ right.name) := by
  exact nodeNames_pairwise_of_nodup
    controlNodes controlNodeNames_nodup

set_option maxRecDepth 300000 in
private theorem controlNodeNames_even :
    ∀ name,
      name ∈ controlNodes.map (fun node => node.name) →
        name % 2 = 0 := by
  decide

set_option maxRecDepth 300000 in
private theorem blockDescriptorCodes_nodup :
    (blockDescriptors.map (fun descriptor =>
      descriptor.code)).Nodup := by
  decide

private theorem descriptorNodes_names_pairwise
    (descriptors : List BlockDescriptor)
    (codesNodup :
      (descriptors.map (fun descriptor =>
        descriptor.code)).Nodup) :
    (descriptors.flatMap
      BlockDescriptor.materialize).Pairwise
        (fun left right => left.name ≠ right.name) := by
  induction descriptors with
  | nil =>
      exact List.Pairwise.nil
  | cons descriptor rest inductionHypothesis =>
      have codeParts := List.nodup_cons.mp codesNodup
      rw [List.flatMap_cons, List.pairwise_append]
      refine
        ⟨blockNodes_names_pairwise
            descriptor.code descriptor.primitives
            descriptor.continuation,
          inductionHypothesis codeParts.2, ?_⟩
      intro left leftMember right rightMember
      rcases List.mem_flatMap.mp rightMember with
        ⟨rightDescriptor, descriptorMember, rightMember⟩
      have codeNe :
          descriptor.code ≠ rightDescriptor.code := by
        intro codeEq
        apply codeParts.1
        exact List.mem_map.mpr
          ⟨rightDescriptor, descriptorMember, codeEq.symm⟩
      exact blockNodes_cross_names
        descriptor.code rightDescriptor.code
        descriptor.primitives rightDescriptor.primitives
        descriptor.continuation rightDescriptor.continuation
        codeNe left leftMember right rightMember

private theorem allBlockNodes_names_pairwise :
    allBlockNodes.Pairwise
      (fun left right => left.name ≠ right.name) := by
  exact descriptorNodes_names_pairwise
    blockDescriptors blockDescriptorCodes_nodup

private def allDescriptorsCompile :
    List BlockDescriptor → Bool
  | [] => true
  | descriptor :: rest =>
      (compileProgram descriptor.primitives).isSome &&
        allDescriptorsCompile rest

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem blockDescriptors_all_compile :
    allDescriptorsCompile blockDescriptors = true := by
  decide

private theorem compile_of_allDescriptorsCompile
    (descriptors : List BlockDescriptor)
    (allCompile : allDescriptorsCompile descriptors = true)
    (descriptor : BlockDescriptor)
    (member : descriptor ∈ descriptors) :
    ∃ programs,
      compileProgram descriptor.primitives = some programs := by
  induction descriptors generalizing descriptor with
  | nil =>
      contradiction
  | cons first rest inductionHypothesis =>
      simp only [allDescriptorsCompile, Bool.and_eq_true]
        at allCompile
      rcases allCompile with ⟨firstCompiles, restCompile⟩
      rcases List.mem_cons.mp member with descriptorEq | restMember
      · subst descriptor
        cases compiled :
            compileProgram first.primitives with
        | none =>
            simp [compiled] at firstCompiles
        | some programs =>
            exact ⟨programs, rfl⟩
      · exact inductionHypothesis restCompile
          descriptor restMember

private theorem allBlockNodes_wellFormed :
    ∀ node, node ∈ allBlockNodes → node.WellFormed := by
  intro node member
  rcases List.mem_flatMap.mp member with
    ⟨descriptor, descriptorMember, nodeMember⟩
  rcases compile_of_allDescriptorsCompile
      blockDescriptors blockDescriptors_all_compile
      descriptor descriptorMember with
    ⟨programs, compiled⟩
  exact blockNodes_wellFormed_of_compiled
    descriptor.code descriptor.primitives programs
    descriptor.continuation compiled node nodeMember

private def allDescriptorsNonempty :
    List BlockDescriptor → Bool
  | [] => true
  | descriptor :: rest =>
      (!descriptor.primitives.isEmpty) &&
        allDescriptorsNonempty rest

set_option maxRecDepth 1000000 in
private theorem blockDescriptors_all_nonempty :
    allDescriptorsNonempty blockDescriptors = true := by
  decide

private theorem nonempty_of_allDescriptorsNonempty
    (descriptors : List BlockDescriptor)
    (allNonempty : allDescriptorsNonempty descriptors = true)
    (descriptor : BlockDescriptor)
    (member : descriptor ∈ descriptors) :
    descriptor.primitives ≠ [] := by
  induction descriptors generalizing descriptor with
  | nil =>
      contradiction
  | cons first rest inductionHypothesis =>
      simp only [allDescriptorsNonempty, Bool.and_eq_true]
        at allNonempty
      rcases allNonempty with
        ⟨firstNonempty, restNonempty⟩
      rcases List.mem_cons.mp member with descriptorEq | restMember
      · subst descriptor
        intro empty
        simp [empty] at firstNonempty
      · exact inductionHypothesis restNonempty
          descriptor restMember

theorem controlNode_member_nodes
    (node : Node) (member : node ∈ controlNodes) :
    node ∈ nodes :=
  List.mem_append.mpr (Or.inl member)

theorem blockNode_member_nodes
    (node : Node) (member : node ∈ allBlockNodes) :
    node ∈ nodes :=
  List.mem_append.mpr (Or.inr member)

theorem descriptorBlockNode_member_nodes
    (descriptor : BlockDescriptor)
    (descriptorMember : descriptor ∈ blockDescriptors)
    (node : Node)
    (nodeMember : node ∈ descriptor.materialize) :
    node ∈ nodes := by
  apply blockNode_member_nodes node
  apply List.mem_flatMap.mpr
  exact ⟨descriptor, descriptorMember, nodeMember⟩

private theorem nodeReference_resolves
    (node : Node) (member : node ∈ nodes) :
    Endpoint.Resolves nodes (.node node.reference) := by
  exact ⟨node, member, rfl, rfl⟩

private theorem blockEntry_resolves
    (descriptor : BlockDescriptor)
    (descriptorMember : descriptor ∈ blockDescriptors) :
    Endpoint.Resolves nodes
      (.node (blockEntry descriptor.code
        descriptor.primitives)) := by
  rcases compile_of_allDescriptorsCompile
      blockDescriptors blockDescriptors_all_compile
      descriptor descriptorMember with
    ⟨programs, compiled⟩
  have primitivesNonempty :=
    nonempty_of_allDescriptorsNonempty
      blockDescriptors blockDescriptors_all_nonempty
      descriptor descriptorMember
  have lengths :=
    blockMachines_length_of_compiled
      descriptor.primitives programs compiled
  cases programs with
  | nil =>
      have machinesEmpty :
          blockMachines descriptor.primitives = [] := by
        unfold blockMachines
        rw [compiled]
        rfl
      rw [machinesEmpty] at lengths
      have primitiveEmpty :
          descriptor.primitives = [] :=
        List.eq_nil_of_length_eq_zero lengths.symm
      exact (primitivesNonempty primitiveEmpty).elim
  | cons program rest =>
      let firstNode : Node :=
        { name := blockNodeName descriptor.code 0
          program := program
          onAccept :=
            entryEndpoint descriptor.code 1 rest
              descriptor.continuation
          onReject := .reject }
      refine ⟨firstNode, ?_, ?_, ?_⟩
      · apply blockNode_member_nodes firstNode
        apply List.mem_flatMap.mpr
        refine ⟨descriptor, descriptorMember, ?_⟩
        simp [BlockDescriptor.materialize, blockNodes,
          blockMachines, compiled, nodesFrom, firstNode,
          entryEndpoint, machineRef]
      · simp [blockEntry, blockEntry?, blockMachines,
          compiled, entryRef?, machineRef, firstNode]
      · simp [blockEntry, blockEntry?, blockMachines,
          compiled, entryRef?, machineRef, firstNode]

private def controlReferences : List NodeRef :=
  controlNodes.map Node.reference

private def blockReferences : List NodeRef :=
  blockDescriptors.map fun descriptor =>
    blockEntry descriptor.code descriptor.primitives

private def knownReferences : List NodeRef :=
  controlReferences ++ blockReferences

private theorem knownReference_resolves
    (reference : NodeRef)
    (known : reference ∈ knownReferences) :
    Endpoint.Resolves nodes (.node reference) := by
  rcases List.mem_append.mp known with
    controlKnown | blockKnown
  · rcases List.mem_map.mp controlKnown with
      ⟨node, nodeMember, referenceEq⟩
    rw [← referenceEq]
    exact nodeReference_resolves node
      (controlNode_member_nodes node nodeMember)
  · rcases List.mem_map.mp blockKnown with
      ⟨descriptor, descriptorMember, referenceEq⟩
    rw [← referenceEq]
    exact blockEntry_resolves descriptor descriptorMember

private def referenceKnownIn :
    List NodeRef → NodeRef → Bool
  | [], _ => false
  | first :: rest, target =>
      decide (first = target) || referenceKnownIn rest target

private theorem member_of_referenceKnownIn
    (references : List NodeRef) (target : NodeRef)
    (known : referenceKnownIn references target = true) :
    target ∈ references := by
  induction references with
  | nil =>
      contradiction
  | cons first rest inductionHypothesis =>
      simp only [referenceKnownIn, Bool.or_eq_true] at known
      rcases known with firstEq | restKnown
      · have equality : first = target := by
          simpa using firstEq
        subst target
        exact List.Mem.head rest
      · exact List.Mem.tail first
          (inductionHypothesis restKnown)

private def endpointKnown : Endpoint → Bool
  | .node reference =>
      referenceKnownIn knownReferences reference
  | .accept | .reject | .dead => true

private theorem endpoint_resolves_of_known
    (endpoint : Endpoint)
    (known : endpointKnown endpoint = true) :
    Endpoint.Resolves nodes endpoint := by
  cases endpoint with
  | node reference =>
      exact knownReference_resolves reference
        (member_of_referenceKnownIn
          knownReferences reference known)
  | accept =>
      trivial
  | reject =>
      trivial
  | dead =>
      trivial

private def allNodeEndpointsKnown :
    List Node → Bool
  | [] => true
  | node :: rest =>
      endpointKnown node.onAccept &&
        (endpointKnown node.onReject &&
          allNodeEndpointsKnown rest)

private theorem endpoints_known_of_all
    (items : List Node)
    (allKnown : allNodeEndpointsKnown items = true)
    (node : Node) (member : node ∈ items) :
    endpointKnown node.onAccept = true ∧
      endpointKnown node.onReject = true := by
  induction items generalizing node with
  | nil =>
      contradiction
  | cons first rest inductionHypothesis =>
      simp only [allNodeEndpointsKnown, Bool.and_eq_true]
        at allKnown
      rcases allKnown with
        ⟨firstAccept, firstReject, restKnown⟩
      rcases List.mem_cons.mp member with nodeEq | restMember
      · subst node
        exact ⟨firstAccept, firstReject⟩
      · exact inductionHypothesis restKnown node restMember

set_option maxRecDepth 1000000 in
private theorem controlEndpoints_all_known :
    allNodeEndpointsKnown controlNodes = true := by
  decide

private theorem controlNode_endpoints_resolve
    (node : Node) (member : node ∈ controlNodes) :
    Endpoint.Resolves nodes node.onAccept ∧
      Endpoint.Resolves nodes node.onReject := by
  rcases endpoints_known_of_all controlNodes
      controlEndpoints_all_known node member with
    ⟨acceptKnown, rejectKnown⟩
  exact
    ⟨endpoint_resolves_of_known node.onAccept acceptKnown,
      endpoint_resolves_of_known node.onReject rejectKnown⟩

private def allContinuationsKnown :
    List BlockDescriptor → Bool
  | [] => true
  | descriptor :: rest =>
      endpointKnown descriptor.continuation &&
        allContinuationsKnown rest

set_option maxRecDepth 1000000 in
private theorem blockContinuations_all_known :
    allContinuationsKnown blockDescriptors = true := by
  decide

private theorem continuation_known_of_all
    (descriptors : List BlockDescriptor)
    (allKnown : allContinuationsKnown descriptors = true)
    (descriptor : BlockDescriptor)
    (member : descriptor ∈ descriptors) :
    endpointKnown descriptor.continuation = true := by
  induction descriptors generalizing descriptor with
  | nil =>
      contradiction
  | cons first rest inductionHypothesis =>
      simp only [allContinuationsKnown, Bool.and_eq_true]
        at allKnown
      rcases allKnown with ⟨firstKnown, restKnown⟩
      rcases List.mem_cons.mp member with descriptorEq | restMember
      · subst descriptor
        exact firstKnown
      · exact inductionHypothesis restKnown
          descriptor restMember

private theorem blockNode_endpoints_resolve
    (node : Node) (member : node ∈ allBlockNodes) :
    Endpoint.Resolves nodes node.onAccept ∧
      Endpoint.Resolves nodes node.onReject := by
  rcases List.mem_flatMap.mp member with
    ⟨descriptor, descriptorMember, nodeMember⟩
  have continuationResolves :
      Endpoint.Resolves nodes descriptor.continuation :=
    endpoint_resolves_of_known descriptor.continuation
      (continuation_known_of_all blockDescriptors
        blockContinuations_all_known descriptor descriptorMember)
  apply nodesFrom_endpoints_resolve nodes descriptor.code 0
    (blockMachines descriptor.primitives)
    descriptor.continuation
  · intro blockNode blockNodeMember
    apply blockNode_member_nodes blockNode
    apply List.mem_flatMap.mpr
    exact ⟨descriptor, descriptorMember, blockNodeMember⟩
  · exact continuationResolves
  · exact nodeMember

private theorem controlNode_name_even
    (node : Node) (member : node ∈ controlNodes) :
    node.name % 2 = 0 := by
  have nameMember :
      node.name ∈ controlNodes.map (fun item => item.name) :=
    List.mem_map.mpr ⟨node, member, rfl⟩
  exact controlNodeNames_even node.name nameMember

private theorem blockNode_name_odd
    (node : Node) (member : node ∈ allBlockNodes) :
    node.name % 2 = 1 := by
  rcases List.mem_flatMap.mp member with
    ⟨descriptor, _descriptorMember, nodeMember⟩
  rcases nodesFrom_member_name descriptor.code 0
      (blockMachines descriptor.primitives)
      descriptor.continuation node nodeMember with
    ⟨offset, _offsetBound, nameEq⟩
  rw [nameEq]
  simpa using blockNodeName_odd descriptor.code offset

private theorem nodes_names_pairwise :
    nodes.Pairwise
      (fun left right => left.name ≠ right.name) := by
  rw [nodes, List.pairwise_append]
  refine
    ⟨controlNodes_names_pairwise,
      allBlockNodes_names_pairwise, ?_⟩
  intro control controlMember block blockMember nameEq
  have even := controlNode_name_even control controlMember
  have odd := blockNode_name_odd block blockMember
  rw [nameEq, odd] at even
  contradiction

private theorem nodes_wellFormed :
    ∀ node, node ∈ nodes → node.WellFormed := by
  intro node member
  rcases List.mem_append.mp member with
    controlMember | blockMember
  · exact controlNodes_wellFormed node controlMember
  · exact allBlockNodes_wellFormed node blockMember

private theorem entry_resolves :
    Endpoint.Resolves nodes (.node scannerRef) := by
  change Endpoint.Resolves nodes
    (.node scannerNode.reference)
  apply nodeReference_resolves scannerNode
  apply controlNode_member_nodes scannerNode
  exact List.Mem.head _

private theorem nodes_endpoints_resolve :
    ∀ node, node ∈ nodes →
      Endpoint.Resolves nodes node.onAccept ∧
        Endpoint.Resolves nodes node.onReject := by
  intro node member
  rcases List.mem_append.mp member with
    controlMember | blockMember
  · exact controlNode_endpoints_resolve node controlMember
  · exact blockNode_endpoints_resolve node blockMember

def graph : Graph :=
  { nodes := nodes
    entry := scannerRef }

/-- Lift an exact sequence of local primitive runs through any materialized
controller block.  Descriptor membership is structural evidence about the
fixed graph, not a runtime lookup or caller-provided machine schedule. -/
theorem descriptor_acceptPath_of_compiled
    (descriptor : BlockDescriptor)
    (descriptorMember : descriptor ∈ blockDescriptors)
    (programs : List WorkMachine)
    (compiled :
      compileProgram descriptor.primitives = some programs)
    (programsNonempty : programs ≠ [])
    (steps : Nat) (initialTape finalTape : WorkTape)
    (runs :
      LinearAcceptRuns programs steps initialTape finalTape) :
    WorkMachineProgramPath.AcceptPath graph
      (.node
        (blockEntry descriptor.code descriptor.primitives))
      descriptor.continuation steps initialTape finalTape := by
  have path :=
    blockNodes_acceptPath_of_compiled graph descriptor.code
      descriptor.primitives programs descriptor.continuation
      steps initialTape finalTape compiled
      (fun node member => by
        change node ∈ nodes
        exact descriptorBlockNode_member_nodes
          descriptor descriptorMember node
          (by
            simpa [BlockDescriptor.materialize] using member))
      runs
  rw [← blockEntry_eq_entryEndpoint_of_compiled
    descriptor.code descriptor.primitives programs
    descriptor.continuation compiled programsNonempty] at path
  exact path

theorem graph_wellFormed :
    graph.WellFormed := by
  exact
    ⟨nodes_names_pairwise,
      nodes_wellFormed,
      entry_resolves,
      nodes_endpoints_resolve⟩

def machine : WorkMachine :=
  WorkMachineProgramGraph.machine graph

def compiledMachine : Machine :=
  compileWorkMachine machine

theorem rules_pairwise :
    machine.rules.Pairwise
      WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed

theorem machine_start_ne_accept :
    machine.startState ≠ machine.acceptState :=
  WorkMachineProgramGraph.machine_start_ne_accept graph

theorem machine_start_ne_reject :
    machine.startState ≠ machine.rejectState :=
  WorkMachineProgramGraph.machine_start_ne_reject graph

theorem machine_accept_ne_reject :
    machine.acceptState ≠ machine.rejectState :=
  WorkMachineProgramGraph.machine_accept_ne_reject graph

theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule machine.rules machine.acceptState symbol = none :=
  WorkMachineProgramGraph.no_rule_at_accept graph symbol

theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule machine.rules machine.rejectState symbol = none :=
  WorkMachineProgramGraph.no_rule_at_reject graph symbol

theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule machine.rules globalDeadState symbol = none :=
  WorkMachineProgramGraph.no_rule_at_dead graph symbol

theorem accept_halted (tape : WorkTape) :
    machine.isHalted
      { state := machine.acceptState, tape := tape } = true :=
  WorkMachineProgramGraph.global_accept_halted graph tape

theorem reject_halted (tape : WorkTape) :
    machine.isHalted
      { state := machine.rejectState, tape := tape } = true :=
  WorkMachineProgramGraph.global_reject_halted graph tape

theorem dead_stuck (tape : WorkTape) :
    workStep? machine
      { state := globalDeadState, tape := tape } = none :=
  WorkMachineProgramGraph.dead_stuck graph tape

theorem rules_length :
    machine.rules.length =
      (nodes.map
        (fun node => 18 + node.program.rules.length)).sum := by
  exact WorkMachineProgramGraph.rules_length graph

/-- Literal rule count of the one fixed grammar-only target-emitter graph.
The value is obtained by reducing the materialized node list and every
embedded work-machine rule list in the kernel. -/
def ruleCount : Nat := 1387921

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
theorem rules_length_literal :
    machine.rules.length = ruleCount := by
  rw [rules_length]
  rfl

end PNP.Concrete.LockedNAND.TargetEmitterController

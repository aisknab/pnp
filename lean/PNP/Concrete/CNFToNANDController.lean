/-
Copyright (c) 2026 PNP Labs.

Literal finite controller for compiling a validated CNF carrier to a
strict-v0 NAND circuit.

The graph in this file is deliberately structural.  It embeds the source
grammar scanner, ledger, carrier validation, two finite CNF grammar passes,
closed emitter blocks, cursor controls, and terminal cleanup in one literal
work-machine rule table.  Every branch is a graph endpoint; no executable
definition accepts a decoded formula, an emission schedule, or a
caller-supplied certificate.

Exact runtime traces are layered above this module.  The public interface
here fixes the graph, proves its structural well-formedness, exposes its
literal rule count, and separates all global endpoints.
-/

import PNP.Concrete.CNFToNANDCarrierTokenReader
import PNP.Concrete.CNFToNANDControllerBlocks
import PNP.Concrete.LockedNANDTargetEmitterBlockCompiler
import PNP.Concrete.LockedNANDTargetEmitterCheckStack
import PNP.Concrete.LockedNANDTargetEmitterCursorControl
import PNP.Concrete.LockedNANDTargetEmitterCursorFinalizer
import PNP.Concrete.LockedNANDTargetEmitterGrammarScanner
import PNP.Concrete.LockedNANDTargetEmitterLedger
import PNP.Concrete.LockedNANDTargetEmitterNavigator

namespace PNP.Concrete.CNFToNANDController

open PNP.Concrete.LockedNAND
open PNP.Concrete.LockedNAND.TargetEmitterPlan
open PNP.Concrete.LockedNAND.TargetEmitterBlockCompiler
open PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler
open PNP.Concrete.WorkMachineProgramGraph

abbrev Primitive :=
  PNP.Concrete.LockedNAND.TargetEmitterPlan.Primitive

namespace Blocks

open PNP.Concrete.CNFToNANDControllerBlocks

def countNegativeSignProgram : List Primitive :=
  countLiteralProgram ++ resetLiteralIndexProgram

def countPositiveSignProgram : List Primitive :=
  countLiteralProgram ++ resetLiteralIndexProgram

def emitNegativeSignProgram : List Primitive :=
  resetLiteralIndexProgram

def emitPositiveSignProgram : List Primitive :=
  resetLiteralIndexProgram

def popCoordinateProgram : List Primitive :=
  PNP.Concrete.CNFToNANDEmitterPlan.popCoordinateProgram

end Blocks

/-! ## Finite grammar control -/

inductive Pass where
  | count
  | emit
deriving BEq, DecidableEq, Repr

inductive FinishKind where
  | empty
  | nonempty
deriving BEq, DecidableEq, Repr

/--
Finite control states for the canonical CNF grammar.

The two clauses states remember whether a completed clause has already been
seen.  Consequently the graph can defer the special empty-formula gate-count
increment until after the first pass has verified the physical `programEnd`.
The overflow literal states ensure that a unary literal index is never
incremented after it reaches the decoded width.
-/
inductive GrammarState where
  | header
  | clausesEmpty
  | clausesNonempty
  | clause
  | positive
  | positiveOverflow
  | negative
  | negativeOverflow
  | finishedEmpty
  | finishedNonempty
deriving BEq, DecidableEq, Repr

def passes : List Pass :=
  [.count, .emit]

def activeGrammarStates : List GrammarState :=
  [.header, .clausesEmpty, .clausesNonempty, .clause,
    .positive, .positiveOverflow, .negative, .negativeOverflow]

def grammarStates : List GrammarState :=
  activeGrammarStates ++ [.finishedEmpty, .finishedNonempty]

def finishKinds : List FinishKind :=
  [.empty, .nonempty]

def cnfTokens : List CNFToken :=
  [.f, .sep, .finish, .t]

def bools : List Bool :=
  [false, true]

def Pass.code : Pass → Nat
  | .count => 0
  | .emit => 1

def FinishKind.code : FinishKind → Nat
  | .empty => 0
  | .nonempty => 1

def GrammarState.code : GrammarState → Nat
  | .header => 0
  | .clausesEmpty => 1
  | .clausesNonempty => 2
  | .clause => 3
  | .positive => 4
  | .positiveOverflow => 5
  | .negative => 6
  | .negativeOverflow => 7
  | .finishedEmpty => 8
  | .finishedNonempty => 9

def tokenCode : CNFToken → Nat
  | .f => 0
  | .sep => 1
  | .finish => 2
  | .t => 3

def tokenSecondCell : CNFToken → WorkSymbol
  | .f | .finish => WorkSymbol.zeroZero
  | .sep | .t => WorkSymbol.zeroOne

def stateFinishKind? : GrammarState → Option FinishKind
  | .finishedEmpty => some .empty
  | .finishedNonempty => some .nonempty
  | _ => none

def validGrammarToken : GrammarState → CNFToken → Bool
  | .header, .f | .header, .t => true
  | .clausesEmpty, .sep | .clausesEmpty, .finish => true
  | .clausesNonempty, .sep | .clausesNonempty, .finish => true
  | .clause, .f | .clause, .t | .clause, .finish => true
  | .positive, .f | .positive, .t => true
  | .positiveOverflow, .f | .positiveOverflow, .t => true
  | .negative, .f | .negative, .t => true
  | .negativeOverflow, .f | .negativeOverflow, .t => true
  | _, _ => false

def deterministicNextState :
    GrammarState → CNFToken → GrammarState
  | .header, .f => .clausesEmpty
  | .header, .t => .header
  | .clausesEmpty, .sep => .clause
  | .clausesEmpty, .finish => .finishedEmpty
  | .clausesNonempty, .sep => .clause
  | .clausesNonempty, .finish => .finishedNonempty
  | .clause, .finish => .clausesNonempty
  | .positive, .f => .clause
  | .positiveOverflow, .f => .clause
  | .positiveOverflow, .t => .positiveOverflow
  | .negative, .f => .clause
  | .negativeOverflow, .f => .clause
  | .negativeOverflow, .t => .negativeOverflow
  | state, _ => state

def inRangeState (positive : Bool) : GrammarState :=
  if positive then .positive else .negative

def overflowState (positive : Bool) : GrammarState :=
  if positive then .positiveOverflow else .negativeOverflow

def actionCode (pass : Pass) (state : GrammarState)
    (token : CNFToken) : Nat :=
  100 * pass.code + 10 * state.code + tokenCode token

/-! ## Even control names and odd compiled-block names -/

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
def workspaceZero : Nat := 3
def validationHeader : Nat := 4
def validationFirst : Nat := 5
def validationFirstNonInput : Nat := 6
def validationFirstConstant : Nat := 7
def validationFirstReader : Nat := 8
def validationSecond : Nat := 9
def validationSecondNonInput : Nat := 10
def validationSecondConstant : Nat := 11
def validationSecondReader : Nat := 12
def validationAdvance : Nat := 13
def validationProgramEnd : Nat := 14
def validationOutputFirst : Nat := 15
def validationOutputNonInput : Nat := 16
def validationOutput : Nat := 17
def validationRewind : Nat := 18
def countHeader : Nat := 19
def emitHeader : Nat := 20
def stackInitialize : Nat := 21

def firstBit (pass : Pass) (state : GrammarState) : Nat :=
  100 + 100 * pass.code + 3 * state.code

def secondBit (pass : Pass) (state : GrammarState)
    (first : Bool) : Nat :=
  firstBit pass state + if first then 2 else 1

def install (pass : Pass) (state : GrammarState)
    (token : CNFToken) : Nat :=
  400 + actionCode pass state token

def literalCompare (pass : Pass) (state : GrammarState)
    (token : CNFToken) : Nat :=
  700 + actionCode pass state token

def restore (pass : Pass) (state : GrammarState)
    (token : CNFToken) : Nat :=
  1000 + actionCode pass state token

def gateAdvance (pass : Pass) (state : GrammarState) : Nat :=
  1300 + 20 * pass.code + state.code

def programEnd (pass : Pass) (kind : FinishKind) : Nat :=
  1400 + 2 * pass.code + kind.code

def countRewind (kind : FinishKind) : Nat :=
  1410 + kind.code

def countInstallVersion (kind : FinishKind) : Nat :=
  1420 + kind.code

def countRestoreVersion : Nat := 1430
def countPassRewind : Nat := 1431

def emitRewind : Nat := 1440
def emitInstallVersion : Nat := 1441

def clauseCompareFirst : Nat := 1450
def clauseCompareLoop : Nat := 1451
def formulaCompareMarkerFirst : Nat := 1460
def formulaCompareFalseFirst : Nat := 1461
def formulaCompareMarkerLoop : Nat := 1462
def formulaCompareFalseLoop : Nat := 1463
def finalizer : Nat := 1470

end Address

namespace Block

def resetWorkspace : Nat := 1
def countWidth : Nat := 10
def countClause : Nat := 11
def countEmptyFormula : Nat := 12
def countNegativeSign : Nat := 13
def countPositiveSign : Nat := 14
def countValidNegative : Nat := 15
def countAdvancePositive : Nat := 16
def countAdvanceNegative : Nat := 17

def emitInitializeClause : Nat := 20
def emitNegativeSign : Nat := 21
def emitPositiveSign : Nat := 22
def emitPositiveLiteral : Nat := 23
def emitNegativeLiteral : Nat := 24
def emitInvalidLiteral : Nat := 25
def emitAdvancePositive : Nat := 26
def emitAdvanceNegative : Nat := 27

def emitHeader : Nat := 30
def initializeFormula : Nat := 31

def clausePopFirst : Nat := 40
def clauseSeed : Nat := 41
def clausePopLoop : Nat := 42
def clauseExtend : Nat := 43
def clauseFinishNonempty : Nat := 44
def clauseFinishEmpty : Nat := 45

def formulaPopFirst : Nat := 50
def formulaSeedFalse : Nat := 51
def formulaSeedGate : Nat := 52
def formulaPopLoop : Nat := 53
def formulaExtendFalse : Nat := 54
def formulaExtendGate : Nat := 55
def formulaEmpty : Nat := 56
def suffix : Nat := 60

end Block

/-! ## Closed references -/

def scannerRef : NodeRef :=
  controlRef Address.scanner TargetEmitterGrammarScanner.machine

def ledgerRef : NodeRef :=
  controlRef Address.ledger TargetEmitterLedger.machine

def stackInitializeRef : NodeRef :=
  controlRef Address.stackInitialize
    TargetEmitterCheckStack.Initialize.machine

def workspaceZeroRef : NodeRef :=
  controlRef Address.workspaceZero
    (TargetEmitterScratchCompareSlot.machineFor .inputCount)

def validationHeaderRef : NodeRef :=
  controlRef Address.validationHeader
    TargetEmitterNavigator.headerMachine

def validationFirstRef : NodeRef :=
  controlRef Address.validationFirst
    TargetEmitterNavigator.sourceFirstMachine

def validationFirstNonInputRef : NodeRef :=
  controlRef Address.validationFirstNonInput
    TargetEmitterNavigator.nonInputMachine

def validationFirstConstantRef : NodeRef :=
  controlRef Address.validationFirstConstant
    TargetEmitterNavigator.constantMachine

def validationFirstReaderRef : NodeRef :=
  controlRef Address.validationFirstReader
    CNFToNANDCarrierTokenReader.firstSourceMachine

def validationSecondRef : NodeRef :=
  controlRef Address.validationSecond
    TargetEmitterNavigator.sourceFirstMachine

def validationSecondNonInputRef : NodeRef :=
  controlRef Address.validationSecondNonInput
    TargetEmitterNavigator.nonInputMachine

def validationSecondConstantRef : NodeRef :=
  controlRef Address.validationSecondConstant
    TargetEmitterNavigator.constantMachine

def validationSecondReaderRef : NodeRef :=
  controlRef Address.validationSecondReader
    CNFToNANDCarrierTokenReader.firstSourceMachine

def validationAdvanceRef : NodeRef :=
  controlRef Address.validationAdvance
    TargetEmitterNavigator.gateAdvanceMachine

def validationProgramEndRef : NodeRef :=
  controlRef Address.validationProgramEnd
    TargetEmitterNavigator.programEndMachine

def validationOutputRef : NodeRef :=
  controlRef Address.validationOutput
    TargetEmitterNavigator.constantMachine

def validationOutputFirstRef : NodeRef :=
  controlRef Address.validationOutputFirst
    TargetEmitterNavigator.sourceFirstMachine

def validationOutputNonInputRef : NodeRef :=
  controlRef Address.validationOutputNonInput
    TargetEmitterNavigator.nonInputMachine

def validationRewindRef : NodeRef :=
  controlRef Address.validationRewind
    CNFToNANDCarrierTokenReader.Rewind.machine

def passHeaderRef (pass : Pass) : NodeRef :=
  controlRef
    (match pass with
      | .count => Address.countHeader
      | .emit => Address.emitHeader)
    TargetEmitterNavigator.headerMachine

def firstBitRef (pass : Pass)
    (state : GrammarState) : NodeRef :=
  controlRef (Address.firstBit pass state)
    CNFToNANDCarrierTokenReader.firstSourceMachine

def secondBitRef (pass : Pass) (state : GrammarState)
    (first : Bool) : NodeRef :=
  controlRef (Address.secondBit pass state first)
    CNFToNANDCarrierTokenReader.secondSourceMachine

def installRef (pass : Pass) (state : GrammarState)
    (token : CNFToken) : NodeRef :=
  controlRef (Address.install pass state token)
    (TargetEmitterCursorControl.installMachine
      (tokenSecondCell token))

def literalCompareRef (pass : Pass)
    (state : GrammarState) (token : CNFToken) : NodeRef :=
  controlRef (Address.literalCompare pass state token)
    (TargetEmitterScratchCompareSlot.machineFor .inputCount)

def restoreRef (pass : Pass) (state : GrammarState)
    (token : CNFToken) : NodeRef :=
  controlRef (Address.restore pass state token)
    (TargetEmitterCursorControl.restoreMachine
      (tokenSecondCell token))

def gateAdvanceRef (pass : Pass)
    (state : GrammarState) : NodeRef :=
  controlRef (Address.gateAdvance pass state)
    TargetEmitterNavigator.gateAdvanceMachine

def programEndRef (pass : Pass)
    (kind : FinishKind) : NodeRef :=
  controlRef (Address.programEnd pass kind)
    TargetEmitterNavigator.programEndMachine

def countRewindRef (kind : FinishKind) : NodeRef :=
  controlRef (Address.countRewind kind)
    CNFToNANDCarrierTokenReader.Rewind.machine

def countInstallVersionRef (kind : FinishKind) : NodeRef :=
  controlRef (Address.countInstallVersion kind)
    (TargetEmitterCursorControl.installMachine
      WorkSymbol.zeroZero)

def countRestoreVersionRef : NodeRef :=
  controlRef Address.countRestoreVersion
    (TargetEmitterCursorControl.restoreMachine
      WorkSymbol.zeroZero)

def countPassRewindRef : NodeRef :=
  controlRef Address.countPassRewind
    CNFToNANDCarrierTokenReader.Rewind.machine

def emitRewindRef : NodeRef :=
  controlRef Address.emitRewind
    CNFToNANDCarrierTokenReader.Rewind.machine

def emitInstallVersionRef : NodeRef :=
  controlRef Address.emitInstallVersion
    (TargetEmitterCursorControl.installMachine
      WorkSymbol.zeroZero)

def clauseCompareFirstRef : NodeRef :=
  controlRef Address.clauseCompareFirst
    (TargetEmitterScratchCompareSlot.machineFor .currentGate)

def clauseCompareLoopRef : NodeRef :=
  controlRef Address.clauseCompareLoop
    (TargetEmitterScratchCompareSlot.machineFor .currentGate)

def formulaCompareMarkerFirstRef : NodeRef :=
  controlRef Address.formulaCompareMarkerFirst
    (TargetEmitterScratchCompareSlot.machineFor .carrierWidth)

def formulaCompareFalseFirstRef : NodeRef :=
  controlRef Address.formulaCompareFalseFirst
    (TargetEmitterScratchCompareSlot.machineFor .currentGate)

def formulaCompareMarkerLoopRef : NodeRef :=
  controlRef Address.formulaCompareMarkerLoop
    (TargetEmitterScratchCompareSlot.machineFor .carrierWidth)

def formulaCompareFalseLoopRef : NodeRef :=
  controlRef Address.formulaCompareFalseLoop
    (TargetEmitterScratchCompareSlot.machineFor .currentGate)

def finalizerRef : NodeRef :=
  controlRef Address.finalizer
    TargetEmitterCursorFinalizer.machine

/-! ## Closed block entries -/

open PNP.Concrete.CNFToNANDControllerBlocks

def resetWorkspaceRef : NodeRef :=
  blockEntry Block.resetWorkspace resetLiteralIndexProgram

def countWidthRef : NodeRef :=
  blockEntry Block.countWidth countWidthUnitProgram

def countClauseRef : NodeRef :=
  blockEntry Block.countClause countClauseProgram

def countEmptyFormulaRef : NodeRef :=
  blockEntry Block.countEmptyFormula countEmptyFormulaProgram

def countNegativeSignRef : NodeRef :=
  blockEntry Block.countNegativeSign Blocks.countNegativeSignProgram

def countPositiveSignRef : NodeRef :=
  blockEntry Block.countPositiveSign Blocks.countPositiveSignProgram

def countValidNegativeRef : NodeRef :=
  blockEntry Block.countValidNegative countValidNegativeProgram

def countAdvancePositiveRef : NodeRef :=
  blockEntry Block.countAdvancePositive advanceLiteralIndexProgram

def countAdvanceNegativeRef : NodeRef :=
  blockEntry Block.countAdvanceNegative advanceLiteralIndexProgram

def emitInitializeClauseRef : NodeRef :=
  blockEntry Block.emitInitializeClause initializeClauseStackProgram

def emitNegativeSignRef : NodeRef :=
  blockEntry Block.emitNegativeSign Blocks.emitNegativeSignProgram

def emitPositiveSignRef : NodeRef :=
  blockEntry Block.emitPositiveSign Blocks.emitPositiveSignProgram

def emitPositiveLiteralRef : NodeRef :=
  blockEntry Block.emitPositiveLiteral emitPositiveLiteralProgram

def emitNegativeLiteralRef : NodeRef :=
  blockEntry Block.emitNegativeLiteral emitNegativeLiteralProgram

def emitInvalidLiteralRef : NodeRef :=
  blockEntry Block.emitInvalidLiteral emitInvalidLiteralProgram

def emitAdvancePositiveRef : NodeRef :=
  blockEntry Block.emitAdvancePositive advanceLiteralIndexProgram

def emitAdvanceNegativeRef : NodeRef :=
  blockEntry Block.emitAdvanceNegative advanceLiteralIndexProgram

def emittedHeaderRef : NodeRef :=
  blockEntry Block.emitHeader emitCircuitHeaderProgram

def initializeFormulaRef : NodeRef :=
  blockEntry Block.initializeFormula initializeFormulaStackProgram

def clausePopFirstRef : NodeRef :=
  blockEntry Block.clausePopFirst Blocks.popCoordinateProgram

def clauseSeedRef : NodeRef :=
  blockEntry Block.clauseSeed seedClauseProgram

def clausePopLoopRef : NodeRef :=
  blockEntry Block.clausePopLoop Blocks.popCoordinateProgram

def clauseExtendRef : NodeRef :=
  blockEntry Block.clauseExtend extendClauseProgram

def clauseFinishNonemptyRef : NodeRef :=
  blockEntry Block.clauseFinishNonempty finishNonemptyClauseProgram

def clauseFinishEmptyRef : NodeRef :=
  blockEntry Block.clauseFinishEmpty finishEmptyClauseProgram

def formulaPopFirstRef : NodeRef :=
  blockEntry Block.formulaPopFirst Blocks.popCoordinateProgram

def formulaSeedFalseRef : NodeRef :=
  blockEntry Block.formulaSeedFalse
    (seedFormulaProgram .constantFalse)

def formulaSeedGateRef : NodeRef :=
  blockEntry Block.formulaSeedGate
    (seedFormulaProgram .gateScratch)

def formulaPopLoopRef : NodeRef :=
  blockEntry Block.formulaPopLoop Blocks.popCoordinateProgram

def formulaExtendFalseRef : NodeRef :=
  blockEntry Block.formulaExtendFalse
    (extendFormulaProgram .constantFalse)

def formulaExtendGateRef : NodeRef :=
  blockEntry Block.formulaExtendGate
    (extendFormulaProgram .gateScratch)

def formulaEmptyRef : NodeRef :=
  blockEntry Block.formulaEmpty emitEmptyFormulaProgram

def suffixRef : NodeRef :=
  blockEntry Block.suffix emitCircuitSuffixProgram

/-! ## Literal grammar branch selection -/

def grammarActionEndpoint (pass : Pass)
    (state : GrammarState) (token : CNFToken) : Endpoint :=
  if validGrammarToken state token then
    .node (installRef pass state token)
  else
    .reject

def postInstallEndpoint : Pass → GrammarState → CNFToken → Endpoint
  | .count, .header, .f =>
      .node (restoreRef .count .clausesEmpty .f)
  | .count, .header, .t => .node countWidthRef
  | .count, .clausesEmpty, .sep => .node countClauseRef
  | .count, .clausesEmpty, .finish =>
      .node (restoreRef .count .finishedEmpty .finish)
  | .count, .clausesNonempty, .sep => .node countClauseRef
  | .count, .clausesNonempty, .finish =>
      .node (restoreRef .count .finishedNonempty .finish)
  | .count, .clause, .f => .node countNegativeSignRef
  | .count, .clause, .t => .node countPositiveSignRef
  | .count, .clause, .finish =>
      .node (restoreRef .count .clausesNonempty .finish)
  | .count, .positive, .f =>
      .node (literalCompareRef .count .positive .f)
  | .count, .positive, .t =>
      .node (literalCompareRef .count .positive .t)
  | .count, .positiveOverflow, .f =>
      .node (restoreRef .count .clause .f)
  | .count, .positiveOverflow, .t =>
      .node (restoreRef .count .positiveOverflow .t)
  | .count, .negative, .f =>
      .node (literalCompareRef .count .negative .f)
  | .count, .negative, .t =>
      .node (literalCompareRef .count .negative .t)
  | .count, .negativeOverflow, .f =>
      .node (restoreRef .count .clause .f)
  | .count, .negativeOverflow, .t =>
      .node (restoreRef .count .negativeOverflow .t)
  | .emit, .header, .f =>
      .node (restoreRef .emit .clausesEmpty .f)
  | .emit, .header, .t =>
      .node (restoreRef .emit .header .t)
  | .emit, .clausesEmpty, .sep => .node emitInitializeClauseRef
  | .emit, .clausesEmpty, .finish =>
      .node (restoreRef .emit .finishedEmpty .finish)
  | .emit, .clausesNonempty, .sep => .node emitInitializeClauseRef
  | .emit, .clausesNonempty, .finish =>
      .node (restoreRef .emit .finishedNonempty .finish)
  | .emit, .clause, .f => .node emitNegativeSignRef
  | .emit, .clause, .t => .node emitPositiveSignRef
  | .emit, .clause, .finish => .node clausePopFirstRef
  | .emit, .positive, .f =>
      .node (literalCompareRef .emit .positive .f)
  | .emit, .positive, .t =>
      .node (literalCompareRef .emit .positive .t)
  | .emit, .positiveOverflow, .f => .node emitInvalidLiteralRef
  | .emit, .positiveOverflow, .t =>
      .node (restoreRef .emit .positiveOverflow .t)
  | .emit, .negative, .f =>
      .node (literalCompareRef .emit .negative .f)
  | .emit, .negative, .t =>
      .node (literalCompareRef .emit .negative .t)
  | .emit, .negativeOverflow, .f => .node emitInvalidLiteralRef
  | .emit, .negativeOverflow, .t =>
      .node (restoreRef .emit .negativeOverflow .t)
  | _, _, _ => .reject

def recoveredToken (first second : Bool) : CNFToken :=
  CNFToken.ofBits first second

def advanceLiteralRef (pass : Pass)
    (positive : Bool) : NodeRef :=
  match pass, positive with
  | .count, true => countAdvancePositiveRef
  | .count, false => countAdvanceNegativeRef
  | .emit, true => emitAdvancePositiveRef
  | .emit, false => emitAdvanceNegativeRef

/-! ## Explicit control nodes -/

def scannerNode : Node :=
  controlNode Address.scanner
    TargetEmitterGrammarScanner.machine
    (.node ledgerRef) .reject

def ledgerNode : Node :=
  controlNode Address.ledger TargetEmitterLedger.machine
    (.node stackInitializeRef) .reject

def stackInitializeNode : Node :=
  controlNode Address.stackInitialize
    TargetEmitterCheckStack.Initialize.machine
    (.node resetWorkspaceRef) .reject

def workspaceZeroNode : Node :=
  controlNode Address.workspaceZero
    (TargetEmitterScratchCompareSlot.machineFor .inputCount)
    (.node validationHeaderRef) .reject

def validationHeaderNode : Node :=
  controlNode Address.validationHeader
    TargetEmitterNavigator.headerMachine
    (.node validationFirstRef) .reject

def validationFirstNode : Node :=
  controlNode Address.validationFirst
    TargetEmitterNavigator.sourceFirstMachine
    .reject (.node validationFirstNonInputRef)

def validationFirstNonInputNode : Node :=
  controlNode Address.validationFirstNonInput
    TargetEmitterNavigator.nonInputMachine
    .reject (.node validationFirstConstantRef)

def validationFirstConstantNode : Node :=
  controlNode Address.validationFirstConstant
    TargetEmitterNavigator.constantMachine
    (.node validationFirstReaderRef)
    (.node validationFirstReaderRef)

def validationFirstReaderNode : Node :=
  controlNode Address.validationFirstReader
    CNFToNANDCarrierTokenReader.firstSourceMachine
    (.node validationSecondRef) (.node validationSecondRef)

def validationSecondNode : Node :=
  controlNode Address.validationSecond
    TargetEmitterNavigator.sourceFirstMachine
    .reject (.node validationSecondNonInputRef)

def validationSecondNonInputNode : Node :=
  controlNode Address.validationSecondNonInput
    TargetEmitterNavigator.nonInputMachine
    .reject (.node validationSecondConstantRef)

def validationSecondConstantNode : Node :=
  controlNode Address.validationSecondConstant
    TargetEmitterNavigator.constantMachine
    (.node validationSecondReaderRef)
    (.node validationSecondReaderRef)

def validationSecondReaderNode : Node :=
  controlNode Address.validationSecondReader
    CNFToNANDCarrierTokenReader.firstSourceMachine
    (.node validationAdvanceRef) (.node validationAdvanceRef)

def validationAdvanceNode : Node :=
  controlNode Address.validationAdvance
    TargetEmitterNavigator.gateAdvanceMachine
    (.node validationFirstRef) (.node validationProgramEndRef)

def validationProgramEndNode : Node :=
  controlNode Address.validationProgramEnd
    TargetEmitterNavigator.programEndMachine
    (.node validationOutputFirstRef) .reject

def validationOutputFirstNode : Node :=
  controlNode Address.validationOutputFirst
    TargetEmitterNavigator.sourceFirstMachine
    .reject (.node validationOutputNonInputRef)

def validationOutputNonInputNode : Node :=
  controlNode Address.validationOutputNonInput
    TargetEmitterNavigator.nonInputMachine
    .reject (.node validationOutputRef)

/-- The carrier output must be the literal false constant. -/
def validationOutputNode : Node :=
  controlNode Address.validationOutput
    TargetEmitterNavigator.constantMachine
    (.node validationRewindRef) .reject

def validationRewindNode : Node :=
  controlNode Address.validationRewind
    CNFToNANDCarrierTokenReader.Rewind.machine
    (.node (passHeaderRef .count)) .reject

def passHeaderNode (pass : Pass) : Node :=
  controlNode
    (match pass with
      | .count => Address.countHeader
      | .emit => Address.emitHeader)
    TargetEmitterNavigator.headerMachine
    (.node (firstBitRef pass .header)) .reject

def firstBitNode (pass : Pass)
    (state : GrammarState) : Node :=
  controlNode (Address.firstBit pass state)
    CNFToNANDCarrierTokenReader.firstSourceMachine
    (.node (secondBitRef pass state false))
    (.node (secondBitRef pass state true))

def secondBitNode (pass : Pass) (state : GrammarState)
    (first : Bool) : Node :=
  controlNode (Address.secondBit pass state first)
    CNFToNANDCarrierTokenReader.secondSourceMachine
    (grammarActionEndpoint pass state
      (recoveredToken first false))
    (grammarActionEndpoint pass state
      (recoveredToken first true))

def installNode (pass : Pass) (state : GrammarState)
    (token : CNFToken) : Node :=
  controlNode (Address.install pass state token)
    (TargetEmitterCursorControl.installMachine
      (tokenSecondCell token))
    (postInstallEndpoint pass state token) .reject

def signCompareNode (pass : Pass)
    (positive : Bool) : Node :=
  let token : CNFToken := if positive then .t else .f
  controlNode (Address.literalCompare pass .clause token)
    (TargetEmitterScratchCompareSlot.machineFor .inputCount)
    (.node (restoreRef pass (overflowState positive) token))
    (.node (restoreRef pass (inRangeState positive) token))

def literalUnitCompareNode (pass : Pass)
    (positive : Bool) : Node :=
  let state := inRangeState positive
  controlNode (Address.literalCompare pass state .t)
    (TargetEmitterScratchCompareSlot.machineFor .inputCount)
    (.node (restoreRef pass (overflowState positive) .t))
    (.node (advanceLiteralRef pass positive))

/--
The unary loop detects strict overflow before incrementing.  Its terminator
therefore performs one final equality test: `index = width` is invalid,
whereas the reject branch is the proved `index < width` case.
-/
def literalTerminatorCompareNode (pass : Pass)
    (positive : Bool) : Node :=
  let state := inRangeState positive
  let invalid :=
    match pass with
    | .count => .node (restoreRef .count .clause .f)
    | .emit => .node emitInvalidLiteralRef
  let valid :=
    match pass, positive with
    | .count, true => .node (restoreRef .count .clause .f)
    | .count, false => .node countValidNegativeRef
    | .emit, true => .node emitPositiveLiteralRef
    | .emit, false => .node emitNegativeLiteralRef
  controlNode (Address.literalCompare pass state .f)
    (TargetEmitterScratchCompareSlot.machineFor .inputCount)
    invalid valid

def restoreNode (pass : Pass) (state : GrammarState)
    (token : CNFToken) : Node :=
  controlNode (Address.restore pass state token)
    (TargetEmitterCursorControl.restoreMachine
      (tokenSecondCell token))
    (.node (gateAdvanceRef pass state)) .reject

def gateAdvanceNode (pass : Pass)
    (state : GrammarState) : Node :=
  match stateFinishKind? state with
  | some kind =>
      controlNode (Address.gateAdvance pass state)
        TargetEmitterNavigator.gateAdvanceMachine
        .reject (.node (programEndRef pass kind))
  | none =>
      controlNode (Address.gateAdvance pass state)
        TargetEmitterNavigator.gateAdvanceMachine
        (.node (firstBitRef pass state)) .reject

def programEndNode (pass : Pass)
    (kind : FinishKind) : Node :=
  controlNode (Address.programEnd pass kind)
    TargetEmitterNavigator.programEndMachine
    (match pass with
      | .count => .node (countRewindRef kind)
      | .emit => .node emitRewindRef)
    .reject

def countRewindNode (kind : FinishKind) : Node :=
  controlNode (Address.countRewind kind)
    CNFToNANDCarrierTokenReader.Rewind.machine
    (.node (countInstallVersionRef kind)) .reject

def countInstallVersionNode (kind : FinishKind) : Node :=
  controlNode (Address.countInstallVersion kind)
    (TargetEmitterCursorControl.installMachine
      WorkSymbol.zeroZero)
    (match kind with
      | .empty => .node countEmptyFormulaRef
      | .nonempty => .node emittedHeaderRef)
    .reject

def countRestoreVersionNode : Node :=
  controlNode Address.countRestoreVersion
    (TargetEmitterCursorControl.restoreMachine
      WorkSymbol.zeroZero)
    (.node countPassRewindRef) .reject

def countPassRewindNode : Node :=
  controlNode Address.countPassRewind
    CNFToNANDCarrierTokenReader.Rewind.machine
    (.node (passHeaderRef .emit)) .reject

def emitRewindNode : Node :=
  controlNode Address.emitRewind
    CNFToNANDCarrierTokenReader.Rewind.machine
    (.node emitInstallVersionRef) .reject

def emitInstallVersionNode : Node :=
  controlNode Address.emitInstallVersion
    (TargetEmitterCursorControl.installMachine
      WorkSymbol.zeroZero)
    (.node formulaPopFirstRef) .reject

def clauseCompareFirstNode : Node :=
  controlNode Address.clauseCompareFirst
    (TargetEmitterScratchCompareSlot.machineFor .currentGate)
    (.node clauseFinishEmptyRef) (.node clauseSeedRef)

def clauseCompareLoopNode : Node :=
  controlNode Address.clauseCompareLoop
    (TargetEmitterScratchCompareSlot.machineFor .currentGate)
    (.node clauseFinishNonemptyRef) (.node clauseExtendRef)

def formulaCompareMarkerFirstNode : Node :=
  controlNode Address.formulaCompareMarkerFirst
    (TargetEmitterScratchCompareSlot.machineFor .carrierWidth)
    (.node formulaEmptyRef) (.node formulaCompareFalseFirstRef)

def formulaCompareFalseFirstNode : Node :=
  controlNode Address.formulaCompareFalseFirst
    (TargetEmitterScratchCompareSlot.machineFor .currentGate)
    (.node formulaSeedFalseRef) (.node formulaSeedGateRef)

def formulaCompareMarkerLoopNode : Node :=
  controlNode Address.formulaCompareMarkerLoop
    (TargetEmitterScratchCompareSlot.machineFor .carrierWidth)
    (.node suffixRef) (.node formulaCompareFalseLoopRef)

def formulaCompareFalseLoopNode : Node :=
  controlNode Address.formulaCompareFalseLoop
    (TargetEmitterScratchCompareSlot.machineFor .currentGate)
    (.node formulaExtendFalseRef) (.node formulaExtendGateRef)

def finalizerNode : Node :=
  controlNode Address.finalizer
    TargetEmitterCursorFinalizer.machine
    .accept .reject

/-! ## Local structural certificates -/

private theorem nodeWellFormed_of_interfaces
    (code : Nat) (program : WorkMachine)
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
    (controlNode code program onAccept onReject).WellFormed := by
  exact
    ⟨pairwise,
      noRuleAt_of_findWorkRule_none
        program program.acceptState noAccept,
      noRuleAt_of_findWorkRule_none
        program program.rejectState noReject,
      acceptNeReject⟩

structure ControlDescriptor where
  code : Nat
  program : WorkMachine
  onAccept : Endpoint
  onReject : Endpoint
  wellFormed :
    (controlNode code program onAccept onReject).WellFormed

def ControlDescriptor.materialize
    (descriptor : ControlDescriptor) : Node :=
  controlNode descriptor.code descriptor.program
    descriptor.onAccept descriptor.onReject

private def scannerDescriptor : ControlDescriptor :=
  { code := Address.scanner
    program := TargetEmitterGrammarScanner.machine
    onAccept := .node ledgerRef
    onReject := .reject
    wellFormed := by
      apply nodeWellFormed_of_interfaces
      · change TargetEmitterGrammarScanner.rules.Pairwise
          TargetEmitterGrammarScanner.QueryDistinct
        exact
          TargetEmitterGrammarScanner.rules_pairwise_query_distinct
      · exact TargetEmitterGrammarScanner.no_rule_at_accept
      · exact TargetEmitterGrammarScanner.no_rule_at_reject
      · exact
          TargetEmitterGrammarScanner.machine_acceptState_ne_rejectState }

private def ledgerDescriptor : ControlDescriptor :=
  { code := Address.ledger
    program := TargetEmitterLedger.machine
    onAccept := .node stackInitializeRef
    onReject := .reject
    wellFormed := by
      apply nodeWellFormed_of_interfaces
      · change TargetEmitterLedger.rules.Pairwise
          TargetEmitterLedger.QueryDistinct
        exact TargetEmitterLedger.rules_pairwise_query_distinct
      · exact TargetEmitterLedger.no_rule_at_accept
      · exact TargetEmitterLedger.no_rule_at_reject
      · exact TargetEmitterLedger.machine_accept_ne_reject }

private def navigatorDescriptor
    (code start : Nat) (onAccept onReject : Endpoint) :
    ControlDescriptor :=
  { code := code
    program := TargetEmitterNavigator.machineFrom start
    onAccept := onAccept
    onReject := onReject
    wellFormed := by
      apply nodeWellFormed_of_interfaces
      · change TargetEmitterNavigator.rules.Pairwise
          TargetEmitterNavigator.QueryDistinct
        exact TargetEmitterNavigator.rules_pairwise
      · exact TargetEmitterNavigator.no_rule_at_accept
      · exact TargetEmitterNavigator.no_rule_at_reject
      · exact TargetEmitterNavigator.machineFrom_accept_ne_reject start }

private def readerDescriptor
    (code : Nat) (advance : Bool)
    (onAccept onReject : Endpoint) : ControlDescriptor :=
  { code := code
    program := CNFToNANDCarrierTokenReader.machine advance
    onAccept := onAccept
    onReject := onReject
    wellFormed := by
      apply nodeWellFormed_of_interfaces
      · change
          (CNFToNANDCarrierTokenReader.rules advance).Pairwise
            CNFToNANDCarrierTokenReader.QueryDistinct
        exact CNFToNANDCarrierTokenReader.rules_pairwise advance
      · exact CNFToNANDCarrierTokenReader.no_rule_at_accept advance
      · exact CNFToNANDCarrierTokenReader.no_rule_at_reject advance
      · exact CNFToNANDCarrierTokenReader.accept_ne_reject advance }

private def rewindDescriptor
    (code : Nat) (onAccept onReject : Endpoint) :
    ControlDescriptor :=
  { code := code
    program := CNFToNANDCarrierTokenReader.Rewind.machine
    onAccept := onAccept
    onReject := onReject
    wellFormed := by
      apply nodeWellFormed_of_interfaces
      · change CNFToNANDCarrierTokenReader.Rewind.rules.Pairwise
          CNFToNANDCarrierTokenReader.Rewind.QueryDistinct
        exact CNFToNANDCarrierTokenReader.Rewind.rules_pairwise
      · exact CNFToNANDCarrierTokenReader.Rewind.no_rule_at_accept
      · exact CNFToNANDCarrierTokenReader.Rewind.no_rule_at_reject
      · exact CNFToNANDCarrierTokenReader.Rewind.accept_ne_reject }

private def compareDescriptor
    (code : Nat) (slot : TargetEmitterLedger.Slot)
    (onAccept onReject : Endpoint) : ControlDescriptor :=
  { code := code
    program := TargetEmitterScratchCompareSlot.machineFor slot
    onAccept := onAccept
    onReject := onReject
    wellFormed := by
      apply nodeWellFormed_of_interfaces
      · change TargetEmitterScratchCompareSlot.rules.Pairwise
          TargetEmitterScratchCompareSlot.QueryDistinct
        exact TargetEmitterScratchCompareSlot.rules_pairwise
      · exact TargetEmitterScratchCompareSlot.no_rule_at_accept
      · exact TargetEmitterScratchCompareSlot.no_rule_at_reject
      · exact TargetEmitterScratchCompareSlot.accept_ne_reject slot }

private def installDescriptor
    (code : Nat) (original : WorkSymbol)
    (onAccept onReject : Endpoint) : ControlDescriptor :=
  { code := code
    program := TargetEmitterCursorControl.installMachine original
    onAccept := onAccept
    onReject := onReject
    wellFormed := by
      apply nodeWellFormed_of_interfaces
      · change (TargetEmitterCursorControl.rules original).Pairwise
          TargetEmitterCursorControl.QueryDistinct
        exact TargetEmitterCursorControl.rules_pairwise original
      · exact TargetEmitterCursorControl.no_rule_at_installed original
      · exact TargetEmitterCursorControl.no_rule_at_reject original
      · exact
          TargetEmitterCursorControl.install_accept_ne_reject original }

private def restoreDescriptor
    (code : Nat) (original : WorkSymbol)
    (onAccept onReject : Endpoint) : ControlDescriptor :=
  { code := code
    program := TargetEmitterCursorControl.restoreMachine original
    onAccept := onAccept
    onReject := onReject
    wellFormed := by
      apply nodeWellFormed_of_interfaces
      · change (TargetEmitterCursorControl.rules original).Pairwise
          TargetEmitterCursorControl.QueryDistinct
        exact TargetEmitterCursorControl.rules_pairwise original
      · exact TargetEmitterCursorControl.no_rule_at_restored original
      · exact TargetEmitterCursorControl.no_rule_at_reject original
      · exact
          TargetEmitterCursorControl.restore_accept_ne_reject original }

private def finalizerDescriptor : ControlDescriptor :=
  { code := Address.finalizer
    program := TargetEmitterCursorFinalizer.machine
    onAccept := .accept
    onReject := .reject
    wellFormed := by
      apply nodeWellFormed_of_interfaces
      · change TargetEmitterCursorFinalizer.rules.Pairwise
          (fun left right =>
            (left.sourceState, left.readSymbol) ≠
              (right.sourceState, right.readSymbol))
        exact TargetEmitterCursorFinalizer.rules_pairwise
      · exact TargetEmitterCursorFinalizer.no_rule_at_accept
      · exact TargetEmitterCursorFinalizer.no_rule_at_reject
      · exact TargetEmitterCursorFinalizer.accept_ne_reject }

def fixedPrefixDescriptors : List ControlDescriptor :=
  [ scannerDescriptor
  , ledgerDescriptor
  , { code := Address.stackInitialize
      program := TargetEmitterCheckStack.Initialize.machine
      onAccept := .node resetWorkspaceRef
      onReject := .reject
      wellFormed := by
        apply nodeWellFormed_of_interfaces
        · change TargetEmitterCheckStack.Initialize.rules.Pairwise
            TargetEmitterCheckStack.QueryDistinct
          exact TargetEmitterCheckStack.Initialize.rules_pairwise
        · exact TargetEmitterCheckStack.Initialize.no_rule_at_accept
        · exact TargetEmitterCheckStack.Initialize.no_rule_at_reject
        · exact TargetEmitterCheckStack.Initialize.accept_ne_reject }
  , compareDescriptor Address.workspaceZero .inputCount
      (.node validationHeaderRef) .reject
  , navigatorDescriptor Address.validationHeader
      TargetEmitterNavigator.State.headerStart
      (.node validationFirstRef) .reject
  , navigatorDescriptor Address.validationFirst
      TargetEmitterNavigator.State.sourceFirst
      .reject (.node validationFirstNonInputRef)
  , navigatorDescriptor Address.validationFirstNonInput
      TargetEmitterNavigator.State.nonInputFirst
      .reject (.node validationFirstConstantRef)
  , navigatorDescriptor Address.validationFirstConstant
      TargetEmitterNavigator.State.constantFirst
      (.node validationFirstReaderRef)
      (.node validationFirstReaderRef)
  , readerDescriptor Address.validationFirstReader true
      (.node validationSecondRef) (.node validationSecondRef)
  , navigatorDescriptor Address.validationSecond
      TargetEmitterNavigator.State.sourceFirst
      .reject (.node validationSecondNonInputRef)
  , navigatorDescriptor Address.validationSecondNonInput
      TargetEmitterNavigator.State.nonInputFirst
      .reject (.node validationSecondConstantRef)
  , navigatorDescriptor Address.validationSecondConstant
      TargetEmitterNavigator.State.constantFirst
      (.node validationSecondReaderRef)
      (.node validationSecondReaderRef)
  , readerDescriptor Address.validationSecondReader true
      (.node validationAdvanceRef) (.node validationAdvanceRef)
  , navigatorDescriptor Address.validationAdvance
      TargetEmitterNavigator.State.gateEndFirst
      (.node validationFirstRef) (.node validationProgramEndRef)
  , navigatorDescriptor Address.validationProgramEnd
      TargetEmitterNavigator.State.programFirst
      (.node validationOutputFirstRef) .reject
  , navigatorDescriptor Address.validationOutputFirst
      TargetEmitterNavigator.State.sourceFirst
      .reject (.node validationOutputNonInputRef)
  , navigatorDescriptor Address.validationOutputNonInput
      TargetEmitterNavigator.State.nonInputFirst
      .reject (.node validationOutputRef)
  , navigatorDescriptor Address.validationOutput
      TargetEmitterNavigator.State.constantFirst
      (.node validationRewindRef) .reject
  , rewindDescriptor Address.validationRewind
      (.node (passHeaderRef .count)) .reject
  , navigatorDescriptor Address.countHeader
      TargetEmitterNavigator.State.headerStart
      (.node (firstBitRef .count .header)) .reject
  , navigatorDescriptor Address.emitHeader
      TargetEmitterNavigator.State.headerStart
      (.node (firstBitRef .emit .header)) .reject
  ]

def grammarReaderDescriptors : List ControlDescriptor :=
  passes.flatMap fun pass =>
    activeGrammarStates.flatMap fun state =>
      [ readerDescriptor (Address.firstBit pass state) true
          (.node (secondBitRef pass state false))
          (.node (secondBitRef pass state true))
      , readerDescriptor (Address.secondBit pass state false) false
          (grammarActionEndpoint pass state
            (recoveredToken false false))
          (grammarActionEndpoint pass state
            (recoveredToken false true))
      , readerDescriptor (Address.secondBit pass state true) false
          (grammarActionEndpoint pass state
            (recoveredToken true false))
          (grammarActionEndpoint pass state
            (recoveredToken true true))
      ]

def installDescriptors : List ControlDescriptor :=
  passes.flatMap fun pass =>
    activeGrammarStates.flatMap fun state =>
      cnfTokens.map fun token =>
        installDescriptor (Address.install pass state token)
          (tokenSecondCell token)
          (postInstallEndpoint pass state token) .reject

def literalCompareDescriptors : List ControlDescriptor :=
  passes.flatMap fun pass =>
    bools.flatMap fun positive =>
      let sign : CNFToken := if positive then .t else .f
      let state := inRangeState positive
      [ compareDescriptor
          (Address.literalCompare pass .clause sign) .inputCount
          (.node (restoreRef pass (overflowState positive) sign))
          (.node (restoreRef pass state sign))
      , compareDescriptor
          (Address.literalCompare pass state .t) .inputCount
          (.node (restoreRef pass (overflowState positive) .t))
          (.node (advanceLiteralRef pass positive))
      , compareDescriptor
          (Address.literalCompare pass state .f) .inputCount
          (match pass with
            | .count => .node (restoreRef .count .clause .f)
            | .emit => .node emitInvalidLiteralRef)
          (match pass, positive with
            | .count, true =>
                .node (restoreRef .count .clause .f)
            | .count, false => .node countValidNegativeRef
            | .emit, true => .node emitPositiveLiteralRef
            | .emit, false => .node emitNegativeLiteralRef)
      ]

def restoreDescriptors : List ControlDescriptor :=
  passes.flatMap fun pass =>
    grammarStates.flatMap fun state =>
      cnfTokens.map fun token =>
        restoreDescriptor (Address.restore pass state token)
          (tokenSecondCell token)
          (.node (gateAdvanceRef pass state)) .reject

def gateAdvanceDescriptors : List ControlDescriptor :=
  passes.flatMap fun pass =>
    grammarStates.map fun state =>
      match stateFinishKind? state with
      | some kind =>
          navigatorDescriptor (Address.gateAdvance pass state)
            TargetEmitterNavigator.State.gateEndFirst
            .reject (.node (programEndRef pass kind))
      | none =>
          navigatorDescriptor (Address.gateAdvance pass state)
            TargetEmitterNavigator.State.gateEndFirst
            (.node (firstBitRef pass state)) .reject

def programEndDescriptors : List ControlDescriptor :=
  passes.flatMap fun pass =>
    finishKinds.map fun kind =>
      navigatorDescriptor (Address.programEnd pass kind)
        TargetEmitterNavigator.State.programFirst
        (match pass with
          | .count => .node (countRewindRef kind)
          | .emit => .node emitRewindRef)
        .reject

def fixedSuffixDescriptors : List ControlDescriptor :=
  [ rewindDescriptor (Address.countRewind .empty)
      (.node (countInstallVersionRef .empty)) .reject
  , rewindDescriptor (Address.countRewind .nonempty)
      (.node (countInstallVersionRef .nonempty)) .reject
  , installDescriptor (Address.countInstallVersion .empty)
      WorkSymbol.zeroZero (.node countEmptyFormulaRef) .reject
  , installDescriptor (Address.countInstallVersion .nonempty)
      WorkSymbol.zeroZero (.node emittedHeaderRef) .reject
  , restoreDescriptor Address.countRestoreVersion
      WorkSymbol.zeroZero (.node countPassRewindRef) .reject
  , rewindDescriptor Address.countPassRewind
      (.node (passHeaderRef .emit)) .reject
  , rewindDescriptor Address.emitRewind
      (.node emitInstallVersionRef) .reject
  , installDescriptor Address.emitInstallVersion
      WorkSymbol.zeroZero (.node formulaPopFirstRef) .reject
  , compareDescriptor Address.clauseCompareFirst .currentGate
      (.node clauseFinishEmptyRef) (.node clauseSeedRef)
  , compareDescriptor Address.clauseCompareLoop .currentGate
      (.node clauseFinishNonemptyRef) (.node clauseExtendRef)
  , compareDescriptor Address.formulaCompareMarkerFirst .carrierWidth
      (.node formulaEmptyRef) (.node formulaCompareFalseFirstRef)
  , compareDescriptor Address.formulaCompareFalseFirst .currentGate
      (.node formulaSeedFalseRef) (.node formulaSeedGateRef)
  , compareDescriptor Address.formulaCompareMarkerLoop .carrierWidth
      (.node suffixRef) (.node formulaCompareFalseLoopRef)
  , compareDescriptor Address.formulaCompareFalseLoop .currentGate
      (.node formulaExtendFalseRef) (.node formulaExtendGateRef)
  , finalizerDescriptor
  ]

def controlDescriptors : List ControlDescriptor :=
  fixedPrefixDescriptors ++
    grammarReaderDescriptors ++
    installDescriptors ++
    literalCompareDescriptors ++
    restoreDescriptors ++
    gateAdvanceDescriptors ++
    programEndDescriptors ++
    fixedSuffixDescriptors

def controlNodes : List Node :=
  controlDescriptors.map ControlDescriptor.materialize

/-! ## Closed compiled blocks -/

structure BlockDescriptor where
  code : Nat
  primitives : List Primitive
  continuation : Endpoint
  closed :
    PNP.Concrete.CNFToNANDEmitterPlan.MachineClosed primitives
  nonempty : primitives ≠ []

def BlockDescriptor.materialize
    (descriptor : BlockDescriptor) : List Node :=
  blockNodes descriptor.code descriptor.primitives
    descriptor.continuation

private theorem fixedProgram_closed
    (program : List Primitive)
    (compiled :
      ∃ machines,
        compileProgram program = some machines) :
    PNP.Concrete.CNFToNANDEmitterPlan.MachineClosed program :=
  compiled

def blockDescriptors : List BlockDescriptor :=
  [ { code := Block.resetWorkspace
      primitives := resetLiteralIndexProgram
      continuation := .node workspaceZeroRef
      closed := resetLiteralIndexProgram_closed
      nonempty := by decide }
  , { code := Block.countWidth
      primitives := countWidthUnitProgram
      continuation := .node (restoreRef .count .header .t)
      closed := countWidthUnitProgram_closed
      nonempty := by decide }
  , { code := Block.countClause
      primitives := countClauseProgram
      continuation := .node (restoreRef .count .clause .sep)
      closed := countClauseProgram_closed
      nonempty := by decide }
  , { code := Block.countEmptyFormula
      primitives := countEmptyFormulaProgram
      continuation := .node emittedHeaderRef
      closed := countEmptyFormulaProgram_closed
      nonempty := by decide }
  , { code := Block.countNegativeSign
      primitives := Blocks.countNegativeSignProgram
      continuation :=
        .node (literalCompareRef .count .clause .f)
      closed := fixedProgram_closed _ ⟨_, rfl⟩
      nonempty := by decide }
  , { code := Block.countPositiveSign
      primitives := Blocks.countPositiveSignProgram
      continuation :=
        .node (literalCompareRef .count .clause .t)
      closed := fixedProgram_closed _ ⟨_, rfl⟩
      nonempty := by decide }
  , { code := Block.countValidNegative
      primitives := countValidNegativeProgram
      continuation := .node (restoreRef .count .clause .f)
      closed := countValidNegativeProgram_closed
      nonempty := by decide }
  , { code := Block.countAdvancePositive
      primitives := advanceLiteralIndexProgram
      continuation := .node (restoreRef .count .positive .t)
      closed := advanceLiteralIndexProgram_closed
      nonempty := by decide }
  , { code := Block.countAdvanceNegative
      primitives := advanceLiteralIndexProgram
      continuation := .node (restoreRef .count .negative .t)
      closed := advanceLiteralIndexProgram_closed
      nonempty := by decide }
  , { code := Block.emitInitializeClause
      primitives := initializeClauseStackProgram
      continuation := .node (restoreRef .emit .clause .sep)
      closed := initializeClauseStackProgram_closed
      nonempty := by decide }
  , { code := Block.emitNegativeSign
      primitives := Blocks.emitNegativeSignProgram
      continuation :=
        .node (literalCompareRef .emit .clause .f)
      closed := fixedProgram_closed _ ⟨_, rfl⟩
      nonempty := by decide }
  , { code := Block.emitPositiveSign
      primitives := Blocks.emitPositiveSignProgram
      continuation :=
        .node (literalCompareRef .emit .clause .t)
      closed := fixedProgram_closed _ ⟨_, rfl⟩
      nonempty := by decide }
  , { code := Block.emitPositiveLiteral
      primitives := emitPositiveLiteralProgram
      continuation := .node (restoreRef .emit .clause .f)
      closed := emitPositiveLiteralProgram_closed
      nonempty := by decide }
  , { code := Block.emitNegativeLiteral
      primitives := emitNegativeLiteralProgram
      continuation := .node (restoreRef .emit .clause .f)
      closed := emitNegativeLiteralProgram_closed
      nonempty := by decide }
  , { code := Block.emitInvalidLiteral
      primitives := emitInvalidLiteralProgram
      continuation := .node (restoreRef .emit .clause .f)
      closed := emitInvalidLiteralProgram_closed
      nonempty := by decide }
  , { code := Block.emitAdvancePositive
      primitives := advanceLiteralIndexProgram
      continuation := .node (restoreRef .emit .positive .t)
      closed := advanceLiteralIndexProgram_closed
      nonempty := by decide }
  , { code := Block.emitAdvanceNegative
      primitives := advanceLiteralIndexProgram
      continuation := .node (restoreRef .emit .negative .t)
      closed := advanceLiteralIndexProgram_closed
      nonempty := by decide }
  , { code := Block.emitHeader
      primitives := emitCircuitHeaderProgram
      continuation := .node initializeFormulaRef
      closed := emitCircuitHeaderProgram_closed
      nonempty := by decide }
  , { code := Block.initializeFormula
      primitives := initializeFormulaStackProgram
      continuation := .node countRestoreVersionRef
      closed := initializeFormulaStackProgram_closed
      nonempty := by decide }
  , { code := Block.clausePopFirst
      primitives := Blocks.popCoordinateProgram
      continuation := .node clauseCompareFirstRef
      closed :=
        PNP.Concrete.CNFToNANDEmitterPlan.popCoordinateProgram_closed
      nonempty := by decide }
  , { code := Block.clauseSeed
      primitives := seedClauseProgram
      continuation := .node clausePopLoopRef
      closed := seedClauseProgram_closed
      nonempty := by decide }
  , { code := Block.clausePopLoop
      primitives := Blocks.popCoordinateProgram
      continuation := .node clauseCompareLoopRef
      closed :=
        PNP.Concrete.CNFToNANDEmitterPlan.popCoordinateProgram_closed
      nonempty := by decide }
  , { code := Block.clauseExtend
      primitives := extendClauseProgram
      continuation := .node clausePopLoopRef
      closed := extendClauseProgram_closed
      nonempty := by decide }
  , { code := Block.clauseFinishNonempty
      primitives := finishNonemptyClauseProgram
      continuation :=
        .node (restoreRef .emit .clausesNonempty .finish)
      closed := finishNonemptyClauseProgram_closed
      nonempty := by decide }
  , { code := Block.clauseFinishEmpty
      primitives := finishEmptyClauseProgram
      continuation :=
        .node (restoreRef .emit .clausesNonempty .finish)
      closed := finishEmptyClauseProgram_closed
      nonempty := by decide }
  , { code := Block.formulaPopFirst
      primitives := Blocks.popCoordinateProgram
      continuation := .node formulaCompareMarkerFirstRef
      closed :=
        PNP.Concrete.CNFToNANDEmitterPlan.popCoordinateProgram_closed
      nonempty := by decide }
  , { code := Block.formulaSeedFalse
      primitives := seedFormulaProgram .constantFalse
      continuation := .node formulaPopLoopRef
      closed := seedFormulaProgram_closed .constantFalse
      nonempty := by decide }
  , { code := Block.formulaSeedGate
      primitives := seedFormulaProgram .gateScratch
      continuation := .node formulaPopLoopRef
      closed := seedFormulaProgram_closed .gateScratch
      nonempty := by decide }
  , { code := Block.formulaPopLoop
      primitives := Blocks.popCoordinateProgram
      continuation := .node formulaCompareMarkerLoopRef
      closed :=
        PNP.Concrete.CNFToNANDEmitterPlan.popCoordinateProgram_closed
      nonempty := by decide }
  , { code := Block.formulaExtendFalse
      primitives := extendFormulaProgram .constantFalse
      continuation := .node formulaPopLoopRef
      closed := extendFormulaProgram_closed .constantFalse
      nonempty := by decide }
  , { code := Block.formulaExtendGate
      primitives := extendFormulaProgram .gateScratch
      continuation := .node formulaPopLoopRef
      closed := extendFormulaProgram_closed .gateScratch
      nonempty := by decide }
  , { code := Block.formulaEmpty
      primitives := emitEmptyFormulaProgram
      continuation := .node suffixRef
      closed := emitEmptyFormulaProgram_closed
      nonempty := by decide }
  , { code := Block.suffix
      primitives := emitCircuitSuffixProgram
      continuation := .node finalizerRef
      closed := emitCircuitSuffixProgram_closed
      nonempty := by decide }
  ]

def allBlockNodes : List Node :=
  blockDescriptors.flatMap BlockDescriptor.materialize

def nodes : List Node :=
  controlNodes ++ allBlockNodes

/-! ## Structural closure of the fixed graph -/

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
      · intro right rightMember equality
        apply parts.1
        exact List.mem_map.mpr
          ⟨right, rightMember, equality.symm⟩
      · exact inductionHypothesis parts.2

private theorem controlNodes_wellFormed :
    ∀ node, node ∈ controlNodes → node.WellFormed := by
  intro node member
  rcases List.mem_map.mp member with
    ⟨descriptor, _descriptorMember, equality⟩
  rw [← equality]
  exact descriptor.wellFormed

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem controlNodeNames_nodup :
    (controlNodes.map (fun node => node.name)).Nodup := by
  decide

private theorem controlNodes_names_pairwise :
    controlNodes.Pairwise
      (fun left right => left.name ≠ right.name) :=
  nodeNames_pairwise_of_nodup
    controlNodes controlNodeNames_nodup

set_option maxRecDepth 1000000 in
private theorem blockDescriptorCodes_nodup :
    (blockDescriptors.map
      (fun descriptor => descriptor.code)).Nodup := by
  decide

private theorem descriptorNodes_names_pairwise
    (descriptors : List BlockDescriptor)
    (codesNodup :
      (descriptors.map
        (fun descriptor => descriptor.code)).Nodup) :
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

private theorem allBlockNodes_wellFormed :
    ∀ node, node ∈ allBlockNodes → node.WellFormed := by
  intro node member
  rcases List.mem_flatMap.mp member with
    ⟨descriptor, _descriptorMember, nodeMember⟩
  rcases descriptor.closed with ⟨programs, compiled⟩
  exact blockNodes_wellFormed_of_compiled
    descriptor.code descriptor.primitives programs
    descriptor.continuation compiled node nodeMember

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
    Endpoint.Resolves nodes (.node node.reference) :=
  ⟨node, member, rfl, rfl⟩

private theorem blockEntry_resolves
    (descriptor : BlockDescriptor)
    (descriptorMember : descriptor ∈ blockDescriptors) :
    Endpoint.Resolves nodes
      (.node (blockEntry descriptor.code
        descriptor.primitives)) := by
  rcases descriptor.closed with ⟨programs, compiled⟩
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
      exact (descriptor.nonempty primitiveEmpty).elim
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
      decide (first = target) ||
        referenceKnownIn rest target

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
set_option maxHeartbeats 0 in
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
set_option maxHeartbeats 0 in
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
  rcases List.mem_map.mp member with
    ⟨descriptor, _descriptorMember, equality⟩
  rw [← equality]
  exact controlNodeName_even descriptor.code

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

private theorem nodes_endpoints_resolve :
    ∀ node, node ∈ nodes →
      Endpoint.Resolves nodes node.onAccept ∧
        Endpoint.Resolves nodes node.onReject := by
  intro node member
  rcases List.mem_append.mp member with
    controlMember | blockMember
  · exact controlNode_endpoints_resolve node controlMember
  · exact blockNode_endpoints_resolve node blockMember

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem entry_resolves :
    Endpoint.Resolves nodes (.node scannerRef) := by
  apply endpoint_resolves_of_known
  decide

def graph : Graph :=
  { nodes := nodes
    entry := scannerRef }

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
        (fun node => 18 + node.program.rules.length)).sum :=
  WorkMachineProgramGraph.rules_length graph

/--
Literal rule count of the one fixed carrier controller.  This is the sum of
the two bridge rows and the embedded local rule table at every materialized
node; no source-dependent lookup contributes rules.
-/
def ruleCount : Nat := 121073

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
theorem rules_length_literal :
    machine.rules.length = ruleCount := by
  rw [rules_length]
  rfl

def nodeCount : Nat := 464

set_option maxRecDepth 1000000 in
theorem nodes_length_literal :
    nodes.length = nodeCount := by
  rfl

/-! ## Stable branch-boundary interfaces -/

theorem scanner_accepts_only_into_ledger :
    scannerNode.onAccept = .node ledgerRef := rfl

theorem ledger_accepts_only_into_stack_initializer :
    ledgerNode.onAccept = .node stackInitializeRef := rfl

theorem stack_initializer_accepts_only_into_workspace_reset :
    stackInitializeNode.onAccept = .node resetWorkspaceRef := rfl

theorem workspace_zero_accepts_validation :
    workspaceZeroNode.onAccept = .node validationHeaderRef := rfl

theorem validation_requires_a_gate :
    validationHeaderNode.onReject = .reject := rfl

theorem validation_first_input_rejects :
    validationFirstNode.onAccept = .reject := rfl

theorem validation_first_gate_rejects :
    validationFirstNonInputNode.onAccept = .reject := rfl

theorem validation_second_input_rejects :
    validationSecondNode.onAccept = .reject := rfl

theorem validation_second_gate_rejects :
    validationSecondNonInputNode.onAccept = .reject := rfl

theorem validation_output_input_rejects :
    validationOutputFirstNode.onAccept = .reject := rfl

theorem validation_output_gate_rejects :
    validationOutputNonInputNode.onAccept = .reject := rfl

theorem validation_output_true_rejects :
    validationOutputNode.onReject = .reject := rfl

theorem validation_output_false_rewinds :
    validationOutputNode.onAccept = .node validationRewindRef := rfl

theorem invalid_grammar_token_rejects
    (pass : Pass) (state : GrammarState) (token : CNFToken)
    (invalid : validGrammarToken state token = false) :
    grammarActionEndpoint pass state token = .reject := by
  simp [grammarActionEndpoint, invalid]

theorem finished_gate_rejects_extra_carrier_gate
    (pass : Pass) (kind : FinishKind) :
    (gateAdvanceNode pass
      (match kind with
        | .empty => .finishedEmpty
        | .nonempty => .finishedNonempty)).onAccept =
      .reject := by
  cases pass <;> cases kind <;> rfl

theorem suffix_is_literal_closed_block :
    ∃ machines,
      compileProgram emitCircuitSuffixProgram = some machines :=
  emitCircuitSuffixProgram_closed

end PNP.Concrete.CNFToNANDController

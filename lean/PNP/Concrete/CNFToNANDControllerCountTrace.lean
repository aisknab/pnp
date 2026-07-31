/-
Copyright (c) 2026 PNP Labs.

Exact first-pass traces for the fixed canonical CNF-to-NAND controller.

The executable graph is unchanged.  Formula structure appears only as a
proof index for the canonical retained carrier.  Every branch below is taken
by a literal reader, cursor, comparison, rewind, or closed emitter block
already materialized in `CNFToNANDController`; no decoded formula or
proof-side schedule is supplied to the machine.
-/

import PNP.Concrete.CNFToNANDControllerCanonicalTrace
import PNP.Concrete.CNFToNANDControllerPolynomialBound
import PNP.Concrete.LockedNANDTargetEmitterScratchCompareSlotExact
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramBound

namespace PNP.Concrete.CNFToNANDControllerCountTrace

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
open PNP.Concrete.CNFToNANDControllerCanonicalTrace
open PNP.Concrete.CNFToNANDControllerPolynomialBound

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

abbrev PrimitiveSafe :=
  PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgram.PrimitiveSafe

abbrev LedgerFits :=
  PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgram.LedgerFits

/-! ## Public count-to-emit handoff -/

/-- Exact strict-v0 target prefix emitted by the completed count pass. -/
def headerTokens (formula : CNFFormula) : List Token :=
  [.version0] ++
    encodeNatTokens formula.variableCount ++
    encodeNatTokens
      (CNFToNANDWorkspace.compilerGateCount formula)

/-- Exact runtime presented to the second, emitting traversal. -/
def emitInitialRuntime (formula : CNFFormula) : Runtime :=
  { captured := 0
    scratch := 0
    registers := CNFToNANDWorkspace.workspaceRegisters formula
    checks := [CNFToNANDWorkspace.formulaStackMarker formula]
    targetTokens := headerTokens formula }

@[simp] theorem emitInitialRuntime_scratch (formula : CNFFormula) :
    (emitInitialRuntime formula).scratch = 0 := by
  rfl

@[simp] theorem emitInitialRuntime_registers (formula : CNFFormula) :
    (emitInitialRuntime formula).registers =
      CNFToNANDWorkspace.workspaceRegisters formula := by
  rfl

@[simp] theorem emitInitialRuntime_checks (formula : CNFFormula) :
    (emitInitialRuntime formula).checks =
      [CNFToNANDWorkspace.formulaStackMarker formula] := by
  rfl

@[simp] theorem emitInitialRuntime_targetTokens (formula : CNFFormula) :
    (emitInitialRuntime formula).targetTokens =
      headerTokens formula := by
  rfl

/-! ## Physical scan representation -/

/-- A controller configuration whose head has crossed exactly `before` cells
of the retained source and is focused on `after`.  The list `before` is kept
in source order; its reversal is the physical left stack. -/
def ScanRepresents (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (before after : List WorkSymbol)
    (target : List Token) (tape : WorkTape) : Prop :=
  WorkConfiguration.BlankEquivalent
    { state := state, tape := tape }
    (TargetEmitter.configAtWord state
      (before.reverse ++
        TargetEmitterRuntime.logicalLeftWorkspace
          capacity scratch registers checks)
      (after ++
        TargetEmitter.sourceTargetBoundary ::
          SourceParser.packedTokenCells target))

theorem scanRepresents_nil_iff_tapeRepresents
    (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (tape : WorkTape) :
    ScanRepresents state capacity scratch registers checks
        [] source target tape ↔
      TapeRepresents state capacity scratch registers checks
        source target tape := by
  simp [ScanRepresents, TapeRepresents,
    TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalWord]

/-! ## Counted register arithmetic -/

/-- The two fields physically populated by the first pass, with every
source-derived ledger field retained verbatim. -/
def countedRegisters (formula : CNFFormula)
    (width gateCount : Nat) : TargetEmitter.UnaryRegisters :=
  { CNFToNANDWorkspace.postLedgerRegisters formula with
    inputCount := width
    currentGate := gateCount
    outputIndex := 0 }

@[simp] theorem countedRegisters_inputCount
    (formula : CNFFormula) (width gateCount : Nat) :
    (countedRegisters formula width gateCount).inputCount = width := by
  rfl

@[simp] theorem countedRegisters_currentGate
    (formula : CNFFormula) (width gateCount : Nat) :
    (countedRegisters formula width gateCount).currentGate = gateCount := by
  rfl

@[simp] theorem countedRegisters_outputIndex
    (formula : CNFFormula) (width gateCount : Nat) :
    (countedRegisters formula width gateCount).outputIndex = 0 := by
  rfl

theorem countedRegisters_zero (formula : CNFFormula) :
    countedRegisters formula 0 0 =
      CNFToNANDWorkspace.postLedgerRegisters formula := by
  rfl

theorem countedRegisters_final (formula : CNFFormula) :
    countedRegisters formula formula.variableCount
        (CNFToNANDWorkspace.compilerGateCount formula) =
      CNFToNANDWorkspace.workspaceRegisters formula := by
  rfl

/-- Gate charge contributed by one literal during the count traversal. -/
def literalGateCharge (width : Nat) (literal : CNFLiteral) : Nat :=
  3 +
    if !literal.positive && literal.variableIndex < width
    then 1 else 0

/-- Gate charge contributed by one clause, including its separator. -/
def clauseGateCharge (width : Nat)
    (clause : List CNFLiteral) : Nat :=
  2 + (clause.map (literalGateCharge width)).sum

/-- Nonempty-formula charge accumulated before the optional empty-formula
normalization gate. -/
def clausesGateCharge (width : Nat) :
    List (List CNFLiteral) → Nat
  | [] => 0
  | clause :: rest =>
      clauseGateCharge width clause + clausesGateCharge width rest

theorem literalGateCharge_eq
    (width : Nat) (literal : CNFLiteral) :
    literalGateCharge width literal =
      3 +
        (if !literal.positive &&
            literal.variableIndex < width then 1 else 0) := by
  rfl

private theorem literalGateCharge_sum_eq
    (width : Nat) (clause : List CNFLiteral) :
    (clause.map (literalGateCharge width)).sum =
      3 * clause.length +
        (clause.filter fun literal =>
          !literal.positive &&
            literal.variableIndex < width).length := by
  induction clause with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons,
        List.length_cons, List.filter_cons]
      rw [inductionHypothesis]
      by_cases condition :
          !literal.positive &&
            literal.variableIndex < width
      · simp [literalGateCharge, condition]
        omega
      · simp [literalGateCharge, condition]
        omega

theorem clauseGateCharge_eq
    (width : Nat) (clause : List CNFLiteral) :
    clauseGateCharge width clause =
      3 * clause.length +
      (clause.filter fun literal =>
          !literal.positive &&
            literal.variableIndex < width).length + 2 := by
  rw [clauseGateCharge, literalGateCharge_sum_eq]
  omega

theorem clausesGateCharge_eq
    (width : Nat) (clauses : List (List CNFLiteral)) :
    clausesGateCharge width clauses =
      (clauses.map fun clause =>
        (clause.filter fun literal =>
          !literal.positive &&
            literal.variableIndex < width).length).sum +
        3 * (clauses.map List.length).sum +
        2 * clauses.length := by
  induction clauses with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      rw [clausesGateCharge, clauseGateCharge_eq,
        inductionHypothesis]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem compilerGateCount_eq_count_charge
    (formula : CNFFormula) :
    CNFToNANDWorkspace.compilerGateCount formula =
      clausesGateCharge formula.variableCount formula.clauses +
        (if formula.clauses.isEmpty then 1 else 0) := by
  unfold CNFToNANDWorkspace.compilerGateCount
  rw [CNFToNAND.compileFormula_gateCount_exact,
    clausesGateCharge_eq]
  simp [CNFToNAND.validNegativeLiteralCount,
    CNFToNAND.literalCount]

theorem countedRegisters_fits
    (formula : CNFFormula) (width gateCount : Nat)
    (widthBound : width ≤ formula.variableCount)
    (gateBound :
      gateCount ≤ CNFToNANDWorkspace.compilerGateCount formula) :
    LedgerFits (CNFToNANDWorkspace.capacity formula)
      (countedRegisters formula width gateCount) := by
  have ledger := postLedgerFits formula
  refine
    { inputCount := Nat.le_trans widthBound
        (CNFToNANDWorkspace.variableCount_le_capacity formula)
      normalizedGateCount := ?_
      carrierWidth := ?_
      baseline := ?_
      currentGate := ?_
      outputIndex := ?_ }
  · exact ledger.normalizedGateCount
  · exact ledger.carrierWidth
  · exact ledger.baseline
  · exact Nat.le_trans gateBound
      (Nat.le_of_lt
        (CNFToNANDWorkspace.compilerGateCount_lt_capacity formula))
  · simp [countedRegisters]

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

private theorem indexedControlNode_member
    (node : Node) (index : Nat)
    (bound : index < controlNodes.length)
    (selected : controlNodes[index] = node) :
    node ∈ graph.nodes := by
  apply controlNode_member_nodes node
  rw [← selected]
  exact List.getElem_mem bound

/-! The fixed controller's useful local nodes, exposed once so the emitting
pass need not replay descriptor-membership reduction. -/

theorem passHeaderNode_member (pass : Pass) :
    passHeaderNode pass ∈ graph.nodes := by
  let index := 19 + pass.code
  have bound : index < controlNodes.length := by
    cases pass <;> decide
  refine indexedControlNode_member (passHeaderNode pass) index
    bound ?_
  cases pass <;> rfl

theorem firstBitNode_member (pass : Pass)
    (state : GrammarState)
    (active : state ∈ activeGrammarStates) :
    firstBitNode pass state ∈ graph.nodes := by
  let index := 21 + 24 * pass.code + 3 * state.code
  have bound : index < controlNodes.length := by
    cases pass <;> cases state <;> decide
  refine indexedControlNode_member (firstBitNode pass state) index
    bound ?_
  cases pass <;> cases state <;>
    simp [activeGrammarStates] at active <;> rfl

theorem secondBitNode_member (pass : Pass)
    (state : GrammarState) (first : Bool)
    (active : state ∈ activeGrammarStates) :
    secondBitNode pass state first ∈ graph.nodes := by
  let index :=
    21 + 24 * pass.code + 3 * state.code +
      (if first then 2 else 1)
  have bound : index < controlNodes.length := by
    cases pass <;> cases state <;> cases first <;> decide
  refine indexedControlNode_member
    (secondBitNode pass state first) index bound ?_
  cases pass <;> cases state <;> cases first <;>
    simp [activeGrammarStates] at active <;> rfl

theorem installNode_member (pass : Pass)
    (state : GrammarState) (token : CNFToken)
    (active : state ∈ activeGrammarStates) :
    installNode pass state token ∈ graph.nodes := by
  let index :=
    69 + 32 * pass.code + 4 * state.code + tokenCode token
  have bound : index < controlNodes.length := by
    cases pass <;> cases state <;> cases token <;> decide
  refine indexedControlNode_member
    (installNode pass state token) index bound ?_
  cases pass <;> cases state <;> cases token <;>
    simp [activeGrammarStates] at active <;> rfl

theorem signCompareNode_member (pass : Pass)
    (positive : Bool) :
    signCompareNode pass positive ∈ graph.nodes := by
  let index :=
    133 + 6 * pass.code + 3 * (if positive then 1 else 0)
  have bound : index < controlNodes.length := by
    cases pass <;> cases positive <;> decide
  refine indexedControlNode_member
    (signCompareNode pass positive) index bound ?_
  cases pass <;> cases positive <;> rfl

theorem literalUnitCompareNode_member (pass : Pass)
    (positive : Bool) :
    literalUnitCompareNode pass positive ∈ graph.nodes := by
  let index :=
    134 + 6 * pass.code + 3 * (if positive then 1 else 0)
  have bound : index < controlNodes.length := by
    cases pass <;> cases positive <;> decide
  refine indexedControlNode_member
    (literalUnitCompareNode pass positive) index bound ?_
  cases pass <;> cases positive <;> rfl

theorem literalTerminatorCompareNode_member (pass : Pass)
    (positive : Bool) :
    literalTerminatorCompareNode pass positive ∈ graph.nodes := by
  let index :=
    135 + 6 * pass.code + 3 * (if positive then 1 else 0)
  have bound : index < controlNodes.length := by
    cases pass <;> cases positive <;> decide
  refine indexedControlNode_member
    (literalTerminatorCompareNode pass positive) index bound ?_
  cases pass <;> cases positive <;> rfl

theorem restoreNode_member (pass : Pass)
    (state : GrammarState) (token : CNFToken) :
    restoreNode pass state token ∈ graph.nodes := by
  let index :=
    145 + 40 * pass.code + 4 * state.code + tokenCode token
  have bound : index < controlNodes.length := by
    cases pass <;> cases state <;> cases token <;> decide
  refine indexedControlNode_member
    (restoreNode pass state token) index bound ?_
  cases pass <;> cases state <;> cases token <;> rfl

theorem gateAdvanceNode_member (pass : Pass)
    (state : GrammarState) :
    gateAdvanceNode pass state ∈ graph.nodes := by
  let index := 225 + 10 * pass.code + state.code
  have bound : index < controlNodes.length := by
    cases pass <;> cases state <;> decide
  refine indexedControlNode_member
    (gateAdvanceNode pass state) index bound ?_
  cases pass <;> cases state <;> rfl

theorem programEndNode_member (pass : Pass)
    (kind : FinishKind) :
    programEndNode pass kind ∈ graph.nodes := by
  let index := 245 + 2 * pass.code + kind.code
  have bound : index < controlNodes.length := by
    cases pass <;> cases kind <;> decide
  refine indexedControlNode_member
    (programEndNode pass kind) index bound ?_
  cases pass <;> cases kind <;> rfl

theorem countRewindNode_member (kind : FinishKind) :
    countRewindNode kind ∈ graph.nodes := by
  let index := 249 + kind.code
  have bound : index < controlNodes.length := by
    cases kind <;> decide
  refine indexedControlNode_member
    (countRewindNode kind) index bound ?_
  cases kind <;> rfl

theorem countInstallVersionNode_member (kind : FinishKind) :
    countInstallVersionNode kind ∈ graph.nodes := by
  let index := 251 + kind.code
  have bound : index < controlNodes.length := by
    cases kind <;> decide
  refine indexedControlNode_member
    (countInstallVersionNode kind) index bound ?_
  cases kind <;> rfl

theorem countRestoreVersionNode_member :
    countRestoreVersionNode ∈ graph.nodes := by
  refine indexedControlNode_member countRestoreVersionNode 253
    (by decide) ?_
  rfl

theorem countPassRewindNode_member :
    countPassRewindNode ∈ graph.nodes := by
  refine indexedControlNode_member countPassRewindNode 254
    (by decide) ?_
  rfl

theorem finalizerNode_member :
    finalizerNode ∈ graph.nodes := by
  refine indexedControlNode_member finalizerNode 263
    (by decide) ?_
  rfl

private theorem localAccept_path
    (code : Nat) (program : WorkMachine)
    (onAccept onReject finalEndpoint : Endpoint)
    (localSteps tailSteps : Nat)
    (initialTape middleTape finalTape : WorkTape)
    (member :
      controlNode code program onAccept onReject ∈ graph.nodes)
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
      finalTape member
      (by simpa [LocalAcceptRun, controlNode] using run) tail
  simpa [controlNode, controlRef, Node.reference] using path

private theorem localReject_path
    (code : Nat) (program : WorkMachine)
    (onAccept onReject finalEndpoint : Endpoint)
    (localSteps tailSteps : Nat)
    (initialTape middleTape finalTape : WorkTape)
    (member :
      controlNode code program onAccept onReject ∈ graph.nodes)
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
      finalTape member
      (by simpa [LocalRejectRun, controlNode] using run) tail
  simpa [controlNode, controlRef, Node.reference] using path

/-! ## Canonical retained-source views -/

def tokenBeforeCells (all processed : List CNFToken)
    (token : CNFToken) : List WorkSymbol :=
  carrierHeaderCells all ++ carrierGateCells processed ++
    [ SourceParser.cell01
    , constantSecondCell
        (CNFToNANDCarrierEncoder.Source.firstBit token)
    , SourceParser.cell01
    ]

def tokenAfterCells (rest : List CNFToken) :
    List WorkSymbol :=
  [SourceParser.cell01, SourceParser.cell11] ++
    carrierGateCells rest ++ carrierFooterCells

def scanBeforeCells (all processed : List CNFToken) :
    List WorkSymbol :=
  carrierHeaderCells all ++ carrierGateCells processed

def scanAfterCells (token : CNFToken)
    (rest : List CNFToken) : List WorkSymbol :=
  carrierGateCellsFor token ++
    carrierGateCells rest ++ carrierFooterCells

def markedSource (all processed : List CNFToken)
    (token : CNFToken) (rest : List CNFToken) :
    List WorkSymbol :=
  tokenBeforeCells all processed token ++
    TargetEmitterCursorAppender.cursorMarker ::
      tokenAfterCells rest

private theorem carrierGateCellsFor_explicit
    (token : CNFToken) :
    carrierGateCellsFor token =
      [ SourceParser.cell01
      , constantSecondCell
          (CNFToNANDCarrierEncoder.Source.firstBit token)
      , SourceParser.cell01
      , tokenSecondCell token
      , SourceParser.cell01
      , SourceParser.cell11
      ] := by
  cases token <;> rfl

private theorem carrierGateCells_append
    (left right : List CNFToken) :
    carrierGateCells (left ++ right) =
      carrierGateCells left ++ carrierGateCells right := by
  induction left with
  | nil =>
      rfl
  | cons token rest inductionHypothesis =>
      simp only [List.cons_append, carrierGateCells,
        inductionHypothesis, List.append_assoc]

private theorem canonicalSource_token_split
    (formula : CNFFormula)
    (processed : List CNFToken) (token : CNFToken)
    (rest : List CNFToken)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ token :: rest) :
    canonicalSource formula =
      tokenBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token ++
        tokenSecondCell token :: tokenAfterCells rest := by
  rw [canonicalSource_eq_carrier_layout, tokens]
  rw [carrierGateCells_append]
  simp [tokenBeforeCells, tokenAfterCells, carrierGateCells,
    carrierGateCellsFor_explicit, List.append_assoc]

private theorem canonicalSource_scan_split
    (formula : CNFFormula)
    (processed : List CNFToken) (token : CNFToken)
    (rest : List CNFToken)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ token :: rest) :
    canonicalSource formula =
      scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed ++
        scanAfterCells token rest := by
  rw [canonicalSource_eq_carrier_layout, tokens]
  rw [carrierGateCells_append]
  simp [scanBeforeCells, scanAfterCells, carrierGateCells,
    List.append_assoc]

private theorem canonicalSource_packed
    (formula : CNFFormula) :
    ∀ symbol, symbol ∈ canonicalSource formula →
      TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  exact
    TargetEmitter.circuitCells_packed
      (CNFToNANDWorkspace.carrierCircuit formula) symbol member

def markedSourceContext
    (formula : CNFFormula)
    (processed : List CNFToken) (token : CNFToken)
    (rest : List CNFToken)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ token :: rest) :
    SourceContext
      (markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        processed token rest) := by
  let before :=
    tokenBeforeCells
      (CNFToNANDWorkspace.formulaTokens formula) processed token
  let after := tokenAfterCells rest
  have sourceEq :=
    canonicalSource_token_split formula processed token rest tokens
  refine
    { head := SourceParser.cell00
      tail :=
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token rest).tail
      source_eq := ?_
      allowed := Or.inl TargetEmitter.PackedSymbol.zeroZero }
  simp [markedSource, tokenBeforeCells, carrierHeaderCells,
    before, after]

def markedCursorLayout
    (formula : CNFFormula)
    (processed : List CNFToken) (token : CNFToken)
    (rest : List CNFToken)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ token :: rest) :
    CursorLayout
      (markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        processed token rest) := by
  let before :=
    tokenBeforeCells
      (CNFToNANDWorkspace.formulaTokens formula) processed token
  let after := tokenAfterCells rest
  have sourceEq :=
    canonicalSource_token_split formula processed token rest tokens
  have packed := canonicalSource_packed formula
  refine
    { cursorBefore := before
      cursorOriginal := tokenSecondCell token
      cursorAfter := after
      cursorSource := by
        simp [markedSource, before, after,
          TargetEmitterCursorAppender.sourceWithCursor]
      originalPacked := ?_
      beforePacked := ?_
      afterPacked := ?_ }
  · intro symbol member
    apply packed symbol
    rw [sourceEq]
    simpa [before, after,
      TargetEmitterCursorAppender.originalSource] using member
  · intro symbol member
    apply packed symbol
    rw [sourceEq]
    exact List.mem_append_left _ member
  · intro symbol member
    apply packed symbol
    rw [sourceEq]
    exact List.mem_append_right _ (List.Mem.tail _ member)

private theorem targetEmitter_configAtWord_eq
    (state : Nat) (left word : List WorkSymbol) :
    { state := state, tape := focusTape left word } =
      TargetEmitter.configAtWord state left word := by
  cases word <;> rfl

private theorem targetEmitter_configAtWord_tape_eq
    (state : Nat) (left word : List WorkSymbol) :
    (TargetEmitter.configAtWord state left word).tape =
      focusTape left word := by
  cases word <;> rfl

private theorem carrierReader_configAtWord_eq
    (state : Nat) (left word : List WorkSymbol) :
    { state := state, tape := focusTape left word } =
      CNFToNANDCarrierTokenReader.configAtWord state left word := by
  cases word <;> rfl

private theorem cursorControl_configAtWord_eq
    (state : Nat) (left word : List WorkSymbol) :
    { state := state, tape := focusTape left word } =
      TargetEmitterCursorControl.configAtWord state left word := by
  cases word <;> rfl

private theorem navigator_configAtWord_eq
    (state : Nat) (left word : List WorkSymbol) :
    { state := state, tape := focusTape left word } =
      TargetEmitterNavigator.configAtWord state left word := by
  cases word <;> rfl

private theorem tokenSecondCell_eq
    (token : CNFToken) :
    tokenSecondCell token =
      constantSecondCell
        (CNFToNANDCarrierEncoder.Source.secondBit token) := by
  cases token <;> rfl

def tokenReaderSteps : Nat := 6

theorem token_bits_reader_path
    (pass : Pass)
    (state : GrammarState)
    (active : state ∈ activeGrammarStates)
    (first second : Bool) (left rest : List WorkSymbol) :
    AcceptPath graph
      (.node (firstBitRef pass state))
      (grammarActionEndpoint pass state
        (recoveredToken first second))
      tokenReaderSteps
      (focusTape left
        ([ SourceParser.cell01
         , constantSecondCell first
         , SourceParser.cell01
         , constantSecondCell second
         ] ++ rest))
      (focusTape
        (SourceParser.cell01 :: constantSecondCell first ::
          SourceParser.cell01 :: left)
        (constantSecondCell second :: rest)) := by
  let middleTape :=
    focusTape
      (constantSecondCell first :: SourceParser.cell01 :: left)
      (SourceParser.cell01 :: constantSecondCell second :: rest)
  let finalTape :=
    focusTape
      (SourceParser.cell01 :: constantSecondCell first ::
        SourceParser.cell01 :: left)
      (constantSecondCell second :: rest)
  have terminal :
      AcceptPath graph
        (grammarActionEndpoint pass state
          (recoveredToken first second))
        (grammarActionEndpoint pass state
          (recoveredToken first second))
        0 finalTape finalTape := .terminal _ _
  have secondPath :
      AcceptPath graph
        (.node (secondBitRef pass state first))
        (grammarActionEndpoint pass state
          (recoveredToken first second))
        3 middleTape finalTape := by
    cases second with
    | false =>
        have run :
            workRunExact?
                CNFToNANDCarrierTokenReader.secondSourceMachine 2
                { state :=
                    CNFToNANDCarrierTokenReader.secondSourceMachine.startState
                  tape := middleTape } =
              some
                { state :=
                    CNFToNANDCarrierTokenReader.secondSourceMachine.acceptState
                  tape := finalTape } := by
          rw [carrierReader_configAtWord_eq,
            carrierReader_configAtWord_eq]
          simpa [middleTape, finalTape, constantSecondCell,
            CNFToNANDCarrierTokenReader.secondSourceMachine,
            CNFToNANDCarrierTokenReader.machine,
            CNFToNANDCarrierTokenReader.State.start,
            CNFToNANDCarrierTokenReader.State.accept,
            CNFToNANDCarrierTokenReader.cell00,
            CNFToNANDCarrierTokenReader.cell01,
            SourceParser.cell00, SourceParser.cell01] using
            CNFToNANDCarrierTokenReader.false_exact false
              (constantSecondCell first ::
                SourceParser.cell01 :: left) rest
        simpa [secondBitNode, secondBitRef, recoveredToken] using
          localAccept_path
            (Address.secondBit pass state first)
            CNFToNANDCarrierTokenReader.secondSourceMachine
            (grammarActionEndpoint pass state
              (recoveredToken first false))
            (grammarActionEndpoint pass state
              (recoveredToken first true))
            (grammarActionEndpoint pass state
              (recoveredToken first false))
            2 0 middleTape finalTape finalTape
            (by simpa [secondBitNode] using
              secondBitNode_member pass state first active)
            run terminal
    | true =>
        have run :
            workRunExact?
                CNFToNANDCarrierTokenReader.secondSourceMachine 2
                { state :=
                    CNFToNANDCarrierTokenReader.secondSourceMachine.startState
                  tape := middleTape } =
              some
                { state :=
                    CNFToNANDCarrierTokenReader.secondSourceMachine.rejectState
                  tape := finalTape } := by
          rw [carrierReader_configAtWord_eq,
            carrierReader_configAtWord_eq]
          simpa [middleTape, finalTape, constantSecondCell,
            CNFToNANDCarrierTokenReader.secondSourceMachine,
            CNFToNANDCarrierTokenReader.machine,
            CNFToNANDCarrierTokenReader.State.start,
            CNFToNANDCarrierTokenReader.State.reject,
            CNFToNANDCarrierTokenReader.cell01,
            SourceParser.cell00, SourceParser.cell01] using
            CNFToNANDCarrierTokenReader.true_exact false
              (constantSecondCell first ::
                SourceParser.cell01 :: left) rest
        simpa [secondBitNode, secondBitRef, recoveredToken] using
          localReject_path
            (Address.secondBit pass state first)
            CNFToNANDCarrierTokenReader.secondSourceMachine
            (grammarActionEndpoint pass state
              (recoveredToken first false))
            (grammarActionEndpoint pass state
              (recoveredToken first true))
            (grammarActionEndpoint pass state
              (recoveredToken first true))
            2 0 middleTape finalTape finalTape
            (by simpa [secondBitNode] using
              secondBitNode_member pass state first active)
            run terminal
  cases first with
  | false =>
      have run :
          workRunExact?
              CNFToNANDCarrierTokenReader.firstSourceMachine 2
              { state :=
                  CNFToNANDCarrierTokenReader.firstSourceMachine.startState
                tape :=
                  focusTape left
                    ([ SourceParser.cell01
                     , constantSecondCell false
                     , SourceParser.cell01
                     , constantSecondCell second
                     ] ++ rest) } =
            some
              { state :=
                  CNFToNANDCarrierTokenReader.firstSourceMachine.acceptState
                tape := middleTape } := by
        rw [carrierReader_configAtWord_eq,
          carrierReader_configAtWord_eq]
        simpa [middleTape, constantSecondCell,
          CNFToNANDCarrierTokenReader.firstSourceMachine,
          CNFToNANDCarrierTokenReader.machine,
          CNFToNANDCarrierTokenReader.State.start,
          CNFToNANDCarrierTokenReader.State.accept,
          CNFToNANDCarrierTokenReader.cell00,
          CNFToNANDCarrierTokenReader.cell01,
          SourceParser.cell00, SourceParser.cell01] using
          CNFToNANDCarrierTokenReader.false_exact true left
            (SourceParser.cell01 ::
              constantSecondCell second :: rest)
      simpa [tokenReaderSteps, firstBitNode, firstBitRef,
        finalTape] using
        localAccept_path
          (Address.firstBit pass state)
          CNFToNANDCarrierTokenReader.firstSourceMachine
          (.node (secondBitRef pass state false))
          (.node (secondBitRef pass state true))
          (grammarActionEndpoint pass state
            (recoveredToken false second))
          2 3 _ middleTape finalTape
          (by simpa [firstBitNode] using
            firstBitNode_member pass state active)
          run secondPath

  | true =>
      have run :
          workRunExact?
              CNFToNANDCarrierTokenReader.firstSourceMachine 2
              { state :=
                  CNFToNANDCarrierTokenReader.firstSourceMachine.startState
                tape :=
                  focusTape left
                    ([ SourceParser.cell01
                     , constantSecondCell true
                     , SourceParser.cell01
                     , constantSecondCell second
                     ] ++ rest) } =
            some
              { state :=
                  CNFToNANDCarrierTokenReader.firstSourceMachine.rejectState
                tape := middleTape } := by
        rw [carrierReader_configAtWord_eq,
          carrierReader_configAtWord_eq]
        simpa [middleTape, constantSecondCell,
          CNFToNANDCarrierTokenReader.firstSourceMachine,
          CNFToNANDCarrierTokenReader.machine,
          CNFToNANDCarrierTokenReader.State.start,
          CNFToNANDCarrierTokenReader.State.reject,
          CNFToNANDCarrierTokenReader.cell01,
          SourceParser.cell00, SourceParser.cell01] using
          CNFToNANDCarrierTokenReader.true_exact true left
            (SourceParser.cell01 ::
              constantSecondCell second :: rest)
      simpa [tokenReaderSteps, firstBitNode, firstBitRef,
        finalTape] using
        localReject_path
          (Address.firstBit pass state)
          CNFToNANDCarrierTokenReader.firstSourceMachine
          (.node (secondBitRef pass state false))
          (.node (secondBitRef pass state true))
          (grammarActionEndpoint pass state
            (recoveredToken true second))
          2 3 _ middleTape finalTape
          (by simpa [firstBitNode] using
            firstBitNode_member pass state active)
          run secondPath

def tokenReadInstallSteps
    (all processed : List CNFToken) (token : CNFToken) : Nat :=
  tokenReaderSteps + (tokenBeforeCells all processed token).length + 3

theorem token_read_install_path
    (pass : Pass) (formula : CNFFormula)
    (processed : List CNFToken) (token : CNFToken)
    (rest : List CNFToken) (state : GrammarState)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ token :: rest)
    (active : state ∈ activeGrammarStates)
    (valid : validGrammarToken state token = true)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef pass state).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells token rest)
        runtime.targetTokens initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node (firstBitRef pass state))
        (postInstallEndpoint pass state token)
        (tokenReadInstallSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token)
        initialTape finalTape ∧
      TapeRepresents 0
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token rest)
        runtime.targetTokens finalTape := by
  let capacity := CNFToNANDWorkspace.capacity formula
  let all := CNFToNANDWorkspace.formulaTokens formula
  let workspace :=
    TargetEmitterRuntime.logicalLeftWorkspace
      capacity runtime.scratch runtime.registers runtime.checks
  let outsideLeft := workspace.tail
  let before := tokenBeforeCells all processed token
  let after := tokenAfterCells rest
  let suffix :=
    TargetEmitter.sourceTargetBoundary ::
      SourceParser.packedTokenCells runtime.targetTokens
  let scanLeft := scanBeforeCells all processed
  let readerRest :=
    [SourceParser.cell01, SourceParser.cell11] ++
      carrierGateCells rest ++ carrierFooterCells ++ suffix
  let canonicalInitial :=
    focusTape (scanLeft.reverse ++ workspace)
      (scanAfterCells token rest ++ suffix)
  let beforeInstall :=
    focusTape (before.reverse ++ workspace)
      (tokenSecondCell token :: after ++ suffix)
  let canonicalFinal :=
    focusTape workspace
      (markedSource all processed token rest ++ suffix)
  have workspaceEq :
      workspace =
        TargetEmitter.sourceLeftBoundary :: outsideLeft := by
    rfl
  have recovered :
      recoveredToken
          (CNFToNANDCarrierEncoder.Source.firstBit token)
          (CNFToNANDCarrierEncoder.Source.secondBit token) =
        token := by
    cases token <;> rfl
  have readerPath :
      AcceptPath graph (.node (firstBitRef pass state))
        (.node (installRef pass state token))
        tokenReaderSteps canonicalInitial beforeInstall := by
    have raw :=
      token_bits_reader_path pass state active
        (CNFToNANDCarrierEncoder.Source.firstBit token)
        (CNFToNANDCarrierEncoder.Source.secondBit token)
        (scanLeft.reverse ++ workspace) readerRest
    rw [recovered] at raw
    have actionEq :
        grammarActionEndpoint pass state token =
          .node (installRef pass state token) := by
      simp [grammarActionEndpoint, valid]
    rw [actionEq] at raw
    simpa [canonicalInitial, beforeInstall, readerRest,
      scanAfterCells, carrierGateCellsFor_explicit,
      tokenSecondCell_eq, before, tokenBeforeCells,
      after, tokenAfterCells, scanLeft, scanBeforeCells,
      List.reverse_append, List.append_assoc] using raw
  have ordinary :
      TargetEmitter.PackedSymbol (tokenSecondCell token) := by
    cases token with
    | f => exact TargetEmitter.PackedSymbol.zeroZero
    | sep => exact TargetEmitter.PackedSymbol.zeroOne
    | finish => exact TargetEmitter.PackedSymbol.zeroZero
    | t => exact TargetEmitter.PackedSymbol.zeroOne
  have prefixPacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    apply canonicalSource_packed formula symbol
    rw [canonicalSource_token_split
      formula processed token rest tokens]
    exact List.mem_append_left _ member
  have installRun :
      workRunExact?
          (TargetEmitterCursorControl.installMachine
            (tokenSecondCell token))
          (before.length + 2)
          { state :=
              (TargetEmitterCursorControl.installMachine
                (tokenSecondCell token)).startState
            tape := beforeInstall } =
        some
          { state :=
              (TargetEmitterCursorControl.installMachine
                (tokenSecondCell token)).acceptState
            tape := canonicalFinal } := by
    rw [cursorControl_configAtWord_eq,
      cursorControl_configAtWord_eq]
    simpa [beforeInstall, canonicalFinal, workspaceEq,
      markedSource, before, after, suffix, all,
      TargetEmitterCursorAppender.cursorMarker,
      TargetEmitterCursorControl.cursorMark,
      TargetEmitterCursorControl.installMachine,
      TargetEmitterCursorControl.installState,
      TargetEmitterCursorControl.installedState,
      List.append_assoc] using
      TargetEmitterCursorControl.install_exact
        (tokenSecondCell token) before after outsideLeft suffix
        ordinary prefixPacked
  have terminal :
      AcceptPath graph
        (postInstallEndpoint pass state token)
        (postInstallEndpoint pass state token) 0
        canonicalFinal canonicalFinal := .terminal _ _
  have installPath :
      AcceptPath graph
        (.node (installRef pass state token))
        (postInstallEndpoint pass state token)
        (before.length + 3) beforeInstall canonicalFinal := by
    simpa [installRef, installNode] using
      localAccept_path
        (Address.install pass state token)
        (TargetEmitterCursorControl.installMachine
          (tokenSecondCell token))
        (postInstallEndpoint pass state token) .reject
        (postInstallEndpoint pass state token)
        (before.length + 2) 0
        beforeInstall canonicalFinal canonicalFinal
        (by simpa [installNode] using
          installNode_member pass state token active)
        installRun terminal
  have canonicalPath :=
    AcceptPath.trans graph (.node (firstBitRef pass state))
      (.node (installRef pass state token))
      (postInstallEndpoint pass state token)
      tokenReaderSteps (before.length + 3)
      canonicalInitial beforeInstall canonicalFinal
      readerPath installPath
  have initialEquivalent :
      WorkTape.BlankEquivalent initialTape canonicalInitial := by
    have tapeEquivalent := represents.tape
    rw [targetEmitter_configAtWord_tape_eq] at tapeEquivalent
    simpa [ScanRepresents, canonicalInitial, scanLeft, workspace,
      suffix, capacity, all, focusTape,
      List.append_assoc] using tapeEquivalent
  rcases AcceptPath.transport canonicalPath initialEquivalent with
    ⟨finalTape, path, finalEquivalent⟩
  refine ⟨finalTape, ?_, ?_⟩
  · simpa [tokenReadInstallSteps, before, all,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using path
  · refine ⟨rfl, ?_⟩
    simpa [TapeRepresents, TargetEmitterRuntime.Represents,
      TargetEmitterRuntime.logicalConfiguration,
      TargetEmitterRuntime.logicalWord,
      canonicalFinal, workspace, suffix, capacity, all, focusTape,
      List.append_assoc] using finalEquivalent

def tokenRestoreAdvanceSteps
    (all processed : List CNFToken) (token : CNFToken) : Nat :=
  (tokenBeforeCells all processed token).length + 6

theorem token_restore_advance_next_path
    (pass : Pass) (formula : CNFFormula)
    (processed : List CNFToken) (token next : CNFToken)
    (tail : List CNFToken) (state : GrammarState)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ token :: next :: tail)
    (notFinished : stateFinishKind? state = none)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (restoreRef pass state token).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token (next :: tail))
        runtime.targetTokens initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node (restoreRef pass state token))
        (.node (firstBitRef pass state))
        (tokenRestoreAdvanceSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token)
        initialTape finalTape ∧
      ScanRepresents (firstBitRef pass state).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [token]))
        (scanAfterCells next tail)
        runtime.targetTokens finalTape := by
  let capacity := CNFToNANDWorkspace.capacity formula
  let all := CNFToNANDWorkspace.formulaTokens formula
  let workspace :=
    TargetEmitterRuntime.logicalLeftWorkspace
      capacity runtime.scratch runtime.registers runtime.checks
  let outsideLeft := workspace.tail
  let before := tokenBeforeCells all processed token
  let after := tokenAfterCells (next :: tail)
  let suffix :=
    TargetEmitter.sourceTargetBoundary ::
      SourceParser.packedTokenCells runtime.targetTokens
  let nextScanLeft :=
    scanBeforeCells all (processed ++ [token])
  let canonicalInitial :=
    focusTape workspace
      (markedSource all processed token (next :: tail) ++ suffix)
  let afterRestore :=
    focusTape
      (tokenSecondCell token :: before.reverse ++ workspace)
      (after ++ suffix)
  let canonicalFinal :=
    focusTape (nextScanLeft.reverse ++ workspace)
      (scanAfterCells next tail ++ suffix)
  have workspaceEq :
      workspace =
        TargetEmitter.sourceLeftBoundary :: outsideLeft := by
    rfl
  have prefixPacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    apply canonicalSource_packed formula symbol
    rw [canonicalSource_token_split
      formula processed token (next :: tail) tokens]
    exact List.mem_append_left _ member
  have restoreRun :
      workRunExact?
          (TargetEmitterCursorControl.restoreMachine
            (tokenSecondCell token))
          (before.length + 1)
          { state :=
              (TargetEmitterCursorControl.restoreMachine
                (tokenSecondCell token)).startState
            tape := canonicalInitial } =
        some
          { state :=
              (TargetEmitterCursorControl.restoreMachine
                (tokenSecondCell token)).acceptState
            tape := afterRestore } := by
    rw [cursorControl_configAtWord_eq,
      cursorControl_configAtWord_eq]
    simpa [canonicalInitial, afterRestore, workspaceEq,
      markedSource, before, after, suffix, all,
      TargetEmitterCursorAppender.cursorMarker,
      TargetEmitterCursorControl.cursorMark,
      TargetEmitterCursorControl.restoreMachine,
      TargetEmitterCursorControl.restoreState,
      TargetEmitterCursorControl.restoredState,
      List.append_assoc] using
      TargetEmitterCursorControl.restore_exact
        (tokenSecondCell token) before
        (after ++ suffix) outsideLeft prefixPacked
  have gateTerminal :
      AcceptPath graph (.node (gateAdvanceRef pass state))
        (.node (gateAdvanceRef pass state)) 0
        afterRestore afterRestore := .terminal _ _
  have restorePath :
      AcceptPath graph (.node (restoreRef pass state token))
        (.node (gateAdvanceRef pass state))
        (before.length + 2) canonicalInitial afterRestore := by
    simpa [restoreRef, restoreNode] using
      localAccept_path
        (Address.restore pass state token)
        (TargetEmitterCursorControl.restoreMachine
          (tokenSecondCell token))
        (.node (gateAdvanceRef pass state)) .reject
        (.node (gateAdvanceRef pass state))
        (before.length + 1) 0
        canonicalInitial afterRestore afterRestore
        (by simpa [restoreNode] using
          restoreNode_member pass state token)
        restoreRun gateTerminal
  have gateRun :
      workRunExact? TargetEmitterNavigator.gateAdvanceMachine 3
          { state :=
              TargetEmitterNavigator.gateAdvanceMachine.startState
            tape := afterRestore } =
        some
          { state :=
              TargetEmitterNavigator.gateAdvanceMachine.acceptState
            tape := canonicalFinal } := by
    rw [navigator_configAtWord_eq,
      navigator_configAtWord_eq]
    simpa [afterRestore, canonicalFinal, after,
      tokenAfterCells, nextScanLeft, scanBeforeCells,
      scanAfterCells, carrierGateCells_append,
      carrierGateCells, carrierGateCellsFor_explicit,
      before, tokenBeforeCells, suffix,
      TargetEmitterNavigator.gateAdvanceMachine,
      TargetEmitterNavigator.machineFrom,
      TargetEmitterNavigator.State.gateEndFirst,
      TargetEmitterNavigator.State.accept,
      SourceParser.cell01, SourceParser.cell11,
      TargetEmitterNavigator.cell01,
      TargetEmitterNavigator.cell11,
      List.reverse_append, List.append_assoc] using
      TargetEmitterNavigator.gateAdvance_next_exact
        (tokenSecondCell token :: before.reverse ++ workspace)
        ((carrierGateCellsFor next).tail ++
          carrierGateCells tail ++ carrierFooterCells ++ suffix)
        SourceParser.cell01 (Or.inr rfl)
  have terminal :
      AcceptPath graph (.node (firstBitRef pass state))
        (.node (firstBitRef pass state)) 0
        canonicalFinal canonicalFinal := .terminal _ _
  have gatePath :
      AcceptPath graph (.node (gateAdvanceRef pass state))
        (.node (firstBitRef pass state)) 4
        afterRestore canonicalFinal := by
    simpa [gateAdvanceRef, gateAdvanceNode, notFinished] using
      localAccept_path
        (Address.gateAdvance pass state)
        TargetEmitterNavigator.gateAdvanceMachine
        (.node (firstBitRef pass state)) .reject
        (.node (firstBitRef pass state))
        3 0 afterRestore canonicalFinal canonicalFinal
        (by simpa [gateAdvanceNode, notFinished] using
          gateAdvanceNode_member pass state)
        gateRun terminal
  have canonicalPath :=
    AcceptPath.trans graph (.node (restoreRef pass state token))
      (.node (gateAdvanceRef pass state))
      (.node (firstBitRef pass state))
      (before.length + 2) 4
      canonicalInitial afterRestore canonicalFinal
      restorePath gatePath
  have initialEquivalent :
      WorkTape.BlankEquivalent initialTape canonicalInitial := by
    have tapeEquivalent := represents.tape
    have tapeEquivalent' :
        WorkTape.BlankEquivalent initialTape
          (TargetEmitter.configAtWord
            (restoreRef pass state token).startState workspace
            (markedSource all processed token (next :: tail) ++
              suffix)).tape := by
      simpa [TapeRepresents, TargetEmitterRuntime.Represents,
        TargetEmitterRuntime.logicalConfiguration,
        TargetEmitterRuntime.logicalWord,
        workspace, suffix, capacity, all,
        List.append_assoc] using tapeEquivalent
    rw [targetEmitter_configAtWord_tape_eq] at tapeEquivalent'
    simpa [canonicalInitial, workspace, suffix, capacity, all,
      List.append_assoc] using tapeEquivalent'
  rcases AcceptPath.transport canonicalPath initialEquivalent with
    ⟨finalTape, path, finalEquivalent⟩
  refine ⟨finalTape, ?_, ?_⟩
  · have stepsEq :
        before.length + 2 + 4 = before.length + 6 := by
      omega
    change
      AcceptPath graph (.node (restoreRef pass state token))
        (.node (firstBitRef pass state))
        (before.length + 6) initialTape finalTape
    rw [← stepsEq]
    exact path
  · unfold ScanRepresents
    refine ⟨rfl, ?_⟩
    rw [targetEmitter_configAtWord_tape_eq]
    simpa [canonicalFinal, nextScanLeft,
      workspace, suffix, capacity, all,
      List.append_assoc] using finalEquivalent

theorem token_restore_advance_end_path
    (pass : Pass) (formula : CNFFormula)
    (processed : List CNFToken) (token : CNFToken)
    (state : GrammarState) (kind : FinishKind)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ [token])
    (finished : stateFinishKind? state = some kind)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (restoreRef pass state token).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token [])
        runtime.targetTokens initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node (restoreRef pass state token))
        (.node (programEndRef pass kind))
        (tokenRestoreAdvanceSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token)
        initialTape finalTape ∧
      ScanRepresents (programEndRef pass kind).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [token]))
        carrierFooterCells runtime.targetTokens finalTape := by
  let capacity := CNFToNANDWorkspace.capacity formula
  let all := CNFToNANDWorkspace.formulaTokens formula
  let workspace :=
    TargetEmitterRuntime.logicalLeftWorkspace
      capacity runtime.scratch runtime.registers runtime.checks
  let outsideLeft := workspace.tail
  let before := tokenBeforeCells all processed token
  let after := tokenAfterCells []
  let suffix :=
    TargetEmitter.sourceTargetBoundary ::
      SourceParser.packedTokenCells runtime.targetTokens
  let finalScanLeft :=
    scanBeforeCells all (processed ++ [token])
  let canonicalInitial :=
    focusTape workspace
      (markedSource all processed token [] ++ suffix)
  let afterRestore :=
    focusTape
      (tokenSecondCell token :: before.reverse ++ workspace)
      (after ++ suffix)
  let canonicalFinal :=
    focusTape (finalScanLeft.reverse ++ workspace)
      (carrierFooterCells ++ suffix)
  have workspaceEq :
      workspace =
        TargetEmitter.sourceLeftBoundary :: outsideLeft := by
    rfl
  have prefixPacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    apply canonicalSource_packed formula symbol
    rw [canonicalSource_token_split
      formula processed token [] (by simpa using tokens)]
    exact List.mem_append_left _ member
  have restoreRun :
      workRunExact?
          (TargetEmitterCursorControl.restoreMachine
            (tokenSecondCell token))
          (before.length + 1)
          { state :=
              (TargetEmitterCursorControl.restoreMachine
                (tokenSecondCell token)).startState
            tape := canonicalInitial } =
        some
          { state :=
              (TargetEmitterCursorControl.restoreMachine
                (tokenSecondCell token)).acceptState
            tape := afterRestore } := by
    rw [cursorControl_configAtWord_eq,
      cursorControl_configAtWord_eq]
    simpa [canonicalInitial, afterRestore, workspaceEq,
      markedSource, before, after, suffix, all,
      TargetEmitterCursorAppender.cursorMarker,
      TargetEmitterCursorControl.cursorMark,
      TargetEmitterCursorControl.restoreMachine,
      TargetEmitterCursorControl.restoreState,
      TargetEmitterCursorControl.restoredState,
      List.append_assoc] using
      TargetEmitterCursorControl.restore_exact
        (tokenSecondCell token) before
        (after ++ suffix) outsideLeft prefixPacked
  have gateTerminal :
      AcceptPath graph (.node (gateAdvanceRef pass state))
        (.node (gateAdvanceRef pass state)) 0
        afterRestore afterRestore := .terminal _ _
  have restorePath :
      AcceptPath graph (.node (restoreRef pass state token))
        (.node (gateAdvanceRef pass state))
        (before.length + 2) canonicalInitial afterRestore := by
    simpa [restoreRef, restoreNode] using
      localAccept_path
        (Address.restore pass state token)
        (TargetEmitterCursorControl.restoreMachine
          (tokenSecondCell token))
        (.node (gateAdvanceRef pass state)) .reject
        (.node (gateAdvanceRef pass state))
        (before.length + 1) 0
        canonicalInitial afterRestore afterRestore
        (by simpa [restoreNode] using
          restoreNode_member pass state token)
        restoreRun gateTerminal
  have gateRun :
      workRunExact? TargetEmitterNavigator.gateAdvanceMachine 3
          { state :=
              TargetEmitterNavigator.gateAdvanceMachine.startState
            tape := afterRestore } =
        some
          { state :=
              TargetEmitterNavigator.gateAdvanceMachine.rejectState
            tape := canonicalFinal } := by
    rw [navigator_configAtWord_eq,
      navigator_configAtWord_eq]
    simpa [afterRestore, canonicalFinal, after,
      tokenAfterCells, finalScanLeft, scanBeforeCells,
      carrierGateCells_append, carrierGateCells,
      carrierGateCellsFor_explicit,
      carrierFooterCells, before, tokenBeforeCells, suffix,
      TargetEmitterNavigator.gateAdvanceMachine,
      TargetEmitterNavigator.machineFrom,
      TargetEmitterNavigator.State.gateEndFirst,
      TargetEmitterNavigator.State.reject,
      SourceParser.cell01, SourceParser.cell10,
      SourceParser.cell11,
      TargetEmitterNavigator.cell01,
      TargetEmitterNavigator.cell10,
      TargetEmitterNavigator.cell11,
      List.reverse_append, List.append_assoc] using
      TargetEmitterNavigator.gateAdvance_programEnd_exact
        (tokenSecondCell token :: before.reverse ++ workspace)
        ((carrierFooterCells.tail) ++ suffix)
  have terminal :
      AcceptPath graph (.node (programEndRef pass kind))
        (.node (programEndRef pass kind)) 0
        canonicalFinal canonicalFinal := .terminal _ _
  have gatePath :
      AcceptPath graph (.node (gateAdvanceRef pass state))
        (.node (programEndRef pass kind)) 4
        afterRestore canonicalFinal := by
    simpa [gateAdvanceRef, gateAdvanceNode, finished] using
      localReject_path
        (Address.gateAdvance pass state)
        TargetEmitterNavigator.gateAdvanceMachine
        .reject (.node (programEndRef pass kind))
        (.node (programEndRef pass kind))
        3 0 afterRestore canonicalFinal canonicalFinal
        (by simpa [gateAdvanceNode, finished] using
          gateAdvanceNode_member pass state)
        gateRun terminal
  have canonicalPath :=
    AcceptPath.trans graph (.node (restoreRef pass state token))
      (.node (gateAdvanceRef pass state))
      (.node (programEndRef pass kind))
      (before.length + 2) 4
      canonicalInitial afterRestore canonicalFinal
      restorePath gatePath
  have initialEquivalent :
      WorkTape.BlankEquivalent initialTape canonicalInitial := by
    have tapeEquivalent := represents.tape
    have tapeEquivalent' :
        WorkTape.BlankEquivalent initialTape
          (TargetEmitter.configAtWord
            (restoreRef pass state token).startState workspace
            (markedSource all processed token [] ++ suffix)).tape := by
      simpa [TapeRepresents, TargetEmitterRuntime.Represents,
        TargetEmitterRuntime.logicalConfiguration,
        TargetEmitterRuntime.logicalWord,
        workspace, suffix, capacity, all,
        List.append_assoc] using tapeEquivalent
    rw [targetEmitter_configAtWord_tape_eq] at tapeEquivalent'
    simpa [canonicalInitial, workspace, suffix, capacity, all,
      List.append_assoc] using tapeEquivalent'
  rcases AcceptPath.transport canonicalPath initialEquivalent with
    ⟨finalTape, path, finalEquivalent⟩
  refine ⟨finalTape, ?_, ?_⟩
  · have stepsEq :
        before.length + 2 + 4 = before.length + 6 := by
      omega
    change
      AcceptPath graph (.node (restoreRef pass state token))
        (.node (programEndRef pass kind))
        (before.length + 6) initialTape finalTape
    rw [← stepsEq]
    exact path
  · unfold ScanRepresents
    refine ⟨rfl, ?_⟩
    rw [targetEmitter_configAtWord_tape_eq]
    simpa [canonicalFinal, finalScanLeft,
      workspace, suffix, capacity, all,
      List.append_assoc] using finalEquivalent

def passRewindRef (pass : Pass) (kind : FinishKind) : NodeRef :=
  match pass with
  | .count => countRewindRef kind
  | .emit => emitRewindRef

def programEndSteps : Nat := 3

theorem program_end_path
    (pass : Pass) (kind : FinishKind)
    (capacity : Nat) (runtime : Runtime)
    (before : List WorkSymbol) (initialTape : WorkTape)
    (represents :
      ScanRepresents (programEndRef pass kind).startState
        capacity runtime.scratch runtime.registers runtime.checks
        before carrierFooterCells runtime.targetTokens initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node (programEndRef pass kind))
        (.node (passRewindRef pass kind))
        programEndSteps initialTape finalTape ∧
      ScanRepresents (passRewindRef pass kind).startState
        capacity runtime.scratch runtime.registers runtime.checks
        (before ++ [SourceParser.cell10, SourceParser.cell00])
        (carrierFooterCells.drop 2) runtime.targetTokens finalTape := by
  let workspace :=
    TargetEmitterRuntime.logicalLeftWorkspace
      capacity runtime.scratch runtime.registers runtime.checks
  let suffix :=
    TargetEmitter.sourceTargetBoundary ::
      SourceParser.packedTokenCells runtime.targetTokens
  let canonicalInitial :=
    focusTape (before.reverse ++ workspace)
      (carrierFooterCells ++ suffix)
  let canonicalFinal :=
    focusTape
      ((before ++
        [SourceParser.cell10, SourceParser.cell00]).reverse ++
          workspace)
      (carrierFooterCells.drop 2 ++ suffix)
  have run :
      workRunExact? TargetEmitterNavigator.programEndMachine 2
          { state :=
              TargetEmitterNavigator.programEndMachine.startState
            tape := canonicalInitial } =
        some
          { state :=
              TargetEmitterNavigator.programEndMachine.acceptState
            tape := canonicalFinal } := by
    rw [navigator_configAtWord_eq,
      navigator_configAtWord_eq]
    simpa [canonicalInitial, canonicalFinal,
      carrierFooterCells, SourceParser.sourceCells, suffix,
      TargetEmitterNavigator.programEndMachine,
      TargetEmitterNavigator.machineFrom,
      TargetEmitterNavigator.State.programFirst,
      TargetEmitterNavigator.State.accept,
      SourceParser.cell00, SourceParser.cell01,
      SourceParser.cell10, SourceParser.cell11,
      TargetEmitterNavigator.cell00,
      TargetEmitterNavigator.cell01,
      TargetEmitterNavigator.cell10,
      TargetEmitterNavigator.cell11,
      List.reverse_append, List.append_assoc] using
      TargetEmitterNavigator.programEnd_exact
        (before.reverse ++ workspace)
        ([SourceParser.cell00, SourceParser.cell10,
          SourceParser.cell01, SourceParser.cell10,
          SourceParser.cell11] ++ suffix)
        SourceParser.cell01
  have terminal :
      AcceptPath graph (.node (passRewindRef pass kind))
        (.node (passRewindRef pass kind)) 0
        canonicalFinal canonicalFinal := .terminal _ _
  have canonicalPath :
      AcceptPath graph (.node (programEndRef pass kind))
        (.node (passRewindRef pass kind))
        programEndSteps canonicalInitial canonicalFinal := by
    cases pass with
    | count =>
        simpa [programEndSteps, passRewindRef,
          programEndRef, programEndNode] using
          localAccept_path
            (Address.programEnd .count kind)
            TargetEmitterNavigator.programEndMachine
            (.node (countRewindRef kind)) .reject
            (.node (countRewindRef kind))
            2 0 canonicalInitial canonicalFinal canonicalFinal
            (by simpa [programEndNode] using
              programEndNode_member .count kind)
            run terminal
    | emit =>
        simpa [programEndSteps, passRewindRef,
          programEndRef, programEndNode] using
          localAccept_path
            (Address.programEnd .emit kind)
            TargetEmitterNavigator.programEndMachine
            (.node emitRewindRef) .reject
            (.node emitRewindRef)
            2 0 canonicalInitial canonicalFinal canonicalFinal
            (by simpa [programEndNode] using
              programEndNode_member .emit kind)
            run terminal
  have initialEquivalent :
      WorkTape.BlankEquivalent initialTape canonicalInitial := by
    have tapeEquivalent := represents.tape
    rw [targetEmitter_configAtWord_tape_eq] at tapeEquivalent
    simpa [canonicalInitial, workspace, suffix,
      List.append_assoc] using tapeEquivalent
  rcases AcceptPath.transport canonicalPath initialEquivalent with
    ⟨finalTape, path, finalEquivalent⟩
  refine ⟨finalTape, path, ?_⟩
  unfold ScanRepresents
  refine ⟨rfl, ?_⟩
  rw [targetEmitter_configAtWord_tape_eq]
  simpa [canonicalFinal, workspace, suffix,
    List.append_assoc] using finalEquivalent

/-! ## Generic source rewind -/

private theorem rewind_workRunExact?_append
    (machine : WorkMachine) (first second : Nat)
    (initial middle final : WorkConfiguration)
    (firstRun :
      workRunExact? machine first initial = some middle)
    (secondRun :
      workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial = some final :=
  PipelineMachineSimulation.workRunExact?_compose
    machine first second initial middle final firstRun secondRun

private theorem rewind_scan_exact
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
        rewind_workRunExact?_append
          CNFToNANDCarrierTokenReader.Rewind.machine
          1 rest.length _ _ _ first tail
      simpa [List.reverse_cons, List.append_assoc,
        Nat.add_comm] using combined

private theorem rewind_exact
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
    rewind_scan_exact nearest outsideLeft right packed
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
    rewind_workRunExact?_append
      CNFToNANDCarrierTokenReader.Rewind.machine
      nearest.length 1 _ _ _ scanned boundary

/-- Exact cost of rewinding a crossed retained-source prefix and taking the
outer graph edge. -/
def sourceRewindSteps (before : List WorkSymbol) : Nat :=
  before.length + 3

/-- Literal graph lifting of the common rewind machine.  This theorem is
parameterized by the actual controller node and therefore serves both count
rewinds and the later completion rewind without a proof-side cursor lookup. -/
theorem source_rewind_path
    (code finalState capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (before : List WorkSymbol)
    (head : WorkSymbol) (after : List WorkSymbol)
    (target : List Token) (continuation : Endpoint)
    (member :
      controlNode code CNFToNANDCarrierTokenReader.Rewind.machine
        continuation .reject ∈ graph.nodes)
    (packed :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (headPacked : TargetEmitter.PackedSymbol head)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (controlRef code
          CNFToNANDCarrierTokenReader.Rewind.machine).startState
        capacity scratch registers checks before (head :: after) target
        initialTape) :
    ∃ finalTape,
      AcceptPath graph
        (.node
          (controlRef code
            CNFToNANDCarrierTokenReader.Rewind.machine))
        continuation (sourceRewindSteps before)
        initialTape finalTape ∧
      TapeRepresents finalState capacity scratch registers checks
        (before ++ head :: after) target finalTape := by
  let outsideLeft :=
    TargetEmitterCheckStack.scratchWord capacity scratch ++
      TargetEmitterLedger.ledgerBoundary ::
        (TargetEmitterLedger.slotBank capacity registers ++
          TargetEmitterCheckStack.stackWord checks)
  let suffix :=
    TargetEmitter.sourceTargetBoundary ::
      SourceParser.packedTokenCells target
  let canonicalInitial :=
    focusTape
      (before.reverse ++
        TargetEmitter.sourceLeftBoundary :: outsideLeft)
      (head :: after ++ suffix)
  let canonicalFinal :=
    focusTape
      (TargetEmitter.sourceLeftBoundary :: outsideLeft)
      (before ++ head :: after ++ suffix)
  have reversePacked :
      ∀ symbol, symbol ∈ head :: before.reverse →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol symbolMember
    simp only [List.mem_cons] at symbolMember
    rcases symbolMember with symbolEq | symbolMember
    · subst symbol
      exact headPacked
    · exact packed symbol (List.mem_reverse.mp symbolMember)
  have run :
      workRunExact? CNFToNANDCarrierTokenReader.Rewind.machine
          (before.length + 2)
          { state :=
              CNFToNANDCarrierTokenReader.Rewind.machine.startState
            tape := canonicalInitial } =
        some
          { state :=
              CNFToNANDCarrierTokenReader.Rewind.machine.acceptState
            tape := canonicalFinal } := by
    have exactRun :=
      rewind_exact (head :: before.reverse) outsideLeft
        (after ++ suffix) reversePacked
    rw [targetEmitter_configAtWord_eq,
      targetEmitter_configAtWord_eq]
    simpa [canonicalInitial, canonicalFinal,
      CNFToNANDCarrierTokenReader.Rewind.machine,
      CNFToNANDCarrierTokenReader.Rewind.sourceLeftBoundary,
      focusTape, TargetEmitter.configAtLeftWord,
      TargetEmitter.configAtWord,
      List.append_assoc] using exactRun
  have terminal :
      AcceptPath graph continuation continuation 0
        canonicalFinal canonicalFinal := .terminal _ _
  have canonicalPath :
      AcceptPath graph
        (.node
          (controlRef code
            CNFToNANDCarrierTokenReader.Rewind.machine))
        continuation (sourceRewindSteps before)
        canonicalInitial canonicalFinal := by
    simpa [sourceRewindSteps] using
      localAccept_path code
        CNFToNANDCarrierTokenReader.Rewind.machine
        continuation .reject continuation
        (before.length + 2) 0
        canonicalInitial canonicalFinal canonicalFinal
        member run terminal
  have initialEquivalent :
      WorkTape.BlankEquivalent initialTape canonicalInitial := by
    have tapeEquivalent := represents.tape
    rw [targetEmitter_configAtWord_tape_eq] at tapeEquivalent
    simpa [canonicalInitial, outsideLeft, suffix,
      ScanRepresents,
      TargetEmitterRuntime.logicalLeftWorkspace,
      List.append_assoc] using tapeEquivalent
  rcases AcceptPath.transport canonicalPath initialEquivalent with
    ⟨finalTape, path, finalEquivalent⟩
  refine ⟨finalTape, path, ?_⟩
  unfold TapeRepresents TargetEmitterRuntime.Represents
  refine
    ⟨TargetEmitterRuntime.logicalConfiguration_state
        finalState capacity scratch registers checks
        (before ++ head :: after) target |>.symm, ?_⟩
  simpa [canonicalFinal, outsideLeft, suffix,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterRuntime.logicalLeftWorkspace,
    targetEmitter_configAtWord_tape_eq,
    List.append_assoc] using finalEquivalent

/-! ## Count-pass header -/

/-- Exact physical cost of crossing the retained carrier header and taking
the graph edge to the first canonical CNF token. -/
def countHeaderScanSteps (formula : CNFFormula) : Nat :=
  TargetEmitterNavigator.headerWorkSteps 0
      (CNFToNANDWorkspace.formulaTokens formula).length + 1

private theorem focusTape_eq_targetEmitter_tape
    (state : Nat) (left word : List WorkSymbol) :
    focusTape left word =
      (TargetEmitter.configAtWord state left word).tape := by
  cases word <;> rfl

theorem count_header_path
    (formula : CNFFormula) (runtime : Runtime)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (passHeaderRef .count).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (canonicalSource formula) runtime.targetTokens initialTape) :
    ∃ first rest finalTape,
      CNFToNANDWorkspace.formulaTokens formula = first :: rest ∧
      AcceptPath graph (.node (passHeaderRef .count))
        (.node (firstBitRef .count .header))
        (countHeaderScanSteps formula) initialTape finalTape ∧
      ScanRepresents (firstBitRef .count .header).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (carrierHeaderCells (first :: rest))
        (carrierGateCells (first :: rest) ++ carrierFooterCells)
        runtime.targetTokens finalTape := by
  cases tokensEq :
      CNFToNANDWorkspace.formulaTokens formula with
  | nil =>
      exact False.elim
        (CNFToNANDWorkspace.formulaTokens_ne_nil formula tokensEq)
  | cons first rest =>
      let left :=
        TargetEmitterRuntime.logicalLeftWorkspace
          (CNFToNANDWorkspace.capacity formula)
          runtime.scratch runtime.registers runtime.checks
      let right :=
        carrierGateCells (first :: rest) ++ carrierFooterCells ++
          TargetEmitter.sourceTargetBoundary ::
            SourceParser.packedTokenCells runtime.targetTokens
      let canonicalInitial :=
        focusTape left
          (carrierHeaderCells (first :: rest) ++ right)
      let canonicalMiddle :=
        focusTape
          ((carrierHeaderCells (first :: rest)).reverse ++ left)
          right
      have localRun :
          workRunExact? TargetEmitterNavigator.headerMachine
              (TargetEmitterNavigator.headerWorkSteps 0
                (first :: rest).length)
              { state :=
                  TargetEmitterNavigator.headerMachine.startState
                tape := canonicalInitial } =
            some
              { state :=
                  TargetEmitterNavigator.headerMachine.acceptState
                tape := canonicalMiddle } := by
        change
          workRunExact? TargetEmitterNavigator.headerMachine
              (TargetEmitterNavigator.headerWorkSteps 0
                (first :: rest).length)
              { state := TargetEmitterNavigator.State.headerStart
                tape :=
                  focusTape left
                    (carrierHeaderCells (first :: rest) ++ right) } =
            some
              { state := TargetEmitterNavigator.State.accept
                tape :=
                  focusTape
                    ((carrierHeaderCells
                        (first :: rest)).reverse ++ left)
                    right }
        rw [navigator_configAtWord_eq, navigator_configAtWord_eq]
        simpa [right, carrierHeaderCells, carrierGateCells,
          carrierGateCellsFor, TargetEmitterNavigator.pushCrossed,
          SourceParser.cell00, SourceParser.cell01,
          TargetEmitterNavigator.cell00,
          TargetEmitterNavigator.cell01,
          List.reverse_append, List.append_assoc] using
          TargetEmitterNavigator.header_nonempty_exact
            0 (first :: rest).length
            SourceParser.cell01
            (constantSecondCell
                (CNFToNANDCarrierEncoder.Source.firstBit first) ::
              SourceParser.cell01 ::
              constantSecondCell
                  (CNFToNANDCarrierEncoder.Source.secondBit first) ::
                SourceParser.cell01 :: SourceParser.cell11 ::
                  carrierGateCells rest ++ carrierFooterCells ++
                TargetEmitter.sourceTargetBoundary ::
                  SourceParser.packedTokenCells runtime.targetTokens)
            left (Or.inr (by
              simp [SourceParser.cell01,
                TargetEmitterNavigator.cell01]))
      have terminal :
          AcceptPath graph
            (.node (firstBitRef .count .header))
            (.node (firstBitRef .count .header)) 0
            canonicalMiddle canonicalMiddle := .terminal _ _
      have canonicalPath :=
        localAccept_path Address.countHeader
          TargetEmitterNavigator.headerMachine
          (.node (firstBitRef .count .header)) .reject
          (.node (firstBitRef .count .header))
          (TargetEmitterNavigator.headerWorkSteps 0
            (first :: rest).length) 0
          canonicalInitial canonicalMiddle canonicalMiddle
          (by simpa [passHeaderNode] using
            passHeaderNode_member .count)
          localRun terminal
      have initialEquivalent :
          WorkTape.BlankEquivalent initialTape canonicalInitial := by
        have tapeEq := represents.tape
        simpa [TapeRepresents, TargetEmitterRuntime.Represents,
          TargetEmitterRuntime.logicalConfiguration,
          TargetEmitterRuntime.logicalWord, canonicalInitial, focusTape,
          TargetEmitter.configAtWord, right, left, tokensEq,
          carrierHeaderCells,
          canonicalSource_eq_carrier_layout,
          List.append_assoc] using tapeEq
      rcases AcceptPath.transport canonicalPath initialEquivalent with
        ⟨finalTape, path, finalEquivalent⟩
      refine ⟨first, rest, finalTape, rfl, ?_, ?_⟩
      · simpa [countHeaderScanSteps, tokensEq, passHeaderRef] using path
      · refine
          { state := by
              simp [TargetEmitter.configAtWord, carrierGateCells,
                carrierGateCellsFor]
            tape := ?_ }
        change
          WorkTape.BlankEquivalent finalTape
            (TargetEmitter.configAtWord
              (firstBitRef .count .header).startState
              ((carrierHeaderCells (first :: rest)).reverse ++
                TargetEmitterRuntime.logicalLeftWorkspace
                  (CNFToNANDWorkspace.capacity formula)
                  runtime.scratch runtime.registers runtime.checks)
              ((carrierGateCells (first :: rest) ++
                    carrierFooterCells) ++
                TargetEmitter.sourceTargetBoundary ::
                  SourceParser.packedTokenCells
                    runtime.targetTokens)).tape
        rw [← focusTape_eq_targetEmitter_tape]
        simpa [canonicalMiddle, right, left,
          List.append_assoc] using finalEquivalent

/-! ## Pass-parametric literal-index comparisons -/

/-- Exact graph cost of one physical scratch-versus-input-count comparison,
including the graph edge out of the literal comparison node. -/
def literalCompareSteps (capacity scratch : Nat) : Nat :=
  TargetEmitterScratchCompareSlot.workSteps
      .inputCount capacity scratch + 1

/-- Lift the equality endpoint of the literal comparison machine into the
fixed controller graph.  The comparison restores the complete logical
workspace before taking its accept edge. -/
theorem literal_compare_equal_path
    (code : Nat) (onAccept onReject : Endpoint)
    (finalState capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (initialTape : WorkTape)
    (member :
      controlNode code
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          onAccept onReject ∈ graph.nodes)
    (fits : LedgerFits capacity registers)
    (equal :
      scratch =
        TargetEmitterLedger.slotValue registers .inputCount)
    (allowed :
      TargetEmitterScratchCompareSlot.SourceAllowed sourceHead)
    (represents :
      TapeRepresents
        (controlRef code
          (TargetEmitterScratchCompareSlot.machineFor
            .inputCount)).startState
        capacity scratch registers checks
        (sourceHead :: sourceTail) target initialTape) :
    ∃ finalTape,
      AcceptPath graph
        (.node
          (controlRef code
            (TargetEmitterScratchCompareSlot.machineFor
              .inputCount)))
        onAccept (literalCompareSteps capacity scratch)
        initialTape finalTape ∧
      TapeRepresents finalState capacity scratch registers checks
        (sourceHead :: sourceTail) target finalTape := by
  have inputRepresents :
      TargetEmitterRuntime.Represents
        (TargetEmitterScratchCompareSlot.startState .inputCount)
        capacity scratch registers checks
        (sourceHead :: sourceTail) target
        { state :=
            TargetEmitterScratchCompareSlot.startState .inputCount
          tape := initialTape } := by
    simpa [TapeRepresents, controlRef,
      TargetEmitterScratchCompareSlot.machineFor] using represents
  rcases
      TargetEmitterRuntimePrimitives.compareRegisterEqual_exact
        .inputCount capacity scratch registers checks
        sourceHead sourceTail target
        { state :=
            TargetEmitterScratchCompareSlot.startState .inputCount
          tape := initialTape }
        fits.toPrimitive equal allowed inputRepresents with
    ⟨finalConfiguration, exactRun, finalRepresents⟩
  have exactRun' :
      workRunExact?
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          (TargetEmitterScratchCompareSlot.workSteps
            .inputCount capacity scratch)
          { state :=
              TargetEmitterScratchCompareSlot.startState .inputCount
            tape := initialTape } =
        some
          { state := TargetEmitterScratchCompareSlot.acceptState
            tape := finalConfiguration.tape } := by
    rcases finalConfiguration with ⟨state, tape⟩
    have stateEq := finalRepresents.state_eq
    simp only at stateEq
    subst state
    exact exactRun
  have terminal :
      AcceptPath graph onAccept onAccept 0
        finalConfiguration.tape finalConfiguration.tape :=
    .terminal _ _
  have path :
      AcceptPath graph
        (.node
          (controlRef code
            (TargetEmitterScratchCompareSlot.machineFor
              .inputCount)))
        onAccept (literalCompareSteps capacity scratch)
        initialTape finalConfiguration.tape := by
    simpa [literalCompareSteps] using
      localAccept_path code
        (TargetEmitterScratchCompareSlot.machineFor .inputCount)
        onAccept onReject onAccept
        (TargetEmitterScratchCompareSlot.workSteps
          .inputCount capacity scratch)
        0 initialTape finalConfiguration.tape
        finalConfiguration.tape member
        exactRun'
        terminal
  refine ⟨finalConfiguration.tape, path, ?_⟩
  exact
    represents_at_state (newState := finalState) finalRepresents

/-- Lift the strict-less endpoint of the literal comparison machine into the
fixed controller graph.  As for equality, the comparison restores every
logical workspace cell before taking its reject edge. -/
theorem literal_compare_less_path
    (code : Nat) (onAccept onReject : Endpoint)
    (finalState capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (initialTape : WorkTape)
    (member :
      controlNode code
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          onAccept onReject ∈ graph.nodes)
    (fits : LedgerFits capacity registers)
    (less :
      scratch <
        TargetEmitterLedger.slotValue registers .inputCount)
    (allowed :
      TargetEmitterScratchCompareSlot.SourceAllowed sourceHead)
    (represents :
      TapeRepresents
        (controlRef code
          (TargetEmitterScratchCompareSlot.machineFor
            .inputCount)).startState
        capacity scratch registers checks
        (sourceHead :: sourceTail) target initialTape) :
    ∃ finalTape,
      AcceptPath graph
        (.node
          (controlRef code
            (TargetEmitterScratchCompareSlot.machineFor
              .inputCount)))
        onReject (literalCompareSteps capacity scratch)
        initialTape finalTape ∧
      TapeRepresents finalState capacity scratch registers checks
        (sourceHead :: sourceTail) target finalTape := by
  have inputRepresents :
      TargetEmitterRuntime.Represents
        (TargetEmitterScratchCompareSlot.startState .inputCount)
        capacity scratch registers checks
        (sourceHead :: sourceTail) target
        { state :=
            TargetEmitterScratchCompareSlot.startState .inputCount
          tape := initialTape } := by
    simpa [TapeRepresents, controlRef,
      TargetEmitterScratchCompareSlot.machineFor] using represents
  rcases
      TargetEmitterRuntimePrimitives.compareRegisterLess_exact
        .inputCount capacity scratch registers checks
        sourceHead sourceTail target
        { state :=
            TargetEmitterScratchCompareSlot.startState .inputCount
          tape := initialTape }
        fits.toPrimitive less allowed inputRepresents with
    ⟨finalConfiguration, exactRun, finalRepresents⟩
  have exactRun' :
      workRunExact?
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          (TargetEmitterScratchCompareSlot.workSteps
            .inputCount capacity scratch)
          { state :=
              TargetEmitterScratchCompareSlot.startState .inputCount
            tape := initialTape } =
        some
          { state := TargetEmitterScratchCompareSlot.rejectState
            tape := finalConfiguration.tape } := by
    rcases finalConfiguration with ⟨state, tape⟩
    have stateEq := finalRepresents.state_eq
    simp only at stateEq
    subst state
    exact exactRun
  have terminal :
      AcceptPath graph onReject onReject 0
        finalConfiguration.tape finalConfiguration.tape :=
    .terminal _ _
  have path :
      AcceptPath graph
        (.node
          (controlRef code
            (TargetEmitterScratchCompareSlot.machineFor
              .inputCount)))
        onReject (literalCompareSteps capacity scratch)
        initialTape finalConfiguration.tape := by
    simpa [literalCompareSteps] using
      localReject_path code
        (TargetEmitterScratchCompareSlot.machineFor .inputCount)
        onAccept onReject onReject
        (TargetEmitterScratchCompareSlot.workSteps
          .inputCount capacity scratch)
        0 initialTape finalConfiguration.tape
        finalConfiguration.tape member
        exactRun'
        terminal
  refine ⟨finalConfiguration.tape, path, ?_⟩
  exact
    represents_at_state (newState := finalState) finalRepresents

/-! ## Closed count blocks -/

private theorem ProgramSafe.singleton
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitive : TargetEmitterPlan.Primitive}
    {initial final : Runtime}
    (safe :
      PrimitiveSafe capacity source context
        primitive initial final) :
    ProgramSafe capacity source context
      [primitive] initial final :=
  .cons primitive [] initial final final safe (.nil final)

private theorem ProgramSafe.append
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {first second : List TargetEmitterPlan.Primitive}
    {initial middle final : Runtime}
    (left :
      ProgramSafe capacity source context
        first initial middle)
    (right :
      ProgramSafe capacity source context
        second middle final) :
    ProgramSafe capacity source context
      (first ++ second) initial final := by
  induction left with
  | nil =>
      exact right
  | cons primitive rest initial next middle head tail ih =>
      exact .cons primitive (rest ++ second)
        initial next final head (ih right)

private theorem resetScratch_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime)
    (bound : runtime.scratch < capacity) :
    ProgramSafe capacity source context [.resetScratch] runtime
      { runtime with scratch := 0 } :=
  ProgramSafe.singleton
    (TargetEmitterRuntimeProgram.PrimitiveSafe.resetScratch
      runtime bound)

private theorem incrementScratch_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime)
    (bound : runtime.scratch < capacity) :
    ProgramSafe capacity source context [.incrementScratch] runtime
      { runtime with scratch := runtime.scratch + 1 } :=
  ProgramSafe.singleton
    (TargetEmitterRuntimeProgram.PrimitiveSafe.incrementScratch
      runtime bound)

private theorem addRegister_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime) (counter : Counter)
    (slot : TargetEmitterLedger.Slot)
    (slotEq : counterSlot counter = some slot)
    (fits : LedgerFits capacity runtime.registers)
    (bound :
      runtime.scratch +
          TargetEmitterLedger.slotValue runtime.registers slot ≤
        capacity) :
    ProgramSafe capacity source context [.addRegister counter] runtime
      { runtime with
        scratch :=
          runtime.scratch +
            TargetEmitterLedger.slotValue runtime.registers slot } :=
  ProgramSafe.singleton
    (TargetEmitterRuntimeProgram.PrimitiveSafe.addRegister
      runtime counter slot slotEq fits bound)

private theorem pushCheck_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (bound : runtime.scratch ≤ capacity) :
    ProgramSafe capacity source context [.pushCheck] runtime
      { runtime with
        checks := runtime.checks ++ [runtime.scratch] } :=
  ProgramSafe.singleton
    (TargetEmitterRuntimeProgram.PrimitiveSafe.pushCheck
      runtime fits bound)

private theorem appendMarked_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source)
    (runtime : Runtime) (token : Token) :
    ProgramSafe capacity source context
      [.append .marked token] runtime
      { runtime with
        targetTokens := runtime.targetTokens ++ [token] } :=
  ProgramSafe.singleton
    (TargetEmitterRuntimeProgram.PrimitiveSafe.appendMarked
      runtime token layout)

private theorem emitScratchMarked_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source)
    (runtime : Runtime)
    (bound : runtime.scratch ≤ capacity) :
    ProgramSafe capacity source context
      [.emitScratchNat .marked] runtime
      { runtime with
        targetTokens :=
          runtime.targetTokens ++
            encodeNatTokens runtime.scratch } :=
  ProgramSafe.singleton
    (TargetEmitterRuntimeProgram.PrimitiveSafe.emitScratchNatMarked
      runtime bound layout)

private theorem incrementRegister_fits
    {capacity : Nat} (slot : TargetEmitterLedger.Slot)
    (registers : TargetEmitter.UnaryRegisters)
    (fits : LedgerFits capacity registers)
    (available :
      TargetEmitterLedger.slotValue registers slot < capacity) :
    LedgerFits capacity
      (TargetEmitterRuntimePrimitives.incrementRegisters
        slot registers) := by
  cases slot <;>
    refine
      { inputCount := ?_
        normalizedGateCount := ?_
        carrierWidth := ?_
        baseline := ?_
        currentGate := ?_
        outputIndex := ?_ } <;>
    simp [TargetEmitterRuntimePrimitives.incrementRegisters,
      TargetEmitterLedger.slotValue] at available ⊢
  all_goals first | exact fits.inputCount
                  | exact fits.normalizedGateCount
                  | exact fits.carrierWidth
                  | exact fits.baseline
                  | exact fits.currentGate
                  | exact fits.outputIndex
                  | omega

private theorem incrementRegister_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime) (counter : Counter)
    (slot : TargetEmitterLedger.Slot)
    (slotEq : counterSlot counter = some slot)
    (fits : LedgerFits capacity runtime.registers)
    (available :
      TargetEmitterLedger.slotValue runtime.registers slot <
        capacity) :
    ProgramSafe capacity source context
      [.incrementRegister counter] runtime
      { runtime with
        registers :=
          TargetEmitterRuntimePrimitives.incrementRegisters
            slot runtime.registers } :=
  ProgramSafe.singleton
    (TargetEmitterRuntimeProgram.PrimitiveSafe.incrementRegister
      runtime counter slot slotEq fits available)

private theorem compiledPrograms_nonempty
    (primitives : List TargetEmitterPlan.Primitive)
    (programs : List WorkMachine)
    (compiled : compileProgram primitives = some programs)
    (primitivesNonempty : primitives ≠ []) :
    programs ≠ [] := by
  cases primitives with
  | nil =>
      exact False.elim (primitivesNonempty rfl)
  | cons primitive rest =>
      cases machineEq : primitiveMachine primitive with
      | none =>
          simp [compileProgram, machineEq] at compiled
      | some machine =>
          cases tailEq : compileProgram rest with
          | none =>
              simp [compileProgram, machineEq, tailEq] at compiled
          | some tail =>
              simp [compileProgram, machineEq, tailEq] at compiled
              subst programs
              simp

private theorem closedBlock_path
    (descriptor : BlockDescriptor)
    (descriptorMember : descriptor ∈ blockDescriptors)
    (finalState : Nat)
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context
        descriptor.primitives initial final)
    (initialScratchBound : initial.scratch ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents
        (blockEntry descriptor.code descriptor.primitives).startState
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
          (.node
            (blockEntry descriptor.code descriptor.primitives))
          descriptor.continuation steps initialTape finalTape ∧
      TapeRepresents finalState
        capacity final.scratch final.registers final.checks
        source final.targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source initial descriptor.primitives := by
  rcases descriptor.closed with ⟨programs, compiled⟩
  have programsNonempty :=
    compiledPrograms_nonempty descriptor.primitives programs
      compiled descriptor.nonempty
  cases programs with
  | nil =>
      contradiction
  | cons first rest =>
      have startEq :
          (blockEntry descriptor.code
              descriptor.primitives).startState =
            TargetEmitterRuntimeProgram.entryState
              0 (first :: rest) := by
        unfold blockEntry blockEntry? blockMachines
        rw [compiled]
        rfl
      rw [startEq] at represents
      let initialActual : WorkConfiguration :=
        { state :=
            TargetEmitterRuntimeProgram.entryState
              0 (first :: rest)
          tape := initialTape }
      have inputRepresents :
          TargetEmitterRuntime.Represents initialActual.state
            capacity initial.scratch initial.registers initial.checks
            source initial.targetTokens initialActual := by
        exact represents
      rcases
          TargetEmitterRuntimeProgramBound.ProgramSafe.linearAcceptRuns_bounded
            safe initialScratchBound (first :: rest) compiled 0
            initialActual inputRepresents with
        ⟨steps, finalConfiguration, runs, finalRepresents, bound⟩
      have included :
          ∀ node,
            node ∈
                blockNodes descriptor.code descriptor.primitives
                  descriptor.continuation →
              node ∈ graph.nodes := by
        intro node nodeMember
        exact
          descriptorBlockNode_member_nodes descriptor descriptorMember
            node nodeMember
      have rawPath :=
        blockNodes_acceptPath_of_compiled graph descriptor.code
          descriptor.primitives (first :: rest)
          descriptor.continuation steps initialTape
          finalConfiguration.tape compiled included runs
      have entryEq :=
        blockEntry_eq_entryEndpoint_of_compiled descriptor.code
          descriptor.primitives (first :: rest)
          descriptor.continuation compiled (by simp)
      have path :
          AcceptPath graph
            (.node
              (blockEntry descriptor.code descriptor.primitives))
            descriptor.continuation steps initialTape
            finalConfiguration.tape := by
        rw [← entryEq] at rawPath
        exact rawPath
      refine
        ⟨steps, finalConfiguration.tape, path, ?_, bound⟩
      exact
        represents_at_state (newState := finalState)
          finalRepresents

private theorem indexedBlock_path
    (index : Nat) (bound : index < blockDescriptors.length)
    (finalState : Nat)
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context
        blockDescriptors[index].primitives initial final)
    (initialScratchBound : initial.scratch ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents
        (blockEntry blockDescriptors[index].code
          blockDescriptors[index].primitives).startState
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
          (.node
            (blockEntry blockDescriptors[index].code
              blockDescriptors[index].primitives))
          blockDescriptors[index].continuation
          steps initialTape finalTape ∧
      TapeRepresents finalState
        capacity final.scratch final.registers final.checks
        source final.targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source initial
          blockDescriptors[index].primitives := by
  exact
    closedBlock_path blockDescriptors[index]
      (List.getElem_mem bound) finalState safe
      initialScratchBound initialTape represents

/-- Logical first-pass runtime after counting `width` header units and
`gateCount` compiler gates.  The count pass emits no target token and keeps
the physical check stack empty. -/
def countRuntime (formula : CNFFormula)
    (width gateCount scratch : Nat) : Runtime :=
  { captured := 0
    scratch := scratch
    registers := countedRegisters formula width gateCount
    checks := []
    targetTokens := [] }

@[simp] theorem countRuntime_scratch
    (formula : CNFFormula) (width gateCount scratch : Nat) :
    (countRuntime formula width gateCount scratch).scratch =
      scratch := by
  rfl

@[simp] theorem countRuntime_registers
    (formula : CNFFormula) (width gateCount scratch : Nat) :
    (countRuntime formula width gateCount scratch).registers =
      countedRegisters formula width gateCount := by
  rfl

@[simp] theorem countRuntime_checks
    (formula : CNFFormula) (width gateCount scratch : Nat) :
    (countRuntime formula width gateCount scratch).checks = [] := by
  rfl

@[simp] theorem countRuntime_targetTokens
    (formula : CNFFormula) (width gateCount scratch : Nat) :
    (countRuntime formula width gateCount scratch).targetTokens = [] := by
  rfl

theorem countRuntime_initial (formula : CNFFormula) :
    countRuntime formula 0 0 0 =
      { captured := 0
        scratch := 0
        registers := CNFToNANDWorkspace.postLedgerRegisters formula
        checks := []
        targetTokens := [] } := by
  simp [countRuntime, countedRegisters_zero]

private theorem countWidth_safe
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (width gateCount scratch : Nat)
    (widthLt : width < formula.variableCount)
    (gateBound :
      gateCount ≤ CNFToNANDWorkspace.compilerGateCount formula) :
    ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
      countWidthUnitProgram
      (countRuntime formula width gateCount scratch)
      (countRuntime formula (width + 1) gateCount scratch) := by
  have fits :=
    countedRegisters_fits formula width gateCount
      (Nat.le_of_lt widthLt) gateBound
  have available :
      TargetEmitterLedger.slotValue
          (countedRegisters formula width gateCount)
          .inputCount <
        CNFToNANDWorkspace.capacity formula := by
    simp [TargetEmitterLedger.slotValue]
    have capacityBound :=
      CNFToNANDWorkspace.variableCount_le_capacity formula
    omega
  have safe :=
    incrementRegister_safe
      (context := context)
      (countRuntime formula width gateCount scratch)
      .inputCount .inputCount rfl fits available
  simpa [countWidthUnitProgram, countRuntime,
    countedRegisters,
    TargetEmitterRuntimePrimitives.incrementRegisters] using safe

private theorem countClause_safe
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (gateCount scratch : Nat)
    (gateBound :
      gateCount + 2 ≤
        CNFToNANDWorkspace.compilerGateCount formula) :
    ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
      countClauseProgram
      (countRuntime formula formula.variableCount gateCount scratch)
      (countRuntime formula formula.variableCount
        (gateCount + 2) scratch) := by
  let first :=
    countRuntime formula formula.variableCount
      (gateCount + 1) scratch
  have initialFits :=
    countedRegisters_fits formula formula.variableCount gateCount
      (by omega) (by omega)
  have firstAvailable :
      TargetEmitterLedger.slotValue
          (countedRegisters formula formula.variableCount gateCount)
          .currentGate <
        CNFToNANDWorkspace.capacity formula := by
    simp [TargetEmitterLedger.slotValue]
    have capacityBound :=
      CNFToNANDWorkspace.compilerGateCount_lt_capacity formula
    omega
  have firstSafe :=
    incrementRegister_safe
      (context := context)
      (countRuntime formula formula.variableCount gateCount scratch)
      .currentGate .currentGate rfl initialFits firstAvailable
  have firstFits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        first.registers := by
    simpa [first, countRuntime, countedRegisters,
      TargetEmitterRuntimePrimitives.incrementRegisters] using
      incrementRegister_fits .currentGate
        (countedRegisters formula formula.variableCount gateCount)
        initialFits firstAvailable
  have secondAvailable :
      TargetEmitterLedger.slotValue first.registers .currentGate <
        CNFToNANDWorkspace.capacity formula := by
    simp [first, countRuntime, countedRegisters,
      TargetEmitterLedger.slotValue]
    have capacityBound :=
      CNFToNANDWorkspace.compilerGateCount_lt_capacity formula
    omega
  have secondSafe :=
    incrementRegister_safe
      (context := context) first
      .currentGate .currentGate rfl firstFits secondAvailable
  have all := firstSafe.append secondSafe
  simpa [countClauseProgram, repeatPrimitive,
    first, countRuntime, countedRegisters,
    TargetEmitterRuntimePrimitives.incrementRegisters,
    List.append_assoc, Nat.add_assoc] using all

private theorem countLiteral_safe
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (gateCount scratch : Nat)
    (gateBound :
      gateCount + 3 ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula) :
    ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
      Blocks.countNegativeSignProgram
      (countRuntime formula formula.variableCount gateCount scratch)
      (countRuntime formula formula.variableCount
        (gateCount + 3) 0) := by
  let first :=
    countRuntime formula formula.variableCount
      (gateCount + 1) scratch
  let second :=
    countRuntime formula formula.variableCount
      (gateCount + 2) scratch
  let third :=
    countRuntime formula formula.variableCount
      (gateCount + 3) scratch
  have initialFits :=
    countedRegisters_fits formula formula.variableCount gateCount
      (by omega) (by omega)
  have firstAvailable :
      TargetEmitterLedger.slotValue
          (countedRegisters formula formula.variableCount gateCount)
          .currentGate <
        CNFToNANDWorkspace.capacity formula := by
    simp [TargetEmitterLedger.slotValue]
    have capacityBound :=
      CNFToNANDWorkspace.compilerGateCount_lt_capacity formula
    omega
  have firstSafe :=
    incrementRegister_safe
      (context := context)
      (countRuntime formula formula.variableCount gateCount scratch)
      .currentGate .currentGate rfl initialFits firstAvailable
  have firstFits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        first.registers := by
    simpa [first, countRuntime, countedRegisters,
      TargetEmitterRuntimePrimitives.incrementRegisters] using
      incrementRegister_fits .currentGate
        (countedRegisters formula formula.variableCount gateCount)
        initialFits firstAvailable
  have secondAvailable :
      TargetEmitterLedger.slotValue first.registers .currentGate <
        CNFToNANDWorkspace.capacity formula := by
    simp [first, countRuntime, countedRegisters,
      TargetEmitterLedger.slotValue]
    have capacityBound :=
      CNFToNANDWorkspace.compilerGateCount_lt_capacity formula
    omega
  have secondSafe :=
    incrementRegister_safe
      (context := context) first
      .currentGate .currentGate rfl firstFits secondAvailable
  have secondFits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        second.registers := by
    simpa [first, second, countRuntime, countedRegisters,
      TargetEmitterRuntimePrimitives.incrementRegisters] using
      incrementRegister_fits .currentGate first.registers
        firstFits secondAvailable
  have thirdAvailable :
      TargetEmitterLedger.slotValue second.registers .currentGate <
        CNFToNANDWorkspace.capacity formula := by
    simp [second, countRuntime, countedRegisters,
      TargetEmitterLedger.slotValue]
    have capacityBound :=
      CNFToNANDWorkspace.compilerGateCount_lt_capacity formula
    omega
  have thirdSafe :=
    incrementRegister_safe
      (context := context) second
      .currentGate .currentGate rfl secondFits thirdAvailable
  have resetSafe :=
    resetScratch_safe (context := context) third (by
      simpa [third, countRuntime] using scratchBound)
  have all :=
    firstSafe.append
      (secondSafe.append (thirdSafe.append resetSafe))
  simpa [Blocks.countNegativeSignProgram,
    countLiteralProgram, resetLiteralIndexProgram,
    repeatPrimitive, first, second, third,
    countRuntime, countedRegisters,
    TargetEmitterRuntimePrimitives.incrementRegisters,
    List.append_assoc, Nat.add_assoc] using all

private theorem countPositiveLiteral_safe
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (gateCount scratch : Nat)
    (gateBound :
      gateCount + 3 ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula) :
    ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
      Blocks.countPositiveSignProgram
      (countRuntime formula formula.variableCount gateCount scratch)
      (countRuntime formula formula.variableCount
        (gateCount + 3) 0) := by
  simpa [Blocks.countPositiveSignProgram,
    Blocks.countNegativeSignProgram] using
    countLiteral_safe (context := context)
      formula gateCount scratch gateBound scratchBound

private theorem countValidNegative_safe
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (gateCount scratch : Nat)
    (gateBound :
      gateCount + 1 ≤
        CNFToNANDWorkspace.compilerGateCount formula) :
    ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
      countValidNegativeProgram
      (countRuntime formula formula.variableCount gateCount scratch)
      (countRuntime formula formula.variableCount
        (gateCount + 1) scratch) := by
  have fits :=
    countedRegisters_fits formula formula.variableCount gateCount
      (by omega) (by omega)
  have available :
      TargetEmitterLedger.slotValue
          (countedRegisters formula formula.variableCount gateCount)
          .currentGate <
        CNFToNANDWorkspace.capacity formula := by
    simp [TargetEmitterLedger.slotValue]
    have capacityBound :=
      CNFToNANDWorkspace.compilerGateCount_lt_capacity formula
    omega
  have safe :=
    incrementRegister_safe
      (context := context)
      (countRuntime formula formula.variableCount gateCount scratch)
      .currentGate .currentGate rfl fits available
  simpa [countValidNegativeProgram, countRuntime,
    countedRegisters,
    TargetEmitterRuntimePrimitives.incrementRegisters] using safe

private theorem countAdvanceLiteral_safe
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (gateCount scratch : Nat)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula) :
    ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
      advanceLiteralIndexProgram
      (countRuntime formula formula.variableCount gateCount scratch)
      (countRuntime formula formula.variableCount
        gateCount (scratch + 1)) := by
  simpa [advanceLiteralIndexProgram, countRuntime] using
    incrementScratch_safe
      (context := context)
      (countRuntime formula formula.variableCount gateCount scratch)
      scratchBound

private theorem countEmptyFormula_safe
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (empty : formula.clauses = []) :
    ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
      countEmptyFormulaProgram
      (countRuntime formula formula.variableCount 0 0)
      (countRuntime formula formula.variableCount 1 0) := by
  have compilerCount :
      CNFToNANDWorkspace.compilerGateCount formula = 1 := by
    rw [compilerGateCount_eq_count_charge]
    simp [empty, clausesGateCharge]
  have fits :=
    countedRegisters_fits formula formula.variableCount 0
      (by omega) (by simp)
  have available :
      TargetEmitterLedger.slotValue
          (countedRegisters formula formula.variableCount 0)
          .currentGate <
        CNFToNANDWorkspace.capacity formula := by
    simp [TargetEmitterLedger.slotValue]
    exact Nat.zero_lt_of_lt
      (CNFToNANDWorkspace.compilerGateCount_lt_capacity formula)
  have safe :=
    incrementRegister_safe
      (context := context)
      (countRuntime formula formula.variableCount 0 0)
      .currentGate .currentGate rfl fits available
  simpa [countEmptyFormulaProgram, countRuntime,
    countedRegisters,
    TargetEmitterRuntimePrimitives.incrementRegisters] using safe

/-- Deterministic envelope attached to one physical count block. -/
def countBlockEnvelope (formula : CNFFormula)
    (source : List WorkSymbol) (runtime : Runtime)
    (primitives : List TargetEmitterPlan.Primitive) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (CNFToNANDWorkspace.capacity formula)
    source runtime primitives

theorem count_width_block_path
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (width gateCount scratch : Nat)
    (widthLt : width < formula.variableCount)
    (gateBound :
      gateCount ≤ CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch ≤ CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents countWidthRef.startState
        (CNFToNANDWorkspace.capacity formula)
        scratch (countedRegisters formula width gateCount) []
        source [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node countWidthRef)
        (.node (restoreRef .count .header .t))
        steps initialTape finalTape ∧
      TapeRepresents (restoreRef .count .header .t).startState
        (CNFToNANDWorkspace.capacity formula)
        scratch (countedRegisters formula (width + 1) gateCount) []
        source [] finalTape ∧
      steps ≤ countBlockEnvelope formula source
        (countRuntime formula width gateCount scratch)
        countWidthUnitProgram := by
  have safe :=
    countWidth_safe (context := context)
      formula width gateCount scratch widthLt gateBound
  have input :
      TapeRepresents
        (blockEntry blockDescriptors[1].code
          blockDescriptors[1].primitives).startState
        (CNFToNANDWorkspace.capacity formula)
        (countRuntime formula width gateCount scratch).scratch
        (countRuntime formula width gateCount scratch).registers
        (countRuntime formula width gateCount scratch).checks
        source
        (countRuntime formula width gateCount scratch).targetTokens
        initialTape := by
    simpa [blockDescriptors, countWidthRef, countRuntime] using
      represents
  rcases indexedBlock_path 1 (by decide)
      (restoreRef .count .header .t).startState
      safe (by simpa [countRuntime] using scratchBound)
      initialTape input with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape,
      by simpa [blockDescriptors, countWidthRef] using path,
      by simpa [countRuntime] using finalRepresents,
      by simpa [countBlockEnvelope, blockDescriptors] using bound⟩

theorem count_clause_block_path
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (gateCount scratch : Nat)
    (gateBound :
      gateCount + 2 ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch ≤ CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents countClauseRef.startState
        (CNFToNANDWorkspace.capacity formula)
        scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node countClauseRef)
        (.node (restoreRef .count .clause .sep))
        steps initialTape finalTape ∧
      TapeRepresents (restoreRef .count .clause .sep).startState
        (CNFToNANDWorkspace.capacity formula)
        scratch
        (countedRegisters formula formula.variableCount
          (gateCount + 2)) []
        source [] finalTape ∧
      steps ≤ countBlockEnvelope formula source
        (countRuntime formula formula.variableCount
          gateCount scratch)
        countClauseProgram := by
  have safe :=
    countClause_safe (context := context)
      formula gateCount scratch gateBound
  have input :
      TapeRepresents
        (blockEntry blockDescriptors[2].code
          blockDescriptors[2].primitives).startState
        (CNFToNANDWorkspace.capacity formula)
        (countRuntime formula formula.variableCount
          gateCount scratch).scratch
        (countRuntime formula formula.variableCount
          gateCount scratch).registers
        (countRuntime formula formula.variableCount
          gateCount scratch).checks
        source
        (countRuntime formula formula.variableCount
          gateCount scratch).targetTokens
        initialTape := by
    simpa [blockDescriptors, countClauseRef, countRuntime] using
      represents
  rcases indexedBlock_path 2 (by decide)
      (restoreRef .count .clause .sep).startState
      safe (by simpa [countRuntime] using scratchBound)
      initialTape input with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape,
      by simpa [blockDescriptors, countClauseRef] using path,
      by simpa [countRuntime] using finalRepresents,
      by simpa [countBlockEnvelope, blockDescriptors] using bound⟩

theorem count_negative_sign_block_path
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (gateCount scratch : Nat)
    (gateBound :
      gateCount + 3 ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents countNegativeSignRef.startState
        (CNFToNANDWorkspace.capacity formula)
        scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node countNegativeSignRef)
        (.node (literalCompareRef .count .clause .f))
        steps initialTape finalTape ∧
      TapeRepresents
        (literalCompareRef .count .clause .f).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        source [] finalTape ∧
      steps ≤ countBlockEnvelope formula source
        (countRuntime formula formula.variableCount
          gateCount scratch)
        Blocks.countNegativeSignProgram := by
  have safe :=
    countLiteral_safe (context := context)
      formula gateCount scratch gateBound scratchBound
  have input :
      TapeRepresents
        (blockEntry blockDescriptors[4].code
          blockDescriptors[4].primitives).startState
        (CNFToNANDWorkspace.capacity formula)
        (countRuntime formula formula.variableCount
          gateCount scratch).scratch
        (countRuntime formula formula.variableCount
          gateCount scratch).registers
        (countRuntime formula formula.variableCount
          gateCount scratch).checks
        source
        (countRuntime formula formula.variableCount
          gateCount scratch).targetTokens
        initialTape := by
    simpa [blockDescriptors, countNegativeSignRef,
      countRuntime] using represents
  rcases indexedBlock_path 4 (by decide)
      (literalCompareRef .count .clause .f).startState
      safe (Nat.le_of_lt scratchBound) initialTape input with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape,
      by simpa [blockDescriptors, countNegativeSignRef] using path,
      by simpa [countRuntime] using finalRepresents,
      by simpa [countBlockEnvelope, blockDescriptors] using bound⟩

theorem count_positive_sign_block_path
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (gateCount scratch : Nat)
    (gateBound :
      gateCount + 3 ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents countPositiveSignRef.startState
        (CNFToNANDWorkspace.capacity formula)
        scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node countPositiveSignRef)
        (.node (literalCompareRef .count .clause .t))
        steps initialTape finalTape ∧
      TapeRepresents
        (literalCompareRef .count .clause .t).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        source [] finalTape ∧
      steps ≤ countBlockEnvelope formula source
        (countRuntime formula formula.variableCount
          gateCount scratch)
        Blocks.countPositiveSignProgram := by
  have safe :=
    countPositiveLiteral_safe (context := context)
      formula gateCount scratch gateBound scratchBound
  have input :
      TapeRepresents
        (blockEntry blockDescriptors[5].code
          blockDescriptors[5].primitives).startState
        (CNFToNANDWorkspace.capacity formula)
        (countRuntime formula formula.variableCount
          gateCount scratch).scratch
        (countRuntime formula formula.variableCount
          gateCount scratch).registers
        (countRuntime formula formula.variableCount
          gateCount scratch).checks
        source
        (countRuntime formula formula.variableCount
          gateCount scratch).targetTokens
        initialTape := by
    simpa [blockDescriptors, countPositiveSignRef,
      countRuntime] using represents
  rcases indexedBlock_path 5 (by decide)
      (literalCompareRef .count .clause .t).startState
      safe (Nat.le_of_lt scratchBound) initialTape input with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape,
      by simpa [blockDescriptors, countPositiveSignRef] using path,
      by simpa [countRuntime] using finalRepresents,
      by simpa [countBlockEnvelope, blockDescriptors] using bound⟩

theorem count_valid_negative_block_path
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (gateCount scratch : Nat)
    (gateBound :
      gateCount + 1 ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch ≤ CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents countValidNegativeRef.startState
        (CNFToNANDWorkspace.capacity formula)
        scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node countValidNegativeRef)
        (.node (restoreRef .count .clause .f))
        steps initialTape finalTape ∧
      TapeRepresents (restoreRef .count .clause .f).startState
        (CNFToNANDWorkspace.capacity formula)
        scratch
        (countedRegisters formula formula.variableCount
          (gateCount + 1)) []
        source [] finalTape ∧
      steps ≤ countBlockEnvelope formula source
        (countRuntime formula formula.variableCount
          gateCount scratch)
        countValidNegativeProgram := by
  have safe :=
    countValidNegative_safe (context := context)
      formula gateCount scratch gateBound
  have input :
      TapeRepresents
        (blockEntry blockDescriptors[6].code
          blockDescriptors[6].primitives).startState
        (CNFToNANDWorkspace.capacity formula)
        (countRuntime formula formula.variableCount
          gateCount scratch).scratch
        (countRuntime formula formula.variableCount
          gateCount scratch).registers
        (countRuntime formula formula.variableCount
          gateCount scratch).checks
        source
        (countRuntime formula formula.variableCount
          gateCount scratch).targetTokens
        initialTape := by
    simpa [blockDescriptors, countValidNegativeRef,
      countRuntime] using represents
  rcases indexedBlock_path 6 (by decide)
      (restoreRef .count .clause .f).startState
      safe (by simpa [countRuntime] using scratchBound)
      initialTape input with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape,
      by simpa [blockDescriptors, countValidNegativeRef] using path,
      by simpa [countRuntime] using finalRepresents,
      by simpa [countBlockEnvelope, blockDescriptors] using bound⟩

theorem count_advance_literal_block_path
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (positive : Bool)
    (gateCount scratch : Nat)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (advanceLiteralRef .count positive).startState
        (CNFToNANDWorkspace.capacity formula)
        scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (advanceLiteralRef .count positive))
        (.node
          (restoreRef .count (inRangeState positive) .t))
        steps initialTape finalTape ∧
      TapeRepresents
        (restoreRef .count (inRangeState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula)
        (scratch + 1)
        (countedRegisters formula formula.variableCount gateCount) []
        source [] finalTape ∧
      steps ≤ countBlockEnvelope formula source
        (countRuntime formula formula.variableCount
          gateCount scratch)
        advanceLiteralIndexProgram := by
  have safe :=
    countAdvanceLiteral_safe (context := context)
      formula gateCount scratch scratchBound
  cases positive with
  | false =>
      have input :
          TapeRepresents
            (blockEntry blockDescriptors[8].code
              blockDescriptors[8].primitives).startState
            (CNFToNANDWorkspace.capacity formula)
            (countRuntime formula formula.variableCount
              gateCount scratch).scratch
            (countRuntime formula formula.variableCount
              gateCount scratch).registers
            (countRuntime formula formula.variableCount
              gateCount scratch).checks
            source
            (countRuntime formula formula.variableCount
              gateCount scratch).targetTokens
            initialTape := by
        simpa [blockDescriptors, advanceLiteralRef,
          countAdvanceNegativeRef, countRuntime] using represents
      rcases indexedBlock_path 8 (by decide)
          (restoreRef .count .negative .t).startState
          safe (Nat.le_of_lt scratchBound) initialTape input with
        ⟨steps, finalTape, path, finalRepresents, bound⟩
      exact
        ⟨steps, finalTape,
          by simpa [blockDescriptors, advanceLiteralRef,
            countAdvanceNegativeRef, inRangeState] using path,
          by simpa [countRuntime, inRangeState] using
            finalRepresents,
          by simpa [countBlockEnvelope, blockDescriptors] using
            bound⟩
  | true =>
      have input :
          TapeRepresents
            (blockEntry blockDescriptors[7].code
              blockDescriptors[7].primitives).startState
            (CNFToNANDWorkspace.capacity formula)
            (countRuntime formula formula.variableCount
              gateCount scratch).scratch
            (countRuntime formula formula.variableCount
              gateCount scratch).registers
            (countRuntime formula formula.variableCount
              gateCount scratch).checks
            source
            (countRuntime formula formula.variableCount
              gateCount scratch).targetTokens
            initialTape := by
        simpa [blockDescriptors, advanceLiteralRef,
          countAdvancePositiveRef, countRuntime] using represents
      rcases indexedBlock_path 7 (by decide)
          (restoreRef .count .positive .t).startState
          safe (Nat.le_of_lt scratchBound) initialTape input with
        ⟨steps, finalTape, path, finalRepresents, bound⟩
      exact
        ⟨steps, finalTape,
          by simpa [blockDescriptors, advanceLiteralRef,
            countAdvancePositiveRef, inRangeState] using path,
          by simpa [countRuntime, inRangeState] using
            finalRepresents,
          by simpa [countBlockEnvelope, blockDescriptors] using
            bound⟩

theorem count_empty_formula_block_path
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) (empty : formula.clauses = [])
    (initialTape : WorkTape)
    (represents :
      TapeRepresents countEmptyFormulaRef.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount 0) []
        source [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node countEmptyFormulaRef)
        (.node emittedHeaderRef)
        steps initialTape finalTape ∧
      TapeRepresents emittedHeaderRef.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount 1) []
        source [] finalTape ∧
      steps ≤ countBlockEnvelope formula source
        (countRuntime formula formula.variableCount 0 0)
        countEmptyFormulaProgram := by
  have safe :=
    countEmptyFormula_safe (context := context) formula empty
  have input :
      TapeRepresents
        (blockEntry blockDescriptors[3].code
          blockDescriptors[3].primitives).startState
        (CNFToNANDWorkspace.capacity formula)
        (countRuntime formula formula.variableCount 0 0).scratch
        (countRuntime formula formula.variableCount 0 0).registers
        (countRuntime formula formula.variableCount 0 0).checks
        source
        (countRuntime formula formula.variableCount 0 0).targetTokens
        initialTape := by
    simpa [blockDescriptors, countEmptyFormulaRef,
      countRuntime] using represents
  rcases indexedBlock_path 3 (by decide)
      emittedHeaderRef.startState safe (by simp [countRuntime])
      initialTape input with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape,
      by simpa [blockDescriptors, countEmptyFormulaRef] using path,
      by simpa [countRuntime] using finalRepresents,
      by simpa [countBlockEnvelope, blockDescriptors] using bound⟩

/-! ## Structural count traversal -/

private def directTokenStepEnvelope
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken) : Nat :=
  tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed token +
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed token

private theorem count_direct_token_step_path
    (formula : CNFFormula)
    (processed : List CNFToken) (token next : CNFToken)
    (tail : List CNFToken)
    (startState restoreState : GrammarState)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ token :: next :: tail)
    (active : startState ∈ activeGrammarStates)
    (valid : validGrammarToken startState token = true)
    (installed :
      postInstallEndpoint .count startState token =
        .node (restoreRef .count restoreState token))
    (notFinished : stateFinishKind? restoreState = none)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .count startState).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells token (next :: tail))
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .count startState))
        (.node (firstBitRef .count restoreState))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .count restoreState).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [token]))
        (scanAfterCells next tail)
        runtime.targetTokens finalTape ∧
      steps ≤ directTokenStepEnvelope formula processed token := by
  rcases
      token_read_install_path .count formula processed token
        (next :: tail) startState runtime tokens active valid
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have restoreRepresents :
      TapeRepresents
        (restoreRef .count restoreState token).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token (next :: tail))
        runtime.targetTokens installedTape := by
    change
      TargetEmitterRuntime.Represents
        (restoreRef .count restoreState token).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token (next :: tail))
        runtime.targetTokens
        { state :=
            (restoreRef .count restoreState token).startState
          tape := installedTape }
    exact
      represents_at_state
        (newState :=
          (restoreRef .count restoreState token).startState)
        installedRepresents
  rcases
      token_restore_advance_next_path .count formula
        processed token next tail restoreState runtime tokens
        notFinished installedTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  refine
    ⟨tokenReadInstallSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token +
        tokenRestoreAdvanceSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph
        (.node (firstBitRef .count startState))
        (.node (restoreRef .count restoreState token))
        (.node (firstBitRef .count restoreState))
        _ _ initialTape installedTape finalTape
        (by simpa [installed] using installPath)
        restorePath
  · exact Nat.le_refl _

private def countFinishStepEnvelope
    (formula : CNFFormula) (processed : List CNFToken) : Nat :=
  tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .finish +
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .finish

private theorem count_finish_path
    (formula : CNFFormula) (processed : List CNFToken)
    (startState restoreState : GrammarState) (kind : FinishKind)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ [.finish])
    (active : startState ∈ activeGrammarStates)
    (valid : validGrammarToken startState .finish = true)
    (installed :
      postInstallEndpoint .count startState .finish =
        .node (restoreRef .count restoreState .finish))
    (finished : stateFinishKind? restoreState = some kind)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .count startState).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .finish [])
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .count startState))
        (.node (programEndRef .count kind))
        steps initialTape finalTape ∧
      ScanRepresents (programEndRef .count kind).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.finish]))
        carrierFooterCells runtime.targetTokens finalTape ∧
      steps ≤ countFinishStepEnvelope formula processed := by
  rcases
      token_read_install_path .count formula processed .finish
        [] startState runtime tokens active valid
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have restoreRepresents :
      TapeRepresents
        (restoreRef .count restoreState .finish).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .finish [])
        runtime.targetTokens installedTape := by
    change
      TargetEmitterRuntime.Represents
        (restoreRef .count restoreState .finish).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .finish [])
        runtime.targetTokens
        { state :=
            (restoreRef .count restoreState .finish).startState
          tape := installedTape }
    exact
      represents_at_state
        (newState :=
          (restoreRef .count restoreState .finish).startState)
        installedRepresents
  rcases
      token_restore_advance_end_path .count formula processed .finish
        restoreState kind runtime tokens finished
        installedTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  refine
    ⟨tokenReadInstallSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .finish +
        tokenRestoreAdvanceSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .finish,
      finalTape,
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        (by simpa [installed] using installPath)
        restorePath,
      finalRepresents, ?_⟩
  exact Nat.le_refl _

private def countClauseSeparatorStepEnvelope
    (formula : CNFFormula) (processed : List CNFToken)
    (next : CNFToken) (tail : List CNFToken)
    (gateCount scratch : Nat) : Nat :=
  tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .sep +
    countBlockEnvelope formula
      (markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        processed .sep (next :: tail))
      (countRuntime formula formula.variableCount gateCount scratch)
      countClauseProgram +
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .sep

private theorem count_clause_separator_step_path
    (formula : CNFFormula)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (state : GrammarState)
    (gateCount scratch : Nat)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .sep :: next :: tail)
    (active : state ∈ activeGrammarStates)
    (valid : validGrammarToken state .sep = true)
    (installed :
      postInstallEndpoint .count state .sep =
        .node countClauseRef)
    (gateBound :
      gateCount + 2 ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .count state).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .sep (next :: tail)) []
        initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .count state))
        (.node (firstBitRef .count .clause))
        steps initialTape finalTape ∧
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount
          (gateCount + 2)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.sep]))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countClauseSeparatorStepEnvelope
          formula processed next tail gateCount scratch := by
  rcases
      token_read_install_path .count formula processed .sep
        (next :: tail) state
        (countRuntime formula formula.variableCount gateCount scratch)
        tokens active valid initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  let context :=
    markedSourceContext formula processed .sep (next :: tail) tokens
  have blockRepresents :
      TapeRepresents countClauseRef.startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .sep (next :: tail))
        [] installedTape := by
    change
      TargetEmitterRuntime.Represents countClauseRef.startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .sep (next :: tail))
        [] { state := countClauseRef.startState
             tape := installedTape }
    exact
      represents_at_state (newState := countClauseRef.startState)
        installedRepresents
  rcases
      count_clause_block_path (context := context)
        formula gateCount scratch gateBound
        (Nat.le_of_lt scratchBound)
        installedTape blockRepresents with
    ⟨blockSteps, blockTape, blockPath, blockRepresents,
      blockBound⟩
  rcases
      token_restore_advance_next_path .count formula
        processed .sep next tail .clause
        (countRuntime formula formula.variableCount
          (gateCount + 2) scratch)
        tokens (by decide) blockTape blockRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .sep
  let restoreSteps :=
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .sep
  have throughBlock :
      AcceptPath graph (.node (firstBitRef .count state))
        (.node (restoreRef .count .clause .sep))
        (installSteps + blockSteps)
        initialTape blockTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      (by simpa [installSteps, installed] using installPath)
      blockPath
  refine
    ⟨installSteps + blockSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughBlock restorePath
  · unfold countClauseSeparatorStepEnvelope
    dsimp [installSteps, restoreSteps]
    omega

private def signToken (positive : Bool) : CNFToken :=
  if positive then .t else .f

private def countSignRef (positive : Bool) : NodeRef :=
  if positive then countPositiveSignRef else countNegativeSignRef

private def countSignPrimitives
    (positive : Bool) : List TargetEmitterPlan.Primitive :=
  if positive then Blocks.countPositiveSignProgram
  else Blocks.countNegativeSignProgram

private theorem countSignBlock_path
    (formula : CNFFormula) (positive : Bool)
    {source : List WorkSymbol} {context : SourceContext source}
    (gateCount scratch : Nat)
    (gateBound :
      gateCount + 3 ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (countSignRef positive).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (countSignRef positive))
        (.node
          (literalCompareRef .count .clause
            (signToken positive)))
        steps initialTape finalTape ∧
      TapeRepresents
        (literalCompareRef .count .clause
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        source [] finalTape ∧
      steps ≤ countBlockEnvelope formula source
        (countRuntime formula formula.variableCount
          gateCount scratch)
        (countSignPrimitives positive) := by
  cases positive with
  | false =>
      simpa [countSignRef, signToken, countSignPrimitives] using
        (count_negative_sign_block_path
          (context := context) formula gateCount scratch
          gateBound scratchBound initialTape
          (by simpa [countSignRef] using represents))
  | true =>
      simpa [countSignRef, signToken, countSignPrimitives] using
        (count_positive_sign_block_path
          (context := context) formula gateCount scratch
          gateBound scratchBound initialTape
          (by simpa [countSignRef] using represents))

private def countSignStepEnvelope
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat) : Nat :=
  tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula)
      processed (signToken positive) +
    countBlockEnvelope formula
      (markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        processed (signToken positive) (next :: tail))
      (countRuntime formula formula.variableCount
        gateCount scratch)
      (countSignPrimitives positive) +
    literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) 0 +
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula)
      processed (signToken positive)

private theorem count_sign_zero_width_step_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (widthZero : formula.variableCount = 0)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ signToken positive :: next :: tail)
    (gateBound :
      gateCount + 3 ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells (signToken positive) (next :: tail)) []
        initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .count .clause))
        (.node
          (firstBitRef .count (overflowState positive)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .count (overflowState positive)).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [signToken positive]))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countSignStepEnvelope formula positive processed
          next tail gateCount scratch := by
  rcases
      token_read_install_path .count formula processed
        (signToken positive) (next :: tail) .clause
        (countRuntime formula formula.variableCount
          gateCount scratch)
        tokens (by simp [activeGrammarStates])
        (by cases positive <;> decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed (signToken positive) (next :: tail)
  let context :=
    markedSourceContext formula processed (signToken positive)
      (next :: tail) tokens
  have blockRepresents :
      TapeRepresents (countSignRef positive).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] installedTape := by
    change
      TargetEmitterRuntime.Represents
        (countSignRef positive).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] { state := (countSignRef positive).startState
                    tape := installedTape }
    exact
      represents_at_state
        (newState := (countSignRef positive).startState)
        installedRepresents
  rcases
      countSignBlock_path (context := context)
        formula positive gateCount scratch gateBound scratchBound
        installedTape blockRepresents with
    ⟨blockSteps, compareTape, blockPath, compareRepresents,
      blockBound⟩
  let sourceTail := source.tail
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail :=
    context.source_eq
  have compareRepresents' :
      TapeRepresents
        (literalCompareRef .count .clause
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        (SourceParser.cell00 :: sourceTail) [] compareTape := by
    change
      TapeRepresents
        (literalCompareRef .count .clause
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        source [] compareTape at compareRepresents
    rw [sourceEq] at compareRepresents
    exact compareRepresents
  have fits :=
    countedRegisters_fits formula formula.variableCount
      (gateCount + 3) (by simp) (Nat.le_trans gateBound
        (by omega))
  have compareMember :
      controlNode
          (Address.literalCompare .count .clause
            (signToken positive))
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          (.node
            (restoreRef .count (overflowState positive)
              (signToken positive)))
          (.node
            (restoreRef .count (inRangeState positive)
              (signToken positive))) ∈
        graph.nodes := by
    cases positive with
    | false =>
        simpa [signCompareNode, signToken,
          literalCompareRef, controlRef] using
          signCompareNode_member .count false
    | true =>
        simpa [signCompareNode, signToken,
          literalCompareRef, controlRef] using
          signCompareNode_member .count true
  rcases
      literal_compare_equal_path
        (Address.literalCompare .count .clause
          (signToken positive))
        (.node
          (restoreRef .count (overflowState positive)
            (signToken positive)))
        (.node
          (restoreRef .count (inRangeState positive)
            (signToken positive)))
        (restoreRef .count (overflowState positive)
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        SourceParser.cell00 sourceTail [] compareTape
        compareMember
        fits
        (by
          simp [widthZero, countedRegisters,
            TargetEmitterLedger.slotValue])
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents' with
    ⟨restoreTape, comparePath, restoreRepresents'⟩
  have restoreRepresents :
      TapeRepresents
        (restoreRef .count (overflowState positive)
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        source [] restoreTape := by
    rw [sourceEq]
    exact restoreRepresents'
  rcases
      token_restore_advance_next_path .count formula
        processed (signToken positive) next tail
        (overflowState positive)
        (countRuntime formula formula.variableCount
          (gateCount + 3) 0)
        tokens
        (by cases positive <;> decide)
        restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula)
      processed (signToken positive)
  let compareSteps :=
    literalCompareSteps (CNFToNANDWorkspace.capacity formula) 0
  let restoreSteps :=
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula)
      processed (signToken positive)
  have throughBlock :
      AcceptPath graph (.node (firstBitRef .count .clause))
        (.node
          (literalCompareRef .count .clause
            (signToken positive)))
        (installSteps + blockSteps)
        initialTape compareTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      (by
        cases positive <;>
          simpa [installSteps, signToken, countSignRef,
            postInstallEndpoint] using installPath)
      blockPath
  have throughCompare :
      AcceptPath graph (.node (firstBitRef .count .clause))
        (.node
          (restoreRef .count (overflowState positive)
            (signToken positive)))
        (installSteps + blockSteps + compareSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      throughBlock comparePath
  refine
    ⟨installSteps + blockSteps + compareSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughCompare restorePath
  · unfold countSignStepEnvelope
    dsimp [installSteps, compareSteps, restoreSteps, source]
      at blockBound ⊢
    omega

private theorem count_sign_positive_width_step_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (widthPositive : 0 < formula.variableCount)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ signToken positive :: next :: tail)
    (gateBound :
      gateCount + 3 ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells (signToken positive) (next :: tail)) []
        initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .count .clause))
        (.node
          (firstBitRef .count (inRangeState positive)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .count (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [signToken positive]))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countSignStepEnvelope formula positive processed
          next tail gateCount scratch := by
  rcases
      token_read_install_path .count formula processed
        (signToken positive) (next :: tail) .clause
        (countRuntime formula formula.variableCount
          gateCount scratch)
        tokens (by simp [activeGrammarStates])
        (by cases positive <;> decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed (signToken positive) (next :: tail)
  let context :=
    markedSourceContext formula processed (signToken positive)
      (next :: tail) tokens
  have blockRepresents :
      TapeRepresents (countSignRef positive).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] installedTape := by
    change
      TargetEmitterRuntime.Represents
        (countSignRef positive).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] { state := (countSignRef positive).startState
                    tape := installedTape }
    exact
      represents_at_state
        (newState := (countSignRef positive).startState)
        installedRepresents
  rcases
      countSignBlock_path (context := context)
        formula positive gateCount scratch gateBound scratchBound
        installedTape blockRepresents with
    ⟨blockSteps, compareTape, blockPath, compareRepresents,
      blockBound⟩
  let sourceTail := source.tail
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail :=
    context.source_eq
  have compareRepresents' :
      TapeRepresents
        (literalCompareRef .count .clause
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        (SourceParser.cell00 :: sourceTail) [] compareTape := by
    change
      TapeRepresents
        (literalCompareRef .count .clause
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        source [] compareTape at compareRepresents
    rw [sourceEq] at compareRepresents
    exact compareRepresents
  have fits :=
    countedRegisters_fits formula formula.variableCount
      (gateCount + 3) (by simp) (Nat.le_trans gateBound
        (by omega))
  have compareMember :
      controlNode
          (Address.literalCompare .count .clause
            (signToken positive))
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          (.node
            (restoreRef .count (overflowState positive)
              (signToken positive)))
          (.node
            (restoreRef .count (inRangeState positive)
              (signToken positive))) ∈
        graph.nodes := by
    cases positive with
    | false =>
        simpa [signCompareNode, signToken,
          literalCompareRef, controlRef] using
          signCompareNode_member .count false
    | true =>
        simpa [signCompareNode, signToken,
          literalCompareRef, controlRef] using
          signCompareNode_member .count true
  rcases
      literal_compare_less_path
        (Address.literalCompare .count .clause
          (signToken positive))
        (.node
          (restoreRef .count (overflowState positive)
            (signToken positive)))
        (.node
          (restoreRef .count (inRangeState positive)
            (signToken positive)))
        (restoreRef .count (inRangeState positive)
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        SourceParser.cell00 sourceTail [] compareTape
        compareMember
        fits
        (by
          simpa [countedRegisters,
            TargetEmitterLedger.slotValue] using widthPositive)
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents' with
    ⟨restoreTape, comparePath, restoreRepresents'⟩
  have restoreRepresents :
      TapeRepresents
        (restoreRef .count (inRangeState positive)
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount
          (gateCount + 3)) []
        source [] restoreTape := by
    rw [sourceEq]
    exact restoreRepresents'
  rcases
      token_restore_advance_next_path .count formula
        processed (signToken positive) next tail
        (inRangeState positive)
        (countRuntime formula formula.variableCount
          (gateCount + 3) 0)
        tokens
        (by cases positive <;> decide)
        restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula)
      processed (signToken positive)
  let compareSteps :=
    literalCompareSteps (CNFToNANDWorkspace.capacity formula) 0
  let restoreSteps :=
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula)
      processed (signToken positive)
  have throughBlock :
      AcceptPath graph (.node (firstBitRef .count .clause))
        (.node
          (literalCompareRef .count .clause
            (signToken positive)))
        (installSteps + blockSteps)
        initialTape compareTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      (by
        cases positive <;>
          simpa [installSteps, signToken, countSignRef,
            postInstallEndpoint] using installPath)
      blockPath
  have throughCompare :
      AcceptPath graph (.node (firstBitRef .count .clause))
        (.node
          (restoreRef .count (inRangeState positive)
            (signToken positive)))
        (installSteps + blockSteps + compareSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      throughBlock comparePath
  refine
    ⟨installSteps + blockSteps + compareSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughCompare restorePath
  · unfold countSignStepEnvelope
    dsimp [installSteps, compareSteps, restoreSteps, source]
      at blockBound ⊢
    omega

private def countInRangeTStepEnvelope
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat) : Nat :=
  tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t +
    literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) scratch +
    countBlockEnvelope formula
      (markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        processed .t (next :: tail))
      (countRuntime formula formula.variableCount gateCount scratch)
      advanceLiteralIndexProgram +
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t

private theorem count_inRange_t_less_step_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .t :: next :: tail)
    (gateBound :
      gateCount ≤ CNFToNANDWorkspace.compilerGateCount formula)
    (less : scratch < formula.variableCount)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (firstBitRef .count (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .t (next :: tail)) [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .count (inRangeState positive)))
        (.node (firstBitRef .count (inRangeState positive)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .count (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula) (scratch + 1)
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.t]))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countInRangeTStepEnvelope formula positive processed
          next tail gateCount scratch := by
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed .t (next :: tail)
  let context :=
    markedSourceContext formula processed .t (next :: tail) tokens
  let sourceTail := source.tail
  have postInstallEq :
      postInstallEndpoint .count (inRangeState positive) .t =
        .node
          (literalCompareRef .count
            (inRangeState positive) .t) := by
    cases positive <;> rfl
  rcases
      token_read_install_path .count formula processed .t
        (next :: tail) (inRangeState positive)
        (countRuntime formula formula.variableCount gateCount scratch)
        tokens
        (by cases positive <;> simp [inRangeState,
          activeGrammarStates])
        (by cases positive <;> decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have compareRepresents :
      TapeRepresents
        (literalCompareRef .count
          (inRangeState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] installedTape := by
    exact represents_at_state installedRepresents
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail :=
    context.source_eq
  have compareRepresents' :
      TapeRepresents
        (literalCompareRef .count
          (inRangeState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (SourceParser.cell00 :: sourceTail) [] installedTape := by
    rw [sourceEq] at compareRepresents
    exact compareRepresents
  have fits :=
    countedRegisters_fits formula formula.variableCount gateCount
      (by simp) gateBound
  have compareMember :
      controlNode
          (Address.literalCompare .count
            (inRangeState positive) .t)
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          (.node
            (restoreRef .count (overflowState positive) .t))
          (.node (advanceLiteralRef .count positive)) ∈
        graph.nodes := by
    cases positive with
    | false =>
        simpa [literalUnitCompareNode, inRangeState,
          overflowState, literalCompareRef, controlRef] using
          literalUnitCompareNode_member .count false
    | true =>
        simpa [literalUnitCompareNode, inRangeState,
          overflowState, literalCompareRef, controlRef] using
          literalUnitCompareNode_member .count true
  rcases
      literal_compare_less_path
        (Address.literalCompare .count
          (inRangeState positive) .t)
        (.node
          (restoreRef .count (overflowState positive) .t))
        (.node (advanceLiteralRef .count positive))
        (advanceLiteralRef .count positive).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        SourceParser.cell00 sourceTail [] installedTape
        compareMember fits
        (by
          simpa [countedRegisters,
            TargetEmitterLedger.slotValue] using less)
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents' with
    ⟨advanceTape, comparePath, advanceRepresents'⟩
  have advanceRepresents :
      TapeRepresents (advanceLiteralRef .count positive).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] advanceTape := by
    rw [sourceEq]
    exact advanceRepresents'
  have scratchCapacity :
      scratch < CNFToNANDWorkspace.capacity formula :=
    Nat.lt_of_lt_of_le less fits.inputCount
  rcases
      count_advance_literal_block_path (context := context)
        formula positive gateCount scratch scratchCapacity
        advanceTape advanceRepresents with
    ⟨advanceSteps, restoreTape, advancePath, restoreRepresents,
      advanceBound⟩
  rcases
      token_restore_advance_next_path .count formula
        processed .t next tail (inRangeState positive)
        (countRuntime formula formula.variableCount
          gateCount (scratch + 1))
        tokens (by cases positive <;> decide)
        restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t
  let compareSteps :=
    literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) scratch
  let restoreSteps :=
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t
  have throughCompare :
      AcceptPath graph
        (.node (firstBitRef .count (inRangeState positive)))
        (.node (advanceLiteralRef .count positive))
        (installSteps + compareSteps)
        initialTape advanceTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      (by
        simpa [installSteps, postInstallEq,
          literalCompareRef] using installPath)
      comparePath
  have throughAdvance :
      AcceptPath graph
        (.node (firstBitRef .count (inRangeState positive)))
        (.node
          (restoreRef .count (inRangeState positive) .t))
        (installSteps + compareSteps + advanceSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      throughCompare advancePath
  refine
    ⟨installSteps + compareSteps + advanceSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughAdvance restorePath
  · unfold countInRangeTStepEnvelope
    dsimp [installSteps, compareSteps, restoreSteps, source]
      at advanceBound ⊢
    omega

private def countComparedDirectStepEnvelope
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken) (scratch : Nat) : Nat :=
  tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed token +
    literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) scratch +
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed token

private theorem count_inRange_t_equal_step_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount : Nat)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .t :: next :: tail)
    (gateBound :
      gateCount ≤ CNFToNANDWorkspace.compilerGateCount formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (firstBitRef .count (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .t (next :: tail)) [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .count (inRangeState positive)))
        (.node (firstBitRef .count (overflowState positive)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .count (overflowState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.t]))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countComparedDirectStepEnvelope
          formula processed .t formula.variableCount := by
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed .t (next :: tail)
  let context :=
    markedSourceContext formula processed .t (next :: tail) tokens
  let sourceTail := source.tail
  rcases
      token_read_install_path .count formula processed .t
        (next :: tail) (inRangeState positive)
        (countRuntime formula formula.variableCount
          gateCount formula.variableCount)
        tokens
        (by cases positive <;> simp [inRangeState,
          activeGrammarStates])
        (by cases positive <;> decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have compareRepresents :
      TapeRepresents
        (literalCompareRef .count
          (inRangeState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        source [] installedTape := by
    exact represents_at_state installedRepresents
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail :=
    context.source_eq
  have compareRepresents' :
      TapeRepresents
        (literalCompareRef .count
          (inRangeState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        (SourceParser.cell00 :: sourceTail) [] installedTape := by
    rw [sourceEq] at compareRepresents
    exact compareRepresents
  have fits :=
    countedRegisters_fits formula formula.variableCount gateCount
      (by simp) gateBound
  have compareMember :
      controlNode
          (Address.literalCompare .count
            (inRangeState positive) .t)
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          (.node
            (restoreRef .count (overflowState positive) .t))
          (.node (advanceLiteralRef .count positive)) ∈
        graph.nodes := by
    cases positive with
    | false =>
        simpa [literalUnitCompareNode, inRangeState,
          overflowState, literalCompareRef, controlRef] using
          literalUnitCompareNode_member .count false
    | true =>
        simpa [literalUnitCompareNode, inRangeState,
          overflowState, literalCompareRef, controlRef] using
          literalUnitCompareNode_member .count true
  rcases
      literal_compare_equal_path
        (Address.literalCompare .count
          (inRangeState positive) .t)
        (.node
          (restoreRef .count (overflowState positive) .t))
        (.node (advanceLiteralRef .count positive))
        (restoreRef .count (overflowState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        SourceParser.cell00 sourceTail [] installedTape
        compareMember fits
        (by simp [countedRegisters,
          TargetEmitterLedger.slotValue])
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents' with
    ⟨restoreTape, comparePath, restoreRepresents'⟩
  have restoreRepresents :
      TapeRepresents
        (restoreRef .count (overflowState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        source [] restoreTape := by
    rw [sourceEq]
    exact restoreRepresents'
  rcases
      token_restore_advance_next_path .count formula
        processed .t next tail (overflowState positive)
        (countRuntime formula formula.variableCount
          gateCount formula.variableCount)
        tokens (by cases positive <;> decide)
        restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t
  let compareSteps :=
    literalCompareSteps
      (CNFToNANDWorkspace.capacity formula)
      formula.variableCount
  let restoreSteps :=
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t
  have throughCompare :
      AcceptPath graph
        (.node (firstBitRef .count (inRangeState positive)))
        (.node
          (restoreRef .count (overflowState positive) .t))
        (installSteps + compareSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      (by
        cases positive <;>
          simpa [installSteps, postInstallEndpoint,
            inRangeState, literalCompareRef] using installPath)
      comparePath
  refine
    ⟨installSteps + compareSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughCompare restorePath
  · unfold countComparedDirectStepEnvelope
    dsimp [installSteps, compareSteps, restoreSteps]
    omega

private theorem count_inRange_f_equal_step_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount : Nat)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .f :: next :: tail)
    (gateBound :
      gateCount ≤ CNFToNANDWorkspace.compilerGateCount formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (firstBitRef .count (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .f (next :: tail)) [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .count (inRangeState positive)))
        (.node (firstBitRef .count .clause))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.f]))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countComparedDirectStepEnvelope
          formula processed .f formula.variableCount := by
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed .f (next :: tail)
  let context :=
    markedSourceContext formula processed .f (next :: tail) tokens
  let sourceTail := source.tail
  rcases
      token_read_install_path .count formula processed .f
        (next :: tail) (inRangeState positive)
        (countRuntime formula formula.variableCount
          gateCount formula.variableCount)
        tokens
        (by cases positive <;> simp [inRangeState,
          activeGrammarStates])
        (by cases positive <;> decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have compareRepresents :
      TapeRepresents
        (literalCompareRef .count
          (inRangeState positive) .f).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        source [] installedTape := by
    exact represents_at_state installedRepresents
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail :=
    context.source_eq
  have compareRepresents' :
      TapeRepresents
        (literalCompareRef .count
          (inRangeState positive) .f).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        (SourceParser.cell00 :: sourceTail) [] installedTape := by
    rw [sourceEq] at compareRepresents
    exact compareRepresents
  have fits :=
    countedRegisters_fits formula formula.variableCount gateCount
      (by simp) gateBound
  have compareMember :
      controlNode
          (Address.literalCompare .count
            (inRangeState positive) .f)
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          (.node (restoreRef .count .clause .f))
          (if positive then
            .node (restoreRef .count .clause .f)
           else .node countValidNegativeRef) ∈
        graph.nodes := by
    cases positive with
    | false =>
        have selected :=
          literalTerminatorCompareNode_member .count false
        change
          controlNode
              (Address.literalCompare .count .negative .f)
              (TargetEmitterScratchCompareSlot.machineFor .inputCount)
              (.node (restoreRef .count .clause .f))
              (.node countValidNegativeRef) ∈ graph.nodes at selected
        exact selected
    | true =>
        have selected :=
          literalTerminatorCompareNode_member .count true
        change
          controlNode
              (Address.literalCompare .count .positive .f)
              (TargetEmitterScratchCompareSlot.machineFor .inputCount)
              (.node (restoreRef .count .clause .f))
              (.node (restoreRef .count .clause .f)) ∈
            graph.nodes at selected
        exact selected
  rcases
      literal_compare_equal_path
        (Address.literalCompare .count
          (inRangeState positive) .f)
        (.node (restoreRef .count .clause .f))
        (if positive then
          .node (restoreRef .count .clause .f)
         else .node countValidNegativeRef)
        (restoreRef .count .clause .f).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        SourceParser.cell00 sourceTail [] installedTape
        compareMember fits
        (by simp [countedRegisters,
          TargetEmitterLedger.slotValue])
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents' with
    ⟨restoreTape, comparePath, restoreRepresents'⟩
  have restoreRepresents :
      TapeRepresents
        (restoreRef .count .clause .f).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        source [] restoreTape := by
    rw [sourceEq]
    exact restoreRepresents'
  rcases
      token_restore_advance_next_path .count formula
        processed .f next tail .clause
        (countRuntime formula formula.variableCount
          gateCount formula.variableCount)
        tokens (by decide) restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f
  let compareSteps :=
    literalCompareSteps
      (CNFToNANDWorkspace.capacity formula)
      formula.variableCount
  let restoreSteps :=
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f
  have throughCompare :
      AcceptPath graph
        (.node (firstBitRef .count (inRangeState positive)))
        (.node (restoreRef .count .clause .f))
        (installSteps + compareSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      (by
        cases positive <;>
          simpa [installSteps, postInstallEndpoint,
            inRangeState, literalCompareRef] using installPath)
      comparePath
  refine
    ⟨installSteps + compareSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughCompare restorePath
  · unfold countComparedDirectStepEnvelope
    dsimp [installSteps, compareSteps, restoreSteps]
    omega

private theorem count_inRange_positive_f_less_step_path
    (formula : CNFFormula)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .f :: next :: tail)
    (gateBound :
      gateCount ≤ CNFToNANDWorkspace.compilerGateCount formula)
    (less : scratch < formula.variableCount)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .count .positive).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .f (next :: tail)) [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .count .positive))
        (.node (firstBitRef .count .clause))
        steps initialTape finalTape ∧
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.f]))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countComparedDirectStepEnvelope
          formula processed .f scratch := by
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed .f (next :: tail)
  let context :=
    markedSourceContext formula processed .f (next :: tail) tokens
  let sourceTail := source.tail
  rcases
      token_read_install_path .count formula processed .f
        (next :: tail) .positive
        (countRuntime formula formula.variableCount gateCount scratch)
        tokens (by simp [activeGrammarStates]) (by decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have compareRepresents :
      TapeRepresents
        (literalCompareRef .count .positive .f).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] installedTape := by
    exact represents_at_state installedRepresents
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail :=
    context.source_eq
  have compareRepresents' :
      TapeRepresents
        (literalCompareRef .count .positive .f).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (SourceParser.cell00 :: sourceTail) [] installedTape := by
    rw [sourceEq] at compareRepresents
    exact compareRepresents
  have fits :=
    countedRegisters_fits formula formula.variableCount gateCount
      (by simp) gateBound
  have compareMember :
      controlNode
          (Address.literalCompare .count .positive .f)
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          (.node (restoreRef .count .clause .f))
          (.node (restoreRef .count .clause .f)) ∈
        graph.nodes := by
    have selected :=
      literalTerminatorCompareNode_member .count true
    change
      controlNode
          (Address.literalCompare .count .positive .f)
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          (.node (restoreRef .count .clause .f))
          (.node (restoreRef .count .clause .f)) ∈
        graph.nodes at selected
    exact selected
  rcases
      literal_compare_less_path
        (Address.literalCompare .count .positive .f)
        (.node (restoreRef .count .clause .f))
        (.node (restoreRef .count .clause .f))
        (restoreRef .count .clause .f).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        SourceParser.cell00 sourceTail [] installedTape
        compareMember fits
        (by
          simpa [countedRegisters,
            TargetEmitterLedger.slotValue] using less)
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents' with
    ⟨restoreTape, comparePath, restoreRepresents'⟩
  have restoreRepresents :
      TapeRepresents (restoreRef .count .clause .f).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] restoreTape := by
    rw [sourceEq]
    exact restoreRepresents'
  rcases
      token_restore_advance_next_path .count formula
        processed .f next tail .clause
        (countRuntime formula formula.variableCount gateCount scratch)
        tokens (by decide) restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f
  let compareSteps :=
    literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) scratch
  let restoreSteps :=
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f
  have throughCompare :
      AcceptPath graph (.node (firstBitRef .count .positive))
        (.node (restoreRef .count .clause .f))
        (installSteps + compareSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      (by
        simpa [installSteps, postInstallEndpoint,
          literalCompareRef] using installPath)
      comparePath
  refine
    ⟨installSteps + compareSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughCompare restorePath
  · unfold countComparedDirectStepEnvelope
    dsimp [installSteps, compareSteps, restoreSteps]
    omega

private def countNegativeTerminatorStepEnvelope
    (formula : CNFFormula) (processed : List CNFToken)
    (next : CNFToken) (tail : List CNFToken)
    (gateCount scratch : Nat) : Nat :=
  tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f +
    literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) scratch +
    countBlockEnvelope formula
      (markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        processed .f (next :: tail))
      (countRuntime formula formula.variableCount gateCount scratch)
      countValidNegativeProgram +
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f

private theorem count_inRange_negative_f_less_step_path
    (formula : CNFFormula)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .f :: next :: tail)
    (gateBound :
      gateCount + 1 ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (less : scratch < formula.variableCount)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .count .negative).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .f (next :: tail)) [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .count .negative))
        (.node (firstBitRef .count .clause))
        steps initialTape finalTape ∧
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount
          (gateCount + 1)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.f]))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countNegativeTerminatorStepEnvelope formula processed
          next tail gateCount scratch := by
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed .f (next :: tail)
  let context :=
    markedSourceContext formula processed .f (next :: tail) tokens
  let sourceTail := source.tail
  rcases
      token_read_install_path .count formula processed .f
        (next :: tail) .negative
        (countRuntime formula formula.variableCount gateCount scratch)
        tokens (by simp [activeGrammarStates]) (by decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have compareRepresents :
      TapeRepresents
        (literalCompareRef .count .negative .f).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] installedTape := by
    exact represents_at_state installedRepresents
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail :=
    context.source_eq
  have compareRepresents' :
      TapeRepresents
        (literalCompareRef .count .negative .f).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (SourceParser.cell00 :: sourceTail) [] installedTape := by
    rw [sourceEq] at compareRepresents
    exact compareRepresents
  have fits :=
    countedRegisters_fits formula formula.variableCount gateCount
      (by simp) (Nat.le_trans (by omega) gateBound)
  have compareMember :
      controlNode
          (Address.literalCompare .count .negative .f)
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          (.node (restoreRef .count .clause .f))
          (.node countValidNegativeRef) ∈ graph.nodes := by
    have selected :=
      literalTerminatorCompareNode_member .count false
    change
      controlNode
          (Address.literalCompare .count .negative .f)
          (TargetEmitterScratchCompareSlot.machineFor .inputCount)
          (.node (restoreRef .count .clause .f))
          (.node countValidNegativeRef) ∈ graph.nodes at selected
    exact selected
  rcases
      literal_compare_less_path
        (Address.literalCompare .count .negative .f)
        (.node (restoreRef .count .clause .f))
        (.node countValidNegativeRef)
        countValidNegativeRef.startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        SourceParser.cell00 sourceTail [] installedTape
        compareMember fits
        (by
          simpa [countedRegisters,
            TargetEmitterLedger.slotValue] using less)
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents' with
    ⟨validTape, comparePath, validRepresents'⟩
  have validRepresents :
      TapeRepresents countValidNegativeRef.startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        source [] validTape := by
    rw [sourceEq]
    exact validRepresents'
  rcases
      count_valid_negative_block_path (context := context)
        formula gateCount scratch gateBound
        (Nat.le_trans (Nat.le_of_lt less)
          (CNFToNANDWorkspace.variableCount_le_capacity formula))
        validTape validRepresents with
    ⟨validSteps, restoreTape, validPath, restoreRepresents,
      validBound⟩
  rcases
      token_restore_advance_next_path .count formula
        processed .f next tail .clause
        (countRuntime formula formula.variableCount
          (gateCount + 1) scratch)
        tokens (by decide) restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f
  let compareSteps :=
    literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) scratch
  let restoreSteps :=
    tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f
  have throughCompare :
      AcceptPath graph (.node (firstBitRef .count .negative))
        (.node countValidNegativeRef)
        (installSteps + compareSteps)
        initialTape validTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      (by
        simpa [installSteps, postInstallEndpoint,
          literalCompareRef] using installPath)
      comparePath
  have throughValid :
      AcceptPath graph (.node (firstBitRef .count .negative))
        (.node (restoreRef .count .clause .f))
        (installSteps + compareSteps + validSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      throughCompare validPath
  refine
    ⟨installSteps + compareSteps + validSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughValid restorePath
  · unfold countNegativeTerminatorStepEnvelope
    dsimp [installSteps, compareSteps, restoreSteps, source]
      at validBound ⊢
    omega

private def countValidTerminatorEnvelope
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat) : Nat :=
  if positive then
    countComparedDirectStepEnvelope formula processed .f scratch
  else
    countNegativeTerminatorStepEnvelope formula processed
      next tail gateCount scratch

private theorem count_inRange_f_less_step_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .f :: next :: tail)
    (gateBound :
      gateCount + (if !positive then 1 else 0) ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (less : scratch < formula.variableCount)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (firstBitRef .count (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .f (next :: tail)) [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .count (inRangeState positive)))
        (.node (firstBitRef .count .clause))
        steps initialTape finalTape ∧
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount
          (gateCount + (if !positive then 1 else 0))) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.f]))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countValidTerminatorEnvelope formula positive processed
          next tail gateCount scratch := by
  cases positive with
  | false =>
      simpa [inRangeState, countValidTerminatorEnvelope] using
        (count_inRange_negative_f_less_step_path
          formula processed next tail gateCount scratch tokens
          (by simpa using gateBound) less initialTape
          (by simpa [inRangeState] using represents))
  | true =>
      simpa [inRangeState, countValidTerminatorEnvelope] using
        (count_inRange_positive_f_less_step_path
          formula processed next tail gateCount scratch tokens
          (by simpa using gateBound) less initialTape
          (by simpa [inRangeState] using represents))

private theorem encodeUnaryTokens_eq_replicate
    (count : Nat) :
    encodeUnaryTokens count =
      List.replicate count CNFToken.t ++ [.f] := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      simp [encodeUnaryTokens, List.replicate_succ,
        inductionHypothesis]

private def countOverflowUnaryEnvelope
    (formula : CNFFormula) (processed : List CNFToken) :
    Nat → Nat
  | 0 =>
      directTokenStepEnvelope formula processed .f
  | remaining + 1 =>
      directTokenStepEnvelope formula processed .t +
        countOverflowUnaryEnvelope formula
          (processed ++ [.t]) remaining

private theorem count_overflow_unary_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (remaining : Nat)
    (next : CNFToken) (tail : List CNFToken)
    (gateCount : Nat)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeUnaryTokens remaining ++ next :: tail)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (firstBitRef .count (overflowState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (encodeUnaryTokens remaining ++ next :: tail) ++
          carrierFooterCells)
        [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .count (overflowState positive)))
        (.node (firstBitRef .count .clause))
        steps initialTape finalTape ∧
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        formula.variableCount
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ encodeUnaryTokens remaining))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countOverflowUnaryEnvelope formula processed remaining := by
  induction remaining generalizing processed initialTape with
  | zero =>
      have directInput :
          ScanRepresents
            (firstBitRef .count (overflowState positive)).startState
            (CNFToNANDWorkspace.capacity formula)
            formula.variableCount
            (countedRegisters formula formula.variableCount gateCount) []
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells .f (next :: tail)) [] initialTape := by
        simpa [encodeUnaryTokens, scanAfterCells,
          carrierGateCells, List.append_assoc] using represents
      rcases
          count_direct_token_step_path formula processed .f next tail
            (overflowState positive) .clause
            (countRuntime formula formula.variableCount
              gateCount formula.variableCount)
            (by simpa [encodeUnaryTokens, List.append_assoc] using tokens)
            (by cases positive <;>
              simp [overflowState, activeGrammarStates])
            (by cases positive <;> decide)
            (by cases positive <;> rfl)
            (by decide) initialTape directInput with
        ⟨steps, finalTape, path, finalRepresents, bound⟩
      exact
        ⟨steps, finalTape, path,
          by simpa [encodeUnaryTokens, List.append_assoc] using
            finalRepresents,
          by simpa [countOverflowUnaryEnvelope] using bound⟩
  | succ remaining inductionHypothesis =>
      have directInput :
          ScanRepresents
            (firstBitRef .count (overflowState positive)).startState
            (CNFToNANDWorkspace.capacity formula)
            formula.variableCount
            (countedRegisters formula formula.variableCount gateCount) []
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells .t
              (encodeUnaryTokens remaining ++ next :: tail))
            [] initialTape := by
        simpa [encodeUnaryTokens, scanAfterCells,
          carrierGateCells, List.append_assoc] using represents
      rcases
          count_direct_token_step_path formula processed .t
            ((encodeUnaryTokens remaining).headD next)
            ((encodeUnaryTokens remaining).tail ++ next :: tail)
            (overflowState positive) (overflowState positive)
            (countRuntime formula formula.variableCount
              gateCount formula.variableCount)
            (by
              have nonempty : encodeUnaryTokens remaining ≠ [] := by
                cases remaining <;> simp [encodeUnaryTokens]
              cases unaryEq : encodeUnaryTokens remaining with
              | nil => exact False.elim (nonempty unaryEq)
              | cons head rest =>
                  simpa [encodeUnaryTokens, unaryEq,
                    List.append_assoc] using tokens)
            (by cases positive <;>
              simp [overflowState, activeGrammarStates])
            (by cases positive <;> decide)
            (by cases positive <;> rfl)
            (by cases positive <;> decide)
            initialTape
            (by
              have nonempty : encodeUnaryTokens remaining ≠ [] := by
                cases remaining <;> simp [encodeUnaryTokens]
              cases unaryEq : encodeUnaryTokens remaining with
              | nil => exact False.elim (nonempty unaryEq)
              | cons head rest =>
                  simpa [unaryEq, List.append_assoc] using directInput) with
        ⟨firstSteps, nextTape, firstPath, nextRepresents,
          firstBound⟩
      have recursiveInput :
          ScanRepresents
            (firstBitRef .count (overflowState positive)).startState
            (CNFToNANDWorkspace.capacity formula)
            formula.variableCount
            (countedRegisters formula formula.variableCount gateCount) []
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula)
              (processed ++ [.t]))
            (carrierGateCells
                (encodeUnaryTokens remaining ++ next :: tail) ++
              carrierFooterCells)
            [] nextTape := by
        have nonempty : encodeUnaryTokens remaining ≠ [] := by
          cases remaining <;> simp [encodeUnaryTokens]
        cases unaryEq : encodeUnaryTokens remaining with
        | nil => exact False.elim (nonempty unaryEq)
        | cons head rest =>
            simpa [unaryEq, scanAfterCells,
              carrierGateCells, List.append_assoc] using
              nextRepresents
      rcases
          inductionHypothesis (processed ++ [.t])
            (by simpa [encodeUnaryTokens, List.append_assoc] using tokens)
            nextTape recursiveInput with
        ⟨tailSteps, finalTape, tailPath, finalRepresents,
          tailBound⟩
      refine
        ⟨firstSteps + tailSteps, finalTape, ?_,
          by simpa [encodeUnaryTokens, List.append_assoc] using
            finalRepresents, ?_⟩
      · exact
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            firstPath tailPath
      · simp only [countOverflowUnaryEnvelope]
        omega

private def countInRangeUnaryEnvelope
    (formula : CNFFormula) (positive : Bool)
    (next : CNFToken) (tail : List CNFToken)
    (gateCount : Nat) (processed : List CNFToken)
    (done : Nat) : Nat → Nat
  | 0 =>
      if done < formula.variableCount then
        countValidTerminatorEnvelope formula positive processed
          next tail gateCount done
      else
        countComparedDirectStepEnvelope formula processed .f done
  | remaining + 1 =>
      let unary := encodeUnaryTokens remaining
      let unaryHead := unary.headD next
      let unaryTail := unary.tail ++ next :: tail
      if done < formula.variableCount then
        countInRangeTStepEnvelope formula positive processed
            unaryHead unaryTail gateCount done +
          countInRangeUnaryEnvelope formula positive next tail
            gateCount (processed ++ [.t]) (done + 1) remaining
      else
        countComparedDirectStepEnvelope formula processed .t done +
          countOverflowUnaryEnvelope formula
            (processed ++ [.t]) remaining

private theorem count_inRange_unary_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (done remaining : Nat)
    (next : CNFToken) (tail : List CNFToken)
    (gateCount : Nat)
    (doneBound : done ≤ formula.variableCount)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeUnaryTokens remaining ++ next :: tail)
    (gateBound :
      gateCount +
          (if !positive &&
              done + remaining < formula.variableCount
           then 1 else 0) ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (firstBitRef .count (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula) done
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (encodeUnaryTokens remaining ++ next :: tail) ++
          carrierFooterCells)
        [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .count (inRangeState positive)))
        (.node (firstBitRef .count .clause))
        steps initialTape finalTape ∧
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        (Nat.min (done + remaining) formula.variableCount)
        (countedRegisters formula formula.variableCount
          (gateCount +
            (if !positive &&
                done + remaining < formula.variableCount
             then 1 else 0))) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ encodeUnaryTokens remaining))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countInRangeUnaryEnvelope formula positive next tail
          gateCount processed done remaining := by
  induction remaining generalizing processed done initialTape with
  | zero =>
      have terminatorInput :
          ScanRepresents
            (firstBitRef .count (inRangeState positive)).startState
            (CNFToNANDWorkspace.capacity formula) done
            (countedRegisters formula formula.variableCount gateCount) []
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells .f (next :: tail)) [] initialTape := by
        simpa [encodeUnaryTokens, scanAfterCells,
          carrierGateCells, List.append_assoc] using represents
      by_cases less : done < formula.variableCount
      · rcases
            count_inRange_f_less_step_path formula positive
              processed next tail gateCount done
              (by simpa [encodeUnaryTokens,
                List.append_assoc] using tokens)
              (by
                simpa [less] using gateBound)
              less initialTape terminatorInput with
          ⟨steps, finalTape, path, finalRepresents, bound⟩
        refine
          ⟨steps, finalTape, path, ?_,
            by simpa [countInRangeUnaryEnvelope, less] using bound⟩
        simpa [encodeUnaryTokens, less,
          Nat.min_eq_left (Nat.le_of_lt less),
          List.append_assoc] using finalRepresents
      · have equal : done = formula.variableCount := by
          omega
        rcases
            count_inRange_f_equal_step_path formula positive
              processed next tail gateCount
              (by simpa [encodeUnaryTokens,
                List.append_assoc] using tokens)
              (by
                have : gateCount ≤
                    CNFToNANDWorkspace.compilerGateCount formula := by
                  omega
                exact this)
              initialTape
              (by simpa [equal] using terminatorInput) with
          ⟨steps, finalTape, path, finalRepresents, bound⟩
        refine
          ⟨steps, finalTape, path, ?_,
            by simpa [countInRangeUnaryEnvelope, less, equal] using
              bound⟩
        simpa [encodeUnaryTokens, less, equal,
          List.append_assoc] using finalRepresents
  | succ remaining inductionHypothesis =>
      let unary := encodeUnaryTokens remaining
      let unaryHead := unary.headD next
      let unaryTail := unary.tail ++ next :: tail
      have unaryNonempty : unary ≠ [] := by
        dsimp [unary]
        cases remaining <;> simp [encodeUnaryTokens]
      have unitInput :
          ScanRepresents
            (firstBitRef .count (inRangeState positive)).startState
            (CNFToNANDWorkspace.capacity formula) done
            (countedRegisters formula formula.variableCount gateCount) []
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells .t (unaryHead :: unaryTail)) []
            initialTape := by
        cases unaryEq : unary with
        | nil => exact False.elim (unaryNonempty unaryEq)
        | cons head rest =>
            simpa [unary, unaryHead, unaryTail, unaryEq,
              encodeUnaryTokens, scanAfterCells,
              carrierGateCells, List.append_assoc] using represents
      have unitTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ .t :: unaryHead :: unaryTail := by
        cases unaryEq : unary with
        | nil => exact False.elim (unaryNonempty unaryEq)
        | cons head rest =>
            simpa [unary, unaryHead, unaryTail, unaryEq,
              encodeUnaryTokens, List.append_assoc] using tokens
      by_cases less : done < formula.variableCount
      · rcases
            count_inRange_t_less_step_path formula positive
              processed unaryHead unaryTail gateCount done
              unitTokens
              (by omega) less initialTape unitInput with
          ⟨firstSteps, nextTape, firstPath, nextRepresents,
            firstBound⟩
        have recursiveInput :
            ScanRepresents
              (firstBitRef .count (inRangeState positive)).startState
              (CNFToNANDWorkspace.capacity formula) (done + 1)
              (countedRegisters formula formula.variableCount gateCount)
              []
              (scanBeforeCells
                (CNFToNANDWorkspace.formulaTokens formula)
                (processed ++ [.t]))
              (carrierGateCells
                  (encodeUnaryTokens remaining ++ next :: tail) ++
                carrierFooterCells)
              [] nextTape := by
          cases unaryEq : unary with
          | nil => exact False.elim (unaryNonempty unaryEq)
          | cons head rest =>
              simpa [unary, unaryHead, unaryTail, unaryEq,
                scanAfterCells, carrierGateCells,
                List.append_assoc] using nextRepresents
        rcases
            inductionHypothesis (processed ++ [.t]) (done + 1)
              (by omega)
              (by
                simpa [encodeUnaryTokens,
                  List.append_assoc] using tokens)
              (by
                simpa [Nat.add_assoc, Nat.add_left_comm,
                  Nat.add_comm] using gateBound)
              nextTape recursiveInput with
          ⟨tailSteps, finalTape, tailPath, finalRepresents,
            tailBound⟩
        refine
          ⟨firstSteps + tailSteps, finalTape,
            AcceptPath.trans graph _ _ _ _ _ _ _ _
              firstPath tailPath,
            ?_, ?_⟩
        · have indexEq :
              done + 1 + remaining =
                done + (remaining + 1) := by
            omega
          rw [indexEq] at finalRepresents
          simpa [encodeUnaryTokens, List.append_assoc] using
            finalRepresents
        · simpa [countInRangeUnaryEnvelope, less,
            unary, unaryHead, unaryTail] using
            Nat.add_le_add firstBound tailBound
      · have equal : done = formula.variableCount := by
          omega
        rcases
            count_inRange_t_equal_step_path formula positive
              processed unaryHead unaryTail gateCount unitTokens
              (by omega) initialTape
              (by simpa [equal] using unitInput) with
          ⟨firstSteps, overflowTape, firstPath,
            overflowRepresents, firstBound⟩
        have overflowInput :
            ScanRepresents
              (firstBitRef .count (overflowState positive)).startState
              (CNFToNANDWorkspace.capacity formula)
              formula.variableCount
              (countedRegisters formula formula.variableCount gateCount)
              []
              (scanBeforeCells
                (CNFToNANDWorkspace.formulaTokens formula)
                (processed ++ [.t]))
              (carrierGateCells
                  (encodeUnaryTokens remaining ++ next :: tail) ++
                carrierFooterCells)
              [] overflowTape := by
          cases unaryEq : unary with
          | nil => exact False.elim (unaryNonempty unaryEq)
          | cons head rest =>
              simpa [unary, unaryHead, unaryTail, unaryEq,
                scanAfterCells, carrierGateCells,
                List.append_assoc] using overflowRepresents
        rcases
            count_overflow_unary_path formula positive
              (processed ++ [.t]) remaining next tail gateCount
              (by simpa [encodeUnaryTokens,
                List.append_assoc] using tokens)
              overflowTape overflowInput with
          ⟨tailSteps, finalTape, tailPath, finalRepresents,
            tailBound⟩
        refine
          ⟨firstSteps + tailSteps, finalTape,
            AcceptPath.trans graph _ _ _ _ _ _ _ _
              firstPath tailPath,
            ?_, ?_⟩
        · have indexNot :
              ¬ formula.variableCount + (remaining + 1) <
                  formula.variableCount := by
            omega
          simpa [encodeUnaryTokens, equal, less, indexNot,
            Nat.min_eq_right (by omega),
            List.append_assoc] using finalRepresents
        · simpa [countInRangeUnaryEnvelope, less,
            unary, unaryHead, unaryTail, equal] using
            Nat.add_le_add firstBound tailBound

private def countLiteralEnvelope
    (formula : CNFFormula) (literal : CNFLiteral)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat) : Nat :=
  let positive := literal.positive
  let unary := encodeUnaryTokens literal.variableIndex
  let unaryHead := unary.headD next
  let unaryTail := unary.tail ++ next :: tail
  countSignStepEnvelope formula positive processed unaryHead unaryTail
      gateCount scratch +
    if formula.variableCount = 0 then
      countOverflowUnaryEnvelope formula
        (processed ++ [signToken positive]) literal.variableIndex
    else
      countInRangeUnaryEnvelope formula positive next tail
        (gateCount + 3) (processed ++ [signToken positive])
        0 literal.variableIndex

private theorem count_literal_path
    (formula : CNFFormula) (literal : CNFLiteral)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeLiteralTokens literal ++ next :: tail)
    (gateBound :
      gateCount +
          literalGateCharge formula.variableCount literal ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (encodeLiteralTokens literal ++ next :: tail) ++
          carrierFooterCells)
        [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .count .clause))
        (.node (firstBitRef .count .clause))
        steps initialTape finalTape ∧
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        (Nat.min literal.variableIndex formula.variableCount)
        (countedRegisters formula formula.variableCount
          (gateCount +
            literalGateCharge formula.variableCount literal)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ encodeLiteralTokens literal))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countLiteralEnvelope formula literal processed next tail
          gateCount scratch := by
  let positive := literal.positive
  let unary := encodeUnaryTokens literal.variableIndex
  let unaryHead := unary.headD next
  let unaryTail := unary.tail ++ next :: tail
  have unaryNonempty : unary ≠ [] := by
    dsimp [unary]
    cases literal.variableIndex <;> simp [encodeUnaryTokens]
  have signTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ signToken positive :: unaryHead :: unaryTail := by
    cases unaryEq : unary with
    | nil => exact False.elim (unaryNonempty unaryEq)
    | cons head rest =>
        simpa [positive, unary, unaryHead, unaryTail, unaryEq,
          signToken, encodeLiteralTokens,
          List.append_assoc] using tokens
  have signInput :
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells (signToken positive)
          (unaryHead :: unaryTail)) [] initialTape := by
    cases unaryEq : unary with
    | nil => exact False.elim (unaryNonempty unaryEq)
    | cons head rest =>
        simpa [positive, unary, unaryHead, unaryTail, unaryEq,
          signToken, encodeLiteralTokens, scanAfterCells,
          carrierGateCells, List.append_assoc] using represents
  by_cases widthZero : formula.variableCount = 0
  · rcases
        count_sign_zero_width_step_path formula positive processed
          unaryHead unaryTail gateCount scratch widthZero signTokens
          (by
            unfold literalGateCharge at gateBound
            simpa [widthZero] using gateBound)
          scratchBound initialTape signInput with
      ⟨signSteps, unaryTape, signPath, unaryRepresents,
        signBound⟩
    have overflowInput :
        ScanRepresents
          (firstBitRef .count (overflowState positive)).startState
          (CNFToNANDWorkspace.capacity formula)
          formula.variableCount
          (countedRegisters formula formula.variableCount
            (gateCount + 3)) []
          (scanBeforeCells
            (CNFToNANDWorkspace.formulaTokens formula)
            (processed ++ [signToken positive]))
          (carrierGateCells (unary ++ next :: tail) ++
            carrierFooterCells)
          [] unaryTape := by
      cases unaryEq : unary with
      | nil => exact False.elim (unaryNonempty unaryEq)
      | cons head rest =>
          simpa [unary, unaryHead, unaryTail, unaryEq, widthZero,
            scanAfterCells, carrierGateCells,
            List.append_assoc] using unaryRepresents
    rcases
        count_overflow_unary_path formula positive
          (processed ++ [signToken positive])
          literal.variableIndex next tail (gateCount + 3)
          (by
            simpa [positive, unary, signToken,
              encodeLiteralTokens, List.append_assoc] using tokens)
          unaryTape overflowInput with
      ⟨unarySteps, finalTape, unaryPath, finalRepresents,
        unaryBound⟩
    refine
      ⟨signSteps + unarySteps, finalTape,
        AcceptPath.trans graph _ _ _ _ _ _ _ _
          signPath unaryPath, ?_, ?_⟩
    · simpa [positive, unary, encodeLiteralTokens, signToken,
        literalGateCharge, widthZero, Nat.add_assoc,
        List.append_assoc] using finalRepresents
    · simpa [countLiteralEnvelope, positive, unary,
        unaryHead, unaryTail, widthZero] using
        Nat.add_le_add signBound unaryBound
  · have widthPositive : 0 < formula.variableCount := by
      omega
    rcases
        count_sign_positive_width_step_path formula positive
          processed unaryHead unaryTail gateCount scratch
          widthPositive signTokens
          (by
            unfold literalGateCharge at gateBound
            omega)
          scratchBound initialTape signInput with
      ⟨signSteps, unaryTape, signPath, unaryRepresents,
        signBound⟩
    have inRangeInput :
        ScanRepresents
          (firstBitRef .count (inRangeState positive)).startState
          (CNFToNANDWorkspace.capacity formula) 0
          (countedRegisters formula formula.variableCount
            (gateCount + 3)) []
          (scanBeforeCells
            (CNFToNANDWorkspace.formulaTokens formula)
            (processed ++ [signToken positive]))
          (carrierGateCells (unary ++ next :: tail) ++
            carrierFooterCells)
          [] unaryTape := by
      cases unaryEq : unary with
      | nil => exact False.elim (unaryNonempty unaryEq)
      | cons head rest =>
          simpa [unary, unaryHead, unaryTail, unaryEq,
            scanAfterCells, carrierGateCells,
            List.append_assoc] using unaryRepresents
    rcases
        count_inRange_unary_path formula positive
          (processed ++ [signToken positive])
          0 literal.variableIndex next tail (gateCount + 3)
          (by omega)
          (by
            simpa [positive, unary, signToken,
              encodeLiteralTokens, List.append_assoc] using tokens)
          (by
            unfold literalGateCharge at gateBound
            simpa [positive, Nat.add_assoc] using gateBound)
          unaryTape inRangeInput with
      ⟨unarySteps, finalTape, unaryPath, finalRepresents,
        unaryBound⟩
    refine
      ⟨signSteps + unarySteps, finalTape,
        AcceptPath.trans graph _ _ _ _ _ _ _ _
          signPath unaryPath, ?_, ?_⟩
    · simpa [positive, unary, encodeLiteralTokens, signToken,
        literalGateCharge, Nat.add_assoc,
        List.append_assoc] using finalRepresents
    · simpa [countLiteralEnvelope, positive, unary,
        unaryHead, unaryTail, widthZero] using
        Nat.add_le_add signBound unaryBound

private theorem variableCount_lt_capacity (formula : CNFFormula) :
    formula.variableCount <
      CNFToNANDWorkspace.capacity formula := by
  have lengthBound :
      formula.variableCount <
        (CNFToNANDWorkspace.formulaTokens formula).length := by
    rw [CNFToNANDWorkspace.formulaTokens,
      encodeFormulaTokens, CookLevin.encodeCNFTokens_length]
    omega
  rw [CNFToNANDWorkspace.capacity_exact]
  omega

private def literalListFinalScratch
    (width : Nat) : List CNFLiteral → Nat → Nat
  | [], scratch => scratch
  | literal :: rest, _ =>
      literalListFinalScratch width rest
        (Nat.min literal.variableIndex width)

private def countLiteralListEnvelope
    (formula : CNFFormula) (next : CNFToken)
    (tail : List CNFToken) :
    List CNFLiteral → List CNFToken → Nat → Nat → Nat
  | [], _, _, _ => 0
  | literal :: rest, processed, gateCount, scratch =>
      let remaining :=
        encodeLiteralListTokens rest ++ next :: tail
      let remainingHead := remaining.headD next
      let remainingTail := remaining.tail
      countLiteralEnvelope formula literal processed
          remainingHead remainingTail gateCount scratch +
        countLiteralListEnvelope formula next tail rest
          (processed ++ encodeLiteralTokens literal)
          (gateCount +
            literalGateCharge formula.variableCount literal)
          (Nat.min literal.variableIndex formula.variableCount)

private theorem count_literal_list_path
    (formula : CNFFormula) (literals : List CNFLiteral)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeLiteralListTokens literals ++ next :: tail)
    (gateBound :
      gateCount +
          (literals.map
            (literalGateCharge formula.variableCount)).sum ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (encodeLiteralListTokens literals ++ next :: tail) ++
          carrierFooterCells)
        [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .count .clause))
        (.node (firstBitRef .count .clause))
        steps initialTape finalTape ∧
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        (literalListFinalScratch formula.variableCount
          literals scratch)
        (countedRegisters formula formula.variableCount
          (gateCount +
            (literals.map
              (literalGateCharge formula.variableCount)).sum)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ encodeLiteralListTokens literals))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countLiteralListEnvelope formula next tail literals
          processed gateCount scratch := by
  induction literals generalizing processed gateCount scratch initialTape with
  | nil =>
      refine ⟨0, initialTape, AcceptPath.terminal _ _, ?_, ?_⟩
      · simpa [encodeLiteralListTokens, literalListFinalScratch,
          scanAfterCells, carrierGateCells,
          List.append_assoc] using represents
      · simp [countLiteralListEnvelope]
  | cons literal rest inductionHypothesis =>
      let remaining :=
        encodeLiteralListTokens rest ++ next :: tail
      let remainingHead := remaining.headD next
      let remainingTail := remaining.tail
      have remainingNonempty : remaining ≠ [] := by
        simp [remaining]
      have literalTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++
              encodeLiteralTokens literal ++
                remainingHead :: remainingTail := by
        cases remainingEq : remaining with
        | nil => exact False.elim (remainingNonempty remainingEq)
        | cons head restTokens =>
            simpa [remaining, remainingHead, remainingTail,
              remainingEq, encodeLiteralListTokens,
              List.append_assoc] using tokens
      have literalInput :
          ScanRepresents (firstBitRef .count .clause).startState
            (CNFToNANDWorkspace.capacity formula) scratch
            (countedRegisters formula formula.variableCount gateCount) []
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (carrierGateCells
                (encodeLiteralTokens literal ++
                  remainingHead :: remainingTail) ++
              carrierFooterCells)
            [] initialTape := by
        cases remainingEq : remaining with
        | nil => exact False.elim (remainingNonempty remainingEq)
        | cons head restTokens =>
            simpa [remaining, remainingHead, remainingTail,
              remainingEq, encodeLiteralListTokens,
              List.append_assoc] using represents
      rcases
          count_literal_path formula literal processed
            remainingHead remainingTail gateCount scratch
            literalTokens
            (by
              simp only [List.map_cons, List.sum_cons] at gateBound
              omega)
            scratchBound initialTape literalInput with
        ⟨literalSteps, nextTape, literalPath, nextRepresents,
          literalBound⟩
      have recursiveInput :
          ScanRepresents (firstBitRef .count .clause).startState
            (CNFToNANDWorkspace.capacity formula)
            (Nat.min literal.variableIndex formula.variableCount)
            (countedRegisters formula formula.variableCount
              (gateCount +
                literalGateCharge formula.variableCount literal)) []
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula)
              (processed ++ encodeLiteralTokens literal))
            (carrierGateCells
                (encodeLiteralListTokens rest ++ next :: tail) ++
              carrierFooterCells)
            [] nextTape := by
        cases remainingEq : remaining with
        | nil => exact False.elim (remainingNonempty remainingEq)
        | cons head restTokens =>
            simpa [remaining, remainingHead, remainingTail,
              remainingEq, scanAfterCells, carrierGateCells,
              List.append_assoc] using nextRepresents
      rcases
          inductionHypothesis
            (processed ++ encodeLiteralTokens literal)
            (gateCount +
              literalGateCharge formula.variableCount literal)
            (Nat.min literal.variableIndex formula.variableCount)
            (by
              simpa [encodeLiteralListTokens,
                List.append_assoc] using tokens)
            (by
              simp only [List.map_cons, List.sum_cons] at gateBound
              omega)
            (Nat.lt_of_le_of_lt (Nat.min_le_right _ _)
              (variableCount_lt_capacity formula))
            nextTape recursiveInput with
        ⟨tailSteps, finalTape, tailPath, finalRepresents,
          tailBound⟩
      refine
        ⟨literalSteps + tailSteps, finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            literalPath tailPath, ?_, ?_⟩
      · simpa [literalListFinalScratch, encodeLiteralListTokens,
          Nat.add_assoc, List.append_assoc] using finalRepresents
      · simpa [countLiteralListEnvelope, remaining,
          remainingHead, remainingTail] using
          Nat.add_le_add literalBound tailBound

private def countClauseEnvelope
    (formula : CNFFormula) (clause : List CNFLiteral)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat) : Nat :=
  let body := encodeLiteralListTokens clause ++ [.finish]
  let bodyHead := body.headD .finish
  let bodyTail := body.tail ++ next :: tail
  countClauseSeparatorStepEnvelope formula processed
      bodyHead bodyTail gateCount scratch +
    countLiteralListEnvelope formula .finish (next :: tail)
      clause (processed ++ [.sep]) (gateCount + 2) scratch +
    directTokenStepEnvelope formula
      (processed ++ .sep :: encodeLiteralListTokens clause) .finish

private theorem count_clause_path
    (formula : CNFFormula) (clause : List CNFLiteral)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (state : GrammarState)
    (gateCount scratch : Nat)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeClauseTokens clause ++ next :: tail)
    (active : state ∈ activeGrammarStates)
    (valid : validGrammarToken state .sep = true)
    (installed :
      postInstallEndpoint .count state .sep =
        .node countClauseRef)
    (gateBound :
      gateCount +
          clauseGateCharge formula.variableCount clause ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .count state).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (encodeClauseTokens clause ++ next :: tail) ++
          carrierFooterCells)
        [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .count state))
        (.node (firstBitRef .count .clausesNonempty))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .count .clausesNonempty).startState
        (CNFToNANDWorkspace.capacity formula)
        (literalListFinalScratch formula.variableCount clause scratch)
        (countedRegisters formula formula.variableCount
          (gateCount +
            clauseGateCharge formula.variableCount clause)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ encodeClauseTokens clause))
        (scanAfterCells next tail) [] finalTape ∧
      steps ≤
        countClauseEnvelope formula clause processed next tail
          gateCount scratch := by
  let body := encodeLiteralListTokens clause ++ [.finish]
  let bodyHead := body.headD .finish
  let bodyTail := body.tail ++ next :: tail
  have bodyNonempty : body ≠ [] := by
    simp [body]
  have separatorTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .sep :: bodyHead :: bodyTail := by
    cases bodyEq : body with
    | nil => exact False.elim (bodyNonempty bodyEq)
    | cons head rest =>
        simpa [body, bodyHead, bodyTail, bodyEq,
          encodeClauseTokens, List.append_assoc] using tokens
  have separatorInput :
      ScanRepresents (firstBitRef .count state).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .sep (bodyHead :: bodyTail)) []
        initialTape := by
    cases bodyEq : body with
    | nil => exact False.elim (bodyNonempty bodyEq)
    | cons head rest =>
        simpa [body, bodyHead, bodyTail, bodyEq,
          encodeClauseTokens, scanAfterCells,
          carrierGateCells, List.append_assoc] using represents
  rcases
      count_clause_separator_step_path formula processed
        bodyHead bodyTail state gateCount scratch separatorTokens
        active valid installed
        (by
          unfold clauseGateCharge at gateBound
          omega)
        scratchBound
        initialTape separatorInput with
    ⟨separatorSteps, bodyTape, separatorPath, bodyRepresents,
      separatorBound⟩
  have literalInput :
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount
          (gateCount + 2)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.sep]))
        (carrierGateCells
            (encodeLiteralListTokens clause ++
              .finish :: next :: tail) ++
          carrierFooterCells)
        [] bodyTape := by
    cases bodyEq : body with
    | nil => exact False.elim (bodyNonempty bodyEq)
    | cons head rest =>
        have bodyParts :
            encodeLiteralListTokens clause ++ [.finish] =
              head :: rest := by
          simpa [body] using bodyEq
        have remainingParts :
            encodeLiteralListTokens clause ++
                .finish :: next :: tail =
              head :: (rest ++ next :: tail) := by
          calc
            encodeLiteralListTokens clause ++
                  .finish :: next :: tail =
                (encodeLiteralListTokens clause ++ [.finish]) ++
                  next :: tail := by
                    simp [List.append_assoc]
            _ = (head :: rest) ++ next :: tail := by
                  rw [bodyParts]
            _ = head :: (rest ++ next :: tail) := rfl
        simpa [body, bodyHead, bodyTail, bodyEq, remainingParts,
          scanAfterCells, carrierGateCells,
          List.append_assoc] using bodyRepresents
  rcases
      count_literal_list_path formula clause
        (processed ++ [.sep]) .finish (next :: tail)
        (gateCount + 2) scratch
        (by
          simpa [encodeClauseTokens,
            List.append_assoc] using tokens)
        (by
          unfold clauseGateCharge at gateBound
          omega)
        scratchBound bodyTape literalInput with
    ⟨literalSteps, finishTape, literalPath, finishRepresents,
      literalBound⟩
  have finishTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        (processed ++ .sep :: encodeLiteralListTokens clause) ++
          .finish :: next :: tail := by
    simpa [encodeClauseTokens, List.append_assoc] using tokens
  have finishInput :
      ScanRepresents (firstBitRef .count .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        (literalListFinalScratch formula.variableCount clause scratch)
        (countedRegisters formula formula.variableCount
          (gateCount + 2 +
            (clause.map
              (literalGateCharge formula.variableCount)).sum)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ .sep :: encodeLiteralListTokens clause))
        (scanAfterCells .finish (next :: tail)) [] finishTape := by
    simpa [List.append_assoc] using finishRepresents
  rcases
      count_direct_token_step_path formula
        (processed ++ .sep :: encodeLiteralListTokens clause)
        .finish next tail .clause .clausesNonempty
        (countRuntime formula formula.variableCount
          (gateCount + 2 +
            (clause.map
              (literalGateCharge formula.variableCount)).sum)
          (literalListFinalScratch
            formula.variableCount clause scratch))
        finishTokens (by simp [activeGrammarStates]) (by decide)
        rfl (by decide) finishTape finishInput with
    ⟨finishSteps, finalTape, finishPath, finalRepresents,
      finishBound⟩
  refine
    ⟨separatorSteps + literalSteps + finishSteps, finalTape,
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        (AcceptPath.trans graph _ _ _ _ _ _ _ _
          separatorPath literalPath)
        finishPath, ?_, ?_⟩
  · simpa [clauseGateCharge, encodeClauseTokens,
      Nat.add_assoc, List.append_assoc] using finalRepresents
  · simpa [countClauseEnvelope, body, bodyHead, bodyTail] using
      Nat.add_le_add (Nat.add_le_add separatorBound literalBound)
        finishBound

private def clauseListFinalScratch
    (width : Nat) : List (List CNFLiteral) → Nat → Nat
  | [], scratch => scratch
  | clause :: rest, scratch =>
      clauseListFinalScratch width rest
        (literalListFinalScratch width clause scratch)

private theorem clauseListFinalScratch_lt_capacity
    (formula : CNFFormula) (clauses : List (List CNFLiteral))
    (scratch : Nat)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula) :
    clauseListFinalScratch formula.variableCount clauses scratch <
      CNFToNANDWorkspace.capacity formula := by
  induction clauses generalizing scratch with
  | nil =>
      simpa [clauseListFinalScratch] using scratchBound
  | cons clause rest inductionHypothesis =>
      apply inductionHypothesis
      induction clause generalizing scratch with
      | nil =>
          simpa [literalListFinalScratch] using scratchBound
      | cons literal literals literalInduction =>
          apply literalInduction
          exact
            Nat.lt_of_le_of_lt (Nat.min_le_right _ _)
              (variableCount_lt_capacity formula)

private def countClauseListEnvelope
    (formula : CNFFormula) :
    List (List CNFLiteral) → List CNFToken → Nat → Nat → Nat
  | [], _, _, _ => 0
  | clause :: rest, processed, gateCount, scratch =>
      let remaining := encodeClauseListTokens rest ++ [.finish]
      let next := remaining.headD .finish
      let tail := remaining.tail
      countClauseEnvelope formula clause processed next tail
          gateCount scratch +
        countClauseListEnvelope formula rest
          (processed ++ encodeClauseTokens clause)
          (gateCount +
            clauseGateCharge formula.variableCount clause)
          (literalListFinalScratch formula.variableCount
            clause scratch)

private theorem count_clause_list_path
    (formula : CNFFormula) (clauses : List (List CNFLiteral))
    (processed : List CNFToken) (state : GrammarState)
    (gateCount scratch : Nat)
    (nonempty : clauses ≠ [])
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeClauseListTokens clauses ++ [.finish])
    (active : state ∈ activeGrammarStates)
    (valid : validGrammarToken state .sep = true)
    (installed :
      postInstallEndpoint .count state .sep =
        .node countClauseRef)
    (gateBound :
      gateCount +
          clausesGateCharge formula.variableCount clauses ≤
        CNFToNANDWorkspace.compilerGateCount formula)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .count state).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount gateCount) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (encodeClauseListTokens clauses ++ [.finish]) ++
          carrierFooterCells)
        [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .count state))
        (.node (firstBitRef .count .clausesNonempty))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .count .clausesNonempty).startState
        (CNFToNANDWorkspace.capacity formula)
        (clauseListFinalScratch formula.variableCount
          clauses scratch)
        (countedRegisters formula formula.variableCount
          (gateCount +
            clausesGateCharge formula.variableCount clauses)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ encodeClauseListTokens clauses))
        (scanAfterCells .finish []) [] finalTape ∧
      steps ≤
        countClauseListEnvelope formula clauses processed
          gateCount scratch := by
  induction clauses generalizing processed state gateCount scratch
      initialTape with
  | nil =>
      exact False.elim (nonempty rfl)
  | cons clause rest inductionHypothesis =>
      let remaining := encodeClauseListTokens rest ++ [.finish]
      let next := remaining.headD .finish
      let tail := remaining.tail
      have remainingNonempty : remaining ≠ [] := by
        simp [remaining]
      have clauseTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ encodeClauseTokens clause ++ next :: tail := by
        cases remainingEq : remaining with
        | nil => exact False.elim (remainingNonempty remainingEq)
        | cons head remainingTail =>
            simpa [remaining, next, tail, remainingEq,
              encodeClauseListTokens, List.append_assoc] using tokens
      have clauseInput :
          ScanRepresents (firstBitRef .count state).startState
            (CNFToNANDWorkspace.capacity formula) scratch
            (countedRegisters formula formula.variableCount gateCount) []
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (carrierGateCells
                (encodeClauseTokens clause ++ next :: tail) ++
              carrierFooterCells)
            [] initialTape := by
        cases remainingEq : remaining with
        | nil => exact False.elim (remainingNonempty remainingEq)
        | cons head remainingTail =>
            simpa [remaining, next, tail, remainingEq,
              encodeClauseListTokens, carrierGateCells,
              List.append_assoc] using represents
      rcases
          count_clause_path formula clause processed next tail state
            gateCount scratch clauseTokens active valid installed
            (by
              simp only [clausesGateCharge] at gateBound
              omega)
            scratchBound initialTape clauseInput with
        ⟨clauseSteps, clauseTape, clausePath, clauseRepresents,
          clauseBound⟩
      cases rest with
      | nil =>
          refine
            ⟨clauseSteps, clauseTape, clausePath, ?_, ?_⟩
          · simpa [clauseListFinalScratch, clausesGateCharge,
              encodeClauseListTokens, remaining, next, tail,
              scanAfterCells, List.append_assoc] using
              clauseRepresents
          · simpa [countClauseListEnvelope, remaining, next, tail]
              using clauseBound
      | cons nextClause remainingClauses =>
          have recursiveTokens :
              CNFToNANDWorkspace.formulaTokens formula =
                (processed ++ encodeClauseTokens clause) ++
                  encodeClauseListTokens
                    (nextClause :: remainingClauses) ++ [.finish] := by
            simpa [encodeClauseListTokens,
              List.append_assoc] using tokens
          have recursiveInputRemaining :
              ScanRepresents
                (firstBitRef .count .clausesNonempty).startState
                (CNFToNANDWorkspace.capacity formula)
                (literalListFinalScratch formula.variableCount
                  clause scratch)
                (countedRegisters formula formula.variableCount
                  (gateCount +
                    clauseGateCharge formula.variableCount clause)) []
                (scanBeforeCells
                  (CNFToNANDWorkspace.formulaTokens formula)
                  (processed ++ encodeClauseTokens clause))
                (carrierGateCells remaining ++
                  carrierFooterCells)
                [] clauseTape := by
            cases remainingEq : remaining with
            | nil =>
                exact False.elim (remainingNonempty remainingEq)
            | cons head remainingTail =>
                simpa [next, tail, remainingEq, scanAfterCells,
                  carrierGateCells, List.append_assoc] using
                  clauseRepresents
          have recursiveInput :
              ScanRepresents
                (firstBitRef .count .clausesNonempty).startState
                (CNFToNANDWorkspace.capacity formula)
                (literalListFinalScratch formula.variableCount
                  clause scratch)
                (countedRegisters formula formula.variableCount
                  (gateCount +
                    clauseGateCharge formula.variableCount clause)) []
                (scanBeforeCells
                  (CNFToNANDWorkspace.formulaTokens formula)
                  (processed ++ encodeClauseTokens clause))
                (carrierGateCells
                    (encodeClauseListTokens
                        (nextClause :: remainingClauses) ++
                      [.finish]) ++
                  carrierFooterCells)
                [] clauseTape := by
            simpa [remaining] using recursiveInputRemaining
          have recursiveGateBound :
              (gateCount +
                    clauseGateCharge formula.variableCount clause) +
                  clausesGateCharge formula.variableCount
                    (nextClause :: remainingClauses) ≤
                CNFToNANDWorkspace.compilerGateCount formula := by
            simpa [clausesGateCharge, Nat.add_assoc] using gateBound
          have clauseScratchBound :
              literalListFinalScratch formula.variableCount
                  clause scratch <
                CNFToNANDWorkspace.capacity formula := by
            simpa [clauseListFinalScratch] using
              clauseListFinalScratch_lt_capacity formula
                [clause] scratch scratchBound
          rcases
              inductionHypothesis
                (processed ++ encodeClauseTokens clause)
                .clausesNonempty
                (gateCount +
                  clauseGateCharge formula.variableCount clause)
                (literalListFinalScratch formula.variableCount
                  clause scratch)
                (by simp)
                recursiveTokens
                (by simp [activeGrammarStates])
                (by decide)
                rfl
                recursiveGateBound
                clauseScratchBound
                clauseTape recursiveInput with
            ⟨tailSteps, finalTape, tailPath, finalRepresents,
              tailBound⟩
          refine
            ⟨clauseSteps + tailSteps, finalTape,
              AcceptPath.trans graph _ _ _ _ _ _ _ _
                clausePath tailPath, ?_, ?_⟩
          · simpa [clauseListFinalScratch, clausesGateCharge,
              encodeClauseListTokens, Nat.add_assoc,
              List.append_assoc] using finalRepresents
          · simpa [countClauseListEnvelope, remaining, next, tail] using
              Nat.add_le_add clauseBound tailBound

private theorem replicate_succ_append
    {α : Type} (count : Nat) (item : α) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      simpa only [Nat.succ_eq_add_one, List.replicate_succ,
        List.cons_append] using
        congrArg (List.cons item) inductionHypothesis

private theorem replicate_add
    {α : Type} (first second : Nat) (item : α) :
    List.replicate (first + second) item =
      List.replicate first item ++
        List.replicate second item := by
  induction first with
  | zero =>
      simp
  | succ first inductionHypothesis =>
      simpa only [Nat.succ_add, List.replicate_succ,
        List.cons_append] using
        congrArg (List.cons item) inductionHypothesis

private def countWidthEnvelope
    (formula : CNFFormula) : Nat → Nat → Nat
  | done, 0 =>
      tokenReadInstallSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          (List.replicate done .t) .f +
        tokenRestoreAdvanceSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          (List.replicate done .t) .f
  | done, remaining + 1 =>
      let processed := List.replicate done CNFToken.t
      let rest :=
        encodeUnaryTokens remaining ++
          encodeClauseListTokens formula.clauses ++ [.finish]
      tokenReadInstallSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .t +
        countBlockEnvelope formula
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed .t rest)
          (countRuntime formula done 0 0)
          countWidthUnitProgram +
        tokenRestoreAdvanceSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .t +
        countWidthEnvelope formula (done + 1) remaining

private theorem count_width_units_path
    (formula : CNFFormula) (done remaining : Nat)
    (sum : done + remaining = formula.variableCount)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .count .header).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula done 0) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (List.replicate done .t))
        (carrierGateCells
            (encodeUnaryTokens remaining ++
              encodeClauseListTokens formula.clauses ++ [.finish]) ++
          carrierFooterCells)
        [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .count .header))
        (.node (firstBitRef .count .clausesEmpty))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .count .clausesEmpty).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount 0) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (encodeUnaryTokens formula.variableCount))
        (carrierGateCells
            (encodeClauseListTokens formula.clauses ++ [.finish]) ++
          carrierFooterCells)
        [] finalTape ∧
      steps ≤ countWidthEnvelope formula done remaining := by
  induction remaining generalizing done initialTape with
  | zero =>
      let processed := List.replicate done CNFToken.t
      let suffix :=
        encodeClauseListTokens formula.clauses ++ [.finish]
      have widthEq : done = formula.variableCount := by
        omega
      have tokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ .f :: suffix := by
        simp [CNFToNANDWorkspace.formulaTokens,
          encodeFormulaTokens, encodeCNFTokens,
          encodeUnaryTokens_eq_replicate, processed, suffix,
          widthEq, List.append_assoc]
      have readInput :
          ScanRepresents (firstBitRef .count .header).startState
            (CNFToNANDWorkspace.capacity formula) 0
            (countedRegisters formula done 0) []
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells .f suffix) [] initialTape := by
        simpa [processed, suffix, encodeUnaryTokens, scanAfterCells,
          carrierGateCells, carrierGateCellsFor] using represents
      rcases token_read_install_path .count formula processed .f
          suffix .header (countRuntime formula done 0 0)
          tokens (by simp [activeGrammarStates]) (by decide)
          initialTape readInput with
        ⟨installedTape, readPath, installedRepresents⟩
      have suffixNonempty : suffix ≠ [] := by
        simp [suffix]
      cases suffixEq : suffix with
      | nil =>
          exact False.elim (suffixNonempty suffixEq)
      | cons next tail =>
          have restoreInput :
              TapeRepresents
                (restoreRef .count .clausesEmpty .f).startState
                (CNFToNANDWorkspace.capacity formula) 0
                (countedRegisters formula done 0) []
                (markedSource
                  (CNFToNANDWorkspace.formulaTokens formula)
                  processed .f (next :: tail))
                [] installedTape := by
            simpa [TapeRepresents, countRuntime,
              postInstallEndpoint, suffixEq] using
              (represents_at_state
                (newState :=
                  (restoreRef .count .clausesEmpty .f).startState)
                installedRepresents)
          rcases token_restore_advance_next_path .count formula
              processed .f next tail .clausesEmpty
              (countRuntime formula done 0 0)
              (by simpa [suffixEq] using tokens)
              (by decide) installedTape restoreInput with
            ⟨finalTape, restorePath, finalRepresents⟩
          refine
            ⟨tokenReadInstallSteps
                (CNFToNANDWorkspace.formulaTokens formula)
                processed .f +
              tokenRestoreAdvanceSteps
                (CNFToNANDWorkspace.formulaTokens formula)
                processed .f,
              finalTape, ?_, ?_, ?_⟩
          · exact
              AcceptPath.trans graph
                (.node (firstBitRef .count .header))
                (.node (restoreRef .count .clausesEmpty .f))
                (.node (firstBitRef .count .clausesEmpty))
                _ _ initialTape installedTape finalTape
                (by simpa [postInstallEndpoint] using readPath)
                restorePath
          · simpa [processed, suffix, suffixEq, widthEq,
              encodeUnaryTokens_eq_replicate,
              replicate_succ_append, scanBeforeCells,
              scanAfterCells, carrierGateCells,
              carrierGateCellsFor,
              List.append_assoc] using finalRepresents
          · simp [countWidthEnvelope, processed]
  | succ remaining inductionHypothesis =>
      let processed := List.replicate done CNFToken.t
      let rest :=
        encodeUnaryTokens remaining ++
          encodeClauseListTokens formula.clauses ++ [.finish]
      have tokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ .t :: rest := by
        have widthEq :
            formula.variableCount = done + (remaining + 1) := by
          omega
        rw [CNFToNANDWorkspace.formulaTokens,
          encodeFormulaTokens, encodeCNFTokens,
          encodeUnaryTokens_eq_replicate, widthEq,
          replicate_add]
        simp [processed, rest, List.replicate_succ,
          encodeUnaryTokens_eq_replicate,
          List.append_assoc]
      have readInput :
          ScanRepresents (firstBitRef .count .header).startState
            (CNFToNANDWorkspace.capacity formula) 0
            (countedRegisters formula done 0) []
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells .t rest) [] initialTape := by
        simpa [processed, rest, scanAfterCells,
          carrierGateCells, carrierGateCellsFor,
          encodeUnaryTokens] using represents
      rcases token_read_install_path .count formula processed .t
          rest .header (countRuntime formula done 0 0)
          tokens (by simp [activeGrammarStates]) (by decide)
          initialTape readInput with
        ⟨installedTape, readPath, installedRepresents⟩
      let context :=
        markedSourceContext formula processed .t rest tokens
      have widthLt : done < formula.variableCount := by
        omega
      rcases count_width_block_path
          (context := context)
          formula done 0 0 widthLt (by simp) (by simp)
          installedTape
          (by
            simpa [TapeRepresents, countRuntime,
              postInstallEndpoint] using
              (represents_at_state
                (newState := countWidthRef.startState)
                installedRepresents)) with
        ⟨blockSteps, blockTape, blockPath, blockRepresents,
          blockBound⟩
      have restNonempty : rest ≠ [] := by
        simp [rest, encodeUnaryTokens_eq_replicate]
      cases restEq : rest with
      | nil =>
          exact False.elim (restNonempty restEq)
      | cons next tail =>
          have restoreInput :
              TapeRepresents
                (restoreRef .count .header .t).startState
                (CNFToNANDWorkspace.capacity formula) 0
                (countedRegisters formula (done + 1) 0) []
                (markedSource
                  (CNFToNANDWorkspace.formulaTokens formula)
                  processed .t (next :: tail))
                [] blockTape := by
            simpa [restEq] using blockRepresents
          rcases token_restore_advance_next_path .count formula
              processed .t next tail .header
              (countRuntime formula (done + 1) 0 0)
              (by simpa [restEq] using tokens)
              (by decide) blockTape restoreInput with
            ⟨nextTape, restorePath, nextRepresents⟩
          have tailInput :
              ScanRepresents
                (firstBitRef .count .header).startState
                (CNFToNANDWorkspace.capacity formula) 0
                (countedRegisters formula (done + 1) 0) []
                (scanBeforeCells
                  (CNFToNANDWorkspace.formulaTokens formula)
                  (List.replicate (done + 1) .t))
                (carrierGateCells
                    (encodeUnaryTokens remaining ++
                      encodeClauseListTokens formula.clauses ++
                        [.finish]) ++
                  carrierFooterCells)
                [] nextTape := by
            simpa [processed, rest, restEq,
              replicate_succ_append, scanAfterCells,
              carrierGateCells, carrierGateCellsFor,
              List.append_assoc] using
              nextRepresents
          rcases inductionHypothesis (done + 1)
              (by omega) nextTape tailInput with
            ⟨tailSteps, finalTape, tailPath, finalRepresents,
              tailBound⟩
          let firstSteps :=
            tokenReadInstallSteps
                (CNFToNANDWorkspace.formulaTokens formula)
                processed .t +
              blockSteps +
              tokenRestoreAdvanceSteps
                (CNFToNANDWorkspace.formulaTokens formula)
                processed .t
          have throughBlock :=
            AcceptPath.trans graph
              (.node (firstBitRef .count .header))
              (.node countWidthRef)
              (.node (restoreRef .count .header .t))
              _ _ initialTape installedTape blockTape
              (by simpa [postInstallEndpoint] using readPath)
              blockPath
          have throughRestore :=
            AcceptPath.trans graph
              (.node (firstBitRef .count .header))
              (.node (restoreRef .count .header .t))
              (.node (firstBitRef .count .header))
              _ _ initialTape blockTape nextTape
              throughBlock restorePath
          refine
            ⟨firstSteps + tailSteps, finalTape, ?_,
              finalRepresents, ?_⟩
          · exact
              AcceptPath.trans graph
                (.node (firstBitRef .count .header))
                (.node (firstBitRef .count .header))
                (.node (firstBitRef .count .clausesEmpty))
                firstSteps tailSteps initialTape nextTape finalTape
                (by simpa [firstSteps, Nat.add_assoc] using
                  throughRestore)
                tailPath
          · dsimp [firstSteps]
            simp only [countWidthEnvelope]
            dsimp [processed, rest] at blockBound ⊢
            omega

private def countEmptyTraversalEnvelope
    (formula : CNFFormula) : Nat :=
  countHeaderScanSteps formula +
    countWidthEnvelope formula 0 formula.variableCount +
    countFinishStepEnvelope formula
      (encodeUnaryTokens formula.variableCount)

private theorem count_empty_traversal_path
    (formula : CNFFormula) (empty : formula.clauses = [])
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (passHeaderRef .count).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula 0 0) []
        (canonicalSource formula) [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (passHeaderRef .count))
        (.node (programEndRef .count .empty))
        steps initialTape finalTape ∧
      ScanRepresents (programEndRef .count .empty).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount 0) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (CNFToNANDWorkspace.formulaTokens formula))
        carrierFooterCells [] finalTape ∧
      steps ≤ countEmptyTraversalEnvelope formula := by
  rcases
      count_header_path formula (countRuntime formula 0 0 0)
        initialTape (by simpa [countRuntime] using represents) with
    ⟨first, rest, headerTape, headerTokensEq, headerPath,
      headerRepresents⟩
  have headerInput :
      ScanRepresents (firstBitRef .count .header).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula 0 0) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) [])
        (carrierGateCells
            (CNFToNANDWorkspace.formulaTokens formula) ++
          carrierFooterCells)
        [] headerTape := by
    rw [headerTokensEq]
    simpa [scanBeforeCells, carrierGateCells] using headerRepresents
  rcases
      count_width_units_path formula 0 formula.variableCount
        (by omega) headerTape headerInput with
    ⟨widthSteps, widthTape, widthPath, widthRepresents,
      widthBound⟩
  have finishTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        encodeUnaryTokens formula.variableCount ++ [.finish] := by
    simp [CNFToNANDWorkspace.formulaTokens,
      encodeFormulaTokens, encodeCNFTokens, empty,
      encodeClauseListTokens]
  have finishInput :
      ScanRepresents
        (firstBitRef .count .clausesEmpty).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount 0) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (encodeUnaryTokens formula.variableCount))
        (scanAfterCells .finish []) [] widthTape := by
    simpa [empty, encodeClauseListTokens, scanAfterCells,
      carrierGateCells] using widthRepresents
  rcases
      count_finish_path formula
        (encodeUnaryTokens formula.variableCount)
        .clausesEmpty .finishedEmpty .empty
        (countRuntime formula formula.variableCount 0 0)
        finishTokens (by simp [activeGrammarStates]) (by decide)
        rfl rfl widthTape finishInput with
    ⟨finishSteps, finalTape, finishPath, finalRepresents,
      finishBound⟩
  refine
    ⟨countHeaderScanSteps formula + widthSteps + finishSteps,
      finalTape,
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        (AcceptPath.trans graph _ _ _ _ _ _ _ _
          headerPath widthPath)
        finishPath, ?_, ?_⟩
  · simpa [countRuntime, finishTokens] using finalRepresents
  · simpa [countEmptyTraversalEnvelope] using
      Nat.add_le_add
        (Nat.add_le_add (Nat.le_refl _) widthBound)
        finishBound

private def countNonemptyTraversalEnvelope
    (formula : CNFFormula) : Nat :=
  countHeaderScanSteps formula +
    countWidthEnvelope formula 0 formula.variableCount +
    countClauseListEnvelope formula formula.clauses
      (encodeUnaryTokens formula.variableCount) 0 0 +
    countFinishStepEnvelope formula
      (encodeUnaryTokens formula.variableCount ++
        encodeClauseListTokens formula.clauses)

private theorem count_nonempty_traversal_path
    (formula : CNFFormula) (nonempty : formula.clauses ≠ [])
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (passHeaderRef .count).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula 0 0) []
        (canonicalSource formula) [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (passHeaderRef .count))
        (.node (programEndRef .count .nonempty))
        steps initialTape finalTape ∧
      ScanRepresents (programEndRef .count .nonempty).startState
        (CNFToNANDWorkspace.capacity formula)
        (clauseListFinalScratch formula.variableCount
          formula.clauses 0)
        (countedRegisters formula formula.variableCount
          (CNFToNANDWorkspace.compilerGateCount formula)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (CNFToNANDWorkspace.formulaTokens formula))
        carrierFooterCells [] finalTape ∧
      steps ≤ countNonemptyTraversalEnvelope formula := by
  rcases
      count_header_path formula (countRuntime formula 0 0 0)
        initialTape (by simpa [countRuntime] using represents) with
    ⟨first, rest, headerTape, headerTokensEq, headerPath,
      headerRepresents⟩
  have headerInput :
      ScanRepresents (firstBitRef .count .header).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula 0 0) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) [])
        (carrierGateCells
            (CNFToNANDWorkspace.formulaTokens formula) ++
          carrierFooterCells)
        [] headerTape := by
    rw [headerTokensEq]
    simpa [scanBeforeCells, carrierGateCells] using headerRepresents
  rcases
      count_width_units_path formula 0 formula.variableCount
        (by omega) headerTape headerInput with
    ⟨widthSteps, widthTape, widthPath, widthRepresents,
      widthBound⟩
  have compilerEq :
      CNFToNANDWorkspace.compilerGateCount formula =
        clausesGateCharge formula.variableCount formula.clauses := by
    rw [compilerGateCount_eq_count_charge]
    cases clausesEq : formula.clauses with
    | nil => exact False.elim (nonempty clausesEq)
    | cons clause clauses =>
        simp [clausesEq]
  have clausesTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        encodeUnaryTokens formula.variableCount ++
          encodeClauseListTokens formula.clauses ++ [.finish] := by
    rfl
  rcases
      count_clause_list_path formula formula.clauses
        (encodeUnaryTokens formula.variableCount)
        .clausesEmpty 0 0 nonempty clausesTokens
        (by simp [activeGrammarStates]) (by decide) rfl
        (by
          rw [← compilerEq]
          omega)
        (by
          exact Nat.zero_lt_of_lt (variableCount_lt_capacity formula))
        widthTape widthRepresents with
    ⟨clauseSteps, clauseTape, clausePath, clauseRepresents,
      clauseBound⟩
  have finishTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        (encodeUnaryTokens formula.variableCount ++
          encodeClauseListTokens formula.clauses) ++ [.finish] := by
    simpa [List.append_assoc] using clausesTokens
  have finishInput :
      ScanRepresents
        (firstBitRef .count .clausesNonempty).startState
        (CNFToNANDWorkspace.capacity formula)
        (clauseListFinalScratch formula.variableCount
          formula.clauses 0)
        (countedRegisters formula formula.variableCount
          (CNFToNANDWorkspace.compilerGateCount formula)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (encodeUnaryTokens formula.variableCount ++
            encodeClauseListTokens formula.clauses))
        (scanAfterCells .finish []) [] clauseTape := by
    rw [compilerEq]
    simpa using clauseRepresents
  rcases
      count_finish_path formula
        (encodeUnaryTokens formula.variableCount ++
          encodeClauseListTokens formula.clauses)
        .clausesNonempty .finishedNonempty .nonempty
        (countRuntime formula formula.variableCount
          (CNFToNANDWorkspace.compilerGateCount formula)
          (clauseListFinalScratch formula.variableCount
            formula.clauses 0))
        finishTokens (by simp [activeGrammarStates]) (by decide)
        rfl rfl clauseTape finishInput with
    ⟨finishSteps, finalTape, finishPath, finalRepresents,
      finishBound⟩
  refine
    ⟨countHeaderScanSteps formula + widthSteps +
        clauseSteps + finishSteps,
      finalTape,
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        (AcceptPath.trans graph _ _ _ _ _ _ _ _
          (AcceptPath.trans graph _ _ _ _ _ _ _ _
            headerPath widthPath)
          clausePath)
        finishPath, ?_, ?_⟩
  · simpa [countRuntime, finishTokens] using finalRepresents
  · simpa [countNonemptyTraversalEnvelope, Nat.add_assoc] using
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.le_refl (countHeaderScanSteps formula)) widthBound)
          clauseBound)
        finishBound

private def countRewindBefore (formula : CNFFormula) :
    List WorkSymbol :=
  scanBeforeCells
      (CNFToNANDWorkspace.formulaTokens formula)
      (CNFToNANDWorkspace.formulaTokens formula) ++
    [SourceParser.cell10, SourceParser.cell00]

private def countRewindAfter : List WorkSymbol :=
  [ SourceParser.cell00
  , SourceParser.cell10
  , SourceParser.cell01
  , SourceParser.cell10
  , SourceParser.cell11
  ]

private theorem canonicalSource_eq_countRewindSplit
    (formula : CNFFormula) :
    canonicalSource formula =
      countRewindBefore formula ++
        SourceParser.cell01 :: countRewindAfter := by
  rw [canonicalSource_eq_carrier_layout]
  simp [countRewindBefore, countRewindAfter, scanBeforeCells,
    carrierFooterCells, SourceParser.sourceCells,
    List.append_assoc]

private theorem count_rewind_path
    (formula : CNFFormula) (kind : FinishKind)
    (runtime : Runtime) (initialTape : WorkTape)
    (represents :
      ScanRepresents (countRewindRef kind).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (countRewindBefore formula)
        (SourceParser.cell01 :: countRewindAfter)
        runtime.targetTokens initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node (countRewindRef kind))
        (.node (countInstallVersionRef kind))
        (sourceRewindSteps (countRewindBefore formula))
        initialTape finalTape ∧
      TapeRepresents (countInstallVersionRef kind).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (canonicalSource formula) runtime.targetTokens finalTape := by
  have beforePacked :
      ∀ symbol, symbol ∈ countRewindBefore formula →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    apply canonicalSource_packed formula symbol
    rw [canonicalSource_eq_countRewindSplit]
    exact List.mem_append_left _ member
  rcases
      source_rewind_path (Address.countRewind kind)
        (countInstallVersionRef kind).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (countRewindBefore formula)
        SourceParser.cell01 countRewindAfter runtime.targetTokens
        (.node (countInstallVersionRef kind))
        (by
          simpa [countRewindNode] using
            countRewindNode_member kind)
        beforePacked TargetEmitter.PackedSymbol.zeroOne
        initialTape represents with
    ⟨finalTape, path, finalRepresents⟩
  refine ⟨finalTape, ?_, ?_⟩
  · simpa [countRewindRef] using path
  · rw [canonicalSource_eq_countRewindSplit formula]
    exact finalRepresents

private def versionMarkedSource (formula : CNFFormula) :
    List WorkSymbol :=
  TargetEmitterCursorAppender.cursorMarker ::
    (canonicalSource formula).tail

private def versionMarkedSourceContext (formula : CNFFormula) :
    SourceContext (versionMarkedSource formula) :=
  { head := TargetEmitterCursorAppender.cursorMarker
    tail := (canonicalSource formula).tail
    source_eq := rfl
    allowed := Or.inr rfl }

private def versionMarkedCursorLayout (formula : CNFFormula) :
    CursorLayout (versionMarkedSource formula) := by
  refine
    { cursorBefore := []
      cursorOriginal := SourceParser.cell00
      cursorAfter := (canonicalSource formula).tail
      cursorSource := ?_
      originalPacked := ?_
      beforePacked := ?_
      afterPacked := ?_ }
  · simp [versionMarkedSource,
      TargetEmitterCursorAppender.sourceWithCursor]
  · intro symbol member
    apply canonicalSource_packed formula symbol
    change
      symbol ∈
        SourceParser.cell00 :: (canonicalSource formula).tail at member
    rw [canonicalSource_eq_cons formula]
    exact member
  · simp
  · intro symbol member
    apply canonicalSource_packed formula symbol
    rw [canonicalSource_eq_cons formula]
    exact List.Mem.tail _ member

private def countAfterInstallRef (kind : FinishKind) : NodeRef :=
  match kind with
  | .empty => countEmptyFormulaRef
  | .nonempty => emittedHeaderRef

private def countInstallVersionSteps : Nat := 3

private theorem count_install_version_path
    (formula : CNFFormula) (kind : FinishKind)
    (runtime : Runtime) (initialTape : WorkTape)
    (represents :
      TapeRepresents (countInstallVersionRef kind).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (canonicalSource formula) runtime.targetTokens initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node (countInstallVersionRef kind))
        (.node (countAfterInstallRef kind))
        countInstallVersionSteps initialTape finalTape ∧
      TapeRepresents (countAfterInstallRef kind).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (versionMarkedSource formula) runtime.targetTokens finalTape := by
  let capacity := CNFToNANDWorkspace.capacity formula
  let workspace :=
    TargetEmitterRuntime.logicalLeftWorkspace capacity
      runtime.scratch runtime.registers runtime.checks
  let outsideLeft := workspace.tail
  let suffix :=
    TargetEmitter.sourceTargetBoundary ::
      SourceParser.packedTokenCells runtime.targetTokens
  let canonicalInitial :=
    focusTape workspace (canonicalSource formula ++ suffix)
  let canonicalFinal :=
    focusTape workspace (versionMarkedSource formula ++ suffix)
  have workspaceEq :
      workspace =
        TargetEmitter.sourceLeftBoundary :: outsideLeft := by
    rfl
  have run :
      workRunExact?
          (TargetEmitterCursorControl.installMachine
            WorkSymbol.zeroZero)
          2
          { state :=
              (TargetEmitterCursorControl.installMachine
                WorkSymbol.zeroZero).startState
            tape := canonicalInitial } =
        some
          { state :=
              (TargetEmitterCursorControl.installMachine
                WorkSymbol.zeroZero).acceptState
            tape := canonicalFinal } := by
    rw [cursorControl_configAtWord_eq,
      cursorControl_configAtWord_eq]
    rw [canonicalSource_eq_cons formula]
    simpa [workspaceEq,
      versionMarkedSource, suffix,
      TargetEmitterCursorControl.installMachine,
      TargetEmitterCursorControl.installState,
      TargetEmitterCursorControl.installedState,
      TargetEmitterCursorControl.cursorMark,
      SourceParser.cell00,
      TargetEmitterCursorAppender.cursorMarker,
      List.append_assoc] using
      TargetEmitterCursorControl.install_exact
        WorkSymbol.zeroZero [] (canonicalSource formula).tail
        outsideLeft suffix TargetEmitter.PackedSymbol.zeroZero
        (by simp)
  have terminal :
      AcceptPath graph (.node (countAfterInstallRef kind))
        (.node (countAfterInstallRef kind)) 0
        canonicalFinal canonicalFinal := .terminal _ _
  have canonicalPath :
      AcceptPath graph (.node (countInstallVersionRef kind))
        (.node (countAfterInstallRef kind))
        countInstallVersionSteps canonicalInitial canonicalFinal := by
    simpa [countInstallVersionSteps, countInstallVersionRef,
      countInstallVersionNode, countAfterInstallRef] using
      localAccept_path
        (Address.countInstallVersion kind)
        (TargetEmitterCursorControl.installMachine
          WorkSymbol.zeroZero)
        (.node (countAfterInstallRef kind)) .reject
        (.node (countAfterInstallRef kind))
        2 0 canonicalInitial canonicalFinal canonicalFinal
        (by
          cases kind with
          | empty =>
              simpa [countInstallVersionNode,
                countAfterInstallRef] using
                countInstallVersionNode_member .empty
          | nonempty =>
              simpa [countInstallVersionNode,
                countAfterInstallRef] using
                countInstallVersionNode_member .nonempty)
        run terminal
  have initialEquivalent :
      WorkTape.BlankEquivalent initialTape canonicalInitial := by
    have tapeEquivalent := represents.tape
    have tapeEquivalent' :
        WorkTape.BlankEquivalent initialTape
          (TargetEmitter.configAtWord
            (countInstallVersionRef kind).startState workspace
            (canonicalSource formula ++ suffix)).tape := by
      simpa [TapeRepresents, TargetEmitterRuntime.Represents,
        TargetEmitterRuntime.logicalConfiguration,
        TargetEmitterRuntime.logicalWord,
        workspace, suffix, capacity,
        List.append_assoc] using tapeEquivalent
    rw [targetEmitter_configAtWord_tape_eq] at tapeEquivalent'
    simpa [canonicalInitial, workspace, suffix, capacity,
      List.append_assoc] using tapeEquivalent'
  rcases AcceptPath.transport canonicalPath initialEquivalent with
    ⟨finalTape, path, finalEquivalent⟩
  refine ⟨finalTape, path, ?_⟩
  unfold TapeRepresents TargetEmitterRuntime.Represents
  refine
    ⟨TargetEmitterRuntime.logicalConfiguration_state
        (countAfterInstallRef kind).startState capacity
        runtime.scratch runtime.registers runtime.checks
        (versionMarkedSource formula) runtime.targetTokens |>.symm, ?_⟩
  simpa [canonicalFinal, workspace, suffix, capacity,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterRuntime.logicalLeftWorkspace,
    targetEmitter_configAtWord_tape_eq,
    List.append_assoc] using finalEquivalent

private theorem emitRetainedNatMarked_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (coordinate :
      PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (valueBound :
      coordinate.value runtime ≤ capacity) :
    ProgramSafe capacity source context
      (PNP.Concrete.CNFToNANDEmitterPlan.emitRetainedNatProgram
        .marked coordinate)
      runtime
      (PNP.Concrete.CNFToNANDEmitterPlan.emittedNatResult
        runtime (coordinate.value runtime)) := by
  cases coordinate with
  | sourceWidth =>
      let reset := { runtime with scratch := 0 }
      let loaded :=
        { runtime with
          scratch := runtime.registers.inputCount }
      have resetSafe :=
        resetScratch_safe (context := context) runtime scratchBound
      have addSafe :
          ProgramSafe capacity source context
            [.addRegister .inputCount] reset loaded := by
        simpa [reset, loaded,
          PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.value,
          TargetEmitterLedger.slotValue] using
          addRegister_safe (context := context) reset
            .inputCount .inputCount rfl fits
            (by
              simpa [reset,
                PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.value,
                TargetEmitterLedger.slotValue]
                using valueBound)
      have emitSafe :=
        emitScratchMarked_safe (context := context)
          layout loaded
          (by
            simpa [loaded,
              PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.value]
              using valueBound)
      simpa [
        PNP.Concrete.CNFToNANDEmitterPlan.emitRetainedNatProgram,
        PNP.Concrete.CNFToNANDEmitterPlan.emittedNatResult,
        PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.counter,
        PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.value,
        reset, loaded, List.append_assoc] using
        resetSafe.append (addSafe.append emitSafe)
  | totalGateCount =>
      let reset := { runtime with scratch := 0 }
      let loaded :=
        { runtime with
          scratch := runtime.registers.currentGate }
      have resetSafe :=
        resetScratch_safe (context := context) runtime scratchBound
      have addSafe :
          ProgramSafe capacity source context
            [.addRegister .currentGate] reset loaded := by
        simpa [reset, loaded,
          PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.value,
          TargetEmitterLedger.slotValue] using
          addRegister_safe (context := context) reset
            .currentGate .currentGate rfl fits
            (by
              simpa [reset,
                PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.value,
                TargetEmitterLedger.slotValue]
                using valueBound)
      have emitSafe :=
        emitScratchMarked_safe (context := context)
          layout loaded
          (by
            simpa [loaded,
              PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.value]
              using valueBound)
      simpa [
        PNP.Concrete.CNFToNANDEmitterPlan.emitRetainedNatProgram,
        PNP.Concrete.CNFToNANDEmitterPlan.emittedNatResult,
        PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.counter,
        PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.value,
        reset, loaded, List.append_assoc] using
        resetSafe.append (addSafe.append emitSafe)

private def emitHeaderRuntime (formula : CNFFormula) : Runtime :=
  { captured := 0
    scratch := CNFToNANDWorkspace.compilerGateCount formula
    registers := CNFToNANDWorkspace.workspaceRegisters formula
    checks := []
    targetTokens := headerTokens formula }

private theorem emitHeader_safe
    {source : List WorkSymbol} {context : SourceContext source}
    (layout : CursorLayout source) (formula : CNFFormula)
    (scratch : Nat)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula) :
    ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
      emitCircuitHeaderProgram
      (countRuntime formula formula.variableCount
        (CNFToNANDWorkspace.compilerGateCount formula) scratch)
      (emitHeaderRuntime formula) := by
  let initial :=
    countRuntime formula formula.variableCount
      (CNFToNANDWorkspace.compilerGateCount formula) scratch
  let afterVersion : Runtime :=
    { initial with targetTokens := [.version0] }
  let afterWidth :=
    PNP.Concrete.CNFToNANDEmitterPlan.emittedNatResult
      afterVersion formula.variableCount
  have fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        initial.registers := by
    simpa [initial, countRuntime, countedRegisters_final] using
      countedRegisters_fits formula formula.variableCount
        (CNFToNANDWorkspace.compilerGateCount formula)
        (Nat.le_refl _) (Nat.le_refl _)
  have versionSafe :
      ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
        [.append .marked .version0] initial afterVersion := by
    simpa [initial, afterVersion, countRuntime] using
      appendMarked_safe (context := context)
        layout initial .version0
  have widthSafe :
      ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
        (PNP.Concrete.CNFToNANDEmitterPlan.emitRetainedNatProgram
          .marked
          .sourceWidth)
        afterVersion afterWidth := by
    apply emitRetainedNatMarked_safe
      (context := context) layout afterVersion .sourceWidth
    · simpa [afterVersion] using fits
    · simpa [afterVersion, initial, countRuntime] using scratchBound
    · simp [afterVersion, initial, countRuntime,
        PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.value]
      exact
        CNFToNANDWorkspace.variableCount_le_capacity formula
  have gateSafe :
      ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
        (PNP.Concrete.CNFToNANDEmitterPlan.emitRetainedNatProgram
          .marked
          .totalGateCount)
        afterWidth (emitHeaderRuntime formula) := by
    have raw :=
      emitRetainedNatMarked_safe (context := context)
        layout afterWidth
        PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.totalGateCount
        (by
          simpa [afterWidth, afterVersion,
            PNP.Concrete.CNFToNANDEmitterPlan.emittedNatResult] using
            fits)
        (by
          simpa [afterWidth, afterVersion, initial,
            PNP.Concrete.CNFToNANDEmitterPlan.emittedNatResult,
            countRuntime] using
            variableCount_lt_capacity formula)
        (by
          simp [afterWidth, afterVersion, initial,
            PNP.Concrete.CNFToNANDEmitterPlan.emittedNatResult,
            countRuntime,
            PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.value]
          exact Nat.le_of_lt
            (CNFToNANDWorkspace.compilerGateCount_lt_capacity formula))
    simpa [emitHeaderRuntime, afterWidth, afterVersion, initial,
      PNP.Concrete.CNFToNANDEmitterPlan.emittedNatResult,
      countRuntime, countedRegisters_final, headerTokens,
      CNFToNANDWorkspace.workspaceRegisters_currentGate,
      PNP.Concrete.CNFToNANDEmitterPlan.RetainedCoordinate.value,
      List.append_assoc] using raw
  have all := versionSafe.append (widthSafe.append gateSafe)
  simpa [emitCircuitHeaderProgram,
    CNFToNANDControllerBlocks.mode,
    PNP.Concrete.CNFToNANDEmitterPlan.circuitHeaderProgram,
    initial, List.append_assoc] using all

private def emitHeaderEnvelope (formula : CNFFormula)
    (scratch : Nat) : Nat :=
  countBlockEnvelope formula (versionMarkedSource formula)
    (countRuntime formula formula.variableCount
      (CNFToNANDWorkspace.compilerGateCount formula) scratch)
    emitCircuitHeaderProgram

private theorem emit_header_block_path
    (formula : CNFFormula) (scratch : Nat)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents emittedHeaderRef.startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (CNFToNANDWorkspace.workspaceRegisters formula) []
        (versionMarkedSource formula) [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node emittedHeaderRef)
        (.node initializeFormulaRef)
        steps initialTape finalTape ∧
      TapeRepresents initializeFormulaRef.startState
        (CNFToNANDWorkspace.capacity formula)
        (CNFToNANDWorkspace.compilerGateCount formula)
        (CNFToNANDWorkspace.workspaceRegisters formula) []
        (versionMarkedSource formula) (headerTokens formula) finalTape ∧
      steps ≤ emitHeaderEnvelope formula scratch := by
  have safe :=
    emitHeader_safe
      (context := versionMarkedSourceContext formula)
      (versionMarkedCursorLayout formula) formula scratch scratchBound
  have input :
      TapeRepresents
        (blockEntry blockDescriptors[17].code
          blockDescriptors[17].primitives).startState
        (CNFToNANDWorkspace.capacity formula)
        (countRuntime formula formula.variableCount
          (CNFToNANDWorkspace.compilerGateCount formula) scratch).scratch
        (countRuntime formula formula.variableCount
          (CNFToNANDWorkspace.compilerGateCount formula) scratch).registers
        (countRuntime formula formula.variableCount
          (CNFToNANDWorkspace.compilerGateCount formula) scratch).checks
        (versionMarkedSource formula)
        (countRuntime formula formula.variableCount
          (CNFToNANDWorkspace.compilerGateCount formula) scratch).targetTokens
        initialTape := by
    simpa [blockDescriptors, emittedHeaderRef,
      countRuntime, countedRegisters_final] using represents
  rcases indexedBlock_path 17 (by decide)
      initializeFormulaRef.startState safe
      (Nat.le_of_lt scratchBound) initialTape input with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape,
      by simpa [blockDescriptors, emittedHeaderRef] using path,
      by simpa [emitHeaderRuntime] using finalRepresents,
      by
        simpa [emitHeaderEnvelope, countBlockEnvelope,
          blockDescriptors, countRuntime] using bound⟩

private theorem formulaStackMarker_lt_capacity
    (formula : CNFFormula) :
    CNFToNANDWorkspace.formulaStackMarker formula <
      CNFToNANDWorkspace.capacity formula := by
  rw [CNFToNANDWorkspace.formulaStackMarker_exact,
    CNFToNANDWorkspace.capacity_exact]
  omega

private theorem initializeFormula_safe
    {source : List WorkSymbol} {context : SourceContext source}
    (formula : CNFFormula) :
    ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
      initializeFormulaStackProgram
      (emitHeaderRuntime formula)
      (emitInitialRuntime formula) := by
  let initial := emitHeaderRuntime formula
  let reset := { initial with scratch := 0 }
  let marker :=
    { initial with
      scratch := CNFToNANDWorkspace.formulaStackMarker formula }
  let pushed :=
    { marker with
      checks := [CNFToNANDWorkspace.formulaStackMarker formula] }
  have fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        initial.registers := by
    simpa [initial, emitHeaderRuntime, countedRegisters_final] using
      countedRegisters_fits formula formula.variableCount
        (CNFToNANDWorkspace.compilerGateCount formula)
        (Nat.le_refl _) (Nat.le_refl _)
  have resetSafe :
      ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
        [.resetScratch] initial reset := by
    simpa [initial, reset, emitHeaderRuntime] using
      resetScratch_safe (context := context) initial
        (by
          simpa [initial, emitHeaderRuntime] using
            CNFToNANDWorkspace.compilerGateCount_lt_capacity formula)
  have markerSafe :
      ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
        [.addRegister .carrierWidth] reset marker := by
    simpa [initial, reset, marker, emitHeaderRuntime,
      CNFToNANDWorkspace.workspaceRegisters_carrierWidth_eq_formulaStackMarker,
      TargetEmitterLedger.slotValue] using
      addRegister_safe (context := context) reset
        .carrierWidth .carrierWidth rfl fits
        (by
          simpa [reset, initial, emitHeaderRuntime,
            TargetEmitterLedger.slotValue,
            CNFToNANDWorkspace.workspaceRegisters_carrierWidth_eq_formulaStackMarker]
            using
              CNFToNANDWorkspace.formulaStackMarker_le_capacity formula)
  have pushSafe :
      ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
        [.pushCheck] marker pushed := by
    simpa [initial, marker, pushed, emitHeaderRuntime] using
      pushCheck_safe (context := context) marker
        (by simpa [marker, initial] using fits)
        (by
          simpa [marker] using
            CNFToNANDWorkspace.formulaStackMarker_le_capacity formula)
  have finalSafe :
      ProgramSafe (CNFToNANDWorkspace.capacity formula) source context
        [.resetScratch] pushed (emitInitialRuntime formula) := by
    simpa [initial, marker, pushed, emitHeaderRuntime,
      emitInitialRuntime] using
      resetScratch_safe (context := context) pushed
        (by
          simpa [pushed, marker] using
            formulaStackMarker_lt_capacity formula)
  have all :=
    resetSafe.append
      (markerSafe.append (pushSafe.append finalSafe))
  simpa [initializeFormulaStackProgram,
    PNP.Concrete.CNFToNANDEmitterPlan.pushFormulaMarkerProgram,
    List.append_assoc] using all

private def initializeFormulaEnvelope (formula : CNFFormula) : Nat :=
  countBlockEnvelope formula (versionMarkedSource formula)
    (emitHeaderRuntime formula) initializeFormulaStackProgram

private theorem initialize_formula_block_path
    (formula : CNFFormula) (initialTape : WorkTape)
    (represents :
      TapeRepresents initializeFormulaRef.startState
        (CNFToNANDWorkspace.capacity formula)
        (CNFToNANDWorkspace.compilerGateCount formula)
        (CNFToNANDWorkspace.workspaceRegisters formula) []
        (versionMarkedSource formula) (headerTokens formula)
        initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node initializeFormulaRef)
        (.node countRestoreVersionRef)
        steps initialTape finalTape ∧
      TapeRepresents countRestoreVersionRef.startState
        (CNFToNANDWorkspace.capacity formula)
        (emitInitialRuntime formula).scratch
        (emitInitialRuntime formula).registers
        (emitInitialRuntime formula).checks
        (versionMarkedSource formula)
        (emitInitialRuntime formula).targetTokens finalTape ∧
      steps ≤ initializeFormulaEnvelope formula := by
  have safe :=
    initializeFormula_safe
      (context := versionMarkedSourceContext formula) formula
  have input :
      TapeRepresents
        (blockEntry blockDescriptors[18].code
          blockDescriptors[18].primitives).startState
        (CNFToNANDWorkspace.capacity formula)
        (emitHeaderRuntime formula).scratch
        (emitHeaderRuntime formula).registers
        (emitHeaderRuntime formula).checks
        (versionMarkedSource formula)
        (emitHeaderRuntime formula).targetTokens initialTape := by
    simpa [blockDescriptors, initializeFormulaRef,
      emitHeaderRuntime] using represents
  rcases indexedBlock_path 18 (by decide)
      countRestoreVersionRef.startState safe
      (Nat.le_of_lt
        (CNFToNANDWorkspace.compilerGateCount_lt_capacity formula))
      initialTape input with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape,
      by simpa [blockDescriptors, initializeFormulaRef] using path,
      finalRepresents,
      by
        simpa [initializeFormulaEnvelope, countBlockEnvelope,
          blockDescriptors] using bound⟩

private def countRestoreVersionSteps : Nat := 2

private theorem count_restore_version_path
    (formula : CNFFormula) (runtime : Runtime)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents countRestoreVersionRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (versionMarkedSource formula) runtime.targetTokens initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node countRestoreVersionRef)
        (.node countPassRewindRef)
        countRestoreVersionSteps initialTape finalTape ∧
      ScanRepresents countPassRewindRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        [SourceParser.cell00] (canonicalSource formula).tail
        runtime.targetTokens finalTape := by
  let capacity := CNFToNANDWorkspace.capacity formula
  let workspace :=
    TargetEmitterRuntime.logicalLeftWorkspace capacity
      runtime.scratch runtime.registers runtime.checks
  let outsideLeft := workspace.tail
  let suffix :=
    TargetEmitter.sourceTargetBoundary ::
      SourceParser.packedTokenCells runtime.targetTokens
  let canonicalInitial :=
    focusTape workspace (versionMarkedSource formula ++ suffix)
  let canonicalFinal :=
    focusTape (SourceParser.cell00 :: workspace)
      ((canonicalSource formula).tail ++ suffix)
  have workspaceEq :
      workspace =
        TargetEmitter.sourceLeftBoundary :: outsideLeft := by
    rfl
  have run :
      workRunExact?
          (TargetEmitterCursorControl.restoreMachine
            WorkSymbol.zeroZero)
          1
          { state :=
              (TargetEmitterCursorControl.restoreMachine
                WorkSymbol.zeroZero).startState
            tape := canonicalInitial } =
        some
          { state :=
              (TargetEmitterCursorControl.restoreMachine
                WorkSymbol.zeroZero).acceptState
            tape := canonicalFinal } := by
    rw [cursorControl_configAtWord_eq,
      cursorControl_configAtWord_eq]
    simpa [canonicalInitial, canonicalFinal, workspaceEq,
      versionMarkedSource, suffix,
      TargetEmitterCursorControl.restoreMachine,
      TargetEmitterCursorControl.restoreState,
      TargetEmitterCursorControl.restoredState,
      TargetEmitterCursorControl.cursorMark,
      SourceParser.cell00,
      TargetEmitterCursorAppender.cursorMarker,
      List.append_assoc] using
      TargetEmitterCursorControl.restore_exact WorkSymbol.zeroZero
        [] ((canonicalSource formula).tail ++ suffix)
        outsideLeft (by simp)
  have terminal :
      AcceptPath graph (.node countPassRewindRef)
        (.node countPassRewindRef) 0
        canonicalFinal canonicalFinal := .terminal _ _
  have canonicalPath :
      AcceptPath graph (.node countRestoreVersionRef)
        (.node countPassRewindRef)
        countRestoreVersionSteps canonicalInitial canonicalFinal := by
    simpa [countRestoreVersionSteps, countRestoreVersionRef,
      countRestoreVersionNode] using
      localAccept_path Address.countRestoreVersion
        (TargetEmitterCursorControl.restoreMachine
          WorkSymbol.zeroZero)
        (.node countPassRewindRef) .reject
        (.node countPassRewindRef)
        1 0 canonicalInitial canonicalFinal canonicalFinal
        countRestoreVersionNode_member run terminal
  have initialEquivalent :
      WorkTape.BlankEquivalent initialTape canonicalInitial := by
    have tapeEquivalent := represents.tape
    have tapeEquivalent' :
        WorkTape.BlankEquivalent initialTape
          (TargetEmitter.configAtWord
            countRestoreVersionRef.startState workspace
            (versionMarkedSource formula ++ suffix)).tape := by
      simpa [TapeRepresents, TargetEmitterRuntime.Represents,
        TargetEmitterRuntime.logicalConfiguration,
        TargetEmitterRuntime.logicalWord,
        workspace, suffix, capacity,
        List.append_assoc] using tapeEquivalent
    rw [targetEmitter_configAtWord_tape_eq] at tapeEquivalent'
    simpa [canonicalInitial, workspace, suffix, capacity,
      List.append_assoc] using tapeEquivalent'
  rcases AcceptPath.transport canonicalPath initialEquivalent with
    ⟨finalTape, path, finalEquivalent⟩
  refine ⟨finalTape, path, ?_⟩
  unfold ScanRepresents
  refine ⟨rfl, ?_⟩
  rw [targetEmitter_configAtWord_tape_eq]
  simpa [canonicalFinal, workspace, suffix, capacity,
    TargetEmitterRuntime.logicalLeftWorkspace,
    List.append_assoc] using finalEquivalent

private theorem canonicalSource_eq_two_cons
    (formula : CNFFormula) :
    canonicalSource formula =
      SourceParser.cell00 :: SourceParser.cell00 ::
        List.drop 2 (canonicalSource formula) := by
  rw [canonicalSource_eq_carrier_layout]
  simp [carrierHeaderCells]

private theorem count_pass_rewind_path
    (formula : CNFFormula) (runtime : Runtime)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents countPassRewindRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        [SourceParser.cell00] (canonicalSource formula).tail
        runtime.targetTokens initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node countPassRewindRef)
        (.node (passHeaderRef .emit))
        (sourceRewindSteps [SourceParser.cell00])
        initialTape finalTape ∧
      TapeRepresents (passHeaderRef .emit).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (canonicalSource formula) runtime.targetTokens finalTape := by
  have tailEq :
      (canonicalSource formula).tail =
        SourceParser.cell00 ::
          List.drop 2 (canonicalSource formula) := by
    have exactTail :=
      congrArg List.tail (canonicalSource_eq_two_cons formula)
    simpa using exactTail
  have rewindInput :
      ScanRepresents countPassRewindRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        [SourceParser.cell00]
        (SourceParser.cell00 ::
          List.drop 2 (canonicalSource formula))
        runtime.targetTokens initialTape := by
    simpa [tailEq] using represents
  rcases
      source_rewind_path Address.countPassRewind
        (passHeaderRef .emit).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        [SourceParser.cell00] SourceParser.cell00
        (List.drop 2 (canonicalSource formula)) runtime.targetTokens
        (.node (passHeaderRef .emit))
        (by
          simpa [countPassRewindNode] using
            countPassRewindNode_member)
        (by
          intro symbol member
          simp only [List.mem_singleton] at member
          subst symbol
          exact TargetEmitter.PackedSymbol.zeroZero)
        TargetEmitter.PackedSymbol.zeroZero
        initialTape rewindInput with
    ⟨finalTape, path, finalRepresents⟩
  refine ⟨finalTape, ?_, ?_⟩
  · simpa [countPassRewindRef] using path
  · rw [canonicalSource_eq_two_cons formula]
    simpa using finalRepresents

private def countNonemptySuffixEnvelope
    (formula : CNFFormula) (scratch : Nat) : Nat :=
  programEndSteps +
    sourceRewindSteps (countRewindBefore formula) +
    countInstallVersionSteps +
    emitHeaderEnvelope formula scratch +
    initializeFormulaEnvelope formula +
    countRestoreVersionSteps +
    sourceRewindSteps [SourceParser.cell00]

private theorem count_nonempty_suffix_path
    (formula : CNFFormula) (scratch : Nat)
    (scratchBound :
      scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (programEndRef .count .nonempty).startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (countedRegisters formula formula.variableCount
          (CNFToNANDWorkspace.compilerGateCount formula)) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (CNFToNANDWorkspace.formulaTokens formula))
        carrierFooterCells [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (programEndRef .count .nonempty))
        (.node (passHeaderRef .emit))
        steps initialTape finalTape ∧
      TapeRepresents (passHeaderRef .emit).startState
        (CNFToNANDWorkspace.capacity formula)
        (emitInitialRuntime formula).scratch
        (emitInitialRuntime formula).registers
        (emitInitialRuntime formula).checks
        (canonicalSource formula)
        (emitInitialRuntime formula).targetTokens finalTape ∧
      steps ≤ countNonemptySuffixEnvelope formula scratch := by
  let runtime :=
    countRuntime formula formula.variableCount
      (CNFToNANDWorkspace.compilerGateCount formula) scratch
  rcases
      program_end_path .count .nonempty
        (CNFToNANDWorkspace.capacity formula) runtime
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (CNFToNANDWorkspace.formulaTokens formula))
        initialTape (by simpa [runtime, countRuntime] using represents) with
    ⟨programTape, programPath, rewindRepresents⟩
  have rewindInput :
      ScanRepresents (countRewindRef .nonempty).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (countRewindBefore formula)
        (SourceParser.cell01 :: countRewindAfter)
        runtime.targetTokens programTape := by
    simpa [passRewindRef, countRewindBefore, countRewindAfter,
      carrierFooterCells, SourceParser.sourceCells,
      List.append_assoc] using rewindRepresents
  rcases
      count_rewind_path formula .nonempty runtime
        programTape rewindInput with
    ⟨rewoundTape, rewindPath, installRepresents⟩
  rcases
      count_install_version_path formula .nonempty runtime
        rewoundTape installRepresents with
    ⟨markedTape, installPath, markedRepresents⟩
  have headerInput :
      TapeRepresents emittedHeaderRef.startState
        (CNFToNANDWorkspace.capacity formula) scratch
        (CNFToNANDWorkspace.workspaceRegisters formula) []
        (versionMarkedSource formula) [] markedTape := by
    simpa [runtime, countAfterInstallRef, countRuntime,
      countedRegisters_final] using markedRepresents
  rcases
      emit_header_block_path formula scratch scratchBound
        markedTape headerInput with
    ⟨headerSteps, headerTape, headerPath, headerRepresents,
      headerBound⟩
  rcases
      initialize_formula_block_path formula headerTape
        headerRepresents with
    ⟨initializeSteps, initializedTape, initializePath,
      initializedRepresents, initializeBound⟩
  rcases
      count_restore_version_path formula (emitInitialRuntime formula)
        initializedTape initializedRepresents with
    ⟨restoreTape, restorePath, passRewindRepresents⟩
  rcases
      count_pass_rewind_path formula (emitInitialRuntime formula)
        restoreTape passRewindRepresents with
    ⟨finalTape, finalRewindPath, finalRepresents⟩
  let totalSteps :=
    programEndSteps +
      sourceRewindSteps (countRewindBefore formula) +
      countInstallVersionSteps +
      headerSteps + initializeSteps +
      countRestoreVersionSteps +
      sourceRewindSteps [SourceParser.cell00]
  refine ⟨totalSteps, finalTape, ?_, finalRepresents, ?_⟩
  · dsimp [totalSteps]
    exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        (AcceptPath.trans graph _ _ _ _ _ _ _ _
          (AcceptPath.trans graph _ _ _ _ _ _ _ _
            (AcceptPath.trans graph _ _ _ _ _ _ _ _
              (AcceptPath.trans graph _ _ _ _ _ _ _ _
                (AcceptPath.trans graph _ _ _ _ _ _ _ _
                  programPath rewindPath)
                installPath)
              headerPath)
            initializePath)
          restorePath)
        finalRewindPath
  · dsimp [totalSteps, countNonemptySuffixEnvelope]
    omega

private def countEmptyNormalizationEnvelope
    (formula : CNFFormula) : Nat :=
  countBlockEnvelope formula (versionMarkedSource formula)
    (countRuntime formula formula.variableCount 0 0)
    countEmptyFormulaProgram

private def countEmptySuffixEnvelope
    (formula : CNFFormula) : Nat :=
  programEndSteps +
    sourceRewindSteps (countRewindBefore formula) +
    countInstallVersionSteps +
    countEmptyNormalizationEnvelope formula +
    emitHeaderEnvelope formula 0 +
    initializeFormulaEnvelope formula +
    countRestoreVersionSteps +
    sourceRewindSteps [SourceParser.cell00]

private theorem count_empty_suffix_path
    (formula : CNFFormula) (empty : formula.clauses = [])
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (programEndRef .count .empty).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount 0) []
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (CNFToNANDWorkspace.formulaTokens formula))
        carrierFooterCells [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (programEndRef .count .empty))
        (.node (passHeaderRef .emit))
        steps initialTape finalTape ∧
      TapeRepresents (passHeaderRef .emit).startState
        (CNFToNANDWorkspace.capacity formula)
        (emitInitialRuntime formula).scratch
        (emitInitialRuntime formula).registers
        (emitInitialRuntime formula).checks
        (canonicalSource formula)
        (emitInitialRuntime formula).targetTokens finalTape ∧
      steps ≤ countEmptySuffixEnvelope formula := by
  let runtime :=
    countRuntime formula formula.variableCount 0 0
  rcases
      program_end_path .count .empty
        (CNFToNANDWorkspace.capacity formula) runtime
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (CNFToNANDWorkspace.formulaTokens formula))
        initialTape (by simpa [runtime, countRuntime] using represents) with
    ⟨programTape, programPath, rewindRepresents⟩
  have rewindInput :
      ScanRepresents (countRewindRef .empty).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (countRewindBefore formula)
        (SourceParser.cell01 :: countRewindAfter)
        runtime.targetTokens programTape := by
    simpa [passRewindRef, countRewindBefore, countRewindAfter,
      carrierFooterCells, SourceParser.sourceCells,
      List.append_assoc] using rewindRepresents
  rcases
      count_rewind_path formula .empty runtime
        programTape rewindInput with
    ⟨rewoundTape, rewindPath, installRepresents⟩
  rcases
      count_install_version_path formula .empty runtime
        rewoundTape installRepresents with
    ⟨markedTape, installPath, markedRepresents⟩
  have normalizationInput :
      TapeRepresents countEmptyFormulaRef.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula formula.variableCount 0) []
        (versionMarkedSource formula) [] markedTape := by
    simpa [runtime, countAfterInstallRef, countRuntime] using
      markedRepresents
  rcases
      count_empty_formula_block_path
        (context := versionMarkedSourceContext formula)
        formula empty markedTape normalizationInput with
    ⟨normalizationSteps, normalizedTape, normalizationPath,
      normalizationRepresents, normalizationBound⟩
  have compilerCount :
      CNFToNANDWorkspace.compilerGateCount formula = 1 := by
    rw [compilerGateCount_eq_count_charge]
    simp [empty, clausesGateCharge]
  have headerInput :
      TapeRepresents emittedHeaderRef.startState
        (CNFToNANDWorkspace.capacity formula) 0
        (CNFToNANDWorkspace.workspaceRegisters formula) []
        (versionMarkedSource formula) [] normalizedTape := by
    rw [← countedRegisters_final formula, compilerCount]
    exact normalizationRepresents
  rcases
      emit_header_block_path formula 0
        (Nat.zero_lt_of_lt
          (variableCount_lt_capacity formula))
        normalizedTape headerInput with
    ⟨headerSteps, headerTape, headerPath, headerRepresents,
      headerBound⟩
  rcases
      initialize_formula_block_path formula headerTape
        headerRepresents with
    ⟨initializeSteps, initializedTape, initializePath,
      initializedRepresents, initializeBound⟩
  rcases
      count_restore_version_path formula (emitInitialRuntime formula)
        initializedTape initializedRepresents with
    ⟨restoreTape, restorePath, passRewindRepresents⟩
  rcases
      count_pass_rewind_path formula (emitInitialRuntime formula)
        restoreTape passRewindRepresents with
    ⟨finalTape, finalRewindPath, finalRepresents⟩
  let totalSteps :=
    programEndSteps +
      sourceRewindSteps (countRewindBefore formula) +
      countInstallVersionSteps +
      normalizationSteps + headerSteps + initializeSteps +
      countRestoreVersionSteps +
      sourceRewindSteps [SourceParser.cell00]
  refine ⟨totalSteps, finalTape, ?_, finalRepresents, ?_⟩
  · dsimp [totalSteps]
    exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        (AcceptPath.trans graph _ _ _ _ _ _ _ _
          (AcceptPath.trans graph _ _ _ _ _ _ _ _
            (AcceptPath.trans graph _ _ _ _ _ _ _ _
              (AcceptPath.trans graph _ _ _ _ _ _ _ _
                (AcceptPath.trans graph _ _ _ _ _ _ _ _
                  (AcceptPath.trans graph _ _ _ _ _ _ _ _
                    programPath rewindPath)
                  installPath)
                normalizationPath)
              headerPath)
            initializePath)
          restorePath)
        finalRewindPath
  · dsimp [totalSteps, countEmptySuffixEnvelope,
      countEmptyNormalizationEnvelope]
    omega

/-! ## Closed polynomial charge for the physical count pass -/

private abbrev countSize (formula : CNFFormula) : Nat :=
  shiftedSize (encodeCNF formula).length

private abbrev countPhase (formula : CNFFormula) : Nat :=
  phaseUnit (encodeCNF formula).length

private theorem coefficient_shifted_le_dataMajorant
    (bitLength coefficient : Nat)
    (coefficientBound : coefficient ≤ 1000 * 1000000) :
    coefficient * shiftedSize bitLength ≤ dataMajorant bitLength := by
  have positive := one_le_shiftedSize bitLength
  have lifted :
      coefficient * shiftedSize bitLength ≤
        coefficient *
          (shiftedSize bitLength * shiftedSize bitLength) := by
    have scaled :=
      Nat.mul_le_mul_left coefficient
        (show shiftedSize bitLength ≤
            shiftedSize bitLength * shiftedSize bitLength by
          simpa only [Nat.mul_one] using
            Nat.mul_le_mul_left (shiftedSize bitLength) positive)
    exact scaled
  calc
    coefficient * shiftedSize bitLength ≤
        coefficient *
          (shiftedSize bitLength * shiftedSize bitLength) :=
      lifted
    _ ≤ (1000 * 1000000) *
          (shiftedSize bitLength * shiftedSize bitLength) :=
      Nat.mul_le_mul_right
        (shiftedSize bitLength * shiftedSize bitLength)
        coefficientBound
    _ = dataMajorant bitLength := by
      unfold dataMajorant squareUnit
      ac_rfl

private theorem formulaTokens_length_le_dataMajorant
    (formula : CNFFormula) :
    (CNFToNANDWorkspace.formulaTokens formula).length ≤
      dataMajorant (encodeCNF formula).length := by
  exact Nat.le_trans
    (formulaTokens_le_shiftedSize formula)
    (by
      simpa only [Nat.one_mul] using
        coefficient_shifted_le_dataMajorant
          (encodeCNF formula).length 1 (by decide))

private theorem capacity_le_dataMajorant
    (formula : CNFFormula) :
    CNFToNANDWorkspace.capacity formula ≤
      dataMajorant (encodeCNF formula).length := by
  exact Nat.le_trans
    (capacity_le_1024_shiftedSize formula)
    (coefficient_shifted_le_dataMajorant
      (encodeCNF formula).length 1024 (by decide))

private theorem canonicalSource_length_le_dataMajorant
    (formula : CNFFormula) :
    (canonicalSource formula).length ≤
      dataMajorant (encodeCNF formula).length := by
  exact Nat.le_trans
    (by
      simpa [canonicalSource] using
        carrierCells_le_sixteen_shiftedSize formula)
    (coefficient_shifted_le_dataMajorant
      (encodeCNF formula).length 16 (by decide))

private theorem markedSource_length_eq_canonicalSource
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken) (rest : List CNFToken)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ token :: rest) :
    (markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        processed token rest).length =
      (canonicalSource formula).length := by
  rw [canonicalSource_eq_carrier_layout]
  simp [markedSource, tokenBeforeCells, tokenAfterCells,
    carrierHeaderCells_length, carrierGateCells_length,
    carrierFooterCells, carrierGateCellsFor, tokens]
  omega

private theorem markedSource_length_le_dataMajorant
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken) (rest : List CNFToken)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ token :: rest) :
    (markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        processed token rest).length ≤
      dataMajorant (encodeCNF formula).length := by
  rw [markedSource_length_eq_canonicalSource
    formula processed token rest tokens]
  exact canonicalSource_length_le_dataMajorant formula

private theorem markedSource_length_le_dataMajorant_of_bounds
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken) (rest : List CNFToken)
    (processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length)
    (restBound :
      rest.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    (markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        processed token rest).length ≤
      dataMajorant (encodeCNF formula).length := by
  have tokenLength :=
    formulaTokens_le_shiftedSize formula
  have positive :
      1 ≤ shiftedSize (encodeCNF formula).length :=
    one_le_shiftedSize (encodeCNF formula).length
  have constantFalseCells :
      (SourceParser.sourceCells (.constant false)).length = 2 := by
    rfl
  have linear :
      (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token rest).length ≤
        40 * shiftedSize (encodeCNF formula).length := by
    simp [markedSource, tokenBeforeCells, tokenAfterCells,
      carrierHeaderCells_length, carrierGateCells_length,
      carrierFooterCells, constantFalseCells]
    omega
  exact Nat.le_trans linear
    (coefficient_shifted_le_dataMajorant
      (encodeCNF formula).length 40 (by decide))

private theorem versionMarkedSource_length_le_dataMajorant
    (formula : CNFFormula) :
    (versionMarkedSource formula).length ≤
      dataMajorant (encodeCNF formula).length := by
  have same :
      (versionMarkedSource formula).length =
        (canonicalSource formula).length := by
    rw [canonicalSource_eq_cons formula]
    simp [versionMarkedSource]
  rw [same]
  exact canonicalSource_length_le_dataMajorant formula

private theorem encodeNatTokens_length_local (value : Nat) :
    (encodeNatTokens value).length = value + 1 := by
  induction value with
  | zero =>
      rfl
  | succ value inductionHypothesis =>
      simp [encodeNatTokens, inductionHypothesis]

private theorem headerTokens_length_le_dataMajorant
    (formula : CNFFormula) :
    (headerTokens formula).length ≤
      dataMajorant (encodeCNF formula).length := by
  have width :
      formula.variableCount ≤
        (CNFToNANDWorkspace.formulaTokens formula).length := by
    rw [CNFToNANDWorkspace.formulaTokens,
      encodeFormulaTokens, CookLevin.encodeCNFTokens_length]
    omega
  have widthSize :
      formula.variableCount ≤ countSize formula :=
    Nat.le_trans width (formulaTokens_le_shiftedSize formula)
  have gatesSize :=
    compilerGateCount_le_sixteen_shiftedSize formula
  have gatesSize' :
      CNFToNANDWorkspace.compilerGateCount formula ≤
        16 * countSize formula := by
    simpa using gatesSize
  have linear :
      (headerTokens formula).length ≤ 20 * countSize formula := by
    simp [headerTokens, encodeNatTokens_length_local]
    have positive : 1 ≤ countSize formula := by
      exact one_le_shiftedSize (encodeCNF formula).length
    omega
  exact Nat.le_trans linear
    (coefficient_shifted_le_dataMajorant
      (encodeCNF formula).length 20 (by decide))

private theorem marked_count_block_le_phase
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken) (rest : List CNFToken)
    (width gateCount scratch : Nat)
    (descriptor : BlockDescriptor)
    (member : descriptor ∈ blockDescriptors)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ token :: rest) :
    countBlockEnvelope formula
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token rest)
        (countRuntime formula width gateCount scratch)
        descriptor.primitives ≤
      countPhase formula := by
  apply descriptorProgramEnvelope_le_phaseUnit
      (descriptor := descriptor) (member := member)
  · exact capacity_le_dataMajorant formula
  · exact
      markedSource_length_le_dataMajorant
        formula processed token rest tokens
  · simp [countRuntime]
  · simp [countRuntime, TargetEmitterRuntimeProgramBound.checkCells,
      TargetEmitterCheckStack.recordsWord]

private theorem marked_count_block_le_phase_of_bounds
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken) (rest : List CNFToken)
    (width gateCount scratch : Nat)
    (descriptor : BlockDescriptor)
    (member : descriptor ∈ blockDescriptors)
    (processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length)
    (restBound :
      rest.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    countBlockEnvelope formula
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token rest)
        (countRuntime formula width gateCount scratch)
        descriptor.primitives ≤
      countPhase formula := by
  apply descriptorProgramEnvelope_le_phaseUnit
      (descriptor := descriptor) (member := member)
  · exact capacity_le_dataMajorant formula
  · exact markedSource_length_le_dataMajorant_of_bounds
      formula processed token rest processedBound restBound
  · simp [countRuntime]
  · simp [countRuntime, TargetEmitterRuntimeProgramBound.checkCells,
      TargetEmitterCheckStack.recordsWord]

private theorem version_count_block_le_phase
    (formula : CNFFormula) (width gateCount scratch : Nat)
    (descriptor : BlockDescriptor)
    (member : descriptor ∈ blockDescriptors) :
    countBlockEnvelope formula (versionMarkedSource formula)
        (countRuntime formula width gateCount scratch)
        descriptor.primitives ≤
      countPhase formula := by
  apply descriptorProgramEnvelope_le_phaseUnit
      (descriptor := descriptor) (member := member)
  · exact capacity_le_dataMajorant formula
  · exact versionMarkedSource_length_le_dataMajorant formula
  · simp [countRuntime]
  · simp [countRuntime, TargetEmitterRuntimeProgramBound.checkCells,
      TargetEmitterCheckStack.recordsWord]

private theorem version_emitHeader_block_le_phase
    (formula : CNFFormula) (descriptor : BlockDescriptor)
    (member : descriptor ∈ blockDescriptors) :
    countBlockEnvelope formula (versionMarkedSource formula)
        (emitHeaderRuntime formula) descriptor.primitives ≤
      countPhase formula := by
  apply descriptorProgramEnvelope_le_phaseUnit
      (descriptor := descriptor) (member := member)
  · exact capacity_le_dataMajorant formula
  · exact versionMarkedSource_length_le_dataMajorant formula
  · exact headerTokens_length_le_dataMajorant formula
  · simp [emitHeaderRuntime,
      TargetEmitterRuntimeProgramBound.checkCells,
      TargetEmitterCheckStack.recordsWord]

private theorem directTokenStepEnvelope_le_phase
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken)
    (processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    directTokenStepEnvelope formula processed token ≤
      countPhase formula := by
  have tokenLength :=
    formulaTokens_le_shiftedSize formula
  have shiftedMaster :=
    shiftedSize_le_masterMajorant (encodeCNF formula).length
  have masterPositive :
      1 ≤ masterMajorant (encodeCNF formula).length :=
    Nat.le_trans
      (one_le_shiftedSize (encodeCNF formula).length)
      shiftedMaster
  have masterSquare :
      masterMajorant (encodeCNF formula).length ≤
        masterMajorant (encodeCNF formula).length *
          masterMajorant (encodeCNF formula).length := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left
        (masterMajorant (encodeCNF formula).length)
        masterPositive
  have linear :
      directTokenStepEnvelope formula processed token ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant (encodeCNF formula).length) + 1 := by
    simp [directTokenStepEnvelope, tokenReadInstallSteps,
      tokenRestoreAdvanceSteps, tokenReaderSteps,
      tokenBeforeCells, carrierHeaderCells_length,
      carrierGateCells_length,
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope]
    omega
  exact Nat.le_trans linear
    (primitiveEnvelope_add_one_le_phaseUnit
      (encodeCNF formula).length)

private theorem literalCompareSteps_le_phase
    (formula : CNFFormula) (scratch : Nat)
    (scratchBound :
      scratch ≤ CNFToNANDWorkspace.capacity formula) :
    literalCompareSteps
        (CNFToNANDWorkspace.capacity formula) scratch ≤
      countPhase formula := by
  let master := masterMajorant (encodeCNF formula).length
  let capacity := CNFToNANDWorkspace.capacity formula
  have capacityBound : capacity ≤ master := by
    simpa [capacity, master] using capacity_le_masterMajorant formula
  have scratchMaster : scratch ≤ master :=
    Nat.le_trans scratchBound capacityBound
  have masterPositive : 1 ≤ master := by
    dsimp [master]
    exact Nat.le_trans
      (one_le_shiftedSize (encodeCNF formula).length)
      (shiftedSize_le_masterMajorant (encodeCNF formula).length)
  have masterSquare : master ≤ master * master := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left master masterPositive
  have product :
      scratch * (14 * capacity + 31) ≤
        master * (14 * master + 31) :=
    Nat.mul_le_mul scratchMaster
      (Nat.add_le_add_right
        (Nat.mul_le_mul_left 14 capacityBound) 31)
  have masterProduct :
      master * (14 * master + 31) =
        14 * (master * master) + 31 * master := by
    rw [Nat.mul_add]
    ac_rfl
  have productSimple :
      scratch * (14 * capacity + 31) ≤
        45 * (master * master) := by
    calc
      scratch * (14 * capacity + 31) ≤
          master * (14 * master + 31) := product
      _ = 14 * (master * master) + 31 * master :=
        masterProduct
      _ ≤ 45 * (master * master) := by omega
  have polynomial :=
    TargetEmitterScratchCompareSlot.workSteps_le_polynomialWorkBound
      TargetEmitterLedger.Slot.inputCount capacity scratch
  unfold literalCompareSteps
  calc
    TargetEmitterScratchCompareSlot.workSteps
          TargetEmitterLedger.Slot.inputCount capacity scratch + 1 ≤
        TargetEmitterScratchCompareSlot.polynomialWorkBound
          capacity scratch + 1 :=
      Nat.add_le_add_right polynomial 1
    _ ≤ TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
          master + 1 := by
      unfold TargetEmitterScratchCompareSlot.polynomialWorkBound
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
      omega
    _ ≤ countPhase formula := by
      dsimp [master]
      exact primitiveEnvelope_add_one_le_phaseUnit
        (encodeCNF formula).length

private theorem countClauseSeparatorStepEnvelope_le_two_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (next : CNFToken) (tail : List CNFToken)
    (gateCount scratch : Nat)
    (processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length)
    (restBound :
      (next :: tail).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    countClauseSeparatorStepEnvelope formula processed next tail
        gateCount scratch ≤
      2 * countPhase formula := by
  have direct :=
    directTokenStepEnvelope_le_phase
      formula processed .sep processedBound
  have block :=
    marked_count_block_le_phase_of_bounds
      formula processed .sep (next :: tail)
      formula.variableCount gateCount scratch
      blockDescriptors[2] (by simp [blockDescriptors])
      processedBound restBound
  change
    countBlockEnvelope formula
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .sep (next :: tail))
        (countRuntime formula formula.variableCount gateCount scratch)
        countClauseProgram ≤
      countPhase formula at block
  unfold directTokenStepEnvelope at direct
  unfold countClauseSeparatorStepEnvelope
  omega

private theorem countSignStepEnvelope_le_three_phases
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length)
    (restBound :
      (next :: tail).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    countSignStepEnvelope formula positive processed next tail
        gateCount scratch ≤
      3 * countPhase formula := by
  have direct :=
    directTokenStepEnvelope_le_phase formula processed
      (signToken positive) processedBound
  have compare :=
    literalCompareSteps_le_phase formula 0 (by omega)
  cases positive with
  | false =>
      have block :=
        marked_count_block_le_phase_of_bounds
          formula processed .f (next :: tail)
          formula.variableCount gateCount scratch
          blockDescriptors[4] (by simp [blockDescriptors])
          processedBound restBound
      change
        countBlockEnvelope formula
            (markedSource
              (CNFToNANDWorkspace.formulaTokens formula)
              processed .f (next :: tail))
            (countRuntime formula formula.variableCount
              gateCount scratch)
            Blocks.countNegativeSignProgram ≤
          countPhase formula at block
      unfold directTokenStepEnvelope at direct
      simp [signToken] at direct
      unfold countSignStepEnvelope
      simp [signToken, countSignPrimitives]
      omega
  | true =>
      have block :=
        marked_count_block_le_phase_of_bounds
          formula processed .t (next :: tail)
          formula.variableCount gateCount scratch
          blockDescriptors[5] (by simp [blockDescriptors])
          processedBound restBound
      change
        countBlockEnvelope formula
            (markedSource
              (CNFToNANDWorkspace.formulaTokens formula)
              processed .t (next :: tail))
            (countRuntime formula formula.variableCount
              gateCount scratch)
            Blocks.countPositiveSignProgram ≤
          countPhase formula at block
      unfold directTokenStepEnvelope at direct
      simp [signToken] at direct
      unfold countSignStepEnvelope
      simp [signToken, countSignPrimitives]
      omega

private theorem countInRangeTStepEnvelope_le_three_phases
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length)
    (restBound :
      (next :: tail).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length)
    (scratchBound :
      scratch ≤ CNFToNANDWorkspace.capacity formula) :
    countInRangeTStepEnvelope formula positive processed next tail
        gateCount scratch ≤
      3 * countPhase formula := by
  have direct :=
    directTokenStepEnvelope_le_phase
      formula processed .t processedBound
  have compare :=
    literalCompareSteps_le_phase formula scratch scratchBound
  have block :=
    marked_count_block_le_phase_of_bounds
      formula processed .t (next :: tail)
      formula.variableCount gateCount scratch
      blockDescriptors[7] (by simp [blockDescriptors])
      processedBound restBound
  have block' :
      countBlockEnvelope formula
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed .t (next :: tail))
          (countRuntime formula formula.variableCount
            gateCount scratch)
          advanceLiteralIndexProgram ≤
        countPhase formula := by
    simpa [blockDescriptors] using block
  unfold directTokenStepEnvelope at direct
  unfold countInRangeTStepEnvelope
  omega

private theorem countComparedDirectStepEnvelope_le_two_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken) (scratch : Nat)
    (processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length)
    (scratchBound :
      scratch ≤ CNFToNANDWorkspace.capacity formula) :
    countComparedDirectStepEnvelope formula processed token scratch ≤
      2 * countPhase formula := by
  have direct :=
    directTokenStepEnvelope_le_phase
      formula processed token processedBound
  have compare :=
    literalCompareSteps_le_phase formula scratch scratchBound
  unfold directTokenStepEnvelope at direct
  unfold countComparedDirectStepEnvelope
  omega

private theorem countNegativeTerminatorStepEnvelope_le_three_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (next : CNFToken) (tail : List CNFToken)
    (gateCount scratch : Nat)
    (processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length)
    (restBound :
      (next :: tail).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length)
    (scratchBound :
      scratch ≤ CNFToNANDWorkspace.capacity formula) :
    countNegativeTerminatorStepEnvelope formula processed next tail
        gateCount scratch ≤
      3 * countPhase formula := by
  have direct :=
    directTokenStepEnvelope_le_phase
      formula processed .f processedBound
  have compare :=
    literalCompareSteps_le_phase formula scratch scratchBound
  have block :=
    marked_count_block_le_phase_of_bounds
      formula processed .f (next :: tail)
      formula.variableCount gateCount scratch
      blockDescriptors[6] (by simp [blockDescriptors])
      processedBound restBound
  have block' :
      countBlockEnvelope formula
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed .f (next :: tail))
          (countRuntime formula formula.variableCount
            gateCount scratch)
          countValidNegativeProgram ≤
        countPhase formula := by
    simpa [blockDescriptors] using block
  unfold directTokenStepEnvelope at direct
  unfold countNegativeTerminatorStepEnvelope
  omega

private theorem countValidTerminatorEnvelope_le_three_phases
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length)
    (restBound :
      (next :: tail).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length)
    (scratchBound :
      scratch ≤ CNFToNANDWorkspace.capacity formula) :
    countValidTerminatorEnvelope formula positive processed next tail
        gateCount scratch ≤
      3 * countPhase formula := by
  cases positive with
  | false =>
      simpa [countValidTerminatorEnvelope] using
        countNegativeTerminatorStepEnvelope_le_three_phases
          formula processed next tail gateCount scratch
          processedBound restBound scratchBound
  | true =>
      have bounded :=
        countComparedDirectStepEnvelope_le_two_phases
          formula processed .f scratch processedBound scratchBound
      simpa [countValidTerminatorEnvelope] using
        Nat.le_trans bounded
          (Nat.mul_le_mul_right (countPhase formula) (by decide : 2 ≤ 3))

private theorem encodeUnaryTokens_length_local (count : Nat) :
    (encodeUnaryTokens count).length = count + 1 := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      simp [encodeUnaryTokens, inductionHypothesis]

private theorem encodeUnaryTokens_tail_length_local (count : Nat) :
    (encodeUnaryTokens count).tail.length = count := by
  cases count with
  | zero =>
      rfl
  | succ count =>
      simp [encodeUnaryTokens, encodeUnaryTokens_length_local]

private theorem countOverflowUnaryEnvelope_le_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (remaining : Nat)
    (lengthBound :
      processed.length + remaining + 1 ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    countOverflowUnaryEnvelope formula processed remaining ≤
      (remaining + 1) * countPhase formula := by
  induction remaining generalizing processed with
  | zero =>
      have processedBound :
          processed.length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        omega
      have direct :=
        directTokenStepEnvelope_le_phase
          formula processed .f processedBound
      simpa [countOverflowUnaryEnvelope] using direct
  | succ remaining inductionHypothesis =>
      have processedBound :
          processed.length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        omega
      have direct :=
        directTokenStepEnvelope_le_phase
          formula processed .t processedBound
      have recursiveLength :
          (processed ++ [CNFToken.t]).length + remaining + 1 ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        simp
        omega
      have recursive :=
        inductionHypothesis (processed ++ [CNFToken.t]) recursiveLength
      have combined := Nat.add_le_add direct recursive
      rw [countOverflowUnaryEnvelope]
      calc
        directTokenStepEnvelope formula processed .t +
              countOverflowUnaryEnvelope formula
                (processed ++ [.t]) remaining ≤
            countPhase formula +
              (remaining + 1) * countPhase formula :=
          combined
        _ = (Nat.succ remaining + 1) * countPhase formula := by
          simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul]
          omega

private theorem countInRangeUnaryEnvelope_le_phases
    (formula : CNFFormula) (positive : Bool)
    (next : CNFToken) (tail : List CNFToken)
    (gateCount : Nat) (processed : List CNFToken)
    (done remaining : Nat)
    (doneBound : done ≤ formula.variableCount)
    (lengthBound :
      processed.length + (remaining + 1) +
          (next :: tail).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    countInRangeUnaryEnvelope formula positive next tail
        gateCount processed done remaining ≤
      3 * (remaining + 1) * countPhase formula := by
  induction remaining generalizing processed done with
  | zero =>
      have processedBound :
          processed.length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        omega
      have restBound :
          (next :: tail).length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        omega
      have scratchBound :
          done ≤ CNFToNANDWorkspace.capacity formula :=
        Nat.le_trans doneBound
          (Nat.le_of_lt (variableCount_lt_capacity formula))
      by_cases less : done < formula.variableCount
      · have bounded :=
          countValidTerminatorEnvelope_le_three_phases
            formula positive processed next tail gateCount done
            processedBound restBound scratchBound
        simpa [countInRangeUnaryEnvelope, less] using bounded
      · have bounded :=
          countComparedDirectStepEnvelope_le_two_phases
            formula processed .f done processedBound scratchBound
        have coefficient : 2 ≤ 3 := by decide
        have scaled :=
          Nat.mul_le_mul_right (countPhase formula) coefficient
        exact
          Nat.le_trans
            (by
              simpa [countInRangeUnaryEnvelope, less] using bounded)
            (by simpa using scaled)
  | succ remaining inductionHypothesis =>
      simp only [List.length_cons] at lengthBound
      let unary := encodeUnaryTokens remaining
      let unaryHead := unary.headD next
      let unaryTail := unary.tail ++ next :: tail
      have processedBound :
          processed.length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        omega
      have restBound :
          (unaryHead :: unaryTail).length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        dsimp [unaryHead, unaryTail, unary]
        simp [encodeUnaryTokens_length_local]
        omega
      have scratchBound :
          done ≤ CNFToNANDWorkspace.capacity formula :=
        Nat.le_trans doneBound
          (Nat.le_of_lt (variableCount_lt_capacity formula))
      by_cases less : done < formula.variableCount
      · have first :=
          countInRangeTStepEnvelope_le_three_phases
            formula positive processed unaryHead unaryTail
            gateCount done processedBound restBound scratchBound
        have recursiveLength :
            (processed ++ [CNFToken.t]).length + (remaining + 1) +
                (next :: tail).length ≤
              (CNFToNANDWorkspace.formulaTokens formula).length := by
          simp
          omega
        have recursive :=
          inductionHypothesis (processed ++ [CNFToken.t]) (done + 1)
            (by omega) recursiveLength
        have combined := Nat.add_le_add first recursive
        have coefficient :
            3 + 3 * (remaining + 1) ≤
              3 * (Nat.succ remaining + 1) := by
          omega
        have scaled :=
          Nat.mul_le_mul_right (countPhase formula) coefficient
        exact
          Nat.le_trans
            (by
              simpa [countInRangeUnaryEnvelope, less,
                unary, unaryHead, unaryTail] using combined)
            (by simpa [Nat.add_mul] using scaled)
      · have first :=
          countComparedDirectStepEnvelope_le_two_phases
            formula processed .t done processedBound scratchBound
        have overflowLength :
            (processed ++ [CNFToken.t]).length + remaining + 1 ≤
              (CNFToNANDWorkspace.formulaTokens formula).length := by
          simp
          omega
        have overflow :=
          countOverflowUnaryEnvelope_le_phases formula
            (processed ++ [CNFToken.t]) remaining overflowLength
        have combined := Nat.add_le_add first overflow
        have coefficient :
            2 + (remaining + 1) ≤
              3 * (Nat.succ remaining + 1) := by
          omega
        have scaled :=
          Nat.mul_le_mul_right (countPhase formula) coefficient
        exact
          Nat.le_trans
            (by
              simpa [countInRangeUnaryEnvelope, less,
                unary, unaryHead, unaryTail] using combined)
            (by simpa [Nat.add_mul] using scaled)

private theorem encodeLiteralTokens_length_local
    (literal : CNFLiteral) :
    (encodeLiteralTokens literal).length =
      literal.variableIndex + 2 := by
  simp [encodeLiteralTokens, encodeUnaryTokens_length_local]

private theorem countLiteralEnvelope_le_phases
    (formula : CNFFormula) (literal : CNFLiteral)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (lengthBound :
      processed.length + (encodeLiteralTokens literal).length +
          (next :: tail).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    countLiteralEnvelope formula literal processed next tail
        gateCount scratch ≤
      3 * (encodeLiteralTokens literal).length *
        countPhase formula := by
  simp only [List.length_cons] at lengthBound
  let positive := literal.positive
  let unary := encodeUnaryTokens literal.variableIndex
  let unaryHead := unary.headD next
  let unaryTail := unary.tail ++ next :: tail
  have processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length := by
    omega
  have signRestBound :
      (unaryHead :: unaryTail).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length := by
    dsimp [unaryHead, unaryTail, unary]
    simp [encodeUnaryTokens_length_local]
    rw [encodeLiteralTokens_length_local] at lengthBound
    omega
  have sign :=
    countSignStepEnvelope_le_three_phases formula positive
      processed unaryHead unaryTail gateCount scratch
      processedBound signRestBound
  by_cases widthZero : formula.variableCount = 0
  · have overflowLength :
        (processed ++ [signToken positive]).length +
            literal.variableIndex + 1 ≤
          (CNFToNANDWorkspace.formulaTokens formula).length := by
      simp
      rw [encodeLiteralTokens_length_local] at lengthBound
      omega
    have overflow :=
      countOverflowUnaryEnvelope_le_phases formula
        (processed ++ [signToken positive])
        literal.variableIndex overflowLength
    have combined := Nat.add_le_add sign overflow
    have coefficient :
        3 + (literal.variableIndex + 1) ≤
          3 * (encodeLiteralTokens literal).length := by
      rw [encodeLiteralTokens_length_local]
      omega
    have scaled :=
      Nat.mul_le_mul_right (countPhase formula) coefficient
    exact
      Nat.le_trans
        (by
          simpa [countLiteralEnvelope, positive, unary,
            unaryHead, unaryTail, widthZero] using combined)
        (by simpa [Nat.add_mul] using scaled)
  · have inRangeLength :
        (processed ++ [signToken positive]).length +
              (literal.variableIndex + 1) +
              (next :: tail).length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
      simp
      rw [encodeLiteralTokens_length_local] at lengthBound
      omega
    have inRange :=
      countInRangeUnaryEnvelope_le_phases formula positive
        next tail (gateCount + 3)
        (processed ++ [signToken positive]) 0
        literal.variableIndex (by omega) inRangeLength
    have combined := Nat.add_le_add sign inRange
    have coefficient :
        3 + 3 * (literal.variableIndex + 1) =
          3 * (encodeLiteralTokens literal).length := by
      rw [encodeLiteralTokens_length_local]
      omega
    calc
      countLiteralEnvelope formula literal processed next tail
            gateCount scratch ≤
          3 * countPhase formula +
            3 * (literal.variableIndex + 1) *
              countPhase formula := by
        simpa [countLiteralEnvelope, positive, unary,
          unaryHead, unaryTail, widthZero] using combined
      _ = (3 + 3 * (literal.variableIndex + 1)) *
            countPhase formula := by
        rw [Nat.add_mul]
      _ = 3 * (encodeLiteralTokens literal).length *
            countPhase formula := by
        rw [coefficient]

private theorem countLiteralListEnvelope_le_phases
    (formula : CNFFormula) (next : CNFToken)
    (tail : List CNFToken) (literals : List CNFLiteral)
    (processed : List CNFToken) (gateCount scratch : Nat)
    (lengthBound :
      processed.length + (encodeLiteralListTokens literals).length +
          (next :: tail).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    countLiteralListEnvelope formula next tail literals
        processed gateCount scratch ≤
      3 * (encodeLiteralListTokens literals).length *
        countPhase formula := by
  induction literals generalizing processed gateCount scratch with
  | nil =>
      simp [countLiteralListEnvelope, encodeLiteralListTokens]
  | cons literal literals inductionHypothesis =>
      let remaining :=
        encodeLiteralListTokens literals ++ next :: tail
      let remainingHead := remaining.headD next
      let remainingTail := remaining.tail
      have remainingNonempty : remaining ≠ [] := by
        simp [remaining]
      have remainingLength :
          (remainingHead :: remainingTail).length =
            remaining.length := by
        cases remainingEq : remaining with
        | nil =>
            exact False.elim (remainingNonempty remainingEq)
        | cons head rest =>
            simp [remainingHead, remainingTail, remainingEq]
      have firstLength :
          processed.length +
                (encodeLiteralTokens literal).length +
                (remainingHead :: remainingTail).length ≤
              (CNFToNANDWorkspace.formulaTokens formula).length := by
        rw [remainingLength]
        dsimp [remaining]
        simp only [List.length_append, List.length_cons]
        simp only [encodeLiteralListTokens,
          List.length_append, List.length_cons] at lengthBound
        omega
      have first :=
        countLiteralEnvelope_le_phases formula literal processed
          remainingHead remainingTail gateCount scratch firstLength
      have recursiveLength :
          (processed ++ encodeLiteralTokens literal).length +
                (encodeLiteralListTokens literals).length +
                (next :: tail).length ≤
              (CNFToNANDWorkspace.formulaTokens formula).length := by
        simp only [List.length_append]
        simp only [encodeLiteralListTokens,
          List.length_append] at lengthBound
        omega
      have recursive :=
        inductionHypothesis
          (processed ++ encodeLiteralTokens literal)
          (gateCount +
            literalGateCharge formula.variableCount literal)
          (Nat.min literal.variableIndex formula.variableCount)
          recursiveLength
      have combined := Nat.add_le_add first recursive
      have coefficient :
          3 * (encodeLiteralTokens literal).length +
              3 * (encodeLiteralListTokens literals).length =
            3 *
              (encodeLiteralListTokens
                (literal :: literals)).length := by
        simp [encodeLiteralListTokens]
        omega
      calc
        countLiteralListEnvelope formula next tail
              (literal :: literals) processed gateCount scratch ≤
            3 * (encodeLiteralTokens literal).length *
                countPhase formula +
              3 * (encodeLiteralListTokens literals).length *
                countPhase formula := by
          simpa [countLiteralListEnvelope, remaining,
            remainingHead, remainingTail] using combined
        _ =
            (3 * (encodeLiteralTokens literal).length +
              3 * (encodeLiteralListTokens literals).length) *
                countPhase formula := by
          rw [Nat.add_mul]
        _ =
            3 * (encodeLiteralListTokens
              (literal :: literals)).length *
                countPhase formula := by
          rw [coefficient]

private theorem countClauseEnvelope_le_phases
    (formula : CNFFormula) (clause : List CNFLiteral)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (gateCount scratch : Nat)
    (lengthBound :
      processed.length + (encodeClauseTokens clause).length +
          (next :: tail).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    countClauseEnvelope formula clause processed next tail
        gateCount scratch ≤
      3 * (encodeClauseTokens clause).length *
        countPhase formula := by
  let body := encodeLiteralListTokens clause ++ [.finish]
  let bodyHead := body.headD .finish
  let bodyTail := body.tail ++ next :: tail
  have processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length := by
    omega
  have bodyNonempty : body ≠ [] := by
    simp [body]
  have bodyRestLength :
      (bodyHead :: bodyTail).length =
        body.length + (next :: tail).length := by
    cases bodyEq : body with
    | nil =>
        exact False.elim (bodyNonempty bodyEq)
    | cons head rest =>
        simp [bodyHead, bodyTail, bodyEq]
        omega
  have separatorRestBound :
      (bodyHead :: bodyTail).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length := by
    rw [bodyRestLength]
    dsimp [body]
    simp only [List.length_append, List.length_cons,
      List.length_nil]
    simp only [encodeClauseTokens, List.length_cons,
      List.length_append, List.length_nil] at lengthBound
    omega
  have separator :=
    countClauseSeparatorStepEnvelope_le_two_phases formula
      processed bodyHead bodyTail gateCount scratch
      processedBound separatorRestBound
  have literalLength :
      (processed ++ [CNFToken.sep]).length +
            (encodeLiteralListTokens clause).length +
            (CNFToken.finish :: next :: tail).length ≤
          (CNFToNANDWorkspace.formulaTokens formula).length := by
    simp only [List.length_append, List.length_singleton,
      List.length_cons, List.length_nil]
    simp only [encodeClauseTokens, List.length_cons,
      List.length_append, List.length_nil] at lengthBound
    omega
  have literals :=
    countLiteralListEnvelope_le_phases formula .finish
      (next :: tail) clause (processed ++ [CNFToken.sep])
      (gateCount + 2) scratch literalLength
  have finishProcessedBound :
      (processed ++ .sep ::
          encodeLiteralListTokens clause).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length := by
    simp only [List.length_append, List.length_cons]
    simp only [encodeClauseTokens, List.length_cons,
      List.length_append, List.length_nil] at lengthBound
    omega
  have finish :=
    directTokenStepEnvelope_le_phase formula
      (processed ++ .sep :: encodeLiteralListTokens clause)
      .finish finishProcessedBound
  have combined :=
    Nat.add_le_add (Nat.add_le_add separator literals) finish
  have coefficient :
      2 + 3 * (encodeLiteralListTokens clause).length + 1 ≤
        3 * (encodeClauseTokens clause).length := by
    simp [encodeClauseTokens]
    omega
  have scaled :=
    Nat.mul_le_mul_right (countPhase formula) coefficient
  exact
    Nat.le_trans
      (by
        simpa [countClauseEnvelope, body, bodyHead, bodyTail,
          Nat.add_assoc] using combined)
      (by
        simpa [Nat.add_mul, Nat.add_assoc] using scaled)

private theorem countClauseListEnvelope_le_phases
    (formula : CNFFormula)
    (clauses : List (List CNFLiteral))
    (processed : List CNFToken) (gateCount scratch : Nat)
    (lengthBound :
      processed.length + (encodeClauseListTokens clauses).length + 1 ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    countClauseListEnvelope formula clauses processed
        gateCount scratch ≤
      3 * (encodeClauseListTokens clauses).length *
        countPhase formula := by
  induction clauses generalizing processed gateCount scratch with
  | nil =>
      simp [countClauseListEnvelope, encodeClauseListTokens]
  | cons clause clauses inductionHypothesis =>
      let remaining := encodeClauseListTokens clauses ++ [.finish]
      let next := remaining.headD .finish
      let tail := remaining.tail
      have remainingNonempty : remaining ≠ [] := by
        simp [remaining]
      have remainingLength :
          (next :: tail).length = remaining.length := by
        cases remainingEq : remaining with
        | nil =>
            exact False.elim (remainingNonempty remainingEq)
        | cons head rest =>
            simp [next, tail, remainingEq]
      have clauseLength :
          processed.length + (encodeClauseTokens clause).length +
                (next :: tail).length ≤
              (CNFToNANDWorkspace.formulaTokens formula).length := by
        rw [remainingLength]
        dsimp [remaining]
        simp only [List.length_append, List.length_singleton]
        simp only [encodeClauseListTokens,
          List.length_append] at lengthBound
        omega
      have first :=
        countClauseEnvelope_le_phases formula clause processed
          next tail gateCount scratch clauseLength
      have recursiveLength :
          (processed ++ encodeClauseTokens clause).length +
                (encodeClauseListTokens clauses).length + 1 ≤
              (CNFToNANDWorkspace.formulaTokens formula).length := by
        simp only [List.length_append]
        simp only [encodeClauseListTokens,
          List.length_append] at lengthBound
        omega
      have recursive :=
        inductionHypothesis
          (processed ++ encodeClauseTokens clause)
          (gateCount +
            clauseGateCharge formula.variableCount clause)
          (literalListFinalScratch formula.variableCount
            clause scratch)
          recursiveLength
      have combined := Nat.add_le_add first recursive
      have coefficient :
          3 * (encodeClauseTokens clause).length +
              3 * (encodeClauseListTokens clauses).length =
            3 *
              (encodeClauseListTokens
                (clause :: clauses)).length := by
        simp [encodeClauseListTokens]
        omega
      calc
        countClauseListEnvelope formula (clause :: clauses)
              processed gateCount scratch ≤
            3 * (encodeClauseTokens clause).length *
                countPhase formula +
              3 * (encodeClauseListTokens clauses).length *
                countPhase formula := by
          simpa [countClauseListEnvelope, remaining,
            next, tail] using combined
        _ =
            (3 * (encodeClauseTokens clause).length +
              3 * (encodeClauseListTokens clauses).length) *
                countPhase formula := by
          rw [Nat.add_mul]
        _ =
            3 * (encodeClauseListTokens
              (clause :: clauses)).length *
                countPhase formula := by
          rw [coefficient]

private theorem variableCount_le_formulaTokens_length_local
    (formula : CNFFormula) :
    formula.variableCount ≤
      (CNFToNANDWorkspace.formulaTokens formula).length := by
  rw [CNFToNANDWorkspace.formulaTokens,
    encodeFormulaTokens, encodeCNFTokens]
  simp only [List.length_append, List.length_singleton,
    encodeUnaryTokens_length_local]
  omega

private theorem countWidthEnvelope_le_phases
    (formula : CNFFormula) (done remaining : Nat)
    (sum : done + remaining = formula.variableCount) :
    countWidthEnvelope formula done remaining ≤
      (2 * remaining + 1) * countPhase formula := by
  induction remaining generalizing done with
  | zero =>
      have processedBound :
          (List.replicate done CNFToken.t).length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        simp
        exact Nat.le_trans (by omega)
          (variableCount_le_formulaTokens_length_local formula)
      have direct :=
        directTokenStepEnvelope_le_phase formula
          (List.replicate done CNFToken.t) .f processedBound
      rw [countWidthEnvelope]
      unfold directTokenStepEnvelope at direct
      simpa only [Nat.mul_zero, Nat.zero_add, Nat.one_mul] using direct
  | succ remaining inductionHypothesis =>
      let processed := List.replicate done CNFToken.t
      let rest :=
        encodeUnaryTokens remaining ++
          encodeClauseListTokens formula.clauses ++ [.finish]
      have processedBound :
          processed.length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        dsimp [processed]
        simp
        exact Nat.le_trans (by omega)
          (variableCount_le_formulaTokens_length_local formula)
      have restBound :
          rest.length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        dsimp [rest]
        simp only [List.length_append, List.length_singleton,
          encodeUnaryTokens_length_local]
        rw [CNFToNANDWorkspace.formulaTokens,
          encodeFormulaTokens, encodeCNFTokens]
        simp only [List.length_append, List.length_singleton,
          encodeUnaryTokens_length_local]
        omega
      have direct :=
        directTokenStepEnvelope_le_phase
          formula processed .t processedBound
      have block :=
        marked_count_block_le_phase_of_bounds formula
          processed .t rest done 0 0
          blockDescriptors[1] (by simp [blockDescriptors])
          processedBound restBound
      change
        countBlockEnvelope formula
            (markedSource
              (CNFToNANDWorkspace.formulaTokens formula)
              processed .t rest)
            (countRuntime formula done 0 0)
            countWidthUnitProgram ≤
          countPhase formula at block
      have recursive :=
        inductionHypothesis (done + 1) (by omega)
      have coefficient :
          2 + (2 * remaining + 1) =
            2 * Nat.succ remaining + 1 := by
        omega
      rw [countWidthEnvelope]
      unfold directTokenStepEnvelope at direct
      calc
        tokenReadInstallSteps
                (CNFToNANDWorkspace.formulaTokens formula)
                processed .t +
              countBlockEnvelope formula
                (markedSource
                  (CNFToNANDWorkspace.formulaTokens formula)
                  processed .t rest)
                (countRuntime formula done 0 0)
                countWidthUnitProgram +
              tokenRestoreAdvanceSteps
                (CNFToNANDWorkspace.formulaTokens formula)
                processed .t +
              countWidthEnvelope formula (done + 1) remaining ≤
            2 * countPhase formula +
              (2 * remaining + 1) * countPhase formula := by
          omega
        _ =
            (2 + (2 * remaining + 1)) *
              countPhase formula := by
          exact
            (Nat.add_mul 2 (2 * remaining + 1)
              (countPhase formula)).symm
        _ =
            (2 * Nat.succ remaining + 1) *
              countPhase formula := by
          rw [coefficient]

private theorem countHeaderScanSteps_le_phase
    (formula : CNFFormula) :
    countHeaderScanSteps formula ≤ countPhase formula := by
  have tokenLength :=
    formulaTokens_le_shiftedSize formula
  have shiftedMaster :=
    shiftedSize_le_masterMajorant (encodeCNF formula).length
  have masterPositive :
      1 ≤ masterMajorant (encodeCNF formula).length :=
    Nat.le_trans
      (one_le_shiftedSize (encodeCNF formula).length)
      shiftedMaster
  have masterSquare :
      masterMajorant (encodeCNF formula).length ≤
        masterMajorant (encodeCNF formula).length *
          masterMajorant (encodeCNF formula).length := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left
        (masterMajorant (encodeCNF formula).length)
        masterPositive
  have linear :
      countHeaderScanSteps formula ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant (encodeCNF formula).length) + 1 := by
    unfold countHeaderScanSteps
      TargetEmitterNavigator.headerWorkSteps
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    omega
  exact Nat.le_trans linear
    (primitiveEnvelope_add_one_le_phaseUnit
      (encodeCNF formula).length)

private theorem countFinishStepEnvelope_le_phase
    (formula : CNFFormula) (processed : List CNFToken)
    (processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    countFinishStepEnvelope formula processed ≤ countPhase formula := by
  simpa [countFinishStepEnvelope, directTokenStepEnvelope] using
    directTokenStepEnvelope_le_phase
      formula processed .finish processedBound

private theorem countEmptyTraversalEnvelope_le_phases
    (formula : CNFFormula) :
    countEmptyTraversalEnvelope formula ≤
      4 *
          ((CNFToNANDWorkspace.formulaTokens formula).length + 1) *
        countPhase formula := by
  have header := countHeaderScanSteps_le_phase formula
  have width :=
    countWidthEnvelope_le_phases formula 0 formula.variableCount
      (by omega)
  have finishProcessed :
      (encodeUnaryTokens formula.variableCount).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length := by
    rw [CNFToNANDWorkspace.formulaTokens,
      encodeFormulaTokens, encodeCNFTokens]
    simp
  have finish :=
    countFinishStepEnvelope_le_phase formula
      (encodeUnaryTokens formula.variableCount) finishProcessed
  have combined :=
    Nat.add_le_add (Nat.add_le_add header width) finish
  have widthTokens :=
    variableCount_le_formulaTokens_length_local formula
  have coefficient :
      1 + (2 * formula.variableCount + 1) + 1 ≤
        4 *
          ((CNFToNANDWorkspace.formulaTokens formula).length + 1) := by
    omega
  have scaled :=
    Nat.mul_le_mul_right (countPhase formula) coefficient
  have first :
      countEmptyTraversalEnvelope formula ≤
        countPhase formula +
            (2 * formula.variableCount + 1) * countPhase formula +
          countPhase formula := by
    simpa [countEmptyTraversalEnvelope, Nat.add_assoc] using combined
  have regroup :
      countPhase formula +
            (2 * formula.variableCount + 1) * countPhase formula +
          countPhase formula =
        (1 + (2 * formula.variableCount + 1) + 1) *
          countPhase formula := by
    symm
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  exact Nat.le_trans first
    (Nat.le_trans (Nat.le_of_eq regroup) scaled)

private theorem countNonemptyTraversalEnvelope_le_phases
    (formula : CNFFormula) :
    countNonemptyTraversalEnvelope formula ≤
      4 *
          ((CNFToNANDWorkspace.formulaTokens formula).length + 1) *
        countPhase formula := by
  have header := countHeaderScanSteps_le_phase formula
  have width :=
    countWidthEnvelope_le_phases formula 0 formula.variableCount
      (by omega)
  have clauseLength :
      (encodeUnaryTokens formula.variableCount).length +
            (encodeClauseListTokens formula.clauses).length + 1 ≤
          (CNFToNANDWorkspace.formulaTokens formula).length := by
    rw [CNFToNANDWorkspace.formulaTokens,
      encodeFormulaTokens, encodeCNFTokens]
    simp only [List.length_append, List.length_singleton]
    exact Nat.le_refl _
  have clauses :=
    countClauseListEnvelope_le_phases formula formula.clauses
      (encodeUnaryTokens formula.variableCount) 0 0 clauseLength
  have finishProcessed :
      (encodeUnaryTokens formula.variableCount ++
          encodeClauseListTokens formula.clauses).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length := by
    rw [CNFToNANDWorkspace.formulaTokens,
      encodeFormulaTokens, encodeCNFTokens]
    simp
  have finish :=
    countFinishStepEnvelope_le_phase formula
      (encodeUnaryTokens formula.variableCount ++
        encodeClauseListTokens formula.clauses)
      finishProcessed
  have combined :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add header width) clauses)
      finish
  have tokenLength :
      (CNFToNANDWorkspace.formulaTokens formula).length =
        formula.variableCount + 1 +
          (encodeClauseListTokens formula.clauses).length + 1 := by
    rw [CNFToNANDWorkspace.formulaTokens,
      encodeFormulaTokens, encodeCNFTokens]
    simp [encodeUnaryTokens_length_local]
    omega
  have coefficient :
      1 + (2 * formula.variableCount + 1) +
            3 * (encodeClauseListTokens formula.clauses).length + 1 ≤
        4 *
          ((CNFToNANDWorkspace.formulaTokens formula).length + 1) := by
    rw [tokenLength]
    omega
  have scaled :=
    Nat.mul_le_mul_right (countPhase formula) coefficient
  have first :
      countNonemptyTraversalEnvelope formula ≤
        countPhase formula +
            (2 * formula.variableCount + 1) * countPhase formula +
          3 * (encodeClauseListTokens formula.clauses).length *
              countPhase formula +
          countPhase formula := by
    simpa [countNonemptyTraversalEnvelope, Nat.add_assoc] using
      combined
  have regroup :
      countPhase formula +
            (2 * formula.variableCount + 1) * countPhase formula +
          3 * (encodeClauseListTokens formula.clauses).length *
              countPhase formula +
          countPhase formula =
        (1 + (2 * formula.variableCount + 1) +
            3 * (encodeClauseListTokens formula.clauses).length + 1) *
          countPhase formula := by
    symm
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul]
  exact Nat.le_trans first
    (Nat.le_trans (Nat.le_of_eq regroup) scaled)

private theorem smallSteps_le_phase
    (formula : CNFFormula) (steps : Nat)
    (small : steps ≤ 100) :
    steps ≤ countPhase formula := by
  have primitiveLow :
      100 ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant (encodeCNF formula).length) + 1 := by
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    omega
  exact Nat.le_trans small
    (Nat.le_trans primitiveLow
      (primitiveEnvelope_add_one_le_phaseUnit
        (encodeCNF formula).length))

private theorem countRewindSteps_le_phase
    (formula : CNFFormula) :
    sourceRewindSteps (countRewindBefore formula) ≤
      countPhase formula := by
  have prefixBound :
      (countRewindBefore formula).length ≤
        (canonicalSource formula).length := by
    have split :=
      congrArg List.length
        (canonicalSource_eq_countRewindSplit formula)
    simp only [List.length_append, List.length_cons] at split
    omega
  have canonicalMaster :
      (canonicalSource formula).length ≤
        masterMajorant (encodeCNF formula).length := by
    simpa [canonicalSource] using
      carrierCells_le_masterMajorant formula
  have prefixMasterBound :=
    Nat.le_trans prefixBound canonicalMaster
  have masterPositive :
      1 ≤ masterMajorant (encodeCNF formula).length :=
    Nat.le_trans
      (one_le_shiftedSize (encodeCNF formula).length)
      (shiftedSize_le_masterMajorant (encodeCNF formula).length)
  have masterSquare :
      masterMajorant (encodeCNF formula).length ≤
        masterMajorant (encodeCNF formula).length *
          masterMajorant (encodeCNF formula).length := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left
        (masterMajorant (encodeCNF formula).length)
        masterPositive
  have localBound :
      sourceRewindSteps (countRewindBefore formula) ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant (encodeCNF formula).length) + 1 := by
    unfold sourceRewindSteps
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    omega
  exact Nat.le_trans localBound
    (primitiveEnvelope_add_one_le_phaseUnit
      (encodeCNF formula).length)

private theorem countEmptyNormalizationEnvelope_le_phase
    (formula : CNFFormula) :
    countEmptyNormalizationEnvelope formula ≤ countPhase formula := by
  have block :=
    version_count_block_le_phase formula formula.variableCount 0 0
      blockDescriptors[3] (by simp [blockDescriptors])
  change
    countBlockEnvelope formula (versionMarkedSource formula)
        (countRuntime formula formula.variableCount 0 0)
        countEmptyFormulaProgram ≤
      countPhase formula at block
  unfold countEmptyNormalizationEnvelope
  exact block

private theorem emitHeaderEnvelope_le_phase
    (formula : CNFFormula) (scratch : Nat) :
    emitHeaderEnvelope formula scratch ≤ countPhase formula := by
  have block :=
    version_count_block_le_phase formula formula.variableCount
      (CNFToNANDWorkspace.compilerGateCount formula) scratch
      blockDescriptors[17] (by simp [blockDescriptors])
  change
    countBlockEnvelope formula (versionMarkedSource formula)
        (countRuntime formula formula.variableCount
          (CNFToNANDWorkspace.compilerGateCount formula) scratch)
        emitCircuitHeaderProgram ≤
      countPhase formula at block
  unfold emitHeaderEnvelope
  exact block

private theorem initializeFormulaEnvelope_le_phase
    (formula : CNFFormula) :
    initializeFormulaEnvelope formula ≤ countPhase formula := by
  have block :=
    version_emitHeader_block_le_phase formula
      blockDescriptors[18] (by simp [blockDescriptors])
  change
    countBlockEnvelope formula (versionMarkedSource formula)
        (emitHeaderRuntime formula) initializeFormulaStackProgram ≤
      countPhase formula at block
  unfold initializeFormulaEnvelope
  exact block

private theorem countNonemptySuffixEnvelope_le_phases
    (formula : CNFFormula) (scratch : Nat) :
    countNonemptySuffixEnvelope formula scratch ≤
      7 * countPhase formula := by
  have program :
      programEndSteps ≤ countPhase formula :=
    smallSteps_le_phase formula programEndSteps (by
      unfold programEndSteps
      decide)
  have rewind := countRewindSteps_le_phase formula
  have install :
      countInstallVersionSteps ≤ countPhase formula :=
    smallSteps_le_phase formula countInstallVersionSteps (by
      unfold countInstallVersionSteps
      decide)
  have header := emitHeaderEnvelope_le_phase formula scratch
  have initialized := initializeFormulaEnvelope_le_phase formula
  have restore :
      countRestoreVersionSteps ≤ countPhase formula :=
    smallSteps_le_phase formula countRestoreVersionSteps (by
      unfold countRestoreVersionSteps
      decide)
  have finalRewind :
      sourceRewindSteps [SourceParser.cell00] ≤ countPhase formula :=
    smallSteps_le_phase formula
      (sourceRewindSteps [SourceParser.cell00]) (by
        unfold sourceRewindSteps
        decide)
  unfold countNonemptySuffixEnvelope
  omega

private theorem countEmptySuffixEnvelope_le_phases
    (formula : CNFFormula) :
    countEmptySuffixEnvelope formula ≤
      8 * countPhase formula := by
  have program :
      programEndSteps ≤ countPhase formula :=
    smallSteps_le_phase formula programEndSteps (by
      unfold programEndSteps
      decide)
  have rewind := countRewindSteps_le_phase formula
  have install :
      countInstallVersionSteps ≤ countPhase formula :=
    smallSteps_le_phase formula countInstallVersionSteps (by
      unfold countInstallVersionSteps
      decide)
  have normalization :=
    countEmptyNormalizationEnvelope_le_phase formula
  have header := emitHeaderEnvelope_le_phase formula 0
  have initialized := initializeFormulaEnvelope_le_phase formula
  have restore :
      countRestoreVersionSteps ≤ countPhase formula :=
    smallSteps_le_phase formula countRestoreVersionSteps (by
      unfold countRestoreVersionSteps
      decide)
  have finalRewind :
      sourceRewindSteps [SourceParser.cell00] ≤ countPhase formula :=
    smallSteps_le_phase formula
      (sourceRewindSteps [SourceParser.cell00]) (by
        unfold sourceRewindSteps
        decide)
  unfold countEmptySuffixEnvelope
  omega

private def countPassExactEnvelope (formula : CNFFormula) : Nat :=
  match formula.clauses with
  | [] =>
      countEmptyTraversalEnvelope formula +
        countEmptySuffixEnvelope formula
  | _ :: _ =>
      countNonemptyTraversalEnvelope formula +
        countNonemptySuffixEnvelope formula
          (clauseListFinalScratch formula.variableCount
            formula.clauses 0)

private theorem countPassExactEnvelope_le_phases
    (formula : CNFFormula) :
    countPassExactEnvelope formula ≤
      (4 *
          ((CNFToNANDWorkspace.formulaTokens formula).length + 1) +
        8) * countPhase formula := by
  cases clausesEq : formula.clauses with
  | nil =>
      have traversal :=
        countEmptyTraversalEnvelope_le_phases formula
      have suffix :=
        countEmptySuffixEnvelope_le_phases formula
      have combined := Nat.add_le_add traversal suffix
      rw [countPassExactEnvelope, clausesEq]
      calc
        countEmptyTraversalEnvelope formula +
              countEmptySuffixEnvelope formula ≤
            4 *
                ((CNFToNANDWorkspace.formulaTokens formula).length + 1) *
                countPhase formula +
              8 * countPhase formula :=
          combined
        _ =
            (4 *
                ((CNFToNANDWorkspace.formulaTokens formula).length + 1) +
              8) * countPhase formula := by
          exact
            (Nat.add_mul
              (4 *
                ((CNFToNANDWorkspace.formulaTokens formula).length + 1))
              8 (countPhase formula)).symm
  | cons clause clauses =>
      have traversal :=
        countNonemptyTraversalEnvelope_le_phases formula
      have suffix :=
        countNonemptySuffixEnvelope_le_phases formula
          (clauseListFinalScratch formula.variableCount
            formula.clauses 0)
      have suffixEight :
          countNonemptySuffixEnvelope formula
              (clauseListFinalScratch formula.variableCount
                formula.clauses 0) ≤
            8 * countPhase formula :=
        Nat.le_trans suffix
          (Nat.mul_le_mul_right (countPhase formula)
            (by decide : 7 ≤ 8))
      have combined := Nat.add_le_add traversal suffixEight
      rw [countPassExactEnvelope, clausesEq]
      calc
        countNonemptyTraversalEnvelope formula +
              countNonemptySuffixEnvelope formula
                (clauseListFinalScratch formula.variableCount
                  formula.clauses 0) ≤
            4 *
                ((CNFToNANDWorkspace.formulaTokens formula).length + 1) *
                countPhase formula +
              8 * countPhase formula :=
          combined
        _ =
            (4 *
                ((CNFToNANDWorkspace.formulaTokens formula).length + 1) +
              8) * countPhase formula := by
          exact
            (Nat.add_mul
              (4 *
                ((CNFToNANDWorkspace.formulaTokens formula).length + 1))
              8 (countPhase formula)).symm

/-- Formula-indexed deterministic envelope for the complete physical first
pass.  The bound covers the literal graph trace from the count header through
the fixed version/header/stack suffix and into the emitting pass. -/
def countPassEnvelope (formula : CNFFormula) : Nat :=
  countPassExactEnvelope formula

/-- The complete physical count-pass trace consumes its reserved quadratic
share of the controller's common polynomial work allocation. -/
theorem countPassEnvelope_le_allocated (formula : CNFFormula) :
    countPassEnvelope formula ≤
      1024 *
        shiftedSize (encodeCNF formula).length *
        shiftedSize (encodeCNF formula).length *
        phaseUnit (encodeCNF formula).length := by
  have linear := countPassExactEnvelope_le_phases formula
  have tokenSize := formulaTokens_le_shiftedSize formula
  have sizePositive :=
    one_le_shiftedSize (encodeCNF formula).length
  have sizeSquare :
      shiftedSize (encodeCNF formula).length ≤
        shiftedSize (encodeCNF formula).length *
          shiftedSize (encodeCNF formula).length := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left
        (shiftedSize (encodeCNF formula).length)
        sizePositive
  have coefficient :
      4 *
            ((CNFToNANDWorkspace.formulaTokens formula).length + 1) +
          8 ≤
        1024 *
          shiftedSize (encodeCNF formula).length *
          shiftedSize (encodeCNF formula).length := by
    let size := shiftedSize (encodeCNF formula).length
    have linearCoefficient :
        4 *
              ((CNFToNANDWorkspace.formulaTokens formula).length + 1) +
            8 ≤
          16 * size := by
      dsimp [size]
      omega
    have squareCoefficient :
        16 * size ≤ 16 * (size * size) :=
      Nat.mul_le_mul_left 16 (by simpa [size] using sizeSquare)
    have allocatedCoefficient :
        16 * (size * size) ≤ 1024 * (size * size) :=
      Nat.mul_le_mul_right (size * size) (by decide)
    calc
      4 *
              ((CNFToNANDWorkspace.formulaTokens formula).length + 1) +
            8 ≤
          16 * size :=
        linearCoefficient
      _ ≤ 16 * (size * size) := squareCoefficient
      _ ≤ 1024 * (size * size) := allocatedCoefficient
      _ =
          1024 *
            shiftedSize (encodeCNF formula).length *
            shiftedSize (encodeCNF formula).length := by
        dsimp [size]
        ac_rfl
  have scaled :=
    Nat.mul_le_mul_right
      (phaseUnit (encodeCNF formula).length) coefficient
  unfold countPassEnvelope
  exact Nat.le_trans linear scaled

/-- Constructive literal-graph execution of the complete count pass.  The
machine traverses the canonical retained formula, installs the exact counted
registers, emits the strict-v0 header, initializes the formula stack, restores
the retained source, and reaches the emitting-pass header. -/
theorem count_pass_path
    (formula : CNFFormula) (initialTape : WorkTape)
    (represents :
      TapeRepresents (passHeaderRef .count).startState
        (CNFToNANDWorkspace.capacity formula) 0
        (countedRegisters formula 0 0) []
        (canonicalSource formula) [] initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (passHeaderRef .count))
        (.node (passHeaderRef .emit))
        steps initialTape finalTape ∧
      TapeRepresents (passHeaderRef .emit).startState
        (CNFToNANDWorkspace.capacity formula)
        (emitInitialRuntime formula).scratch
        (emitInitialRuntime formula).registers
        (emitInitialRuntime formula).checks
        (canonicalSource formula)
        (emitInitialRuntime formula).targetTokens finalTape ∧
      steps ≤ countPassEnvelope formula := by
  cases clausesEq : formula.clauses with
  | nil =>
      rcases
          count_empty_traversal_path formula clausesEq
            initialTape represents with
        ⟨traversalSteps, traversalTape, traversalPath,
          traversalRepresents, traversalBound⟩
      rcases
          count_empty_suffix_path formula clausesEq
            traversalTape traversalRepresents with
        ⟨suffixSteps, finalTape, suffixPath, finalRepresents,
          suffixBound⟩
      refine
        ⟨traversalSteps + suffixSteps, finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            traversalPath suffixPath,
          finalRepresents, ?_⟩
      simpa [countPassEnvelope, countPassExactEnvelope,
        clausesEq] using Nat.add_le_add traversalBound suffixBound
  | cons clause clauses =>
      have nonempty : formula.clauses ≠ [] := by
        simp [clausesEq]
      rcases
          count_nonempty_traversal_path formula nonempty
            initialTape represents with
        ⟨traversalSteps, traversalTape, traversalPath,
          traversalRepresents, traversalBound⟩
      have scratchBound :
          clauseListFinalScratch formula.variableCount
              formula.clauses 0 <
            CNFToNANDWorkspace.capacity formula := by
        exact
          clauseListFinalScratch_lt_capacity formula formula.clauses 0
            (Nat.zero_lt_of_lt (variableCount_lt_capacity formula))
      rcases
          count_nonempty_suffix_path formula
            (clauseListFinalScratch formula.variableCount
              formula.clauses 0)
            scratchBound traversalTape traversalRepresents with
        ⟨suffixSteps, finalTape, suffixPath, finalRepresents,
          suffixBound⟩
      refine
        ⟨traversalSteps + suffixSteps, finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            traversalPath suffixPath,
          finalRepresents, ?_⟩
      simpa [countPassEnvelope, countPassExactEnvelope,
        clausesEq] using Nat.add_le_add traversalBound suffixBound

end PNP.Concrete.CNFToNANDControllerCountTrace

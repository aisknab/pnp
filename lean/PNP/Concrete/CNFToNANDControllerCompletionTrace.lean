/-
Copyright (c) 2026 PNP Labs.

Certificate-free completion of the fixed canonical CNF-to-NAND controller.

This file starts at the public canonical-prefix handoff.  Formula structure
is used only to index the proof and its exact cost; the executable graph
continues to branch solely on symbols read from the retained carrier.
-/

import PNP.Concrete.CNFToNANDControllerCountTrace
import PNP.Concrete.CNFToNANDControllerPolynomialBound
import PNP.Concrete.LockedNANDTargetEmitterControllerCompletionTrace
import PNP.Concrete.LockedNANDTargetEmitterScratchCompareSlotExact
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramBound

namespace PNP.Concrete.CNFToNANDControllerCompletionTrace

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
open PNP.Concrete.CNFToNANDEmitterPlan

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

abbrev ScanRepresents :=
  PNP.Concrete.CNFToNANDControllerCountTrace.ScanRepresents

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

private theorem tapeRepresents_at_state
    {oldState newState capacity scratch : Nat}
    {registers : TargetEmitter.UnaryRegisters}
    {checks : List Nat} {source : List WorkSymbol}
    {target : List Token} {tape : WorkTape}
    (represents :
      TapeRepresents oldState capacity scratch registers checks
        source target tape) :
    TapeRepresents newState capacity scratch registers checks
      source target tape := by
  unfold TapeRepresents at represents ⊢
  exact represents_at_state represents

private theorem controlNode_member
    (code : Nat) (program : WorkMachine)
    (onAccept onReject : Endpoint)
    (member :
      controlNode code program onAccept onReject ∈ controlNodes) :
    controlNode code program onAccept onReject ∈ graph.nodes := by
  exact controlNode_member_nodes _ member

private theorem indexedControlNode_member
    (node : Node) (index : Nat)
    (bound : index < controlNodes.length)
    (selected : controlNodes[index] = node) :
    node ∈ graph.nodes := by
  apply controlNode_member_nodes node
  rw [← selected]
  exact List.getElem_mem bound

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
        some { state := program.acceptState, tape := middleTape })
    (tail :
      AcceptPath graph onAccept finalEndpoint tailSteps
        middleTape finalTape) :
    AcceptPath graph (.node (controlRef code program)) finalEndpoint
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
        some { state := program.rejectState, tape := middleTape })
    (tail :
      AcceptPath graph onReject finalEndpoint tailSteps
        middleTape finalTape) :
    AcceptPath graph (.node (controlRef code program)) finalEndpoint
      (localSteps + 1 + tailSteps) initialTape finalTape := by
  have path :=
    AcceptPath.stepReject
      (controlNode code program onAccept onReject)
      finalEndpoint localSteps tailSteps initialTape middleTape
      finalTape member
      (by simpa [LocalRejectRun, controlNode] using run) tail
  simpa [controlNode, controlRef, Node.reference] using path

private theorem passHeaderNode_member (pass : Pass) :
    passHeaderNode pass ∈ graph.nodes := by
  let index := 19 + pass.code
  have bound : index < controlNodes.length := by
    cases pass <;> decide
  refine indexedControlNode_member (passHeaderNode pass) index
    bound ?_
  cases pass <;> rfl

private theorem firstBitNode_member (pass : Pass)
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

private theorem secondBitNode_member (pass : Pass)
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

private theorem installNode_member (pass : Pass)
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

private theorem signCompareNode_member (pass : Pass)
    (positive : Bool) :
    signCompareNode pass positive ∈ graph.nodes := by
  let index :=
    133 + 6 * pass.code + 3 * (if positive then 1 else 0)
  have bound : index < controlNodes.length := by
    cases pass <;> cases positive <;> decide
  refine indexedControlNode_member
    (signCompareNode pass positive) index bound ?_
  cases pass <;> cases positive <;> rfl

private theorem literalUnitCompareNode_member (pass : Pass)
    (positive : Bool) :
    literalUnitCompareNode pass positive ∈ graph.nodes := by
  let index :=
    134 + 6 * pass.code + 3 * (if positive then 1 else 0)
  have bound : index < controlNodes.length := by
    cases pass <;> cases positive <;> decide
  refine indexedControlNode_member
    (literalUnitCompareNode pass positive) index bound ?_
  cases pass <;> cases positive <;> rfl

private theorem literalTerminatorCompareNode_member
    (pass : Pass) (positive : Bool) :
    literalTerminatorCompareNode pass positive ∈ graph.nodes := by
  let index :=
    135 + 6 * pass.code + 3 * (if positive then 1 else 0)
  have bound : index < controlNodes.length := by
    cases pass <;> cases positive <;> decide
  refine indexedControlNode_member
    (literalTerminatorCompareNode pass positive) index bound ?_
  cases pass <;> cases positive <;> rfl

private theorem restoreNode_member (pass : Pass)
    (state : GrammarState) (token : CNFToken) :
    restoreNode pass state token ∈ graph.nodes := by
  let index :=
    145 + 40 * pass.code + 4 * state.code + tokenCode token
  have bound : index < controlNodes.length := by
    cases pass <;> cases state <;> cases token <;> decide
  refine indexedControlNode_member
    (restoreNode pass state token) index bound ?_
  cases pass <;> cases state <;> cases token <;> rfl

private theorem gateAdvanceNode_member (pass : Pass)
    (state : GrammarState) :
    gateAdvanceNode pass state ∈ graph.nodes := by
  let index := 225 + 10 * pass.code + state.code
  have bound : index < controlNodes.length := by
    cases pass <;> cases state <;> decide
  refine indexedControlNode_member
    (gateAdvanceNode pass state) index bound ?_
  cases pass <;> cases state <;> rfl

private theorem programEndNode_member (pass : Pass)
    (kind : FinishKind) :
    programEndNode pass kind ∈ graph.nodes := by
  let index := 245 + 2 * pass.code + kind.code
  have bound : index < controlNodes.length := by
    cases pass <;> cases kind <;> decide
  refine indexedControlNode_member
    (programEndNode pass kind) index bound ?_
  cases pass <;> cases kind <;> rfl

private theorem emitRewindNode_member :
    emitRewindNode ∈ graph.nodes := by
  refine indexedControlNode_member emitRewindNode 255 (by decide) ?_
  rfl

private theorem emitInstallVersionNode_member :
    emitInstallVersionNode ∈ graph.nodes := by
  refine indexedControlNode_member emitInstallVersionNode 256
    (by decide) ?_
  rfl

private theorem clauseCompareFirstNode_member :
    clauseCompareFirstNode ∈ graph.nodes := by
  refine indexedControlNode_member clauseCompareFirstNode 257
    (by decide) ?_
  rfl

private theorem clauseCompareLoopNode_member :
    clauseCompareLoopNode ∈ graph.nodes := by
  refine indexedControlNode_member clauseCompareLoopNode 258
    (by decide) ?_
  rfl

private theorem formulaCompareMarkerFirstNode_member :
    formulaCompareMarkerFirstNode ∈ graph.nodes := by
  refine indexedControlNode_member formulaCompareMarkerFirstNode 259
    (by decide) ?_
  rfl

private theorem formulaCompareFalseFirstNode_member :
    formulaCompareFalseFirstNode ∈ graph.nodes := by
  refine indexedControlNode_member formulaCompareFalseFirstNode 260
    (by decide) ?_
  rfl

private theorem formulaCompareMarkerLoopNode_member :
    formulaCompareMarkerLoopNode ∈ graph.nodes := by
  refine indexedControlNode_member formulaCompareMarkerLoopNode 261
    (by decide) ?_
  rfl

private theorem formulaCompareFalseLoopNode_member :
    formulaCompareFalseLoopNode ∈ graph.nodes := by
  refine indexedControlNode_member formulaCompareFalseLoopNode 262
    (by decide) ?_
  rfl

private theorem finalizerNode_member :
    finalizerNode ∈ graph.nodes := by
  refine indexedControlNode_member finalizerNode 263 (by decide) ?_
  rfl

/-! ## Canonical emit runtime and retained-source views -/

abbrev headerTokens :=
  PNP.Concrete.CNFToNANDControllerCountTrace.headerTokens

abbrev emitInitialRuntime :=
  PNP.Concrete.CNFToNANDControllerCountTrace.emitInitialRuntime

private theorem emitInitialRuntime_fits (formula : CNFFormula) :
    LedgerFits (CNFToNANDWorkspace.capacity formula)
      (emitInitialRuntime formula).registers := by
  let shape := CNFToNANDWorkspace.workspaceShape formula
  exact
    { inputCount := shape.inputBound
      normalizedGateCount := shape.normalizedGateBound
      carrierWidth := shape.carrierWidthBound
      baseline := shape.baselineBound
      currentGate := shape.currentGateBound
      outputIndex := shape.outputIndexBound }

private abbrev tokenBeforeCells :=
  PNP.Concrete.CNFToNANDControllerCountTrace.tokenBeforeCells

private abbrev tokenAfterCells :=
  PNP.Concrete.CNFToNANDControllerCountTrace.tokenAfterCells

private abbrev scanBeforeCells :=
  PNP.Concrete.CNFToNANDControllerCountTrace.scanBeforeCells

private abbrev scanAfterCells :=
  PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells

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

private abbrev markedSource :=
  PNP.Concrete.CNFToNANDControllerCountTrace.markedSource

private abbrev markedSourceContext :=
  PNP.Concrete.CNFToNANDControllerCountTrace.markedSourceContext

private abbrev markedCursorLayout :=
  PNP.Concrete.CNFToNANDControllerCountTrace.markedCursorLayout

/-! ## Small capacity-safe program combinators -/

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

private theorem popCheck_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime) (prior : List Nat) (value : Nat)
    (fits : LedgerFits capacity runtime.registers)
    (scratchZero : runtime.scratch = 0)
    (checks : runtime.checks = prior ++ [value])
    (bound : value ≤ capacity) :
    ProgramSafe capacity source context [.popCheck] runtime
      { runtime with scratch := value, checks := prior } :=
  ProgramSafe.singleton
    (TargetEmitterRuntimeProgram.PrimitiveSafe.popCheck
      runtime prior value fits
      scratchZero checks bound)

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
      runtime counter slot
      slotEq fits bound)

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

private theorem repeatIncrementScratch_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (count : Nat) (runtime : Runtime)
    (bound : runtime.scratch + count ≤ capacity) :
    ProgramSafe capacity source context
      (repeatPrimitive count .incrementScratch) runtime
      { runtime with scratch := runtime.scratch + count } := by
  induction count generalizing runtime with
  | zero =>
      simpa [repeatPrimitive] using
        (TargetEmitterRuntimeProgram.ProgramSafe.nil runtime :
          ProgramSafe capacity source context [] runtime runtime)
  | succ count ih =>
      rw [show
        repeatPrimitive (Nat.succ count) .incrementScratch =
          .incrementScratch ::
            repeatPrimitive count .incrementScratch by
        simp [repeatPrimitive, List.replicate_succ]]
      let middle : Runtime :=
        { runtime with scratch := runtime.scratch + 1 }
      refine
        .cons .incrementScratch
          (repeatPrimitive count .incrementScratch)
          runtime middle
          { runtime with
            scratch := runtime.scratch + Nat.succ count }
          (TargetEmitterRuntimeProgram.PrimitiveSafe.incrementScratch
            runtime (by omega)) ?_
      have tail := ih middle (by simp [middle]; omega)
      simpa [middle, Nat.add_assoc, Nat.add_comm 1 count] using tail

private theorem incrementOutput_fits
    {capacity : Nat} (registers : TargetEmitter.UnaryRegisters)
    (fits : LedgerFits capacity registers)
    (available : registers.outputIndex < capacity) :
    LedgerFits capacity
      (TargetEmitterRuntimePrimitives.incrementRegisters
        .outputIndex registers) := by
  refine
    { inputCount := ?_
      normalizedGateCount := ?_
      carrierWidth := ?_
      baseline := ?_
      currentGate := ?_
      outputIndex := ?_ }
  all_goals
    simp [TargetEmitterRuntimePrimitives.incrementRegisters]
  · exact fits.inputCount
  · exact fits.normalizedGateCount
  · exact fits.carrierWidth
  · exact fits.baseline
  · exact fits.currentGate
  · omega

private theorem repeatIncrementOutput_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (count : Nat) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (bound : runtime.registers.outputIndex + count ≤ capacity) :
    ProgramSafe capacity source context
      (repeatPrimitive count
        (.incrementRegister .outputIndex))
      runtime
      (advanceOutputIndexResult runtime count) := by
  induction count generalizing runtime with
  | zero =>
      simpa [repeatPrimitive, advanceOutputIndexResult] using
        (TargetEmitterRuntimeProgram.ProgramSafe.nil runtime :
          ProgramSafe capacity source context [] runtime runtime)
  | succ count ih =>
      rw [show
        repeatPrimitive (Nat.succ count)
            (.incrementRegister .outputIndex) =
          .incrementRegister .outputIndex ::
            repeatPrimitive count
              (.incrementRegister .outputIndex) by
        simp [repeatPrimitive, List.replicate_succ]]
      let middle : Runtime :=
        { runtime with
          registers :=
            TargetEmitterRuntimePrimitives.incrementRegisters
              .outputIndex runtime.registers }
      have available :
          runtime.registers.outputIndex < capacity := by
        omega
      have middleFits : LedgerFits capacity middle.registers :=
        incrementOutput_fits runtime.registers fits available
      refine
        .cons (.incrementRegister .outputIndex)
          (repeatPrimitive count
            (.incrementRegister .outputIndex))
          runtime middle
          (advanceOutputIndexResult runtime (Nat.succ count))
          (TargetEmitterRuntimeProgram.PrimitiveSafe.incrementRegister
            runtime
            .outputIndex .outputIndex rfl fits available) ?_
      have tail := ih middle middleFits (by
        simp [middle,
          TargetEmitterRuntimePrimitives.incrementRegisters]
        omega)
      simpa [middle, advanceOutputIndexResult,
        TargetEmitterRuntimePrimitives.incrementRegisters,
        Nat.add_assoc, Nat.add_comm 1 count] using tail

private theorem computeGateAt_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (bias : Nat) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (coordinateBound :
      runtime.registers.outputIndex + bias ≤ capacity) :
    ProgramSafe capacity source context
      (computeGateAtProgram bias) runtime
      { runtime with
        scratch := runtime.registers.outputIndex + bias } := by
  let reset : Runtime := { runtime with scratch := 0 }
  let loaded : Runtime :=
    { runtime with scratch := runtime.registers.outputIndex }
  have resetSafe :=
    resetScratch_safe (context := context) runtime scratchBound
  have loadSafe :
      ProgramSafe capacity source context
        [.addRegister .outputIndex] reset loaded := by
    simpa [reset, loaded, TargetEmitterLedger.slotValue] using
      addRegister_safe (context := context) reset
        .outputIndex .outputIndex rfl
        (by simpa [reset] using fits)
        (by simpa [reset, TargetEmitterLedger.slotValue] using
          (show runtime.registers.outputIndex ≤ capacity by
            omega))
  have increments :=
    repeatIncrementScratch_safe (context := context)
      bias loaded (by simpa [loaded] using coordinateBound)
  have all :=
    resetSafe.append (loadSafe.append increments)
  simpa [computeGateAtProgram, reset, loaded,
    List.append_assoc] using all

private theorem emitSourceMarked_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source)
    (emission : EmissionSource) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (coordinateBound :
      ∀ bias, emission = .gateAt bias →
        runtime.registers.outputIndex + bias ≤ capacity)
    (notCaptured : emission ≠ .inputCaptured) :
    ProgramSafe capacity source context
      (emitSourceProgram .marked emission) runtime
      (emitSourceResult runtime emission) := by
  cases emission with
  | constant value =>
      cases value with
      | false =>
          simpa [emitSourceProgram, emitSourceResult,
            EmissionSource.finalScratch, EmissionSource.evaluate,
            encodeSourceTokens] using
            appendMarked_safe (context := context)
              layout runtime .constantFalse
      | true =>
          simpa [emitSourceProgram, emitSourceResult,
            EmissionSource.finalScratch, EmissionSource.evaluate,
            encodeSourceTokens] using
            appendMarked_safe (context := context)
              layout runtime .constantTrue
  | inputCaptured =>
      exact False.elim (notCaptured rfl)
  | inputScratch =>
      let tagged : Runtime :=
        { runtime with
          targetTokens := runtime.targetTokens ++ [.input] }
      have tag :=
        appendMarked_safe (capacity := capacity) (context := context)
          layout runtime .input
      have natural :=
        emitScratchMarked_safe (context := context) layout tagged
          (by simpa [tagged] using Nat.le_of_lt scratchBound)
      have all := tag.append natural
      simpa [emitSourceProgram, emitScratchNatProgram,
        emitSourceResult, EmissionSource.finalScratch,
        EmissionSource.evaluate, encodeSourceTokens, tagged,
        List.append_assoc] using all
  | gateScratch =>
      let tagged : Runtime :=
        { runtime with
          targetTokens := runtime.targetTokens ++ [.gate] }
      have tag :=
        appendMarked_safe (capacity := capacity) (context := context)
          layout runtime .gate
      have natural :=
        emitScratchMarked_safe (context := context) layout tagged
          (by simpa [tagged] using Nat.le_of_lt scratchBound)
      have all := tag.append natural
      simpa [emitSourceProgram, emitScratchNatProgram,
        emitSourceResult, EmissionSource.finalScratch,
        EmissionSource.evaluate, encodeSourceTokens, tagged,
        List.append_assoc] using all
  | gateAt bias =>
      let tagged : Runtime :=
        { runtime with
          targetTokens := runtime.targetTokens ++ [.gate] }
      let computed : Runtime :=
        { tagged with
          scratch := runtime.registers.outputIndex + bias }
      have tag :=
        appendMarked_safe (capacity := capacity) (context := context)
          layout runtime .gate
      have computation :=
        computeGateAt_safe (context := context) bias tagged
          (by simpa [tagged] using fits)
          (by simpa [tagged] using scratchBound)
          (by simpa [tagged] using coordinateBound bias rfl)
      have natural :=
        emitScratchMarked_safe (context := context) layout computed
          (by
            simp [computed]
            exact coordinateBound bias rfl)
      have all := tag.append (computation.append natural)
      simpa [emitSourceProgram, emitGateAtNatProgram,
        emittedNatResult, computeGateAtProgram,
        emitSourceResult, EmissionSource.finalScratch,
        EmissionSource.evaluate, encodeSourceTokens,
        tagged, computed, List.append_assoc] using all

private theorem emitGateMarked_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source)
    (left right : EmissionSource) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (leftBound :
      ∀ bias, left = .gateAt bias →
        runtime.registers.outputIndex + bias ≤ capacity)
    (rightBound :
      ∀ bias, right = .gateAt bias →
        runtime.registers.outputIndex + bias ≤ capacity)
    (leftNotCaptured : left ≠ .inputCaptured)
    (rightNotCaptured : right ≠ .inputCaptured)
    (leftFinalBound :
      left.finalScratch runtime < capacity) :
    ProgramSafe capacity source context
      (emitGateProgram .marked left right) runtime
      (emitGateResult runtime left right) := by
  let afterLeft := emitSourceResult runtime left
  let afterRight := emitSourceResult afterLeft right
  have leftSafe :=
    emitSourceMarked_safe (context := context) layout left runtime
      fits scratchBound leftBound leftNotCaptured
  have rightSafe :=
    emitSourceMarked_safe (context := context) layout right afterLeft
      (by simpa [afterLeft, emitSourceResult] using fits)
      (by simpa [afterLeft, emitSourceResult] using leftFinalBound)
      (by
        intro bias equality
        simpa [afterLeft, emitSourceResult] using
          rightBound bias equality)
      rightNotCaptured
  have endSafe :=
    appendMarked_safe (capacity := capacity) (context := context)
      layout afterRight .gateEnd
  have all := leftSafe.append (rightSafe.append endSafe)
  simpa [emitGateProgram, emitGateResult, afterLeft, afterRight,
    List.append_assoc] using all

private def pushGateAtResult
    (runtime : Runtime) (bias : Nat) : Runtime :=
  { runtime with
    scratch := 0
    checks :=
      runtime.checks ++
        [runtime.registers.outputIndex + bias] }

private theorem pushGateAt_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (bias : Nat) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (coordinateBound :
      runtime.registers.outputIndex + bias < capacity) :
    ProgramSafe capacity source context
      (pushGateAtProgram bias) runtime
      (pushGateAtResult runtime bias) := by
  let computed : Runtime :=
    { runtime with
      scratch := runtime.registers.outputIndex + bias }
  let pushed : Runtime :=
    { computed with
      checks :=
        computed.checks ++ [computed.scratch] }
  have computation :=
    computeGateAt_safe (context := context) bias runtime fits
      scratchBound (Nat.le_of_lt coordinateBound)
  have push :=
    pushCheck_safe (context := context) computed
      (by simpa [computed] using fits)
      (by simp [computed]; omega)
  have reset :=
    resetScratch_safe (context := context) pushed
      (by simpa [pushed, computed] using coordinateBound)
  have all := computation.append (push.append reset)
  simpa [pushGateAtProgram, pushGateAtResult, computed, pushed,
    List.append_assoc] using all

private def pushTotalGateResult (runtime : Runtime) : Runtime :=
  { runtime with
    scratch := 0
    checks :=
      runtime.checks ++ [runtime.registers.currentGate] }

private theorem pushTotalGate_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (gateBound : runtime.registers.currentGate < capacity) :
    ProgramSafe capacity source context
      pushTotalGateSentinelProgram runtime
      (pushTotalGateResult runtime) := by
  let reset : Runtime := { runtime with scratch := 0 }
  let loaded : Runtime :=
    { runtime with scratch := runtime.registers.currentGate }
  let pushed : Runtime :=
    { loaded with
      checks := loaded.checks ++ [loaded.scratch] }
  have resetSafe :=
    resetScratch_safe (context := context) runtime scratchBound
  have loadSafe :
      ProgramSafe capacity source context
        [.addRegister .currentGate] reset loaded := by
    simpa [reset, loaded, TargetEmitterLedger.slotValue] using
      addRegister_safe (context := context) reset
        .currentGate .currentGate rfl
        (by simpa [reset] using fits)
        (by simp [reset, TargetEmitterLedger.slotValue]; omega)
  have pushSafe :=
    pushCheck_safe (context := context) loaded
      (by simpa [loaded] using fits)
      (by simp [loaded]; omega)
  have finalReset :=
    resetScratch_safe (context := context) pushed
      (by simpa [pushed, loaded] using gateBound)
  have all :=
    resetSafe.append
      (loadSafe.append (pushSafe.append finalReset))
  simpa [pushTotalGateSentinelProgram, pushTotalGateResult,
    reset, loaded, pushed, List.append_assoc] using all

private def popCoordinateResult
    (runtime : Runtime) (prior : List Nat) (value : Nat) :
    Runtime :=
  { runtime with scratch := value, checks := prior }

private theorem popCoordinate_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime) (prior : List Nat) (value : Nat)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (checks : runtime.checks = prior ++ [value])
    (valueBound : value ≤ capacity) :
    ProgramSafe capacity source context popCoordinateProgram runtime
      (popCoordinateResult runtime prior value) := by
  let reset : Runtime := { runtime with scratch := 0 }
  have resetSafe :=
    resetScratch_safe (context := context) runtime scratchBound
  have popSafe :=
    popCheck_safe (context := context) reset prior value
      (by simpa [reset] using fits) rfl
      (by simpa [reset] using checks) valueBound
  have all := resetSafe.append popSafe
  simpa [popCoordinateProgram, popCoordinateResult, reset] using all

private def resetLiteralResult (runtime : Runtime) : Runtime :=
  { runtime with scratch := 0 }

private theorem resetLiteral_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime)
    (scratchBound : runtime.scratch < capacity) :
    ProgramSafe capacity source context resetLiteralIndexProgram
      runtime (resetLiteralResult runtime) := by
  simpa [resetLiteralIndexProgram, resetLiteralResult] using
    resetScratch_safe (context := context) runtime scratchBound

private def advanceLiteralResult (runtime : Runtime) : Runtime :=
  { runtime with scratch := runtime.scratch + 1 }

private theorem advanceLiteral_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime)
    (scratchBound : runtime.scratch < capacity) :
    ProgramSafe capacity source context advanceLiteralIndexProgram
      runtime (advanceLiteralResult runtime) := by
  simpa [advanceLiteralIndexProgram, advanceLiteralResult] using
    incrementScratch_safe (context := context) runtime scratchBound

private def positiveLiteralResult (runtime : Runtime) : Runtime :=
  advanceOutputIndexResult
    (pushGateAtResult
      (emitGateResult runtime .inputScratch .inputScratch) 0) 1

private theorem positiveLiteral_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity) :
    ProgramSafe capacity source context emitPositiveLiteralProgram
      runtime (positiveLiteralResult runtime) := by
  let emitted :=
    emitGateResult runtime .inputScratch .inputScratch
  let pushed := pushGateAtResult emitted 0
  have emission :=
    emitGateMarked_safe (context := context) layout
      .inputScratch .inputScratch runtime fits scratchBound
      (by intro bias impossible; cases impossible)
      (by intro bias impossible; cases impossible)
      (by decide) (by decide) scratchBound
  have push :=
    pushGateAt_safe (context := context) 0 emitted
      (by simpa [emitted, emitGateResult, emitSourceResult] using fits)
      (by
        simpa [emitted, emitGateResult, emitSourceResult,
          EmissionSource.finalScratch] using scratchBound)
      (by
        simp [emitted, emitGateResult, emitSourceResult]
        omega)
  have advance :=
    repeatIncrementOutput_safe (context := context) 1 pushed
      (by
        simpa [pushed, pushGateAtResult, emitted, emitGateResult,
          emitSourceResult] using fits)
      (by
        simp [pushed, pushGateAtResult, emitted, emitGateResult,
          emitSourceResult]
        omega)
  have all := emission.append (push.append advance)
  simpa [emitPositiveLiteralProgram, emitSelfNANDProgram,
    CNFToNANDControllerBlocks.mode, advanceOutputIndexProgram,
    positiveLiteralResult, emitted, pushed, List.append_assoc] using all

private def negativeLiteralResult (runtime : Runtime) : Runtime :=
  let first :=
    emitGateResult runtime .inputScratch .inputScratch
  let second :=
    emitGateResult first (.gateAt 0) (.gateAt 0)
  advanceOutputIndexResult
    (pushGateAtResult second 1) 2

private theorem negativeLiteral_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 2 ≤ capacity) :
    ProgramSafe capacity source context emitNegativeLiteralProgram
      runtime (negativeLiteralResult runtime) := by
  let first :=
    emitGateResult runtime .inputScratch .inputScratch
  let second :=
    emitGateResult first (.gateAt 0) (.gateAt 0)
  let pushed := pushGateAtResult second 1
  have firstSafe :=
    emitGateMarked_safe (context := context) layout
      .inputScratch .inputScratch runtime fits scratchBound
      (by intro bias impossible; cases impossible)
      (by intro bias impossible; cases impossible)
      (by decide) (by decide) scratchBound
  have secondSafe :=
    emitGateMarked_safe (context := context) layout
      (.gateAt 0) (.gateAt 0) first
      (by simpa [first, emitGateResult, emitSourceResult] using fits)
      (by
        simpa [first, emitGateResult, emitSourceResult,
          EmissionSource.finalScratch] using scratchBound)
      (by
        intro bias equality
        cases equality
        change runtime.registers.outputIndex + 0 ≤ capacity
        omega)
      (by
        intro bias equality
        cases equality
        change runtime.registers.outputIndex + 0 ≤ capacity
        omega)
      (by decide) (by decide)
      (by
        change runtime.registers.outputIndex + 0 < capacity
        omega)
  have push :=
    pushGateAt_safe (context := context) 1 second
      (by
        simpa [second, first, emitGateResult, emitSourceResult] using fits)
      (by
        simp [second, first, emitGateResult, emitSourceResult,
          EmissionSource.finalScratch]
        omega)
      (by
        simp [second, first, emitGateResult, emitSourceResult]
        omega)
  have advance :=
    repeatIncrementOutput_safe (context := context) 2 pushed
      (by
        simpa [pushed, pushGateAtResult, second, first, emitGateResult,
          emitSourceResult] using fits)
      (by
        simp [pushed, pushGateAtResult, second, first, emitGateResult,
          emitSourceResult]
        omega)
  have all :=
    firstSafe.append
      (secondSafe.append (push.append advance))
  simpa [emitNegativeLiteralProgram, emitSelfNANDProgram,
    CNFToNANDControllerBlocks.mode, advanceOutputIndexProgram,
    negativeLiteralResult, first, second, pushed,
    List.append_assoc] using all

private def invalidLiteralResult (runtime : Runtime) : Runtime :=
  advanceOutputIndexResult
    (pushGateAtResult
      (emitGateResult runtime (.constant false) (.constant false)) 0) 1

private theorem invalidLiteral_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity) :
    ProgramSafe capacity source context emitInvalidLiteralProgram
      runtime (invalidLiteralResult runtime) := by
  let emitted :=
    emitGateResult runtime (.constant false) (.constant false)
  let pushed := pushGateAtResult emitted 0
  have emission :=
    emitGateMarked_safe (context := context) layout
      (.constant false) (.constant false) runtime fits scratchBound
      (by intro bias impossible; cases impossible)
      (by intro bias impossible; cases impossible)
      (by decide) (by decide)
      (by simpa [EmissionSource.finalScratch] using scratchBound)
  have push :=
    pushGateAt_safe (context := context) 0 emitted
      (by simpa [emitted, emitGateResult, emitSourceResult] using fits)
      (by
        simpa [emitted, emitGateResult, emitSourceResult,
          EmissionSource.finalScratch] using scratchBound)
      (by
        simp [emitted, emitGateResult, emitSourceResult]
        omega)
  have advance :=
    repeatIncrementOutput_safe (context := context) 1 pushed
      (by
        simpa [pushed, pushGateAtResult, emitted, emitGateResult,
          emitSourceResult] using fits)
      (by
        simp [pushed, pushGateAtResult, emitted, emitGateResult,
          emitSourceResult]
        omega)
  have all := emission.append (push.append advance)
  simpa [emitInvalidLiteralProgram, emitSelfNANDProgram,
    CNFToNANDControllerBlocks.mode, advanceOutputIndexProgram,
    invalidLiteralResult, emitted, pushed, List.append_assoc] using all

private def seedClauseResult (runtime : Runtime) : Runtime :=
  let falseGate :=
    emitGateResult runtime (.constant false) (.constant false)
  let combined :=
    emitGateResult falseGate .gateScratch (.gateAt 0)
  advanceOutputIndexResult combined 1

private theorem seedClause_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity) :
    ProgramSafe capacity source context seedClauseProgram
      runtime (seedClauseResult runtime) := by
  let falseGate :=
    emitGateResult runtime (.constant false) (.constant false)
  let combined :=
    emitGateResult falseGate .gateScratch (.gateAt 0)
  have falseSafe :=
    emitGateMarked_safe (context := context) layout
      (.constant false) (.constant false) runtime fits scratchBound
      (by intro bias impossible; cases impossible)
      (by intro bias impossible; cases impossible)
      (by decide) (by decide)
      (by simpa [EmissionSource.finalScratch] using scratchBound)
  have combinedSafe :=
    emitGateMarked_safe (context := context) layout
      .gateScratch (.gateAt 0) falseGate
      (by simpa [falseGate, emitGateResult, emitSourceResult] using fits)
      (by
        simpa [falseGate, emitGateResult, emitSourceResult,
          EmissionSource.finalScratch] using scratchBound)
      (by intro bias impossible; cases impossible)
      (by
        intro bias equality
        cases equality
        change runtime.registers.outputIndex + 0 ≤ capacity
        omega)
      (by decide) (by decide)
      (by
        simpa [falseGate, emitGateResult, emitSourceResult,
          EmissionSource.finalScratch] using scratchBound)
  have advance :=
    repeatIncrementOutput_safe (context := context) 1 combined
      (by
        simpa [combined, falseGate, emitGateResult,
          emitSourceResult] using fits)
      (by
        simp [combined, falseGate, emitGateResult, emitSourceResult]
        omega)
  have all := falseSafe.append (combinedSafe.append advance)
  simpa [seedClauseProgram, emitSelfNANDProgram,
    CNFToNANDControllerBlocks.mode, advanceOutputIndexProgram,
    seedClauseResult, falseGate, combined,
    List.append_assoc] using all

private def extendClauseResult (runtime : Runtime) : Runtime :=
  let preserved : Runtime :=
    { runtime with
      checks := runtime.checks ++ [runtime.scratch] }
  let negated :=
    emitGateResult preserved (.gateAt 0) (.gateAt 0)
  let restored :=
    popCoordinateResult negated runtime.checks runtime.scratch
  let combined :=
    emitGateResult restored .gateScratch (.gateAt 1)
  advanceOutputIndexResult combined 2

private theorem extendClause_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 2 ≤ capacity) :
    ProgramSafe capacity source context extendClauseProgram
      runtime (extendClauseResult runtime) := by
  let preserved : Runtime :=
    { runtime with
      checks := runtime.checks ++ [runtime.scratch] }
  let negated :=
    emitGateResult preserved (.gateAt 0) (.gateAt 0)
  let restored :=
    popCoordinateResult negated runtime.checks runtime.scratch
  let combined :=
    emitGateResult restored .gateScratch (.gateAt 1)
  have preserve :=
    pushCheck_safe (context := context) runtime fits
      (Nat.le_of_lt scratchBound)
  have negate :=
    emitGateMarked_safe (context := context) layout
      (.gateAt 0) (.gateAt 0) preserved
      (by simpa [preserved] using fits)
      (by simpa [preserved] using scratchBound)
      (by
        intro bias equality
        cases equality
        change runtime.registers.outputIndex + 0 ≤ capacity
        omega)
      (by
        intro bias equality
        cases equality
        change runtime.registers.outputIndex + 0 ≤ capacity
        omega)
      (by decide) (by decide)
      (by
        change runtime.registers.outputIndex + 0 < capacity
        omega)
  have restore :=
    popCoordinate_safe (context := context) negated
      runtime.checks runtime.scratch
      (by
        simpa [negated, preserved, emitGateResult,
          emitSourceResult] using fits)
      (by
        simp [negated, preserved, emitGateResult,
          emitSourceResult, EmissionSource.finalScratch]
        omega)
      (by
        simp [negated, preserved, emitGateResult, emitSourceResult])
      (Nat.le_of_lt scratchBound)
  have combine :=
    emitGateMarked_safe (context := context) layout
      .gateScratch (.gateAt 1) restored
      (by
        simpa [restored, popCoordinateResult, negated, preserved,
          emitGateResult, emitSourceResult] using fits)
      (by simpa [restored, popCoordinateResult] using scratchBound)
      (by intro bias impossible; cases impossible)
      (by
        intro bias equality
        cases equality
        change runtime.registers.outputIndex + 1 ≤ capacity
        omega)
      (by decide) (by decide)
      (by simpa [restored, popCoordinateResult,
        EmissionSource.finalScratch] using scratchBound)
  have advance :=
    repeatIncrementOutput_safe (context := context) 2 combined
      (by
        simpa [combined, restored, popCoordinateResult, negated,
          preserved, emitGateResult, emitSourceResult] using fits)
      (by
        simp [combined, restored, popCoordinateResult, negated,
          preserved, emitGateResult, emitSourceResult]
        omega)
  have all :=
    preserve.append
      (negate.append (restore.append (combine.append advance)))
  simpa [extendClauseProgram, popCoordinateProgram,
    emitSelfNANDProgram, CNFToNANDControllerBlocks.mode,
    advanceOutputIndexProgram, extendClauseResult, preserved,
    negated, restored, combined, List.append_assoc] using all

private def finishNonemptyClauseResult (runtime : Runtime) : Runtime :=
  advanceOutputIndexResult (pushGateAtResult runtime 0) 1

private theorem finishNonemptyClause_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity) :
    ProgramSafe capacity source context finishNonemptyClauseProgram
      runtime (finishNonemptyClauseResult runtime) := by
  let pushed := pushGateAtResult runtime 0
  have push :=
    pushGateAt_safe (context := context) 0 runtime fits scratchBound
      (by omega)
  have advance :=
    repeatIncrementOutput_safe (context := context) 1 pushed
      (by simpa [pushed, pushGateAtResult] using fits)
      (by simp [pushed, pushGateAtResult]; omega)
  have all := push.append advance
  simpa [finishNonemptyClauseProgram,
    advanceOutputIndexProgram, finishNonemptyClauseResult,
    pushed, List.append_assoc] using all

private theorem finishEmptyClause_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (gateBound : runtime.registers.currentGate < capacity) :
    ProgramSafe capacity source context finishEmptyClauseProgram
      runtime (pushTotalGateResult runtime) := by
  simpa [finishEmptyClauseProgram] using
    pushTotalGate_safe (context := context) runtime fits
      scratchBound gateBound

private def seedFormulaResult
    (source : ClauseSource) (runtime : Runtime) : Runtime :=
  let combined :=
    emitGateResult runtime source.emission (.constant true)
  let normalized :=
    emitGateResult combined (.gateAt 0) (.gateAt 0)
  advanceOutputIndexResult normalized 1

private theorem seedFormula_safe
    {capacity : Nat} {sourceWord : List WorkSymbol}
    {context : SourceContext sourceWord}
    (layout : CursorLayout sourceWord)
    (source : ClauseSource) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity) :
    ProgramSafe capacity sourceWord context (seedFormulaProgram source)
      runtime (seedFormulaResult source runtime) := by
  let combined :=
    emitGateResult runtime source.emission (.constant true)
  let normalized :=
    emitGateResult combined (.gateAt 0) (.gateAt 0)
  have combinedSafe :
      ProgramSafe capacity sourceWord context
        (emitGateProgram .marked source.emission (.constant true))
        runtime combined := by
    apply emitGateMarked_safe (context := context) layout
      source.emission (.constant true) runtime fits scratchBound
    · intro bias impossible
      cases source <;> cases impossible
    · intro bias impossible
      cases impossible
    · cases source <;> decide
    · decide
    · cases source <;>
        simpa [ClauseSource.emission,
          EmissionSource.finalScratch] using scratchBound
  have normalizedSafe :=
    emitGateMarked_safe (context := context) layout
      (.gateAt 0) (.gateAt 0) combined
      (by simpa [combined, emitGateResult, emitSourceResult] using fits)
      (by
        cases source <;>
          simpa [combined, emitGateResult, emitSourceResult,
            ClauseSource.emission, EmissionSource.finalScratch] using
            scratchBound)
      (by
        intro bias equality
        cases equality
        change runtime.registers.outputIndex + 0 ≤ capacity
        omega)
      (by
        intro bias equality
        cases equality
        change runtime.registers.outputIndex + 0 ≤ capacity
        omega)
      (by decide) (by decide)
      (by
        change runtime.registers.outputIndex + 0 < capacity
        omega)
  have advance :=
    repeatIncrementOutput_safe (context := context) 1 normalized
      (by
        simpa [normalized, combined, emitGateResult,
          emitSourceResult] using fits)
      (by
        simp [normalized, combined, emitGateResult, emitSourceResult]
        omega)
  have all := combinedSafe.append (normalizedSafe.append advance)
  simpa [seedFormulaProgram, CNFToNANDControllerBlocks.mode,
    emitSelfNANDProgram, advanceOutputIndexProgram,
    seedFormulaResult, combined, normalized,
    List.append_assoc] using all

private def extendFormulaResult
    (source : ClauseSource) (runtime : Runtime) : Runtime :=
  let combined :=
    emitGateResult runtime source.emission (.gateAt 0)
  let normalized :=
    emitGateResult combined (.gateAt 1) (.gateAt 1)
  advanceOutputIndexResult normalized 2

private theorem extendFormula_safe
    {capacity : Nat} {sourceWord : List WorkSymbol}
    {context : SourceContext sourceWord}
    (layout : CursorLayout sourceWord)
    (source : ClauseSource) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 2 ≤ capacity) :
    ProgramSafe capacity sourceWord context
      (extendFormulaProgram source) runtime
      (extendFormulaResult source runtime) := by
  let combined :=
    emitGateResult runtime source.emission (.gateAt 0)
  let normalized :=
    emitGateResult combined (.gateAt 1) (.gateAt 1)
  have combinedSafe :
      ProgramSafe capacity sourceWord context
        (emitGateProgram .marked source.emission (.gateAt 0))
        runtime combined := by
    apply emitGateMarked_safe (context := context) layout
      source.emission (.gateAt 0) runtime fits scratchBound
    · intro bias impossible
      cases source <;> cases impossible
    · intro bias equality
      cases equality
      change runtime.registers.outputIndex + 0 ≤ capacity
      omega
    · cases source <;> decide
    · decide
    · cases source <;>
        simpa [ClauseSource.emission,
          EmissionSource.finalScratch] using scratchBound
  have normalizedSafe :=
    emitGateMarked_safe (context := context) layout
      (.gateAt 1) (.gateAt 1) combined
      (by simpa [combined, emitGateResult, emitSourceResult] using fits)
      (by
        simp [combined, emitGateResult, emitSourceResult,
          EmissionSource.finalScratch]
        omega)
      (by
        intro bias equality
        cases equality
        change runtime.registers.outputIndex + 1 ≤ capacity
        omega)
      (by
        intro bias equality
        cases equality
        change runtime.registers.outputIndex + 1 ≤ capacity
        omega)
      (by decide) (by decide)
      (by
        change runtime.registers.outputIndex + 1 < capacity
        omega)
  have advance :=
    repeatIncrementOutput_safe (context := context) 2 normalized
      (by
        simpa [normalized, combined, emitGateResult,
          emitSourceResult] using fits)
      (by
        simp [normalized, combined, emitGateResult, emitSourceResult]
        omega)
  have all := combinedSafe.append (normalizedSafe.append advance)
  simpa [extendFormulaProgram, CNFToNANDControllerBlocks.mode,
    emitSelfNANDProgram, advanceOutputIndexProgram,
    extendFormulaResult, combined, normalized,
    List.append_assoc] using all

private def emptyFormulaResult (runtime : Runtime) : Runtime :=
  emitGateResult runtime (.constant false) (.constant false)

private theorem emptyFormula_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity) :
    ProgramSafe capacity source context emitEmptyFormulaProgram
      runtime (emptyFormulaResult runtime) := by
  simpa [emitEmptyFormulaProgram, emitSelfNANDProgram,
    CNFToNANDControllerBlocks.mode, emptyFormulaResult] using
    emitGateMarked_safe (context := context) layout
      (.constant false) (.constant false) runtime fits scratchBound
      (by intro bias impossible; cases impossible)
      (by intro bias impossible; cases impossible)
      (by decide) (by decide)
      (by simpa [EmissionSource.finalScratch] using scratchBound)

private theorem suffix_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex ≤ capacity) :
    ProgramSafe capacity source context emitCircuitSuffixProgram runtime
      (circuitSuffixResult runtime) := by
  let afterProgram : Runtime :=
    { runtime with
      targetTokens := runtime.targetTokens ++ [.programEnd] }
  let afterOutput :=
    emitSourceResult afterProgram (.gateAt 0)
  let afterEnd : Runtime :=
    { afterOutput with
      targetTokens := afterOutput.targetTokens ++ [.outputsEnd] }
  have programToken :=
    appendMarked_safe (capacity := capacity) (context := context)
      layout runtime .programEnd
  have output :=
    emitSourceMarked_safe (context := context) layout
      (.gateAt 0) afterProgram
      (by simpa [afterProgram] using fits)
      (by simpa [afterProgram] using scratchBound)
      (by
        intro bias equality
        cases equality
        simpa [afterProgram] using outputBound)
      (by decide)
  have outputsEnd :=
    appendMarked_safe (capacity := capacity) (context := context)
      layout afterOutput .outputsEnd
  have instanceEnd :=
    appendMarked_safe (capacity := capacity) (context := context)
      layout afterEnd .instanceEnd
  have all :=
    programToken.append
      (output.append (outputsEnd.append instanceEnd))
  simpa [emitCircuitSuffixProgram, circuitSuffixProgram,
    CNFToNANDControllerBlocks.mode, circuitSuffixResult,
    afterProgram, afterOutput, afterEnd, emitSourceResult,
    EmissionSource.finalScratch, EmissionSource.evaluate,
    encodeSourceTokens, List.append_assoc] using all

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
        source final.targetTokens finalTape := by
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
      rcases
          materializedBlock_path descriptor descriptorMember
            (first :: rest) compiled (by simp)
            safe initialTape represents with
        ⟨steps, finalTape, path, finalRepresents⟩
      refine ⟨steps, finalTape, path, ?_⟩
      exact represents_at_state (newState := finalState) finalRepresents

private theorem closedBlock_path_bounded
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
      have inputRepresents :
          TargetEmitterRuntime.Represents
            (TargetEmitterRuntimeProgram.entryState
              0 (first :: rest))
            capacity initial.scratch initial.registers initial.checks
            source initial.targetTokens
            { state :=
                TargetEmitterRuntimeProgram.entryState
                  0 (first :: rest)
              tape := initialTape } := by
        rw [← startEq]
        exact represents
      rcases
          PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramBound.ProgramSafe.linearAcceptRuns_bounded
            safe initialScratchBound (first :: rest) compiled 0
            { state :=
                TargetEmitterRuntimeProgram.entryState
                  0 (first :: rest)
              tape := initialTape }
            inputRepresents with
        ⟨steps, actualFinal, runs, finalRepresents, bounded⟩
      have included :
          ∀ node,
            node ∈
                blockNodes descriptor.code descriptor.primitives
                  descriptor.continuation →
              node ∈ graph.nodes := by
        intro node nodeMember
        exact
          descriptorBlockNode_member_nodes descriptor
            descriptorMember node nodeMember
      have rawPath :=
        blockNodes_acceptPath_of_compiled graph descriptor.code
          descriptor.primitives (first :: rest)
          descriptor.continuation steps initialTape
          actualFinal.tape compiled included runs
      have entryEq :=
        blockEntry_eq_entryEndpoint_of_compiled descriptor.code
          descriptor.primitives (first :: rest)
          descriptor.continuation compiled (by simp)
      refine ⟨steps, actualFinal.tape, ?_, ?_, bounded⟩
      · rw [← entryEq] at rawPath
        exact rawPath
      · exact
          represents_at_state
            (newState := finalState) finalRepresents

private theorem indexedBlock_path
    (index : Nat) (bound : index < blockDescriptors.length)
    (finalState : Nat)
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context
        blockDescriptors[index].primitives initial final)
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
        source final.targetTokens finalTape := by
  exact
    closedBlock_path blockDescriptors[index]
      (List.getElem_mem bound) finalState safe initialTape represents

private theorem namedIndexedBlock_path
    (index : Nat) (bound : index < blockDescriptors.length)
    (entry : NodeRef) (continuation : Endpoint)
    (entryEq :
      blockEntry blockDescriptors[index].code
          blockDescriptors[index].primitives = entry)
    (continuationEq :
      blockDescriptors[index].continuation = continuation)
    (finalState : Nat)
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context
        blockDescriptors[index].primitives initial final)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents entry.startState
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node entry) continuation
        steps initialTape finalTape ∧
      TapeRepresents finalState
        capacity final.scratch final.registers final.checks
        source final.targetTokens finalTape := by
  have input :
      TapeRepresents
        (blockEntry blockDescriptors[index].code
          blockDescriptors[index].primitives).startState
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens initialTape := by
    simpa [entryEq] using represents
  rcases indexedBlock_path index bound finalState
      safe initialTape input with
    ⟨steps, finalTape, path, finalRepresents⟩
  exact
    ⟨steps, finalTape,
      by simpa [entryEq, continuationEq] using path,
      finalRepresents⟩

private theorem namedIndexedBlock_path_bounded
    (index : Nat) (bound : index < blockDescriptors.length)
    (entry : NodeRef) (continuation : Endpoint)
    (entryEq :
      blockEntry blockDescriptors[index].code
          blockDescriptors[index].primitives = entry)
    (continuationEq :
      blockDescriptors[index].continuation = continuation)
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
      TapeRepresents entry.startState
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node entry) continuation
        steps initialTape finalTape ∧
      TapeRepresents finalState
        capacity final.scratch final.registers final.checks
        source final.targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source initial
          blockDescriptors[index].primitives := by
  have input :
      TapeRepresents
        (blockEntry blockDescriptors[index].code
          blockDescriptors[index].primitives).startState
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens initialTape := by
    simpa [entryEq] using represents
  rcases
      closedBlock_path_bounded blockDescriptors[index]
        (List.getElem_mem bound) finalState safe
        initialScratchBound initialTape input with
    ⟨steps, finalTape, path, finalRepresents, bounded⟩
  exact
    ⟨steps, finalTape,
      by simpa [entryEq, continuationEq] using path,
      finalRepresents, bounded⟩

private theorem positiveLiteralBlock_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents emitPositiveLiteralRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node emitPositiveLiteralRef)
        (.node (restoreRef .emit .clause .f))
        steps initialTape finalTape ∧
      TapeRepresents (restoreRef .emit .clause .f).startState
        capacity (positiveLiteralResult runtime).scratch
        (positiveLiteralResult runtime).registers
        (positiveLiteralResult runtime).checks source
        (positiveLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[12].primitives := by
  have safe :
      ProgramSafe capacity source context
        blockDescriptors[12].primitives runtime
        (positiveLiteralResult runtime) := by
    simpa [blockDescriptors] using
      positiveLiteral_safe layout runtime fits scratchBound outputBound
  rcases namedIndexedBlock_path_bounded 12 (by decide)
      emitPositiveLiteralRef
      (.node (restoreRef .emit .clause .f))
      (by rfl) (by rfl)
      (restoreRef .emit .clause .f).startState
      safe (Nat.le_of_lt scratchBound)
      initialTape represents with
    ⟨steps, finalTape, path, finalRepresents, bounded⟩
  exact ⟨steps, finalTape, path, finalRepresents, bounded⟩

private theorem initializeClauseBlock_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (gateBound : runtime.registers.currentGate < capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents emitInitializeClauseRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node emitInitializeClauseRef)
        (.node (restoreRef .emit .clause .sep))
        steps initialTape finalTape ∧
      TapeRepresents (restoreRef .emit .clause .sep).startState
        capacity (pushTotalGateResult runtime).scratch
        (pushTotalGateResult runtime).registers
        (pushTotalGateResult runtime).checks source
        (pushTotalGateResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[9].primitives := by
  have safe :
      ProgramSafe capacity source context
        blockDescriptors[9].primitives runtime
        (pushTotalGateResult runtime) := by
    simpa [blockDescriptors, initializeClauseStackProgram] using
      pushTotalGate_safe (context := context) runtime fits
        scratchBound gateBound
  exact namedIndexedBlock_path_bounded 9 (by decide)
    emitInitializeClauseRef
    (.node (restoreRef .emit .clause .sep))
    (by rfl) (by rfl)
    (restoreRef .emit .clause .sep).startState
    safe (Nat.le_of_lt scratchBound) initialTape represents

private theorem negativeSignBlock_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime) (scratchBound : runtime.scratch < capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents emitNegativeSignRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node emitNegativeSignRef)
        (.node (literalCompareRef .emit .clause .f))
        steps initialTape finalTape ∧
      TapeRepresents (literalCompareRef .emit .clause .f).startState
        capacity (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks source
        (resetLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[10].primitives := by
  have safe :
      ProgramSafe capacity source context
        blockDescriptors[10].primitives runtime
        (resetLiteralResult runtime) := by
    simpa [blockDescriptors, Blocks.emitNegativeSignProgram] using
      resetLiteral_safe (context := context) runtime scratchBound
  exact namedIndexedBlock_path_bounded 10 (by decide)
    emitNegativeSignRef
    (.node (literalCompareRef .emit .clause .f))
    (by rfl) (by rfl)
    (literalCompareRef .emit .clause .f).startState
    safe (Nat.le_of_lt scratchBound) initialTape represents

private theorem positiveSignBlock_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime) (scratchBound : runtime.scratch < capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents emitPositiveSignRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node emitPositiveSignRef)
        (.node (literalCompareRef .emit .clause .t))
        steps initialTape finalTape ∧
      TapeRepresents (literalCompareRef .emit .clause .t).startState
        capacity (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks source
        (resetLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[11].primitives := by
  have safe :
      ProgramSafe capacity source context
        blockDescriptors[11].primitives runtime
        (resetLiteralResult runtime) := by
    simpa [blockDescriptors, Blocks.emitPositiveSignProgram] using
      resetLiteral_safe (context := context) runtime scratchBound
  exact namedIndexedBlock_path_bounded 11 (by decide)
    emitPositiveSignRef
    (.node (literalCompareRef .emit .clause .t))
    (by rfl) (by rfl)
    (literalCompareRef .emit .clause .t).startState
    safe (Nat.le_of_lt scratchBound) initialTape represents

private theorem negativeLiteralBlock_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 2 ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents emitNegativeLiteralRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node emitNegativeLiteralRef)
        (.node (restoreRef .emit .clause .f))
        steps initialTape finalTape ∧
      TapeRepresents (restoreRef .emit .clause .f).startState
        capacity (negativeLiteralResult runtime).scratch
        (negativeLiteralResult runtime).registers
        (negativeLiteralResult runtime).checks source
        (negativeLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[13].primitives := by
  have safe :
      ProgramSafe capacity source context
        blockDescriptors[13].primitives runtime
        (negativeLiteralResult runtime) := by
    simpa [blockDescriptors] using
      negativeLiteral_safe layout runtime fits scratchBound outputBound
  exact namedIndexedBlock_path_bounded 13 (by decide)
    emitNegativeLiteralRef
    (.node (restoreRef .emit .clause .f))
    (by rfl) (by rfl)
    (restoreRef .emit .clause .f).startState
    safe (Nat.le_of_lt scratchBound) initialTape represents

private theorem invalidLiteralBlock_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents emitInvalidLiteralRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node emitInvalidLiteralRef)
        (.node (restoreRef .emit .clause .f))
        steps initialTape finalTape ∧
      TapeRepresents (restoreRef .emit .clause .f).startState
        capacity (invalidLiteralResult runtime).scratch
        (invalidLiteralResult runtime).registers
        (invalidLiteralResult runtime).checks source
        (invalidLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[14].primitives := by
  have safe :
      ProgramSafe capacity source context
        blockDescriptors[14].primitives runtime
        (invalidLiteralResult runtime) := by
    simpa [blockDescriptors] using
      invalidLiteral_safe layout runtime fits scratchBound outputBound
  exact namedIndexedBlock_path_bounded 14 (by decide)
    emitInvalidLiteralRef
    (.node (restoreRef .emit .clause .f))
    (by rfl) (by rfl)
    (restoreRef .emit .clause .f).startState
    safe (Nat.le_of_lt scratchBound) initialTape represents

private theorem advanceLiteralBlock_path
    (positive : Bool)
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime)
    (scratchBound : runtime.scratch < capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (advanceLiteralRef .emit positive).startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (advanceLiteralRef .emit positive))
        (.node
          (restoreRef .emit (inRangeState positive) .t))
        steps initialTape finalTape ∧
      TapeRepresents
        (restoreRef .emit (inRangeState positive) .t).startState
        capacity (advanceLiteralResult runtime).scratch
        (advanceLiteralResult runtime).registers
        (advanceLiteralResult runtime).checks source
        (advanceLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime
          (if positive then blockDescriptors[15].primitives
            else blockDescriptors[16].primitives) := by
  have safe :
      ProgramSafe capacity source context
        advanceLiteralIndexProgram runtime
        (advanceLiteralResult runtime) := by
    exact advanceLiteral_safe (context := context) runtime scratchBound
  cases positive with
  | false =>
      simpa [advanceLiteralRef, inRangeState, blockDescriptors] using
        (namedIndexedBlock_path_bounded 16 (by decide)
          emitAdvanceNegativeRef
          (.node (restoreRef .emit .negative .t))
          (by rfl) (by rfl)
          (restoreRef .emit .negative .t).startState
          (by simpa [blockDescriptors] using safe)
          (Nat.le_of_lt scratchBound)
          initialTape
          (by simpa [advanceLiteralRef] using represents))
  | true =>
      simpa [advanceLiteralRef, inRangeState, blockDescriptors] using
        (namedIndexedBlock_path_bounded 15 (by decide)
          emitAdvancePositiveRef
          (.node (restoreRef .emit .positive .t))
          (by rfl) (by rfl)
          (restoreRef .emit .positive .t).startState
          (by simpa [blockDescriptors] using safe)
          (Nat.le_of_lt scratchBound)
          initialTape
          (by simpa [advanceLiteralRef] using represents))

private def slotCompareSteps
    (slot : TargetEmitterLedger.Slot)
    (capacity scratch : Nat) : Nat :=
  TargetEmitterScratchCompareSlot.workSteps
      slot capacity scratch + 1

private theorem slot_compare_equal_path
    (slot : TargetEmitterLedger.Slot)
    (code : Nat) (onAccept onReject : Endpoint)
    (finalState capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (initialTape : WorkTape)
    (member :
      controlNode code
          (TargetEmitterScratchCompareSlot.machineFor slot)
          onAccept onReject ∈ graph.nodes)
    (fits : LedgerFits capacity registers)
    (equal :
      scratch =
        TargetEmitterLedger.slotValue registers slot)
    (allowed :
      TargetEmitterScratchCompareSlot.SourceAllowed sourceHead)
    (represents :
      TapeRepresents
        (controlRef code
          (TargetEmitterScratchCompareSlot.machineFor slot)).startState
        capacity scratch registers checks
        (sourceHead :: sourceTail) target initialTape) :
    ∃ finalTape,
      AcceptPath graph
        (.node
          (controlRef code
            (TargetEmitterScratchCompareSlot.machineFor slot)))
        onAccept (slotCompareSteps slot capacity scratch)
        initialTape finalTape ∧
      TapeRepresents finalState capacity scratch registers checks
        (sourceHead :: sourceTail) target finalTape := by
  have inputRepresents :
      TargetEmitterRuntime.Represents
        (TargetEmitterScratchCompareSlot.startState slot)
        capacity scratch registers checks
        (sourceHead :: sourceTail) target
        { state :=
            TargetEmitterScratchCompareSlot.startState slot
          tape := initialTape } := by
    simpa [TapeRepresents, controlRef,
      TargetEmitterScratchCompareSlot.machineFor] using represents
  rcases
      TargetEmitterRuntimePrimitives.compareRegisterEqual_exact
        slot capacity scratch registers checks
        sourceHead sourceTail target
        { state :=
            TargetEmitterScratchCompareSlot.startState slot
          tape := initialTape }
        fits.toPrimitive equal allowed inputRepresents with
    ⟨finalConfiguration, exactRun, finalRepresents⟩
  have exactRun' :
      workRunExact?
          (TargetEmitterScratchCompareSlot.machineFor slot)
          (TargetEmitterScratchCompareSlot.workSteps
            slot capacity scratch)
          { state :=
              TargetEmitterScratchCompareSlot.startState slot
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
            (TargetEmitterScratchCompareSlot.machineFor slot)))
        onAccept (slotCompareSteps slot capacity scratch)
        initialTape finalConfiguration.tape := by
    simpa [slotCompareSteps] using
      localAccept_path code
        (TargetEmitterScratchCompareSlot.machineFor slot)
        onAccept onReject onAccept
        (TargetEmitterScratchCompareSlot.workSteps
          slot capacity scratch)
        0 initialTape finalConfiguration.tape
        finalConfiguration.tape member exactRun' terminal
  exact
    ⟨finalConfiguration.tape, path,
      represents_at_state
        (newState := finalState) finalRepresents⟩

private theorem slot_compare_less_path
    (slot : TargetEmitterLedger.Slot)
    (code : Nat) (onAccept onReject : Endpoint)
    (finalState capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (initialTape : WorkTape)
    (member :
      controlNode code
          (TargetEmitterScratchCompareSlot.machineFor slot)
          onAccept onReject ∈ graph.nodes)
    (fits : LedgerFits capacity registers)
    (less :
      scratch <
        TargetEmitterLedger.slotValue registers slot)
    (allowed :
      TargetEmitterScratchCompareSlot.SourceAllowed sourceHead)
    (represents :
      TapeRepresents
        (controlRef code
          (TargetEmitterScratchCompareSlot.machineFor slot)).startState
        capacity scratch registers checks
        (sourceHead :: sourceTail) target initialTape) :
    ∃ finalTape,
      AcceptPath graph
        (.node
          (controlRef code
            (TargetEmitterScratchCompareSlot.machineFor slot)))
        onReject (slotCompareSteps slot capacity scratch)
        initialTape finalTape ∧
      TapeRepresents finalState capacity scratch registers checks
        (sourceHead :: sourceTail) target finalTape := by
  have inputRepresents :
      TargetEmitterRuntime.Represents
        (TargetEmitterScratchCompareSlot.startState slot)
        capacity scratch registers checks
        (sourceHead :: sourceTail) target
        { state :=
            TargetEmitterScratchCompareSlot.startState slot
          tape := initialTape } := by
    simpa [TapeRepresents, controlRef,
      TargetEmitterScratchCompareSlot.machineFor] using represents
  rcases
      TargetEmitterRuntimePrimitives.compareRegisterLess_exact
        slot capacity scratch registers checks
        sourceHead sourceTail target
        { state :=
            TargetEmitterScratchCompareSlot.startState slot
          tape := initialTape }
        fits.toPrimitive less allowed inputRepresents with
    ⟨finalConfiguration, exactRun, finalRepresents⟩
  have exactRun' :
      workRunExact?
          (TargetEmitterScratchCompareSlot.machineFor slot)
          (TargetEmitterScratchCompareSlot.workSteps
            slot capacity scratch)
          { state :=
              TargetEmitterScratchCompareSlot.startState slot
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
            (TargetEmitterScratchCompareSlot.machineFor slot)))
        onReject (slotCompareSteps slot capacity scratch)
        initialTape finalConfiguration.tape := by
    simpa [slotCompareSteps] using
      localReject_path code
        (TargetEmitterScratchCompareSlot.machineFor slot)
        onAccept onReject onReject
        (TargetEmitterScratchCompareSlot.workSteps
          slot capacity scratch)
        0 initialTape finalConfiguration.tape
        finalConfiguration.tape member exactRun' terminal
  exact
    ⟨finalConfiguration.tape, path,
      represents_at_state
        (newState := finalState) finalRepresents⟩

private theorem popCoordinateBlock_path
    (index : Nat) (bound : index < blockDescriptors.length)
    (entry : NodeRef) (continuation : Endpoint)
    (primitivesEq :
      blockDescriptors[index].primitives =
        Blocks.popCoordinateProgram)
    (entryEq :
      blockEntry blockDescriptors[index].code
          blockDescriptors[index].primitives = entry)
    (continuationEq :
      blockDescriptors[index].continuation = continuation)
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime) (prior : List Nat) (value : Nat)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (checks : runtime.checks = prior ++ [value])
    (valueBound : value ≤ capacity)
    (finalState : Nat)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents entry.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node entry) continuation
        steps initialTape finalTape ∧
      TapeRepresents finalState capacity
        (popCoordinateResult runtime prior value).scratch
        (popCoordinateResult runtime prior value).registers
        (popCoordinateResult runtime prior value).checks source
        (popCoordinateResult runtime prior value).targetTokens
        finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[index].primitives := by
  have safe :
      ProgramSafe capacity source context
        Blocks.popCoordinateProgram runtime
        (popCoordinateResult runtime prior value) :=
    popCoordinate_safe (context := context)
      runtime prior value fits scratchBound checks valueBound
  exact
    namedIndexedBlock_path_bounded index bound entry continuation
      entryEq continuationEq finalState
      (by simpa [primitivesEq] using safe)
      (Nat.le_of_lt scratchBound)
      initialTape represents

private theorem clauseSeedBlock_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents clauseSeedRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node clauseSeedRef)
        (.node clausePopLoopRef)
        steps initialTape finalTape ∧
      TapeRepresents clausePopLoopRef.startState
        capacity (seedClauseResult runtime).scratch
        (seedClauseResult runtime).registers
        (seedClauseResult runtime).checks source
        (seedClauseResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[20].primitives := by
  have safe :
      ProgramSafe capacity source context seedClauseProgram runtime
        (seedClauseResult runtime) :=
    seedClause_safe layout runtime fits scratchBound outputBound
  exact namedIndexedBlock_path_bounded 20 (by decide)
    clauseSeedRef (.node clausePopLoopRef)
    (by rfl) (by rfl) clausePopLoopRef.startState
    (by simpa [blockDescriptors] using safe)
    (Nat.le_of_lt scratchBound)
    initialTape represents

private theorem clauseExtendBlock_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 2 ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents clauseExtendRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node clauseExtendRef)
        (.node clausePopLoopRef)
        steps initialTape finalTape ∧
      TapeRepresents clausePopLoopRef.startState
        capacity (extendClauseResult runtime).scratch
        (extendClauseResult runtime).registers
        (extendClauseResult runtime).checks source
        (extendClauseResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[22].primitives := by
  have safe :
      ProgramSafe capacity source context extendClauseProgram runtime
        (extendClauseResult runtime) :=
    extendClause_safe layout runtime fits scratchBound outputBound
  exact namedIndexedBlock_path_bounded 22 (by decide)
    clauseExtendRef (.node clausePopLoopRef)
    (by rfl) (by rfl) clausePopLoopRef.startState
    (by simpa [blockDescriptors] using safe)
    (Nat.le_of_lt scratchBound)
    initialTape represents

private theorem clauseFinishNonemptyBlock_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents clauseFinishNonemptyRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node clauseFinishNonemptyRef)
        (.node (restoreRef .emit .clausesNonempty .finish))
        steps initialTape finalTape ∧
      TapeRepresents
        (restoreRef .emit .clausesNonempty .finish).startState
        capacity (finishNonemptyClauseResult runtime).scratch
        (finishNonemptyClauseResult runtime).registers
        (finishNonemptyClauseResult runtime).checks source
        (finishNonemptyClauseResult runtime).targetTokens
        finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[23].primitives := by
  have safe :
      ProgramSafe capacity source context
        finishNonemptyClauseProgram runtime
        (finishNonemptyClauseResult runtime) :=
    finishNonemptyClause_safe
      (context := context) runtime fits scratchBound outputBound
  exact namedIndexedBlock_path_bounded 23 (by decide)
    clauseFinishNonemptyRef
    (.node (restoreRef .emit .clausesNonempty .finish))
    (by rfl) (by rfl)
    (restoreRef .emit .clausesNonempty .finish).startState
    (by simpa [blockDescriptors] using safe)
    (Nat.le_of_lt scratchBound)
    initialTape represents

private theorem clauseFinishEmptyBlock_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (gateBound : runtime.registers.currentGate < capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents clauseFinishEmptyRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node clauseFinishEmptyRef)
        (.node (restoreRef .emit .clausesNonempty .finish))
        steps initialTape finalTape ∧
      TapeRepresents
        (restoreRef .emit .clausesNonempty .finish).startState
        capacity (pushTotalGateResult runtime).scratch
        (pushTotalGateResult runtime).registers
        (pushTotalGateResult runtime).checks source
        (pushTotalGateResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[24].primitives := by
  have safe :
      ProgramSafe capacity source context finishEmptyClauseProgram
        runtime (pushTotalGateResult runtime) :=
    finishEmptyClause_safe
      (context := context) runtime fits scratchBound gateBound
  exact namedIndexedBlock_path_bounded 24 (by decide)
    clauseFinishEmptyRef
    (.node (restoreRef .emit .clausesNonempty .finish))
    (by rfl) (by rfl)
    (restoreRef .emit .clausesNonempty .finish).startState
    (by simpa [blockDescriptors] using safe)
    (Nat.le_of_lt scratchBound)
    initialTape represents

private theorem formulaSeedBlock_path
    (clauseSource : ClauseSource)
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents
        (match clauseSource with
          | .constantFalse => formulaSeedFalseRef
          | .gateScratch => formulaSeedGateRef).startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node
          (match clauseSource with
            | .constantFalse => formulaSeedFalseRef
            | .gateScratch => formulaSeedGateRef))
        (.node formulaPopLoopRef)
        steps initialTape finalTape ∧
      TapeRepresents formulaPopLoopRef.startState
        capacity (seedFormulaResult clauseSource runtime).scratch
        (seedFormulaResult clauseSource runtime).registers
        (seedFormulaResult clauseSource runtime).checks source
        (seedFormulaResult clauseSource runtime).targetTokens
        finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime
          (match clauseSource with
            | .constantFalse => blockDescriptors[26].primitives
            | .gateScratch => blockDescriptors[27].primitives) := by
  have safe :
      ProgramSafe capacity source context
        (seedFormulaProgram clauseSource) runtime
        (seedFormulaResult clauseSource runtime) :=
    seedFormula_safe layout clauseSource runtime fits
      scratchBound outputBound
  cases clauseSource with
  | constantFalse =>
      exact namedIndexedBlock_path_bounded 26 (by decide)
        formulaSeedFalseRef (.node formulaPopLoopRef)
        (by rfl) (by rfl) formulaPopLoopRef.startState
        (by simpa [blockDescriptors] using safe)
        (Nat.le_of_lt scratchBound)
        initialTape represents
  | gateScratch =>
      exact namedIndexedBlock_path_bounded 27 (by decide)
        formulaSeedGateRef (.node formulaPopLoopRef)
        (by rfl) (by rfl) formulaPopLoopRef.startState
        (by simpa [blockDescriptors] using safe)
        (Nat.le_of_lt scratchBound)
        initialTape represents

private theorem formulaExtendBlock_path
    (clauseSource : ClauseSource)
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex + 2 ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents
        (match clauseSource with
          | .constantFalse => formulaExtendFalseRef
          | .gateScratch => formulaExtendGateRef).startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node
          (match clauseSource with
            | .constantFalse => formulaExtendFalseRef
            | .gateScratch => formulaExtendGateRef))
        (.node formulaPopLoopRef)
        steps initialTape finalTape ∧
      TapeRepresents formulaPopLoopRef.startState
        capacity (extendFormulaResult clauseSource runtime).scratch
        (extendFormulaResult clauseSource runtime).registers
        (extendFormulaResult clauseSource runtime).checks source
        (extendFormulaResult clauseSource runtime).targetTokens
        finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime
          (match clauseSource with
            | .constantFalse => blockDescriptors[29].primitives
            | .gateScratch => blockDescriptors[30].primitives) := by
  have safe :
      ProgramSafe capacity source context
        (extendFormulaProgram clauseSource) runtime
        (extendFormulaResult clauseSource runtime) :=
    extendFormula_safe layout clauseSource runtime fits
      scratchBound outputBound
  cases clauseSource with
  | constantFalse =>
      exact namedIndexedBlock_path_bounded 29 (by decide)
        formulaExtendFalseRef (.node formulaPopLoopRef)
        (by rfl) (by rfl) formulaPopLoopRef.startState
        (by simpa [blockDescriptors] using safe)
        (Nat.le_of_lt scratchBound)
        initialTape represents
  | gateScratch =>
      exact namedIndexedBlock_path_bounded 30 (by decide)
        formulaExtendGateRef (.node formulaPopLoopRef)
        (by rfl) (by rfl) formulaPopLoopRef.startState
        (by simpa [blockDescriptors] using safe)
        (Nat.le_of_lt scratchBound)
        initialTape represents

private theorem formulaEmptyBlock_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents formulaEmptyRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node formulaEmptyRef)
        (.node suffixRef) steps initialTape finalTape ∧
      TapeRepresents suffixRef.startState
        capacity (emptyFormulaResult runtime).scratch
        (emptyFormulaResult runtime).registers
        (emptyFormulaResult runtime).checks source
        (emptyFormulaResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[31].primitives := by
  have safe :
      ProgramSafe capacity source context emitEmptyFormulaProgram
        runtime (emptyFormulaResult runtime) :=
    emptyFormula_safe layout runtime fits scratchBound
  exact namedIndexedBlock_path_bounded 31 (by decide)
    formulaEmptyRef (.node suffixRef)
    (by rfl) (by rfl) suffixRef.startState
    (by simpa [blockDescriptors] using safe)
    (Nat.le_of_lt scratchBound)
    initialTape represents

private theorem suffixBlock_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents suffixRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node suffixRef)
        (.node finalizerRef) steps initialTape finalTape ∧
      TapeRepresents finalizerRef.startState
        capacity (circuitSuffixResult runtime).scratch
        (circuitSuffixResult runtime).registers
        (circuitSuffixResult runtime).checks source
        (circuitSuffixResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[32].primitives := by
  have safe :
      ProgramSafe capacity source context emitCircuitSuffixProgram
        runtime (circuitSuffixResult runtime) :=
    suffix_safe layout runtime fits scratchBound outputBound
  exact namedIndexedBlock_path_bounded 32 (by decide)
    suffixRef (.node finalizerRef)
    (by rfl) (by rfl) finalizerRef.startState
    (by simpa [blockDescriptors] using safe)
    (Nat.le_of_lt scratchBound)
    initialTape represents

/-! ## Emit-pass header -/

def emitHeaderScanSteps (formula : CNFFormula) : Nat :=
  TargetEmitterNavigator.headerWorkSteps 0
      (CNFToNANDWorkspace.formulaTokens formula).length + 1

private theorem navigator_configAtWord_eq
    (state : Nat) (left word : List WorkSymbol) :
    { state := state, tape := focusTape left word } =
      TargetEmitterNavigator.configAtWord state left word := by
  cases word <;> rfl

private theorem focusTape_eq_targetEmitter_tape
    (state : Nat) (left word : List WorkSymbol) :
    focusTape left word =
      (TargetEmitter.configAtWord state left word).tape := by
  cases word <;> rfl

theorem emit_header_path
    (formula : CNFFormula) (runtime : Runtime)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (passHeaderRef .emit).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (canonicalSource formula) runtime.targetTokens initialTape) :
    ∃ first rest finalTape,
      CNFToNANDWorkspace.formulaTokens formula = first :: rest ∧
      AcceptPath graph (.node (passHeaderRef .emit))
        (.node (firstBitRef .emit .header))
        (emitHeaderScanSteps formula) initialTape finalTape ∧
      ScanRepresents (firstBitRef .emit .header).startState
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
            (.node (firstBitRef .emit .header))
            (.node (firstBitRef .emit .header)) 0
            canonicalMiddle canonicalMiddle := .terminal _ _
      have canonicalPath :=
        localAccept_path Address.emitHeader
          TargetEmitterNavigator.headerMachine
          (.node (firstBitRef .emit .header)) .reject
          (.node (firstBitRef .emit .header))
          (TargetEmitterNavigator.headerWorkSteps 0
            (first :: rest).length) 0
          canonicalInitial canonicalMiddle canonicalMiddle
          (by simpa [passHeaderNode] using
            passHeaderNode_member .emit)
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
      · simpa [emitHeaderScanSteps, tokensEq, passHeaderRef] using path
      · refine
          { state := by
              simp [TargetEmitter.configAtWord, carrierGateCells,
                carrierGateCellsFor]
            tape := ?_ }
        change
          WorkTape.BlankEquivalent finalTape
            (TargetEmitter.configAtWord
              (firstBitRef .emit .header).startState
              ((carrierHeaderCells (first :: rest)).reverse ++
                TargetEmitterRuntime.logicalLeftWorkspace
                  (CNFToNANDWorkspace.capacity formula)
                  runtime.scratch runtime.registers runtime.checks)
              ((carrierGateCells (first :: rest) ++ carrierFooterCells) ++
                TargetEmitter.sourceTargetBoundary ::
                  SourceParser.packedTokenCells
                    runtime.targetTokens)).tape
        rw [← focusTape_eq_targetEmitter_tape]
        simpa [canonicalMiddle, right, left,
          List.append_assoc] using finalEquivalent

private def emitWidthCost
    (formula : CNFFormula) : Nat → List CNFToken → Nat
  | 0, processed =>
      PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
          (CNFToNANDWorkspace.formulaTokens formula) processed .f +
        PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
          (CNFToNANDWorkspace.formulaTokens formula) processed .f
  | count + 1, processed =>
      PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
          (CNFToNANDWorkspace.formulaTokens formula) processed .t +
        PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
          (CNFToNANDWorkspace.formulaTokens formula) processed .t +
        emitWidthCost formula count (processed ++ [.t])

private theorem emit_width_path
    (formula : CNFFormula) (runtime : Runtime) :
    ∀ (count : Nat) (processed : List CNFToken)
      (next : CNFToken) (tail : List CNFToken),
      CNFToNANDWorkspace.formulaTokens formula =
          processed ++ encodeUnaryTokens count ++ next :: tail →
      ∀ initialTape,
      ScanRepresents (firstBitRef .emit .header).startState
          (CNFToNANDWorkspace.capacity formula)
          runtime.scratch runtime.registers runtime.checks
          (scanBeforeCells
            (CNFToNANDWorkspace.formulaTokens formula) processed)
          (carrierGateCells
              (encodeUnaryTokens count ++ next :: tail) ++
            carrierFooterCells)
          runtime.targetTokens initialTape →
      ∃ steps finalTape,
        AcceptPath graph (.node (firstBitRef .emit .header))
          (.node (firstBitRef .emit .clausesEmpty))
          steps initialTape finalTape ∧
        ScanRepresents
          (firstBitRef .emit .clausesEmpty).startState
          (CNFToNANDWorkspace.capacity formula)
          runtime.scratch runtime.registers runtime.checks
          (scanBeforeCells
            (CNFToNANDWorkspace.formulaTokens formula)
            (processed ++ encodeUnaryTokens count))
          (scanAfterCells next tail)
          runtime.targetTokens finalTape ∧
        steps ≤ emitWidthCost formula count processed := by
  intro count
  induction count with
  | zero =>
      intro processed next tail tokens initialTape represents
      have tokenRepresents :
          ScanRepresents (firstBitRef .emit .header).startState
            (CNFToNANDWorkspace.capacity formula)
            runtime.scratch runtime.registers runtime.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells .f (next :: tail))
            runtime.targetTokens initialTape := by
        simpa [encodeUnaryTokens,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
          carrierGateCells, List.append_assoc] using represents
      rcases
          PNP.Concrete.CNFToNANDControllerCountTrace.token_read_install_path
            .emit formula processed .f (next :: tail) .header runtime
            (by simpa [encodeUnaryTokens, List.append_assoc] using tokens)
            (by simp [activeGrammarStates])
            (by decide) initialTape tokenRepresents with
        ⟨installedTape, installPath, installedRepresents⟩
      have installedAtRestore :
          TapeRepresents (restoreRef .emit .clausesEmpty .f).startState
            (CNFToNANDWorkspace.capacity formula)
            runtime.scratch runtime.registers runtime.checks
            (markedSource
              (CNFToNANDWorkspace.formulaTokens formula)
              processed .f (next :: tail))
            runtime.targetTokens installedTape := by
        exact represents_at_state installedRepresents
      rcases
          PNP.Concrete.CNFToNANDControllerCountTrace.token_restore_advance_next_path
            .emit formula processed .f next tail .clausesEmpty runtime
            (by simpa [encodeUnaryTokens, List.append_assoc] using tokens)
            rfl installedTape installedAtRestore with
        ⟨finalTape, restorePath, finalRepresents⟩
      refine
        ⟨PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
              (CNFToNANDWorkspace.formulaTokens formula) processed .f +
            PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
              (CNFToNANDWorkspace.formulaTokens formula) processed .f,
          finalTape, ?_, ?_, ?_⟩
      · exact
          AcceptPath.trans graph
            (.node (firstBitRef .emit .header))
            (.node (restoreRef .emit .clausesEmpty .f))
            (.node (firstBitRef .emit .clausesEmpty))
            _ _ initialTape installedTape finalTape
            (by simpa [postInstallEndpoint] using installPath)
            restorePath
      · simpa [encodeUnaryTokens] using finalRepresents
      · simp [emitWidthCost]
  | succ count inductionHypothesis =>
      intro processed next tail tokens initialTape represents
      cases unaryEq : encodeUnaryTokens count with
      | nil =>
          cases count <;> simp [encodeUnaryTokens] at unaryEq
      | cons first rest =>
          have tokenRepresents :
              ScanRepresents (firstBitRef .emit .header).startState
                (CNFToNANDWorkspace.capacity formula)
                runtime.scratch runtime.registers runtime.checks
                (scanBeforeCells
                  (CNFToNANDWorkspace.formulaTokens formula) processed)
                (scanAfterCells .t (first :: rest ++ next :: tail))
                runtime.targetTokens initialTape := by
            simpa [encodeUnaryTokens, unaryEq,
              PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
              carrierGateCells, List.append_assoc] using represents
          have tokens' :
              CNFToNANDWorkspace.formulaTokens formula =
                processed ++
                  (.t :: first :: (rest ++ next :: tail)) := by
            simpa [encodeUnaryTokens, unaryEq,
              List.append_assoc] using tokens
          rcases
              PNP.Concrete.CNFToNANDControllerCountTrace.token_read_install_path
                .emit formula processed .t
                (first :: rest ++ next :: tail) .header runtime
                tokens'
                (by simp [activeGrammarStates])
                (by decide) initialTape tokenRepresents with
            ⟨installedTape, installPath, installedRepresents⟩
          have installedAtRestore :
              TapeRepresents (restoreRef .emit .header .t).startState
                (CNFToNANDWorkspace.capacity formula)
                runtime.scratch runtime.registers runtime.checks
                (markedSource
                  (CNFToNANDWorkspace.formulaTokens formula)
                  processed .t
                  (first :: rest ++ next :: tail))
                runtime.targetTokens installedTape := by
            exact represents_at_state installedRepresents
          rcases
              PNP.Concrete.CNFToNANDControllerCountTrace.token_restore_advance_next_path
                .emit formula processed .t first
                (rest ++ next :: tail) .header runtime
                tokens'
                rfl installedTape installedAtRestore with
            ⟨nextTape, restorePath, nextRepresents⟩
          have recursiveTokens :
              CNFToNANDWorkspace.formulaTokens formula =
                (processed ++ [.t]) ++
                  encodeUnaryTokens count ++ next :: tail := by
            simpa [unaryEq, List.append_assoc] using tokens'
          have recursiveRepresents :
              ScanRepresents (firstBitRef .emit .header).startState
                (CNFToNANDWorkspace.capacity formula)
                runtime.scratch runtime.registers runtime.checks
                (scanBeforeCells
                  (CNFToNANDWorkspace.formulaTokens formula)
                  (processed ++ [.t]))
                (carrierGateCells
                    (encodeUnaryTokens count ++ next :: tail) ++
                  carrierFooterCells)
                runtime.targetTokens nextTape := by
            simpa [unaryEq,
              PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
              carrierGateCells,
              List.append_assoc] using nextRepresents
          rcases inductionHypothesis
              (processed ++ [.t]) next tail recursiveTokens
              nextTape recursiveRepresents with
            ⟨tailSteps, finalTape, tailPath, finalRepresents,
              tailBound⟩
          let prefixSteps :=
            PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
                (CNFToNANDWorkspace.formulaTokens formula) processed .t +
              PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
                (CNFToNANDWorkspace.formulaTokens formula) processed .t
          have prefixPath :
              AcceptPath graph
                (.node (firstBitRef .emit .header))
                (.node (firstBitRef .emit .header))
                prefixSteps initialTape nextTape := by
            exact
              AcceptPath.trans graph
                (.node (firstBitRef .emit .header))
                (.node (restoreRef .emit .header .t))
                (.node (firstBitRef .emit .header))
                _ _ initialTape installedTape nextTape
                (by simpa [postInstallEndpoint] using installPath)
                restorePath
          refine ⟨prefixSteps + tailSteps, finalTape, ?_, ?_, ?_⟩
          · exact
              AcceptPath.trans graph
                (.node (firstBitRef .emit .header))
                (.node (firstBitRef .emit .header))
                (.node (firstBitRef .emit .clausesEmpty))
                prefixSteps tailSteps initialTape nextTape finalTape
                prefixPath tailPath
          · simpa [encodeUnaryTokens, List.append_assoc] using
              finalRepresents
          · simp [emitWidthCost, prefixSteps] at tailBound ⊢
            omega

/-! ## Token-wise emission paths -/

private def signToken (positive : Bool) : CNFToken :=
  if positive then .t else .f

private def emitSignRef (positive : Bool) : NodeRef :=
  if positive then emitPositiveSignRef else emitNegativeSignRef

private def signBlockPrimitives
    (positive : Bool) : List TargetEmitterPlan.Primitive :=
  if positive then blockDescriptors[11].primitives
  else blockDescriptors[10].primitives

private theorem emitSignBlock_path
    (positive : Bool)
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (runtime : Runtime) (scratchBound : runtime.scratch < capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (emitSignRef positive).startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (emitSignRef positive))
        (.node
          (literalCompareRef .emit .clause
            (signToken positive)))
        steps initialTape finalTape ∧
      TapeRepresents
        (literalCompareRef .emit .clause
          (signToken positive)).startState
        capacity (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks source
        (resetLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime (signBlockPrimitives positive) := by
  cases positive with
  | false =>
      simpa [emitSignRef, signToken, signBlockPrimitives] using
        (negativeSignBlock_path (context := context)
          runtime scratchBound initialTape
          (by simpa [emitSignRef] using represents))
  | true =>
      simpa [emitSignRef, signToken, signBlockPrimitives] using
        (positiveSignBlock_path (context := context)
          runtime scratchBound initialTape
          (by simpa [emitSignRef] using represents))

private def signPrefixCost
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime) : Nat :=
  PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed
      (signToken positive) +
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
      (CNFToNANDWorkspace.capacity formula)
      (PNP.Concrete.CNFToNANDControllerCountTrace.markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        processed (signToken positive) (next :: tail))
      runtime (signBlockPrimitives positive)

private theorem emit_sign_prefix_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ signToken positive :: next :: tail)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells (signToken positive) (next :: tail))
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .emit .clause))
        (.node
          (literalCompareRef .emit .clause
            (signToken positive)))
        steps initialTape finalTape ∧
      TapeRepresents
        (literalCompareRef .emit .clause
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed (signToken positive) (next :: tail))
        (resetLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        signPrefixCost formula positive processed next tail runtime := by
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_read_install_path
        .emit formula processed (signToken positive)
        (next :: tail) .clause runtime tokens
        (by simp [activeGrammarStates])
        (by cases positive <;> decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed (signToken positive) (next :: tail)
  let context :=
    markedSourceContext formula processed
      (signToken positive) (next :: tail) tokens
  have postInstallEq :
      postInstallEndpoint .emit .clause (signToken positive) =
        .node (emitSignRef positive) := by
    cases positive <;> rfl
  have blockInput :
      TapeRepresents (emitSignRef positive).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens installedTape :=
    represents_at_state installedRepresents
  rcases
      emitSignBlock_path positive (context := context)
        runtime scratchBound installedTape blockInput with
    ⟨blockSteps, finalTape, blockPath, finalRepresents,
      blockBound⟩
  let readSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed
      (signToken positive)
  refine
    ⟨readSteps + blockSteps, finalTape, ?_,
      by simpa [source] using finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        (by simpa [readSteps, postInstallEq] using installPath)
        blockPath
  · unfold signPrefixCost
    have blockBound' :
        blockSteps ≤
          TargetEmitterRuntimeProgramBound.programWorkEnvelope
            (CNFToNANDWorkspace.capacity formula)
            (PNP.Concrete.CNFToNANDControllerCountTrace.markedSource
              (CNFToNANDWorkspace.formulaTokens formula)
              processed (signToken positive) (next :: tail))
            runtime (signBlockPrimitives positive) := by
      simpa only [source, markedSource] using blockBound
    omega

private def signStepCost
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime) : Nat :=
  signPrefixCost formula positive processed next tail runtime +
    PNP.Concrete.CNFToNANDControllerCountTrace.literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) 0 +
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed
      (signToken positive)

private theorem emit_sign_less_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ signToken positive :: next :: tail)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (positiveWidth : 0 < runtime.registers.inputCount)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells (signToken positive) (next :: tail))
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .emit .clause))
        (.node (firstBitRef .emit (inRangeState positive)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [signToken positive]))
        (scanAfterCells next tail)
        (resetLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        signStepCost formula positive processed next tail runtime := by
  rcases
      emit_sign_prefix_path formula positive processed next tail
        runtime tokens scratchBound initialTape represents with
    ⟨prefixSteps, compareTape, prefixPath, compareRepresents,
      prefixBound⟩
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed (signToken positive) (next :: tail)
  let context :=
    markedSourceContext formula processed
      (signToken positive) (next :: tail) tokens
  let sourceTail := source.tail
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail :=
    context.source_eq
  have markedEq :
      markedSource (CNFToNANDWorkspace.formulaTokens formula)
          processed (signToken positive) (next :: tail) =
        SourceParser.cell00 :: sourceTail := by
    simpa only [source] using sourceEq
  have compareRepresents' :
      TapeRepresents
        (literalCompareRef .emit .clause
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks
        (SourceParser.cell00 :: sourceTail)
        (resetLiteralResult runtime).targetTokens compareTape := by
    rw [markedEq] at compareRepresents
    exact compareRepresents
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.literal_compare_less_path
        (Address.literalCompare .emit .clause
          (signToken positive))
        (.node
          (restoreRef .emit (overflowState positive)
            (signToken positive)))
        (.node
          (restoreRef .emit (inRangeState positive)
            (signToken positive)))
        (restoreRef .emit (inRangeState positive)
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks
        SourceParser.cell00 sourceTail
        (resetLiteralResult runtime).targetTokens compareTape
        (by simpa [signCompareNode, signToken,
            literalCompareRef, controlRef] using
          signCompareNode_member .emit positive)
        (by simpa [resetLiteralResult] using fits)
        (by simpa [resetLiteralResult,
            TargetEmitterLedger.slotValue] using positiveWidth)
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents' with
    ⟨restoreTape, comparePath, restoreRepresents'⟩
  have restoreRepresents :
      TapeRepresents
        (restoreRef .emit (inRangeState positive)
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks source
        (resetLiteralResult runtime).targetTokens restoreTape := by
    rw [sourceEq]
    exact restoreRepresents'
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_restore_advance_next_path
        .emit formula processed (signToken positive) next tail
        (inRangeState positive) (resetLiteralResult runtime)
        tokens (by cases positive <;> rfl)
        restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let compareSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) 0
  let restoreSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed
      (signToken positive)
  have comparePath' :
      AcceptPath graph
        (.node
          (literalCompareRef .emit .clause
            (signToken positive)))
        (.node
          (restoreRef .emit (inRangeState positive)
            (signToken positive)))
        compareSteps compareTape restoreTape := by
    simpa [compareSteps, resetLiteralResult,
      literalCompareRef] using comparePath
  have throughCompare :
      AcceptPath graph
        (.node (firstBitRef .emit .clause))
        (.node
          (restoreRef .emit (inRangeState positive)
            (signToken positive)))
        (prefixSteps + compareSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      prefixPath comparePath'
  refine
    ⟨prefixSteps + compareSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughCompare restorePath
  · unfold signStepCost
    omega

private theorem emit_sign_equal_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ signToken positive :: next :: tail)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (zeroWidth : runtime.registers.inputCount = 0)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells (signToken positive) (next :: tail))
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .emit .clause))
        (.node (firstBitRef .emit (overflowState positive)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit (overflowState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [signToken positive]))
        (scanAfterCells next tail)
        (resetLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        signStepCost formula positive processed next tail runtime := by
  rcases
      emit_sign_prefix_path formula positive processed next tail
        runtime tokens scratchBound initialTape represents with
    ⟨prefixSteps, compareTape, prefixPath, compareRepresents,
      prefixBound⟩
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed (signToken positive) (next :: tail)
  let context :=
    markedSourceContext formula processed
      (signToken positive) (next :: tail) tokens
  let sourceTail := source.tail
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail :=
    context.source_eq
  have markedEq :
      markedSource (CNFToNANDWorkspace.formulaTokens formula)
          processed (signToken positive) (next :: tail) =
        SourceParser.cell00 :: sourceTail := by
    simpa only [source] using sourceEq
  have compareRepresents' :
      TapeRepresents
        (literalCompareRef .emit .clause
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks
        (SourceParser.cell00 :: sourceTail)
        (resetLiteralResult runtime).targetTokens compareTape := by
    rw [markedEq] at compareRepresents
    exact compareRepresents
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.literal_compare_equal_path
        (Address.literalCompare .emit .clause
          (signToken positive))
        (.node
          (restoreRef .emit (overflowState positive)
            (signToken positive)))
        (.node
          (restoreRef .emit (inRangeState positive)
            (signToken positive)))
        (restoreRef .emit (overflowState positive)
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks
        SourceParser.cell00 sourceTail
        (resetLiteralResult runtime).targetTokens compareTape
        (by simpa [signCompareNode, signToken,
            literalCompareRef, controlRef] using
          signCompareNode_member .emit positive)
        (by simpa [resetLiteralResult] using fits)
        (by
          simp [resetLiteralResult,
            TargetEmitterLedger.slotValue, zeroWidth])
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents' with
    ⟨restoreTape, comparePath, restoreRepresents'⟩
  have restoreRepresents :
      TapeRepresents
        (restoreRef .emit (overflowState positive)
          (signToken positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks source
        (resetLiteralResult runtime).targetTokens restoreTape := by
    rw [sourceEq]
    exact restoreRepresents'
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_restore_advance_next_path
        .emit formula processed (signToken positive) next tail
        (overflowState positive) (resetLiteralResult runtime)
        tokens (by cases positive <;> rfl)
        restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let compareSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) 0
  let restoreSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed
      (signToken positive)
  have comparePath' :
      AcceptPath graph
        (.node
          (literalCompareRef .emit .clause
            (signToken positive)))
        (.node
          (restoreRef .emit (overflowState positive)
            (signToken positive)))
        compareSteps compareTape restoreTape := by
    simpa [compareSteps, resetLiteralResult,
      literalCompareRef] using comparePath
  have throughCompare :
      AcceptPath graph
        (.node (firstBitRef .emit .clause))
        (.node
          (restoreRef .emit (overflowState positive)
            (signToken positive)))
        (prefixSteps + compareSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      prefixPath comparePath'
  refine
    ⟨prefixSteps + compareSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughCompare restorePath
  · unfold signStepCost
    omega

private def inRangeTStepCost
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime) : Nat :=
  PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t +
    PNP.Concrete.CNFToNANDControllerCountTrace.literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) runtime.scratch +
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
      (CNFToNANDWorkspace.capacity formula)
      (PNP.Concrete.CNFToNANDControllerCountTrace.markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        processed .t (next :: tail))
      runtime
      (if positive then blockDescriptors[15].primitives
        else blockDescriptors[16].primitives) +
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t

private theorem emit_inRange_t_step_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .t :: next :: tail)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (less :
      runtime.scratch < runtime.registers.inputCount)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (firstBitRef .emit (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .t (next :: tail))
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node (firstBitRef .emit (inRangeState positive)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        (advanceLiteralResult runtime).scratch
        (advanceLiteralResult runtime).registers
        (advanceLiteralResult runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.t]))
        (scanAfterCells next tail)
        (advanceLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        inRangeTStepCost formula positive processed next tail runtime := by
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed .t (next :: tail)
  let context :=
    markedSourceContext formula processed .t (next :: tail) tokens
  let sourceTail := source.tail
  have postInstallEq :
      postInstallEndpoint .emit (inRangeState positive) .t =
        .node
          (literalCompareRef .emit
            (inRangeState positive) .t) := by
    cases positive <;> rfl
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_read_install_path
        .emit formula processed .t (next :: tail)
        (inRangeState positive) runtime tokens
        (by cases positive <;> simp [inRangeState,
          activeGrammarStates])
        (by cases positive <;> decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have compareRepresents :
      TapeRepresents
        (literalCompareRef .emit
          (inRangeState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens installedTape := by
    exact represents_at_state installedRepresents
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail := by
    exact context.source_eq
  have compareRepresents' :
      TapeRepresents
        (literalCompareRef .emit
          (inRangeState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (SourceParser.cell00 :: sourceTail)
        runtime.targetTokens installedTape := by
    rw [sourceEq] at compareRepresents
    exact compareRepresents
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.literal_compare_less_path
        (Address.literalCompare .emit
          (inRangeState positive) .t)
        (.node
          (restoreRef .emit (overflowState positive) .t))
        (.node (advanceLiteralRef .emit positive))
        (advanceLiteralRef .emit positive).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        SourceParser.cell00 sourceTail runtime.targetTokens
        installedTape
        (by simpa [literalUnitCompareNode,
            literalCompareRef, controlRef] using
          literalUnitCompareNode_member .emit positive)
        fits less
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents' with
    ⟨advanceTape, comparePath, advanceRepresents'⟩
  have advanceRepresents :
      TapeRepresents (advanceLiteralRef .emit positive).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens advanceTape := by
    rw [sourceEq]
    exact advanceRepresents'
  have scratchCapacity :
      runtime.scratch <
        CNFToNANDWorkspace.capacity formula :=
    Nat.lt_of_lt_of_le less fits.inputCount
  rcases
      advanceLiteralBlock_path positive (context := context)
        runtime scratchCapacity advanceTape advanceRepresents with
    ⟨advanceSteps, restoreTape, advancePath, restoreRepresents,
      advanceBound⟩
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_restore_advance_next_path
        .emit formula processed .t next tail
        (inRangeState positive) (advanceLiteralResult runtime)
        tokens
        (by cases positive <;> rfl)
        restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t
  let compareSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) runtime.scratch
  let restoreSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t
  have installPath' :
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node
          (literalCompareRef .emit
            (inRangeState positive) .t))
        installSteps initialTape installedTape := by
    simpa [installSteps, postInstallEq] using installPath
  have throughCompare :
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node (advanceLiteralRef .emit positive))
        (installSteps + compareSteps)
        initialTape advanceTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      installPath' comparePath
  have throughAdvance :
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node
          (restoreRef .emit (inRangeState positive) .t))
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
  · unfold inRangeTStepCost
    have advanceBound' :
        advanceSteps ≤
          TargetEmitterRuntimeProgramBound.programWorkEnvelope
            (CNFToNANDWorkspace.capacity formula)
            (PNP.Concrete.CNFToNANDControllerCountTrace.markedSource
              (CNFToNANDWorkspace.formulaTokens formula)
              processed .t (next :: tail))
            runtime
            (if positive then blockDescriptors[15].primitives
              else blockDescriptors[16].primitives) := by
      simpa only [markedSource] using advanceBound
    omega

private theorem replicate_succ_append
    {α : Type} (count : Nat) (item : α) :
    List.replicate (count + 1) item =
      item :: List.replicate count item := by
  simp [List.replicate_succ]

private def advanceLiteralRun :
    Nat → Runtime → Runtime
  | 0, runtime => runtime
  | count + 1, runtime =>
      advanceLiteralRun count (advanceLiteralResult runtime)

private def inRangeTRunCost
    (formula : CNFFormula) (positive : Bool) :
    Nat → List CNFToken → List CNFToken → Runtime → Nat
  | 0, _, _, _ => 0
  | count + 1, processed, suffix, runtime =>
      let remainder :=
        List.replicate count CNFToken.t ++ suffix
      match remainder with
      | [] => 0
      | next :: tail =>
          inRangeTStepCost formula positive processed
              next tail runtime +
            inRangeTRunCost formula positive count
              (processed ++ [.t]) suffix
              (advanceLiteralResult runtime)

private theorem emit_inRange_t_run_path
    (formula : CNFFormula) (positive : Bool) :
    ∀ (count : Nat) (processed suffix : List CNFToken)
      (runtime : Runtime),
      CNFToNANDWorkspace.formulaTokens formula =
          processed ++ List.replicate count .t ++ suffix →
      suffix ≠ [] →
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers →
      runtime.scratch + count ≤ runtime.registers.inputCount →
      ∀ initialTape,
      ScanRepresents
        (firstBitRef .emit (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (List.replicate count .t ++ suffix) ++
          carrierFooterCells)
        runtime.targetTokens initialTape →
      ∃ steps finalTape,
        AcceptPath graph
          (.node (firstBitRef .emit (inRangeState positive)))
          (.node (firstBitRef .emit (inRangeState positive)))
          steps initialTape finalTape ∧
        ScanRepresents
          (firstBitRef .emit (inRangeState positive)).startState
          (CNFToNANDWorkspace.capacity formula)
          (advanceLiteralRun count runtime).scratch
          (advanceLiteralRun count runtime).registers
          (advanceLiteralRun count runtime).checks
          (scanBeforeCells
            (CNFToNANDWorkspace.formulaTokens formula)
            (processed ++ List.replicate count .t))
          (carrierGateCells suffix ++ carrierFooterCells)
          (advanceLiteralRun count runtime).targetTokens finalTape ∧
        steps ≤
          inRangeTRunCost formula positive count processed
            suffix runtime := by
  intro count
  induction count with
  | zero =>
      intro processed suffix runtime tokens suffixNonempty fits
        scratchBound initialTape represents
      exact
        ⟨0, initialTape, .terminal _ _,
          by simpa [advanceLiteralRun] using represents,
          by simp [inRangeTRunCost]⟩
  | succ count inductionHypothesis =>
      intro processed suffix runtime tokens suffixNonempty fits
        scratchBound initialTape represents
      let remainder :=
        List.replicate count CNFToken.t ++ suffix
      have remainderNonempty : remainder ≠ [] := by
        intro empty
        have : suffix = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro item member
          have appended :
              item ∈ List.replicate count CNFToken.t ++ suffix :=
            List.mem_append_right _ member
          simpa [remainder, empty] using appended
        exact suffixNonempty this
      cases remainderEq : remainder with
      | nil =>
          exact False.elim (remainderNonempty remainderEq)
      | cons next tail =>
          have stepTokens :
              CNFToNANDWorkspace.formulaTokens formula =
                processed ++ .t :: next :: tail := by
            simpa [List.replicate_succ, remainder, remainderEq,
              List.append_assoc] using tokens
          have stepRepresents :
              ScanRepresents
                (firstBitRef .emit
                  (inRangeState positive)).startState
                (CNFToNANDWorkspace.capacity formula)
                runtime.scratch runtime.registers runtime.checks
                (scanBeforeCells
                  (CNFToNANDWorkspace.formulaTokens formula)
                  processed)
                (scanAfterCells .t (next :: tail))
                runtime.targetTokens initialTape := by
            simpa [List.replicate_succ, remainder, remainderEq,
              PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
              carrierGateCells, List.append_assoc] using represents
          have less :
              runtime.scratch < runtime.registers.inputCount := by
            omega
          rcases
              emit_inRange_t_step_path formula positive processed
                next tail runtime stepTokens fits less
                initialTape stepRepresents with
            ⟨stepSteps, nextTape, stepPath, nextRepresents,
              stepBound⟩
          have recursiveTokens :
              CNFToNANDWorkspace.formulaTokens formula =
                (processed ++ [.t]) ++
                  List.replicate count .t ++ suffix := by
            simpa [List.replicate_succ, List.append_assoc] using
              tokens
          have recursiveRepresents :
              ScanRepresents
                (firstBitRef .emit
                  (inRangeState positive)).startState
                (CNFToNANDWorkspace.capacity formula)
                (advanceLiteralResult runtime).scratch
                (advanceLiteralResult runtime).registers
                (advanceLiteralResult runtime).checks
                (scanBeforeCells
                  (CNFToNANDWorkspace.formulaTokens formula)
                  (processed ++ [.t]))
                (carrierGateCells
                    (List.replicate count .t ++ suffix) ++
                  carrierFooterCells)
                (advanceLiteralResult runtime).targetTokens
                nextTape := by
            simpa [remainder, remainderEq,
              PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
              carrierGateCells, List.append_assoc] using
              nextRepresents
          have recursiveFits :
              LedgerFits (CNFToNANDWorkspace.capacity formula)
                (advanceLiteralResult runtime).registers := by
            simpa [advanceLiteralResult] using fits
          have recursiveBound :
              (advanceLiteralResult runtime).scratch + count ≤
                (advanceLiteralResult runtime).registers.inputCount := by
            simp [advanceLiteralResult] at scratchBound ⊢
            omega
          rcases
              inductionHypothesis
                (processed ++ [.t]) suffix
                (advanceLiteralResult runtime)
                recursiveTokens suffixNonempty recursiveFits
                recursiveBound nextTape recursiveRepresents with
            ⟨tailSteps, finalTape, tailPath, finalRepresents,
              tailBound⟩
          refine
            ⟨stepSteps + tailSteps, finalTape, ?_, ?_, ?_⟩
          · exact
              AcceptPath.trans graph _ _ _ _ _ _ _ _
                stepPath tailPath
          · simpa [advanceLiteralRun, List.replicate_succ,
              List.append_assoc] using finalRepresents
          · simp only [inRangeTRunCost]
            rw [show
              List.replicate count CNFToken.t ++ suffix =
                next :: tail by
              exact remainderEq]
            exact Nat.add_le_add stepBound tailBound

private def equalTStepCost
    (formula : CNFFormula) (processed : List CNFToken)
    (runtime : Runtime) : Nat :=
  PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t +
    PNP.Concrete.CNFToNANDControllerCountTrace.literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) runtime.scratch +
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t

private theorem emit_equal_t_step_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .t :: next :: tail)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (equal :
      runtime.scratch = runtime.registers.inputCount)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (firstBitRef .emit (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .t (next :: tail))
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node (firstBitRef .emit (overflowState positive)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit (overflowState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.t]))
        (scanAfterCells next tail)
        runtime.targetTokens finalTape ∧
      steps ≤ equalTStepCost formula processed runtime := by
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed .t (next :: tail)
  let context :=
    markedSourceContext formula processed .t (next :: tail) tokens
  let sourceTail := source.tail
  have postInstallEq :
      postInstallEndpoint .emit (inRangeState positive) .t =
        .node
          (literalCompareRef .emit
            (inRangeState positive) .t) := by
    cases positive <;> rfl
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_read_install_path
        .emit formula processed .t (next :: tail)
        (inRangeState positive) runtime tokens
        (by cases positive <;> simp [inRangeState,
          activeGrammarStates])
        (by cases positive <;> decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail :=
    context.source_eq
  have compareRepresents :
      TapeRepresents
        (literalCompareRef .emit
          (inRangeState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (SourceParser.cell00 :: sourceTail)
        runtime.targetTokens installedTape := by
    have atState :
        TapeRepresents
          (literalCompareRef .emit
            (inRangeState positive) .t).startState
          (CNFToNANDWorkspace.capacity formula)
          runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens installedTape :=
      represents_at_state installedRepresents
    rw [sourceEq] at atState
    exact atState
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.literal_compare_equal_path
        (Address.literalCompare .emit
          (inRangeState positive) .t)
        (.node
          (restoreRef .emit (overflowState positive) .t))
        (.node (advanceLiteralRef .emit positive))
        (restoreRef .emit (overflowState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        SourceParser.cell00 sourceTail runtime.targetTokens
        installedTape
        (by simpa [literalUnitCompareNode,
            literalCompareRef, controlRef] using
          literalUnitCompareNode_member .emit positive)
        fits equal
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents with
    ⟨restoreTape, comparePath, restoreRepresents'⟩
  have restoreRepresents :
      TapeRepresents
        (restoreRef .emit (overflowState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens restoreTape := by
    rw [sourceEq]
    exact restoreRepresents'
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_restore_advance_next_path
        .emit formula processed .t next tail
        (overflowState positive) runtime tokens
        (by cases positive <;> rfl)
        restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t
  let compareSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) runtime.scratch
  let restoreSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t
  have installPath' :
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node
          (literalCompareRef .emit
            (inRangeState positive) .t))
        installSteps initialTape installedTape := by
    simpa [installSteps, postInstallEq] using installPath
  have throughCompare :
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node
          (restoreRef .emit (overflowState positive) .t))
        (installSteps + compareSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      installPath' comparePath
  refine
    ⟨installSteps + compareSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughCompare restorePath
  · simp [equalTStepCost, installSteps, compareSteps, restoreSteps]

private def overflowTStepCost
    (formula : CNFFormula) (processed : List CNFToken) : Nat :=
  PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t +
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t

private theorem emit_overflow_t_step_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .t :: next :: tail)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (firstBitRef .emit (overflowState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .t (next :: tail))
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .emit (overflowState positive)))
        (.node (firstBitRef .emit (overflowState positive)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit (overflowState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.t]))
        (scanAfterCells next tail)
        runtime.targetTokens finalTape ∧
      steps ≤ overflowTStepCost formula processed := by
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_read_install_path
        .emit formula processed .t (next :: tail)
        (overflowState positive) runtime tokens
        (by cases positive <;> simp [overflowState,
          activeGrammarStates])
        (by cases positive <;> decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have postInstallEq :
      postInstallEndpoint .emit (overflowState positive) .t =
        .node
          (restoreRef .emit (overflowState positive) .t) := by
    cases positive <;> rfl
  have restoreRepresents :
      TapeRepresents
        (restoreRef .emit (overflowState positive) .t).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .t (next :: tail))
        runtime.targetTokens installedTape :=
    represents_at_state installedRepresents
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_restore_advance_next_path
        .emit formula processed .t next tail
        (overflowState positive) runtime tokens
        (by cases positive <;> rfl)
        installedTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t
  let restoreSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .t
  refine
    ⟨installSteps + restoreSteps, finalTape, ?_,
      finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        (by simpa [installSteps, postInstallEq] using installPath)
        restorePath
  · simp [overflowTStepCost, installSteps, restoreSteps]

private def overflowTRunCost
    (formula : CNFFormula) :
    Nat → List CNFToken → List CNFToken → Nat
  | 0, _, _ => 0
  | count + 1, processed, suffix =>
      let remainder :=
        List.replicate count CNFToken.t ++ suffix
      match remainder with
      | [] => 0
      | next :: tail =>
          overflowTStepCost formula processed +
            overflowTRunCost formula count
              (processed ++ [.t]) suffix

private theorem emit_overflow_t_run_path
    (formula : CNFFormula) (positive : Bool) :
    ∀ (count : Nat) (processed suffix : List CNFToken)
      (runtime : Runtime),
      CNFToNANDWorkspace.formulaTokens formula =
          processed ++ List.replicate count .t ++ suffix →
      suffix ≠ [] →
      ∀ initialTape,
      ScanRepresents
        (firstBitRef .emit (overflowState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (List.replicate count .t ++ suffix) ++
          carrierFooterCells)
        runtime.targetTokens initialTape →
      ∃ steps finalTape,
        AcceptPath graph
          (.node (firstBitRef .emit (overflowState positive)))
          (.node (firstBitRef .emit (overflowState positive)))
          steps initialTape finalTape ∧
        ScanRepresents
          (firstBitRef .emit (overflowState positive)).startState
          (CNFToNANDWorkspace.capacity formula)
          runtime.scratch runtime.registers runtime.checks
          (scanBeforeCells
            (CNFToNANDWorkspace.formulaTokens formula)
            (processed ++ List.replicate count .t))
          (carrierGateCells suffix ++ carrierFooterCells)
          runtime.targetTokens finalTape ∧
        steps ≤
          overflowTRunCost formula count processed suffix := by
  intro count
  induction count with
  | zero =>
      intro processed suffix runtime tokens suffixNonempty
        initialTape represents
      exact
        ⟨0, initialTape, .terminal _ _,
          by simpa using represents,
          by simp [overflowTRunCost]⟩
  | succ count inductionHypothesis =>
      intro processed suffix runtime tokens suffixNonempty
        initialTape represents
      let remainder :=
        List.replicate count CNFToken.t ++ suffix
      have remainderNonempty : remainder ≠ [] := by
        exact
          List.append_ne_nil_of_right_ne_nil
            (List.replicate count CNFToken.t) suffixNonempty
      cases remainderEq : remainder with
      | nil =>
          exact False.elim (remainderNonempty remainderEq)
      | cons next tail =>
          have stepTokens :
              CNFToNANDWorkspace.formulaTokens formula =
                processed ++ .t :: next :: tail := by
            simpa [List.replicate_succ, remainder, remainderEq,
              List.append_assoc] using tokens
          have stepRepresents :
              ScanRepresents
                (firstBitRef .emit
                  (overflowState positive)).startState
                (CNFToNANDWorkspace.capacity formula)
                runtime.scratch runtime.registers runtime.checks
                (scanBeforeCells
                  (CNFToNANDWorkspace.formulaTokens formula)
                  processed)
                (scanAfterCells .t (next :: tail))
                runtime.targetTokens initialTape := by
            simpa [List.replicate_succ, remainder, remainderEq,
              PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
              carrierGateCells, List.append_assoc] using represents
          rcases
              emit_overflow_t_step_path formula positive processed
                next tail runtime stepTokens
                initialTape stepRepresents with
            ⟨stepSteps, nextTape, stepPath, nextRepresents,
              stepBound⟩
          have recursiveTokens :
              CNFToNANDWorkspace.formulaTokens formula =
                (processed ++ [.t]) ++
                  List.replicate count .t ++ suffix := by
            simpa [List.replicate_succ, List.append_assoc] using
              tokens
          have recursiveRepresents :
              ScanRepresents
                (firstBitRef .emit
                  (overflowState positive)).startState
                (CNFToNANDWorkspace.capacity formula)
                runtime.scratch runtime.registers runtime.checks
                (scanBeforeCells
                  (CNFToNANDWorkspace.formulaTokens formula)
                  (processed ++ [.t]))
                (carrierGateCells
                    (List.replicate count .t ++ suffix) ++
                  carrierFooterCells)
                runtime.targetTokens nextTape := by
            simpa [remainder, remainderEq,
              PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
              carrierGateCells, List.append_assoc] using
              nextRepresents
          rcases
              inductionHypothesis
                (processed ++ [.t]) suffix runtime
                recursiveTokens suffixNonempty
                nextTape recursiveRepresents with
            ⟨tailSteps, finalTape, tailPath, finalRepresents,
              tailBound⟩
          refine
            ⟨stepSteps + tailSteps, finalTape, ?_, ?_, ?_⟩
          · exact
              AcceptPath.trans graph _ _ _ _ _ _ _ _
                stepPath tailPath
          · simpa [List.replicate_succ,
              List.append_assoc] using finalRepresents
          · simp only [overflowTRunCost]
            rw [show
              List.replicate count CNFToken.t ++ suffix =
                next :: tail by
              exact remainderEq]
            exact Nat.add_le_add stepBound tailBound

private def validLiteralRef (positive : Bool) : NodeRef :=
  if positive then emitPositiveLiteralRef else emitNegativeLiteralRef

private def validLiteralResult
    (positive : Bool) (runtime : Runtime) : Runtime :=
  if positive then positiveLiteralResult runtime
  else negativeLiteralResult runtime

private def validLiteralPrimitives
    (positive : Bool) : List TargetEmitterPlan.Primitive :=
  if positive then blockDescriptors[12].primitives
  else blockDescriptors[13].primitives

private def validLiteralOutputGrowth (positive : Bool) : Nat :=
  if positive then 1 else 2

private theorem emitValidLiteralBlock_path
    (positive : Bool)
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputBound :
      runtime.registers.outputIndex +
          validLiteralOutputGrowth positive ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (validLiteralRef positive).startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (validLiteralRef positive))
        (.node (restoreRef .emit .clause .f))
        steps initialTape finalTape ∧
      TapeRepresents (restoreRef .emit .clause .f).startState
        capacity (validLiteralResult positive runtime).scratch
        (validLiteralResult positive runtime).registers
        (validLiteralResult positive runtime).checks source
        (validLiteralResult positive runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime
          (validLiteralPrimitives positive) := by
  cases positive with
  | false =>
      simpa [validLiteralRef, validLiteralResult,
        validLiteralPrimitives, validLiteralOutputGrowth] using
        (negativeLiteralBlock_path (context := context)
          layout runtime fits scratchBound outputBound
          initialTape
          (by simpa [validLiteralRef] using represents))
  | true =>
      simpa [validLiteralRef, validLiteralResult,
        validLiteralPrimitives, validLiteralOutputGrowth] using
        (positiveLiteralBlock_path (context := context)
          layout runtime fits scratchBound outputBound
          initialTape
          (by simpa [validLiteralRef] using represents))

private theorem emitLiteralTerminatorNode_member
    (positive : Bool) :
    controlNode
        (Address.literalCompare .emit
          (inRangeState positive) .f)
        (TargetEmitterScratchCompareSlot.machineFor .inputCount)
        (.node emitInvalidLiteralRef)
        (.node (validLiteralRef positive)) ∈ graph.nodes := by
  cases positive with
  | false =>
      exact literalTerminatorCompareNode_member .emit false
  | true =>
      exact literalTerminatorCompareNode_member .emit true

private def validTerminatorCost
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (runtime : Runtime)
    (source : List WorkSymbol) : Nat :=
  PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f +
    PNP.Concrete.CNFToNANDControllerCountTrace.literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) runtime.scratch +
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
      (CNFToNANDWorkspace.capacity formula) source runtime
      (validLiteralPrimitives positive) +
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f

private theorem emit_valid_terminator_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .f :: next :: tail)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (less :
      runtime.scratch < runtime.registers.inputCount)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (outputBound :
      runtime.registers.outputIndex +
          validLiteralOutputGrowth positive ≤
        CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (firstBitRef .emit (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .f (next :: tail))
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node (firstBitRef .emit .clause))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        (validLiteralResult positive runtime).scratch
        (validLiteralResult positive runtime).registers
        (validLiteralResult positive runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.f]))
        (scanAfterCells next tail)
        (validLiteralResult positive runtime).targetTokens
        finalTape ∧
      steps ≤
        validTerminatorCost formula positive processed runtime
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed .f (next :: tail)) := by
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed .f (next :: tail)
  let context :=
    markedSourceContext formula processed .f (next :: tail) tokens
  let layout :=
    markedCursorLayout formula processed .f (next :: tail) tokens
  let sourceTail := source.tail
  have postInstallEq :
      postInstallEndpoint .emit (inRangeState positive) .f =
        .node
          (literalCompareRef .emit
            (inRangeState positive) .f) := by
    cases positive <;> rfl
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_read_install_path
        .emit formula processed .f (next :: tail)
        (inRangeState positive) runtime tokens
        (by cases positive <;> simp [inRangeState,
          activeGrammarStates])
        (by cases positive <;> decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail :=
    context.source_eq
  have compareRepresents :
      TapeRepresents
        (literalCompareRef .emit
          (inRangeState positive) .f).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (SourceParser.cell00 :: sourceTail)
        runtime.targetTokens installedTape := by
    have atState :
        TapeRepresents
          (literalCompareRef .emit
            (inRangeState positive) .f).startState
          (CNFToNANDWorkspace.capacity formula)
          runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens installedTape :=
      represents_at_state installedRepresents
    rw [sourceEq] at atState
    exact atState
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.literal_compare_less_path
        (Address.literalCompare .emit
          (inRangeState positive) .f)
        (.node emitInvalidLiteralRef)
        (.node (validLiteralRef positive))
        (validLiteralRef positive).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        SourceParser.cell00 sourceTail runtime.targetTokens
        installedTape
        (by simpa [literalCompareRef, controlRef] using
          emitLiteralTerminatorNode_member positive)
        fits less
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents with
    ⟨blockInputTape, comparePath, blockRepresents'⟩
  have blockRepresents :
      TapeRepresents (validLiteralRef positive).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens blockInputTape := by
    rw [sourceEq]
    exact blockRepresents'
  rcases
      emitValidLiteralBlock_path positive
        (context := context) layout runtime fits scratchBound
        outputBound blockInputTape blockRepresents with
    ⟨blockSteps, restoreTape, blockPath, restoreRepresents,
      blockBound⟩
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_restore_advance_next_path
        .emit formula processed .f next tail .clause
        (validLiteralResult positive runtime) tokens
        (by decide)
        restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f
  let compareSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) runtime.scratch
  let restoreSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f
  have throughCompare :
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node (validLiteralRef positive))
        (installSteps + compareSteps)
        initialTape blockInputTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      (by
        simpa [installSteps, postInstallEq,
          literalCompareRef] using installPath)
      comparePath
  have throughBlock :
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node (restoreRef .emit .clause .f))
        (installSteps + compareSteps + blockSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      throughCompare blockPath
  refine
    ⟨installSteps + compareSteps + blockSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughBlock restorePath
  · unfold validTerminatorCost
    have blockBound' :
        blockSteps ≤
          TargetEmitterRuntimeProgramBound.programWorkEnvelope
            (CNFToNANDWorkspace.capacity formula)
            (markedSource
              (CNFToNANDWorkspace.formulaTokens formula)
              processed .f (next :: tail))
            runtime (validLiteralPrimitives positive) := by
      simpa [source] using blockBound
    dsimp [installSteps, compareSteps, restoreSteps, source]
    omega

private def invalidEqualTerminatorCost
    (formula : CNFFormula) (processed : List CNFToken)
    (runtime : Runtime) (source : List WorkSymbol) : Nat :=
  PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f +
    PNP.Concrete.CNFToNANDControllerCountTrace.literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) runtime.scratch +
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
      (CNFToNANDWorkspace.capacity formula) source runtime
      blockDescriptors[14].primitives +
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f

private theorem emit_invalid_equal_terminator_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .f :: next :: tail)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (equal :
      runtime.scratch = runtime.registers.inputCount)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤
        CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (firstBitRef .emit (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .f (next :: tail))
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node (firstBitRef .emit .clause))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        (invalidLiteralResult runtime).scratch
        (invalidLiteralResult runtime).registers
        (invalidLiteralResult runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.f]))
        (scanAfterCells next tail)
        (invalidLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        invalidEqualTerminatorCost formula processed runtime
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed .f (next :: tail)) := by
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed .f (next :: tail)
  let context :=
    markedSourceContext formula processed .f (next :: tail) tokens
  let layout :=
    markedCursorLayout formula processed .f (next :: tail) tokens
  let sourceTail := source.tail
  have postInstallEq :
      postInstallEndpoint .emit (inRangeState positive) .f =
        .node
          (literalCompareRef .emit
            (inRangeState positive) .f) := by
    cases positive <;> rfl
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_read_install_path
        .emit formula processed .f (next :: tail)
        (inRangeState positive) runtime tokens
        (by cases positive <;> simp [inRangeState,
          activeGrammarStates])
        (by cases positive <;> decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have sourceEq :
      source = SourceParser.cell00 :: sourceTail :=
    context.source_eq
  have compareRepresents :
      TapeRepresents
        (literalCompareRef .emit
          (inRangeState positive) .f).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (SourceParser.cell00 :: sourceTail)
        runtime.targetTokens installedTape := by
    have atState :
        TapeRepresents
          (literalCompareRef .emit
            (inRangeState positive) .f).startState
          (CNFToNANDWorkspace.capacity formula)
          runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens installedTape :=
      represents_at_state installedRepresents
    rw [sourceEq] at atState
    exact atState
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.literal_compare_equal_path
        (Address.literalCompare .emit
          (inRangeState positive) .f)
        (.node emitInvalidLiteralRef)
        (.node (validLiteralRef positive))
        emitInvalidLiteralRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        SourceParser.cell00 sourceTail runtime.targetTokens
        installedTape
        (by simpa [literalCompareRef, controlRef] using
          emitLiteralTerminatorNode_member positive)
        fits equal
        (Or.inl TargetEmitter.PackedSymbol.zeroZero)
        compareRepresents with
    ⟨blockInputTape, comparePath, blockRepresents'⟩
  have blockRepresents :
      TapeRepresents emitInvalidLiteralRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens blockInputTape := by
    rw [sourceEq]
    exact blockRepresents'
  rcases
      invalidLiteralBlock_path (context := context)
        layout runtime fits scratchBound outputBound
        blockInputTape blockRepresents with
    ⟨blockSteps, restoreTape, blockPath, restoreRepresents,
      blockBound⟩
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_restore_advance_next_path
        .emit formula processed .f next tail .clause
        (invalidLiteralResult runtime) tokens (by decide)
        restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f
  let compareSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.literalCompareSteps
      (CNFToNANDWorkspace.capacity formula) runtime.scratch
  let restoreSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f
  have throughCompare :
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node emitInvalidLiteralRef)
        (installSteps + compareSteps)
        initialTape blockInputTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      (by
        simpa [installSteps, postInstallEq,
          literalCompareRef] using installPath)
      comparePath
  have throughBlock :
      AcceptPath graph
        (.node (firstBitRef .emit (inRangeState positive)))
        (.node (restoreRef .emit .clause .f))
        (installSteps + compareSteps + blockSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      throughCompare blockPath
  refine
    ⟨installSteps + compareSteps + blockSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughBlock restorePath
  · unfold invalidEqualTerminatorCost
    have blockBound' :
        blockSteps ≤
          TargetEmitterRuntimeProgramBound.programWorkEnvelope
            (CNFToNANDWorkspace.capacity formula)
            (markedSource
              (CNFToNANDWorkspace.formulaTokens formula)
              processed .f (next :: tail))
            runtime blockDescriptors[14].primitives := by
      simpa [source] using blockBound
    dsimp [installSteps, compareSteps, restoreSteps, source]
    omega

private def overflowTerminatorCost
    (formula : CNFFormula) (processed : List CNFToken)
    (runtime : Runtime) (source : List WorkSymbol) : Nat :=
  PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f +
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
      (CNFToNANDWorkspace.capacity formula) source runtime
      blockDescriptors[14].primitives +
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f

private theorem emit_overflow_terminator_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .f :: next :: tail)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤
        CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents
        (firstBitRef .emit (overflowState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .f (next :: tail))
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .emit (overflowState positive)))
        (.node (firstBitRef .emit .clause))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        (invalidLiteralResult runtime).scratch
        (invalidLiteralResult runtime).registers
        (invalidLiteralResult runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.f]))
        (scanAfterCells next tail)
        (invalidLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        overflowTerminatorCost formula processed runtime
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed .f (next :: tail)) := by
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed .f (next :: tail)
  let context :=
    markedSourceContext formula processed .f (next :: tail) tokens
  let layout :=
    markedCursorLayout formula processed .f (next :: tail) tokens
  have postInstallEq :
      postInstallEndpoint .emit (overflowState positive) .f =
        .node emitInvalidLiteralRef := by
    cases positive <;> rfl
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_read_install_path
        .emit formula processed .f (next :: tail)
        (overflowState positive) runtime tokens
        (by cases positive <;> simp [overflowState,
          activeGrammarStates])
        (by cases positive <;> decide)
        initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have blockRepresents :
      TapeRepresents emitInvalidLiteralRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens installedTape := by
    simpa [TapeRepresents, postInstallEndpoint] using
      (represents_at_state
        (newState := emitInvalidLiteralRef.startState)
        installedRepresents)
  rcases
      invalidLiteralBlock_path (context := context)
        layout runtime fits scratchBound outputBound
        installedTape blockRepresents with
    ⟨blockSteps, restoreTape, blockPath, restoreRepresents,
      blockBound⟩
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_restore_advance_next_path
        .emit formula processed .f next tail .clause
        (invalidLiteralResult runtime) tokens (by decide)
        restoreTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  let installSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f
  let restoreSteps :=
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .f
  have throughBlock :
      AcceptPath graph
        (.node (firstBitRef .emit (overflowState positive)))
        (.node (restoreRef .emit .clause .f))
        (installSteps + blockSteps)
        initialTape restoreTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      (by
        simpa [installSteps, postInstallEq] using installPath)
      blockPath
  refine
    ⟨installSteps + blockSteps + restoreSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        throughBlock restorePath
  · unfold overflowTerminatorCost
    have blockBound' :
        blockSteps ≤
          TargetEmitterRuntimeProgramBound.programWorkEnvelope
            (CNFToNANDWorkspace.capacity formula)
            (markedSource
              (CNFToNANDWorkspace.formulaTokens formula)
              processed .f (next :: tail))
            runtime blockDescriptors[14].primitives := by
      simpa [source] using blockBound
    dsimp [installSteps, restoreSteps, source]
    omega

/-! ## Structural emit semantics -/

private def popLast : List Nat → List Nat × Nat
  | [] => ([], 0)
  | value :: rest =>
      match rest with
      | [] => ([], value)
      | _ =>
          let popped := popLast rest
          (value :: popped.1, popped.2)

@[simp] private theorem popLast_append_singleton
    (prior : List Nat) (value : Nat) :
    popLast (prior ++ [value]) = (prior, value) := by
  induction prior with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil =>
          rfl
      | cons next rest =>
          change
            (let popped :=
                popLast (next :: rest ++ [value]);
              (head :: popped.1, popped.2)) =
              (head :: next :: rest, value)
          rw [inductionHypothesis]

private def popNewestResult (runtime : Runtime) : Runtime :=
  { runtime with
    scratch := (popLast runtime.checks).2
    checks := (popLast runtime.checks).1 }

private theorem popNewestResult_of_checks
    (runtime : Runtime) (prior : List Nat) (value : Nat)
    (checks : runtime.checks = prior ++ [value]) :
    popNewestResult runtime =
      popCoordinateResult runtime prior value := by
  simp [popNewestResult, popCoordinateResult, checks]

private def literalEmitGateCount
    (width : Nat) (literal : CNFLiteral) : Nat :=
  if literal.variableIndex < width then
    if literal.positive then 1 else 2
  else
    1

private def literalRuntime
    (width : Nat) (literal : CNFLiteral)
    (runtime : Runtime) : Runtime :=
  let scanned :=
    { runtime with
      scratch := min literal.variableIndex width }
  if literal.variableIndex < width then
    if literal.positive then
      positiveLiteralResult scanned
    else
      negativeLiteralResult scanned
  else
    invalidLiteralResult scanned

private def literalListRuntime
    (width : Nat) : List CNFLiteral → Runtime → Runtime
  | [], runtime => runtime
  | literal :: rest, runtime =>
      literalListRuntime width rest
        (literalRuntime width literal runtime)

private def literalListGateCount
    (width : Nat) : List CNFLiteral → Nat
  | [] => 0
  | literal :: rest =>
      literalEmitGateCount width literal +
        literalListGateCount width rest

private def clauseFoldLoopRuntime :
    Nat → Runtime → Runtime
  | 0, runtime =>
      finishNonemptyClauseResult (popNewestResult runtime)
  | count + 1, runtime =>
      clauseFoldLoopRuntime count
        (extendClauseResult (popNewestResult runtime))

private def clauseFoldRuntime
    (literalCount : Nat) (runtime : Runtime) : Runtime :=
  match literalCount with
  | 0 =>
      pushTotalGateResult (popNewestResult runtime)
  | count + 1 =>
      clauseFoldLoopRuntime count
        (seedClauseResult (popNewestResult runtime))

private def clauseRuntime
    (width : Nat) (clause : List CNFLiteral)
    (runtime : Runtime) : Runtime :=
  clauseFoldRuntime clause.length
    (literalListRuntime width clause
      (pushTotalGateResult runtime))

private def clauseGateCount
    (width : Nat) (clause : List CNFLiteral) : Nat :=
  literalListGateCount width clause + 2 * clause.length

private def clauseListRuntime
    (width : Nat) :
    List (List CNFLiteral) → Runtime → Runtime
  | [], runtime => runtime
  | clause :: rest, runtime =>
      clauseListRuntime width rest
        (clauseRuntime width clause runtime)

private def clauseListGateCount
    (width : Nat) :
    List (List CNFLiteral) → Nat
  | [] => 0
  | clause :: rest =>
      clauseGateCount width clause +
        clauseListGateCount width rest

private def runtimeClauseSource (runtime : Runtime) : ClauseSource :=
  if runtime.scratch = runtime.registers.currentGate then
    .constantFalse
  else
    .gateScratch

private def formulaFoldLoopRuntime :
    Nat → Runtime → Runtime
  | 0, runtime =>
      popNewestResult runtime
  | count + 1, runtime =>
      let popped := popNewestResult runtime
      formulaFoldLoopRuntime count
        (extendFormulaResult
          (runtimeClauseSource popped) popped)

private def formulaFoldRuntime
    (clauseCount : Nat) (runtime : Runtime) : Runtime :=
  match clauseCount with
  | 0 =>
      emptyFormulaResult (popNewestResult runtime)
  | count + 1 =>
      let popped := popNewestResult runtime
      formulaFoldLoopRuntime count
        (seedFormulaResult
          (runtimeClauseSource popped) popped)

private def formulaRuntime (formula : CNFFormula) : Runtime :=
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses
      (emitInitialRuntime formula)
  formulaFoldRuntime formula.clauses.length clauses

private def completedRuntime (formula : CNFFormula) : Runtime :=
  circuitSuffixResult (formulaRuntime formula)

private theorem literalEmitGateCount_eq
    (width : Nat) (literal : CNFLiteral) :
    literalEmitGateCount width literal =
      1 +
        (if !literal.positive &&
            literal.variableIndex < width then 1 else 0) := by
  unfold literalEmitGateCount
  by_cases valid : literal.variableIndex < width <;>
    cases positive : literal.positive <;>
      simp [valid, positive]

private theorem literalListGateCount_eq
    (width : Nat) (literals : List CNFLiteral) :
    literalListGateCount width literals =
      literals.length +
        (literals.filter fun literal =>
          !literal.positive &&
            literal.variableIndex < width).length := by
  induction literals with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      rw [literalListGateCount, literalEmitGateCount_eq,
        inductionHypothesis]
      by_cases valid : literal.variableIndex < width <;>
        cases positive : literal.positive <;>
          simp [valid, positive] <;> omega

private theorem clauseListGateCount_eq
    (formula : CNFFormula) :
    clauseListGateCount formula.variableCount formula.clauses =
      CNFToNAND.validNegativeLiteralCount formula +
        3 * CNFToNAND.literalCount formula := by
  unfold CNFToNAND.validNegativeLiteralCount
    CNFToNAND.literalCount
  induction formula.clauses with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      simp only [clauseListGateCount, clauseGateCount,
        List.map_cons, List.sum_cons, literalListGateCount_eq]
      rw [inductionHypothesis]
      omega

private theorem compilerGateCount_eq_structural
    (formula : CNFFormula) :
    CNFToNANDWorkspace.compilerGateCount formula =
      clauseListGateCount formula.variableCount formula.clauses +
        2 * formula.clauses.length +
        (if formula.clauses.isEmpty then 1 else 0) := by
  rw [clauseListGateCount_eq]
  unfold CNFToNANDWorkspace.compilerGateCount
  rw [CNFToNAND.compileFormula_gateCount_exact]

/-- Output decoding is insensitive to the finite blank padding selected by
the physical trace. -/
theorem encodeWorkTape_outputBits_eq_of_blankEquivalent
    {first second : WorkTape}
    (equivalent : WorkTape.BlankEquivalent first second) :
    (encodeWorkTape first).outputBits =
      (encodeWorkTape second).outputBits :=
  PNP.Concrete.LockedNAND.TargetEmitterControllerCompletionTrace.encodeWorkTape_outputBits_eq_of_blankEquivalent
    equivalent

/-! ## Literal traversal -/

private theorem encodeUnaryTokens_eq_replicate (count : Nat) :
    encodeUnaryTokens count =
      List.replicate count CNFToken.t ++ [.f] := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      simp [encodeUnaryTokens, List.replicate_succ,
        inductionHypothesis]

private theorem advanceLiteralRun_eq
    (count : Nat) (runtime : Runtime) :
    advanceLiteralRun count runtime =
      { runtime with scratch := runtime.scratch + count } := by
  induction count generalizing runtime with
  | zero =>
      simp [advanceLiteralRun]
  | succ count inductionHypothesis =>
      rw [advanceLiteralRun, inductionHypothesis]
      simp [advanceLiteralResult]
      omega

private theorem advanceLiteralRun_reset_eq
    (count : Nat) (runtime : Runtime) :
    advanceLiteralRun count (resetLiteralResult runtime) =
      { runtime with scratch := count } := by
  rw [advanceLiteralRun_eq]
  simp [resetLiteralResult]

private theorem literalRuntime_of_valid
    (width : Nat) (literal : CNFLiteral)
    (runtime : Runtime)
    (valid : literal.variableIndex < width) :
    literalRuntime width literal runtime =
      validLiteralResult literal.positive
        { runtime with scratch := literal.variableIndex } := by
  unfold literalRuntime
  rw [Nat.min_eq_left (Nat.le_of_lt valid)]
  cases positive : literal.positive <;>
    simp [valid, positive, validLiteralResult]

private theorem literalRuntime_of_invalid
    (width : Nat) (literal : CNFLiteral)
    (runtime : Runtime)
    (invalid : width ≤ literal.variableIndex) :
    literalRuntime width literal runtime =
      invalidLiteralResult
        { runtime with scratch := width } := by
  unfold literalRuntime
  rw [Nat.min_eq_right invalid]
  have notValid : ¬ literal.variableIndex < width :=
    Nat.not_lt.mpr invalid
  simp [notValid]

private def validLiteralCost
    (formula : CNFFormula) (processed : List CNFToken)
    (literal : CNFLiteral) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime) : Nat :=
  match literal.variableIndex with
  | 0 =>
      signStepCost formula literal.positive processed .f (next :: tail)
          runtime +
        validTerminatorCost formula literal.positive
          (processed ++ [signToken literal.positive])
          (resetLiteralResult runtime)
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            (processed ++ [signToken literal.positive])
            .f (next :: tail))
  | count + 1 =>
      signStepCost formula literal.positive processed .t
          (List.replicate count .t ++ .f :: next :: tail)
          runtime +
        inRangeTRunCost formula literal.positive (count + 1)
          (processed ++ [signToken literal.positive])
          (.f :: next :: tail) (resetLiteralResult runtime) +
        validTerminatorCost formula literal.positive
          ((processed ++ [signToken literal.positive]) ++
            List.replicate (count + 1) .t)
          (advanceLiteralRun (count + 1)
            (resetLiteralResult runtime))
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            ((processed ++ [signToken literal.positive]) ++
              List.replicate (count + 1) .t)
            .f (next :: tail))

private theorem emit_valid_literal_path
    (formula : CNFFormula) (processed : List CNFToken)
    (literal : CNFLiteral) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeLiteralTokens literal ++ next :: tail)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (inputCount :
      runtime.registers.inputCount = formula.variableCount)
    (valid :
      literal.variableIndex < formula.variableCount)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (outputBound :
      runtime.registers.outputIndex +
          validLiteralOutputGrowth literal.positive ≤
        CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (encodeLiteralTokens literal ++ next :: tail) ++
          carrierFooterCells)
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
        (.node (firstBitRef .emit .clause))
        (.node (firstBitRef .emit .clause))
        steps initialTape finalTape ∧
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        (literalRuntime formula.variableCount literal runtime).scratch
        (literalRuntime formula.variableCount literal runtime).registers
        (literalRuntime formula.variableCount literal runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ encodeLiteralTokens literal))
        (scanAfterCells next tail)
        (literalRuntime formula.variableCount literal runtime).targetTokens
        finalTape ∧
      steps ≤
        validLiteralCost formula processed literal next tail runtime := by
  let positive := literal.positive
  let index := literal.variableIndex
  let afterSign := processed ++ [signToken positive]
  let reset := resetLiteralResult runtime
  have positiveWidth :
      0 < runtime.registers.inputCount := by
    rw [inputCount]
    omega
  cases indexEq : index with
  | zero =>
      have literalIndex : literal.variableIndex = 0 := by
        simpa [index] using indexEq
      have signTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ signToken positive :: .f :: next :: tail := by
        simpa [encodeLiteralTokens, signToken, positive,
          literalIndex, encodeUnaryTokens, List.append_assoc] using
          tokens
      have signRepresents :
          ScanRepresents (firstBitRef .emit .clause).startState
            (CNFToNANDWorkspace.capacity formula)
            runtime.scratch runtime.registers runtime.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells (signToken positive)
              (.f :: next :: tail))
            runtime.targetTokens initialTape := by
        simpa [encodeLiteralTokens, signToken, positive,
          literalIndex, encodeUnaryTokens, scanAfterCells,
          carrierGateCells, carrierGateCellsFor,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
          List.append_assoc] using represents
      rcases
          emit_sign_less_path formula positive processed .f
            (next :: tail) runtime signTokens fits positiveWidth
            scratchBound initialTape signRepresents with
        ⟨signSteps, terminatorTape, signPath,
          terminatorRepresents, signBound⟩
      have terminatorTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            afterSign ++ .f :: next :: tail := by
        simpa [afterSign, List.append_assoc] using signTokens
      have terminatorInput :
          ScanRepresents
            (firstBitRef .emit (inRangeState positive)).startState
            (CNFToNANDWorkspace.capacity formula)
            reset.scratch reset.registers reset.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) afterSign)
            (scanAfterCells .f (next :: tail))
            reset.targetTokens terminatorTape := by
        simpa [afterSign, reset] using terminatorRepresents
      have resetFits :
          LedgerFits (CNFToNANDWorkspace.capacity formula)
            reset.registers := by
        simpa [reset, resetLiteralResult] using fits
      have resetLess :
          reset.scratch < reset.registers.inputCount := by
        simp [reset, resetLiteralResult]
        exact positiveWidth
      have resetScratch :
          reset.scratch < CNFToNANDWorkspace.capacity formula := by
        exact Nat.lt_of_lt_of_le resetLess resetFits.inputCount
      have resetOutput :
          reset.registers.outputIndex +
              validLiteralOutputGrowth positive ≤
            CNFToNANDWorkspace.capacity formula := by
        simpa [reset, resetLiteralResult, positive] using outputBound
      rcases
          emit_valid_terminator_path formula positive afterSign
            next tail reset terminatorTokens resetFits resetLess
            resetScratch resetOutput terminatorTape terminatorInput with
        ⟨terminatorSteps, finalTape, terminatorPath,
          finalRepresents, terminatorBound⟩
      refine
        ⟨signSteps + terminatorSteps, finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            signPath terminatorPath, ?_, ?_⟩
      · have runtimeEq :
            literalRuntime formula.variableCount literal runtime =
              validLiteralResult positive reset := by
          rw [literalRuntime_of_valid _ _ _ valid]
          simp [literalIndex, reset, resetLiteralResult, positive]
        simpa [runtimeEq, afterSign, encodeLiteralTokens,
          signToken, positive, literalIndex, encodeUnaryTokens,
          List.append_assoc] using finalRepresents
      · have signBound' :
            signSteps ≤
              signStepCost formula literal.positive processed .f
                (next :: tail) runtime := by
          simpa [positive] using signBound
        have terminatorBound' :
            terminatorSteps ≤
              validTerminatorCost formula literal.positive
                (processed ++ [signToken literal.positive])
                (resetLiteralResult runtime)
                (markedSource
                  (CNFToNANDWorkspace.formulaTokens formula)
                  (processed ++ [signToken literal.positive])
                  .f (next :: tail)) := by
          simpa [positive, afterSign, reset] using terminatorBound
        simp only [validLiteralCost, literalIndex]
        omega
  | succ count =>
      have literalIndex :
          literal.variableIndex = count + 1 := by
        simpa [index] using indexEq
      have signTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ signToken positive :: .t ::
              (List.replicate count .t ++ .f :: next :: tail) := by
        simpa [encodeLiteralTokens, signToken, positive,
          literalIndex, encodeUnaryTokens_eq_replicate,
          List.replicate_succ, List.append_assoc] using tokens
      have signRepresents :
          ScanRepresents (firstBitRef .emit .clause).startState
            (CNFToNANDWorkspace.capacity formula)
            runtime.scratch runtime.registers runtime.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells (signToken positive)
              (.t :: (List.replicate count CNFToken.t ++
                .f :: next :: tail)))
            runtime.targetTokens initialTape := by
        simpa [encodeLiteralTokens, signToken, positive,
          literalIndex, encodeUnaryTokens_eq_replicate,
          List.replicate_succ, scanAfterCells, carrierGateCells,
          carrierGateCellsFor,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
          List.append_assoc] using represents
      rcases
          emit_sign_less_path formula positive processed .t
            (List.replicate count CNFToken.t ++ .f :: next :: tail)
            runtime signTokens fits positiveWidth scratchBound
            initialTape signRepresents with
        ⟨signSteps, runTape, signPath, runRepresents,
          signBound⟩
      have runTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            afterSign ++ List.replicate (count + 1) .t ++
              (.f :: next :: tail) := by
        simpa [afterSign, List.replicate_succ,
          List.append_assoc] using signTokens
      have runInput :
          ScanRepresents
            (firstBitRef .emit (inRangeState positive)).startState
            (CNFToNANDWorkspace.capacity formula)
            reset.scratch reset.registers reset.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) afterSign)
            (carrierGateCells
                (List.replicate (count + 1) .t ++
                  .f :: next :: tail) ++
              carrierFooterCells)
            reset.targetTokens runTape := by
        simpa [afterSign, reset, scanAfterCells,
          carrierGateCells, carrierGateCellsFor,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
          List.replicate_succ,
          List.append_assoc] using runRepresents
      have resetFits :
          LedgerFits (CNFToNANDWorkspace.capacity formula)
            reset.registers := by
        simpa [reset, resetLiteralResult] using fits
      have runBound :
          reset.scratch + (count + 1) ≤
            reset.registers.inputCount := by
        simp [reset, resetLiteralResult, inputCount]
        omega
      rcases
          emit_inRange_t_run_path formula positive (count + 1)
            afterSign (.f :: next :: tail) reset runTokens
            (by simp) resetFits runBound runTape runInput with
        ⟨runSteps, terminatorTape, runPath,
          terminatorRepresents, runStepsBound⟩
      let scanned := advanceLiteralRun (count + 1) reset
      let terminatorProcessed :=
        afterSign ++ List.replicate (count + 1) CNFToken.t
      have terminatorTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            terminatorProcessed ++ .f :: next :: tail := by
        simpa [terminatorProcessed, List.append_assoc] using runTokens
      have terminatorInput :
          ScanRepresents
            (firstBitRef .emit (inRangeState positive)).startState
            (CNFToNANDWorkspace.capacity formula)
            scanned.scratch scanned.registers scanned.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula)
              terminatorProcessed)
            (scanAfterCells .f (next :: tail))
            scanned.targetTokens terminatorTape := by
        simpa [scanned, terminatorProcessed, scanAfterCells,
          carrierGateCells, carrierGateCellsFor,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
          List.append_assoc] using
          terminatorRepresents
      have scannedFits :
          LedgerFits (CNFToNANDWorkspace.capacity formula)
            scanned.registers := by
        simpa [scanned, advanceLiteralRun_eq, reset,
          resetLiteralResult] using fits
      have scannedLess :
          scanned.scratch < scanned.registers.inputCount := by
        simp [scanned, advanceLiteralRun_reset_eq, reset, inputCount]
        omega
      have scannedScratch :
          scanned.scratch < CNFToNANDWorkspace.capacity formula := by
        exact Nat.lt_of_lt_of_le scannedLess scannedFits.inputCount
      have scannedOutput :
          scanned.registers.outputIndex +
              validLiteralOutputGrowth positive ≤
            CNFToNANDWorkspace.capacity formula := by
        simpa [scanned, advanceLiteralRun_eq, reset,
          resetLiteralResult, positive] using outputBound
      rcases
          emit_valid_terminator_path formula positive
            terminatorProcessed next tail scanned
            terminatorTokens scannedFits scannedLess scannedScratch
            scannedOutput terminatorTape terminatorInput with
        ⟨terminatorSteps, finalTape, terminatorPath,
          finalRepresents, terminatorBound⟩
      have prefixPath :
          AcceptPath graph
            (.node (firstBitRef .emit .clause))
            (.node (firstBitRef .emit (inRangeState positive)))
            (signSteps + runSteps)
            initialTape terminatorTape :=
        AcceptPath.trans graph _ _ _ _ _ _ _ _
          signPath runPath
      refine
        ⟨signSteps + runSteps + terminatorSteps, finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            prefixPath terminatorPath, ?_, ?_⟩
      · have runtimeEq :
            literalRuntime formula.variableCount literal runtime =
              validLiteralResult positive scanned := by
          rw [literalRuntime_of_valid _ _ _ valid]
          simp [scanned, advanceLiteralRun_reset_eq, reset,
            literalIndex, positive]
        simpa [runtimeEq, terminatorProcessed, afterSign,
          encodeLiteralTokens, signToken, positive, literalIndex,
          encodeUnaryTokens_eq_replicate, List.append_assoc] using
          finalRepresents
      · have signBound' :
            signSteps ≤
              signStepCost formula literal.positive processed .t
                (List.replicate count CNFToken.t ++
                  .f :: next :: tail) runtime := by
          simpa [positive] using signBound
        have runStepsBound' :
            runSteps ≤
              inRangeTRunCost formula literal.positive
                (count + 1)
                (processed ++ [signToken literal.positive])
                (.f :: next :: tail)
                (resetLiteralResult runtime) := by
          simpa [positive, afterSign, reset] using runStepsBound
        have terminatorBound' :
            terminatorSteps ≤
              validTerminatorCost formula literal.positive
                ((processed ++ [signToken literal.positive]) ++
                  List.replicate (count + 1) CNFToken.t)
                (advanceLiteralRun (count + 1)
                  (resetLiteralResult runtime))
                (markedSource
                  (CNFToNANDWorkspace.formulaTokens formula)
                  ((processed ++ [signToken literal.positive]) ++
                    List.replicate (count + 1) CNFToken.t)
                  .f (next :: tail)) := by
          simpa [positive, terminatorProcessed, afterSign,
            scanned, reset] using terminatorBound
        simp only [validLiteralCost, literalIndex]
        omega

private def unaryLiteralResult
    (positive : Bool) (count : Nat)
    (runtime : Runtime) : Runtime :=
  let scanned :=
    { runtime with
      scratch :=
        min (runtime.scratch + count)
          runtime.registers.inputCount }
  if runtime.scratch + count < runtime.registers.inputCount then
    validLiteralResult positive scanned
  else
    invalidLiteralResult scanned

private def unaryLiteralCost
    (formula : CNFFormula) (positive : Bool) :
    Nat → List CNFToken → Runtime → CNFToken →
      List CNFToken → Nat
  | 0, processed, runtime, next, tail =>
      if runtime.scratch < runtime.registers.inputCount then
        validTerminatorCost formula positive processed runtime
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed .f (next :: tail))
      else
        invalidEqualTerminatorCost formula processed runtime
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed .f (next :: tail))
  | count + 1, processed, runtime, next, tail =>
      let remainder :=
        List.replicate count CNFToken.t ++ .f :: next :: tail
      match remainder with
      | [] => 0
      | nextToken :: tokenTail =>
          if runtime.scratch < runtime.registers.inputCount then
            inRangeTStepCost formula positive processed
                nextToken tokenTail runtime +
              unaryLiteralCost formula positive count
                (processed ++ [.t])
                (advanceLiteralResult runtime) next tail
          else
            equalTStepCost formula processed runtime +
              overflowTRunCost formula count
                (processed ++ [.t]) (.f :: next :: tail) +
              overflowTerminatorCost formula
                (processed ++
                  List.replicate (count + 1) CNFToken.t)
                runtime
                (markedSource
                  (CNFToNANDWorkspace.formulaTokens formula)
                  (processed ++
                    List.replicate (count + 1) CNFToken.t)
                  .f (next :: tail))

set_option maxHeartbeats 100000 in
private theorem unaryLiteralCost_succ
    (formula : CNFFormula) (positive : Bool) (count : Nat)
    (processed : List CNFToken) (runtime : Runtime)
    (next : CNFToken) (tail : List CNFToken)
    (nextToken : CNFToken) (tokenTail : List CNFToken)
    (remainderEq :
      List.replicate count CNFToken.t ++ .f :: next :: tail =
        nextToken :: tokenTail) :
    unaryLiteralCost formula positive (Nat.succ count)
        processed runtime next tail =
      if runtime.scratch < runtime.registers.inputCount then
        inRangeTStepCost formula positive processed
            nextToken tokenTail runtime +
          unaryLiteralCost formula positive count
            (processed ++ [.t]) (advanceLiteralResult runtime) next tail
      else
        equalTStepCost formula processed runtime +
            overflowTRunCost formula count
              (processed ++ [.t]) (.f :: next :: tail) +
          overflowTerminatorCost formula
            (processed ++ List.replicate (count + 1) CNFToken.t)
            runtime
            (markedSource
              (CNFToNANDWorkspace.formulaTokens formula)
              (processed ++ List.replicate (count + 1) CNFToken.t)
              .f (next :: tail)) := by
  simp only [unaryLiteralCost, remainderEq]

private theorem emit_unary_literal_path
    (formula : CNFFormula) (positive : Bool) :
    ∀ (count : Nat) (processed : List CNFToken)
      (runtime : Runtime) (next : CNFToken)
      (tail : List CNFToken),
      CNFToNANDWorkspace.formulaTokens formula =
          processed ++ List.replicate count .t ++
            .f :: next :: tail →
      LedgerFits (CNFToNANDWorkspace.capacity formula)
          runtime.registers →
      runtime.scratch ≤ runtime.registers.inputCount →
      runtime.registers.inputCount <
          CNFToNANDWorkspace.capacity formula →
      runtime.registers.outputIndex +
          validLiteralOutputGrowth positive ≤
          CNFToNANDWorkspace.capacity formula →
      ∀ initialTape,
      ScanRepresents
        (firstBitRef .emit (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (List.replicate count .t ++ .f :: next :: tail) ++
          carrierFooterCells)
        runtime.targetTokens initialTape →
      ∃ steps finalTape,
        AcceptPath graph
          (.node (firstBitRef .emit (inRangeState positive)))
          (.node (firstBitRef .emit .clause))
          steps initialTape finalTape ∧
        ScanRepresents (firstBitRef .emit .clause).startState
          (CNFToNANDWorkspace.capacity formula)
          (unaryLiteralResult positive count runtime).scratch
          (unaryLiteralResult positive count runtime).registers
          (unaryLiteralResult positive count runtime).checks
          (scanBeforeCells
            (CNFToNANDWorkspace.formulaTokens formula)
            (processed ++
              List.replicate count CNFToken.t ++ [.f]))
          (scanAfterCells next tail)
          (unaryLiteralResult positive count runtime).targetTokens
          finalTape ∧
        steps ≤
          unaryLiteralCost formula positive count
            processed runtime next tail := by
  intro count
  induction count with
  | zero =>
      intro processed runtime next tail tokens fits scratchLe
        inputCapacity outputBound initialTape represents
      by_cases less :
          runtime.scratch < runtime.registers.inputCount
      · have input :
            ScanRepresents
              (firstBitRef .emit (inRangeState positive)).startState
              (CNFToNANDWorkspace.capacity formula)
              runtime.scratch runtime.registers runtime.checks
              (scanBeforeCells
                (CNFToNANDWorkspace.formulaTokens formula) processed)
              (scanAfterCells .f (next :: tail))
              runtime.targetTokens initialTape := by
          simpa [scanAfterCells, carrierGateCells,
            carrierGateCellsFor,
            PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells]
            using represents
        have scratchCapacity :
            runtime.scratch <
              CNFToNANDWorkspace.capacity formula :=
          Nat.lt_trans less inputCapacity
        rcases
            emit_valid_terminator_path formula positive processed
              next tail runtime
              (by simpa using tokens)
              fits less scratchCapacity outputBound
              initialTape input with
          ⟨steps, finalTape, path, finalRepresents, bounded⟩
        refine ⟨steps, finalTape, path, ?_, ?_⟩
        · have resultEq :
              unaryLiteralResult positive 0 runtime =
                validLiteralResult positive runtime := by
            have minEq :
                min (runtime.scratch + 0)
                    runtime.registers.inputCount =
                  runtime.scratch := by
              exact Nat.min_eq_left (Nat.le_of_lt less)
            have scannedEq :
                { runtime with
                    scratch :=
                      min (runtime.scratch + 0)
                        runtime.registers.inputCount } =
                  runtime := by
              rw [minEq]
            unfold unaryLiteralResult
            rw [scannedEq]
            simp [less]
          simpa [resultEq] using finalRepresents
        · simpa [unaryLiteralCost, less] using bounded
      · have equal :
            runtime.scratch = runtime.registers.inputCount := by
          omega
        have input :
            ScanRepresents
              (firstBitRef .emit (inRangeState positive)).startState
              (CNFToNANDWorkspace.capacity formula)
              runtime.scratch runtime.registers runtime.checks
              (scanBeforeCells
                (CNFToNANDWorkspace.formulaTokens formula) processed)
              (scanAfterCells .f (next :: tail))
              runtime.targetTokens initialTape := by
          simpa [scanAfterCells, carrierGateCells,
            carrierGateCellsFor,
            PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells]
            using represents
        have scratchCapacity :
            runtime.scratch <
              CNFToNANDWorkspace.capacity formula := by
          rw [equal]
          exact inputCapacity
        have invalidOutput :
            runtime.registers.outputIndex + 1 ≤
              CNFToNANDWorkspace.capacity formula := by
          cases positive <;>
            simp [validLiteralOutputGrowth] at outputBound ⊢ <;>
            omega
        rcases
            emit_invalid_equal_terminator_path formula positive
              processed next tail runtime
              (by simpa using tokens)
              fits equal scratchCapacity invalidOutput
              initialTape input with
          ⟨steps, finalTape, path, finalRepresents, bounded⟩
        refine ⟨steps, finalTape, path, ?_, ?_⟩
        · have resultEq :
              unaryLiteralResult positive 0 runtime =
                invalidLiteralResult runtime := by
            have minEq :
                min (runtime.scratch + 0)
                    runtime.registers.inputCount =
                  runtime.scratch := by
              exact Nat.min_eq_left scratchLe
            have scannedEq :
                { runtime with
                    scratch :=
                      min (runtime.scratch + 0)
                        runtime.registers.inputCount } =
                  runtime := by
              rw [minEq]
            unfold unaryLiteralResult
            rw [scannedEq]
            simp [less]
          simpa [resultEq] using finalRepresents
        · simpa [unaryLiteralCost, less] using bounded
  | succ count inductionHypothesis =>
      intro processed runtime next tail tokens fits scratchLe
        inputCapacity outputBound initialTape represents
      let remainder :=
        List.replicate count CNFToken.t ++ .f :: next :: tail
      have remainderNonempty : remainder ≠ [] := by
        simp [remainder]
      cases remainderEq : remainder with
      | nil =>
          exact False.elim (remainderNonempty remainderEq)
      | cons nextToken tokenTail =>
          have stepTokens :
              CNFToNANDWorkspace.formulaTokens formula =
                processed ++ .t :: nextToken :: tokenTail := by
            simpa [List.replicate_succ, remainder, remainderEq,
              List.append_assoc] using tokens
          have stepRepresents :
              ScanRepresents
                (firstBitRef .emit
                  (inRangeState positive)).startState
                (CNFToNANDWorkspace.capacity formula)
                runtime.scratch runtime.registers runtime.checks
                (scanBeforeCells
                  (CNFToNANDWorkspace.formulaTokens formula)
                  processed)
                (scanAfterCells .t (nextToken :: tokenTail))
                runtime.targetTokens initialTape := by
            simpa [List.replicate_succ, remainder, remainderEq,
              scanAfterCells, carrierGateCells, carrierGateCellsFor,
              PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
              List.append_assoc] using represents
          by_cases less :
              runtime.scratch < runtime.registers.inputCount
          · rcases
                emit_inRange_t_step_path formula positive processed
                  nextToken tokenTail runtime stepTokens fits less
                  initialTape stepRepresents with
              ⟨stepSteps, nextTape, stepPath, nextRepresents,
                stepBound⟩
            have recursiveTokens :
                CNFToNANDWorkspace.formulaTokens formula =
                  (processed ++ [.t]) ++
                    List.replicate count .t ++
                      .f :: next :: tail := by
              simpa [List.replicate_succ,
                List.append_assoc] using tokens
            have recursiveRepresents :
                ScanRepresents
                  (firstBitRef .emit
                    (inRangeState positive)).startState
                  (CNFToNANDWorkspace.capacity formula)
                  (advanceLiteralResult runtime).scratch
                  (advanceLiteralResult runtime).registers
                  (advanceLiteralResult runtime).checks
                  (scanBeforeCells
                    (CNFToNANDWorkspace.formulaTokens formula)
                    (processed ++ [.t]))
                  (carrierGateCells
                      (List.replicate count .t ++
                        .f :: next :: tail) ++
                    carrierFooterCells)
                  (advanceLiteralResult runtime).targetTokens
                  nextTape := by
              simpa [remainder, remainderEq, scanAfterCells,
                carrierGateCells, carrierGateCellsFor,
                PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
                List.append_assoc] using nextRepresents
            have recursiveFits :
                LedgerFits (CNFToNANDWorkspace.capacity formula)
                  (advanceLiteralResult runtime).registers := by
              simpa [advanceLiteralResult] using fits
            have recursiveScratch :
                (advanceLiteralResult runtime).scratch ≤
                  (advanceLiteralResult runtime).registers.inputCount := by
              simp [advanceLiteralResult]
              omega
            have recursiveInputCapacity :
                (advanceLiteralResult runtime).registers.inputCount <
                  CNFToNANDWorkspace.capacity formula := by
              simpa [advanceLiteralResult] using inputCapacity
            have recursiveOutput :
                (advanceLiteralResult runtime).registers.outputIndex +
                    validLiteralOutputGrowth positive ≤
                  CNFToNANDWorkspace.capacity formula := by
              simpa [advanceLiteralResult] using outputBound
            rcases
                inductionHypothesis
                  (processed ++ [.t])
                  (advanceLiteralResult runtime)
                  next tail recursiveTokens recursiveFits
                  recursiveScratch recursiveInputCapacity
                  recursiveOutput nextTape recursiveRepresents with
              ⟨tailSteps, finalTape, tailPath, finalRepresents,
                tailBound⟩
            refine
              ⟨stepSteps + tailSteps, finalTape,
                AcceptPath.trans graph _ _ _ _ _ _ _ _
                  stepPath tailPath, ?_, ?_⟩
            · have resultEq :
                  unaryLiteralResult positive (count + 1) runtime =
                    unaryLiteralResult positive count
                      (advanceLiteralResult runtime) := by
                have sumEq :
                    runtime.scratch + (count + 1) =
                      (advanceLiteralResult runtime).scratch +
                        count := by
                  simp [advanceLiteralResult]
                  omega
                unfold unaryLiteralResult
                rw [sumEq]
                simp [advanceLiteralResult]
              simpa [resultEq, List.replicate_succ,
                List.append_assoc] using finalRepresents
            · simp only [unaryLiteralCost]
              rw [show
                List.replicate count CNFToken.t ++
                    .f :: next :: tail =
                  nextToken :: tokenTail by
                exact remainderEq]
              simp [less]
              exact Nat.add_le_add stepBound tailBound
          · have equal :
                runtime.scratch =
                  runtime.registers.inputCount := by
              omega
            rcases
                emit_equal_t_step_path formula positive processed
                  nextToken tokenTail runtime stepTokens fits equal
                  initialTape stepRepresents with
              ⟨equalSteps, overflowTape, equalPath,
                overflowRepresents, equalBound⟩
            have overflowTokens :
                CNFToNANDWorkspace.formulaTokens formula =
                  (processed ++ [.t]) ++
                    List.replicate count .t ++
                      .f :: next :: tail := by
              simpa [List.replicate_succ,
                List.append_assoc] using tokens
            have overflowInput :
                ScanRepresents
                  (firstBitRef .emit
                    (overflowState positive)).startState
                  (CNFToNANDWorkspace.capacity formula)
                  runtime.scratch runtime.registers runtime.checks
                  (scanBeforeCells
                    (CNFToNANDWorkspace.formulaTokens formula)
                    (processed ++ [.t]))
                  (carrierGateCells
                      (List.replicate count .t ++
                        .f :: next :: tail) ++
                    carrierFooterCells)
                  runtime.targetTokens overflowTape := by
              simpa [remainder, remainderEq, scanAfterCells,
                carrierGateCells, carrierGateCellsFor,
                PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
                List.append_assoc] using overflowRepresents
            rcases
                emit_overflow_t_run_path formula positive count
                  (processed ++ [.t]) (.f :: next :: tail)
                  runtime overflowTokens (by simp)
                  overflowTape overflowInput with
              ⟨overflowSteps, terminatorTape, overflowPath,
                terminatorRepresents, overflowBound⟩
            let terminatorProcessed :=
              processed ++
                List.replicate (count + 1) CNFToken.t
            have terminatorTokens :
                CNFToNANDWorkspace.formulaTokens formula =
                  terminatorProcessed ++ .f :: next :: tail := by
              simpa [terminatorProcessed, List.replicate_succ,
                List.append_assoc] using tokens
            have terminatorInput :
                ScanRepresents
                  (firstBitRef .emit
                    (overflowState positive)).startState
                  (CNFToNANDWorkspace.capacity formula)
                  runtime.scratch runtime.registers runtime.checks
                  (scanBeforeCells
                    (CNFToNANDWorkspace.formulaTokens formula)
                    terminatorProcessed)
                  (scanAfterCells .f (next :: tail))
                  runtime.targetTokens terminatorTape := by
              simpa [terminatorProcessed, scanAfterCells,
                carrierGateCells, carrierGateCellsFor,
                PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
                List.replicate_succ, List.append_assoc] using
                terminatorRepresents
            have scratchCapacity :
                runtime.scratch <
                  CNFToNANDWorkspace.capacity formula := by
              rw [equal]
              exact inputCapacity
            have invalidOutput :
                runtime.registers.outputIndex + 1 ≤
                  CNFToNANDWorkspace.capacity formula := by
              cases positive <;>
                simp [validLiteralOutputGrowth] at outputBound ⊢ <;>
                omega
            rcases
                emit_overflow_terminator_path formula positive
                  terminatorProcessed next tail runtime
                  terminatorTokens fits scratchCapacity invalidOutput
                  terminatorTape terminatorInput with
              ⟨terminatorSteps, finalTape, terminatorPath,
                finalRepresents, terminatorBound⟩
            have prefixPath :
                AcceptPath graph
                  (.node
                    (firstBitRef .emit (inRangeState positive)))
                  (.node
                    (firstBitRef .emit (overflowState positive)))
                  (equalSteps + overflowSteps)
                  initialTape terminatorTape :=
              AcceptPath.trans graph _ _ _ _ _ _ _ _
                equalPath overflowPath
            refine
              ⟨equalSteps + overflowSteps + terminatorSteps,
                finalTape,
                AcceptPath.trans graph _ _ _ _ _ _ _ _
                  prefixPath terminatorPath, ?_, ?_⟩
            · have resultEq :
                  unaryLiteralResult positive (count + 1) runtime =
                    invalidLiteralResult runtime := by
                have notLess :
                    ¬runtime.scratch + (count + 1) <
                      runtime.registers.inputCount := by
                  omega
                have minEq :
                    min (runtime.scratch + (count + 1))
                        runtime.registers.inputCount =
                      runtime.registers.inputCount :=
                  Nat.min_eq_right (by omega)
                have scannedEq :
                    { runtime with
                        scratch :=
                          min (runtime.scratch + (count + 1))
                            runtime.registers.inputCount } =
                      runtime := by
                  rw [minEq, ← equal]
                unfold unaryLiteralResult
                rw [scannedEq]
                simp [notLess]
              simpa [resultEq, terminatorProcessed,
                List.replicate_succ, List.append_assoc] using
                finalRepresents
            · have overflowBound' :
                  overflowSteps ≤
                    overflowTRunCost formula count
                      (processed ++ [.t]) (.f :: next :: tail) :=
                overflowBound
              have terminatorBound' :
                  terminatorSteps ≤
                    overflowTerminatorCost formula
                      (processed ++
                        List.replicate (count + 1) CNFToken.t)
                      runtime
                      (markedSource
                        (CNFToNANDWorkspace.formulaTokens formula)
                        (processed ++
                          List.replicate (count + 1) CNFToken.t)
                        .f (next :: tail)) := by
                simpa [terminatorProcessed] using terminatorBound
              simp only [unaryLiteralCost]
              rw [show
                List.replicate count CNFToken.t ++
                    .f :: next :: tail =
                  nextToken :: tokenTail by
                exact remainderEq]
              simp [less]
              omega

private def literalSignCost
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (count : Nat)
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime) : Nat :=
  match count with
  | 0 =>
      signStepCost formula positive processed .f
        (next :: tail) runtime
  | remaining + 1 =>
      signStepCost formula positive processed .t
        (List.replicate remaining CNFToken.t ++
          .f :: next :: tail) runtime

private theorem literalSignCost_zero
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime) :
    literalSignCost formula positive processed 0 next tail runtime =
      signStepCost formula positive processed .f (next :: tail) runtime := by
  rfl

private theorem literalSignCost_succ
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (remaining : Nat)
    (next : CNFToken) (tail : List CNFToken) (runtime : Runtime) :
    literalSignCost formula positive processed (Nat.succ remaining)
        next tail runtime =
      signStepCost formula positive processed .t
        (List.replicate remaining CNFToken.t ++ .f :: next :: tail)
        runtime := by
  rfl

private theorem emit_sign_less_literal_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (count : Nat)
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ signToken positive ::
          List.replicate count .t ++ .f :: next :: tail)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (positiveWidth : 0 < runtime.registers.inputCount)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (signToken positive ::
              List.replicate count .t ++ .f :: next :: tail) ++
          carrierFooterCells)
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .emit .clause))
        (.node (firstBitRef .emit (inRangeState positive)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit (inRangeState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [signToken positive]))
        (carrierGateCells
            (List.replicate count .t ++ .f :: next :: tail) ++
          carrierFooterCells)
        (resetLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        literalSignCost formula positive processed count
          next tail runtime := by
  cases count with
  | zero =>
      have input :
          ScanRepresents (firstBitRef .emit .clause).startState
            (CNFToNANDWorkspace.capacity formula)
            runtime.scratch runtime.registers runtime.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells (signToken positive)
              (.f :: next :: tail))
            runtime.targetTokens initialTape := by
        simpa [scanAfterCells, carrierGateCells, carrierGateCellsFor,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells]
          using represents
      rcases
          emit_sign_less_path formula positive processed .f
            (next :: tail) runtime
            (by simpa using tokens)
            fits positiveWidth scratchBound initialTape input with
        ⟨steps, finalTape, path, finalRepresents, bounded⟩
      exact
        ⟨steps, finalTape, path,
          by simpa [scanAfterCells, carrierGateCells,
            carrierGateCellsFor,
            PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells]
            using finalRepresents,
          by simpa [literalSignCost] using bounded⟩
  | succ remaining =>
      have input :
          ScanRepresents (firstBitRef .emit .clause).startState
            (CNFToNANDWorkspace.capacity formula)
            runtime.scratch runtime.registers runtime.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells (signToken positive)
              (.t ::
                (List.replicate remaining CNFToken.t ++
                  .f :: next :: tail)))
            runtime.targetTokens initialTape := by
        simpa [List.replicate_succ, scanAfterCells,
          carrierGateCells, carrierGateCellsFor,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
          List.append_assoc] using represents
      rcases
          emit_sign_less_path formula positive processed .t
            (List.replicate remaining CNFToken.t ++
              .f :: next :: tail)
            runtime
            (by simpa [List.replicate_succ,
              List.append_assoc] using tokens)
            fits positiveWidth scratchBound initialTape input with
        ⟨steps, finalTape, path, finalRepresents, bounded⟩
      exact
        ⟨steps, finalTape, path,
          by simpa [List.replicate_succ, scanAfterCells,
            carrierGateCells, carrierGateCellsFor,
            PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
            List.append_assoc] using finalRepresents,
          by simpa [literalSignCost] using bounded⟩

private theorem emit_sign_equal_literal_path
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (count : Nat)
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ signToken positive ::
          List.replicate count .t ++ .f :: next :: tail)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (zeroWidth : runtime.registers.inputCount = 0)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (signToken positive ::
              List.replicate count .t ++ .f :: next :: tail) ++
          carrierFooterCells)
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .emit .clause))
        (.node (firstBitRef .emit (overflowState positive)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit (overflowState positive)).startState
        (CNFToNANDWorkspace.capacity formula)
        (resetLiteralResult runtime).scratch
        (resetLiteralResult runtime).registers
        (resetLiteralResult runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [signToken positive]))
        (carrierGateCells
            (List.replicate count .t ++ .f :: next :: tail) ++
          carrierFooterCells)
        (resetLiteralResult runtime).targetTokens finalTape ∧
      steps ≤
        literalSignCost formula positive processed count
          next tail runtime := by
  cases count with
  | zero =>
      have input :
          ScanRepresents (firstBitRef .emit .clause).startState
            (CNFToNANDWorkspace.capacity formula)
            runtime.scratch runtime.registers runtime.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells (signToken positive)
              (.f :: next :: tail))
            runtime.targetTokens initialTape := by
        simpa [scanAfterCells, carrierGateCells, carrierGateCellsFor,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells]
          using represents
      rcases
          emit_sign_equal_path formula positive processed .f
            (next :: tail) runtime
            (by simpa using tokens)
            fits zeroWidth scratchBound initialTape input with
        ⟨steps, finalTape, path, finalRepresents, bounded⟩
      exact
        ⟨steps, finalTape, path,
          by simpa [scanAfterCells, carrierGateCells,
            carrierGateCellsFor,
            PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells]
            using finalRepresents,
          by simpa [literalSignCost] using bounded⟩
  | succ remaining =>
      have input :
          ScanRepresents (firstBitRef .emit .clause).startState
            (CNFToNANDWorkspace.capacity formula)
            runtime.scratch runtime.registers runtime.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells (signToken positive)
              (.t ::
                (List.replicate remaining CNFToken.t ++
                  .f :: next :: tail)))
            runtime.targetTokens initialTape := by
        simpa [List.replicate_succ, scanAfterCells,
          carrierGateCells, carrierGateCellsFor,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
          List.append_assoc] using represents
      rcases
          emit_sign_equal_path formula positive processed .t
            (List.replicate remaining CNFToken.t ++
              .f :: next :: tail)
            runtime
            (by simpa [List.replicate_succ,
              List.append_assoc] using tokens)
            fits zeroWidth scratchBound initialTape input with
        ⟨steps, finalTape, path, finalRepresents, bounded⟩
      exact
        ⟨steps, finalTape, path,
          by simpa [List.replicate_succ, scanAfterCells,
            carrierGateCells, carrierGateCellsFor,
            PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
            List.append_assoc] using finalRepresents,
          by simpa [literalSignCost] using bounded⟩

private theorem formulaVariableCount_lt_capacity
    (formula : CNFFormula) :
    formula.variableCount <
      CNFToNANDWorkspace.capacity formula := by
  have tokenLength :
      formula.variableCount + 1 ≤
        (CNFToNANDWorkspace.formulaTokens formula).length := by
    rw [CNFToNANDWorkspace.formulaTokens, encodeFormulaTokens,
      CookLevin.encodeCNFTokens_length]
    omega
  rw [CNFToNANDWorkspace.capacity_exact]
  omega

private theorem unaryLiteralResult_reset_eq_literalRuntime
    (width : Nat) (literal : CNFLiteral)
    (runtime : Runtime)
    (inputCount : runtime.registers.inputCount = width) :
    unaryLiteralResult literal.positive literal.variableIndex
        (resetLiteralResult runtime) =
      literalRuntime width literal runtime := by
  by_cases valid : literal.variableIndex < width
  · rw [literalRuntime_of_valid _ _ _ valid]
    have less :
        literal.variableIndex <
          runtime.registers.inputCount := by
      simpa [inputCount] using valid
    have minEq :
        min literal.variableIndex runtime.registers.inputCount =
          literal.variableIndex := by
      exact Nat.min_eq_left (Nat.le_of_lt less)
    unfold unaryLiteralResult
    simp [resetLiteralResult, less, minEq]
  · have invalid : width ≤ literal.variableIndex :=
      Nat.le_of_not_gt valid
    rw [literalRuntime_of_invalid _ _ _ invalid]
    have notLess :
        ¬literal.variableIndex <
          runtime.registers.inputCount := by
      simpa [inputCount] using valid
    have minEq :
        min literal.variableIndex runtime.registers.inputCount =
          width := by
      rw [inputCount]
      exact Nat.min_eq_right invalid
    unfold unaryLiteralResult
    simp [resetLiteralResult, notLess, minEq]

private def literalCost
    (formula : CNFFormula) (processed : List CNFToken)
    (literal : CNFLiteral) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime) : Nat :=
  let afterSign :=
    processed ++ [signToken literal.positive]
  let reset := resetLiteralResult runtime
  let terminatorProcessed :=
    afterSign ++
      List.replicate literal.variableIndex CNFToken.t
  literalSignCost formula literal.positive processed
      literal.variableIndex next tail runtime +
    unaryLiteralCost formula literal.positive
      literal.variableIndex afterSign reset next tail +
    overflowTRunCost formula literal.variableIndex
      afterSign (.f :: next :: tail) +
    overflowTerminatorCost formula terminatorProcessed reset
      (markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        terminatorProcessed .f (next :: tail))

private theorem emit_literal_path
    (formula : CNFFormula) (processed : List CNFToken)
    (literal : CNFLiteral) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeLiteralTokens literal ++ next :: tail)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (inputCount :
      runtime.registers.inputCount = formula.variableCount)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (outputBound :
      runtime.registers.outputIndex + 2 ≤
        CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (encodeLiteralTokens literal ++ next :: tail) ++
          carrierFooterCells)
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .emit .clause))
        (.node (firstBitRef .emit .clause))
        steps initialTape finalTape ∧
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        (literalRuntime formula.variableCount literal runtime).scratch
        (literalRuntime formula.variableCount literal runtime).registers
        (literalRuntime formula.variableCount literal runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ encodeLiteralTokens literal))
        (scanAfterCells next tail)
        (literalRuntime formula.variableCount literal runtime).targetTokens
        finalTape ∧
      steps ≤
        literalCost formula processed literal next tail runtime := by
  let afterSign :=
    processed ++ [signToken literal.positive]
  let reset := resetLiteralResult runtime
  let terminatorProcessed :=
    afterSign ++
      List.replicate literal.variableIndex CNFToken.t
  have expandedTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ signToken literal.positive ::
          List.replicate literal.variableIndex .t ++
            .f :: next :: tail := by
    simpa [encodeLiteralTokens, signToken,
      encodeUnaryTokens_eq_replicate, List.append_assoc] using tokens
  have expandedRepresents :
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (signToken literal.positive ::
              List.replicate literal.variableIndex .t ++
                .f :: next :: tail) ++
          carrierFooterCells)
        runtime.targetTokens initialTape := by
    simpa [encodeLiteralTokens, signToken,
      encodeUnaryTokens_eq_replicate, List.append_assoc] using represents
  by_cases zeroWidth : runtime.registers.inputCount = 0
  · rcases
        emit_sign_equal_literal_path formula literal.positive
          processed literal.variableIndex next tail runtime
          expandedTokens fits zeroWidth scratchBound
          initialTape expandedRepresents with
      ⟨signSteps, overflowTape, signPath, overflowRepresents,
        signBound⟩
    have overflowTokens :
        CNFToNANDWorkspace.formulaTokens formula =
          afterSign ++
            List.replicate literal.variableIndex .t ++
              .f :: next :: tail := by
      simpa [afterSign, List.append_assoc] using expandedTokens
    have overflowInput :
        ScanRepresents
          (firstBitRef .emit
            (overflowState literal.positive)).startState
          (CNFToNANDWorkspace.capacity formula)
          reset.scratch reset.registers reset.checks
          (scanBeforeCells
            (CNFToNANDWorkspace.formulaTokens formula) afterSign)
          (carrierGateCells
              (List.replicate literal.variableIndex .t ++
                .f :: next :: tail) ++
            carrierFooterCells)
          reset.targetTokens overflowTape := by
      simpa [afterSign, reset] using overflowRepresents
    rcases
        emit_overflow_t_run_path formula literal.positive
          literal.variableIndex afterSign (.f :: next :: tail)
          reset overflowTokens (by simp)
          overflowTape overflowInput with
      ⟨overflowSteps, terminatorTape, overflowPath,
        terminatorRepresents, overflowBound⟩
    have terminatorTokens :
        CNFToNANDWorkspace.formulaTokens formula =
          terminatorProcessed ++ .f :: next :: tail := by
      simpa [terminatorProcessed, List.append_assoc] using
        overflowTokens
    have terminatorInput :
        ScanRepresents
          (firstBitRef .emit
            (overflowState literal.positive)).startState
          (CNFToNANDWorkspace.capacity formula)
          reset.scratch reset.registers reset.checks
          (scanBeforeCells
            (CNFToNANDWorkspace.formulaTokens formula)
            terminatorProcessed)
          (scanAfterCells .f (next :: tail))
          reset.targetTokens terminatorTape := by
      simpa [terminatorProcessed, scanAfterCells,
        carrierGateCells, carrierGateCellsFor,
        PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
        List.append_assoc] using terminatorRepresents
    have resetFits :
        LedgerFits (CNFToNANDWorkspace.capacity formula)
          reset.registers := by
      simpa [reset, resetLiteralResult] using fits
    have resetScratch :
        reset.scratch < CNFToNANDWorkspace.capacity formula := by
      simp [reset, resetLiteralResult]
      exact Nat.zero_lt_of_lt
        (formulaVariableCount_lt_capacity formula)
    have invalidOutput :
        reset.registers.outputIndex + 1 ≤
          CNFToNANDWorkspace.capacity formula := by
      simp [reset, resetLiteralResult] at outputBound ⊢
      omega
    rcases
        emit_overflow_terminator_path formula literal.positive
          terminatorProcessed next tail reset terminatorTokens
          resetFits resetScratch invalidOutput
          terminatorTape terminatorInput with
      ⟨terminatorSteps, finalTape, terminatorPath,
        finalRepresents, terminatorBound⟩
    have prefixPath :
        AcceptPath graph (.node (firstBitRef .emit .clause))
          (.node
            (firstBitRef .emit
              (overflowState literal.positive)))
          (signSteps + overflowSteps)
          initialTape terminatorTape :=
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        signPath overflowPath
    refine
      ⟨signSteps + overflowSteps + terminatorSteps,
        finalTape,
        AcceptPath.trans graph _ _ _ _ _ _ _ _
          prefixPath terminatorPath, ?_, ?_⟩
    · have formulaZero :
          formula.variableCount = 0 := by
        rw [← inputCount]
        exact zeroWidth
      have invalid :
          formula.variableCount ≤ literal.variableIndex := by
        simp [formulaZero]
      have runtimeEq :
          literalRuntime formula.variableCount literal runtime =
            invalidLiteralResult reset := by
        rw [literalRuntime_of_invalid _ _ _ invalid]
        simp [formulaZero, reset, resetLiteralResult]
      simpa [runtimeEq, terminatorProcessed, afterSign,
        encodeLiteralTokens, signToken,
        encodeUnaryTokens_eq_replicate,
        List.append_assoc] using finalRepresents
    · have signBound' :
          signSteps ≤
            literalSignCost formula literal.positive processed
              literal.variableIndex next tail runtime :=
        signBound
      have overflowBound' :
          overflowSteps ≤
            overflowTRunCost formula literal.variableIndex
              afterSign (.f :: next :: tail) :=
        overflowBound
      have terminatorBound' :
          terminatorSteps ≤
            overflowTerminatorCost formula terminatorProcessed reset
              (markedSource
                (CNFToNANDWorkspace.formulaTokens formula)
                terminatorProcessed .f (next :: tail)) :=
        terminatorBound
      dsimp [afterSign] at overflowBound'
      dsimp [terminatorProcessed, afterSign, reset] at terminatorBound'
      unfold literalCost
      dsimp only
      omega
  · have positiveWidth :
        0 < runtime.registers.inputCount := Nat.pos_of_ne_zero zeroWidth
    rcases
        emit_sign_less_literal_path formula literal.positive
          processed literal.variableIndex next tail runtime
          expandedTokens fits positiveWidth scratchBound
          initialTape expandedRepresents with
      ⟨signSteps, unaryTape, signPath, unaryRepresents,
        signBound⟩
    have unaryTokens :
        CNFToNANDWorkspace.formulaTokens formula =
          afterSign ++
            List.replicate literal.variableIndex .t ++
              .f :: next :: tail := by
      simpa [afterSign, List.append_assoc] using expandedTokens
    have unaryInput :
        ScanRepresents
          (firstBitRef .emit
            (inRangeState literal.positive)).startState
          (CNFToNANDWorkspace.capacity formula)
          reset.scratch reset.registers reset.checks
          (scanBeforeCells
            (CNFToNANDWorkspace.formulaTokens formula) afterSign)
          (carrierGateCells
              (List.replicate literal.variableIndex .t ++
                .f :: next :: tail) ++
            carrierFooterCells)
          reset.targetTokens unaryTape := by
      simpa [afterSign, reset] using unaryRepresents
    have resetFits :
        LedgerFits (CNFToNANDWorkspace.capacity formula)
          reset.registers := by
      simpa [reset, resetLiteralResult] using fits
    have resetScratch :
        reset.scratch ≤ reset.registers.inputCount := by
      simp [reset, resetLiteralResult]
    have resetInputCapacity :
        reset.registers.inputCount <
          CNFToNANDWorkspace.capacity formula := by
      simpa [reset, resetLiteralResult, inputCount] using
        formulaVariableCount_lt_capacity formula
    have unaryOutput :
        reset.registers.outputIndex +
            validLiteralOutputGrowth literal.positive ≤
          CNFToNANDWorkspace.capacity formula := by
      cases positive : literal.positive <;>
        simp [reset, resetLiteralResult,
          validLiteralOutputGrowth, positive] at outputBound ⊢ <;>
        omega
    rcases
        emit_unary_literal_path formula literal.positive
          literal.variableIndex afterSign reset next tail
          unaryTokens resetFits resetScratch resetInputCapacity
          unaryOutput unaryTape unaryInput with
      ⟨unarySteps, finalTape, unaryPath, finalRepresents,
        unaryBound⟩
    refine
      ⟨signSteps + unarySteps, finalTape,
        AcceptPath.trans graph _ _ _ _ _ _ _ _
          signPath unaryPath, ?_, ?_⟩
    · have runtimeEq :
          unaryLiteralResult literal.positive literal.variableIndex
              reset =
            literalRuntime formula.variableCount literal runtime := by
        simpa [reset] using
          unaryLiteralResult_reset_eq_literalRuntime
            formula.variableCount literal runtime inputCount
      simpa [runtimeEq, afterSign, encodeLiteralTokens,
        signToken, encodeUnaryTokens_eq_replicate,
        List.append_assoc] using finalRepresents
    · have signBound' :
          signSteps ≤
            literalSignCost formula literal.positive processed
              literal.variableIndex next tail runtime :=
        signBound
      have unaryBound' :
          unarySteps ≤
            unaryLiteralCost formula literal.positive
              literal.variableIndex afterSign reset next tail :=
        unaryBound
      dsimp [afterSign, reset] at unaryBound'
      unfold literalCost
      dsimp only
      omega

private theorem literalEmitGateCount_le_two
    (width : Nat) (literal : CNFLiteral) :
    literalEmitGateCount width literal ≤ 2 := by
  unfold literalEmitGateCount
  by_cases valid : literal.variableIndex < width <;>
    cases positive : literal.positive <;>
      simp [valid, positive]

private theorem literalRuntime_outputIndex
    (width : Nat) (literal : CNFLiteral) (runtime : Runtime) :
    (literalRuntime width literal runtime).registers.outputIndex =
      runtime.registers.outputIndex +
        literalEmitGateCount width literal := by
  unfold literalRuntime literalEmitGateCount
  by_cases valid : literal.variableIndex < width <;>
    cases positive : literal.positive <;>
      simp [valid, positive, positiveLiteralResult,
        negativeLiteralResult, invalidLiteralResult,
        advanceOutputIndexResult, pushGateAtResult,
        emitGateResult, emitSourceResult]

private theorem literalRuntime_fits
    (capacity width : Nat) (literal : CNFLiteral)
    (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (outputBound :
      runtime.registers.outputIndex +
          literalEmitGateCount width literal ≤ capacity) :
    LedgerFits capacity
      (literalRuntime width literal runtime).registers := by
  unfold literalEmitGateCount at outputBound
  unfold literalRuntime
  by_cases valid : literal.variableIndex < width <;>
    cases positive : literal.positive <;>
      simp [valid, positive, positiveLiteralResult,
        negativeLiteralResult, invalidLiteralResult,
        advanceOutputIndexResult, pushGateAtResult,
        emitGateResult, emitSourceResult] at outputBound ⊢ <;>
      exact
        { inputCount := fits.inputCount
          normalizedGateCount := fits.normalizedGateCount
          carrierWidth := fits.carrierWidth
          baseline := fits.baseline
          currentGate := fits.currentGate
          outputIndex := outputBound }

private theorem literalRuntime_inputCount
    (width : Nat) (literal : CNFLiteral) (runtime : Runtime) :
    (literalRuntime width literal runtime).registers.inputCount =
      runtime.registers.inputCount := by
  unfold literalRuntime
  by_cases valid : literal.variableIndex < width <;>
    cases positive : literal.positive <;>
      simp [valid, positive, positiveLiteralResult,
        negativeLiteralResult, invalidLiteralResult,
        advanceOutputIndexResult, pushGateAtResult,
        emitGateResult, emitSourceResult]

private theorem literalRuntime_currentGate
    (width : Nat) (literal : CNFLiteral) (runtime : Runtime) :
    (literalRuntime width literal runtime).registers.currentGate =
      runtime.registers.currentGate := by
  unfold literalRuntime
  by_cases valid : literal.variableIndex < width <;>
    cases positive : literal.positive <;>
      simp [valid, positive, positiveLiteralResult,
        negativeLiteralResult, invalidLiteralResult,
        advanceOutputIndexResult, pushGateAtResult,
        emitGateResult, emitSourceResult]

private theorem literalRuntime_scratch_lt
    (capacity width : Nat) (literal : CNFLiteral)
    (runtime : Runtime)
    (widthBound : width < capacity) :
    (literalRuntime width literal runtime).scratch < capacity := by
  unfold literalRuntime
  by_cases valid : literal.variableIndex < width <;>
    cases positive : literal.positive <;>
      simp [valid, positive, positiveLiteralResult,
        negativeLiteralResult, invalidLiteralResult,
        advanceOutputIndexResult, pushGateAtResult,
        emitGateResult, emitSourceResult] <;>
      omega

private def literalListCost
    (formula : CNFFormula) (processed : List CNFToken) :
    List CNFLiteral → CNFToken → List CNFToken → Runtime → Nat
  | [], _, _, _ => 0
  | literal :: rest, next, tail, runtime =>
      let remainder :=
        encodeLiteralListTokens rest ++ next :: tail
      match remainder with
      | [] => 0
      | successor :: successorTail =>
          literalCost formula processed literal successor
              successorTail runtime +
            literalListCost formula
              (processed ++ encodeLiteralTokens literal)
              rest next tail
              (literalRuntime formula.variableCount literal runtime)

set_option maxHeartbeats 100000 in
private theorem literalListCost_cons_of_remainder
    (formula : CNFFormula) (processed : List CNFToken)
    (literal : CNFLiteral) (rest : List CNFLiteral)
    (next : CNFToken) (tail : List CNFToken) (runtime : Runtime)
    (successor : CNFToken) (successorTail : List CNFToken)
    (remainderEq :
      encodeLiteralListTokens rest ++ next :: tail =
        successor :: successorTail) :
    literalListCost formula processed (literal :: rest)
        next tail runtime =
      literalCost formula processed literal successor successorTail runtime +
        literalListCost formula
          (processed ++ encodeLiteralTokens literal) rest next tail
          (literalRuntime formula.variableCount literal runtime) := by
  simp only [literalListCost, remainderEq]

private theorem emit_literal_list_path
    (formula : CNFFormula) (processed : List CNFToken)
    (literals : List CNFLiteral) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeLiteralListTokens literals ++
          next :: tail)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (inputCount :
      runtime.registers.inputCount = formula.variableCount)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (outputBound :
      runtime.registers.outputIndex + 2 * literals.length ≤
        CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (encodeLiteralListTokens literals ++ next :: tail) ++
          carrierFooterCells)
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .emit .clause))
        (.node (firstBitRef .emit .clause))
        steps initialTape finalTape ∧
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        (literalListRuntime formula.variableCount literals runtime).scratch
        (literalListRuntime
          formula.variableCount literals runtime).registers
        (literalListRuntime
          formula.variableCount literals runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ encodeLiteralListTokens literals))
        (scanAfterCells next tail)
        (literalListRuntime
          formula.variableCount literals runtime).targetTokens
        finalTape ∧
      steps ≤
        literalListCost formula processed literals next tail runtime := by
  induction literals generalizing processed runtime initialTape with
  | nil =>
      refine ⟨0, initialTape, .terminal _ _, ?_, ?_⟩
      · simpa [literalListRuntime, encodeLiteralListTokens,
          scanAfterCells,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
          carrierGateCells, carrierGateCellsFor,
          List.append_assoc] using represents
      · simp [literalListCost]
  | cons literal rest inductionHypothesis =>
      let remainder :=
        encodeLiteralListTokens rest ++ next :: tail
      have remainderNe : remainder ≠ [] := by
        simp [remainder]
      obtain ⟨successor, successorTail, remainderEq⟩ :=
        List.exists_cons_of_ne_nil remainderNe
      have literalTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ encodeLiteralTokens literal ++
              successor :: successorTail := by
        rw [encodeLiteralListTokens] at tokens
        simpa [remainder, remainderEq, List.append_assoc] using tokens
      have literalInput :
          ScanRepresents
            (firstBitRef .emit .clause).startState
            (CNFToNANDWorkspace.capacity formula)
            runtime.scratch runtime.registers runtime.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (carrierGateCells
                (encodeLiteralTokens literal ++
                  successor :: successorTail) ++
              carrierFooterCells)
            runtime.targetTokens initialTape := by
        simpa [encodeLiteralListTokens, remainder,
          remainderEq, List.append_assoc] using represents
      have firstOutput :
          runtime.registers.outputIndex + 2 ≤
            CNFToNANDWorkspace.capacity formula := by
        simp only [List.length_cons] at outputBound
        omega
      rcases
          emit_literal_path formula processed literal successor
            successorTail runtime literalTokens fits inputCount
            scratchBound firstOutput initialTape literalInput with
        ⟨literalSteps, literalTape, literalPath,
          literalRepresents, literalBound⟩
      have growth :=
        literalEmitGateCount_le_two
          formula.variableCount literal
      have literalOutput :
          (literalRuntime formula.variableCount literal runtime).registers.outputIndex =
            runtime.registers.outputIndex +
              literalEmitGateCount formula.variableCount literal :=
        literalRuntime_outputIndex
          formula.variableCount literal runtime
      have nextFits :
          LedgerFits (CNFToNANDWorkspace.capacity formula)
            (literalRuntime
              formula.variableCount literal runtime).registers := by
        exact literalRuntime_fits
          (CNFToNANDWorkspace.capacity formula)
          formula.variableCount literal runtime fits
          (Nat.le_trans
            (Nat.add_le_add_left growth
              runtime.registers.outputIndex)
            firstOutput)
      have nextInput :
          (literalRuntime
              formula.variableCount literal runtime).registers.inputCount =
            formula.variableCount := by
        rw [literalRuntime_inputCount]
        exact inputCount
      have nextScratch :
          (literalRuntime
              formula.variableCount literal runtime).scratch <
            CNFToNANDWorkspace.capacity formula :=
        literalRuntime_scratch_lt
          (CNFToNANDWorkspace.capacity formula)
          formula.variableCount literal runtime
          (formulaVariableCount_lt_capacity formula)
      have nextOutput :
          (literalRuntime
                formula.variableCount literal runtime).registers.outputIndex +
              2 * rest.length ≤
            CNFToNANDWorkspace.capacity formula := by
        simp only [List.length_cons] at outputBound
        rw [literalOutput]
        omega
      have recursiveTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            (processed ++ encodeLiteralTokens literal) ++
              encodeLiteralListTokens rest ++ next :: tail := by
        simpa [encodeLiteralListTokens, List.append_assoc] using tokens
      have recursiveInput :
          ScanRepresents
            (firstBitRef .emit .clause).startState
            (CNFToNANDWorkspace.capacity formula)
            (literalRuntime
              formula.variableCount literal runtime).scratch
            (literalRuntime
              formula.variableCount literal runtime).registers
            (literalRuntime
              formula.variableCount literal runtime).checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula)
              (processed ++ encodeLiteralTokens literal))
            (carrierGateCells
                (encodeLiteralListTokens rest ++ next :: tail) ++
              carrierFooterCells)
            (literalRuntime
              formula.variableCount literal runtime).targetTokens
            literalTape := by
        simpa [scanAfterCells,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
          carrierGateCells, carrierGateCellsFor,
          remainder, remainderEq,
          List.append_assoc] using literalRepresents
      rcases
          inductionHypothesis
            (processed ++ encodeLiteralTokens literal)
            (literalRuntime formula.variableCount literal runtime)
            recursiveTokens nextFits nextInput nextScratch nextOutput
            literalTape recursiveInput with
        ⟨restSteps, finalTape, restPath, finalRepresents,
          restBound⟩
      refine
        ⟨literalSteps + restSteps, finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            literalPath restPath, ?_, ?_⟩
      · simpa [literalListRuntime, encodeLiteralListTokens,
          List.append_assoc] using finalRepresents
      · simp [literalListCost, remainder, remainderEq]
        omega

private def literalCoordinate
    (width : Nat) (literal : CNFLiteral)
    (runtime : Runtime) : Nat :=
  runtime.registers.outputIndex +
    (if !literal.positive &&
        literal.variableIndex < width then 1 else 0)

private theorem literalRuntime_checks
    (width : Nat) (literal : CNFLiteral) (runtime : Runtime) :
    (literalRuntime width literal runtime).checks =
      runtime.checks ++
        [literalCoordinate width literal runtime] := by
  unfold literalRuntime literalCoordinate
  by_cases valid : literal.variableIndex < width <;>
    cases positive : literal.positive <;>
      simp [valid, positive, positiveLiteralResult,
        negativeLiteralResult, invalidLiteralResult,
        advanceOutputIndexResult, pushGateAtResult,
        emitGateResult, emitSourceResult]

private def literalListCoordinates
    (width : Nat) :
    List CNFLiteral → Runtime → List Nat
  | [], _ => []
  | literal :: rest, runtime =>
      literalCoordinate width literal runtime ::
        literalListCoordinates width rest
          (literalRuntime width literal runtime)

private theorem literalListCoordinates_length
    (width : Nat) (literals : List CNFLiteral)
    (runtime : Runtime) :
    (literalListCoordinates width literals runtime).length =
      literals.length := by
  induction literals generalizing runtime with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      simp [literalListCoordinates, inductionHypothesis]

private theorem literalListRuntime_checks
    (width : Nat) (literals : List CNFLiteral)
    (runtime : Runtime) :
    (literalListRuntime width literals runtime).checks =
      runtime.checks ++
        literalListCoordinates width literals runtime := by
  induction literals generalizing runtime with
  | nil =>
      simp [literalListRuntime, literalListCoordinates]
  | cons literal rest inductionHypothesis =>
      rw [literalListRuntime, inductionHypothesis,
        literalRuntime_checks]
      simp [literalListCoordinates, List.append_assoc]

private theorem literalListRuntime_outputIndex
    (width : Nat) (literals : List CNFLiteral)
    (runtime : Runtime) :
    (literalListRuntime width literals runtime).registers.outputIndex =
      runtime.registers.outputIndex +
        literalListGateCount width literals := by
  induction literals generalizing runtime with
  | nil =>
      simp [literalListRuntime, literalListGateCount]
  | cons literal rest inductionHypothesis =>
      rw [literalListRuntime, inductionHypothesis,
        literalRuntime_outputIndex]
      simp [literalListGateCount, Nat.add_assoc]

private theorem literalListRuntime_inputCount
    (width : Nat) (literals : List CNFLiteral)
    (runtime : Runtime) :
    (literalListRuntime width literals runtime).registers.inputCount =
      runtime.registers.inputCount := by
  induction literals generalizing runtime with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      rw [literalListRuntime, inductionHypothesis,
        literalRuntime_inputCount]

private theorem literalListRuntime_currentGate
    (width : Nat) (literals : List CNFLiteral)
    (runtime : Runtime) :
    (literalListRuntime width literals runtime).registers.currentGate =
      runtime.registers.currentGate := by
  induction literals generalizing runtime with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      rw [literalListRuntime, inductionHypothesis,
        literalRuntime_currentGate]

private theorem literalListRuntime_scratch_lt
    (capacity width : Nat) (literals : List CNFLiteral)
    (runtime : Runtime)
    (scratchBound : runtime.scratch < capacity)
    (widthBound : width < capacity) :
    (literalListRuntime width literals runtime).scratch < capacity := by
  induction literals generalizing runtime with
  | nil =>
      exact scratchBound
  | cons literal rest inductionHypothesis =>
      rw [literalListRuntime]
      exact inductionHypothesis
        (literalRuntime width literal runtime)
        (literalRuntime_scratch_lt
          capacity width literal runtime widthBound)

private theorem literalListRuntime_fits
    (capacity width : Nat) (literals : List CNFLiteral)
    (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (outputBound :
      runtime.registers.outputIndex +
          literalListGateCount width literals ≤ capacity) :
    LedgerFits capacity
      (literalListRuntime width literals runtime).registers := by
  induction literals generalizing runtime with
  | nil =>
      simpa [literalListRuntime] using fits
  | cons literal rest inductionHypothesis =>
      have firstBound :
          runtime.registers.outputIndex +
              literalEmitGateCount width literal ≤ capacity := by
        simp only [literalListGateCount] at outputBound
        omega
      have firstFits :=
        literalRuntime_fits capacity width literal runtime
          fits firstBound
      apply inductionHypothesis
      · exact firstFits
      · rw [literalRuntime_outputIndex]
        simp only [literalListGateCount] at outputBound
        omega

private theorem literalListCoordinates_lt_currentGate
    (width : Nat) (literals : List CNFLiteral)
    (runtime : Runtime)
    (bound :
      runtime.registers.outputIndex + 2 * literals.length ≤
        runtime.registers.currentGate) :
    ∀ coordinate,
      coordinate ∈ literalListCoordinates width literals runtime →
        coordinate < runtime.registers.currentGate := by
  induction literals generalizing runtime with
  | nil =>
      simp [literalListCoordinates]
  | cons literal rest inductionHypothesis =>
      intro coordinate member
      simp only [literalListCoordinates, List.mem_cons] at member
      rcases member with coordinateEq | member
      · subst coordinate
        unfold literalCoordinate
        split <;>
          simp only [List.length_cons] at bound <;>
          omega
      · have growth :=
          literalEmitGateCount_le_two width literal
        have nextBound :
            (literalRuntime width literal runtime).registers.outputIndex +
                2 * rest.length ≤
              (literalRuntime width literal runtime).registers.currentGate := by
          rw [literalRuntime_outputIndex,
            literalRuntime_currentGate]
          simp only [List.length_cons] at bound
          omega
        have less :=
          inductionHypothesis
            (literalRuntime width literal runtime)
            nextBound coordinate member
        simpa [literalRuntime_currentGate] using less

/-! ## Clause traversal and stack fold -/

private def clauseSeparatorCost
    (formula : CNFFormula) (processed : List CNFToken)
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime) : Nat :=
  let source :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      processed .sep (next :: tail)
  CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula)
      processed .sep +
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
      (CNFToNANDWorkspace.capacity formula)
      source runtime blockDescriptors[9].primitives +
    CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula)
      processed .sep

private theorem emit_clause_separator_path
    (formula : CNFFormula) (processed : List CNFToken)
    (next : CNFToken) (tail : List CNFToken)
    (state : GrammarState) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .sep :: next :: tail)
    (active : state ∈ activeGrammarStates)
    (valid : validGrammarToken state .sep = true)
    (post :
      postInstallEndpoint .emit state .sep =
        .node emitInitializeClauseRef)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (gateBound :
      runtime.registers.currentGate <
        CNFToNANDWorkspace.capacity formula)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit state).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .sep (next :: tail))
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .emit state))
        (.node (firstBitRef .emit .clause))
        steps initialTape finalTape ∧
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        (pushTotalGateResult runtime).scratch
        (pushTotalGateResult runtime).registers
        (pushTotalGateResult runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.sep]))
        (scanAfterCells next tail)
        (pushTotalGateResult runtime).targetTokens finalTape ∧
      steps ≤
        clauseSeparatorCost formula processed next tail runtime := by
  rcases
      CNFToNANDControllerCountTrace.token_read_install_path
        .emit formula processed .sep (next :: tail) state runtime
        tokens active valid initialTape represents with
    ⟨installedTape, installedPath, installedRepresents⟩
  have installedRepresents' :
      TapeRepresents
        emitInitializeClauseRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .sep (next :: tail))
        runtime.targetTokens installedTape := by
    exact
      tapeRepresents_at_state
        (by simpa using installedRepresents)
  let context :=
    markedSourceContext formula processed .sep
      (next :: tail) tokens
  rcases
      initializeClauseBlock_path
        (context := context) runtime fits scratchBound gateBound
        installedTape installedRepresents' with
    ⟨initializeSteps, initializedTape, initializePath,
      initializedRepresents, initializeBound⟩
  have restoreInput :
      TapeRepresents
        (restoreRef .emit .clause .sep).startState
        (CNFToNANDWorkspace.capacity formula)
        (pushTotalGateResult runtime).scratch
        (pushTotalGateResult runtime).registers
        (pushTotalGateResult runtime).checks
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .sep (next :: tail))
        (pushTotalGateResult runtime).targetTokens initializedTape := by
    simpa [context] using initializedRepresents
  rcases
      CNFToNANDControllerCountTrace.token_restore_advance_next_path
        .emit formula processed .sep next tail .clause
        (pushTotalGateResult runtime) tokens rfl
        initializedTape restoreInput with
    ⟨finalTape, restorePath, finalRepresents⟩
  let readSteps :=
    CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .sep
  let restoreSteps :=
    CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .sep
  have installedPath' :
      AcceptPath graph (.node (firstBitRef .emit state))
        (.node emitInitializeClauseRef) readSteps
        initialTape installedTape := by
    simpa [readSteps, post] using installedPath
  have prefixPath :
      AcceptPath graph (.node (firstBitRef .emit state))
        (.node (restoreRef .emit .clause .sep))
        (readSteps + initializeSteps)
        initialTape initializedTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      installedPath' initializePath
  refine
    ⟨readSteps + initializeSteps + restoreSteps, finalTape,
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        prefixPath restorePath, finalRepresents, ?_⟩
  unfold clauseSeparatorCost
  dsimp only
  have initializeBound' :
      initializeSteps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          (CNFToNANDWorkspace.capacity formula)
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed .sep (next :: tail))
          runtime blockDescriptors[9].primitives :=
    initializeBound
  simp only [readSteps, restoreSteps]
  omega

private theorem seedClauseResult_outputIndex
    (runtime : Runtime) :
    (seedClauseResult runtime).registers.outputIndex =
      runtime.registers.outputIndex + 1 := by
  simp [seedClauseResult, advanceOutputIndexResult,
    emitGateResult, emitSourceResult]

private theorem extendClauseResult_outputIndex
    (runtime : Runtime) :
    (extendClauseResult runtime).registers.outputIndex =
      runtime.registers.outputIndex + 2 := by
  simp [extendClauseResult, advanceOutputIndexResult,
    popCoordinateResult, emitGateResult, emitSourceResult]

private theorem finishNonemptyClauseResult_outputIndex
    (runtime : Runtime) :
    (finishNonemptyClauseResult runtime).registers.outputIndex =
      runtime.registers.outputIndex + 1 := by
  simp [finishNonemptyClauseResult, advanceOutputIndexResult,
    pushGateAtResult]

private theorem seedClauseResult_checks (runtime : Runtime) :
    (seedClauseResult runtime).checks = runtime.checks := by
  simp [seedClauseResult, advanceOutputIndexResult,
    emitGateResult, emitSourceResult]

private theorem extendClauseResult_checks (runtime : Runtime) :
    (extendClauseResult runtime).checks = runtime.checks := by
  simp [extendClauseResult, advanceOutputIndexResult,
    popCoordinateResult, emitGateResult, emitSourceResult]

private theorem finishNonemptyClauseResult_checks
    (runtime : Runtime) :
    (finishNonemptyClauseResult runtime).checks =
      runtime.checks ++ [runtime.registers.outputIndex] := by
  simp [finishNonemptyClauseResult, advanceOutputIndexResult,
    pushGateAtResult]

private theorem seedClauseResult_currentGate (runtime : Runtime) :
    (seedClauseResult runtime).registers.currentGate =
      runtime.registers.currentGate := by
  simp [seedClauseResult, advanceOutputIndexResult,
    emitGateResult, emitSourceResult]

private theorem extendClauseResult_currentGate (runtime : Runtime) :
    (extendClauseResult runtime).registers.currentGate =
      runtime.registers.currentGate := by
  simp [extendClauseResult, advanceOutputIndexResult,
    popCoordinateResult, emitGateResult, emitSourceResult]

private theorem finishNonemptyClauseResult_currentGate
    (runtime : Runtime) :
    (finishNonemptyClauseResult runtime).registers.currentGate =
      runtime.registers.currentGate := by
  simp [finishNonemptyClauseResult, advanceOutputIndexResult,
    pushGateAtResult]

private theorem clauseResult_fits_one
    (capacity : Nat) (runtime result : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (registers :
      result.registers =
        { runtime.registers with
          outputIndex := runtime.registers.outputIndex + 1 })
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity) :
    LedgerFits capacity result.registers := by
  rw [registers]
  exact
    { inputCount := fits.inputCount
      normalizedGateCount := fits.normalizedGateCount
      carrierWidth := fits.carrierWidth
      baseline := fits.baseline
      currentGate := fits.currentGate
      outputIndex := outputBound }

private theorem clauseResult_fits_two
    (capacity : Nat) (runtime result : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (registers :
      result.registers =
        { runtime.registers with
          outputIndex := runtime.registers.outputIndex + 2 })
    (outputBound :
      runtime.registers.outputIndex + 2 ≤ capacity) :
    LedgerFits capacity result.registers := by
  rw [registers]
  exact
    { inputCount := fits.inputCount
      normalizedGateCount := fits.normalizedGateCount
      carrierWidth := fits.carrierWidth
      baseline := fits.baseline
      currentGate := fits.currentGate
      outputIndex := outputBound }

private theorem seedClauseResult_registers (runtime : Runtime) :
    (seedClauseResult runtime).registers =
      { runtime.registers with
        outputIndex := runtime.registers.outputIndex + 1 } := by
  simp [seedClauseResult, advanceOutputIndexResult,
    emitGateResult, emitSourceResult]

private theorem extendClauseResult_registers (runtime : Runtime) :
    (extendClauseResult runtime).registers =
      { runtime.registers with
        outputIndex := runtime.registers.outputIndex + 2 } := by
  simp [extendClauseResult, advanceOutputIndexResult,
    popCoordinateResult, emitGateResult, emitSourceResult]

private theorem finishNonemptyClauseResult_registers
    (runtime : Runtime) :
    (finishNonemptyClauseResult runtime).registers =
      { runtime.registers with
        outputIndex := runtime.registers.outputIndex + 1 } := by
  simp [finishNonemptyClauseResult, advanceOutputIndexResult,
    pushGateAtResult]

private theorem seedClauseResult_scratch_lt
    (capacity : Nat) (runtime : Runtime)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity) :
    (seedClauseResult runtime).scratch < capacity := by
  simp [seedClauseResult, advanceOutputIndexResult,
    emitGateResult, emitSourceResult, EmissionSource.finalScratch]
  omega

private theorem extendClauseResult_scratch_lt
    (capacity : Nat) (runtime : Runtime)
    (outputBound :
      runtime.registers.outputIndex + 2 ≤ capacity) :
    (extendClauseResult runtime).scratch < capacity := by
  simp [extendClauseResult, advanceOutputIndexResult,
    popCoordinateResult, emitGateResult, emitSourceResult,
    EmissionSource.finalScratch]
  omega

private def clauseFoldLoopCost
    (capacity : Nat) (source : List WorkSymbol)
    (marker : Nat) :
    List Nat → Runtime → Nat
  | [], runtime =>
      TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[21].primitives +
        slotCompareSteps .currentGate capacity marker +
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source (popNewestResult runtime)
          blockDescriptors[23].primitives
  | value :: rest, runtime =>
      TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[21].primitives +
        slotCompareSteps .currentGate capacity value +
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source (popNewestResult runtime)
          blockDescriptors[22].primitives +
        clauseFoldLoopCost capacity source marker rest
          (extendClauseResult (popNewestResult runtime))

private theorem clause_fold_loop_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source)
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks =
        prior ++ marker :: pending.reverse)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (gateMarker :
      marker = runtime.registers.currentGate)
    (gateBound : runtime.registers.currentGate < capacity)
    (valuesBound :
      ∀ value, value ∈ pending →
        value < runtime.registers.currentGate)
    (outputBound :
      runtime.registers.outputIndex +
          (2 * pending.length + 1) ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents clausePopLoopRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node clausePopLoopRef)
        (.node (restoreRef .emit .clausesNonempty .finish))
        steps initialTape finalTape ∧
      TapeRepresents
        (restoreRef .emit .clausesNonempty .finish).startState
        capacity
        (clauseFoldLoopRuntime pending.length runtime).scratch
        (clauseFoldLoopRuntime pending.length runtime).registers
        (clauseFoldLoopRuntime pending.length runtime).checks
        source
        (clauseFoldLoopRuntime pending.length runtime).targetTokens
        finalTape ∧
      steps ≤
        clauseFoldLoopCost capacity source marker pending runtime := by
  induction pending generalizing prior runtime initialTape with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      have markerCapacity : marker ≤ capacity := by
        rw [gateMarker]
        exact Nat.le_of_lt gateBound
      rcases
          popCoordinateBlock_path 21 (by decide)
            clausePopLoopRef (.node clauseCompareLoopRef)
            (by rfl) (by rfl) (by rfl)
            (context := context) runtime prior marker fits
            scratchBound checks' markerCapacity
            clauseCompareLoopRef.startState initialTape represents with
        ⟨popSteps, popTape, popPath, popRepresents, popBound⟩
      let popped := popCoordinateResult runtime prior marker
      have poppedFits :
          LedgerFits capacity popped.registers := by
        simpa [popped, popCoordinateResult] using fits
      have poppedRepresents :
          TapeRepresents clauseCompareLoopRef.startState
            capacity popped.scratch popped.registers popped.checks
            (context.head :: context.tail) popped.targetTokens
            popTape := by
        simpa [popped, context.source_eq] using popRepresents
      have equal :
          popped.scratch =
            TargetEmitterLedger.slotValue
              popped.registers .currentGate := by
        simp [popped, popCoordinateResult,
          TargetEmitterLedger.slotValue, gateMarker]
      rcases
          slot_compare_equal_path .currentGate
            Address.clauseCompareLoop
            (.node clauseFinishNonemptyRef)
            (.node clauseExtendRef)
            clauseFinishNonemptyRef.startState
            capacity popped.scratch popped.registers popped.checks
            context.head context.tail popped.targetTokens popTape
            clauseCompareLoopNode_member poppedFits equal
            context.compareAllowed poppedRepresents with
        ⟨compareTape, comparePath, compareRepresents⟩
      have finishInput :
          TapeRepresents clauseFinishNonemptyRef.startState
            capacity popped.scratch popped.registers popped.checks
            source popped.targetTokens compareTape := by
        simpa [context.source_eq] using compareRepresents
      have finishOutput :
          popped.registers.outputIndex + 1 ≤ capacity := by
        simpa [popped, popCoordinateResult] using outputBound
      have poppedScratch : popped.scratch < capacity := by
        simp [popped, popCoordinateResult]
        omega
      rcases
          clauseFinishNonemptyBlock_path
            (context := context) popped poppedFits poppedScratch
            finishOutput compareTape finishInput with
        ⟨finishSteps, finalTape, finishPath,
          finalRepresents, finishBound⟩
      have prefixPath :
          AcceptPath graph (.node clausePopLoopRef)
            (.node clauseFinishNonemptyRef)
            (popSteps +
              slotCompareSteps .currentGate capacity marker)
            initialTape compareTape :=
        AcceptPath.trans graph _ _ _ _ _ _ _ _
          popPath comparePath
      refine
        ⟨popSteps +
            slotCompareSteps .currentGate capacity marker +
            finishSteps,
          finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            prefixPath finishPath, ?_, ?_⟩
      · have newest :
            popNewestResult runtime = popped := by
          exact popNewestResult_of_checks runtime prior marker checks'
        simpa [clauseFoldLoopRuntime, newest, popped] using
          finalRepresents
      · have newest :
            popNewestResult runtime = popped := by
          exact popNewestResult_of_checks runtime prior marker checks'
        unfold clauseFoldLoopCost
        rw [newest]
        omega
  | cons value rest inductionHypothesis =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      have valueLess :
          value < runtime.registers.currentGate :=
        valuesBound value (List.Mem.head rest)
      have valueCapacity : value ≤ capacity :=
        Nat.le_trans (Nat.le_of_lt valueLess)
          (Nat.le_of_lt gateBound)
      rcases
          popCoordinateBlock_path 21 (by decide)
            clausePopLoopRef (.node clauseCompareLoopRef)
            (by rfl) (by rfl) (by rfl)
            (context := context) runtime
            (prior ++ marker :: rest.reverse) value fits
            scratchBound checks' valueCapacity
            clauseCompareLoopRef.startState initialTape represents with
        ⟨popSteps, popTape, popPath, popRepresents, popBound⟩
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have poppedFits :
          LedgerFits capacity popped.registers := by
        simpa [popped, popCoordinateResult] using fits
      have poppedRepresents :
          TapeRepresents clauseCompareLoopRef.startState
            capacity popped.scratch popped.registers popped.checks
            (context.head :: context.tail) popped.targetTokens
            popTape := by
        simpa [popped, context.source_eq] using popRepresents
      have less :
          popped.scratch <
            TargetEmitterLedger.slotValue
              popped.registers .currentGate := by
        simpa [popped, popCoordinateResult,
          TargetEmitterLedger.slotValue] using valueLess
      rcases
          slot_compare_less_path .currentGate
            Address.clauseCompareLoop
            (.node clauseFinishNonemptyRef)
            (.node clauseExtendRef)
            clauseExtendRef.startState
            capacity popped.scratch popped.registers popped.checks
            context.head context.tail popped.targetTokens popTape
            clauseCompareLoopNode_member poppedFits less
            context.compareAllowed poppedRepresents with
        ⟨compareTape, comparePath, compareRepresents⟩
      have extendInput :
          TapeRepresents clauseExtendRef.startState
            capacity popped.scratch popped.registers popped.checks
            source popped.targetTokens compareTape := by
        simpa [context.source_eq] using compareRepresents
      have extendOutput :
          popped.registers.outputIndex + 2 ≤ capacity := by
        simpa [popped, popCoordinateResult] using
          (show runtime.registers.outputIndex + 2 ≤ capacity by
            simp only [List.length_cons] at outputBound
            omega)
      have poppedScratch : popped.scratch < capacity := by
        simpa [popped, popCoordinateResult] using
          Nat.lt_trans valueLess gateBound
      rcases
          clauseExtendBlock_path (context := context)
            layout popped poppedFits
            poppedScratch extendOutput compareTape extendInput with
        ⟨extendSteps, extendTape, extendPath,
          extendRepresents, extendBound⟩
      let extended := extendClauseResult popped
      have extendedFits :
          LedgerFits capacity extended.registers :=
        clauseResult_fits_two capacity popped extended poppedFits
          (by simpa [extended] using
            extendClauseResult_registers popped)
          extendOutput
      have extendedScratch : extended.scratch < capacity :=
        extendClauseResult_scratch_lt capacity popped extendOutput
      have extendedGate :
          marker = extended.registers.currentGate := by
        rw [extendClauseResult_currentGate]
        exact gateMarker
      have remainingBound :
          ∀ item, item ∈ rest →
            item < extended.registers.currentGate := by
        intro item member
        rw [extendClauseResult_currentGate]
        exact valuesBound item (List.Mem.tail value member)
      have remainingOutput :
          extended.registers.outputIndex +
              (2 * rest.length + 1) ≤ capacity := by
        dsimp [extended]
        rw [extendClauseResult_outputIndex]
        simp only [popped, popCoordinateResult]
        simp only [List.length_cons] at outputBound
        omega
      have extendedGateBound :
          extended.registers.currentGate < capacity := by
        rw [extendClauseResult_currentGate]
        simpa [popped, popCoordinateResult] using gateBound
      have extendedChecks :
          extended.checks =
            prior ++ marker :: rest.reverse := by
        rw [extendClauseResult_checks]
        simp [extended, popped, popCoordinateResult]
      have recursiveInput :
          TapeRepresents clausePopLoopRef.startState
            capacity extended.scratch extended.registers
            extended.checks source extended.targetTokens extendTape := by
        simpa [extended] using extendRepresents
      rcases
          inductionHypothesis prior extended extendedChecks
            extendedFits extendedScratch extendedGate
            extendedGateBound
            remainingBound remainingOutput extendTape recursiveInput with
        ⟨restSteps, finalTape, restPath,
          finalRepresents, restCostBound⟩
      let compareSteps :=
        slotCompareSteps .currentGate capacity value
      have comparePath' :
          AcceptPath graph (.node clauseCompareLoopRef)
            (.node clauseExtendRef) compareSteps
            popTape compareTape := by
        simpa [compareSteps, clauseCompareLoopRef,
          popped, popCoordinateResult] using
          comparePath
      have prefixPath :
          AcceptPath graph (.node clausePopLoopRef)
            (.node clausePopLoopRef)
            (popSteps + compareSteps + extendSteps)
            initialTape extendTape := by
        have first :
            AcceptPath graph (.node clausePopLoopRef)
              (.node clauseExtendRef)
              (popSteps + compareSteps)
              initialTape compareTape :=
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            popPath comparePath'
        exact
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            first extendPath
      refine
        ⟨popSteps + compareSteps + extendSteps + restSteps,
          finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            prefixPath restPath, ?_, ?_⟩
      · have newest :
            popNewestResult runtime = popped := by
          exact
            popNewestResult_of_checks runtime
              (prior ++ marker :: rest.reverse) value checks'
        simpa [clauseFoldLoopRuntime, newest, popped, extended] using
          finalRepresents
      · have newest :
            popNewestResult runtime = popped := by
          exact
            popNewestResult_of_checks runtime
              (prior ++ marker :: rest.reverse) value checks'
        unfold clauseFoldLoopCost
        rw [newest]
        dsimp [extended] at restCostBound
        dsimp [extended, compareSteps]
        omega

private def clauseFoldCost
    (capacity : Nat) (source : List WorkSymbol)
    (marker : Nat) :
    List Nat → Runtime → Nat
  | [], runtime =>
      TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[19].primitives +
        slotCompareSteps .currentGate capacity marker +
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source (popNewestResult runtime)
          blockDescriptors[24].primitives
  | value :: rest, runtime =>
      TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[19].primitives +
        slotCompareSteps .currentGate capacity value +
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source (popNewestResult runtime)
          blockDescriptors[20].primitives +
        clauseFoldLoopCost capacity source marker rest
          (seedClauseResult (popNewestResult runtime))

private theorem clause_fold_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source)
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks =
        prior ++ marker :: pending.reverse)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (gateMarker :
      marker = runtime.registers.currentGate)
    (gateBound : runtime.registers.currentGate < capacity)
    (valuesBound :
      ∀ value, value ∈ pending →
        value < runtime.registers.currentGate)
    (outputBound :
      runtime.registers.outputIndex +
          2 * pending.length ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents clausePopFirstRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node clausePopFirstRef)
        (.node (restoreRef .emit .clausesNonempty .finish))
        steps initialTape finalTape ∧
      TapeRepresents
        (restoreRef .emit .clausesNonempty .finish).startState
        capacity
        (clauseFoldRuntime pending.length runtime).scratch
        (clauseFoldRuntime pending.length runtime).registers
        (clauseFoldRuntime pending.length runtime).checks
        source
        (clauseFoldRuntime pending.length runtime).targetTokens
        finalTape ∧
      steps ≤
        clauseFoldCost capacity source marker pending runtime := by
  cases pending with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      have markerCapacity : marker ≤ capacity := by
        rw [gateMarker]
        exact Nat.le_of_lt gateBound
      rcases
          popCoordinateBlock_path 19 (by decide)
            clausePopFirstRef (.node clauseCompareFirstRef)
            (by rfl) (by rfl) (by rfl)
            (context := context) runtime prior marker fits
            scratchBound checks' markerCapacity
            clauseCompareFirstRef.startState initialTape represents with
        ⟨popSteps, popTape, popPath, popRepresents, popBound⟩
      let popped := popCoordinateResult runtime prior marker
      have poppedFits :
          LedgerFits capacity popped.registers := by
        simpa [popped, popCoordinateResult] using fits
      have poppedRepresents :
          TapeRepresents clauseCompareFirstRef.startState
            capacity popped.scratch popped.registers popped.checks
            (context.head :: context.tail) popped.targetTokens
            popTape := by
        simpa [popped, context.source_eq] using popRepresents
      have equal :
          popped.scratch =
            TargetEmitterLedger.slotValue
              popped.registers .currentGate := by
        simp [popped, popCoordinateResult,
          TargetEmitterLedger.slotValue, gateMarker]
      rcases
          slot_compare_equal_path .currentGate
            Address.clauseCompareFirst
            (.node clauseFinishEmptyRef) (.node clauseSeedRef)
            clauseFinishEmptyRef.startState
            capacity popped.scratch popped.registers popped.checks
            context.head context.tail popped.targetTokens popTape
            clauseCompareFirstNode_member poppedFits equal
            context.compareAllowed poppedRepresents with
        ⟨compareTape, comparePath, compareRepresents⟩
      have finishInput :
          TapeRepresents clauseFinishEmptyRef.startState
            capacity popped.scratch popped.registers popped.checks
            source popped.targetTokens compareTape := by
        simpa [context.source_eq] using compareRepresents
      have poppedScratch : popped.scratch < capacity := by
        simp [popped, popCoordinateResult]
        omega
      rcases
          clauseFinishEmptyBlock_path
            (context := context) popped poppedFits poppedScratch
            (by
              simpa [popped, popCoordinateResult] using gateBound)
            compareTape finishInput with
        ⟨finishSteps, finalTape, finishPath,
          finalRepresents, finishBound⟩
      have prefixPath :
          AcceptPath graph (.node clausePopFirstRef)
            (.node clauseFinishEmptyRef)
            (popSteps +
              slotCompareSteps .currentGate capacity marker)
            initialTape compareTape :=
        AcceptPath.trans graph _ _ _ _ _ _ _ _
          popPath comparePath
      refine
        ⟨popSteps +
            slotCompareSteps .currentGate capacity marker +
            finishSteps,
          finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            prefixPath finishPath, ?_, ?_⟩
      · have newest :
            popNewestResult runtime = popped :=
          popNewestResult_of_checks runtime prior marker checks'
        simpa [clauseFoldRuntime, newest, popped] using
          finalRepresents
      · have newest :
            popNewestResult runtime = popped :=
          popNewestResult_of_checks runtime prior marker checks'
        simp only [clauseFoldCost]
        rw [newest]
        omega
  | cons value rest =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      have valueLess :
          value < runtime.registers.currentGate :=
        valuesBound value (List.Mem.head rest)
      have valueCapacity : value ≤ capacity :=
        Nat.le_trans (Nat.le_of_lt valueLess)
          (Nat.le_of_lt gateBound)
      rcases
          popCoordinateBlock_path 19 (by decide)
            clausePopFirstRef (.node clauseCompareFirstRef)
            (by rfl) (by rfl) (by rfl)
            (context := context) runtime
            (prior ++ marker :: rest.reverse) value fits
            scratchBound checks' valueCapacity
            clauseCompareFirstRef.startState initialTape represents with
        ⟨popSteps, popTape, popPath, popRepresents, popBound⟩
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have poppedFits :
          LedgerFits capacity popped.registers := by
        simpa [popped, popCoordinateResult] using fits
      have poppedRepresents :
          TapeRepresents clauseCompareFirstRef.startState
            capacity popped.scratch popped.registers popped.checks
            (context.head :: context.tail) popped.targetTokens
            popTape := by
        simpa [popped, context.source_eq] using popRepresents
      have less :
          popped.scratch <
            TargetEmitterLedger.slotValue
              popped.registers .currentGate := by
        simpa [popped, popCoordinateResult,
          TargetEmitterLedger.slotValue] using valueLess
      rcases
          slot_compare_less_path .currentGate
            Address.clauseCompareFirst
            (.node clauseFinishEmptyRef) (.node clauseSeedRef)
            clauseSeedRef.startState
            capacity popped.scratch popped.registers popped.checks
            context.head context.tail popped.targetTokens popTape
            clauseCompareFirstNode_member poppedFits less
            context.compareAllowed poppedRepresents with
        ⟨compareTape, comparePath, compareRepresents⟩
      have seedInput :
          TapeRepresents clauseSeedRef.startState
            capacity popped.scratch popped.registers popped.checks
            source popped.targetTokens compareTape := by
        simpa [context.source_eq] using compareRepresents
      have seedOutput :
          popped.registers.outputIndex + 1 ≤ capacity := by
        simp only [List.length_cons] at outputBound
        simpa [popped, popCoordinateResult] using
          (show runtime.registers.outputIndex + 1 ≤ capacity by
            omega)
      have poppedScratch : popped.scratch < capacity := by
        simpa [popped, popCoordinateResult] using
          Nat.lt_trans valueLess gateBound
      rcases
          clauseSeedBlock_path (context := context)
            layout popped poppedFits
            poppedScratch seedOutput compareTape seedInput with
        ⟨seedSteps, seedTape, seedPath,
          seedRepresents, seedBound⟩
      let seeded := seedClauseResult popped
      have seededFits :
          LedgerFits capacity seeded.registers :=
        clauseResult_fits_one capacity popped seeded poppedFits
          (by simpa [seeded] using
            seedClauseResult_registers popped)
          seedOutput
      have seededScratch : seeded.scratch < capacity :=
        seedClauseResult_scratch_lt capacity popped seedOutput
      have seededGate :
          marker = seeded.registers.currentGate := by
        rw [seedClauseResult_currentGate]
        exact gateMarker
      have seededGateBound :
          seeded.registers.currentGate < capacity := by
        rw [seedClauseResult_currentGate]
        simpa [popped, popCoordinateResult] using gateBound
      have remainingBound :
          ∀ item, item ∈ rest →
            item < seeded.registers.currentGate := by
        intro item member
        rw [seedClauseResult_currentGate]
        simpa [popped, popCoordinateResult] using
          valuesBound item (List.Mem.tail value member)
      have remainingOutput :
          seeded.registers.outputIndex +
              (2 * rest.length + 1) ≤ capacity := by
        dsimp [seeded]
        rw [seedClauseResult_outputIndex]
        simp only [popped, popCoordinateResult]
        simp only [List.length_cons] at outputBound
        omega
      have seededChecks :
          seeded.checks =
            prior ++ marker :: rest.reverse := by
        rw [seedClauseResult_checks]
        simp [seeded, popped, popCoordinateResult]
      have recursiveInput :
          TapeRepresents clausePopLoopRef.startState
            capacity seeded.scratch seeded.registers seeded.checks
            source seeded.targetTokens seedTape := by
        simpa [seeded] using seedRepresents
      rcases
          clause_fold_loop_path (context := context)
            layout prior marker rest seeded
            seededChecks seededFits seededScratch seededGate
            seededGateBound remainingBound remainingOutput
            seedTape recursiveInput with
        ⟨loopSteps, finalTape, loopPath,
          finalRepresents, loopBound⟩
      let compareSteps :=
        slotCompareSteps .currentGate capacity value
      have comparePath' :
          AcceptPath graph (.node clauseCompareFirstRef)
            (.node clauseSeedRef) compareSteps popTape compareTape := by
        simpa [compareSteps, clauseCompareFirstRef,
          popped, popCoordinateResult] using
          comparePath
      have prefixPath :
          AcceptPath graph (.node clausePopFirstRef)
            (.node clausePopLoopRef)
            (popSteps + compareSteps + seedSteps)
            initialTape seedTape := by
        have first :
            AcceptPath graph (.node clausePopFirstRef)
              (.node clauseSeedRef)
              (popSteps + compareSteps)
              initialTape compareTape :=
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            popPath comparePath'
        exact
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            first seedPath
      refine
        ⟨popSteps + compareSteps + seedSteps + loopSteps,
          finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            prefixPath loopPath, ?_, ?_⟩
      · have newest :
            popNewestResult runtime = popped :=
          popNewestResult_of_checks runtime
            (prior ++ marker :: rest.reverse) value checks'
        simpa [clauseFoldRuntime, newest, popped, seeded] using
          finalRepresents
      · have newest :
            popNewestResult runtime = popped :=
          popNewestResult_of_checks runtime
            (prior ++ marker :: rest.reverse) value checks'
        simp only [clauseFoldCost]
        rw [newest]
        dsimp [seeded] at loopBound
        dsimp [seeded, compareSteps]
        omega

private def clausePathCost
    (formula : CNFFormula) (processed : List CNFToken)
    (state : GrammarState) (clause : List CNFLiteral)
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime) : Nat :=
  let initialized := pushTotalGateResult runtime
  let clauseProcessed := processed ++ [.sep]
  let listed :=
    literalListRuntime formula.variableCount clause initialized
  let coordinates :=
    literalListCoordinates formula.variableCount clause initialized
  let finishProcessed :=
    clauseProcessed ++ encodeLiteralListTokens clause
  let finishSource :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      finishProcessed .finish (next :: tail)
  let remainder :=
    encodeLiteralListTokens clause ++ .finish :: next :: tail
  clauseSeparatorCost formula processed
      (remainder.headD .f) remainder.tail
      runtime +
    literalListCost formula clauseProcessed clause .finish
      (next :: tail) initialized +
    CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula)
      finishProcessed .finish +
    clauseFoldCost (CNFToNANDWorkspace.capacity formula)
      finishSource listed.registers.currentGate
      coordinates.reverse listed +
    CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula)
      finishProcessed .finish

private theorem emit_clause_path
    (formula : CNFFormula) (processed : List CNFToken)
    (state : GrammarState) (clause : List CNFLiteral)
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeClauseTokens clause ++ next :: tail)
    (active : state ∈ activeGrammarStates)
    (valid : validGrammarToken state .sep = true)
    (post :
      postInstallEndpoint .emit state .sep =
        .node emitInitializeClauseRef)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (inputCount :
      runtime.registers.inputCount = formula.variableCount)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (gateExact :
      runtime.registers.currentGate =
        CNFToNANDWorkspace.compilerGateCount formula)
    (outputBound :
      runtime.registers.outputIndex +
          clauseGateCount formula.variableCount clause ≤
        runtime.registers.currentGate)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit state).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (encodeClauseTokens clause ++ next :: tail) ++
          carrierFooterCells)
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .emit state))
        (.node (firstBitRef .emit .clausesNonempty))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit .clausesNonempty).startState
        (CNFToNANDWorkspace.capacity formula)
        (clauseRuntime
          formula.variableCount clause runtime).scratch
        (clauseRuntime
          formula.variableCount clause runtime).registers
        (clauseRuntime
          formula.variableCount clause runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ encodeClauseTokens clause))
        (scanAfterCells next tail)
        (clauseRuntime
          formula.variableCount clause runtime).targetTokens
        finalTape ∧
      steps ≤
        clausePathCost formula processed state clause next tail
          runtime := by
  let initialized := pushTotalGateResult runtime
  let clauseProcessed := processed ++ [.sep]
  have gateBound :
      runtime.registers.currentGate <
        CNFToNANDWorkspace.capacity formula := by
    rw [gateExact]
    exact CNFToNANDWorkspace.compilerGateCount_lt_capacity formula
  let remainder :=
    encodeLiteralListTokens clause ++ .finish :: next :: tail
  have remainderNe : remainder ≠ [] := by
    simp [remainder]
  obtain ⟨first, rest, remainderEq⟩ :=
    List.exists_cons_of_ne_nil remainderNe
  have separatorTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .sep :: first :: rest := by
    simpa [encodeClauseTokens, remainder, remainderEq,
      List.append_assoc] using tokens
  have separatorInput :
      ScanRepresents (firstBitRef .emit state).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .sep (first :: rest))
        runtime.targetTokens initialTape := by
    simpa [encodeClauseTokens, scanAfterCells,
      PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
      carrierGateCells, carrierGateCellsFor,
      remainder, remainderEq, List.append_assoc] using represents
  rcases
      emit_clause_separator_path formula processed first rest state
        runtime separatorTokens active valid post fits scratchBound
        gateBound initialTape separatorInput with
    ⟨separatorSteps, separatorTape, separatorPath,
      separatorRepresents, separatorBound⟩
  have literalTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        clauseProcessed ++ encodeLiteralListTokens clause ++
          .finish :: next :: tail := by
    simpa [clauseProcessed, encodeClauseTokens,
      List.append_assoc] using tokens
  have literalInput :
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        initialized.scratch initialized.registers initialized.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          clauseProcessed)
        (carrierGateCells
            (encodeLiteralListTokens clause ++
              .finish :: next :: tail) ++
          carrierFooterCells)
        initialized.targetTokens separatorTape := by
    simpa [initialized, clauseProcessed, remainder,
      remainderEq, scanAfterCells,
      PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
      carrierGateCells, carrierGateCellsFor,
      List.append_assoc] using separatorRepresents
  have initializedFits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        initialized.registers := by
    simpa [initialized, pushTotalGateResult] using fits
  have initializedInput :
      initialized.registers.inputCount = formula.variableCount := by
    simpa [initialized, pushTotalGateResult] using inputCount
  have initializedScratch :
      initialized.scratch < CNFToNANDWorkspace.capacity formula := by
    simp [initialized, pushTotalGateResult]
    exact Nat.zero_lt_of_lt
      (formulaVariableCount_lt_capacity formula)
  have literalOutput :
      initialized.registers.outputIndex + 2 * clause.length ≤
        CNFToNANDWorkspace.capacity formula := by
    simp [initialized, pushTotalGateResult, clauseGateCount] at outputBound ⊢
    omega
  rcases
      emit_literal_list_path formula clauseProcessed clause
        .finish (next :: tail) initialized literalTokens
        initializedFits initializedInput initializedScratch
        literalOutput separatorTape literalInput with
    ⟨literalSteps, literalTape, literalPath,
      literalRepresents, literalBound⟩
  let listed :=
    literalListRuntime formula.variableCount clause initialized
  let finishProcessed :=
    clauseProcessed ++ encodeLiteralListTokens clause
  have finishTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        finishProcessed ++ .finish :: next :: tail := by
    simpa [finishProcessed, List.append_assoc] using literalTokens
  have finishInput :
      ScanRepresents (firstBitRef .emit .clause).startState
        (CNFToNANDWorkspace.capacity formula)
        listed.scratch listed.registers listed.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          finishProcessed)
        (scanAfterCells .finish (next :: tail))
        listed.targetTokens literalTape := by
    simpa [listed, finishProcessed] using literalRepresents
  rcases
      CNFToNANDControllerCountTrace.token_read_install_path
        .emit formula finishProcessed .finish (next :: tail)
        .clause listed finishTokens (by simp [activeGrammarStates])
        rfl literalTape finishInput with
    ⟨finishTape, finishReadPath, finishRepresents⟩
  let finishSource :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      finishProcessed .finish (next :: tail)
  have foldInput :
      TapeRepresents clausePopFirstRef.startState
        (CNFToNANDWorkspace.capacity formula)
        listed.scratch listed.registers listed.checks
        finishSource listed.targetTokens finishTape := by
    exact tapeRepresents_at_state
      (by simpa [finishSource] using finishRepresents)
  let coordinates :=
    literalListCoordinates formula.variableCount clause initialized
  have listedChecks :
      listed.checks =
        runtime.checks ++
          listed.registers.currentGate ::
            coordinates := by
    rw [literalListRuntime_checks]
    simp [listed, initialized, coordinates, pushTotalGateResult,
      literalListRuntime_currentGate, List.append_assoc]
  have foldChecks :
      listed.checks =
        runtime.checks ++
          listed.registers.currentGate ::
            coordinates.reverse.reverse := by
    simpa using listedChecks
  have listedFits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        listed.registers := by
    apply literalListRuntime_fits
    · exact initializedFits
    · simp [initialized, pushTotalGateResult, clauseGateCount] at outputBound ⊢
      omega
  have listedScratch :
      listed.scratch < CNFToNANDWorkspace.capacity formula := by
    apply literalListRuntime_scratch_lt
    · exact initializedScratch
    · exact formulaVariableCount_lt_capacity formula
  have listedGate :
      listed.registers.currentGate =
        runtime.registers.currentGate := by
    exact literalListRuntime_currentGate _ _ _
  have coordinatesBound :
      ∀ value, value ∈ coordinates.reverse →
        value < listed.registers.currentGate := by
    intro value member
    have originalMember := List.mem_reverse.mp member
    rw [listedGate]
    exact
      literalListCoordinates_lt_currentGate
        formula.variableCount clause initialized
        (by
          simp [initialized, pushTotalGateResult,
            clauseGateCount] at outputBound ⊢
          omega)
        value (by simpa [coordinates] using originalMember)
  have foldOutput :
      listed.registers.outputIndex +
          2 * coordinates.reverse.length ≤
        CNFToNANDWorkspace.capacity formula := by
    rw [literalListRuntime_outputIndex]
    rw [List.length_reverse,
      literalListCoordinates_length]
    simp [initialized, pushTotalGateResult,
      clauseGateCount] at outputBound ⊢
    omega
  let context :=
    markedSourceContext formula finishProcessed .finish
      (next :: tail) finishTokens
  let layout :=
    markedCursorLayout formula finishProcessed .finish
      (next :: tail) finishTokens
  rcases
      clause_fold_path (context := context) layout runtime.checks
        listed.registers.currentGate coordinates.reverse listed
        foldChecks listedFits listedScratch rfl
        (by
          rw [listedGate, gateExact]
          exact CNFToNANDWorkspace.compilerGateCount_lt_capacity formula)
        coordinatesBound foldOutput finishTape foldInput with
    ⟨foldSteps, foldedTape, foldPath,
      foldRepresents, foldBound⟩
  let folded := clauseFoldRuntime clause.length listed
  have restoreInput :
      TapeRepresents
        (restoreRef .emit .clausesNonempty .finish).startState
        (CNFToNANDWorkspace.capacity formula)
        folded.scratch folded.registers folded.checks
        finishSource folded.targetTokens foldedTape := by
    simpa [folded, coordinates,
      literalListCoordinates_length] using foldRepresents
  rcases
      CNFToNANDControllerCountTrace.token_restore_advance_next_path
        .emit formula finishProcessed .finish next tail
        .clausesNonempty folded finishTokens rfl
        foldedTape restoreInput with
    ⟨finalTape, restorePath, finalRepresents⟩
  let readSteps :=
    CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula)
      finishProcessed .finish
  let restoreSteps :=
    CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula)
      finishProcessed .finish
  have prefixOne :
      AcceptPath graph (.node (firstBitRef .emit state))
        (.node (firstBitRef .emit .clause))
        (separatorSteps + literalSteps)
        initialTape literalTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      separatorPath literalPath
  have prefixTwo :
      AcceptPath graph (.node (firstBitRef .emit state))
        (.node clausePopFirstRef)
        (separatorSteps + literalSteps + readSteps)
        initialTape finishTape := by
    exact AcceptPath.trans graph _ _ _ _ _ _ _ _
      prefixOne
      (by
        simpa [readSteps, postInstallEndpoint] using finishReadPath)
  have prefixThree :
      AcceptPath graph (.node (firstBitRef .emit state))
        (.node (restoreRef .emit .clausesNonempty .finish))
        (separatorSteps + literalSteps + readSteps + foldSteps)
        initialTape foldedTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      prefixTwo foldPath
  refine
    ⟨separatorSteps + literalSteps + readSteps +
        foldSteps + restoreSteps,
      finalTape,
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        prefixThree restorePath, ?_, ?_⟩
  · simpa [clauseRuntime, folded, listed, initialized,
      finishProcessed, clauseProcessed, encodeClauseTokens,
      List.append_assoc] using finalRepresents
  · unfold clausePathCost
    dsimp only
    have separatorBound' :
        separatorSteps ≤
          clauseSeparatorCost formula processed first rest runtime :=
      separatorBound
    have literalBound' :
        literalSteps ≤
          literalListCost formula clauseProcessed clause .finish
            (next :: tail) initialized :=
      literalBound
    have foldBound' :
        foldSteps ≤
          clauseFoldCost (CNFToNANDWorkspace.capacity formula)
            finishSource listed.registers.currentGate
            coordinates.reverse listed :=
      foldBound
    have firstEq : remainder.headD .f = first := by
      rw [remainderEq]
      rfl
    have restEq : remainder.tail = rest := by
      rw [remainderEq]
      rfl
    simp only [clauseProcessed, initialized] at literalBound'
    simp only [finishSource, finishProcessed, clauseProcessed,
      listed, coordinates, initialized] at foldBound'
    simp only [readSteps, restoreSteps, finishProcessed,
      clauseProcessed, listed, coordinates, initialized,
      finishSource]
    rw [firstEq, restEq]
    omega

@[simp] private theorem popNewestResult_registers
    (runtime : Runtime) :
    (popNewestResult runtime).registers = runtime.registers := rfl

@[simp] private theorem pushTotalGateResult_registers
    (runtime : Runtime) :
    (pushTotalGateResult runtime).registers = runtime.registers := rfl

private theorem literalRuntime_registers
    (width : Nat) (literal : CNFLiteral) (runtime : Runtime) :
    (literalRuntime width literal runtime).registers =
      { runtime.registers with
        outputIndex :=
          runtime.registers.outputIndex +
            literalEmitGateCount width literal } := by
  unfold literalRuntime literalEmitGateCount
  by_cases valid : literal.variableIndex < width <;>
    cases positive : literal.positive <;>
      simp [valid, positive, positiveLiteralResult,
        negativeLiteralResult, invalidLiteralResult,
        advanceOutputIndexResult, pushGateAtResult,
        emitGateResult, emitSourceResult]

private theorem literalListRuntime_registers
    (width : Nat) (literals : List CNFLiteral)
    (runtime : Runtime) :
    (literalListRuntime width literals runtime).registers =
      { runtime.registers with
        outputIndex :=
          runtime.registers.outputIndex +
            literalListGateCount width literals } := by
  induction literals generalizing runtime with
  | nil =>
      simp [literalListRuntime, literalListGateCount]
  | cons literal rest inductionHypothesis =>
      rw [literalListRuntime, inductionHypothesis,
        literalRuntime_registers]
      simp [literalListGateCount, Nat.add_assoc]

private theorem clauseFoldLoopRuntime_registers
    (count : Nat) (runtime : Runtime) :
    (clauseFoldLoopRuntime count runtime).registers =
      { runtime.registers with
        outputIndex :=
          runtime.registers.outputIndex + (2 * count + 1) } := by
  induction count generalizing runtime with
  | zero =>
      rw [clauseFoldLoopRuntime,
        finishNonemptyClauseResult_registers]
      simp
  | succ count inductionHypothesis =>
      rw [clauseFoldLoopRuntime, inductionHypothesis,
        extendClauseResult_registers]
      change
        { runtime.registers with
          outputIndex :=
            (runtime.registers.outputIndex + 2) +
              (2 * count + 1) } =
        { runtime.registers with
          outputIndex :=
            runtime.registers.outputIndex +
              (2 * (count + 1) + 1) }
      rw [show
        (runtime.registers.outputIndex + 2) +
              (2 * count + 1) =
            runtime.registers.outputIndex +
              (2 * (count + 1) + 1) by omega]

private theorem clauseFoldRuntime_registers
    (count : Nat) (runtime : Runtime) :
    (clauseFoldRuntime count runtime).registers =
      { runtime.registers with
        outputIndex :=
          runtime.registers.outputIndex + 2 * count } := by
  cases count with
  | zero =>
      simp [clauseFoldRuntime]
  | succ count =>
      rw [clauseFoldRuntime, clauseFoldLoopRuntime_registers,
        seedClauseResult_registers]
      change
        { runtime.registers with
          outputIndex :=
            (runtime.registers.outputIndex + 1) +
              (2 * count + 1) } =
        { runtime.registers with
          outputIndex :=
            runtime.registers.outputIndex + 2 * (count + 1) }
      rw [show
        (runtime.registers.outputIndex + 1) +
              (2 * count + 1) =
            runtime.registers.outputIndex + 2 * (count + 1) by omega]

private theorem clauseFoldLoopRuntime_outputIndex
    (count : Nat) (runtime : Runtime) :
    (clauseFoldLoopRuntime count runtime).registers.outputIndex =
      runtime.registers.outputIndex + (2 * count + 1) := by
  induction count generalizing runtime with
  | zero =>
      simpa using congrArg
        (fun registers => registers.outputIndex)
        (clauseFoldLoopRuntime_registers 0 runtime)
  | succ count inductionHypothesis =>
      simpa using congrArg
        (fun registers => registers.outputIndex)
        (clauseFoldLoopRuntime_registers (count + 1) runtime)

private theorem clauseFoldRuntime_outputIndex
    (count : Nat) (runtime : Runtime) :
    (clauseFoldRuntime count runtime).registers.outputIndex =
      runtime.registers.outputIndex + 2 * count := by
  simpa using congrArg
    (fun registers => registers.outputIndex)
    (clauseFoldRuntime_registers count runtime)

private theorem clauseFoldLoopRuntime_inputCount
    (count : Nat) (runtime : Runtime) :
    (clauseFoldLoopRuntime count runtime).registers.inputCount =
      runtime.registers.inputCount := by
  simpa using congrArg
    (fun registers => registers.inputCount)
    (clauseFoldLoopRuntime_registers count runtime)

private theorem clauseFoldRuntime_inputCount
    (count : Nat) (runtime : Runtime) :
    (clauseFoldRuntime count runtime).registers.inputCount =
      runtime.registers.inputCount := by
  simpa using congrArg
    (fun registers => registers.inputCount)
    (clauseFoldRuntime_registers count runtime)

private theorem clauseFoldLoopRuntime_currentGate
    (count : Nat) (runtime : Runtime) :
    (clauseFoldLoopRuntime count runtime).registers.currentGate =
      runtime.registers.currentGate := by
  simpa using congrArg
    (fun registers => registers.currentGate)
    (clauseFoldLoopRuntime_registers count runtime)

private theorem clauseFoldRuntime_currentGate
    (count : Nat) (runtime : Runtime) :
    (clauseFoldRuntime count runtime).registers.currentGate =
      runtime.registers.currentGate := by
  simpa using congrArg
    (fun registers => registers.currentGate)
    (clauseFoldRuntime_registers count runtime)

private theorem clauseFoldLoopRuntime_scratch
    (count : Nat) (runtime : Runtime) :
    (clauseFoldLoopRuntime count runtime).scratch = 0 := by
  induction count generalizing runtime with
  | zero =>
      simp [clauseFoldLoopRuntime, popNewestResult,
        popCoordinateResult, finishNonemptyClauseResult,
        advanceOutputIndexResult, pushGateAtResult]
  | succ count inductionHypothesis =>
      rw [clauseFoldLoopRuntime, inductionHypothesis]

private theorem clauseFoldRuntime_scratch
    (count : Nat) (runtime : Runtime) :
    (clauseFoldRuntime count runtime).scratch = 0 := by
  cases count with
  | zero =>
      simp [clauseFoldRuntime, popNewestResult,
        popCoordinateResult, pushTotalGateResult]
  | succ count =>
      rw [clauseFoldRuntime, clauseFoldLoopRuntime_scratch]

private theorem clauseRuntime_outputIndex
    (width : Nat) (clause : List CNFLiteral)
    (runtime : Runtime) :
    (clauseRuntime width clause runtime).registers.outputIndex =
      runtime.registers.outputIndex + clauseGateCount width clause := by
  unfold clauseRuntime
  rw [clauseFoldRuntime_outputIndex,
    literalListRuntime_outputIndex]
  simp [clauseGateCount]
  omega

private theorem clauseRuntime_inputCount
    (width : Nat) (clause : List CNFLiteral)
    (runtime : Runtime) :
    (clauseRuntime width clause runtime).registers.inputCount =
      runtime.registers.inputCount := by
  rw [clauseRuntime, clauseFoldRuntime_inputCount,
    literalListRuntime_inputCount]
  rfl

private theorem clauseRuntime_currentGate
    (width : Nat) (clause : List CNFLiteral)
    (runtime : Runtime) :
    (clauseRuntime width clause runtime).registers.currentGate =
      runtime.registers.currentGate := by
  rw [clauseRuntime, clauseFoldRuntime_currentGate,
    literalListRuntime_currentGate]
  rfl

private theorem clauseRuntime_scratch
    (width : Nat) (clause : List CNFLiteral)
    (runtime : Runtime) :
    (clauseRuntime width clause runtime).scratch = 0 := by
  rw [clauseRuntime, clauseFoldRuntime_scratch]

private theorem clauseRuntime_registers
    (width : Nat) (clause : List CNFLiteral)
    (runtime : Runtime) :
    (clauseRuntime width clause runtime).registers =
      { runtime.registers with
        outputIndex :=
          runtime.registers.outputIndex +
            clauseGateCount width clause } := by
  unfold clauseRuntime
  rw [clauseFoldRuntime_registers,
    literalListRuntime_registers]
  change
    { runtime.registers with
      outputIndex :=
        (runtime.registers.outputIndex +
            literalListGateCount width clause) +
          2 * clause.length } =
    { runtime.registers with
      outputIndex :=
        runtime.registers.outputIndex +
          clauseGateCount width clause }
  rw [show
    (runtime.registers.outputIndex +
          literalListGateCount width clause) +
        2 * clause.length =
      runtime.registers.outputIndex +
        clauseGateCount width clause by
    simp [clauseGateCount]
    omega]

private theorem clauseRuntime_fits
    (capacity width : Nat) (clause : List CNFLiteral)
    (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (outputBound :
      runtime.registers.outputIndex +
          clauseGateCount width clause ≤ capacity) :
    LedgerFits capacity
      (clauseRuntime width clause runtime).registers := by
  rw [clauseRuntime_registers]
  exact
    { inputCount := fits.inputCount
      normalizedGateCount := fits.normalizedGateCount
      carrierWidth := fits.carrierWidth
      baseline := fits.baseline
      currentGate := fits.currentGate
      outputIndex := outputBound }

private def clauseListPathCost
    (formula : CNFFormula) (processed : List CNFToken) :
    GrammarState → List (List CNFLiteral) →
      CNFToken → List CNFToken → Runtime → Nat
  | _, [], _, _, _ => 0
  | state, clause :: rest, next, tail, runtime =>
      let remainder :=
        encodeClauseListTokens rest ++ next :: tail
      clausePathCost formula processed state clause
          (remainder.headD .f) remainder.tail runtime +
        clauseListPathCost formula
          (processed ++ encodeClauseTokens clause)
          .clausesNonempty rest next tail
          (clauseRuntime formula.variableCount clause runtime)

private theorem emit_clause_list_path
    (formula : CNFFormula) (processed : List CNFToken)
    (state : GrammarState) (clauses : List (List CNFLiteral))
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeClauseListTokens clauses ++ next :: tail)
    (active : state ∈ activeGrammarStates)
    (valid : validGrammarToken state .sep = true)
    (post :
      postInstallEndpoint .emit state .sep =
        .node emitInitializeClauseRef)
    (fits :
      LedgerFits (CNFToNANDWorkspace.capacity formula)
        runtime.registers)
    (inputCount :
      runtime.registers.inputCount = formula.variableCount)
    (scratchBound :
      runtime.scratch < CNFToNANDWorkspace.capacity formula)
    (gateExact :
      runtime.registers.currentGate =
        CNFToNANDWorkspace.compilerGateCount formula)
    (outputBound :
      runtime.registers.outputIndex +
          clauseListGateCount formula.variableCount clauses ≤
        runtime.registers.currentGate)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit state).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (carrierGateCells
            (encodeClauseListTokens clauses ++ next :: tail) ++
          carrierFooterCells)
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .emit state))
        (.node (firstBitRef .emit
          (if clauses.isEmpty then state else .clausesNonempty)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit
          (if clauses.isEmpty then state else .clausesNonempty)).startState
        (CNFToNANDWorkspace.capacity formula)
        (clauseListRuntime
          formula.variableCount clauses runtime).scratch
        (clauseListRuntime
          formula.variableCount clauses runtime).registers
        (clauseListRuntime
          formula.variableCount clauses runtime).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ encodeClauseListTokens clauses))
        (scanAfterCells next tail)
        (clauseListRuntime
          formula.variableCount clauses runtime).targetTokens
        finalTape ∧
      steps ≤
        clauseListPathCost formula processed state clauses next tail
          runtime := by
  induction clauses generalizing processed state runtime initialTape with
  | nil =>
      refine ⟨0, initialTape, ?_, ?_, ?_⟩
      · simpa using
          (AcceptPath.terminal
            (.node (firstBitRef .emit state)) initialTape)
      · simpa [clauseListRuntime, encodeClauseListTokens,
          scanAfterCells,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
          carrierGateCells, carrierGateCellsFor,
          List.append_assoc] using represents
      · simp [clauseListPathCost]
  | cons clause restClauses inductionHypothesis =>
      let remainder :=
        encodeClauseListTokens restClauses ++ next :: tail
      have remainderNe : remainder ≠ [] := by simp [remainder]
      obtain ⟨successor, successorTail, remainderEq⟩ :=
        List.exists_cons_of_ne_nil remainderNe
      have clauseTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ encodeClauseTokens clause ++
              successor :: successorTail := by
        simpa [encodeClauseListTokens, remainder, remainderEq,
          List.append_assoc] using tokens
      have clauseInput :
          ScanRepresents (firstBitRef .emit state).startState
            (CNFToNANDWorkspace.capacity formula)
            runtime.scratch runtime.registers runtime.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (carrierGateCells
                (encodeClauseTokens clause ++
                  successor :: successorTail) ++
              carrierFooterCells)
            runtime.targetTokens initialTape := by
        simpa [encodeClauseListTokens, remainder, remainderEq,
          List.append_assoc] using represents
      have firstOutput :
          runtime.registers.outputIndex +
              clauseGateCount formula.variableCount clause ≤
            runtime.registers.currentGate := by
        simp only [clauseListGateCount] at outputBound
        omega
      rcases
          emit_clause_path formula processed state clause
            successor successorTail runtime clauseTokens active valid
            post fits inputCount scratchBound gateExact firstOutput
            initialTape clauseInput with
        ⟨clauseSteps, clauseTape, clausePath,
          clauseRepresents, clauseBound⟩
      let nextRuntime :=
        clauseRuntime formula.variableCount clause runtime
      have nextFits :
          LedgerFits (CNFToNANDWorkspace.capacity formula)
            nextRuntime.registers := by
        apply clauseRuntime_fits
        · exact fits
        · exact Nat.le_trans firstOutput
            (Nat.le_of_lt
              (by
                rw [gateExact]
                exact
                  CNFToNANDWorkspace.compilerGateCount_lt_capacity
                    formula))
      have nextInput :
          nextRuntime.registers.inputCount = formula.variableCount := by
        rw [clauseRuntime_inputCount]
        exact inputCount
      have nextScratch :
          nextRuntime.scratch <
            CNFToNANDWorkspace.capacity formula := by
        rw [clauseRuntime_scratch]
        exact Nat.zero_lt_of_lt
          (formulaVariableCount_lt_capacity formula)
      have nextGate :
          nextRuntime.registers.currentGate =
            CNFToNANDWorkspace.compilerGateCount formula := by
        rw [clauseRuntime_currentGate]
        exact gateExact
      have nextOutput :
          nextRuntime.registers.outputIndex +
              clauseListGateCount formula.variableCount restClauses ≤
            nextRuntime.registers.currentGate := by
        rw [clauseRuntime_outputIndex,
          clauseRuntime_currentGate]
        simp only [clauseListGateCount] at outputBound
        omega
      have recursiveTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            (processed ++ encodeClauseTokens clause) ++
              encodeClauseListTokens restClauses ++ next :: tail := by
        simpa [encodeClauseListTokens, List.append_assoc] using tokens
      have recursiveInput :
          ScanRepresents
            (firstBitRef .emit .clausesNonempty).startState
            (CNFToNANDWorkspace.capacity formula)
            nextRuntime.scratch nextRuntime.registers
            nextRuntime.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula)
              (processed ++ encodeClauseTokens clause))
            (carrierGateCells
                (encodeClauseListTokens restClauses ++
                  next :: tail) ++ carrierFooterCells)
            nextRuntime.targetTokens clauseTape := by
        simpa [nextRuntime, scanAfterCells,
          PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells,
          carrierGateCells, carrierGateCellsFor,
          remainder, remainderEq, List.append_assoc] using
          clauseRepresents
      rcases
          inductionHypothesis
            (processed ++ encodeClauseTokens clause)
            .clausesNonempty nextRuntime recursiveTokens
            (by simp [activeGrammarStates]) rfl rfl nextFits
            nextInput nextScratch nextGate nextOutput
            clauseTape recursiveInput with
        ⟨restSteps, finalTape, restPath,
          finalRepresents, restBound⟩
      have combined :
          AcceptPath graph (.node (firstBitRef .emit state))
            (.node (firstBitRef .emit
              (if restClauses.isEmpty
                then .clausesNonempty else .clausesNonempty)))
            (clauseSteps + restSteps) initialTape finalTape :=
        AcceptPath.trans graph _ _ _ _ _ _ _ _
          clausePath restPath
      refine
        ⟨clauseSteps + restSteps, finalTape, ?_, ?_, ?_⟩
      · simpa using combined
      · simpa [clauseListRuntime, encodeClauseListTokens,
          List.append_assoc] using finalRepresents
      · simp only [clauseListPathCost]
        have successorEq : remainder.headD .f = successor := by
          rw [remainderEq]
          rfl
        have successorTailEq : remainder.tail = successorTail := by
          rw [remainderEq]
          rfl
        rw [successorEq, successorTailEq]
        simp only [nextRuntime] at restBound
        omega

private theorem clauseFoldLoopRuntime_checks_of
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks =
        prior ++ marker :: pending.reverse) :
    (clauseFoldLoopRuntime pending.length runtime).checks =
      prior ++
        [runtime.registers.outputIndex + 2 * pending.length] := by
  induction pending generalizing runtime with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      have newest :
          popNewestResult runtime =
            popCoordinateResult runtime prior marker :=
        popNewestResult_of_checks runtime prior marker checks'
      simp [clauseFoldLoopRuntime, newest,
        finishNonemptyClauseResult_checks,
        popCoordinateResult]
  | cons value rest inductionHypothesis =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have newest : popNewestResult runtime = popped :=
        popNewestResult_of_checks runtime
          (prior ++ marker :: rest.reverse) value checks'
      have extendedChecks :
          (extendClauseResult popped).checks =
            prior ++ marker :: rest.reverse := by
        rw [extendClauseResult_checks]
        simp [popped, popCoordinateResult]
      simp only [List.length_cons]
      rw [clauseFoldLoopRuntime, newest,
        inductionHypothesis
          (extendClauseResult popped) extendedChecks]
      have arithmetic :
          (extendClauseResult popped).registers.outputIndex +
                2 * rest.length =
            runtime.registers.outputIndex +
                2 * (rest.length + 1) := by
        rw [extendClauseResult_outputIndex]
        simp [popped, popCoordinateResult]
        omega
      rw [arithmetic]

private def clauseFoldCoordinate
    (pending : List Nat) (runtime : Runtime) : Nat :=
  match pending with
  | [] => runtime.registers.currentGate
  | _ :: rest =>
      runtime.registers.outputIndex + (2 * rest.length + 1)

private theorem clauseFoldRuntime_checks_of
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks =
        prior ++ marker :: pending.reverse) :
    (clauseFoldRuntime pending.length runtime).checks =
      prior ++ [clauseFoldCoordinate pending runtime] := by
  cases pending with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      have newest :
          popNewestResult runtime =
            popCoordinateResult runtime prior marker :=
        popNewestResult_of_checks runtime prior marker checks'
      simp [clauseFoldRuntime, clauseFoldCoordinate, newest,
        pushTotalGateResult, popCoordinateResult]
  | cons value rest =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have newest : popNewestResult runtime = popped :=
        popNewestResult_of_checks runtime
          (prior ++ marker :: rest.reverse) value checks'
      have seededChecks :
          (seedClauseResult popped).checks =
            prior ++ marker :: rest.reverse := by
        rw [seedClauseResult_checks]
        simp [popped, popCoordinateResult]
      simp only [List.length_cons]
      rw [clauseFoldRuntime, newest,
        clauseFoldLoopRuntime_checks_of prior marker rest
          (seedClauseResult popped) seededChecks]
      simp [clauseFoldCoordinate, seedClauseResult_outputIndex,
        popped, popCoordinateResult]
      omega

private def clauseCoordinate
    (width : Nat) (clause : List CNFLiteral)
    (runtime : Runtime) : Nat :=
  let listed :=
    literalListRuntime width clause (pushTotalGateResult runtime)
  clauseFoldCoordinate
    (literalListCoordinates width clause
      (pushTotalGateResult runtime)).reverse listed

private theorem clauseRuntime_checks
    (width : Nat) (clause : List CNFLiteral)
    (runtime : Runtime) :
    (clauseRuntime width clause runtime).checks =
      runtime.checks ++
        [clauseCoordinate width clause runtime] := by
  let initialized := pushTotalGateResult runtime
  let listed := literalListRuntime width clause initialized
  let coordinates :=
    literalListCoordinates width clause initialized
  have listedChecks :
      listed.checks =
        runtime.checks ++
          listed.registers.currentGate :: coordinates := by
    rw [literalListRuntime_checks]
    simp [listed, initialized, coordinates, pushTotalGateResult,
      literalListRuntime_currentGate, List.append_assoc]
  have foldChecks :=
    clauseFoldRuntime_checks_of runtime.checks
      listed.registers.currentGate coordinates.reverse listed
      (by simpa using listedChecks)
  simpa [clauseRuntime, clauseCoordinate, initialized, listed,
    coordinates, literalListCoordinates_length] using foldChecks

private def clauseListCoordinates
    (width : Nat) :
    List (List CNFLiteral) → Runtime → List Nat
  | [], _ => []
  | clause :: rest, runtime =>
      clauseCoordinate width clause runtime ::
        clauseListCoordinates width rest
          (clauseRuntime width clause runtime)

private theorem clauseListCoordinates_length
    (width : Nat) (clauses : List (List CNFLiteral))
    (runtime : Runtime) :
    (clauseListCoordinates width clauses runtime).length =
      clauses.length := by
  induction clauses generalizing runtime with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      simp [clauseListCoordinates, inductionHypothesis]

private theorem clauseListRuntime_checks
    (width : Nat) (clauses : List (List CNFLiteral))
    (runtime : Runtime) :
    (clauseListRuntime width clauses runtime).checks =
      runtime.checks ++
        clauseListCoordinates width clauses runtime := by
  induction clauses generalizing runtime with
  | nil =>
      simp [clauseListRuntime, clauseListCoordinates]
  | cons clause rest inductionHypothesis =>
      rw [clauseListRuntime, inductionHypothesis,
        clauseRuntime_checks]
      simp [clauseListCoordinates, List.append_assoc]

private theorem clauseListRuntime_outputIndex
    (width : Nat) (clauses : List (List CNFLiteral))
    (runtime : Runtime) :
    (clauseListRuntime width clauses runtime).registers.outputIndex =
      runtime.registers.outputIndex +
        clauseListGateCount width clauses := by
  induction clauses generalizing runtime with
  | nil =>
      simp [clauseListRuntime, clauseListGateCount]
  | cons clause rest inductionHypothesis =>
      rw [clauseListRuntime, inductionHypothesis,
        clauseRuntime_outputIndex]
      simp [clauseListGateCount, Nat.add_assoc]

private theorem clauseListRuntime_currentGate
    (width : Nat) (clauses : List (List CNFLiteral))
    (runtime : Runtime) :
    (clauseListRuntime width clauses runtime).registers.currentGate =
      runtime.registers.currentGate := by
  induction clauses generalizing runtime with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      rw [clauseListRuntime, inductionHypothesis,
        clauseRuntime_currentGate]

private theorem clauseListRuntime_carrierWidth
    (width : Nat) (clauses : List (List CNFLiteral))
    (runtime : Runtime) :
    (clauseListRuntime width clauses runtime).registers.carrierWidth =
      runtime.registers.carrierWidth := by
  induction clauses generalizing runtime with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      rw [clauseListRuntime, inductionHypothesis,
        clauseRuntime_registers]

private theorem clauseCoordinate_eq_currentGate_of_empty
    (width : Nat) (runtime : Runtime) :
    clauseCoordinate width [] runtime =
      runtime.registers.currentGate := by
  simp [clauseCoordinate, clauseFoldCoordinate,
    literalListRuntime, literalListCoordinates,
    pushTotalGateResult]

private theorem clauseCoordinate_lt_currentGate_of_nonempty
    (width : Nat) (literal : CNFLiteral)
    (rest : List CNFLiteral) (runtime : Runtime)
    (bound :
      runtime.registers.outputIndex +
          clauseGateCount width (literal :: rest) ≤
        runtime.registers.currentGate) :
    clauseCoordinate width (literal :: rest) runtime <
      runtime.registers.currentGate := by
  let initialized := pushTotalGateResult runtime
  let coordinates :=
    literalListCoordinates width (literal :: rest) initialized
  have coordinatesLength :
      coordinates.length = rest.length + 1 := by
    simpa [coordinates] using
      literalListCoordinates_length width (literal :: rest) initialized
  cases reversedEq : coordinates.reverse with
  | nil =>
      have : coordinates.length = 0 := by
        rw [← List.length_reverse, reversedEq]
        rfl
      omega
  | cons head tail =>
      have tailLength : tail.length = rest.length := by
        have reversedLength :
            (coordinates.reverse).length = rest.length + 1 := by
          simpa using coordinatesLength
        rw [reversedEq] at reversedLength
        simpa using Nat.succ.inj reversedLength
      change
        clauseFoldCoordinate coordinates.reverse
            (literalListRuntime width (literal :: rest) initialized) <
          runtime.registers.currentGate
      rw [reversedEq]
      simp only [clauseFoldCoordinate]
      rw [literalListRuntime_outputIndex]
      simp [initialized, pushTotalGateResult] at bound ⊢
      simp only [tailLength]
      simp only [clauseGateCount] at bound
      simp only [List.length_cons] at bound
      omega

private theorem clauseListCoordinates_classified
    (width : Nat) (clauses : List (List CNFLiteral))
    (runtime : Runtime)
    (bound :
      runtime.registers.outputIndex +
          clauseListGateCount width clauses ≤
        runtime.registers.currentGate) :
    ∀ value, value ∈ clauseListCoordinates width clauses runtime →
      value = runtime.registers.currentGate ∨
        value < runtime.registers.currentGate := by
  induction clauses generalizing runtime with
  | nil =>
      intro value member
      simp [clauseListCoordinates] at member
  | cons clause rest inductionHypothesis =>
      intro value member
      simp only [clauseListCoordinates, List.mem_cons] at member
      rcases member with rfl | restMember
      · cases clause with
        | nil =>
            exact Or.inl
              (clauseCoordinate_eq_currentGate_of_empty width runtime)
        | cons literal tail =>
            exact Or.inr
              (clauseCoordinate_lt_currentGate_of_nonempty
                width literal tail runtime (by
                  simp only [clauseListGateCount] at bound
                  omega))
      · have restBound :
            (clauseRuntime width clause runtime).registers.outputIndex +
                clauseListGateCount width rest ≤
              (clauseRuntime width clause runtime).registers.currentGate := by
          rw [clauseRuntime_outputIndex, clauseRuntime_currentGate]
          simp only [clauseListGateCount] at bound
          omega
        rcases
            inductionHypothesis
              (clauseRuntime width clause runtime) restBound
              value restMember with
          equal | less
        · exact Or.inl (equal.trans (clauseRuntime_currentGate _ _ _))
        · exact Or.inr (by
            rw [clauseRuntime_currentGate] at less
            exact less)

/-! ## Formula-stack fold -/

private theorem seedFormulaResult_registers
    (source : ClauseSource) (runtime : Runtime) :
    (seedFormulaResult source runtime).registers =
      { runtime.registers with
        outputIndex := runtime.registers.outputIndex + 1 } := by
  cases source <;>
    simp [seedFormulaResult, advanceOutputIndexResult,
      emitGateResult, emitSourceResult]

private theorem extendFormulaResult_registers
    (source : ClauseSource) (runtime : Runtime) :
    (extendFormulaResult source runtime).registers =
      { runtime.registers with
        outputIndex := runtime.registers.outputIndex + 2 } := by
  cases source <;>
    simp [extendFormulaResult, advanceOutputIndexResult,
      emitGateResult, emitSourceResult]

private theorem seedFormulaResult_checks
    (source : ClauseSource) (runtime : Runtime) :
    (seedFormulaResult source runtime).checks = runtime.checks := by
  cases source <;>
    simp [seedFormulaResult, advanceOutputIndexResult,
      emitGateResult, emitSourceResult]

private theorem extendFormulaResult_checks
    (source : ClauseSource) (runtime : Runtime) :
    (extendFormulaResult source runtime).checks = runtime.checks := by
  cases source <;>
    simp [extendFormulaResult, advanceOutputIndexResult,
      emitGateResult, emitSourceResult]

private theorem seedFormulaResult_scratch_lt
    (capacity : Nat) (source : ClauseSource) (runtime : Runtime)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity) :
    (seedFormulaResult source runtime).scratch < capacity := by
  cases source <;>
    simp [seedFormulaResult, advanceOutputIndexResult,
      emitGateResult, emitSourceResult,
      EmissionSource.finalScratch] <;> omega

private theorem extendFormulaResult_scratch_lt
    (capacity : Nat) (source : ClauseSource) (runtime : Runtime)
    (outputBound :
      runtime.registers.outputIndex + 2 ≤ capacity) :
    (extendFormulaResult source runtime).scratch < capacity := by
  cases source <;>
    simp [extendFormulaResult, advanceOutputIndexResult,
      emitGateResult, emitSourceResult,
      EmissionSource.finalScratch] <;> omega

private theorem formulaResult_fits_one
    (capacity : Nat) (source : ClauseSource) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity) :
    LedgerFits capacity
      (seedFormulaResult source runtime).registers := by
  rw [seedFormulaResult_registers]
  exact
    { inputCount := fits.inputCount
      normalizedGateCount := fits.normalizedGateCount
      carrierWidth := fits.carrierWidth
      baseline := fits.baseline
      currentGate := fits.currentGate
      outputIndex := outputBound }

private theorem formulaResult_fits_two
    (capacity : Nat) (source : ClauseSource) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (outputBound :
      runtime.registers.outputIndex + 2 ≤ capacity) :
    LedgerFits capacity
      (extendFormulaResult source runtime).registers := by
  rw [extendFormulaResult_registers]
  exact
    { inputCount := fits.inputCount
      normalizedGateCount := fits.normalizedGateCount
      carrierWidth := fits.carrierWidth
      baseline := fits.baseline
      currentGate := fits.currentGate
      outputIndex := outputBound }

private theorem seedFormulaResult_currentGate
    (source : ClauseSource) (runtime : Runtime) :
    (seedFormulaResult source runtime).registers.currentGate =
      runtime.registers.currentGate := by
  rw [seedFormulaResult_registers]

private theorem extendFormulaResult_currentGate
    (source : ClauseSource) (runtime : Runtime) :
    (extendFormulaResult source runtime).registers.currentGate =
      runtime.registers.currentGate := by
  rw [extendFormulaResult_registers]

private theorem seedFormulaResult_carrierWidth
    (source : ClauseSource) (runtime : Runtime) :
    (seedFormulaResult source runtime).registers.carrierWidth =
      runtime.registers.carrierWidth := by
  rw [seedFormulaResult_registers]

private theorem extendFormulaResult_carrierWidth
    (source : ClauseSource) (runtime : Runtime) :
    (extendFormulaResult source runtime).registers.carrierWidth =
      runtime.registers.carrierWidth := by
  rw [extendFormulaResult_registers]

private def formulaSeedTailCost
    (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime) : Nat :=
  slotCompareSteps .currentGate capacity runtime.scratch +
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
      capacity source runtime
        (match runtimeClauseSource runtime with
        | .constantFalse => blockDescriptors[26].primitives
        | .gateScratch => blockDescriptors[27].primitives)

private theorem formula_seed_tail_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (classified :
      runtime.scratch = runtime.registers.currentGate ∨
        runtime.scratch < runtime.registers.currentGate)
    (outputBound :
      runtime.registers.outputIndex + 1 ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents formulaCompareFalseFirstRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node formulaCompareFalseFirstRef)
        (.node formulaPopLoopRef) steps initialTape finalTape ∧
      TapeRepresents formulaPopLoopRef.startState
        capacity
        (seedFormulaResult
          (runtimeClauseSource runtime) runtime).scratch
        (seedFormulaResult
          (runtimeClauseSource runtime) runtime).registers
        (seedFormulaResult
          (runtimeClauseSource runtime) runtime).checks
        source
        (seedFormulaResult
          (runtimeClauseSource runtime) runtime).targetTokens
        finalTape ∧
      steps ≤ formulaSeedTailCost capacity source runtime := by
  rcases classified with equal | less
  · have compareInput :
        TapeRepresents formulaCompareFalseFirstRef.startState
          capacity runtime.scratch runtime.registers runtime.checks
          (context.head :: context.tail) runtime.targetTokens
          initialTape := by
      simpa [context.source_eq] using represents
    rcases
        slot_compare_equal_path .currentGate
          Address.formulaCompareFalseFirst
          (.node formulaSeedFalseRef) (.node formulaSeedGateRef)
          formulaSeedFalseRef.startState
          capacity runtime.scratch runtime.registers runtime.checks
          context.head context.tail runtime.targetTokens initialTape
          formulaCompareFalseFirstNode_member fits
          (by simpa [TargetEmitterLedger.slotValue] using equal)
          context.compareAllowed compareInput with
      ⟨blockTape, comparePath, blockRepresents'⟩
    have blockRepresents :
        TapeRepresents formulaSeedFalseRef.startState
          capacity runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens blockTape := by
      simpa [context.source_eq] using blockRepresents'
    rcases
        formulaSeedBlock_path .constantFalse
          (context := context) layout runtime fits scratchBound
          outputBound blockTape blockRepresents with
      ⟨blockSteps, finalTape, blockPath,
        finalRepresents, blockBound⟩
    refine
      ⟨slotCompareSteps .currentGate capacity runtime.scratch +
          blockSteps,
        finalTape,
        AcceptPath.trans graph _ _ _ _ _ _ _ _
          comparePath blockPath, ?_, ?_⟩
    · simpa [runtimeClauseSource, equal] using finalRepresents
    · unfold formulaSeedTailCost
      simp [runtimeClauseSource, equal]
      omega
  · have compareInput :
        TapeRepresents formulaCompareFalseFirstRef.startState
          capacity runtime.scratch runtime.registers runtime.checks
          (context.head :: context.tail) runtime.targetTokens
          initialTape := by
      simpa [context.source_eq] using represents
    rcases
        slot_compare_less_path .currentGate
          Address.formulaCompareFalseFirst
          (.node formulaSeedFalseRef) (.node formulaSeedGateRef)
          formulaSeedGateRef.startState
          capacity runtime.scratch runtime.registers runtime.checks
          context.head context.tail runtime.targetTokens initialTape
          formulaCompareFalseFirstNode_member fits
          (by simpa [TargetEmitterLedger.slotValue] using less)
          context.compareAllowed compareInput with
      ⟨blockTape, comparePath, blockRepresents'⟩
    have blockRepresents :
        TapeRepresents formulaSeedGateRef.startState
          capacity runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens blockTape := by
      simpa [context.source_eq] using blockRepresents'
    rcases
        formulaSeedBlock_path .gateScratch
          (context := context) layout runtime fits scratchBound
          outputBound blockTape blockRepresents with
      ⟨blockSteps, finalTape, blockPath,
        finalRepresents, blockBound⟩
    refine
      ⟨slotCompareSteps .currentGate capacity runtime.scratch +
          blockSteps,
        finalTape,
        AcceptPath.trans graph _ _ _ _ _ _ _ _
          comparePath blockPath, ?_, ?_⟩
    · have notEqual : runtime.scratch ≠
          runtime.registers.currentGate := Nat.ne_of_lt less
      simpa [runtimeClauseSource, notEqual] using finalRepresents
    · unfold formulaSeedTailCost
      have notEqual : runtime.scratch ≠
          runtime.registers.currentGate := Nat.ne_of_lt less
      simp [runtimeClauseSource, notEqual]
      omega

private def formulaExtendTailCost
    (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime) : Nat :=
  slotCompareSteps .currentGate capacity runtime.scratch +
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
      capacity source runtime
        (match runtimeClauseSource runtime with
        | .constantFalse => blockDescriptors[29].primitives
        | .gateScratch => blockDescriptors[30].primitives)

private theorem formula_extend_tail_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source) (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (classified :
      runtime.scratch = runtime.registers.currentGate ∨
        runtime.scratch < runtime.registers.currentGate)
    (outputBound :
      runtime.registers.outputIndex + 2 ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents formulaCompareFalseLoopRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node formulaCompareFalseLoopRef)
        (.node formulaPopLoopRef) steps initialTape finalTape ∧
      TapeRepresents formulaPopLoopRef.startState
        capacity
        (extendFormulaResult
          (runtimeClauseSource runtime) runtime).scratch
        (extendFormulaResult
          (runtimeClauseSource runtime) runtime).registers
        (extendFormulaResult
          (runtimeClauseSource runtime) runtime).checks
        source
        (extendFormulaResult
          (runtimeClauseSource runtime) runtime).targetTokens
        finalTape ∧
      steps ≤ formulaExtendTailCost capacity source runtime := by
  rcases classified with equal | less
  · have compareInput :
        TapeRepresents formulaCompareFalseLoopRef.startState
          capacity runtime.scratch runtime.registers runtime.checks
          (context.head :: context.tail) runtime.targetTokens
          initialTape := by
      simpa [context.source_eq] using represents
    rcases
        slot_compare_equal_path .currentGate
          Address.formulaCompareFalseLoop
          (.node formulaExtendFalseRef) (.node formulaExtendGateRef)
          formulaExtendFalseRef.startState
          capacity runtime.scratch runtime.registers runtime.checks
          context.head context.tail runtime.targetTokens initialTape
          formulaCompareFalseLoopNode_member fits
          (by simpa [TargetEmitterLedger.slotValue] using equal)
          context.compareAllowed compareInput with
      ⟨blockTape, comparePath, blockRepresents'⟩
    have blockRepresents :
        TapeRepresents formulaExtendFalseRef.startState
          capacity runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens blockTape := by
      simpa [context.source_eq] using blockRepresents'
    rcases
        formulaExtendBlock_path .constantFalse
          (context := context) layout runtime fits scratchBound
          outputBound blockTape blockRepresents with
      ⟨blockSteps, finalTape, blockPath,
        finalRepresents, blockBound⟩
    refine
      ⟨slotCompareSteps .currentGate capacity runtime.scratch +
          blockSteps,
        finalTape,
        AcceptPath.trans graph _ _ _ _ _ _ _ _
          comparePath blockPath, ?_, ?_⟩
    · simpa [runtimeClauseSource, equal] using finalRepresents
    · unfold formulaExtendTailCost
      simp [runtimeClauseSource, equal]
      omega
  · have compareInput :
        TapeRepresents formulaCompareFalseLoopRef.startState
          capacity runtime.scratch runtime.registers runtime.checks
          (context.head :: context.tail) runtime.targetTokens
          initialTape := by
      simpa [context.source_eq] using represents
    rcases
        slot_compare_less_path .currentGate
          Address.formulaCompareFalseLoop
          (.node formulaExtendFalseRef) (.node formulaExtendGateRef)
          formulaExtendGateRef.startState
          capacity runtime.scratch runtime.registers runtime.checks
          context.head context.tail runtime.targetTokens initialTape
          formulaCompareFalseLoopNode_member fits
          (by simpa [TargetEmitterLedger.slotValue] using less)
          context.compareAllowed compareInput with
      ⟨blockTape, comparePath, blockRepresents'⟩
    have blockRepresents :
        TapeRepresents formulaExtendGateRef.startState
          capacity runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens blockTape := by
      simpa [context.source_eq] using blockRepresents'
    rcases
        formulaExtendBlock_path .gateScratch
          (context := context) layout runtime fits scratchBound
          outputBound blockTape blockRepresents with
      ⟨blockSteps, finalTape, blockPath,
        finalRepresents, blockBound⟩
    refine
      ⟨slotCompareSteps .currentGate capacity runtime.scratch +
          blockSteps,
        finalTape,
        AcceptPath.trans graph _ _ _ _ _ _ _ _
          comparePath blockPath, ?_, ?_⟩
    · have notEqual : runtime.scratch ≠
          runtime.registers.currentGate := Nat.ne_of_lt less
      simpa [runtimeClauseSource, notEqual] using finalRepresents
    · unfold formulaExtendTailCost
      have notEqual : runtime.scratch ≠
          runtime.registers.currentGate := Nat.ne_of_lt less
      simp [runtimeClauseSource, notEqual]
      omega

private def formulaFoldLoopCost
    (capacity : Nat) (source : List WorkSymbol) :
    List Nat → Runtime → Nat
  | [], runtime =>
      TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[28].primitives +
        slotCompareSteps .carrierWidth capacity
          runtime.registers.carrierWidth
  | _ :: rest, runtime =>
      TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[28].primitives +
        slotCompareSteps .carrierWidth capacity
          (popNewestResult runtime).scratch +
        formulaExtendTailCost capacity source
          (popNewestResult runtime) +
        formulaFoldLoopCost capacity source rest
          (extendFormulaResult
            (runtimeClauseSource (popNewestResult runtime))
            (popNewestResult runtime))

private theorem formula_fold_loop_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source)
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks =
        prior ++ marker :: pending.reverse)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (carrierMarker :
      marker = runtime.registers.carrierWidth)
    (carrierBound :
      runtime.registers.carrierWidth < capacity)
    (gateBelowCarrier :
      runtime.registers.currentGate <
        runtime.registers.carrierWidth)
    (classified :
      ∀ value, value ∈ pending →
        value = runtime.registers.currentGate ∨
          value < runtime.registers.currentGate)
    (outputBound :
      runtime.registers.outputIndex +
          2 * pending.length ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents formulaPopLoopRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node formulaPopLoopRef)
        (.node suffixRef) steps initialTape finalTape ∧
      TapeRepresents suffixRef.startState
        capacity
        (formulaFoldLoopRuntime pending.length runtime).scratch
        (formulaFoldLoopRuntime pending.length runtime).registers
        (formulaFoldLoopRuntime pending.length runtime).checks
        source
        (formulaFoldLoopRuntime pending.length runtime).targetTokens
        finalTape ∧
      steps ≤
        formulaFoldLoopCost capacity source pending runtime := by
  induction pending generalizing prior runtime initialTape with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      have markerCapacity : marker ≤ capacity := by
        rw [carrierMarker]
        exact Nat.le_of_lt carrierBound
      rcases
          popCoordinateBlock_path 28 (by decide)
            formulaPopLoopRef (.node formulaCompareMarkerLoopRef)
            (by rfl) (by rfl) (by rfl)
            (context := context) runtime prior marker fits
            scratchBound checks' markerCapacity
            formulaCompareMarkerLoopRef.startState
            initialTape represents with
        ⟨popSteps, popTape, popPath, popRepresents, popBound⟩
      let popped := popCoordinateResult runtime prior marker
      have poppedFits :
          LedgerFits capacity popped.registers := by
        simpa [popped, popCoordinateResult] using fits
      have compareInput :
          TapeRepresents formulaCompareMarkerLoopRef.startState
            capacity popped.scratch popped.registers popped.checks
            (context.head :: context.tail) popped.targetTokens
            popTape := by
        simpa [popped, context.source_eq] using popRepresents
      have equal :
          popped.scratch =
            TargetEmitterLedger.slotValue
              popped.registers .carrierWidth := by
        simp [popped, popCoordinateResult,
          TargetEmitterLedger.slotValue, carrierMarker]
      rcases
          slot_compare_equal_path .carrierWidth
            Address.formulaCompareMarkerLoop
            (.node suffixRef) (.node formulaCompareFalseLoopRef)
            suffixRef.startState
            capacity popped.scratch popped.registers popped.checks
            context.head context.tail popped.targetTokens popTape
            formulaCompareMarkerLoopNode_member poppedFits equal
            context.compareAllowed compareInput with
        ⟨finalTape, comparePath, finalRepresents'⟩
      have finalRepresents :
          TapeRepresents suffixRef.startState
            capacity popped.scratch popped.registers popped.checks
            source popped.targetTokens finalTape := by
        simpa [context.source_eq] using finalRepresents'
      refine
        ⟨popSteps +
            slotCompareSteps .carrierWidth capacity marker,
          finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            popPath (by
              simpa [formulaCompareMarkerLoopRef, popped,
                popCoordinateResult, carrierMarker]
                using comparePath),
          ?_, ?_⟩
      · have newest : popNewestResult runtime = popped :=
          popNewestResult_of_checks runtime prior marker checks'
        simpa [formulaFoldLoopRuntime, newest, popped] using
          finalRepresents
      · simp only [formulaFoldLoopCost]
        rw [carrierMarker]
        omega
  | cons value rest inductionHypothesis =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      have valueClass :=
        classified value (List.Mem.head rest)
      have valueBelowCarrier :
          value < runtime.registers.carrierWidth := by
        rcases valueClass with equal | less
        · rw [equal]
          exact gateBelowCarrier
        · exact Nat.lt_trans less gateBelowCarrier
      have valueCapacity : value ≤ capacity :=
        Nat.le_trans (Nat.le_of_lt valueBelowCarrier)
          (Nat.le_of_lt carrierBound)
      rcases
          popCoordinateBlock_path 28 (by decide)
            formulaPopLoopRef (.node formulaCompareMarkerLoopRef)
            (by rfl) (by rfl) (by rfl)
            (context := context) runtime
            (prior ++ marker :: rest.reverse) value fits
            scratchBound checks' valueCapacity
            formulaCompareMarkerLoopRef.startState
            initialTape represents with
        ⟨popSteps, popTape, popPath, popRepresents, popBound⟩
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have poppedFits :
          LedgerFits capacity popped.registers := by
        simpa [popped, popCoordinateResult] using fits
      have markerInput :
          TapeRepresents formulaCompareMarkerLoopRef.startState
            capacity popped.scratch popped.registers popped.checks
            (context.head :: context.tail) popped.targetTokens
            popTape := by
        simpa [popped, context.source_eq] using popRepresents
      have markerLess :
          popped.scratch <
            TargetEmitterLedger.slotValue
              popped.registers .carrierWidth := by
        simpa [popped, popCoordinateResult,
          TargetEmitterLedger.slotValue] using valueBelowCarrier
      rcases
          slot_compare_less_path .carrierWidth
            Address.formulaCompareMarkerLoop
            (.node suffixRef) (.node formulaCompareFalseLoopRef)
            formulaCompareFalseLoopRef.startState
            capacity popped.scratch popped.registers popped.checks
            context.head context.tail popped.targetTokens popTape
            formulaCompareMarkerLoopNode_member poppedFits markerLess
            context.compareAllowed markerInput with
        ⟨falseTape, markerPath, falseRepresents'⟩
      have falseRepresents :
          TapeRepresents formulaCompareFalseLoopRef.startState
            capacity popped.scratch popped.registers popped.checks
            source popped.targetTokens falseTape := by
        simpa [context.source_eq] using falseRepresents'
      have poppedClass :
          popped.scratch = popped.registers.currentGate ∨
            popped.scratch < popped.registers.currentGate := by
        simpa [popped, popCoordinateResult] using valueClass
      have poppedScratch : popped.scratch < capacity := by
        simpa [popped, popCoordinateResult] using
          Nat.lt_trans valueBelowCarrier carrierBound
      have extendOutput :
          popped.registers.outputIndex + 2 ≤ capacity := by
        simpa [popped, popCoordinateResult] using
          (show runtime.registers.outputIndex + 2 ≤ capacity by
            simp only [List.length_cons] at outputBound
            omega)
      rcases
          formula_extend_tail_path (context := context)
            layout popped poppedFits poppedScratch poppedClass
            extendOutput falseTape falseRepresents with
        ⟨extendSteps, extendTape, extendPath,
          extendRepresents, extendBound⟩
      let extended :=
        extendFormulaResult (runtimeClauseSource popped) popped
      have extendedFits :
          LedgerFits capacity extended.registers := by
        exact formulaResult_fits_two capacity
          (runtimeClauseSource popped) popped poppedFits extendOutput
      have extendedScratch : extended.scratch < capacity := by
        exact extendFormulaResult_scratch_lt capacity
          (runtimeClauseSource popped) popped extendOutput
      have extendedMarker :
          marker = extended.registers.carrierWidth := by
        rw [extendFormulaResult_carrierWidth]
        exact carrierMarker
      have extendedCarrierBound :
          extended.registers.carrierWidth < capacity := by
        rw [extendFormulaResult_carrierWidth]
        exact carrierBound
      have extendedGateBelow :
          extended.registers.currentGate <
            extended.registers.carrierWidth := by
        rw [extendFormulaResult_currentGate,
          extendFormulaResult_carrierWidth]
        exact gateBelowCarrier
      have remainingClass :
          ∀ item, item ∈ rest →
            item = extended.registers.currentGate ∨
              item < extended.registers.currentGate := by
        intro item member
        rw [extendFormulaResult_currentGate]
        exact classified item (List.Mem.tail value member)
      have remainingOutput :
          extended.registers.outputIndex +
              2 * rest.length ≤ capacity := by
        dsimp [extended]
        rw [extendFormulaResult_registers]
        simp only [popped, popCoordinateResult]
        simp only [List.length_cons] at outputBound
        omega
      have extendedChecks :
          extended.checks =
            prior ++ marker :: rest.reverse := by
        rw [extendFormulaResult_checks]
        simp [extended, popped, popCoordinateResult]
      have recursiveInput :
          TapeRepresents formulaPopLoopRef.startState
            capacity extended.scratch extended.registers
            extended.checks source extended.targetTokens
            extendTape := by
        simpa [extended] using extendRepresents
      rcases
          inductionHypothesis prior extended extendedChecks
            extendedFits extendedScratch extendedMarker
            extendedCarrierBound extendedGateBelow
            remainingClass remainingOutput
            extendTape recursiveInput with
        ⟨restSteps, finalTape, restPath,
          finalRepresents, restBound⟩
      let markerSteps :=
        slotCompareSteps .carrierWidth capacity value
      have markerPath' :
          AcceptPath graph (.node formulaCompareMarkerLoopRef)
            (.node formulaCompareFalseLoopRef)
            markerSteps popTape falseTape := by
        simpa [markerSteps, formulaCompareMarkerLoopRef,
          popped, popCoordinateResult] using markerPath
      have prefixPath :
          AcceptPath graph (.node formulaPopLoopRef)
            (.node formulaPopLoopRef)
            (popSteps + markerSteps + extendSteps)
            initialTape extendTape := by
        exact
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            (AcceptPath.trans graph _ _ _ _ _ _ _ _
              popPath markerPath')
            extendPath
      refine
        ⟨popSteps + markerSteps + extendSteps + restSteps,
          finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            prefixPath restPath, ?_, ?_⟩
      · have newest : popNewestResult runtime = popped :=
          popNewestResult_of_checks runtime
            (prior ++ marker :: rest.reverse) value checks'
        simpa [formulaFoldLoopRuntime, newest, popped, extended] using
          finalRepresents
      · have newest : popNewestResult runtime = popped :=
          popNewestResult_of_checks runtime
            (prior ++ marker :: rest.reverse) value checks'
        have scratchEq : popped.scratch = value := by
          simp [popped, popCoordinateResult]
        simp only [formulaFoldLoopCost]
        rw [newest]
        rw [scratchEq]
        dsimp [extended] at restBound
        dsimp [markerSteps, extended]
        omega

private def formulaFoldCost
    (capacity : Nat) (source : List WorkSymbol) :
    List Nat → Runtime → Nat
  | [], runtime =>
      TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[25].primitives +
        slotCompareSteps .carrierWidth capacity
          runtime.registers.carrierWidth +
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source (popNewestResult runtime)
          blockDescriptors[31].primitives
  | _ :: rest, runtime =>
      TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source runtime blockDescriptors[25].primitives +
        slotCompareSteps .carrierWidth capacity
          (popNewestResult runtime).scratch +
        formulaSeedTailCost capacity source
          (popNewestResult runtime) +
        formulaFoldLoopCost capacity source rest
          (seedFormulaResult
            (runtimeClauseSource (popNewestResult runtime))
            (popNewestResult runtime))

private theorem formula_fold_path
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (layout : CursorLayout source)
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks =
        prior ++ marker :: pending.reverse)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (carrierMarker :
      marker = runtime.registers.carrierWidth)
    (carrierBound :
      runtime.registers.carrierWidth < capacity)
    (gateBelowCarrier :
      runtime.registers.currentGate <
        runtime.registers.carrierWidth)
    (classified :
      ∀ value, value ∈ pending →
        value = runtime.registers.currentGate ∨
          value < runtime.registers.currentGate)
    (outputBound :
      runtime.registers.outputIndex +
        (if pending.isEmpty then 0
          else 2 * pending.length - 1) ≤ capacity)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents formulaPopFirstRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node formulaPopFirstRef)
        (.node suffixRef) steps initialTape finalTape ∧
      TapeRepresents suffixRef.startState
        capacity
        (formulaFoldRuntime pending.length runtime).scratch
        (formulaFoldRuntime pending.length runtime).registers
        (formulaFoldRuntime pending.length runtime).checks
        source
        (formulaFoldRuntime pending.length runtime).targetTokens
        finalTape ∧
      steps ≤ formulaFoldCost capacity source pending runtime := by
  cases pending with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      have markerCapacity : marker ≤ capacity := by
        rw [carrierMarker]
        exact Nat.le_of_lt carrierBound
      rcases
          popCoordinateBlock_path 25 (by decide)
            formulaPopFirstRef (.node formulaCompareMarkerFirstRef)
            (by rfl) (by rfl) (by rfl)
            (context := context) runtime prior marker fits
            scratchBound checks' markerCapacity
            formulaCompareMarkerFirstRef.startState
            initialTape represents with
        ⟨popSteps, popTape, popPath, popRepresents, popBound⟩
      let popped := popCoordinateResult runtime prior marker
      have poppedFits :
          LedgerFits capacity popped.registers := by
        simpa [popped, popCoordinateResult] using fits
      have markerInput :
          TapeRepresents formulaCompareMarkerFirstRef.startState
            capacity popped.scratch popped.registers popped.checks
            (context.head :: context.tail) popped.targetTokens
            popTape := by
        simpa [popped, context.source_eq] using popRepresents
      have equal :
          popped.scratch =
            TargetEmitterLedger.slotValue
              popped.registers .carrierWidth := by
        simp [popped, popCoordinateResult,
          TargetEmitterLedger.slotValue, carrierMarker]
      rcases
          slot_compare_equal_path .carrierWidth
            Address.formulaCompareMarkerFirst
            (.node formulaEmptyRef)
            (.node formulaCompareFalseFirstRef)
            formulaEmptyRef.startState
            capacity popped.scratch popped.registers popped.checks
            context.head context.tail popped.targetTokens popTape
            formulaCompareMarkerFirstNode_member poppedFits equal
            context.compareAllowed markerInput with
        ⟨emptyTape, markerPath, emptyRepresents'⟩
      have emptyRepresents :
          TapeRepresents formulaEmptyRef.startState
            capacity popped.scratch popped.registers popped.checks
            source popped.targetTokens emptyTape := by
        simpa [context.source_eq] using emptyRepresents'
      have poppedScratch : popped.scratch < capacity := by
        simpa [popped, popCoordinateResult, carrierMarker] using
          carrierBound
      rcases
          formulaEmptyBlock_path (context := context)
            layout popped poppedFits poppedScratch
            emptyTape emptyRepresents with
        ⟨emptySteps, finalTape, emptyPath,
          finalRepresents, emptyBound⟩
      refine
        ⟨popSteps +
            slotCompareSteps .carrierWidth capacity marker +
            emptySteps,
          finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            (AcceptPath.trans graph _ _ _ _ _ _ _ _
              popPath (by
                simpa [formulaCompareMarkerFirstRef, popped,
                  popCoordinateResult, carrierMarker]
                  using markerPath))
            emptyPath, ?_, ?_⟩
      · have newest : popNewestResult runtime = popped :=
          popNewestResult_of_checks runtime prior marker checks'
        simpa [formulaFoldRuntime, newest, popped] using finalRepresents
      · have newest : popNewestResult runtime = popped :=
          popNewestResult_of_checks runtime prior marker checks'
        simp only [formulaFoldCost]
        rw [newest]
        rw [carrierMarker]
        omega
  | cons value rest =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      have valueClass :=
        classified value (List.Mem.head rest)
      have valueBelowCarrier :
          value < runtime.registers.carrierWidth := by
        rcases valueClass with equal | less
        · rw [equal]
          exact gateBelowCarrier
        · exact Nat.lt_trans less gateBelowCarrier
      have valueCapacity : value ≤ capacity :=
        Nat.le_trans (Nat.le_of_lt valueBelowCarrier)
          (Nat.le_of_lt carrierBound)
      rcases
          popCoordinateBlock_path 25 (by decide)
            formulaPopFirstRef (.node formulaCompareMarkerFirstRef)
            (by rfl) (by rfl) (by rfl)
            (context := context) runtime
            (prior ++ marker :: rest.reverse) value fits
            scratchBound checks' valueCapacity
            formulaCompareMarkerFirstRef.startState
            initialTape represents with
        ⟨popSteps, popTape, popPath, popRepresents, popBound⟩
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have poppedFits :
          LedgerFits capacity popped.registers := by
        simpa [popped, popCoordinateResult] using fits
      have markerInput :
          TapeRepresents formulaCompareMarkerFirstRef.startState
            capacity popped.scratch popped.registers popped.checks
            (context.head :: context.tail) popped.targetTokens
            popTape := by
        simpa [popped, context.source_eq] using popRepresents
      have markerLess :
          popped.scratch <
            TargetEmitterLedger.slotValue
              popped.registers .carrierWidth := by
        simpa [popped, popCoordinateResult,
          TargetEmitterLedger.slotValue] using valueBelowCarrier
      rcases
          slot_compare_less_path .carrierWidth
            Address.formulaCompareMarkerFirst
            (.node formulaEmptyRef)
            (.node formulaCompareFalseFirstRef)
            formulaCompareFalseFirstRef.startState
            capacity popped.scratch popped.registers popped.checks
            context.head context.tail popped.targetTokens popTape
            formulaCompareMarkerFirstNode_member poppedFits markerLess
            context.compareAllowed markerInput with
        ⟨falseTape, markerPath, falseRepresents'⟩
      have falseRepresents :
          TapeRepresents formulaCompareFalseFirstRef.startState
            capacity popped.scratch popped.registers popped.checks
            source popped.targetTokens falseTape := by
        simpa [context.source_eq] using falseRepresents'
      have poppedClass :
          popped.scratch = popped.registers.currentGate ∨
            popped.scratch < popped.registers.currentGate := by
        simpa [popped, popCoordinateResult] using valueClass
      have poppedScratch : popped.scratch < capacity := by
        simpa [popped, popCoordinateResult] using
          Nat.lt_trans valueBelowCarrier carrierBound
      have seedOutput :
          popped.registers.outputIndex + 1 ≤ capacity := by
        simpa [popped, popCoordinateResult] using
          (show runtime.registers.outputIndex + 1 ≤ capacity by
            simp at outputBound
            omega)
      rcases
          formula_seed_tail_path (context := context)
            layout popped poppedFits poppedScratch poppedClass
            seedOutput falseTape falseRepresents with
        ⟨seedSteps, seedTape, seedPath,
          seedRepresents, seedBound⟩
      let seeded :=
        seedFormulaResult (runtimeClauseSource popped) popped
      have seededFits :
          LedgerFits capacity seeded.registers := by
        exact formulaResult_fits_one capacity
          (runtimeClauseSource popped) popped poppedFits seedOutput
      have seededScratch : seeded.scratch < capacity := by
        exact seedFormulaResult_scratch_lt capacity
          (runtimeClauseSource popped) popped seedOutput
      have seededMarker :
          marker = seeded.registers.carrierWidth := by
        rw [seedFormulaResult_carrierWidth]
        exact carrierMarker
      have seededCarrierBound :
          seeded.registers.carrierWidth < capacity := by
        rw [seedFormulaResult_carrierWidth]
        exact carrierBound
      have seededGateBelow :
          seeded.registers.currentGate <
            seeded.registers.carrierWidth := by
        rw [seedFormulaResult_currentGate,
          seedFormulaResult_carrierWidth]
        exact gateBelowCarrier
      have remainingClass :
          ∀ item, item ∈ rest →
            item = seeded.registers.currentGate ∨
              item < seeded.registers.currentGate := by
        intro item member
        rw [seedFormulaResult_currentGate]
        exact classified item (List.Mem.tail value member)
      have remainingOutput :
          seeded.registers.outputIndex +
              2 * rest.length ≤ capacity := by
        dsimp [seeded]
        rw [seedFormulaResult_registers]
        simp only [popped, popCoordinateResult]
        simp at outputBound
        omega
      have seededChecks :
          seeded.checks =
            prior ++ marker :: rest.reverse := by
        rw [seedFormulaResult_checks]
        simp [seeded, popped, popCoordinateResult]
      have recursiveInput :
          TapeRepresents formulaPopLoopRef.startState
            capacity seeded.scratch seeded.registers seeded.checks
            source seeded.targetTokens seedTape := by
        simpa [seeded] using seedRepresents
      rcases
          formula_fold_loop_path (context := context)
            layout prior marker rest seeded seededChecks
            seededFits seededScratch seededMarker
            seededCarrierBound seededGateBelow remainingClass
            remainingOutput seedTape recursiveInput with
        ⟨loopSteps, finalTape, loopPath,
          finalRepresents, loopBound⟩
      let markerSteps :=
        slotCompareSteps .carrierWidth capacity value
      have markerPath' :
          AcceptPath graph (.node formulaCompareMarkerFirstRef)
            (.node formulaCompareFalseFirstRef)
            markerSteps popTape falseTape := by
        simpa [markerSteps, formulaCompareMarkerFirstRef,
          popped, popCoordinateResult] using markerPath
      have prefixPath :
          AcceptPath graph (.node formulaPopFirstRef)
            (.node formulaPopLoopRef)
            (popSteps + markerSteps + seedSteps)
            initialTape seedTape := by
        exact
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            (AcceptPath.trans graph _ _ _ _ _ _ _ _
              popPath markerPath')
            seedPath
      refine
        ⟨popSteps + markerSteps + seedSteps + loopSteps,
          finalTape,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            prefixPath loopPath, ?_, ?_⟩
      · have newest : popNewestResult runtime = popped :=
          popNewestResult_of_checks runtime
            (prior ++ marker :: rest.reverse) value checks'
        simpa [formulaFoldRuntime, newest, popped, seeded] using
          finalRepresents
      · have newest : popNewestResult runtime = popped :=
          popNewestResult_of_checks runtime
            (prior ++ marker :: rest.reverse) value checks'
        have scratchEq : popped.scratch = value := by
          simp [popped, popCoordinateResult]
        simp only [formulaFoldCost]
        rw [newest]
        rw [scratchEq]
        dsimp [seeded] at loopBound
        dsimp [markerSteps, seeded]
        omega

/-! ## End token, retained-source rewind, and formula cursor -/

private def emitFinishCost
    (formula : CNFFormula) (processed : List CNFToken) : Nat :=
  PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .finish +
    PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed .finish

private theorem emit_finish_path
    (formula : CNFFormula) (processed : List CNFToken)
    (startState restoreState : GrammarState) (kind : FinishKind)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ [.finish])
    (active : startState ∈ activeGrammarStates)
    (valid : validGrammarToken startState .finish = true)
    (installed :
      postInstallEndpoint .emit startState .finish =
        .node (restoreRef .emit restoreState .finish))
    (finished : stateFinishKind? restoreState = some kind)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit startState).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .finish [])
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .emit startState))
        (.node (programEndRef .emit kind))
        steps initialTape finalTape ∧
      ScanRepresents (programEndRef .emit kind).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (processed ++ [.finish]))
        carrierFooterCells runtime.targetTokens finalTape ∧
      steps ≤ emitFinishCost formula processed := by
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_read_install_path
        .emit formula processed .finish [] startState runtime
        tokens active valid initialTape represents with
    ⟨installedTape, installPath, installedRepresents⟩
  have restoreRepresents :
      TapeRepresents
        (restoreRef .emit restoreState .finish).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .finish [])
        runtime.targetTokens installedTape := by
    exact
      represents_at_state
        (newState :=
          (restoreRef .emit restoreState .finish).startState)
        installedRepresents
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.token_restore_advance_end_path
        .emit formula processed .finish restoreState kind runtime
        tokens finished installedTape restoreRepresents with
    ⟨finalTape, restorePath, finalRepresents⟩
  refine
    ⟨PNP.Concrete.CNFToNANDControllerCountTrace.tokenReadInstallSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .finish +
        PNP.Concrete.CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .finish,
      finalTape,
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        (by simpa [installed] using installPath)
        restorePath,
      finalRepresents, ?_⟩
  exact Nat.le_refl _

private def emitRewindBefore (formula : CNFFormula) :
    List WorkSymbol :=
  scanBeforeCells
      (CNFToNANDWorkspace.formulaTokens formula)
      (CNFToNANDWorkspace.formulaTokens formula) ++
    [SourceParser.cell10, SourceParser.cell00]

private def emitRewindAfter : List WorkSymbol :=
  [ SourceParser.cell00
  , SourceParser.cell10
  , SourceParser.cell01
  , SourceParser.cell10
  , SourceParser.cell11
  ]

private theorem canonicalSource_eq_emitRewindSplit
    (formula : CNFFormula) :
    canonicalSource formula =
      emitRewindBefore formula ++
        SourceParser.cell01 :: emitRewindAfter := by
  rw [canonicalSource_eq_carrier_layout]
  simp [emitRewindBefore, emitRewindAfter,
    PNP.Concrete.CNFToNANDControllerCountTrace.scanBeforeCells,
    carrierFooterCells, SourceParser.sourceCells,
    List.append_assoc]

private theorem canonicalSource_packed
    (formula : CNFFormula) :
    ∀ symbol, symbol ∈ canonicalSource formula →
      TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  exact
    TargetEmitter.circuitCells_packed
      (CNFToNANDWorkspace.carrierCircuit formula) symbol member

private theorem emit_rewind_path
    (formula : CNFFormula) (runtime : Runtime)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents emitRewindRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (emitRewindBefore formula)
        (SourceParser.cell01 :: emitRewindAfter)
        runtime.targetTokens initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node emitRewindRef)
        (.node emitInstallVersionRef)
        (PNP.Concrete.CNFToNANDControllerCountTrace.sourceRewindSteps
          (emitRewindBefore formula))
        initialTape finalTape ∧
      TapeRepresents emitInstallVersionRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (canonicalSource formula) runtime.targetTokens finalTape := by
  have beforePacked :
      ∀ symbol, symbol ∈ emitRewindBefore formula →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    apply canonicalSource_packed formula symbol
    rw [canonicalSource_eq_emitRewindSplit]
    exact List.mem_append_left _ member
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.source_rewind_path
        Address.emitRewind emitInstallVersionRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (emitRewindBefore formula)
        SourceParser.cell01 emitRewindAfter runtime.targetTokens
        (.node emitInstallVersionRef)
        (by simpa [emitRewindNode] using emitRewindNode_member)
        beforePacked TargetEmitter.PackedSymbol.zeroOne
        initialTape represents with
    ⟨finalTape, path, finalRepresents⟩
  refine ⟨finalTape, ?_, ?_⟩
  · simpa [emitRewindRef] using path
  · rw [canonicalSource_eq_emitRewindSplit formula]
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

private theorem targetEmitter_configAtWord_tape_eq
    (state : Nat) (left right : List WorkSymbol) :
    (TargetEmitter.configAtWord state left right).tape =
      focusTape left right := by
  cases right <;> rfl

private theorem cursorControl_configAtWord_eq
    (state : Nat) (left right : List WorkSymbol) :
    { state := state, tape := focusTape left right } =
      TargetEmitterCursorControl.configAtWord state left right := by
  cases right <;> rfl

private def emitInstallVersionSteps : Nat := 3

private theorem emit_install_version_path
    (formula : CNFFormula) (runtime : Runtime)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents emitInstallVersionRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (canonicalSource formula) runtime.targetTokens initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node emitInstallVersionRef)
        (.node formulaPopFirstRef)
        emitInstallVersionSteps initialTape finalTape ∧
      TapeRepresents formulaPopFirstRef.startState
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
      AcceptPath graph (.node formulaPopFirstRef)
        (.node formulaPopFirstRef) 0
        canonicalFinal canonicalFinal := .terminal _ _
  have canonicalPath :
      AcceptPath graph (.node emitInstallVersionRef)
        (.node formulaPopFirstRef)
        emitInstallVersionSteps canonicalInitial canonicalFinal := by
    simpa [emitInstallVersionSteps, emitInstallVersionRef,
      emitInstallVersionNode] using
      localAccept_path Address.emitInstallVersion
        (TargetEmitterCursorControl.installMachine
          WorkSymbol.zeroZero)
        (.node formulaPopFirstRef) .reject
        (.node formulaPopFirstRef)
        2 0 canonicalInitial canonicalFinal canonicalFinal
        (by simpa [emitInstallVersionNode] using
          emitInstallVersionNode_member)
        run terminal
  have initialEquivalent :
      WorkTape.BlankEquivalent initialTape canonicalInitial := by
    have tapeEquivalent := represents.tape
    have tapeEquivalent' :
        WorkTape.BlankEquivalent initialTape
          (TargetEmitter.configAtWord
            emitInstallVersionRef.startState workspace
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
        formulaPopFirstRef.startState capacity
        runtime.scratch runtime.registers runtime.checks
        (versionMarkedSource formula) runtime.targetTokens |>.symm, ?_⟩
  simpa [canonicalFinal, workspace, suffix, capacity,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterRuntime.logicalLeftWorkspace,
    targetEmitter_configAtWord_tape_eq,
    List.append_assoc] using finalEquivalent

/-! ## Terminal source cleanup -/

private def FinalTapeRepresents
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (tape : WorkTape) : Prop :=
  WorkTape.BlankEquivalent tape
    (TargetEmitterCursorFinalizer.finalTape source
      (SourceParser.packedTokenCells target)
      (TargetEmitterRuntimePrimitives.fixedWorkspace
        capacity scratch registers checks)
      [])

private def finalizerPathSteps (source : List WorkSymbol) : Nat :=
  TargetEmitterCursorFinalizer.workSteps source + 1

private theorem finalizer_accept_path
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (initialTape : WorkTape)
    (allowed :
      ∀ symbol, symbol ∈ source →
        TargetEmitterCursorFinalizer.SourceSymbol symbol)
    (represents :
      TapeRepresents finalizerRef.startState
        capacity scratch registers checks source target initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node finalizerRef) .accept
        (finalizerPathSteps source) initialTape finalTape ∧
      FinalTapeRepresents capacity scratch registers checks
        source target finalTape := by
  let initial : WorkConfiguration :=
    { state := finalizerRef.startState, tape := initialTape }
  let outsideLeft :=
    TargetEmitterRuntimePrimitives.fixedWorkspace
      capacity scratch registers checks
  let canonicalInput :=
    TargetEmitterCursorFinalizer.inputConfiguration source
      (SourceParser.packedTokenCells target) outsideLeft []
  let canonicalFinal :=
    TargetEmitterCursorFinalizer.finalConfiguration source
      (SourceParser.packedTokenCells target) outsideLeft []
  have actualToLogical :
      WorkConfiguration.BlankEquivalent initial
        (TargetEmitterRuntime.logicalConfiguration
          TargetEmitterCursorFinalizer.eraseState
          capacity scratch registers checks source target) := by
    simpa [TapeRepresents, TargetEmitterRuntime.Represents,
      initial, finalizerRef, controlRef,
      TargetEmitterCursorFinalizer.machine] using represents
  have canonicalToLogical :
      WorkConfiguration.BlankEquivalent canonicalInput
        (TargetEmitterRuntime.logicalConfiguration
          TargetEmitterCursorFinalizer.eraseState
          capacity scratch registers checks source target) := by
    cases source with
    | nil =>
        simpa [canonicalInput,
          TargetEmitterCursorFinalizer.inputConfiguration,
          TargetEmitterCursorFinalizer.configurationAtWord,
          TargetEmitterCursorFinalizer.tapeAtWord,
          TargetEmitter.configAtWord,
          TargetEmitterRuntime.logicalLeftWorkspace,
          TargetEmitterRuntimePrimitives.fixedWorkspace,
          TargetEmitterRuntime.logicalWord, outsideLeft,
          List.append_assoc] using
            (TargetEmitterRuntime.padded_blankEquivalent
              TargetEmitterCursorFinalizer.eraseState
              capacity scratch registers checks [] target 0 1)
    | cons head tail =>
        simpa [canonicalInput,
          TargetEmitterCursorFinalizer.inputConfiguration,
          TargetEmitterCursorFinalizer.configurationAtWord,
          TargetEmitterCursorFinalizer.tapeAtWord,
          TargetEmitter.configAtWord,
          TargetEmitterRuntime.logicalLeftWorkspace,
          TargetEmitterRuntimePrimitives.fixedWorkspace,
          TargetEmitterRuntime.logicalWord, outsideLeft,
          List.append_assoc] using
            (TargetEmitterRuntime.padded_blankEquivalent
              TargetEmitterCursorFinalizer.eraseState
              capacity scratch registers checks
              (head :: tail) target 0 1)
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent initial canonicalInput :=
    WorkConfiguration.blankEquivalent_trans actualToLogical
      (WorkConfiguration.blankEquivalent_symm canonicalToLogical)
  have canonicalRun :
      workRunExact? TargetEmitterCursorFinalizer.machine
          (TargetEmitterCursorFinalizer.workSteps source)
          canonicalInput =
        some canonicalFinal := by
    simpa [canonicalInput, canonicalFinal] using
      (TargetEmitterCursorFinalizer.finalize_exact source
        (SourceParser.packedTokenCells target) outsideLeft [] allowed)
  rcases
      workRunExact?_transport TargetEmitterCursorFinalizer.machine
        (TargetEmitterCursorFinalizer.workSteps source)
        inputEquivalent canonicalRun with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  have localRun :
      LocalAcceptRun finalizerNode
        (TargetEmitterCursorFinalizer.workSteps source)
        initialTape actualFinal.tape := by
    apply
      (show
        ∀ (node : Node) (steps : Nat)
          (first last : WorkConfiguration),
          first.state = node.program.startState →
          last.state = node.program.acceptState →
          workRunExact? node.program steps first = some last →
          LocalAcceptRun node steps first.tape last.tape from by
            intro node steps first last firstState lastState run
            rcases first with ⟨firstStateValue, firstTape⟩
            rcases last with ⟨lastStateValue, lastTape⟩
            change firstStateValue = node.program.startState at firstState
            change lastStateValue = node.program.acceptState at lastState
            subst firstStateValue
            subst lastStateValue
            exact run)
        finalizerNode
        (TargetEmitterCursorFinalizer.workSteps source)
        initial actualFinal
    · rfl
    · simpa [finalizerNode, controlNode,
        TargetEmitterCursorFinalizer.machine, canonicalFinal,
        TargetEmitterCursorFinalizer.finalConfiguration] using
        finalEquivalent.state
    · simpa [finalizerNode, controlNode] using exactRun
  have tail :
      AcceptPath graph .accept .accept 0
        actualFinal.tape actualFinal.tape :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.step finalizerNode .accept
      (TargetEmitterCursorFinalizer.workSteps source) 0
      initialTape actualFinal.tape actualFinal.tape
      finalizerNode_member localRun tail
  refine ⟨actualFinal.tape, ?_, ?_⟩
  · simpa [finalizerPathSteps, finalizerRef, finalizerNode,
      controlRef, controlNode, Node.reference] using path
  · simpa [FinalTapeRepresents, canonicalFinal,
      TargetEmitterCursorFinalizer.finalConfiguration,
      outsideLeft] using finalEquivalent.tape

/-! ## Closed completion suffix -/

private def endAndInstallCost
    (formula : CNFFormula) (processed : List CNFToken) : Nat :=
  emitFinishCost formula processed +
    PNP.Concrete.CNFToNANDControllerCountTrace.programEndSteps +
    PNP.Concrete.CNFToNANDControllerCountTrace.sourceRewindSteps
      (emitRewindBefore formula) +
    emitInstallVersionSteps

private theorem end_and_install_path
    (formula : CNFFormula) (processed : List CNFToken)
    (startState restoreState : GrammarState) (kind : FinishKind)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ [.finish])
    (active : startState ∈ activeGrammarStates)
    (valid : validGrammarToken startState .finish = true)
    (installed :
      postInstallEndpoint .emit startState .finish =
        .node (restoreRef .emit restoreState .finish))
    (finished : stateFinishKind? restoreState = some kind)
    (initialTape : WorkTape)
    (represents :
      ScanRepresents (firstBitRef .emit startState).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) processed)
        (scanAfterCells .finish [])
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (firstBitRef .emit startState))
        (.node formulaPopFirstRef) steps initialTape finalTape ∧
      TapeRepresents formulaPopFirstRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (versionMarkedSource formula) runtime.targetTokens finalTape ∧
      steps ≤ endAndInstallCost formula processed := by
  rcases
      emit_finish_path formula processed startState restoreState kind
        runtime tokens active valid installed finished
        initialTape represents with
    ⟨finishSteps, finishTape, finishPath,
      finishRepresents, finishBound⟩
  rcases
      PNP.Concrete.CNFToNANDControllerCountTrace.program_end_path
        .emit kind (CNFToNANDWorkspace.capacity formula) runtime
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (CNFToNANDWorkspace.formulaTokens formula))
        finishTape (by simpa [tokens, List.append_assoc] using
          finishRepresents) with
    ⟨programTape, programPath, rewindRepresents⟩
  have rewindInput :
      ScanRepresents emitRewindRef.startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (emitRewindBefore formula)
        (SourceParser.cell01 :: emitRewindAfter)
        runtime.targetTokens programTape := by
    simpa [PNP.Concrete.CNFToNANDControllerCountTrace.passRewindRef,
      emitRewindBefore, emitRewindAfter,
      carrierFooterCells, SourceParser.sourceCells,
      List.append_assoc] using rewindRepresents
  rcases
      emit_rewind_path formula runtime programTape rewindInput with
    ⟨rewoundTape, rewindPath, installRepresents⟩
  rcases
      emit_install_version_path formula runtime
        rewoundTape installRepresents with
    ⟨finalTape, installPath, finalRepresents⟩
  let totalSteps :=
    finishSteps +
      PNP.Concrete.CNFToNANDControllerCountTrace.programEndSteps +
      PNP.Concrete.CNFToNANDControllerCountTrace.sourceRewindSteps
        (emitRewindBefore formula) +
      emitInstallVersionSteps
  refine ⟨totalSteps, finalTape, ?_, finalRepresents, ?_⟩
  · dsimp [totalSteps]
    exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        (AcceptPath.trans graph _ _ _ _ _ _ _ _
          (AcceptPath.trans graph _ _ _ _ _ _ _ _
            finishPath programPath)
          rewindPath)
        installPath
  · unfold endAndInstallCost
    dsimp [totalSteps]
    omega

private theorem clauseListRuntime_registers
    (width : Nat) (clauses : List (List CNFLiteral))
    (runtime : Runtime) :
    (clauseListRuntime width clauses runtime).registers =
      { runtime.registers with
        outputIndex :=
          runtime.registers.outputIndex +
            clauseListGateCount width clauses } := by
  induction clauses generalizing runtime with
  | nil =>
      simp [clauseListRuntime, clauseListGateCount]
  | cons clause rest inductionHypothesis =>
      rw [clauseListRuntime, inductionHypothesis,
        clauseRuntime_registers]
      change
        { runtime.registers with
          outputIndex :=
            (runtime.registers.outputIndex +
                clauseGateCount width clause) +
              clauseListGateCount width rest } =
        { runtime.registers with
          outputIndex :=
            runtime.registers.outputIndex +
              (clauseGateCount width clause +
                clauseListGateCount width rest) }
      rw [Nat.add_assoc]

private theorem clauseListRuntime_fits
    (capacity width : Nat) (clauses : List (List CNFLiteral))
    (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (outputBound :
      runtime.registers.outputIndex +
          clauseListGateCount width clauses ≤ capacity) :
    LedgerFits capacity
      (clauseListRuntime width clauses runtime).registers := by
  rw [clauseListRuntime_registers]
  exact
    { inputCount := fits.inputCount
      normalizedGateCount := fits.normalizedGateCount
      carrierWidth := fits.carrierWidth
      baseline := fits.baseline
      currentGate := fits.currentGate
      outputIndex := outputBound }

private theorem clauseListRuntime_scratch_of_zero
    (width : Nat) (clauses : List (List CNFLiteral))
    (runtime : Runtime) (zero : runtime.scratch = 0) :
    (clauseListRuntime width clauses runtime).scratch = 0 := by
  induction clauses generalizing runtime with
  | nil =>
      simpa [clauseListRuntime] using zero
  | cons clause rest inductionHypothesis =>
      rw [clauseListRuntime]
      apply inductionHypothesis
      exact clauseRuntime_scratch width clause runtime

private theorem formulaFoldLoopRuntime_registers
    (count : Nat) (runtime : Runtime) :
    (formulaFoldLoopRuntime count runtime).registers =
      { runtime.registers with
        outputIndex :=
          runtime.registers.outputIndex + 2 * count } := by
  induction count generalizing runtime with
  | zero =>
      simp [formulaFoldLoopRuntime, popNewestResult]
  | succ count inductionHypothesis =>
      rw [formulaFoldLoopRuntime, inductionHypothesis,
        extendFormulaResult_registers]
      change
        { runtime.registers with
          outputIndex :=
            (runtime.registers.outputIndex + 2) + 2 * count } =
        { runtime.registers with
          outputIndex :=
            runtime.registers.outputIndex + 2 * (count + 1) }
      rw [show
        (runtime.registers.outputIndex + 2) + 2 * count =
          runtime.registers.outputIndex + 2 * (count + 1) by omega]

private theorem formulaFoldRuntime_registers
    (count : Nat) (runtime : Runtime) :
    (formulaFoldRuntime count runtime).registers =
      { runtime.registers with
        outputIndex :=
          runtime.registers.outputIndex +
            (if count = 0 then 0 else 2 * count - 1) } := by
  cases count with
  | zero =>
      simp [formulaFoldRuntime, emptyFormulaResult,
        popNewestResult, emitGateResult, emitSourceResult]
  | succ count =>
      rw [formulaFoldRuntime, formulaFoldLoopRuntime_registers,
        seedFormulaResult_registers]
      change
        { runtime.registers with
          outputIndex :=
            (runtime.registers.outputIndex + 1) + 2 * count } =
        { runtime.registers with
          outputIndex :=
            runtime.registers.outputIndex +
              (if count + 1 = 0 then 0
                else 2 * (count + 1) - 1) }
      simp
      rw [show
        (runtime.registers.outputIndex + 1) + 2 * count =
          runtime.registers.outputIndex +
            (2 * (count + 1) - 1) by omega]

private theorem emptyFormulaResult_scratch (runtime : Runtime) :
    (emptyFormulaResult runtime).scratch = runtime.scratch := by
  simp [emptyFormulaResult, emitGateResult, emitSourceResult,
    EmissionSource.finalScratch]

private theorem formulaFoldLoopRuntime_scratch_of
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks = prior ++ marker :: pending.reverse) :
    (formulaFoldLoopRuntime pending.length runtime).scratch = marker := by
  induction pending generalizing runtime with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      have newest :=
        popNewestResult_of_checks runtime prior marker checks'
      simp [formulaFoldLoopRuntime, newest, popCoordinateResult]
  | cons value rest inductionHypothesis =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have newest := popNewestResult_of_checks runtime
        (prior ++ marker :: rest.reverse) value checks'
      have extendedChecks :
          (extendFormulaResult
              (runtimeClauseSource popped) popped).checks =
            prior ++ marker :: rest.reverse := by
        rw [extendFormulaResult_checks]
        simp [popped, popCoordinateResult]
      simp only [List.length_cons]
      rw [formulaFoldLoopRuntime, newest]
      exact inductionHypothesis _ extendedChecks

private theorem formulaFoldRuntime_scratch_of
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks = prior ++ marker :: pending.reverse) :
    (formulaFoldRuntime pending.length runtime).scratch = marker := by
  cases pending with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      have newest :=
        popNewestResult_of_checks runtime prior marker checks'
      simp [formulaFoldRuntime, newest, popCoordinateResult,
        emptyFormulaResult_scratch]
  | cons value rest =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have newest := popNewestResult_of_checks runtime
        (prior ++ marker :: rest.reverse) value checks'
      have seededChecks :
          (seedFormulaResult
              (runtimeClauseSource popped) popped).checks =
            prior ++ marker :: rest.reverse := by
        rw [seedFormulaResult_checks]
        simp [popped, popCoordinateResult]
      simp only [List.length_cons]
      rw [formulaFoldRuntime, newest]
      exact formulaFoldLoopRuntime_scratch_of
        prior marker rest _ seededChecks

private theorem formulaStackMarker_lt_capacity
    (formula : CNFFormula) :
    CNFToNANDWorkspace.formulaStackMarker formula <
      CNFToNANDWorkspace.capacity formula := by
  rw [CNFToNANDWorkspace.formulaStackMarker_exact,
    CNFToNANDWorkspace.capacity_exact]
  omega

private def formulaSuffixCost (formula : CNFFormula) : Nat :=
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses
      (emitInitialRuntime formula)
  let coordinates :=
    clauseListCoordinates formula.variableCount formula.clauses
      (emitInitialRuntime formula)
  formulaFoldCost (CNFToNANDWorkspace.capacity formula)
      (versionMarkedSource formula) coordinates.reverse clauses +
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
      (CNFToNANDWorkspace.capacity formula)
      (versionMarkedSource formula)
      (formulaFoldRuntime formula.clauses.length clauses)
      blockDescriptors[32].primitives +
    finalizerPathSteps (versionMarkedSource formula)

private theorem formula_suffix_accept_path
    (formula : CNFFormula) (initialTape : WorkTape)
    (represents :
      TapeRepresents formulaPopFirstRef.startState
        (CNFToNANDWorkspace.capacity formula)
        (clauseListRuntime formula.variableCount formula.clauses
          (emitInitialRuntime formula)).scratch
        (clauseListRuntime formula.variableCount formula.clauses
          (emitInitialRuntime formula)).registers
        (clauseListRuntime formula.variableCount formula.clauses
          (emitInitialRuntime formula)).checks
        (versionMarkedSource formula)
        (clauseListRuntime formula.variableCount formula.clauses
          (emitInitialRuntime formula)).targetTokens
        initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node formulaPopFirstRef) .accept
        steps initialTape finalTape ∧
      FinalTapeRepresents
        (CNFToNANDWorkspace.capacity formula)
        (completedRuntime formula).scratch
        (completedRuntime formula).registers
        (completedRuntime formula).checks
        (versionMarkedSource formula)
        (completedRuntime formula).targetTokens
        finalTape ∧
      steps ≤ formulaSuffixCost formula := by
  let initial := emitInitialRuntime formula
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses initial
  let coordinates :=
    clauseListCoordinates formula.variableCount formula.clauses initial
  let pending := coordinates.reverse
  let marker := CNFToNANDWorkspace.formulaStackMarker formula
  let capacity := CNFToNANDWorkspace.capacity formula
  let source := versionMarkedSource formula
  let context := versionMarkedSourceContext formula
  let layout := versionMarkedCursorLayout formula
  have clauseBudget :
      initial.registers.outputIndex +
          clauseListGateCount formula.variableCount formula.clauses ≤
        initial.registers.currentGate := by
    change
      0 +
          clauseListGateCount formula.variableCount formula.clauses ≤
        CNFToNANDWorkspace.compilerGateCount formula
    rw [compilerGateCount_eq_structural]
    omega
  have clausesFits :
      LedgerFits capacity clauses.registers := by
    apply clauseListRuntime_fits
    · exact emitInitialRuntime_fits formula
    · exact Nat.le_trans clauseBudget
        (Nat.le_of_lt
          (CNFToNANDWorkspace.compilerGateCount_lt_capacity formula))
  have clausesScratch : clauses.scratch < capacity := by
    have zero :
        clauses.scratch = 0 := by
      exact clauseListRuntime_scratch_of_zero
        formula.variableCount formula.clauses initial rfl
    rw [zero]
    exact Nat.zero_lt_of_lt
      (formulaStackMarker_lt_capacity formula)
  have clausesChecks :
      clauses.checks =
        [] ++ marker :: pending.reverse := by
    rw [show pending.reverse = coordinates by
      simp [pending]]
    simpa [clauses, coordinates, initial, marker,
      emitInitialRuntime] using
      (clauseListRuntime_checks formula.variableCount
        formula.clauses initial)
  have markerExact :
      marker = clauses.registers.carrierWidth := by
    rw [clauseListRuntime_carrierWidth]
    simp [marker, initial, emitInitialRuntime,
      CNFToNANDWorkspace.workspaceRegisters_carrierWidth_eq_formulaStackMarker]
  have markerBound :
      clauses.registers.carrierWidth < capacity := by
    rw [← markerExact]
    exact formulaStackMarker_lt_capacity formula
  have gateBelow :
      clauses.registers.currentGate <
        clauses.registers.carrierWidth := by
    rw [clauseListRuntime_currentGate,
      clauseListRuntime_carrierWidth]
    change
      CNFToNANDWorkspace.compilerGateCount formula <
        (CNFToNANDWorkspace.workspaceRegisters formula).carrierWidth
    exact
      CNFToNANDWorkspace.compilerGateCount_lt_workspaceCarrierWidth
        formula
  have coordinateClasses :
      ∀ value, value ∈ pending →
        value = clauses.registers.currentGate ∨
          value < clauses.registers.currentGate := by
    intro value member
    have originalMember :
        value ∈ coordinates := List.mem_reverse.mp member
    have classified :=
      clauseListCoordinates_classified formula.variableCount
        formula.clauses initial clauseBudget value
        (by simpa [coordinates] using originalMember)
    rw [clauseListRuntime_currentGate]
    simpa [clauses] using classified
  have formulaOutput :
      clauses.registers.outputIndex +
          (if pending.isEmpty then 0
            else 2 * pending.length - 1) ≤ capacity := by
    have gateCapacity :=
      CNFToNANDWorkspace.compilerGateCount_lt_capacity formula
    cases clauseCase : formula.clauses with
    | nil =>
        have pendingLength :
            pending.length = 0 := by
          simpa [clauseCase] using
            (show pending.length = formula.clauses.length by
              simp [pending, coordinates,
                clauseListCoordinates_length])
        cases pendingEq : pending with
        | nil =>
            have structural :=
              compilerGateCount_eq_structural formula
            rw [clauseCase] at structural
            simp at structural
            simp [clauses, pendingEq, clauseCase,
              clauseListRuntime, initial, emitInitialRuntime,
              CNFToNANDWorkspace.workspaceRegisters_outputIndex]
        | cons head tail =>
            rw [pendingEq] at pendingLength
            simp at pendingLength
    | cons clause rest =>
        have structural :=
          compilerGateCount_eq_structural formula
        rw [clauseCase] at structural
        have clausesOutput :=
          clauseListRuntime_outputIndex formula.variableCount
            formula.clauses initial
        have pendingLength :
            pending.length = formula.clauses.length := by
          simp [pending, coordinates,
            clauseListCoordinates_length]
        cases pendingEq : pending with
        | nil =>
            rw [pendingEq] at pendingLength
            rw [clauseCase] at pendingLength
            simp only [List.length_nil, List.length_cons] at pendingLength
            omega
        | cons head tail =>
            simp only [pendingEq, List.isEmpty, Bool.false_eq_true,
              if_false, List.length_cons]
            have clausesOutput' :
                clauses.registers.outputIndex =
                  initial.registers.outputIndex +
                    clauseListGateCount formula.variableCount
                      formula.clauses := by
              simpa [clauses] using clausesOutput
            rw [clausesOutput']
            have initialOutput :
                initial.registers.outputIndex = 0 := by rfl
            rw [initialOutput]
            rw [pendingEq, clauseCase] at pendingLength
            rw [clauseCase] at ⊢
            simp at pendingLength structural
            omega
  have foldInput :
      TapeRepresents formulaPopFirstRef.startState
        capacity clauses.scratch clauses.registers clauses.checks
        source clauses.targetTokens initialTape := by
    simpa [capacity, clauses, initial, source] using represents
  rcases
      formula_fold_path (context := context) layout
        [] marker pending clauses clausesChecks clausesFits
        clausesScratch markerExact markerBound gateBelow
        coordinateClasses formulaOutput initialTape foldInput with
    ⟨foldSteps, suffixTape, foldPath,
      suffixRepresents, foldBound⟩
  let folded := formulaFoldRuntime pending.length clauses
  have foldedOutput :
      folded.registers.outputIndex ≤ capacity := by
    dsimp [folded]
    rw [formulaFoldRuntime_registers]
    rw [clauseListRuntime_outputIndex]
    have initialOutput :
        initial.registers.outputIndex = 0 := by rfl
    rw [initialOutput]
    have pendingLength :
        pending.length = formula.clauses.length := by
      simp [pending, coordinates, clauseListCoordinates_length]
    rw [pendingLength]
    cases clauseCase : formula.clauses with
    | nil =>
        have structural :=
          compilerGateCount_eq_structural formula
        rw [clauseCase] at structural
        have gateCapacity :=
          CNFToNANDWorkspace.compilerGateCount_lt_capacity formula
        simp at structural ⊢
        omega
    | cons clause rest =>
        have structural :=
          compilerGateCount_eq_structural formula
        rw [clauseCase] at structural
        have gateCapacity :=
          CNFToNANDWorkspace.compilerGateCount_lt_capacity formula
        simp [clauseCase] at structural ⊢
        omega
  have foldedFits :
      LedgerFits capacity folded.registers := by
    have registersEq :=
      formulaFoldRuntime_registers pending.length clauses
    change LedgerFits capacity
      (formulaFoldRuntime pending.length clauses).registers
    rw [registersEq]
    have output :
        clauses.registers.outputIndex +
            (if pending.length = 0 then 0
              else 2 * pending.length - 1) ≤ capacity := by
      have foldedOutput' := foldedOutput
      change
        (formulaFoldRuntime pending.length clauses).registers.outputIndex ≤
          capacity at foldedOutput'
      rw [formulaFoldRuntime_registers] at foldedOutput'
      exact foldedOutput'
    exact
      { inputCount := clausesFits.inputCount
        normalizedGateCount := clausesFits.normalizedGateCount
        carrierWidth := clausesFits.carrierWidth
        baseline := clausesFits.baseline
        currentGate := clausesFits.currentGate
        outputIndex := output }
  have foldedScratch : folded.scratch < capacity := by
    have scratchEq :
        folded.scratch = marker := by
      exact formulaFoldRuntime_scratch_of
        [] marker pending clauses clausesChecks
    rw [scratchEq]
    exact formulaStackMarker_lt_capacity formula
  have suffixInput :
      TapeRepresents suffixRef.startState
        capacity folded.scratch folded.registers folded.checks
        source folded.targetTokens suffixTape := by
    simpa [folded] using suffixRepresents
  rcases
      suffixBlock_path (context := context) layout folded
        foldedFits foldedScratch foldedOutput
        suffixTape suffixInput with
    ⟨suffixSteps, finalizerTape, suffixPath,
      finalizerRepresents, suffixBound⟩
  have allowed :
      ∀ symbol, symbol ∈ source →
        TargetEmitterCursorFinalizer.SourceSymbol symbol :=
    PNP.Concrete.LockedNAND.TargetEmitterControllerOutputTrace.CursorLayout.finalizerAllowed
      layout
  rcases
      finalizer_accept_path capacity
        (circuitSuffixResult folded).scratch
        (circuitSuffixResult folded).registers
        (circuitSuffixResult folded).checks source
        (circuitSuffixResult folded).targetTokens
        finalizerTape allowed finalizerRepresents with
    ⟨finalTape, finalizerPath, finalRepresents⟩
  refine
    ⟨foldSteps + suffixSteps +
        finalizerPathSteps source,
      finalTape,
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        (AcceptPath.trans graph _ _ _ _ _ _ _ _
          foldPath suffixPath)
        finalizerPath,
      ?_, ?_⟩
  · simpa [completedRuntime, formulaRuntime, folded,
      pending, coordinates, clauses, initial, source,
      clauseListCoordinates_length] using finalRepresents
  · unfold formulaSuffixCost
    dsimp only
    have pendingLength :
        pending.length = formula.clauses.length := by
      simp [pending, coordinates, clauseListCoordinates_length]
    rw [← pendingLength]
    dsimp [capacity, source] at foldBound suffixBound ⊢
    change
      foldSteps + suffixSteps +
          finalizerPathSteps (versionMarkedSource formula) ≤
        formulaFoldCost
            (CNFToNANDWorkspace.capacity formula)
            (versionMarkedSource formula) pending clauses +
          TargetEmitterRuntimeProgramBound.programWorkEnvelope
            (CNFToNANDWorkspace.capacity formula)
            (versionMarkedSource formula)
            folded blockDescriptors[32].primitives +
          finalizerPathSteps (versionMarkedSource formula)
    omega

/-! ## Complete emitting traversal -/

def emitTraversalCost (formula : CNFFormula) : Nat :=
  emitHeaderScanSteps formula +
    emitWidthCost formula formula.variableCount [] +
    clauseListPathCost formula
      (encodeUnaryTokens formula.variableCount)
      .clausesEmpty formula.clauses .finish []
      (emitInitialRuntime formula)

private theorem emit_traversal_path
    (formula : CNFFormula) (initialTape : WorkTape)
    (represents :
      TapeRepresents (passHeaderRef .emit).startState
        (CNFToNANDWorkspace.capacity formula)
        (emitInitialRuntime formula).scratch
        (emitInitialRuntime formula).registers
        (emitInitialRuntime formula).checks
        (canonicalSource formula)
        (emitInitialRuntime formula).targetTokens
        initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (passHeaderRef .emit))
        (.node (firstBitRef .emit
          (if formula.clauses.isEmpty
            then .clausesEmpty else .clausesNonempty)))
        steps initialTape finalTape ∧
      ScanRepresents
        (firstBitRef .emit
          (if formula.clauses.isEmpty
            then .clausesEmpty else .clausesNonempty)).startState
        (CNFToNANDWorkspace.capacity formula)
        (clauseListRuntime formula.variableCount formula.clauses
          (emitInitialRuntime formula)).scratch
        (clauseListRuntime formula.variableCount formula.clauses
          (emitInitialRuntime formula)).registers
        (clauseListRuntime formula.variableCount formula.clauses
          (emitInitialRuntime formula)).checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (encodeUnaryTokens formula.variableCount ++
            encodeClauseListTokens formula.clauses))
        (scanAfterCells .finish [])
        (clauseListRuntime formula.variableCount formula.clauses
          (emitInitialRuntime formula)).targetTokens
        finalTape ∧
      steps ≤ emitTraversalCost formula := by
  let runtime := emitInitialRuntime formula
  rcases emit_header_path formula runtime initialTape represents with
    ⟨first, rest, headerTape, tokensEq, headerPath,
      headerRepresents⟩
  let suffix :=
    encodeClauseListTokens formula.clauses ++ [.finish]
  have suffixNe : suffix ≠ [] := by simp [suffix]
  obtain ⟨next, tail, suffixEq⟩ :=
    List.exists_cons_of_ne_nil suffixNe
  have widthTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        [] ++ encodeUnaryTokens formula.variableCount ++
          next :: tail := by
    simp only [List.nil_append]
    rw [← suffixEq]
    simp [CNFToNANDWorkspace.formulaTokens,
      encodeFormulaTokens, encodeCNFTokens, suffix,
      List.append_assoc]
  have headerInput :
      ScanRepresents (firstBitRef .emit .header).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula) [])
        (carrierGateCells
            (encodeUnaryTokens formula.variableCount ++
              next :: tail) ++ carrierFooterCells)
        runtime.targetTokens headerTape := by
    have allEq :
        first :: rest =
          encodeUnaryTokens formula.variableCount ++ next :: tail :=
      tokensEq.symm.trans widthTokens
    rw [allEq] at headerRepresents
    have emptyGates :
        carrierGateCells ([] : List CNFToken) = [] := by
      rfl
    simpa [
      PNP.Concrete.CNFToNANDControllerCountTrace.scanBeforeCells,
      widthTokens, emptyGates] using headerRepresents
  rcases
      emit_width_path formula runtime formula.variableCount []
        next tail widthTokens headerTape headerInput with
    ⟨widthSteps, widthTape, widthPath, widthRepresents,
      widthBound⟩
  have clauseInput :
      ScanRepresents (firstBitRef .emit .clausesEmpty).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          (encodeUnaryTokens formula.variableCount))
        (carrierGateCells
            (encodeClauseListTokens formula.clauses ++
              [.finish]) ++ carrierFooterCells)
        runtime.targetTokens widthTape := by
    have tailEq :
        next :: tail =
          encodeClauseListTokens formula.clauses ++ [.finish] := by
      exact suffixEq.symm.trans (by rfl)
    have afterEq :
        PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells
            next tail =
          carrierGateCells
              (encodeClauseListTokens formula.clauses ++ [.finish]) ++
            carrierFooterCells := by
      unfold
        PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells
      change
        carrierGateCells (next :: tail) ++ carrierFooterCells =
          carrierGateCells
              (encodeClauseListTokens formula.clauses ++ [.finish]) ++
            carrierFooterCells
      rw [tailEq]
    change
      ScanRepresents
        (firstBitRef .emit .clausesEmpty).startState
        (CNFToNANDWorkspace.capacity formula)
        runtime.scratch runtime.registers runtime.checks
        (PNP.Concrete.CNFToNANDControllerCountTrace.scanBeforeCells
          (CNFToNANDWorkspace.formulaTokens formula)
          ([] ++ encodeUnaryTokens formula.variableCount))
        (PNP.Concrete.CNFToNANDControllerCountTrace.scanAfterCells
          next tail)
        runtime.targetTokens widthTape at widthRepresents
    rw [afterEq] at widthRepresents
    simpa using widthRepresents
  have clauseTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        encodeUnaryTokens formula.variableCount ++
          encodeClauseListTokens formula.clauses ++
            .finish :: [] := by
    rfl
  have clauseBudget :
      runtime.registers.outputIndex +
          clauseListGateCount formula.variableCount formula.clauses ≤
        runtime.registers.currentGate := by
    change
      0 +
          clauseListGateCount formula.variableCount formula.clauses ≤
        CNFToNANDWorkspace.compilerGateCount formula
    rw [compilerGateCount_eq_structural]
    omega
  rcases
      emit_clause_list_path formula
        (encodeUnaryTokens formula.variableCount)
        .clausesEmpty formula.clauses .finish [] runtime
        clauseTokens
        (by simp [activeGrammarStates]) (by decide) rfl
        (emitInitialRuntime_fits formula)
        (by simp [runtime, emitInitialRuntime,
          CNFToNANDWorkspace.workspaceRegisters_inputCount])
        (by simp [runtime, emitInitialRuntime]
            exact Nat.zero_lt_of_lt
              (formulaStackMarker_lt_capacity formula))
        (by simp [runtime, emitInitialRuntime,
          CNFToNANDWorkspace.workspaceRegisters_currentGate])
        clauseBudget widthTape clauseInput with
    ⟨clauseSteps, finalTape, clausePath,
      finalRepresents, clauseBound⟩
  refine
    ⟨emitHeaderScanSteps formula + widthSteps + clauseSteps,
      finalTape,
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        (AcceptPath.trans graph _ _ _ _ _ _ _ _
          headerPath widthPath)
        clausePath,
      ?_, ?_⟩
  · simpa [runtime] using finalRepresents
  · unfold emitTraversalCost
    simpa [runtime, Nat.add_assoc] using
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.le_refl (emitHeaderScanSteps formula)) widthBound)
        clauseBound

def completionEnvelope (formula : CNFFormula) : Nat :=
  emitTraversalCost formula +
    endAndInstallCost formula
      (encodeUnaryTokens formula.variableCount ++
        encodeClauseListTokens formula.clauses) +
    formulaSuffixCost formula

private theorem completion_physical_path
    (formula : CNFFormula) (initialTape : WorkTape)
    (represents :
      TapeRepresents (passHeaderRef .emit).startState
        (CNFToNANDWorkspace.capacity formula)
        (emitInitialRuntime formula).scratch
        (emitInitialRuntime formula).registers
        (emitInitialRuntime formula).checks
        (canonicalSource formula)
        (emitInitialRuntime formula).targetTokens
        initialTape) :
    ∃ steps finalTape,
      steps ≤ completionEnvelope formula ∧
      AcceptPath graph (.node (passHeaderRef .emit)) .accept
        steps initialTape finalTape ∧
      FinalTapeRepresents
        (CNFToNANDWorkspace.capacity formula)
        (completedRuntime formula).scratch
        (completedRuntime formula).registers
        (completedRuntime formula).checks
        (versionMarkedSource formula)
        (completedRuntime formula).targetTokens
        finalTape := by
  rcases emit_traversal_path formula initialTape represents with
    ⟨traversalSteps, traversalTape, traversalPath,
      traversalRepresents, traversalBound⟩
  let processed :=
    encodeUnaryTokens formula.variableCount ++
      encodeClauseListTokens formula.clauses
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses
      (emitInitialRuntime formula)
  have tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ [.finish] := by
    rfl
  cases clauseCase : formula.clauses with
  | nil =>
      have endInput :
          ScanRepresents
            (firstBitRef .emit .clausesEmpty).startState
            (CNFToNANDWorkspace.capacity formula)
            clauses.scratch clauses.registers clauses.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells .finish [])
            clauses.targetTokens traversalTape := by
        simpa [clauseCase, clauses, processed] using
          traversalRepresents
      rcases
          end_and_install_path formula processed
            .clausesEmpty .finishedEmpty .empty clauses
            tokens (by simp [activeGrammarStates]) (by decide)
            rfl rfl traversalTape endInput with
        ⟨endSteps, formulaTape, endPath,
          formulaRepresents, endBound⟩
      rcases
          formula_suffix_accept_path formula formulaTape
            (by simpa [clauses] using formulaRepresents) with
        ⟨suffixSteps, finalTape, suffixPath,
          finalRepresents, suffixBound⟩
      refine
        ⟨traversalSteps + endSteps + suffixSteps,
          finalTape, ?_,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            (AcceptPath.trans graph _ _ _ _ _ _ _ _
              (by simpa [clauseCase] using traversalPath)
              endPath)
            suffixPath,
          finalRepresents⟩
      unfold completionEnvelope
      have endBound' :
          endSteps ≤
            endAndInstallCost formula
              (encodeUnaryTokens formula.variableCount ++
                encodeClauseListTokens formula.clauses) := by
        simpa [processed] using endBound
      omega
  | cons clause rest =>
      have endInput :
          ScanRepresents
            (firstBitRef .emit .clausesNonempty).startState
            (CNFToNANDWorkspace.capacity formula)
            clauses.scratch clauses.registers clauses.checks
            (scanBeforeCells
              (CNFToNANDWorkspace.formulaTokens formula) processed)
            (scanAfterCells .finish [])
            clauses.targetTokens traversalTape := by
        simpa [clauseCase, clauses, processed] using
          traversalRepresents
      rcases
          end_and_install_path formula processed
            .clausesNonempty .finishedNonempty .nonempty clauses
            tokens (by simp [activeGrammarStates]) (by decide)
            rfl rfl traversalTape endInput with
        ⟨endSteps, formulaTape, endPath,
          formulaRepresents, endBound⟩
      rcases
          formula_suffix_accept_path formula formulaTape
            (by simpa [clauses] using formulaRepresents) with
        ⟨suffixSteps, finalTape, suffixPath,
          finalRepresents, suffixBound⟩
      refine
        ⟨traversalSteps + endSteps + suffixSteps,
          finalTape, ?_,
          AcceptPath.trans graph _ _ _ _ _ _ _ _
            (AcceptPath.trans graph _ _ _ _ _ _ _ _
              (by simpa [clauseCase] using traversalPath)
              endPath)
            suffixPath,
          finalRepresents⟩
      unfold completionEnvelope
      have endBound' :
          endSteps ≤
            endAndInstallCost formula
              (encodeUnaryTokens formula.variableCount ++
                encodeClauseListTokens formula.clauses) := by
        simpa [processed] using endBound
      omega

private theorem run_push_negate_probe
    (source : LockedNAND.RawSource)
    (state : CNFToNAND.CompilationState) :
    CNFToNAND.runCompilationPlan
        [.push source, .negate] state =
      some
        { gates :=
            state.gates ++
              [{ left := source, right := source }]
          stack :=
            .gate state.gates.length :: state.stack } := by
  simp [CNFToNAND.runCompilationPlan,
    CNFToNAND.CompilationAction.step]
  rfl

/-! ## Pure postfix correspondence -/

private def decodedCoordinate (total coordinate : Nat) :
    LockedNAND.RawSource :=
  if coordinate = total then
    .constant false
  else
    .gate coordinate

private def encodedCoordinate (total : Nat) :
    LockedNAND.RawSource → Nat
  | .constant false => total
  | .constant true => total
  | .input index => index
  | .gate index => index

private theorem encodeGateListTokens_append_local
    (first second : List LockedNAND.RawGate) :
    encodeGateListTokens (first ++ second) =
      encodeGateListTokens first ++ encodeGateListTokens second := by
  induction first with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      simp [encodeGateListTokens, inductionHypothesis,
        List.append_assoc]

private structure RuntimeMatchesCompilation
    (formula : CNFFormula)
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime) : Prop where
  scratch : runtime.scratch = 0
  currentGate :
    runtime.registers.currentGate =
      CNFToNANDWorkspace.compilerGateCount formula
  outputIndex :
    runtime.registers.outputIndex = state.gates.length
  targetTokens :
    runtime.targetTokens =
      headerTokens formula ++
        encodeGateListTokens state.gates
  checks :
    runtime.checks =
      CNFToNANDWorkspace.formulaStackMarker formula ::
        state.stack.reverse.map
          (encodedCoordinate
            (CNFToNANDWorkspace.compilerGateCount formula))

private def emittedNandState
    (state : CNFToNAND.CompilationState)
    (left right : LockedNAND.RawSource)
    (rest : List LockedNAND.RawSource) :
    CNFToNAND.CompilationState :=
  { gates :=
      state.gates ++ [{ left := left, right := right }]
    stack := .gate state.gates.length :: rest }

private def literalCompilationResult
    (width : Nat) (literal : CNFLiteral)
    (state : CNFToNAND.CompilationState) :
    CNFToNAND.CompilationState :=
  if literal.variableIndex < width then
    if literal.positive then
      emittedNandState state
        (.input literal.variableIndex)
        (.input literal.variableIndex) state.stack
    else
      let first :=
        emittedNandState state
          (.input literal.variableIndex)
          (.input literal.variableIndex) state.stack
      emittedNandState first
        (.gate state.gates.length)
        (.gate state.gates.length) state.stack
  else
    emittedNandState state
      (.constant false) (.constant false) state.stack

private theorem literalRuntime_matchesCompilation
    (formula : CNFFormula) (width : Nat)
    (literal : CNFLiteral)
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime)
    (correspondence :
      RuntimeMatchesCompilation formula state runtime) :
    RuntimeMatchesCompilation formula
      (literalCompilationResult width literal state)
      (literalRuntime width literal runtime) := by
  rcases correspondence with
    ⟨scratch, currentGate, outputIndex, targetTokens, checks⟩
  by_cases valid : literal.variableIndex < width
  · cases polarity : literal.positive
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [literalRuntime, valid, polarity,
          negativeLiteralResult, advanceOutputIndexResult,
          pushGateAtResult, emitGateResult, emitSourceResult]
      · simpa [literalRuntime, valid, polarity,
          negativeLiteralResult, advanceOutputIndexResult,
          pushGateAtResult, emitGateResult, emitSourceResult] using
          currentGate
      · simp [literalRuntime, literalCompilationResult,
          valid, polarity, negativeLiteralResult,
          advanceOutputIndexResult, pushGateAtResult,
          emitGateResult, emitSourceResult, emittedNandState,
          outputIndex]
      · simp [literalRuntime, literalCompilationResult,
          valid, polarity, negativeLiteralResult,
          advanceOutputIndexResult, pushGateAtResult,
          emitGateResult_targetTokens,
          encodeGateListTokens_append_local,
          emittedNandState, outputIndex, targetTokens,
          Nat.min_eq_left (Nat.le_of_lt valid),
          EmissionSource.evaluate, emitSourceResult,
          EmissionSource.finalScratch, emitGateResult,
          encodeGateListTokens, encodeGateTokens,
          List.append_assoc]
      · simp [literalRuntime, literalCompilationResult,
          valid, polarity, negativeLiteralResult,
          advanceOutputIndexResult, pushGateAtResult,
          emitGateResult, emitSourceResult, emittedNandState,
          encodedCoordinate, checks, outputIndex,
          List.reverse_cons, List.map_append,
          List.append_assoc]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [literalRuntime, valid, polarity,
          positiveLiteralResult, advanceOutputIndexResult,
          pushGateAtResult, emitGateResult, emitSourceResult]
      · simpa [literalRuntime, valid, polarity,
          positiveLiteralResult, advanceOutputIndexResult,
          pushGateAtResult, emitGateResult, emitSourceResult] using
          currentGate
      · simp [literalRuntime, literalCompilationResult,
          valid, polarity, positiveLiteralResult,
          advanceOutputIndexResult, pushGateAtResult,
          emitGateResult, emitSourceResult, emittedNandState,
          outputIndex]
      · simp [literalRuntime, literalCompilationResult,
          valid, polarity, positiveLiteralResult,
          advanceOutputIndexResult, pushGateAtResult,
          emitGateResult_targetTokens,
          encodeGateListTokens_append_local,
          emittedNandState, outputIndex, targetTokens,
          Nat.min_eq_left (Nat.le_of_lt valid),
          EmissionSource.evaluate, emitSourceResult,
          EmissionSource.finalScratch, emitGateResult,
          encodeGateListTokens, encodeGateTokens,
          List.append_assoc]
      · simp [literalRuntime, literalCompilationResult,
          valid, polarity, positiveLiteralResult,
          advanceOutputIndexResult, pushGateAtResult,
          emitGateResult, emitSourceResult, emittedNandState,
          encodedCoordinate, checks, outputIndex,
          List.reverse_cons, List.map_append,
          List.append_assoc]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [literalRuntime, valid,
        invalidLiteralResult, advanceOutputIndexResult,
        pushGateAtResult, emitGateResult, emitSourceResult]
    · simpa [literalRuntime, valid,
        invalidLiteralResult, advanceOutputIndexResult,
        pushGateAtResult, emitGateResult, emitSourceResult] using
        currentGate
    · simp [literalRuntime, literalCompilationResult,
        valid, invalidLiteralResult, advanceOutputIndexResult,
        pushGateAtResult, emitGateResult, emitSourceResult,
        emittedNandState, outputIndex]
    · simp [literalRuntime, literalCompilationResult,
        valid, invalidLiteralResult, advanceOutputIndexResult,
        pushGateAtResult,
        emitGateResult_targetTokens,
        encodeGateListTokens_append_local,
        emittedNandState, outputIndex, targetTokens,
        EmissionSource.evaluate, emitSourceResult,
        encodeGateListTokens,
        List.append_assoc]
    · simp [literalRuntime, literalCompilationResult,
        valid, invalidLiteralResult, advanceOutputIndexResult,
        pushGateAtResult, emitGateResult, emitSourceResult,
        emittedNandState, encodedCoordinate, checks, outputIndex,
        List.reverse_cons, List.map_append,
        List.append_assoc]

private theorem runCompilationPlan_append_local
    (first second : List CNFToNAND.CompilationAction)
    (state : CNFToNAND.CompilationState) :
    CNFToNAND.runCompilationPlan (first ++ second) state =
      match CNFToNAND.runCompilationPlan first state with
      | none => none
      | some middle =>
          CNFToNAND.runCompilationPlan second middle := by
  induction first generalizing state with
  | nil =>
      rfl
  | cons action rest inductionHypothesis =>
      simp only [List.cons_append, CNFToNAND.runCompilationPlan]
      cases stepped : action.step state with
      | none =>
          rfl
      | some next =>
          exact inductionHypothesis next

private theorem run_negate_exact
    (state : CNFToNAND.CompilationState)
    (source : LockedNAND.RawSource)
    (rest : List LockedNAND.RawSource)
    (stack : state.stack = source :: rest) :
    CNFToNAND.runCompilationPlan [.negate] state =
      some (emittedNandState state source source rest) := by
  simp [CNFToNAND.runCompilationPlan,
    CNFToNAND.CompilationAction.step, stack]
  rfl

private theorem run_literalCompilation
    (width : Nat) (literal : CNFLiteral)
    (state : CNFToNAND.CompilationState) :
    CNFToNAND.runCompilationPlan
        (CNFToNAND.literalPlan width literal ++ [.negate])
        state =
      some (literalCompilationResult width literal state) := by
  by_cases valid : literal.variableIndex < width
  · cases polarity : literal.positive
    · let first :=
        emittedNandState state
          (.input literal.variableIndex)
          (.input literal.variableIndex) state.stack
      calc
        CNFToNAND.runCompilationPlan
            (CNFToNAND.literalPlan width literal ++ [.negate])
            state =
          CNFToNAND.runCompilationPlan
            ([.push (.input literal.variableIndex), .negate] ++
              [.negate]) state := by
                simp [CNFToNAND.literalPlan, valid, polarity]
        _ =
          CNFToNAND.runCompilationPlan [.negate] first := by
            rw [runCompilationPlan_append_local,
              run_push_negate_probe]
            rfl
        _ =
          some
            (emittedNandState first
              (.gate state.gates.length)
              (.gate state.gates.length) state.stack) := by
            exact run_negate_exact first
              (.gate state.gates.length) state.stack rfl
        _ = some
            (literalCompilationResult width literal state) := by
              simp [literalCompilationResult, valid, polarity,
                first]
    · simpa [CNFToNAND.literalPlan, valid, polarity,
        literalCompilationResult, emittedNandState] using
        run_push_negate_probe
          (.input literal.variableIndex) state
  · simpa [CNFToNAND.literalPlan, valid,
      literalCompilationResult, emittedNandState] using
      run_push_negate_probe (.constant false) state

private def literalCompilationPlan
    (width : Nat) : List CNFLiteral →
      List CNFToNAND.CompilationAction
  | [] => []
  | literal :: rest =>
      CNFToNAND.literalPlan width literal ++ [.negate] ++
        literalCompilationPlan width rest

private def literalListCompilationResult
    (width : Nat) : List CNFLiteral →
      CNFToNAND.CompilationState →
        CNFToNAND.CompilationState
  | [], state => state
  | literal :: rest, state =>
      literalListCompilationResult width rest
        (literalCompilationResult width literal state)

private theorem literalCompilationResult_gates_length
    (width : Nat) (literal : CNFLiteral)
    (state : CNFToNAND.CompilationState) :
    (literalCompilationResult width literal state).gates.length =
      state.gates.length + literalEmitGateCount width literal := by
  by_cases valid : literal.variableIndex < width
  · cases polarity : literal.positive <;>
      simp [literalCompilationResult, literalEmitGateCount,
        emittedNandState, valid, polarity]
  · simp [literalCompilationResult, literalEmitGateCount,
      emittedNandState, valid]

private theorem literalListCompilationResult_gates_length
    (width : Nat) (literals : List CNFLiteral)
    (state : CNFToNAND.CompilationState) :
    (literalListCompilationResult width literals state).gates.length =
      state.gates.length + literalListGateCount width literals := by
  induction literals generalizing state with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      rw [literalListCompilationResult,
        inductionHypothesis,
        literalCompilationResult_gates_length]
      simp [literalListGateCount]
      omega

private theorem run_literalCompilationPlan
    (width : Nat) (literals : List CNFLiteral)
    (state : CNFToNAND.CompilationState) :
    CNFToNAND.runCompilationPlan
        (literalCompilationPlan width literals) state =
      some
        (literalListCompilationResult width literals state) := by
  induction literals generalizing state with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      rw [literalCompilationPlan,
        runCompilationPlan_append_local,
        run_literalCompilation]
      simp only
      rw [inductionHypothesis]
      rfl

private theorem literalListRuntime_matchesCompilation
    (formula : CNFFormula) (width : Nat)
    (literals : List CNFLiteral)
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime)
    (correspondence :
      RuntimeMatchesCompilation formula state runtime) :
    RuntimeMatchesCompilation formula
      (literalListCompilationResult width literals state)
      (literalListRuntime width literals runtime) := by
  induction literals generalizing state runtime with
  | nil =>
      simpa [literalListCompilationResult, literalListRuntime] using
        correspondence
  | cons literal rest inductionHypothesis =>
      let nextState :=
        literalCompilationResult width literal state
      let nextRuntime :=
        literalRuntime width literal runtime
      have nextCorrespondence :
          RuntimeMatchesCompilation formula nextState nextRuntime := by
        exact literalRuntime_matchesCompilation
          formula width literal state runtime correspondence
      change
        RuntimeMatchesCompilation formula
          (literalListCompilationResult width rest nextState)
          (literalListRuntime width rest nextRuntime)
      exact inductionHypothesis nextState nextRuntime
        nextCorrespondence

private def storedFalseState
    (state : CNFToNAND.CompilationState) :
    CNFToNAND.CompilationState :=
  { state with stack := .constant false :: state.stack }

private theorem pushTotalGateResult_matchesCompilation
    (formula : CNFFormula)
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime)
    (correspondence :
      RuntimeMatchesCompilation formula state runtime) :
    RuntimeMatchesCompilation formula
      (storedFalseState state) (pushTotalGateResult runtime) := by
  rcases correspondence with
    ⟨scratch, currentGate, outputIndex, targetTokens, checks⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [pushTotalGateResult]
  · simpa [pushTotalGateResult] using currentGate
  · simpa [pushTotalGateResult, storedFalseState] using outputIndex
  · simpa [pushTotalGateResult, storedFalseState] using targetTokens
  · simp [pushTotalGateResult, storedFalseState,
      encodedCoordinate, checks, currentGate,
      List.reverse_cons, List.map_append,
      List.append_assoc]

private def literalStackCoordinates
    (width : Nat) :
    List CNFLiteral → Nat → List Nat
  | [], _ => []
  | literal :: rest, start =>
      let growth := literalEmitGateCount width literal
      literalStackCoordinates width rest (start + growth) ++
        [start + growth - 1]

private theorem literalCompilationResult_stack
    (width : Nat) (literal : CNFLiteral)
    (state : CNFToNAND.CompilationState) :
    (literalCompilationResult width literal state).stack =
      .gate
          (state.gates.length +
            literalEmitGateCount width literal - 1) ::
        state.stack := by
  by_cases valid : literal.variableIndex < width
  · cases polarity : literal.positive <;>
      simp [literalCompilationResult, literalEmitGateCount,
        emittedNandState, valid, polarity] <;>
      omega
  · simp [literalCompilationResult, literalEmitGateCount,
      emittedNandState, valid]

private theorem literalListCompilationResult_stack
    (width : Nat) (literals : List CNFLiteral)
    (state : CNFToNAND.CompilationState) :
    (literalListCompilationResult width literals state).stack =
      (literalStackCoordinates width literals state.gates.length).map
          LockedNAND.RawSource.gate ++
        state.stack := by
  induction literals generalizing state with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      rw [literalListCompilationResult,
        inductionHypothesis,
        literalCompilationResult_stack,
        literalCompilationResult_gates_length]
      simp [literalStackCoordinates, List.map_append,
        List.append_assoc]

private theorem literalCompilationResult_gates_of_eq
    (width : Nat) (literal : CNFLiteral)
    (left right : CNFToNAND.CompilationState)
    (gates : left.gates = right.gates) :
    (literalCompilationResult width literal left).gates =
      (literalCompilationResult width literal right).gates := by
  by_cases valid : literal.variableIndex < width
  · cases polarity : literal.positive <;>
      simp [literalCompilationResult, emittedNandState,
        valid, polarity, gates]
  · simp [literalCompilationResult, emittedNandState,
      valid, gates]

private theorem literalListCompilationResult_gates_of_eq
    (width : Nat) (literals : List CNFLiteral)
    (left right : CNFToNAND.CompilationState)
    (gates : left.gates = right.gates) :
    (literalListCompilationResult width literals left).gates =
      (literalListCompilationResult width literals right).gates := by
  induction literals generalizing left right with
  | nil =>
      exact gates
  | cons literal rest inductionHypothesis =>
      apply inductionHypothesis
      exact literalCompilationResult_gates_of_eq
        width literal left right gates

private theorem run_nand_exact
    (state : CNFToNAND.CompilationState)
    (left right : LockedNAND.RawSource)
    (rest : List LockedNAND.RawSource)
    (stack : state.stack = right :: left :: rest) :
    CNFToNAND.runCompilationPlan [.nand] state =
      some (emittedNandState state left right rest) := by
  simp [CNFToNAND.runCompilationPlan,
    CNFToNAND.CompilationAction.step, stack]
  rfl

private def seedClauseCompilationResult
    (literalCoordinate : Nat)
    (rest : List LockedNAND.RawSource)
    (state : CNFToNAND.CompilationState) :
    CNFToNAND.CompilationState :=
  let falseGate :=
    emittedNandState state
      (.constant false) (.constant false)
      (.gate literalCoordinate :: rest)
  emittedNandState falseGate
    (.gate literalCoordinate)
    (.gate state.gates.length) rest

private theorem run_seedClauseCompilation
    (literalCoordinate : Nat)
    (rest : List LockedNAND.RawSource)
    (state : CNFToNAND.CompilationState)
    (stack :
      state.stack = .gate literalCoordinate :: rest) :
    CNFToNAND.runCompilationPlan
        [.push (.constant false), .negate, .nand] state =
      some
        (seedClauseCompilationResult
          literalCoordinate rest state) := by
  let falseGate :=
    emittedNandState state
      (.constant false) (.constant false)
      (.gate literalCoordinate :: rest)
  calc
    CNFToNAND.runCompilationPlan
        [.push (.constant false), .negate, .nand] state =
      CNFToNAND.runCompilationPlan [.nand] falseGate := by
        change
          CNFToNAND.runCompilationPlan
              ([.push (.constant false), .negate] ++ [.nand])
              state =
            CNFToNAND.runCompilationPlan [.nand] falseGate
        rw [runCompilationPlan_append_local,
          run_push_negate_probe]
        simp [falseGate, emittedNandState, stack]
    _ =
      some
        (emittedNandState falseGate
          (.gate literalCoordinate)
          (.gate state.gates.length) rest) := by
            exact run_nand_exact falseGate
              (.gate literalCoordinate)
              (.gate state.gates.length) rest
              (by simp [falseGate, emittedNandState, stack])
    _ =
      some
        (seedClauseCompilationResult
          literalCoordinate rest state) := by
            rfl

private def extendClauseCompilationResult
    (accumulatorCoordinate nextCoordinate : Nat)
    (rest : List LockedNAND.RawSource)
    (state : CNFToNAND.CompilationState) :
    CNFToNAND.CompilationState :=
  let negated :=
    emittedNandState state
      (.gate accumulatorCoordinate)
      (.gate accumulatorCoordinate)
      (.gate nextCoordinate :: rest)
  emittedNandState negated
    (.gate nextCoordinate)
    (.gate state.gates.length) rest

private theorem run_extendClauseCompilation
    (accumulatorCoordinate nextCoordinate : Nat)
    (rest : List LockedNAND.RawSource)
    (state : CNFToNAND.CompilationState)
    (stack :
      state.stack =
        .gate accumulatorCoordinate ::
          .gate nextCoordinate :: rest) :
    CNFToNAND.runCompilationPlan [.negate, .nand] state =
      some
        (extendClauseCompilationResult
          accumulatorCoordinate nextCoordinate rest state) := by
  let negated :=
    emittedNandState state
      (.gate accumulatorCoordinate)
      (.gate accumulatorCoordinate)
      (.gate nextCoordinate :: rest)
  calc
    CNFToNAND.runCompilationPlan [.negate, .nand] state =
      CNFToNAND.runCompilationPlan [.nand] negated := by
        change
          CNFToNAND.runCompilationPlan
              ([.negate] ++ [.nand]) state =
            CNFToNAND.runCompilationPlan [.nand] negated
        rw [runCompilationPlan_append_local,
          run_negate_exact state
            (.gate accumulatorCoordinate)
            (.gate nextCoordinate :: rest) stack]
    _ =
      some
        (emittedNandState negated
          (.gate nextCoordinate)
          (.gate state.gates.length) rest) := by
            exact run_nand_exact negated
              (.gate nextCoordinate)
              (.gate state.gates.length) rest
              (by simp [negated, emittedNandState, stack])
    _ =
      some
        (extendClauseCompilationResult
          accumulatorCoordinate nextCoordinate rest state) := by
            rfl

private structure ClauseAccumulatorMatches
    (formula : CNFFormula)
    (pending : List Nat)
    (prior : List LockedNAND.RawSource)
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime) : Prop where
  currentGate :
    runtime.registers.currentGate =
      CNFToNANDWorkspace.compilerGateCount formula
  outputIndex :
    runtime.registers.outputIndex + 1 = state.gates.length
  targetTokens :
    runtime.targetTokens =
      headerTokens formula ++
        encodeGateListTokens state.gates
  stack :
    state.stack =
      .gate runtime.registers.outputIndex ::
        pending.map LockedNAND.RawSource.gate ++ prior
  checks :
    runtime.checks =
      CNFToNANDWorkspace.formulaStackMarker formula ::
        (pending.map LockedNAND.RawSource.gate ++
            [LockedNAND.RawSource.constant false] ++ prior).reverse.map
          (encodedCoordinate
            (CNFToNANDWorkspace.compilerGateCount formula))

private def clauseFoldTailPlan :
    List Nat → List CNFToNAND.CompilationAction
  | [] => []
  | _ :: rest =>
      [.negate, .nand] ++ clauseFoldTailPlan rest

private def clauseFoldSource
    (pending : List Nat) (runtime : Runtime) :
    LockedNAND.RawSource :=
  match pending with
  | [] => .constant false
  | _ :: _ =>
      .gate (clauseFoldCoordinate pending runtime)

private theorem clauseAccumulator_fold_matchesCompilation
    (formula : CNFFormula)
    (pending : List Nat)
    (prior : List LockedNAND.RawSource)
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime)
    (correspondence :
      ClauseAccumulatorMatches formula pending prior state runtime) :
    ∃ finalState,
      CNFToNAND.runCompilationPlan
          (clauseFoldTailPlan pending) state =
        some finalState ∧
      RuntimeMatchesCompilation formula finalState
        (clauseFoldLoopRuntime pending.length runtime) ∧
      finalState.stack =
        .gate
            (runtime.registers.outputIndex +
              2 * pending.length) ::
          prior := by
  induction pending generalizing state runtime with
  | nil =>
      rcases correspondence with
        ⟨currentGate, outputIndex, targetTokens, stack, checks⟩
      let checkPrior :=
        CNFToNANDWorkspace.formulaStackMarker formula ::
          prior.reverse.map
            (encodedCoordinate
              (CNFToNANDWorkspace.compilerGateCount formula))
      have checks' :
          runtime.checks =
            checkPrior ++
              [CNFToNANDWorkspace.compilerGateCount formula] := by
        simpa [checkPrior, encodedCoordinate,
          List.reverse_append, List.map_append,
          List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime checkPrior
          (CNFToNANDWorkspace.compilerGateCount formula)
      have newest :
          popNewestResult runtime = popped := by
        exact popNewestResult_of_checks runtime checkPrior
          (CNFToNANDWorkspace.compilerGateCount formula) checks'
      let finalRuntime := finishNonemptyClauseResult popped
      refine ⟨state, rfl, ?_, ?_⟩
      change
        RuntimeMatchesCompilation formula state
          (clauseFoldLoopRuntime 0 runtime)
      rw [clauseFoldLoopRuntime, newest]
      change RuntimeMatchesCompilation formula state finalRuntime
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [finalRuntime, finishNonemptyClauseResult,
          advanceOutputIndexResult, pushGateAtResult, popped,
          popCoordinateResult]
      · simpa [finalRuntime, finishNonemptyClauseResult,
          advanceOutputIndexResult, pushGateAtResult, popped,
          popCoordinateResult] using currentGate
      · simp [finalRuntime, finishNonemptyClauseResult,
          advanceOutputIndexResult, pushGateAtResult, popped,
          popCoordinateResult]
        omega
      · simpa [finalRuntime, finishNonemptyClauseResult,
          advanceOutputIndexResult, pushGateAtResult, popped,
          popCoordinateResult] using targetTokens
      · simp [finalRuntime, finishNonemptyClauseResult,
          advanceOutputIndexResult, pushGateAtResult, popped,
          popCoordinateResult, checkPrior, stack,
          encodedCoordinate, List.reverse_cons,
          List.map_append, List.append_assoc]
      · simpa using stack
  | cons coordinate rest inductionHypothesis =>
      rcases correspondence with
        ⟨currentGate, outputIndex, targetTokens, stack, checks⟩
      let remainingSources :=
        rest.map LockedNAND.RawSource.gate ++ prior
      let checkPrior :=
        CNFToNANDWorkspace.formulaStackMarker formula ::
          (rest.map LockedNAND.RawSource.gate ++
              [LockedNAND.RawSource.constant false] ++ prior).reverse.map
            (encodedCoordinate
              (CNFToNANDWorkspace.compilerGateCount formula))
      have checks' :
          runtime.checks = checkPrior ++ [coordinate] := by
        simpa [checkPrior, encodedCoordinate,
          List.reverse_append, List.map_append,
          List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime checkPrior coordinate
      have newest :
          popNewestResult runtime = popped := by
        exact popNewestResult_of_checks runtime checkPrior
          coordinate checks'
      let nextState :=
        extendClauseCompilationResult
          runtime.registers.outputIndex coordinate
          remainingSources state
      let nextRuntime := extendClauseResult popped
      have nextCorrespondence :
          ClauseAccumulatorMatches formula rest prior
            nextState nextRuntime := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simpa [nextRuntime, extendClauseResult,
            advanceOutputIndexResult, popped,
            popCoordinateResult, emitGateResult,
            emitSourceResult] using currentGate
        · simp [nextRuntime, nextState,
            extendClauseCompilationResult, emittedNandState,
            extendClauseResult, advanceOutputIndexResult,
            popped, popCoordinateResult, emitGateResult,
            emitSourceResult] at outputIndex ⊢
          omega
        · simp [nextRuntime, nextState,
            extendClauseCompilationResult, emittedNandState,
            extendClauseResult, advanceOutputIndexResult,
            popped, popCoordinateResult,
            emitGateResult_targetTokens,
            encodeGateListTokens_append_local,
            EmissionSource.evaluate, EmissionSource.finalScratch,
            emitGateResult, emitSourceResult,
            encodeGateListTokens, encodeGateTokens,
            targetTokens, outputIndex, List.append_assoc]
        · simp [nextState, nextRuntime,
            extendClauseCompilationResult, emittedNandState,
            extendClauseResult, advanceOutputIndexResult,
            popped, popCoordinateResult, emitGateResult,
            emitSourceResult, remainingSources, stack] at outputIndex ⊢
          omega
        · change nextRuntime.checks = checkPrior
          simp [nextRuntime, extendClauseResult,
            advanceOutputIndexResult, popped,
            popCoordinateResult, emitGateResult,
            emitSourceResult, checkPrior]
      rcases
          inductionHypothesis nextState nextRuntime
            nextCorrespondence with
        ⟨finalState, restRun, finalCorrespondence,
          finalStack⟩
      refine ⟨finalState, ?_, ?_, ?_⟩
      · rw [clauseFoldTailPlan,
          runCompilationPlan_append_local,
          run_extendClauseCompilation
            runtime.registers.outputIndex coordinate
            remainingSources state
            (by
              simpa [remainingSources, List.append_assoc] using stack)]
        exact restRun
      · simpa [clauseFoldLoopRuntime, newest,
          popped, nextRuntime] using finalCorrespondence
      · have coordinateEq :
            nextRuntime.registers.outputIndex +
                2 * rest.length =
              runtime.registers.outputIndex +
                2 * (coordinate :: rest).length := by
          simp [nextRuntime, extendClauseResult,
            advanceOutputIndexResult, popped,
            popCoordinateResult, emitGateResult,
            emitSourceResult]
          omega
        rw [← coordinateEq]
        exact finalStack

private def clauseFinishPlan
    (pending : List Nat) :
    List CNFToNAND.CompilationAction :=
  [.push (.constant false)] ++ clauseFoldTailPlan pending

private theorem clause_fold_matchesCompilation
    (formula : CNFFormula)
    (pending : List Nat)
    (prior : List LockedNAND.RawSource)
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime)
    (currentGate :
      runtime.registers.currentGate =
        CNFToNANDWorkspace.compilerGateCount formula)
    (outputIndex :
      runtime.registers.outputIndex = state.gates.length)
    (targetTokens :
      runtime.targetTokens =
        headerTokens formula ++
          encodeGateListTokens state.gates)
    (stack :
      state.stack =
        pending.map LockedNAND.RawSource.gate ++ prior)
    (checks :
      runtime.checks =
        CNFToNANDWorkspace.formulaStackMarker formula ::
          (pending.map LockedNAND.RawSource.gate ++
              [LockedNAND.RawSource.constant false] ++ prior).reverse.map
            (encodedCoordinate
              (CNFToNANDWorkspace.compilerGateCount formula))) :
    ∃ finalState,
      CNFToNAND.runCompilationPlan
          (clauseFinishPlan pending) state =
        some finalState ∧
      RuntimeMatchesCompilation formula finalState
        (clauseFoldRuntime pending.length runtime) ∧
      finalState.stack =
        clauseFoldSource pending runtime :: prior := by
  cases pending with
  | nil =>
      let checkPrior :=
        CNFToNANDWorkspace.formulaStackMarker formula ::
          prior.reverse.map
            (encodedCoordinate
              (CNFToNANDWorkspace.compilerGateCount formula))
      have checks' :
          runtime.checks =
            checkPrior ++
              [CNFToNANDWorkspace.compilerGateCount formula] := by
        simpa [checkPrior, encodedCoordinate,
          List.reverse_append, List.map_append,
          List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime checkPrior
          (CNFToNANDWorkspace.compilerGateCount formula)
      have newest :
          popNewestResult runtime = popped := by
        exact popNewestResult_of_checks runtime checkPrior
          (CNFToNANDWorkspace.compilerGateCount formula) checks'
      let finalState := storedFalseState state
      let finalRuntime := pushTotalGateResult popped
      refine ⟨finalState, ?_, ?_, ?_⟩
      · simp [clauseFinishPlan, clauseFoldTailPlan,
          CNFToNAND.runCompilationPlan,
          CNFToNAND.CompilationAction.step,
          finalState, storedFalseState]
      · change
          RuntimeMatchesCompilation formula finalState
            (clauseFoldRuntime 0 runtime)
        rw [clauseFoldRuntime, newest]
        change RuntimeMatchesCompilation formula finalState finalRuntime
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp [finalRuntime, pushTotalGateResult, popped,
            popCoordinateResult]
        · simpa [finalRuntime, pushTotalGateResult, popped,
            popCoordinateResult] using currentGate
        · simpa [finalRuntime, finalState, pushTotalGateResult,
            popped, popCoordinateResult, storedFalseState] using
            outputIndex
        · simpa [finalRuntime, finalState, pushTotalGateResult,
            popped, popCoordinateResult, storedFalseState] using
            targetTokens
        · simp [finalRuntime, finalState, pushTotalGateResult,
            popped, popCoordinateResult, storedFalseState,
            checkPrior, stack, currentGate, encodedCoordinate,
            List.reverse_cons, List.map_append,
            List.append_assoc]
      · simp [finalState, storedFalseState, clauseFoldSource]
        simpa using stack
  | cons coordinate rest =>
      let remainingSources :=
        rest.map LockedNAND.RawSource.gate ++ prior
      let checkPrior :=
        CNFToNANDWorkspace.formulaStackMarker formula ::
          (rest.map LockedNAND.RawSource.gate ++
              [LockedNAND.RawSource.constant false] ++ prior).reverse.map
            (encodedCoordinate
              (CNFToNANDWorkspace.compilerGateCount formula))
      have checks' :
          runtime.checks = checkPrior ++ [coordinate] := by
        simpa [checkPrior, encodedCoordinate,
          List.reverse_append, List.map_append,
          List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime checkPrior coordinate
      have newest :
          popNewestResult runtime = popped := by
        exact popNewestResult_of_checks runtime checkPrior
          coordinate checks'
      let nextState :=
        seedClauseCompilationResult coordinate
          remainingSources state
      let nextRuntime := seedClauseResult popped
      have nextCorrespondence :
          ClauseAccumulatorMatches formula rest prior
            nextState nextRuntime := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simpa [nextRuntime, seedClauseResult,
            advanceOutputIndexResult, popped,
            popCoordinateResult, emitGateResult,
            emitSourceResult] using currentGate
        · simp [nextRuntime, nextState,
            seedClauseCompilationResult, emittedNandState,
            seedClauseResult, advanceOutputIndexResult,
            popped, popCoordinateResult, emitGateResult,
            emitSourceResult] at outputIndex ⊢
          omega
        · simp [nextRuntime, nextState,
            seedClauseCompilationResult, emittedNandState,
            seedClauseResult, advanceOutputIndexResult,
            popped, popCoordinateResult,
            emitGateResult_targetTokens,
            encodeGateListTokens_append_local,
            EmissionSource.evaluate, EmissionSource.finalScratch,
            emitGateResult, emitSourceResult,
            encodeGateListTokens, encodeGateTokens,
            targetTokens, outputIndex, List.append_assoc]
        · simp [nextState, nextRuntime,
            seedClauseCompilationResult, emittedNandState,
            seedClauseResult, advanceOutputIndexResult,
            popped, popCoordinateResult, emitGateResult,
            emitSourceResult, remainingSources, stack] at outputIndex ⊢
          omega
        · change nextRuntime.checks = checkPrior
          simp [nextRuntime, seedClauseResult,
            advanceOutputIndexResult, popped,
            popCoordinateResult, emitGateResult,
            emitSourceResult, checkPrior]
      rcases
          clauseAccumulator_fold_matchesCompilation formula
            rest prior nextState nextRuntime nextCorrespondence with
        ⟨finalState, restRun, finalCorrespondence,
          finalStack⟩
      refine ⟨finalState, ?_, ?_, ?_⟩
      · change
          CNFToNAND.runCompilationPlan
              ([.push (.constant false), .negate, .nand] ++
                clauseFoldTailPlan rest) state =
            some finalState
        rw [runCompilationPlan_append_local,
          run_seedClauseCompilation coordinate
            remainingSources state
            (by
              simpa [remainingSources, List.append_assoc] using stack)]
        exact restRun
      · simpa [clauseFoldRuntime, newest, popped,
          nextRuntime] using finalCorrespondence
      · have coordinateEq :
            nextRuntime.registers.outputIndex +
                2 * rest.length =
              clauseFoldCoordinate (coordinate :: rest)
                runtime := by
          simp [nextRuntime, seedClauseResult,
            advanceOutputIndexResult, popped,
            popCoordinateResult, emitGateResult,
            emitSourceResult, clauseFoldCoordinate]
          omega
        simp only [clauseFoldSource]
        rw [← coordinateEq]
        exact finalStack

private theorem literalStackCoordinates_length
    (width : Nat) (literals : List CNFLiteral)
    (start : Nat) :
    (literalStackCoordinates width literals start).length =
      literals.length := by
  induction literals generalizing start with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      simp [literalStackCoordinates, inductionHypothesis]

private theorem clauseFoldTailPlan_append
    (first second : List Nat) :
    clauseFoldTailPlan (first ++ second) =
      clauseFoldTailPlan first ++ clauseFoldTailPlan second := by
  induction first with
  | nil =>
      rfl
  | cons coordinate rest inductionHypothesis =>
      simp [clauseFoldTailPlan, inductionHypothesis,
        List.append_assoc]

private theorem clausePlan_eq_literal_and_finish
    (width : Nat) (clause : List CNFLiteral)
    (start : Nat) :
    CNFToNAND.clausePlan width clause =
      literalCompilationPlan width clause ++
        clauseFinishPlan
          (literalStackCoordinates width clause start) := by
  induction clause generalizing start with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      rw [CNFToNAND.clausePlan_cons,
        inductionHypothesis
          (start + literalEmitGateCount width literal)]
      simp [literalCompilationPlan, literalStackCoordinates,
        clauseFinishPlan, clauseFoldTailPlan_append,
        clauseFoldTailPlan, List.append_assoc]

private theorem literalListCoordinates_eq_reverse_literalStack
    (width : Nat) (literals : List CNFLiteral)
    (start : Nat) (runtime : Runtime)
    (outputIndex :
      runtime.registers.outputIndex = start) :
    literalListCoordinates width literals runtime =
      (literalStackCoordinates width literals start).reverse := by
  induction literals generalizing start runtime with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      have nextOutput :
          (literalRuntime width literal runtime).registers.outputIndex =
            start + literalEmitGateCount width literal := by
        rw [literalRuntime_outputIndex, outputIndex]
      rw [literalListCoordinates, literalStackCoordinates,
        List.reverse_append,
        inductionHypothesis
          (start + literalEmitGateCount width literal)
          (literalRuntime width literal runtime) nextOutput]
      by_cases valid : literal.variableIndex < width <;>
        cases polarity : literal.positive <;>
          simp [literalCoordinate, literalEmitGateCount,
            valid, polarity, outputIndex] <;>
          omega

private theorem clauseRuntime_matchesCompilation
    (formula : CNFFormula)
    (width : Nat) (clause : List CNFLiteral)
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime)
    (correspondence :
      RuntimeMatchesCompilation formula state runtime)
    (outputBound :
      runtime.registers.outputIndex +
          clauseGateCount width clause ≤
        CNFToNANDWorkspace.compilerGateCount formula) :
    ∃ finalState,
      CNFToNAND.runCompilationPlan
          (CNFToNAND.clausePlan width clause) state =
        some finalState ∧
      RuntimeMatchesCompilation formula finalState
        (clauseRuntime width clause runtime) ∧
      finalState.stack =
        decodedCoordinate
            (CNFToNANDWorkspace.compilerGateCount formula)
            (clauseCoordinate width clause runtime) ::
          state.stack := by
  let stored := storedFalseState state
  let initialized := pushTotalGateResult runtime
  have initializedCorrespondence :
      RuntimeMatchesCompilation formula stored initialized := by
    exact pushTotalGateResult_matchesCompilation
      formula state runtime correspondence
  let actualLiterals :=
    literalListCompilationResult width clause state
  let storedLiterals :=
    literalListCompilationResult width clause stored
  let scanned :=
    literalListRuntime width clause initialized
  have scannedCorrespondence :
      RuntimeMatchesCompilation formula storedLiterals scanned := by
    exact literalListRuntime_matchesCompilation
      formula width clause stored initialized
        initializedCorrespondence
  let pending :=
    literalStackCoordinates width clause state.gates.length
  have gatesEq :
      storedLiterals.gates = actualLiterals.gates := by
    apply literalListCompilationResult_gates_of_eq
    rfl
  have actualStack :
      actualLiterals.stack =
        pending.map LockedNAND.RawSource.gate ++ state.stack := by
    simpa [actualLiterals, pending] using
      literalListCompilationResult_stack width clause state
  have storedStack :
      storedLiterals.stack =
        pending.map LockedNAND.RawSource.gate ++
          [LockedNAND.RawSource.constant false] ++ state.stack := by
    have stackEq :=
      literalListCompilationResult_stack width clause stored
    have pendingEq :
        literalStackCoordinates width clause stored.gates.length =
          pending := by
      rfl
    simpa [storedLiterals, stored, storedFalseState,
      pendingEq, List.append_assoc] using stackEq
  rcases scannedCorrespondence with
    ⟨scannedScratch, scannedCurrent, scannedOutput,
      scannedTarget, scannedChecks⟩
  have scannedOutput' :
      scanned.registers.outputIndex =
        actualLiterals.gates.length := by
    rw [← gatesEq]
    exact scannedOutput
  have scannedTarget' :
      scanned.targetTokens =
        headerTokens formula ++
          encodeGateListTokens actualLiterals.gates := by
    rw [← gatesEq]
    exact scannedTarget
  have scannedChecks' :
      scanned.checks =
        CNFToNANDWorkspace.formulaStackMarker formula ::
          (pending.map LockedNAND.RawSource.gate ++
              [LockedNAND.RawSource.constant false] ++
              state.stack).reverse.map
            (encodedCoordinate
              (CNFToNANDWorkspace.compilerGateCount formula)) := by
    rw [scannedChecks, storedStack]
  have initializedOutput :
      initialized.registers.outputIndex =
        state.gates.length := by
    simpa [initialized, pushTotalGateResult] using
      correspondence.outputIndex
  have physicalCoordinates :
      literalListCoordinates width clause initialized =
        pending.reverse := by
    simpa [pending] using
      literalListCoordinates_eq_reverse_literalStack
        width clause state.gates.length initialized
        initializedOutput
  have clauseCoordinateEq :
      clauseCoordinate width clause runtime =
        clauseFoldCoordinate pending scanned := by
    simp [clauseCoordinate, initialized, scanned,
      physicalCoordinates]
  rcases
      clause_fold_matchesCompilation formula pending state.stack
        actualLiterals scanned scannedCurrent scannedOutput'
        scannedTarget' actualStack scannedChecks' with
    ⟨finalState, finishRun, finalCorrespondence,
      finalStack⟩
  refine ⟨finalState, ?_, ?_, ?_⟩
  · rw [clausePlan_eq_literal_and_finish
        width clause state.gates.length,
      runCompilationPlan_append_local,
      run_literalCompilationPlan]
    exact finishRun
  · have pendingLength :
        pending.length = clause.length := by
      simpa [pending] using
        literalStackCoordinates_length
          width clause state.gates.length
    rw [pendingLength] at finalCorrespondence
    simpa [clauseRuntime, scanned, initialized] using
      finalCorrespondence
  · rw [finalStack]
    congr 1
    cases clause with
    | nil =>
        simp [pending, literalStackCoordinates,
          clauseFoldSource, decodedCoordinate,
          clauseCoordinate_eq_currentGate_of_empty,
          correspondence.currentGate]
    | cons literal rest =>
        have pendingNonempty : pending ≠ [] := by
          intro empty
          have pendingLength :
              pending.length = (literal :: rest).length := by
            simpa [pending] using
              literalStackCoordinates_length
                width (literal :: rest) state.gates.length
          rw [empty] at pendingLength
          simp only [List.length_nil, List.length_cons] at pendingLength
          omega
        have boundAtCurrentGate :
            runtime.registers.outputIndex +
                clauseGateCount width (literal :: rest) ≤
              runtime.registers.currentGate := by
          rw [correspondence.currentGate]
          exact outputBound
        have coordinateLess :
            clauseCoordinate width (literal :: rest) runtime <
              CNFToNANDWorkspace.compilerGateCount formula := by
          rw [← correspondence.currentGate]
          exact
            clauseCoordinate_lt_currentGate_of_nonempty
              width literal rest runtime boundAtCurrentGate
        cases pendingEq : pending with
        | nil =>
            exact False.elim (pendingNonempty pendingEq)
        | cons coordinate tail =>
            simp only [clauseFoldSource]
            rw [pendingEq] at clauseCoordinateEq
            rw [← clauseCoordinateEq]
            simp [decodedCoordinate,
              Nat.ne_of_lt coordinateLess]

private def clauseCompilationPlan
    (width : Nat) :
    List (List CNFLiteral) →
      List CNFToNAND.CompilationAction
  | [] => []
  | clause :: rest =>
      CNFToNAND.clausePlan width clause ++
        clauseCompilationPlan width rest

private theorem clauseListRuntime_matchesCompilation
    (formula : CNFFormula)
    (width : Nat) (clauses : List (List CNFLiteral))
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime)
    (correspondence :
      RuntimeMatchesCompilation formula state runtime)
    (outputBound :
      runtime.registers.outputIndex +
          clauseListGateCount width clauses ≤
        CNFToNANDWorkspace.compilerGateCount formula) :
    ∃ finalState,
      CNFToNAND.runCompilationPlan
          (clauseCompilationPlan width clauses) state =
        some finalState ∧
      RuntimeMatchesCompilation formula finalState
        (clauseListRuntime width clauses runtime) ∧
      finalState.stack =
        (clauseListCoordinates width clauses runtime).reverse.map
            (decodedCoordinate
              (CNFToNANDWorkspace.compilerGateCount formula)) ++
          state.stack := by
  induction clauses generalizing state runtime with
  | nil =>
      exact ⟨state, rfl, correspondence, rfl⟩
  | cons clause rest inductionHypothesis =>
      have clauseBound :
          runtime.registers.outputIndex +
              clauseGateCount width clause ≤
            CNFToNANDWorkspace.compilerGateCount formula := by
        simp only [clauseListGateCount] at outputBound
        omega
      rcases
          clauseRuntime_matchesCompilation formula width clause
            state runtime correspondence clauseBound with
        ⟨nextState, clauseRun, nextCorrespondence,
          nextStack⟩
      have restBound :
          (clauseRuntime width clause runtime).registers.outputIndex +
              clauseListGateCount width rest ≤
            CNFToNANDWorkspace.compilerGateCount formula := by
        rw [clauseRuntime_outputIndex]
        simp only [clauseListGateCount] at outputBound
        omega
      rcases
          inductionHypothesis nextState
            (clauseRuntime width clause runtime)
            nextCorrespondence restBound with
        ⟨finalState, restRun, finalCorrespondence,
          finalStack⟩
      refine ⟨finalState, ?_, ?_, ?_⟩
      · rw [clauseCompilationPlan,
          runCompilationPlan_append_local, clauseRun]
        exact restRun
      · simpa [clauseListRuntime] using finalCorrespondence
      · rw [finalStack, nextStack]
        simp [clauseListCoordinates, List.reverse_cons,
          List.map_append, List.append_assoc]

private def seedFormulaCompilationResult
    (source : LockedNAND.RawSource)
    (rest : List LockedNAND.RawSource)
    (state : CNFToNAND.CompilationState) :
    CNFToNAND.CompilationState :=
  let combined :=
    emittedNandState state source
      (.constant true) rest
  emittedNandState combined
    (.gate state.gates.length)
    (.gate state.gates.length) rest

private theorem run_seedFormulaCompilation
    (source : LockedNAND.RawSource)
    (rest : List LockedNAND.RawSource)
    (state : CNFToNAND.CompilationState)
    (stack : state.stack = source :: rest) :
    CNFToNAND.runCompilationPlan
        [.push (.constant true), .nand, .negate] state =
      some
        (seedFormulaCompilationResult source rest state) := by
  let pushed : CNFToNAND.CompilationState :=
    { state with
      stack := .constant true :: source :: rest }
  let combined :=
    emittedNandState pushed source (.constant true) rest
  have pushRun :
      CNFToNAND.runCompilationPlan
          [.push (.constant true)] state =
        some pushed := by
    simp [CNFToNAND.runCompilationPlan,
      CNFToNAND.CompilationAction.step, pushed, stack]
  have nandRun :
      CNFToNAND.runCompilationPlan [.nand] pushed =
        some combined := by
    simpa [pushed, combined] using
      run_nand_exact pushed source (.constant true) rest rfl
  change
    CNFToNAND.runCompilationPlan
        ([.push (.constant true)] ++ [.nand] ++ [.negate])
        state =
      some
        (seedFormulaCompilationResult source rest state)
  rw [List.append_assoc,
    runCompilationPlan_append_local, pushRun]
  simp only
  rw [runCompilationPlan_append_local, nandRun]
  simpa [pushed, combined, seedFormulaCompilationResult,
    emittedNandState] using
    run_negate_exact combined
      (.gate pushed.gates.length) rest
      (by simp [combined, emittedNandState])

private def extendFormulaCompilationResult
    (accumulator source : LockedNAND.RawSource)
    (rest : List LockedNAND.RawSource)
    (state : CNFToNAND.CompilationState) :
    CNFToNAND.CompilationState :=
  let combined :=
    emittedNandState state source accumulator rest
  emittedNandState combined
    (.gate state.gates.length)
    (.gate state.gates.length) rest

private theorem run_extendFormulaCompilation
    (accumulator source : LockedNAND.RawSource)
    (rest : List LockedNAND.RawSource)
    (state : CNFToNAND.CompilationState)
    (stack :
      state.stack = accumulator :: source :: rest) :
    CNFToNAND.runCompilationPlan [.nand, .negate] state =
      some
        (extendFormulaCompilationResult
          accumulator source rest state) := by
  let combined :=
    emittedNandState state source accumulator rest
  have nandRun :
      CNFToNAND.runCompilationPlan [.nand] state =
        some combined := by
    simpa [combined] using
      run_nand_exact state source accumulator rest stack
  change
    CNFToNAND.runCompilationPlan
        ([.nand] ++ [.negate]) state =
      some
        (extendFormulaCompilationResult
          accumulator source rest state)
  rw [runCompilationPlan_append_local, nandRun]
  simpa [combined, extendFormulaCompilationResult] using
    run_negate_exact combined
      (.gate state.gates.length) rest
      (by simp [combined, emittedNandState])

private def formulaFoldTailPlan :
    List Nat → List CNFToNAND.CompilationAction
  | [] => []
  | _ :: rest =>
      [.nand, .negate] ++ formulaFoldTailPlan rest

private structure FormulaAccumulatorMatches
    (formula : CNFFormula)
    (pending : List Nat)
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime) : Prop where
  currentGate :
    runtime.registers.currentGate =
      CNFToNANDWorkspace.compilerGateCount formula
  outputIndex :
    runtime.registers.outputIndex + 1 =
      state.gates.length
  targetTokens :
    runtime.targetTokens =
      headerTokens formula ++
        encodeGateListTokens state.gates
  stack :
    state.stack =
      .gate runtime.registers.outputIndex ::
        pending.map
          (decodedCoordinate
            (CNFToNANDWorkspace.compilerGateCount formula))
  checks :
    runtime.checks =
      CNFToNANDWorkspace.formulaStackMarker formula ::
        pending.reverse

private structure FormulaResultMatches
    (formula : CNFFormula)
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime) : Prop where
  outputIndex :
    runtime.registers.outputIndex + 1 =
      state.gates.length
  targetTokens :
    runtime.targetTokens =
      headerTokens formula ++
        encodeGateListTokens state.gates
  stack :
    state.stack =
      [.gate runtime.registers.outputIndex]
  checks :
    runtime.checks = []

private theorem runtimeClauseSource_evaluate_popCoordinate
    (runtime : Runtime) (prior : List Nat)
    (coordinate total : Nat)
    (currentGate :
      runtime.registers.currentGate = total) :
    (runtimeClauseSource
        (popCoordinateResult runtime prior coordinate)).emission.evaluate
          (popCoordinateResult runtime prior coordinate) =
      decodedCoordinate total coordinate := by
  by_cases equal : coordinate = total
  · simp [runtimeClauseSource, popCoordinateResult,
      currentGate, equal, ClauseSource.emission,
      EmissionSource.evaluate, decodedCoordinate]
  · simp [runtimeClauseSource, popCoordinateResult,
      currentGate, equal, ClauseSource.emission,
      EmissionSource.evaluate, decodedCoordinate]

private theorem formulaAccumulator_fold_matchesCompilation
    (formula : CNFFormula)
    (pending : List Nat)
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime)
    (correspondence :
      FormulaAccumulatorMatches formula pending state runtime) :
    ∃ finalState,
      CNFToNAND.runCompilationPlan
          (formulaFoldTailPlan pending) state =
        some finalState ∧
      FormulaResultMatches formula finalState
        (formulaFoldLoopRuntime pending.length runtime) := by
  induction pending generalizing state runtime with
  | nil =>
      rcases correspondence with
        ⟨currentGate, outputIndex, targetTokens, stack, checks⟩
      let marker :=
        CNFToNANDWorkspace.formulaStackMarker formula
      have checks' : runtime.checks = [] ++ [marker] := by
        simpa [marker] using checks
      let popped :=
        popCoordinateResult runtime [] marker
      have newest : popNewestResult runtime = popped := by
        exact popNewestResult_of_checks runtime [] marker checks'
      refine ⟨state, rfl, ?_⟩
      change
        FormulaResultMatches formula state
          (formulaFoldLoopRuntime 0 runtime)
      rw [formulaFoldLoopRuntime, newest]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [popped, popCoordinateResult] using outputIndex
      · simpa [popped, popCoordinateResult] using targetTokens
      · simpa [popped, popCoordinateResult] using stack
      · simp [popped, popCoordinateResult]
  | cons coordinate rest inductionHypothesis =>
      rcases correspondence with
        ⟨currentGate, outputIndex, targetTokens, stack, checks⟩
      let remainingSources :=
        rest.map
          (decodedCoordinate
            (CNFToNANDWorkspace.compilerGateCount formula))
      let checkPrior :=
        CNFToNANDWorkspace.formulaStackMarker formula ::
          rest.reverse
      have checks' :
          runtime.checks = checkPrior ++ [coordinate] := by
        simpa [checkPrior, List.reverse_cons,
          List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime checkPrior coordinate
      have newest : popNewestResult runtime = popped := by
        exact popNewestResult_of_checks
          runtime checkPrior coordinate checks'
      let nextState :=
        extendFormulaCompilationResult
          (.gate runtime.registers.outputIndex)
          (decodedCoordinate
            (CNFToNANDWorkspace.compilerGateCount formula)
            coordinate)
          remainingSources state
      let nextRuntime :=
        extendFormulaResult
          (runtimeClauseSource popped) popped
      have sourceEvaluate :
          (runtimeClauseSource popped).emission.evaluate popped =
            decodedCoordinate
              (CNFToNANDWorkspace.compilerGateCount formula)
              coordinate := by
        exact runtimeClauseSource_evaluate_popCoordinate
          runtime checkPrior coordinate
            (CNFToNANDWorkspace.compilerGateCount formula)
            currentGate
      have nextCorrespondence :
          FormulaAccumulatorMatches formula rest
            nextState nextRuntime := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simpa [nextRuntime, extendFormulaResult,
            advanceOutputIndexResult, popped,
            popCoordinateResult, emitGateResult,
            emitSourceResult] using currentGate
        · simp [nextRuntime, nextState,
            extendFormulaCompilationResult, emittedNandState,
            extendFormulaResult, advanceOutputIndexResult,
            popped, popCoordinateResult, emitGateResult,
            emitSourceResult] at outputIndex ⊢
          omega
        · by_cases equal :
              coordinate =
                CNFToNANDWorkspace.compilerGateCount formula
          · simp [nextRuntime, nextState,
              extendFormulaCompilationResult, emittedNandState,
              extendFormulaResult, advanceOutputIndexResult,
              runtimeClauseSource, popped, popCoordinateResult,
              currentGate, equal, decodedCoordinate,
              ClauseSource.emission,
              emitGateResult_targetTokens,
              encodeGateListTokens_append_local,
              EmissionSource.evaluate_after_emit,
              EmissionSource.evaluate,
              EmissionSource.finalScratch,
              emitGateResult, emitSourceResult,
              encodeGateListTokens, encodeGateTokens,
              targetTokens, outputIndex,
              List.append_assoc]
          · simp [nextRuntime, nextState,
              extendFormulaCompilationResult, emittedNandState,
              extendFormulaResult, advanceOutputIndexResult,
              runtimeClauseSource, popped, popCoordinateResult,
              currentGate, equal, decodedCoordinate,
              ClauseSource.emission,
              emitGateResult_targetTokens,
              encodeGateListTokens_append_local,
              EmissionSource.evaluate_after_emit,
              EmissionSource.evaluate,
              EmissionSource.finalScratch,
              emitGateResult, emitSourceResult,
              encodeGateListTokens, encodeGateTokens,
              targetTokens, outputIndex,
              List.append_assoc]
        · simp [nextState, nextRuntime,
            extendFormulaCompilationResult, emittedNandState,
            extendFormulaResult, advanceOutputIndexResult,
            popped, popCoordinateResult, emitGateResult,
            emitSourceResult, remainingSources, stack] at outputIndex ⊢
          omega
        · change nextRuntime.checks = checkPrior
          rw [extendFormulaResult_checks]
          simp [popped, popCoordinateResult]
      rcases
          inductionHypothesis nextState nextRuntime
            nextCorrespondence with
        ⟨finalState, restRun, finalCorrespondence⟩
      refine ⟨finalState, ?_, ?_⟩
      · rw [formulaFoldTailPlan,
          runCompilationPlan_append_local,
          run_extendFormulaCompilation
            (.gate runtime.registers.outputIndex)
            (decodedCoordinate
              (CNFToNANDWorkspace.compilerGateCount formula)
              coordinate)
            remainingSources state
            (by
              simpa [remainingSources,
                List.append_assoc] using stack)]
        exact restRun
      · simpa [formulaFoldLoopRuntime, newest,
          popped, nextRuntime] using finalCorrespondence

private def formulaFoldPlan :
    List Nat → List CNFToNAND.CompilationAction
  | [] => [.push (.constant true)]
  | _ :: rest =>
      [.push (.constant true), .nand, .negate] ++
        formulaFoldTailPlan rest

private theorem formula_fold_nonempty_matchesCompilation
    (formula : CNFFormula)
    (coordinate : Nat) (rest : List Nat)
    (state : CNFToNAND.CompilationState)
    (runtime : Runtime)
    (currentGate :
      runtime.registers.currentGate =
        CNFToNANDWorkspace.compilerGateCount formula)
    (outputIndex :
      runtime.registers.outputIndex = state.gates.length)
    (targetTokens :
      runtime.targetTokens =
        headerTokens formula ++
          encodeGateListTokens state.gates)
    (stack :
      state.stack =
        (coordinate :: rest).map
          (decodedCoordinate
            (CNFToNANDWorkspace.compilerGateCount formula)))
    (checks :
      runtime.checks =
        CNFToNANDWorkspace.formulaStackMarker formula ::
          (coordinate :: rest).reverse) :
    ∃ finalState,
      CNFToNAND.runCompilationPlan
          (formulaFoldPlan (coordinate :: rest)) state =
        some finalState ∧
      FormulaResultMatches formula finalState
        (formulaFoldRuntime (coordinate :: rest).length runtime) := by
  let checkPrior :=
    CNFToNANDWorkspace.formulaStackMarker formula ::
      rest.reverse
  have checks' :
      runtime.checks = checkPrior ++ [coordinate] := by
    simpa [checkPrior, List.reverse_cons,
      List.append_assoc] using checks
  let popped :=
    popCoordinateResult runtime checkPrior coordinate
  have newest : popNewestResult runtime = popped := by
    exact popNewestResult_of_checks
      runtime checkPrior coordinate checks'
  let remainingSources :=
    rest.map
      (decodedCoordinate
        (CNFToNANDWorkspace.compilerGateCount formula))
  let nextState :=
    seedFormulaCompilationResult
      (decodedCoordinate
        (CNFToNANDWorkspace.compilerGateCount formula)
        coordinate)
      remainingSources state
  let nextRuntime :=
    seedFormulaResult (runtimeClauseSource popped) popped
  have nextCorrespondence :
      FormulaAccumulatorMatches formula rest
        nextState nextRuntime := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [nextRuntime, seedFormulaResult,
        advanceOutputIndexResult, popped,
        popCoordinateResult, emitGateResult,
        emitSourceResult] using currentGate
    · simp [nextRuntime, nextState,
        seedFormulaCompilationResult, emittedNandState,
        seedFormulaResult, advanceOutputIndexResult,
        popped, popCoordinateResult, emitGateResult,
        emitSourceResult] at outputIndex ⊢
      omega
    · by_cases equal :
          coordinate =
            CNFToNANDWorkspace.compilerGateCount formula
      · simp [nextRuntime, nextState,
          seedFormulaCompilationResult, emittedNandState,
          seedFormulaResult, advanceOutputIndexResult,
          runtimeClauseSource, popped, popCoordinateResult,
          currentGate, equal, decodedCoordinate,
          ClauseSource.emission,
          encodeGateListTokens_append_local,
          EmissionSource.evaluate,
          EmissionSource.finalScratch,
          emitGateResult, emitSourceResult,
          encodeGateListTokens, encodeGateTokens,
          targetTokens, outputIndex,
          List.append_assoc]
      · simp [nextRuntime, nextState,
          seedFormulaCompilationResult, emittedNandState,
          seedFormulaResult, advanceOutputIndexResult,
          runtimeClauseSource, popped, popCoordinateResult,
          currentGate, equal, decodedCoordinate,
          ClauseSource.emission,
          encodeGateListTokens_append_local,
          EmissionSource.evaluate,
          EmissionSource.finalScratch,
          emitGateResult, emitSourceResult,
          encodeGateListTokens, encodeGateTokens,
          targetTokens, outputIndex,
          List.append_assoc]
    · simp [nextState, nextRuntime,
        seedFormulaCompilationResult, emittedNandState,
        seedFormulaResult, advanceOutputIndexResult,
        popped, popCoordinateResult, emitGateResult,
        emitSourceResult, remainingSources, stack] at outputIndex ⊢
      omega
    · change nextRuntime.checks = checkPrior
      rw [seedFormulaResult_checks]
      simp [popped, popCoordinateResult]
  rcases
      formulaAccumulator_fold_matchesCompilation formula rest
        nextState nextRuntime nextCorrespondence with
    ⟨finalState, restRun, finalCorrespondence⟩
  refine ⟨finalState, ?_, ?_⟩
  · rw [formulaFoldPlan,
      runCompilationPlan_append_local,
      run_seedFormulaCompilation
        (decodedCoordinate
          (CNFToNANDWorkspace.compilerGateCount formula)
          coordinate)
        remainingSources state
        (by simpa [remainingSources] using stack)]
    exact restRun
  · simpa [formulaFoldRuntime, newest,
      popped, nextRuntime] using finalCorrespondence

private theorem formulaFoldTailPlan_commutes_pair
    (pending : List Nat) :
    [.nand, .negate] ++ formulaFoldTailPlan pending =
      formulaFoldTailPlan pending ++ [.nand, .negate] := by
  induction pending with
  | nil =>
      rfl
  | cons coordinate rest inductionHypothesis =>
      let pair : List CNFToNAND.CompilationAction :=
        [.nand, .negate]
      change
        pair ++ (pair ++ formulaFoldTailPlan rest) =
          (pair ++ formulaFoldTailPlan rest) ++ pair
      calc
        pair ++ (pair ++ formulaFoldTailPlan rest) =
            pair ++
              (formulaFoldTailPlan rest ++ pair) := by
                rw [inductionHypothesis]
        _ =
            (pair ++ formulaFoldTailPlan rest) ++ pair := by
              rw [List.append_assoc]

private theorem formulaFoldPlan_eq_push_tail
    (pending : List Nat) :
    formulaFoldPlan pending =
      [.push (.constant true)] ++
        formulaFoldTailPlan pending := by
  cases pending <;>
    simp [formulaFoldPlan, formulaFoldTailPlan,
      List.append_assoc]

private theorem formulaFoldPlan_cons
    (coordinate : Nat) (rest : List Nat) :
    formulaFoldPlan (coordinate :: rest) =
      formulaFoldPlan rest ++ [.nand, .negate] := by
  rw [formulaFoldPlan_eq_push_tail,
    formulaFoldPlan_eq_push_tail, formulaFoldTailPlan]
  rw [formulaFoldTailPlan_commutes_pair rest]
  simp [List.append_assoc]

private theorem clausesPlan_eq_clauseCompilation_formulaFold
    (width : Nat) (clauses : List (List CNFLiteral))
    (coordinates : List Nat)
    (lengthEq : coordinates.length = clauses.length) :
    CNFToNAND.clausesPlan width clauses =
      clauseCompilationPlan width clauses ++
        formulaFoldPlan coordinates := by
  induction clauses generalizing coordinates with
  | nil =>
      have empty : coordinates = [] := by
        simpa using List.eq_nil_of_length_eq_zero lengthEq
      simp [empty, clauseCompilationPlan, formulaFoldPlan]
  | cons clause rest inductionHypothesis =>
      cases coordinates with
      | nil =>
          simp only [List.length_nil, List.length_cons] at lengthEq
          omega
      | cons coordinate tail =>
          have tailLength : tail.length = rest.length := by
            simpa using Nat.succ.inj lengthEq
          rw [CNFToNAND.clausesPlan_cons,
            inductionHypothesis tail tailLength,
            clauseCompilationPlan,
            formulaFoldPlan_cons]
          simp [List.append_assoc]

private theorem emitInitialRuntime_matchesCompilation
    (formula : CNFFormula) :
    RuntimeMatchesCompilation formula
      { gates := [], stack := [] }
      (emitInitialRuntime formula) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · exact
      CNFToNANDWorkspace.workspaceRegisters_currentGate formula
  · exact
      CNFToNANDWorkspace.workspaceRegisters_outputIndex formula
  · change
      headerTokens formula =
        headerTokens formula ++ encodeGateListTokens []
    rw [show encodeGateListTokens [] = [] by rfl]
    simp
  · simp [emitInitialRuntime]

private theorem completedRuntime_targetTokens_eq_of_nonempty
    (formula : CNFFormula)
    (nonempty : formula.clauses ≠ []) :
    (completedRuntime formula).targetTokens =
      LockedNAND.encodeCircuitTokens
        (CNFToNAND.compileFormula formula) := by
  let initialState : CNFToNAND.CompilationState :=
    { gates := [], stack := [] }
  let initial := emitInitialRuntime formula
  let clausesRuntime :=
    clauseListRuntime formula.variableCount formula.clauses initial
  let coordinates :=
    clauseListCoordinates formula.variableCount formula.clauses initial
  let pending := coordinates.reverse
  have initialCorrespondence :
      RuntimeMatchesCompilation formula initialState initial := by
    simpa [initialState, initial] using
      emitInitialRuntime_matchesCompilation formula
  have clauseBound :
      initial.registers.outputIndex +
          clauseListGateCount formula.variableCount
            formula.clauses ≤
        CNFToNANDWorkspace.compilerGateCount formula := by
    simp [initial, emitInitialRuntime,
      CNFToNANDWorkspace.workspaceRegisters_outputIndex]
    rw [compilerGateCount_eq_structural]
    omega
  rcases
      clauseListRuntime_matchesCompilation formula
        formula.variableCount formula.clauses
        initialState initial initialCorrespondence clauseBound with
    ⟨clauseState, clauseRun, clauseCorrespondence,
      clauseStack⟩
  have pendingLength :
      pending.length = formula.clauses.length := by
    simp [pending, coordinates,
      clauseListCoordinates_length]
  have pendingNonempty : pending ≠ [] := by
    intro empty
    rw [empty] at pendingLength
    simp at pendingLength
    exact nonempty (List.eq_nil_of_length_eq_zero pendingLength.symm)
  have clauseStack' :
      clauseState.stack =
        pending.map
          (decodedCoordinate
            (CNFToNANDWorkspace.compilerGateCount formula)) := by
    simpa [pending, initialState] using clauseStack
  have clauseChecks :
      clausesRuntime.checks =
        CNFToNANDWorkspace.formulaStackMarker formula ::
          pending.reverse := by
    rw [clauseListRuntime_checks]
    simp [clausesRuntime, pending, coordinates, initial,
      emitInitialRuntime]
  cases pendingEq : pending with
  | nil =>
      exact False.elim (pendingNonempty pendingEq)
  | cons coordinate rest =>
      have foldStack :
          clauseState.stack =
            (coordinate :: rest).map
              (decodedCoordinate
                (CNFToNANDWorkspace.compilerGateCount formula)) := by
        rw [← pendingEq]
        exact clauseStack'
      have foldChecks :
          clausesRuntime.checks =
            CNFToNANDWorkspace.formulaStackMarker formula ::
              (coordinate :: rest).reverse := by
        rw [← pendingEq]
        exact clauseChecks
      rcases
          formula_fold_nonempty_matchesCompilation formula
            coordinate rest clauseState clausesRuntime
            clauseCorrespondence.currentGate
            clauseCorrespondence.outputIndex
            clauseCorrespondence.targetTokens
            foldStack foldChecks with
        ⟨finalState, foldRun, finalCorrespondence⟩
      have planEq :
          CNFToNAND.formulaPlan formula =
            clauseCompilationPlan formula.variableCount
                formula.clauses ++
              formulaFoldPlan (coordinate :: rest) := by
        unfold CNFToNAND.formulaPlan
        apply clausesPlan_eq_clauseCompilation_formulaFold
        simpa [← pendingEq] using pendingLength
      have fullRun :
          CNFToNAND.runCompilationPlan
              (CNFToNAND.formulaPlan formula) initialState =
            some finalState := by
        rw [planEq, runCompilationPlan_append_local,
          clauseRun]
        exact foldRun
      have finalized :
          CNFToNAND.finalizeCompilation formula.variableCount
              finalState =
            some (CNFToNAND.compileFormula formula) := by
        have exactRun :=
          CNFToNAND.executeFormulaPlan_exact formula
        unfold CNFToNAND.executeFormulaPlan at exactRun
        simpa [initialState, fullRun] using exactRun
      have foldLength :
          (coordinate :: rest).length =
            formula.clauses.length := by
        simpa [← pendingEq] using pendingLength
      rw [foldLength] at finalCorrespondence
      let folded :=
        formulaFoldRuntime formula.clauses.length clausesRuntime
      have foldedCorrespondence :
          FormulaResultMatches formula finalState folded := by
        simpa [folded] using finalCorrespondence
      have circuitEq :
          { inputCount := formula.variableCount
            gates := finalState.gates
            output := LockedNAND.RawSource.gate
              folded.registers.outputIndex } =
            CNFToNAND.compileFormula formula := by
        have normalized := finalized
        simp [CNFToNAND.finalizeCompilation,
          foldedCorrespondence.stack] at normalized
        exact normalized
      have formulaRuntimeEq :
          formulaRuntime formula = folded := by
        rfl
      have gateCountEq :
          CNFToNANDWorkspace.compilerGateCount formula =
            finalState.gates.length := by
        unfold CNFToNANDWorkspace.compilerGateCount
        rw [← circuitEq]
      rw [completedRuntime, formulaRuntimeEq]
      change
        folded.targetTokens ++ [.programEnd] ++
              encodeSourceTokens
                (.gate folded.registers.outputIndex) ++
              [.outputsEnd, .instanceEnd] =
          LockedNAND.encodeCircuitTokens
            (CNFToNAND.compileFormula formula)
      rw [foldedCorrespondence.targetTokens, ← circuitEq]
      simp [circuitSuffixResult,
        LockedNAND.encodeCircuitTokens, headerTokens,
        PNP.Concrete.CNFToNANDControllerCountTrace.headerTokens,
        gateCountEq, List.append_assoc]

private theorem completedRuntime_targetTokens_eq
    (formula : CNFFormula) :
    (completedRuntime formula).targetTokens =
      LockedNAND.encodeCircuitTokens
        (CNFToNAND.compileFormula formula) := by
  rcases formula with ⟨inputs, clauses⟩
  cases clauses with
  | nil =>
      let formula : CNFFormula :=
        { variableCount := inputs, clauses := [] }
      let expected : LockedNAND.RawCircuit :=
        { inputCount := inputs
          gates :=
            [{ left := .constant false
               right := .constant false }]
          output := .gate 0 }
      have exactRun :=
        CNFToNAND.executeFormulaPlan_exact formula
      have emptyRun :=
        CNFToNAND.executeFormulaPlan_empty_formula inputs
      have circuitEq :
          CNFToNAND.compileFormula formula = expected := by
        exact Option.some.inj (exactRun.symm.trans emptyRun)
      change
        (completedRuntime formula).targetTokens =
          LockedNAND.encodeCircuitTokens
            (CNFToNAND.compileFormula formula)
      rw [circuitEq]
      simp [completedRuntime, formulaRuntime,
        clauseListRuntime, formulaFoldRuntime,
        popNewestResult, emptyFormulaResult,
        emitInitialRuntime, emitGateResult, emitSourceResult,
        EmissionSource.evaluate, EmissionSource.finalScratch,
        circuitSuffixResult,
        LockedNAND.encodeCircuitTokens,
        PNP.Concrete.CNFToNANDControllerCountTrace.headerTokens,
        CNFToNANDWorkspace.compilerGateCount,
        CNFToNANDWorkspace.workspaceRegisters_outputIndex,
        circuitEq, expected, formula, encodeGateListTokens,
        encodeGateTokens, encodeSourceTokens,
        List.append_assoc]
  | cons clause rest =>
      exact
        completedRuntime_targetTokens_eq_of_nonempty
          { variableCount := inputs
            clauses := clause :: rest } (by simp)

/-- The emitting traversal completes from the count-pass handoff within its
explicit envelope and leaves exactly the pure compiler's strict-v0 output
word on the reached accepting tape. -/
theorem completion_path
    (formula : CNFFormula) (initialTape : WorkTape)
    (represents :
      TapeRepresents (passHeaderRef .emit).startState
        (CNFToNANDWorkspace.capacity formula)
        (emitInitialRuntime formula).scratch
        (emitInitialRuntime formula).registers
        (emitInitialRuntime formula).checks
        (canonicalSource formula)
        (emitInitialRuntime formula).targetTokens
        initialTape) :
    ∃ steps finalTape,
      steps ≤ completionEnvelope formula ∧
      AcceptPath graph (.node (passHeaderRef .emit)) .accept
        steps initialTape finalTape ∧
      (encodeWorkTape finalTape).outputBits =
        CNFToNAND.emitFormulaPlan formula := by
  rcases completion_physical_path formula initialTape represents with
    ⟨steps, finalTape, bound, path, finalRepresents⟩
  have equivalent :
      WorkTape.BlankEquivalent finalTape
        (TargetEmitterCursorFinalizer.finalTape
          (versionMarkedSource formula)
          (SourceParser.packedTokenCells
            (completedRuntime formula).targetTokens)
          (TargetEmitterRuntimePrimitives.fixedWorkspace
            (CNFToNANDWorkspace.capacity formula)
            (completedRuntime formula).scratch
            (completedRuntime formula).registers
            (completedRuntime formula).checks)
          []) := by
    simpa [FinalTapeRepresents] using finalRepresents
  have observed :=
    encodeWorkTape_outputBits_eq_of_blankEquivalent equivalent
  have canonical :=
    TargetEmitterControllerOutputTrace.canonicalFinal_output_eq
      (versionMarkedSource formula)
      (completedRuntime formula).targetTokens
      (CNFToNANDWorkspace.capacity formula)
      (completedRuntime formula).scratch
      (completedRuntime formula).registers
      (completedRuntime formula).checks
  have outputTarget :
      (encodeWorkTape finalTape).outputBits =
        encodeTokens (completedRuntime formula).targetTokens :=
    observed.trans canonical
  refine ⟨steps, finalTape, bound, path, ?_⟩
  calc
    (encodeWorkTape finalTape).outputBits =
        encodeTokens (completedRuntime formula).targetTokens :=
      outputTarget
    _ =
        encodeTokens
          (LockedNAND.encodeCircuitTokens
            (CNFToNAND.compileFormula formula)) := by
      rw [completedRuntime_targetTokens_eq]
    _ = CNFToNAND.emitFormulaPlan formula := by
      rw [CNFToNAND.emitFormulaPlan_exact]
      rfl

/-! ## Closed polynomial charge for the completion pass -/

private abbrev completionSize (formula : CNFFormula) : Nat :=
  shiftedSize (encodeCNF formula).length

private abbrev completionPhase (formula : CNFFormula) : Nat :=
  phaseUnit (encodeCNF formula).length

private theorem cnfToNANDOutputSizePolynomial_le_dataMajorant
    (bitLength : Nat) :
    CNFToNAND.cnfToNANDOutputSizePolynomial.eval bitLength ≤
      dataMajorant bitLength := by
  let size := shiftedSize bitLength
  have positive : 1 ≤ size := one_le_shiftedSize bitLength
  have linearLift : 19 * size ≤ 19 * size * size := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (19 * size) positive
  have coarse :
      4 * ((5 * size) * (15 * size) + 19 * size) ≤
        376 * size * size := by
    calc
      4 * ((5 * size) * (15 * size) + 19 * size) ≤
          4 * ((5 * size) * (15 * size) + 19 * size * size) :=
        Nat.mul_le_mul_left 4
          (Nat.add_le_add_left linearLift
            ((5 * size) * (15 * size)))
      _ = 376 * size * size := by
        rw [Nat.mul_add]
        have first :
            4 * ((5 * size) * (15 * size)) =
              300 * (size * size) := by
          ac_rfl
        have second :
            4 * (19 * size * size) =
              76 * (size * size) := by
          ac_rfl
        rw [first, second]
        calc
          300 * (size * size) + 76 * (size * size) =
              376 * (size * size) := by omega
          _ = 376 * size * size := by ac_rfl
  have coefficientBound : 376 ≤ 1000 * 1000000 := by decide
  have scaled :
      376 * size * size ≤
        (1000 * 1000000) * size * size :=
    Nat.mul_le_mul_right size
      (Nat.mul_le_mul_right size coefficientBound)
  have coefficient :
      376 * size * size ≤ dataMajorant bitLength := by
    unfold dataMajorant squareUnit
    change
      376 * size * size ≤
        1000 * (1000000 * size * size)
    simpa only [Nat.mul_assoc] using scaled
  rw [CNFToNAND.cnfToNANDOutputSizePolynomial_eval]
  change
    4 * ((5 * size) * (15 * size) + 19 * size) ≤
      dataMajorant bitLength
  exact Nat.le_trans coarse coefficient

private theorem completedRuntime_targetTokens_length_le_dataMajorant
    (formula : CNFFormula) :
    (completedRuntime formula).targetTokens.length ≤
      dataMajorant (encodeCNF formula).length := by
  have decoded := decodeEncodedCNF_canonical formula
  have outputBound :=
    CNFToNAND.compileEncodedCNFToNAND_size_le (encodeCNF formula)
  rw [CNFToNAND.compileEncodedCNFToNAND_of_decoded
      (encodeCNF formula) formula decoded] at outputBound
  have serialized :
      (LockedNAND.encodeCircuit
          (CNFToNAND.compileFormula formula)).length ≤
        CNFToNAND.cnfToNANDOutputSizePolynomial.eval
          (encodeCNF formula).length := by
    simpa only [BitString.size] using outputBound
  have tokenBits :
      (LockedNAND.encodeCircuitTokens
          (CNFToNAND.compileFormula formula)).length ≤
        (LockedNAND.encodeCircuit
          (CNFToNAND.compileFormula formula)).length := by
    simp only [LockedNAND.encodeCircuit,
      LockedNAND.encodeTokens_length]
    omega
  rw [completedRuntime_targetTokens_eq]
  exact Nat.le_trans tokenBits
    (Nat.le_trans serialized
      (cnfToNANDOutputSizePolynomial_le_dataMajorant
        (encodeCNF formula).length))

private theorem target_length_le_completed_of_append
    (formula : CNFFormula) (runtime : Runtime)
    (suffix : List Token)
    (targetEq :
      (completedRuntime formula).targetTokens =
        runtime.targetTokens ++ suffix) :
    runtime.targetTokens.length ≤
      dataMajorant (encodeCNF formula).length := by
  exact Nat.le_trans
    (show runtime.targetTokens.length ≤
        (completedRuntime formula).targetTokens.length by
      rw [targetEq, List.length_append]
      omega)
    (completedRuntime_targetTokens_length_le_dataMajorant formula)

private theorem checkCells_le_mul_of_forall_lt
    (capacity : Nat) (checks : List Nat)
    (bounded : ∀ value, value ∈ checks → value < capacity) :
    TargetEmitterRuntimeProgramBound.checkCells checks ≤
      checks.length * capacity := by
  induction checks with
  | nil =>
      simp [TargetEmitterRuntimeProgramBound.checkCells,
        TargetEmitterCheckStack.recordsWord]
  | cons value rest inductionHypothesis =>
      have valueBound : value + 1 ≤ capacity := by
        exact bounded value (List.Mem.head rest)
      have tailBounds :
          ∀ item, item ∈ rest → item < capacity := by
        intro item member
        exact bounded item (List.Mem.tail value member)
      have tailBound := inductionHypothesis tailBounds
      rw [show
        TargetEmitterRuntimeProgramBound.checkCells
            (value :: rest) =
          value + 1 +
            TargetEmitterRuntimeProgramBound.checkCells rest by
        simp [TargetEmitterRuntimeProgramBound.checkCells,
          TargetEmitterCheckStack.recordsWord,
          TargetEmitterCheckStack.recordWord_length]]
      simp only [List.length_cons]
      rw [Nat.succ_mul]
      omega

private theorem checkCells_le_dataMajorant
    (formula : CNFFormula) (checks : List Nat)
    (lengthBound :
      checks.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 2)
    (valuesBound :
      ∀ value, value ∈ checks →
        value < CNFToNANDWorkspace.capacity formula) :
    TargetEmitterRuntimeProgramBound.checkCells checks ≤
      dataMajorant (encodeCNF formula).length := by
  let size := completionSize formula
  have positive : 1 ≤ size := by
    exact one_le_shiftedSize (encodeCNF formula).length
  have tokenSize :
      (CNFToNANDWorkspace.formulaTokens formula).length ≤ size :=
    formulaTokens_le_shiftedSize formula
  have capacitySize :
      CNFToNANDWorkspace.capacity formula ≤ 1024 * size := by
    simpa [size] using capacity_le_1024_shiftedSize formula
  have lengthSize : checks.length ≤ 3 * size := by omega
  have occupied :=
    checkCells_le_mul_of_forall_lt
      (CNFToNANDWorkspace.capacity formula) checks valuesBound
  have product :
      checks.length * CNFToNANDWorkspace.capacity formula ≤
        (3 * size) * (1024 * size) :=
    Nat.mul_le_mul lengthSize capacitySize
  have coefficientBound : 3072 ≤ 1000 * 1000000 := by decide
  calc
    TargetEmitterRuntimeProgramBound.checkCells checks ≤
        checks.length * CNFToNANDWorkspace.capacity formula :=
      occupied
    _ ≤ (3 * size) * (1024 * size) := product
    _ = 3072 * (size * size) := by
      calc
        (3 * size) * (1024 * size) =
            (3 * 1024) * (size * size) := by ac_rfl
        _ = 3072 * (size * size) := by rfl
    _ ≤ (1000 * 1000000) * (size * size) :=
      Nat.mul_le_mul_right (size * size) coefficientBound
    _ = dataMajorant (encodeCNF formula).length := by
      unfold dataMajorant squareUnit
      dsimp [size]
      ac_rfl

/-! Append-only target witnesses. -/

private def TargetAppend (initial final : Runtime) : Prop :=
  ∃ suffix : List Token,
    final.targetTokens = initial.targetTokens ++ suffix

private theorem targetAppend_refl (runtime : Runtime) :
    TargetAppend runtime runtime := by
  exact ⟨[], by simp⟩

private theorem targetAppend_trans
    {first middle final : Runtime}
    (firstMiddle : TargetAppend first middle)
    (middleFinal : TargetAppend middle final) :
    TargetAppend first final := by
  rcases firstMiddle with ⟨firstSuffix, firstEq⟩
  rcases middleFinal with ⟨secondSuffix, secondEq⟩
  refine ⟨firstSuffix ++ secondSuffix, ?_⟩
  rw [secondEq, firstEq, List.append_assoc]

private theorem targetAppend_before_completed
    {before after : Runtime} (formula : CNFFormula)
    (beforeAfter : TargetAppend before after)
    (tail : List Token)
    (afterCompleted :
      (completedRuntime formula).targetTokens =
        after.targetTokens ++ tail) :
    ∃ suffix : List Token,
      (completedRuntime formula).targetTokens =
        before.targetTokens ++ suffix := by
  have afterFinal : TargetAppend after (completedRuntime formula) :=
    ⟨tail, afterCompleted⟩
  exact targetAppend_trans beforeAfter afterFinal

private theorem targetAppend_of_target_eq
    {initial final : Runtime}
    (targetEq : final.targetTokens = initial.targetTokens) :
    TargetAppend initial final := by
  refine ⟨[], ?_⟩
  simpa using targetEq

private theorem emitGateResult_target_append
    (runtime : Runtime) (left right : EmissionSource) :
    TargetAppend runtime (emitGateResult runtime left right) := by
  refine
    ⟨encodeGateTokens
        { left := left.evaluate runtime
          right :=
            right.evaluate (emitSourceResult runtime left) },
      ?_⟩
  exact emitGateResult_targetTokens runtime left right

private theorem advanceOutputIndexResult_target_append
    (runtime : Runtime) (count : Nat) :
    TargetAppend runtime
      (advanceOutputIndexResult runtime count) := by
  exact targetAppend_of_target_eq rfl

private theorem pushGateAtResult_target_append
    (runtime : Runtime) (bias : Nat) :
    TargetAppend runtime (pushGateAtResult runtime bias) := by
  exact targetAppend_of_target_eq rfl

private theorem pushTotalGateResult_target_append
    (runtime : Runtime) :
    TargetAppend runtime (pushTotalGateResult runtime) := by
  exact targetAppend_of_target_eq rfl

private theorem popCoordinateResult_target_append
    (runtime : Runtime) (prior : List Nat) (value : Nat) :
    TargetAppend runtime
      (popCoordinateResult runtime prior value) := by
  exact targetAppend_of_target_eq rfl

private theorem popNewestResult_target_append
    (runtime : Runtime) :
    TargetAppend runtime (popNewestResult runtime) := by
  exact targetAppend_of_target_eq rfl

private theorem positiveLiteralResult_target_append
    (runtime : Runtime) :
    TargetAppend runtime (positiveLiteralResult runtime) := by
  let emitted :=
    emitGateResult runtime .inputScratch .inputScratch
  let pushed := pushGateAtResult emitted 0
  have emission : TargetAppend runtime emitted := by
    exact emitGateResult_target_append runtime
      .inputScratch .inputScratch
  have push : TargetAppend emitted pushed := by
    exact pushGateAtResult_target_append emitted 0
  have advance :
      TargetAppend pushed (advanceOutputIndexResult pushed 1) := by
    exact advanceOutputIndexResult_target_append pushed 1
  simpa [positiveLiteralResult, emitted, pushed] using
    targetAppend_trans emission
      (targetAppend_trans push advance)

private theorem negativeLiteralResult_target_append
    (runtime : Runtime) :
    TargetAppend runtime (negativeLiteralResult runtime) := by
  let first :=
    emitGateResult runtime .inputScratch .inputScratch
  let second :=
    emitGateResult first (.gateAt 0) (.gateAt 0)
  let pushed := pushGateAtResult second 1
  have firstAppend : TargetAppend runtime first := by
    exact emitGateResult_target_append runtime
      .inputScratch .inputScratch
  have secondAppend : TargetAppend first second := by
    exact emitGateResult_target_append first
      (.gateAt 0) (.gateAt 0)
  have push : TargetAppend second pushed := by
    exact pushGateAtResult_target_append second 1
  have advance :
      TargetAppend pushed (advanceOutputIndexResult pushed 2) := by
    exact advanceOutputIndexResult_target_append pushed 2
  simpa [negativeLiteralResult, first, second, pushed] using
    targetAppend_trans firstAppend
      (targetAppend_trans secondAppend
        (targetAppend_trans push advance))

private theorem invalidLiteralResult_target_append
    (runtime : Runtime) :
    TargetAppend runtime (invalidLiteralResult runtime) := by
  let emitted :=
    emitGateResult runtime (.constant false) (.constant false)
  let pushed := pushGateAtResult emitted 0
  have emission : TargetAppend runtime emitted := by
    exact emitGateResult_target_append runtime
      (.constant false) (.constant false)
  have push : TargetAppend emitted pushed := by
    exact pushGateAtResult_target_append emitted 0
  have advance :
      TargetAppend pushed (advanceOutputIndexResult pushed 1) := by
    exact advanceOutputIndexResult_target_append pushed 1
  simpa [invalidLiteralResult, emitted, pushed] using
    targetAppend_trans emission
      (targetAppend_trans push advance)

private theorem literalRuntime_target_append
    (width : Nat) (literal : CNFLiteral)
    (runtime : Runtime) :
    TargetAppend runtime (literalRuntime width literal runtime) := by
  let scanned : Runtime :=
    { runtime with scratch := min literal.variableIndex width }
  have scan : TargetAppend runtime scanned := by
    apply targetAppend_of_target_eq
    rfl
  by_cases valid : literal.variableIndex < width
  · cases positive : literal.positive with
    | false =>
        simpa [literalRuntime, scanned, valid, positive] using
          targetAppend_trans scan
            (negativeLiteralResult_target_append scanned)
    | true =>
        simpa [literalRuntime, scanned, valid, positive] using
          targetAppend_trans scan
            (positiveLiteralResult_target_append scanned)
  · simpa [literalRuntime, scanned, valid] using
      targetAppend_trans scan
        (invalidLiteralResult_target_append scanned)

private theorem literalListRuntime_target_append
    (width : Nat) (literals : List CNFLiteral)
    (runtime : Runtime) :
    TargetAppend runtime
      (literalListRuntime width literals runtime) := by
  induction literals generalizing runtime with
  | nil =>
      simpa [literalListRuntime] using targetAppend_refl runtime
  | cons literal rest inductionHypothesis =>
      have first :=
        literalRuntime_target_append width literal runtime
      have tail :=
        inductionHypothesis
          (literalRuntime width literal runtime)
      simpa [literalListRuntime] using
        targetAppend_trans first tail

private theorem seedClauseResult_target_append
    (runtime : Runtime) :
    TargetAppend runtime (seedClauseResult runtime) := by
  let falseGate :=
    emitGateResult runtime (.constant false) (.constant false)
  let combined :=
    emitGateResult falseGate .gateScratch (.gateAt 0)
  have falseAppend : TargetAppend runtime falseGate := by
    exact emitGateResult_target_append runtime
      (.constant false) (.constant false)
  have combinedAppend : TargetAppend falseGate combined := by
    exact emitGateResult_target_append falseGate
      .gateScratch (.gateAt 0)
  have advance :
      TargetAppend combined
        (advanceOutputIndexResult combined 1) := by
    exact advanceOutputIndexResult_target_append combined 1
  simpa [seedClauseResult, falseGate, combined] using
    targetAppend_trans falseAppend
      (targetAppend_trans combinedAppend advance)

private theorem extendClauseResult_target_append
    (runtime : Runtime) :
    TargetAppend runtime (extendClauseResult runtime) := by
  let preserved : Runtime :=
    { runtime with
      checks := runtime.checks ++ [runtime.scratch] }
  let negated :=
    emitGateResult preserved (.gateAt 0) (.gateAt 0)
  let restored :=
    popCoordinateResult negated runtime.checks runtime.scratch
  let combined :=
    emitGateResult restored .gateScratch (.gateAt 1)
  have preserve : TargetAppend runtime preserved := by
    apply targetAppend_of_target_eq
    rfl
  have negate : TargetAppend preserved negated := by
    exact emitGateResult_target_append preserved
      (.gateAt 0) (.gateAt 0)
  have restore : TargetAppend negated restored := by
    exact popCoordinateResult_target_append negated
      runtime.checks runtime.scratch
  have combine : TargetAppend restored combined := by
    exact emitGateResult_target_append restored
      .gateScratch (.gateAt 1)
  have advance :
      TargetAppend combined
        (advanceOutputIndexResult combined 2) := by
    exact advanceOutputIndexResult_target_append combined 2
  simpa [extendClauseResult, preserved, negated, restored,
    combined] using
      targetAppend_trans preserve
        (targetAppend_trans negate
          (targetAppend_trans restore
            (targetAppend_trans combine advance)))

private theorem finishNonemptyClauseResult_target_append
    (runtime : Runtime) :
    TargetAppend runtime (finishNonemptyClauseResult runtime) := by
  let pushed := pushGateAtResult runtime 0
  have push : TargetAppend runtime pushed := by
    exact pushGateAtResult_target_append runtime 0
  have advance :
      TargetAppend pushed (advanceOutputIndexResult pushed 1) := by
    exact advanceOutputIndexResult_target_append pushed 1
  simpa [finishNonemptyClauseResult, pushed] using
    targetAppend_trans push advance

private theorem clauseFoldLoopRuntime_target_append
    (count : Nat) (runtime : Runtime) :
    TargetAppend runtime
      (clauseFoldLoopRuntime count runtime) := by
  induction count generalizing runtime with
  | zero =>
      have pop := popNewestResult_target_append runtime
      have finish :=
        finishNonemptyClauseResult_target_append
          (popNewestResult runtime)
      simpa [clauseFoldLoopRuntime] using
        targetAppend_trans pop finish
  | succ count inductionHypothesis =>
      have pop := popNewestResult_target_append runtime
      have extend :=
        extendClauseResult_target_append
          (popNewestResult runtime)
      have tail :=
        inductionHypothesis
          (extendClauseResult (popNewestResult runtime))
      simpa [clauseFoldLoopRuntime] using
        targetAppend_trans pop
          (targetAppend_trans extend tail)

private theorem clauseFoldRuntime_target_append
    (literalCount : Nat) (runtime : Runtime) :
    TargetAppend runtime
      (clauseFoldRuntime literalCount runtime) := by
  cases literalCount with
  | zero =>
      have pop := popNewestResult_target_append runtime
      have push :=
        pushTotalGateResult_target_append
          (popNewestResult runtime)
      simpa [clauseFoldRuntime] using
        targetAppend_trans pop push
  | succ count =>
      have pop := popNewestResult_target_append runtime
      have seed :=
        seedClauseResult_target_append
          (popNewestResult runtime)
      have fold :=
        clauseFoldLoopRuntime_target_append count
          (seedClauseResult (popNewestResult runtime))
      simpa [clauseFoldRuntime] using
        targetAppend_trans pop
          (targetAppend_trans seed fold)

private theorem clauseRuntime_target_append
    (width : Nat) (clause : List CNFLiteral)
    (runtime : Runtime) :
    TargetAppend runtime
      (clauseRuntime width clause runtime) := by
  let pushed := pushTotalGateResult runtime
  let literals := literalListRuntime width clause pushed
  have push : TargetAppend runtime pushed := by
    exact pushTotalGateResult_target_append runtime
  have literalAppend : TargetAppend pushed literals := by
    exact literalListRuntime_target_append width clause pushed
  have fold :
      TargetAppend literals
        (clauseFoldRuntime clause.length literals) := by
    exact clauseFoldRuntime_target_append clause.length literals
  simpa [clauseRuntime, pushed, literals] using
    targetAppend_trans push
      (targetAppend_trans literalAppend fold)

private theorem clauseListRuntime_target_append
    (width : Nat) (clauses : List (List CNFLiteral))
    (runtime : Runtime) :
    TargetAppend runtime
      (clauseListRuntime width clauses runtime) := by
  induction clauses generalizing runtime with
  | nil =>
      simpa [clauseListRuntime] using targetAppend_refl runtime
  | cons clause rest inductionHypothesis =>
      have clauseAppend :=
        clauseRuntime_target_append width clause runtime
      have restAppend :=
        inductionHypothesis
          (clauseRuntime width clause runtime)
      simpa [clauseListRuntime] using
        targetAppend_trans clauseAppend restAppend

private theorem seedFormulaResult_target_append
    (source : ClauseSource) (runtime : Runtime) :
    TargetAppend runtime (seedFormulaResult source runtime) := by
  let combined :=
    emitGateResult runtime source.emission (.constant true)
  let normalized :=
    emitGateResult combined (.gateAt 0) (.gateAt 0)
  have combine : TargetAppend runtime combined := by
    exact emitGateResult_target_append runtime
      source.emission (.constant true)
  have normalize : TargetAppend combined normalized := by
    exact emitGateResult_target_append combined
      (.gateAt 0) (.gateAt 0)
  have advance :
      TargetAppend normalized
        (advanceOutputIndexResult normalized 1) := by
    exact advanceOutputIndexResult_target_append normalized 1
  simpa [seedFormulaResult, combined, normalized] using
    targetAppend_trans combine
      (targetAppend_trans normalize advance)

private theorem extendFormulaResult_target_append
    (source : ClauseSource) (runtime : Runtime) :
    TargetAppend runtime (extendFormulaResult source runtime) := by
  let combined :=
    emitGateResult runtime source.emission (.gateAt 0)
  let normalized :=
    emitGateResult combined (.gateAt 1) (.gateAt 1)
  have combine : TargetAppend runtime combined := by
    exact emitGateResult_target_append runtime
      source.emission (.gateAt 0)
  have normalize : TargetAppend combined normalized := by
    exact emitGateResult_target_append combined
      (.gateAt 1) (.gateAt 1)
  have advance :
      TargetAppend normalized
        (advanceOutputIndexResult normalized 2) := by
    exact advanceOutputIndexResult_target_append normalized 2
  simpa [extendFormulaResult, combined, normalized] using
    targetAppend_trans combine
      (targetAppend_trans normalize advance)

private theorem emptyFormulaResult_target_append
    (runtime : Runtime) :
    TargetAppend runtime (emptyFormulaResult runtime) := by
  simpa [emptyFormulaResult] using
    emitGateResult_target_append runtime
      (.constant false) (.constant false)

private theorem formulaFoldLoopRuntime_target_append
    (count : Nat) (runtime : Runtime) :
    TargetAppend runtime
      (formulaFoldLoopRuntime count runtime) := by
  induction count generalizing runtime with
  | zero =>
      simpa [formulaFoldLoopRuntime] using
        popNewestResult_target_append runtime
  | succ count inductionHypothesis =>
      let popped := popNewestResult runtime
      let extended :=
        extendFormulaResult (runtimeClauseSource popped) popped
      have pop : TargetAppend runtime popped := by
        exact popNewestResult_target_append runtime
      have extend : TargetAppend popped extended := by
        exact extendFormulaResult_target_append
          (runtimeClauseSource popped) popped
      have tail :
          TargetAppend extended
            (formulaFoldLoopRuntime count extended) := by
        exact inductionHypothesis extended
      simpa [formulaFoldLoopRuntime, popped, extended] using
        targetAppend_trans pop
          (targetAppend_trans extend tail)

private theorem formulaFoldRuntime_target_append
    (clauseCount : Nat) (runtime : Runtime) :
    TargetAppend runtime
      (formulaFoldRuntime clauseCount runtime) := by
  cases clauseCount with
  | zero =>
      have pop := popNewestResult_target_append runtime
      have empty :=
        emptyFormulaResult_target_append
          (popNewestResult runtime)
      simpa [formulaFoldRuntime] using
        targetAppend_trans pop empty
  | succ count =>
      let popped := popNewestResult runtime
      let seeded :=
        seedFormulaResult (runtimeClauseSource popped) popped
      have pop : TargetAppend runtime popped := by
        exact popNewestResult_target_append runtime
      have seed : TargetAppend popped seeded := by
        exact seedFormulaResult_target_append
          (runtimeClauseSource popped) popped
      have fold :
          TargetAppend seeded
            (formulaFoldLoopRuntime count seeded) := by
        exact formulaFoldLoopRuntime_target_append count seeded
      simpa [formulaFoldRuntime, popped, seeded] using
        targetAppend_trans pop
          (targetAppend_trans seed fold)

private theorem formulaRuntime_target_append
    (formula : CNFFormula) :
    TargetAppend (emitInitialRuntime formula)
      (formulaRuntime formula) := by
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses
      (emitInitialRuntime formula)
  have clauseAppend :
      TargetAppend (emitInitialRuntime formula) clauses := by
    exact clauseListRuntime_target_append
      formula.variableCount formula.clauses
      (emitInitialRuntime formula)
  have foldAppend :
      TargetAppend clauses
        (formulaFoldRuntime formula.clauses.length clauses) := by
    exact formulaFoldRuntime_target_append
      formula.clauses.length clauses
  simpa [formulaRuntime, clauses] using
    targetAppend_trans clauseAppend foldAppend

private theorem circuitSuffixResult_target_append
    (runtime : Runtime) :
    TargetAppend runtime (circuitSuffixResult runtime) := by
  refine
    ⟨[.programEnd] ++
        encodeSourceTokens
          (.gate runtime.registers.outputIndex) ++
        [.outputsEnd, .instanceEnd],
      ?_⟩
  change
    runtime.targetTokens ++ [.programEnd] ++
          encodeSourceTokens
            (.gate runtime.registers.outputIndex) ++
          [.outputsEnd, .instanceEnd] =
      runtime.targetTokens ++
        ([.programEnd] ++
          encodeSourceTokens
            (.gate runtime.registers.outputIndex) ++
          [.outputsEnd, .instanceEnd])
  simp only [List.append_assoc]

private theorem completedRuntime_target_append
    (formula : CNFFormula) :
    TargetAppend (emitInitialRuntime formula)
      (completedRuntime formula) := by
  have formulaAppend := formulaRuntime_target_append formula
  have suffixAppend :=
    circuitSuffixResult_target_append (formulaRuntime formula)
  simpa [completedRuntime] using
    targetAppend_trans formulaAppend suffixAppend

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
  have constantFalseCells :
      (SourceParser.sourceCells (.constant false)).length = 2 := by
    rfl
  have equalLength :
      (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token rest).length =
        (canonicalSource formula).length := by
    rw [canonicalSource_eq_carrier_layout]
    change
      (PNP.Concrete.CNFToNANDControllerCountTrace.markedSource
        (CNFToNANDWorkspace.formulaTokens formula)
        processed token rest).length = _
    simp [PNP.Concrete.CNFToNANDControllerCountTrace.markedSource,
      PNP.Concrete.CNFToNANDControllerCountTrace.tokenBeforeCells,
      PNP.Concrete.CNFToNANDControllerCountTrace.tokenAfterCells,
      carrierHeaderCells_length, carrierGateCells_length,
      carrierFooterCells, carrierGateCellsFor,
      constantFalseCells, tokens]
    omega
  rw [equalLength]
  exact canonicalSource_length_le_dataMajorant formula

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

private theorem descriptorCost_le_phase
    (formula : CNFFormula) (source : List WorkSymbol)
    (runtime : Runtime) (descriptor : BlockDescriptor)
    (member : descriptor ∈ blockDescriptors)
    (sourceBound :
      source.length ≤ dataMajorant (encodeCNF formula).length)
    (targetAppend : TargetAppend runtime (completedRuntime formula))
    (checksLength :
      runtime.checks.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 2)
    (checksValues :
      ∀ value, value ∈ runtime.checks →
        value < CNFToNANDWorkspace.capacity formula) :
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
        (CNFToNANDWorkspace.capacity formula) source runtime
        descriptor.primitives ≤
      completionPhase formula := by
  rcases targetAppend with ⟨suffix, targetEq⟩
  apply descriptorProgramEnvelope_le_phaseUnit
      (descriptor := descriptor) (member := member)
  · exact capacity_le_dataMajorant formula
  · exact sourceBound
  · exact target_length_le_completed_of_append
      formula runtime suffix targetEq
  · exact checkCells_le_dataMajorant
      formula runtime.checks checksLength checksValues

private theorem formulaFoldLoopRuntime_checks_of
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks =
        prior ++ marker :: pending.reverse) :
    (formulaFoldLoopRuntime pending.length runtime).checks =
      prior := by
  induction pending generalizing runtime with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      have newest :
          popNewestResult runtime =
            popCoordinateResult runtime prior marker :=
        popNewestResult_of_checks runtime prior marker checks'
      simp [formulaFoldLoopRuntime, newest,
        popCoordinateResult]
  | cons value rest inductionHypothesis =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have newest : popNewestResult runtime = popped :=
        popNewestResult_of_checks runtime
          (prior ++ marker :: rest.reverse) value checks'
      have extendedChecks :
          (extendFormulaResult
              (runtimeClauseSource popped) popped).checks =
            prior ++ marker :: rest.reverse := by
        rw [extendFormulaResult_checks]
        simp [popped, popCoordinateResult]
      simp only [List.length_cons]
      rw [formulaFoldLoopRuntime, newest]
      exact inductionHypothesis _ extendedChecks

private theorem formulaFoldRuntime_checks_of
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks =
        prior ++ marker :: pending.reverse) :
    (formulaFoldRuntime pending.length runtime).checks = prior := by
  cases pending with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      have newest :
          popNewestResult runtime =
            popCoordinateResult runtime prior marker :=
        popNewestResult_of_checks runtime prior marker checks'
      simp [formulaFoldRuntime, newest, popCoordinateResult,
        emptyFormulaResult, emitGateResult, emitSourceResult]
  | cons value rest =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have newest : popNewestResult runtime = popped :=
        popNewestResult_of_checks runtime
          (prior ++ marker :: rest.reverse) value checks'
      have seededChecks :
          (seedFormulaResult
              (runtimeClauseSource popped) popped).checks =
            prior ++ marker :: rest.reverse := by
        rw [seedFormulaResult_checks]
        simp [popped, popCoordinateResult]
      simp only [List.length_cons]
      rw [formulaFoldRuntime, newest]
      exact formulaFoldLoopRuntime_checks_of
        prior marker rest _ seededChecks

private theorem formulaRuntime_checks_eq_nil
    (formula : CNFFormula) :
    (formulaRuntime formula).checks = [] := by
  let initial := emitInitialRuntime formula
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses initial
  let coordinates :=
    clauseListCoordinates formula.variableCount formula.clauses initial
  let pending := coordinates.reverse
  let marker := CNFToNANDWorkspace.formulaStackMarker formula
  have clausesChecks :
      clauses.checks = [] ++ marker :: pending.reverse := by
    rw [show pending.reverse = coordinates by simp [pending]]
    simpa [clauses, coordinates, initial, marker] using
      (clauseListRuntime_checks formula.variableCount
        formula.clauses initial)
  have consumed :=
    formulaFoldRuntime_checks_of [] marker pending clauses
      clausesChecks
  have pendingLength :
      pending.length = formula.clauses.length := by
    simp [pending, coordinates, clauseListCoordinates_length]
  rw [pendingLength] at consumed
  simpa [formulaRuntime, clauses, initial] using consumed

private theorem completedRuntime_checks_eq_nil
    (formula : CNFFormula) :
    (completedRuntime formula).checks = [] := by
  change (formulaRuntime formula).checks = []
  exact formulaRuntime_checks_eq_nil formula

private structure RuntimeDataBounded
    (formula : CNFFormula) (runtime : Runtime) : Prop where
  target : TargetAppend runtime (completedRuntime formula)
  checksLength :
    runtime.checks.length ≤
      (CNFToNANDWorkspace.formulaTokens formula).length + 2
  checksValues :
    ∀ value, value ∈ runtime.checks →
      value < CNFToNANDWorkspace.capacity formula

private theorem RuntimeDataBounded.descriptor
    {formula : CNFFormula} {source : List WorkSymbol}
    {runtime : Runtime} {descriptor : BlockDescriptor}
    (bounded : RuntimeDataBounded formula runtime)
    (member : descriptor ∈ blockDescriptors)
    (sourceBound :
      source.length ≤ dataMajorant (encodeCNF formula).length) :
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
        (CNFToNANDWorkspace.capacity formula) source runtime
        descriptor.primitives ≤
      completionPhase formula := by
  exact descriptorCost_le_phase formula source runtime descriptor
    member sourceBound bounded.target bounded.checksLength
    bounded.checksValues

private theorem RuntimeDataBounded.of_same_data
    {formula : CNFFormula} {initial final : Runtime}
    (bounded : RuntimeDataBounded formula initial)
    (target : final.targetTokens = initial.targetTokens)
    (checks : final.checks = initial.checks) :
    RuntimeDataBounded formula final := by
  refine ⟨?_, ?_, ?_⟩
  · rcases bounded.target with ⟨suffix, targetEq⟩
    exact ⟨suffix, by simpa [target] using targetEq⟩
  · simpa [checks] using bounded.checksLength
  · intro value member
    apply bounded.checksValues value
    simpa [checks] using member

private theorem RuntimeDataBounded.before
    {formula : CNFFormula} {before after : Runtime}
    (afterBound : RuntimeDataBounded formula after)
    (step : TargetAppend before after)
    (checksLength :
      before.checks.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 2)
    (checksValues :
      ∀ value, value ∈ before.checks →
        value < CNFToNANDWorkspace.capacity formula) :
    RuntimeDataBounded formula before := by
  exact
    { target := targetAppend_trans step afterBound.target
      checksLength := checksLength
      checksValues := checksValues }

private theorem RuntimeDataBounded.before_of_checks_append
    {formula : CNFFormula} {before after : Runtime}
    (afterBound : RuntimeDataBounded formula after)
    (step : TargetAppend before after)
    (suffix : List Nat)
    (checks : after.checks = before.checks ++ suffix) :
    RuntimeDataBounded formula before := by
  apply afterBound.before step
  · exact Nat.le_trans
      (show before.checks.length ≤ after.checks.length by
        rw [checks, List.length_append]
        omega)
      afterBound.checksLength
  · intro value member
    apply afterBound.checksValues value
    rw [checks]
    exact List.mem_append_left suffix member

private theorem completedRuntime_dataBounded
    (formula : CNFFormula) :
    RuntimeDataBounded formula (completedRuntime formula) := by
  refine ⟨targetAppend_refl _, ?_, ?_⟩
  · rw [completedRuntime_checks_eq_nil]
    simp
  · intro value member
    rw [completedRuntime_checks_eq_nil] at member
    simp at member

private theorem RuntimeDataBounded.resetLiteral
    {formula : CNFFormula} {runtime : Runtime}
    (bounded : RuntimeDataBounded formula runtime) :
    RuntimeDataBounded formula (resetLiteralResult runtime) := by
  exact bounded.of_same_data rfl rfl

private theorem RuntimeDataBounded.advanceLiteral
    {formula : CNFFormula} {runtime : Runtime}
    (bounded : RuntimeDataBounded formula runtime) :
    RuntimeDataBounded formula (advanceLiteralResult runtime) := by
  exact bounded.of_same_data rfl rfl

private theorem markedDescriptorCost_le_phase
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken) (rest : List CNFToken)
    (runtime : Runtime) (descriptor : BlockDescriptor)
    (member : descriptor ∈ blockDescriptors)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ token :: rest)
    (bounded : RuntimeDataBounded formula runtime) :
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
        (CNFToNANDWorkspace.capacity formula)
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed token rest)
        runtime descriptor.primitives ≤
      completionPhase formula := by
  exact bounded.descriptor member
    (markedSource_length_le_dataMajorant
      formula processed token rest tokens)

private theorem versionDescriptorCost_le_phase
    (formula : CNFFormula) (runtime : Runtime)
    (descriptor : BlockDescriptor)
    (member : descriptor ∈ blockDescriptors)
    (bounded : RuntimeDataBounded formula runtime) :
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
        (CNFToNANDWorkspace.capacity formula)
        (versionMarkedSource formula) runtime descriptor.primitives ≤
      completionPhase formula := by
  exact bounded.descriptor member
    (versionMarkedSource_length_le_dataMajorant formula)

private theorem smallSteps_le_phase
    (formula : CNFFormula) (steps : Nat)
    (small : steps ≤ 100) :
    steps ≤ completionPhase formula := by
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

private theorem emitHeaderScanSteps_le_phase
    (formula : CNFFormula) :
    emitHeaderScanSteps formula ≤ completionPhase formula := by
  have tokenLength := formulaTokens_le_shiftedSize formula
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
      emitHeaderScanSteps formula ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant (encodeCNF formula).length) + 1 := by
    unfold emitHeaderScanSteps
      TargetEmitterNavigator.headerWorkSteps
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    omega
  exact Nat.le_trans linear
    (primitiveEnvelope_add_one_le_phaseUnit
      (encodeCNF formula).length)

private def directTokenCost
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken) : Nat :=
  CNFToNANDControllerCountTrace.tokenReadInstallSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed token +
    CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
      (CNFToNANDWorkspace.formulaTokens formula) processed token

private theorem directTokenCost_le_phase
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken)
    (processedBound :
      processed.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length) :
    directTokenCost formula processed token ≤
      completionPhase formula := by
  have tokenLength := formulaTokens_le_shiftedSize formula
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
      directTokenCost formula processed token ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant (encodeCNF formula).length) + 1 := by
    unfold directTokenCost
      CNFToNANDControllerCountTrace.tokenReadInstallSteps
      CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
    simp [
      CNFToNANDControllerCountTrace.tokenReadInstallSteps,
      CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps,
      CNFToNANDControllerCountTrace.tokenReaderSteps,
      PNP.Concrete.CNFToNANDControllerCountTrace.tokenBeforeCells,
      carrierHeaderCells_length,
      carrierGateCells_length,
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope]
    omega
  exact Nat.le_trans linear
    (primitiveEnvelope_add_one_le_phaseUnit
      (encodeCNF formula).length)

private theorem slotCompareSteps_le_phase
    (formula : CNFFormula) (slot : TargetEmitterLedger.Slot)
    (scratch : Nat)
    (scratchBound :
      scratch ≤ CNFToNANDWorkspace.capacity formula) :
    slotCompareSteps slot
        (CNFToNANDWorkspace.capacity formula) scratch ≤
      completionPhase formula := by
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
  have productSimple :
      scratch * (14 * capacity + 31) ≤
        45 * (master * master) := by
    calc
      scratch * (14 * capacity + 31) ≤
          master * (14 * master + 31) := product
      _ = 14 * (master * master) + 31 * master := by
        rw [Nat.mul_add]
        ac_rfl
      _ ≤ 45 * (master * master) := by omega
  have polynomial :=
    TargetEmitterScratchCompareSlot.workSteps_le_polynomialWorkBound
      slot capacity scratch
  unfold slotCompareSteps
  calc
    TargetEmitterScratchCompareSlot.workSteps
          slot capacity scratch + 1 ≤
        TargetEmitterScratchCompareSlot.polynomialWorkBound
          capacity scratch + 1 :=
      Nat.add_le_add_right polynomial 1
    _ ≤ TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
          master + 1 := by
      unfold TargetEmitterScratchCompareSlot.polynomialWorkBound
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
      omega
    _ ≤ completionPhase formula := by
      dsimp [master]
      exact primitiveEnvelope_add_one_le_phaseUnit
        (encodeCNF formula).length

private theorem emitRewindSteps_le_phase
    (formula : CNFFormula) :
    CNFToNANDControllerCountTrace.sourceRewindSteps
        (emitRewindBefore formula) ≤
      completionPhase formula := by
  have prefixBound :
      (emitRewindBefore formula).length ≤
        (canonicalSource formula).length := by
    have split :=
      congrArg List.length
        (canonicalSource_eq_emitRewindSplit formula)
    simp only [List.length_append, List.length_cons] at split
    omega
  have canonicalMaster :
      (canonicalSource formula).length ≤
        masterMajorant (encodeCNF formula).length := by
    simpa [canonicalSource] using
      carrierCells_le_masterMajorant formula
  have prefixMasterBound := Nat.le_trans prefixBound canonicalMaster
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
      CNFToNANDControllerCountTrace.sourceRewindSteps
          (emitRewindBefore formula) ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant (encodeCNF formula).length) + 1 := by
    unfold CNFToNANDControllerCountTrace.sourceRewindSteps
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    omega
  exact Nat.le_trans localBound
    (primitiveEnvelope_add_one_le_phaseUnit
      (encodeCNF formula).length)

private theorem finalizerPathSteps_le_phase
    (formula : CNFFormula) :
    finalizerPathSteps (versionMarkedSource formula) ≤
      completionPhase formula := by
  have sourceMaster :
      (versionMarkedSource formula).length ≤
        masterMajorant (encodeCNF formula).length :=
    Nat.le_trans
      (versionMarkedSource_length_le_dataMajorant formula)
      (by
        unfold masterMajorant
        omega)
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
      finalizerPathSteps (versionMarkedSource formula) ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant (encodeCNF formula).length) + 1 := by
    unfold finalizerPathSteps TargetEmitterCursorFinalizer.workSteps
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    omega
  exact Nat.le_trans localBound
    (primitiveEnvelope_add_one_le_phaseUnit
      (encodeCNF formula).length)

private theorem processed_length_le_of_tokens
    (formula : CNFFormula) (processed : List CNFToken)
    (token : CNFToken) (rest : List CNFToken)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ token :: rest) :
    processed.length ≤
      (CNFToNANDWorkspace.formulaTokens formula).length := by
  rw [tokens, List.length_append, List.length_cons]
  omega

private theorem literalCompareSteps_le_phase
    (formula : CNFFormula) (scratch : Nat)
    (scratchBound :
      scratch ≤ CNFToNANDWorkspace.capacity formula) :
    CNFToNANDControllerCountTrace.literalCompareSteps
        (CNFToNANDWorkspace.capacity formula) scratch ≤
      completionPhase formula := by
  simpa [CNFToNANDControllerCountTrace.literalCompareSteps,
    slotCompareSteps] using
    slotCompareSteps_le_phase formula .inputCount scratch scratchBound

private theorem signStepCost_le_three_phases
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ signToken positive :: next :: tail)
    (bounded : RuntimeDataBounded formula runtime) :
    signStepCost formula positive processed next tail runtime ≤
      3 * completionPhase formula := by
  have processedBound := processed_length_le_of_tokens formula
    processed (signToken positive) (next :: tail) tokens
  have direct := directTokenCost_le_phase formula processed
    (signToken positive) processedBound
  have compare := literalCompareSteps_le_phase formula 0 (by omega)
  have block :
      TargetEmitterRuntimeProgramBound.programWorkEnvelope
          (CNFToNANDWorkspace.capacity formula)
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed (signToken positive) (next :: tail))
          runtime (signBlockPrimitives positive) ≤
        completionPhase formula := by
    cases positive with
    | false =>
        simpa [signBlockPrimitives, signToken] using
          markedDescriptorCost_le_phase formula processed .f
            (next :: tail) runtime blockDescriptors[10]
            (by simp [blockDescriptors]) (by simpa [signToken] using tokens)
            bounded
    | true =>
        simpa [signBlockPrimitives, signToken] using
          markedDescriptorCost_le_phase formula processed .t
            (next :: tail) runtime blockDescriptors[11]
            (by simp [blockDescriptors]) (by simpa [signToken] using tokens)
            bounded
  unfold directTokenCost at direct
  simp only [markedSource] at block
  unfold signStepCost signPrefixCost
  omega

private theorem inRangeTStepCost_le_three_phases
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .t :: next :: tail)
    (scratchBound :
      runtime.scratch ≤ CNFToNANDWorkspace.capacity formula)
    (bounded : RuntimeDataBounded formula runtime) :
    inRangeTStepCost formula positive processed next tail runtime ≤
      3 * completionPhase formula := by
  have processedBound := processed_length_le_of_tokens formula
    processed .t (next :: tail) tokens
  have direct :=
    directTokenCost_le_phase formula processed .t processedBound
  have compare := literalCompareSteps_le_phase formula
    runtime.scratch scratchBound
  have block :
      TargetEmitterRuntimeProgramBound.programWorkEnvelope
          (CNFToNANDWorkspace.capacity formula)
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed .t (next :: tail)) runtime
          (if positive then blockDescriptors[15].primitives
            else blockDescriptors[16].primitives) ≤
        completionPhase formula := by
    cases positive with
    | false =>
        simpa using
          markedDescriptorCost_le_phase formula processed .t
            (next :: tail) runtime blockDescriptors[16]
            (by simp [blockDescriptors]) tokens bounded
    | true =>
        simpa using
          markedDescriptorCost_le_phase formula processed .t
            (next :: tail) runtime blockDescriptors[15]
            (by simp [blockDescriptors]) tokens bounded
  unfold directTokenCost at direct
  simp only [markedSource] at block
  unfold inRangeTStepCost
  omega

private theorem equalTStepCost_le_two_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .t :: next :: tail)
    (scratchBound :
      runtime.scratch ≤ CNFToNANDWorkspace.capacity formula) :
    equalTStepCost formula processed runtime ≤
      2 * completionPhase formula := by
  have processedBound := processed_length_le_of_tokens formula
    processed .t (next :: tail) tokens
  have direct :=
    directTokenCost_le_phase formula processed .t processedBound
  have compare := literalCompareSteps_le_phase formula
    runtime.scratch scratchBound
  unfold directTokenCost at direct
  unfold equalTStepCost
  omega

private theorem overflowTStepCost_le_phase
    (formula : CNFFormula) (processed : List CNFToken)
    (next : CNFToken) (tail : List CNFToken)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .t :: next :: tail) :
    overflowTStepCost formula processed ≤
      completionPhase formula := by
  have processedBound := processed_length_le_of_tokens formula
    processed .t (next :: tail) tokens
  simpa [overflowTStepCost, directTokenCost] using
    directTokenCost_le_phase formula processed .t processedBound

private theorem validTerminatorCost_le_three_phases
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .f :: next :: tail)
    (scratchBound :
      runtime.scratch ≤ CNFToNANDWorkspace.capacity formula)
    (bounded : RuntimeDataBounded formula runtime) :
    validTerminatorCost formula positive processed runtime
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .f (next :: tail)) ≤
      3 * completionPhase formula := by
  have processedBound := processed_length_le_of_tokens formula
    processed .f (next :: tail) tokens
  have direct :=
    directTokenCost_le_phase formula processed .f processedBound
  have compare := literalCompareSteps_le_phase formula
    runtime.scratch scratchBound
  have block :
      TargetEmitterRuntimeProgramBound.programWorkEnvelope
          (CNFToNANDWorkspace.capacity formula)
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed .f (next :: tail)) runtime
          (validLiteralPrimitives positive) ≤
        completionPhase formula := by
    cases positive with
    | false =>
        simpa [validLiteralPrimitives] using
          markedDescriptorCost_le_phase formula processed .f
            (next :: tail) runtime blockDescriptors[13]
            (by simp [blockDescriptors]) tokens bounded
    | true =>
        simpa [validLiteralPrimitives] using
          markedDescriptorCost_le_phase formula processed .f
            (next :: tail) runtime blockDescriptors[12]
            (by simp [blockDescriptors]) tokens bounded
  unfold directTokenCost at direct
  unfold validTerminatorCost
  omega

private theorem invalidEqualTerminatorCost_le_three_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .f :: next :: tail)
    (scratchBound :
      runtime.scratch ≤ CNFToNANDWorkspace.capacity formula)
    (bounded : RuntimeDataBounded formula runtime) :
    invalidEqualTerminatorCost formula processed runtime
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .f (next :: tail)) ≤
      3 * completionPhase formula := by
  have processedBound := processed_length_le_of_tokens formula
    processed .f (next :: tail) tokens
  have direct :=
    directTokenCost_le_phase formula processed .f processedBound
  have compare := literalCompareSteps_le_phase formula
    runtime.scratch scratchBound
  have block :=
    markedDescriptorCost_le_phase formula processed .f
      (next :: tail) runtime blockDescriptors[14]
      (by simp [blockDescriptors]) tokens bounded
  unfold directTokenCost at direct
  unfold invalidEqualTerminatorCost
  omega

private theorem overflowTerminatorCost_le_two_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .f :: next :: tail)
    (bounded : RuntimeDataBounded formula runtime) :
    overflowTerminatorCost formula processed runtime
        (markedSource
          (CNFToNANDWorkspace.formulaTokens formula)
          processed .f (next :: tail)) ≤
      2 * completionPhase formula := by
  have processedBound := processed_length_le_of_tokens formula
    processed .f (next :: tail) tokens
  have direct :=
    directTokenCost_le_phase formula processed .f processedBound
  have block :=
    markedDescriptorCost_le_phase formula processed .f
      (next :: tail) runtime blockDescriptors[14]
      (by simp [blockDescriptors]) tokens bounded
  unfold directTokenCost at direct
  unfold overflowTerminatorCost
  omega

private theorem inRangeTRunCost_le_phases
    (formula : CNFFormula) (positive : Bool) :
    ∀ (count : Nat) (processed suffix : List CNFToken)
      (runtime : Runtime),
      CNFToNANDWorkspace.formulaTokens formula =
          processed ++ List.replicate count .t ++ suffix →
      suffix ≠ [] →
      runtime.scratch + count ≤
        CNFToNANDWorkspace.capacity formula →
      RuntimeDataBounded formula runtime →
      inRangeTRunCost formula positive count processed suffix runtime ≤
        3 * count * completionPhase formula := by
  intro count
  induction count with
  | zero =>
      intro processed suffix runtime tokens suffixNonempty
        scratchBound bounded
      simp [inRangeTRunCost]
  | succ count inductionHypothesis =>
      intro processed suffix runtime tokens suffixNonempty
        scratchBound bounded
      let remainder := List.replicate count CNFToken.t ++ suffix
      have remainderNonempty : remainder ≠ [] :=
        List.append_ne_nil_of_right_ne_nil _ suffixNonempty
      obtain ⟨next, tail, remainderEq⟩ :=
        List.exists_cons_of_ne_nil remainderNonempty
      have stepTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ .t :: next :: tail := by
        simpa [List.replicate_succ, remainder, remainderEq,
          List.append_assoc] using tokens
      have stepBound :=
        inRangeTStepCost_le_three_phases formula positive
          processed next tail runtime stepTokens
          (by omega) bounded
      have recursiveTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            (processed ++ [.t]) ++
              List.replicate count .t ++ suffix := by
        simpa [List.replicate_succ, List.append_assoc] using tokens
      have recursiveScratch :
          (advanceLiteralResult runtime).scratch + count ≤
            CNFToNANDWorkspace.capacity formula := by
        simp [advanceLiteralResult]
        omega
      have recursiveBound :=
        inductionHypothesis (processed ++ [.t]) suffix
          (advanceLiteralResult runtime) recursiveTokens
          suffixNonempty recursiveScratch bounded.advanceLiteral
      simp only [inRangeTRunCost]
      rw [show
        List.replicate count CNFToken.t ++ suffix =
          next :: tail from remainderEq]
      calc
        inRangeTStepCost formula positive processed next tail runtime +
              inRangeTRunCost formula positive count
                (processed ++ [.t]) suffix
                (advanceLiteralResult runtime) ≤
            3 * completionPhase formula +
              3 * count * completionPhase formula :=
          Nat.add_le_add stepBound recursiveBound
        _ = (3 + 3 * count) * completionPhase formula := by
          rw [Nat.add_mul]
        _ = 3 * (count + 1) * completionPhase formula := by
          congr 1
          omega

private theorem overflowTRunCost_le_phases
    (formula : CNFFormula) :
    ∀ (count : Nat) (processed suffix : List CNFToken),
      CNFToNANDWorkspace.formulaTokens formula =
          processed ++ List.replicate count .t ++ suffix →
      suffix ≠ [] →
      overflowTRunCost formula count processed suffix ≤
        count * completionPhase formula := by
  intro count
  induction count with
  | zero =>
      intro processed suffix tokens suffixNonempty
      simp [overflowTRunCost]
  | succ count inductionHypothesis =>
      intro processed suffix tokens suffixNonempty
      let remainder := List.replicate count CNFToken.t ++ suffix
      have remainderNonempty : remainder ≠ [] :=
        List.append_ne_nil_of_right_ne_nil _ suffixNonempty
      obtain ⟨next, tail, remainderEq⟩ :=
        List.exists_cons_of_ne_nil remainderNonempty
      have stepTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ .t :: next :: tail := by
        simpa [List.replicate_succ, remainder, remainderEq,
          List.append_assoc] using tokens
      have stepBound :=
        overflowTStepCost_le_phase formula processed
          next tail stepTokens
      have recursiveTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            (processed ++ [.t]) ++
              List.replicate count .t ++ suffix := by
        simpa [List.replicate_succ, List.append_assoc] using tokens
      have recursiveBound :=
        inductionHypothesis (processed ++ [.t]) suffix
          recursiveTokens suffixNonempty
      simp only [overflowTRunCost]
      rw [show
        List.replicate count CNFToken.t ++ suffix =
          next :: tail from remainderEq]
      calc
        overflowTStepCost formula processed +
              overflowTRunCost formula count
                (processed ++ [.t]) suffix ≤
            completionPhase formula +
              count * completionPhase formula :=
          Nat.add_le_add stepBound recursiveBound
        _ = (1 + count) * completionPhase formula := by
          rw [Nat.add_mul, Nat.one_mul]
        _ = (count + 1) * completionPhase formula := by
          rw [Nat.add_comm 1 count]

private theorem literalSignCost_le_three_phases
    (formula : CNFFormula) (positive : Bool)
    (processed : List CNFToken) (count : Nat)
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ signToken positive ::
          List.replicate count .t ++ .f :: next :: tail)
    (bounded : RuntimeDataBounded formula runtime) :
    literalSignCost formula positive processed count next tail runtime ≤
      3 * completionPhase formula := by
  cases count with
  | zero =>
      have stepTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ signToken positive :: .f :: next :: tail := by
        simpa using tokens
      rw [literalSignCost_zero]
      exact
        signStepCost_le_three_phases formula positive processed .f
          (next :: tail) runtime stepTokens bounded
  | succ remaining =>
      have stepTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ signToken positive :: .t ::
              (List.replicate remaining .t ++ .f :: next :: tail) := by
        simpa [Nat.succ_eq_add_one, List.replicate_succ,
          List.append_assoc] using tokens
      have stepBound :=
        signStepCost_le_three_phases formula positive processed .t
          (List.replicate remaining .t ++ .f :: next :: tail)
          runtime stepTokens bounded
      rw [literalSignCost_succ]
      exact stepBound

private theorem three_successor_coefficient
    (count : Nat) :
    3 + 3 * (count + 1) = 3 * ((count + 1) + 1) := by
  omega

private theorem unaryLiteral_overflow_coefficient
    (count : Nat) :
    2 + count + 2 ≤ 3 * ((count + 1) + 1) := by
  omega

private theorem unaryLiteralCost_le_phases
    (formula : CNFFormula) (positive : Bool) :
    ∀ (count : Nat) (processed : List CNFToken)
      (runtime : Runtime) (next : CNFToken)
      (tail : List CNFToken),
      CNFToNANDWorkspace.formulaTokens formula =
          processed ++ List.replicate count .t ++
            .f :: next :: tail →
      runtime.scratch ≤ CNFToNANDWorkspace.capacity formula →
      runtime.registers.inputCount ≤
        CNFToNANDWorkspace.capacity formula →
      RuntimeDataBounded formula runtime →
      unaryLiteralCost formula positive count processed runtime
          next tail ≤
        3 * (count + 1) * completionPhase formula := by
  intro count
  induction count with
  | zero =>
      intro processed runtime next tail tokens scratchBound inputBound bounded
      have terminatorTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ .f :: next :: tail := by
        simpa using tokens
      by_cases less : runtime.scratch < runtime.registers.inputCount
      · have cost :=
          validTerminatorCost_le_three_phases formula positive
            processed next tail runtime terminatorTokens scratchBound bounded
        simp only [unaryLiteralCost]
        rw [if_pos less]
        exact cost
      · have cost :=
          invalidEqualTerminatorCost_le_three_phases formula
            processed next tail runtime terminatorTokens scratchBound bounded
        simp only [unaryLiteralCost]
        rw [if_neg less]
        exact cost
  | succ count inductionHypothesis =>
      intro processed runtime next tail tokens scratchBound inputBound bounded
      let remainder :=
        List.replicate count CNFToken.t ++ .f :: next :: tail
      have remainderNonempty : remainder ≠ [] := by
        simp [remainder]
      obtain ⟨nextToken, tokenTail, remainderEq⟩ :=
        List.exists_cons_of_ne_nil remainderNonempty
      have stepTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ .t :: nextToken :: tokenTail := by
        simpa [List.replicate_succ, remainder, remainderEq,
          List.append_assoc] using tokens
      have recursiveTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            (processed ++ [.t]) ++ List.replicate count .t ++
              .f :: next :: tail := by
        simpa [List.replicate_succ, List.append_assoc] using tokens
      by_cases less : runtime.scratch < runtime.registers.inputCount
      · have stepBound :=
          inRangeTStepCost_le_three_phases formula positive processed
            nextToken tokenTail runtime stepTokens scratchBound bounded
        have nextScratch :
            (advanceLiteralResult runtime).scratch ≤
              CNFToNANDWorkspace.capacity formula := by
          simpa [advanceLiteralResult] using
            Nat.le_trans less inputBound
        have nextInputBound :
            (advanceLiteralResult runtime).registers.inputCount ≤
              CNFToNANDWorkspace.capacity formula := by
          simpa [advanceLiteralResult] using inputBound
        have restBound :=
          inductionHypothesis (processed ++ [.t])
            (advanceLiteralResult runtime) next tail recursiveTokens
            nextScratch nextInputBound bounded.advanceLiteral
        rw [unaryLiteralCost_succ formula positive count processed
          runtime next tail nextToken tokenTail remainderEq]
        rw [if_pos less]
        calc
          inRangeTStepCost formula positive processed nextToken
                  tokenTail runtime +
                unaryLiteralCost formula positive count
                  (processed ++ [.t]) (advanceLiteralResult runtime)
                  next tail ≤
              3 * completionPhase formula +
                3 * (count + 1) * completionPhase formula :=
            Nat.add_le_add stepBound restBound
          _ = (3 + 3 * (count + 1)) * completionPhase formula := by
            rw [Nat.add_mul]
          _ = 3 * ((count + 1) + 1) * completionPhase formula := by
            rw [three_successor_coefficient]
      · have equalBound :=
          equalTStepCost_le_two_phases formula processed
            nextToken tokenTail runtime stepTokens scratchBound
        have overflowBound :=
          overflowTRunCost_le_phases formula count
            (processed ++ [.t]) (.f :: next :: tail)
            recursiveTokens (by simp)
        have terminatorTokens :
            CNFToNANDWorkspace.formulaTokens formula =
              (processed ++ List.replicate (count + 1) .t) ++
                .f :: next :: tail := by
          simpa [List.append_assoc] using tokens
        have terminatorBound :=
          overflowTerminatorCost_le_two_phases formula
            (processed ++ List.replicate (count + 1) .t)
            next tail runtime terminatorTokens bounded
        rw [unaryLiteralCost_succ formula positive count processed
          runtime next tail nextToken tokenTail remainderEq]
        rw [if_neg less]
        have coefficient := unaryLiteral_overflow_coefficient count
        have scaled :=
          Nat.mul_le_mul_right (completionPhase formula) coefficient
        calc
          equalTStepCost formula processed runtime +
                  overflowTRunCost formula count (processed ++ [.t])
                    (.f :: next :: tail) +
                overflowTerminatorCost formula
                  (processed ++ List.replicate (count + 1) .t)
                  runtime
                  (markedSource
                    (CNFToNANDWorkspace.formulaTokens formula)
                    (processed ++ List.replicate (count + 1) .t)
                    .f (next :: tail)) ≤
              2 * completionPhase formula +
                  count * completionPhase formula +
                2 * completionPhase formula := by
            exact
              Nat.add_le_add
                (Nat.add_le_add equalBound overflowBound)
                terminatorBound
          _ = (2 + count + 2) * completionPhase formula := by
            rw [Nat.add_mul, Nat.add_mul]
          _ ≤ 3 * ((count + 1) + 1) * completionPhase formula := by
            simpa only [Nat.mul_assoc] using scaled

private theorem literalCost_coefficient
    (index : Nat) :
    3 + 3 * (index + 1) + index + 2 =
      4 * (index + 2) := by
  omega

private theorem two_phase_identity (phase : Nat) :
    phase + phase = 2 * phase := by
  omega

private theorem three_phase_identity (phase : Nat) :
    phase + phase + phase = 3 * phase := by
  omega

private theorem four_phase_identity (phase : Nat) :
    phase + phase + 2 * phase = 4 * phase := by
  omega

private theorem four_single_phase_identity (phase : Nat) :
    phase + phase + phase + phase = 4 * phase := by
  omega

private theorem formulaLoop_successor_coefficient
    (count : Nat) :
    4 + (4 * count + 2) = 4 * (count + 1) + 2 := by
  omega

private theorem formulaFold_successor_coefficient
    (count : Nat) :
    4 + (4 * count + 2) ≤ 4 * (count + 1) + 3 := by
  omega

private theorem clausePath_coefficient
    (literalTokens literalCount : Nat)
    (lengthBound : literalCount ≤ literalTokens) :
    2 + 4 * literalTokens + 1 + 3 * (literalCount + 1) ≤
      8 * (literalTokens + 2) := by
  omega

private theorem literalCost_le_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (literal : CNFLiteral) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeLiteralTokens literal ++ next :: tail)
    (inputBound :
      runtime.registers.inputCount ≤
        CNFToNANDWorkspace.capacity formula)
    (bounded : RuntimeDataBounded formula runtime) :
    literalCost formula processed literal next tail runtime ≤
      4 * (encodeLiteralTokens literal).length *
        completionPhase formula := by
  let afterSign :=
    processed ++ [signToken literal.positive]
  let reset := resetLiteralResult runtime
  let terminatorProcessed :=
    afterSign ++ List.replicate literal.variableIndex CNFToken.t
  have expandedTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ signToken literal.positive ::
          List.replicate literal.variableIndex .t ++
            .f :: next :: tail := by
    simpa [encodeLiteralTokens, signToken,
      encodeUnaryTokens_eq_replicate, List.append_assoc] using tokens
  have unaryTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        afterSign ++ List.replicate literal.variableIndex .t ++
          .f :: next :: tail := by
    simpa [afterSign, List.append_assoc] using expandedTokens
  have signBound :=
    literalSignCost_le_three_phases formula literal.positive
      processed literal.variableIndex next tail runtime
      expandedTokens bounded
  have resetBound : RuntimeDataBounded formula reset := by
    exact bounded.resetLiteral
  have unaryBound :=
    unaryLiteralCost_le_phases formula literal.positive
      literal.variableIndex afterSign reset next tail unaryTokens
      (by simp [reset, resetLiteralResult])
      (by simpa [reset, resetLiteralResult] using inputBound)
      resetBound
  have overflowBound :=
    overflowTRunCost_le_phases formula literal.variableIndex
      afterSign (.f :: next :: tail) unaryTokens (by simp)
  have terminatorTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        terminatorProcessed ++ .f :: next :: tail := by
    simpa [terminatorProcessed, List.append_assoc] using unaryTokens
  have terminatorBound :=
    overflowTerminatorCost_le_two_phases formula terminatorProcessed
      next tail reset terminatorTokens resetBound
  have literalLength :
      (encodeLiteralTokens literal).length =
        literal.variableIndex + 2 := by
    simp [encodeLiteralTokens, encodeUnaryTokens_eq_replicate]
  unfold literalCost
  dsimp only
  rw [show processed ++ [signToken literal.positive] = afterSign by rfl]
  rw [show resetLiteralResult runtime = reset by rfl]
  rw [show
    afterSign ++ List.replicate literal.variableIndex CNFToken.t =
      terminatorProcessed by rfl]
  calc
    literalSignCost formula literal.positive processed
            literal.variableIndex next tail runtime +
          unaryLiteralCost formula literal.positive
            literal.variableIndex afterSign reset next tail +
        overflowTRunCost formula literal.variableIndex afterSign
          (.f :: next :: tail) +
        overflowTerminatorCost formula terminatorProcessed reset
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            terminatorProcessed .f (next :: tail)) ≤
      3 * completionPhase formula +
          3 * (literal.variableIndex + 1) * completionPhase formula +
        literal.variableIndex * completionPhase formula +
        2 * completionPhase formula := by
      exact
        Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add signBound unaryBound)
            overflowBound)
          terminatorBound
    _ =
        (3 + 3 * (literal.variableIndex + 1) +
            literal.variableIndex + 2) * completionPhase formula := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
    _ = 4 * (literal.variableIndex + 2) * completionPhase formula := by
      rw [literalCost_coefficient]
    _ = 4 * (encodeLiteralTokens literal).length *
          completionPhase formula := by
      rw [literalLength]

private theorem literalListCost_le_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (literals : List CNFLiteral) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeLiteralListTokens literals ++
          next :: tail)
    (inputBound :
      runtime.registers.inputCount ≤
        CNFToNANDWorkspace.capacity formula)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (literalListRuntime formula.variableCount literals runtime)) :
    literalListCost formula processed literals next tail runtime ≤
      4 * (encodeLiteralListTokens literals).length *
        completionPhase formula := by
  induction literals generalizing processed runtime with
  | nil =>
      simp [literalListCost, encodeLiteralListTokens]
  | cons literal rest inductionHypothesis =>
      let remainder :=
        encodeLiteralListTokens rest ++ next :: tail
      have remainderNonempty : remainder ≠ [] := by
        simp [remainder]
      obtain ⟨successor, successorTail, remainderEq⟩ :=
        List.exists_cons_of_ne_nil remainderNonempty
      let intermediate :=
        literalRuntime formula.variableCount literal runtime
      have literalTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ encodeLiteralTokens literal ++
              successor :: successorTail := by
        rw [encodeLiteralListTokens] at tokens
        simpa [remainder, remainderEq, List.append_assoc] using tokens
      have recursiveTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            (processed ++ encodeLiteralTokens literal) ++
              encodeLiteralListTokens rest ++ next :: tail := by
        rw [encodeLiteralListTokens] at tokens
        simpa [List.append_assoc] using tokens
      have tailFinalBound :
          RuntimeDataBounded formula
            (literalListRuntime formula.variableCount rest intermediate) := by
        simpa [literalListRuntime, intermediate] using finalBound
      have intermediateBound :
          RuntimeDataBounded formula intermediate := by
        apply tailFinalBound.before_of_checks_append
            (literalListRuntime_target_append
              formula.variableCount rest intermediate)
            (literalListCoordinates formula.variableCount rest intermediate)
        exact literalListRuntime_checks
          formula.variableCount rest intermediate
      have intermediateInputBound :
          intermediate.registers.inputCount ≤
            CNFToNANDWorkspace.capacity formula := by
        simpa [intermediate, literalRuntime_inputCount] using inputBound
      have firstBound :=
        literalCost_le_phases formula processed literal successor
          successorTail runtime literalTokens inputBound startBound
      have restBound :=
        inductionHypothesis
          (processed ++ encodeLiteralTokens literal) intermediate
          recursiveTokens intermediateInputBound intermediateBound
          tailFinalBound
      rw [literalListCost_cons_of_remainder formula processed literal rest
        next tail runtime successor successorTail remainderEq]
      calc
        literalCost formula processed literal successor
                successorTail runtime +
              literalListCost formula
                (processed ++ encodeLiteralTokens literal) rest
                next tail intermediate ≤
            4 * (encodeLiteralTokens literal).length *
                completionPhase formula +
              4 * (encodeLiteralListTokens rest).length *
                completionPhase formula :=
          Nat.add_le_add firstBound restBound
        _ =
            (4 * (encodeLiteralTokens literal).length +
                4 * (encodeLiteralListTokens rest).length) *
              completionPhase formula := by
          rw [Nat.add_mul]
        _ =
            4 * ((encodeLiteralTokens literal).length +
                (encodeLiteralListTokens rest).length) *
              completionPhase formula := by
          rw [Nat.mul_add]
        _ =
            4 * (encodeLiteralListTokens (literal :: rest)).length *
              completionPhase formula := by
          simp [encodeLiteralListTokens]

private theorem blockDescriptor9_mem :
    blockDescriptors[9] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor19_mem :
    blockDescriptors[19] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor20_mem :
    blockDescriptors[20] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor21_mem :
    blockDescriptors[21] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor22_mem :
    blockDescriptors[22] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor23_mem :
    blockDescriptors[23] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor24_mem :
    blockDescriptors[24] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor25_mem :
    blockDescriptors[25] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor26_mem :
    blockDescriptors[26] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor27_mem :
    blockDescriptors[27] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor28_mem :
    blockDescriptors[28] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor29_mem :
    blockDescriptors[29] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor30_mem :
    blockDescriptors[30] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor31_mem :
    blockDescriptors[31] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem blockDescriptor32_mem :
    blockDescriptors[32] ∈ blockDescriptors := by simp [blockDescriptors]

private theorem clauseSeparatorCost_le_two_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .sep :: next :: tail)
    (bounded : RuntimeDataBounded formula runtime) :
    clauseSeparatorCost formula processed next tail runtime ≤
      2 * completionPhase formula := by
  have processedBound :=
    processed_length_le_of_tokens formula processed .sep
      (next :: tail) tokens
  have direct :=
    directTokenCost_le_phase formula processed .sep processedBound
  have block :=
    markedDescriptorCost_le_phase formula processed .sep
      (next :: tail) runtime blockDescriptors[9]
      blockDescriptor9_mem tokens bounded
  unfold directTokenCost at direct
  simp only [markedSource] at block
  unfold clauseSeparatorCost
  dsimp only
  calc
    CNFToNANDControllerCountTrace.tokenReadInstallSteps
            (CNFToNANDWorkspace.formulaTokens formula) processed .sep +
          TargetEmitterRuntimeProgramBound.programWorkEnvelope
            (CNFToNANDWorkspace.capacity formula)
            (markedSource
              (CNFToNANDWorkspace.formulaTokens formula)
              processed .sep (next :: tail))
            runtime blockDescriptors[9].primitives +
        CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
          (CNFToNANDWorkspace.formulaTokens formula) processed .sep =
      (CNFToNANDControllerCountTrace.tokenReadInstallSteps
            (CNFToNANDWorkspace.formulaTokens formula) processed .sep +
          CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
            (CNFToNANDWorkspace.formulaTokens formula) processed .sep) +
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          (CNFToNANDWorkspace.capacity formula)
          (markedSource
            (CNFToNANDWorkspace.formulaTokens formula)
            processed .sep (next :: tail))
          runtime blockDescriptors[9].primitives := by
        ac_rfl
    _ ≤ completionPhase formula + completionPhase formula :=
      Nat.add_le_add direct block
    _ = 2 * completionPhase formula :=
      two_phase_identity (completionPhase formula)

private theorem clauseFoldLoopCost_le_phases
    (formula : CNFFormula) (source : List WorkSymbol)
    (sourceBound :
      source.length ≤ dataMajorant (encodeCNF formula).length)
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks =
        prior ++ marker :: pending.reverse)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (clauseFoldLoopRuntime pending.length runtime)) :
    clauseFoldLoopCost
        (CNFToNANDWorkspace.capacity formula) source marker
        pending runtime ≤
      3 * (pending.length + 1) * completionPhase formula := by
  induction pending generalizing runtime with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      let popped := popCoordinateResult runtime prior marker
      have newest : popNewestResult runtime = popped :=
        popNewestResult_of_checks runtime prior marker checks'
      have finishBound :
          RuntimeDataBounded formula
            (finishNonemptyClauseResult popped) := by
        simpa [clauseFoldLoopRuntime, newest, popped] using finalBound
      have poppedBound : RuntimeDataBounded formula popped := by
        apply finishBound.before_of_checks_append
            (finishNonemptyClauseResult_target_append popped)
            [popped.registers.outputIndex]
        exact finishNonemptyClauseResult_checks popped
      have first := startBound.descriptor
        blockDescriptor21_mem
        sourceBound
      have compare := slotCompareSteps_le_phase formula .currentGate marker
        (Nat.le_of_lt (startBound.checksValues marker (by
          rw [checks']
          simp)))
      have last := poppedBound.descriptor
        blockDescriptor23_mem
        sourceBound
      simp only [clauseFoldLoopCost]
      rw [newest]
      calc
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
                (CNFToNANDWorkspace.capacity formula) source runtime
                blockDescriptors[21].primitives +
              slotCompareSteps .currentGate
                (CNFToNANDWorkspace.capacity formula) marker +
            TargetEmitterRuntimeProgramBound.programWorkEnvelope
              (CNFToNANDWorkspace.capacity formula) source popped
              blockDescriptors[23].primitives ≤
            completionPhase formula + completionPhase formula +
              completionPhase formula :=
          Nat.add_le_add (Nat.add_le_add first compare) last
        _ = 3 * completionPhase formula :=
          three_phase_identity (completionPhase formula)
  | cons value rest inductionHypothesis =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have newest : popNewestResult runtime = popped :=
        popNewestResult_of_checks runtime
          (prior ++ marker :: rest.reverse) value checks'
      let extended := extendClauseResult popped
      have extendedChecks :
          extended.checks = prior ++ marker :: rest.reverse := by
        simpa [extended, popped, popCoordinateResult] using
          extendClauseResult_checks popped
      have runtimeChecks : runtime.checks = extended.checks ++ [value] := by
        rw [checks', extendedChecks]
      have tailFinalBound :
          RuntimeDataBounded formula
            (clauseFoldLoopRuntime rest.length extended) := by
        simpa [clauseFoldLoopRuntime, newest, extended] using finalBound
      have extendedBound : RuntimeDataBounded formula extended := by
        apply tailFinalBound.before
            (clauseFoldLoopRuntime_target_append rest.length extended)
        · exact Nat.le_trans
            (show extended.checks.length ≤ runtime.checks.length by
              rw [runtimeChecks, List.length_append]
              omega)
            startBound.checksLength
        · intro coordinate member
          apply startBound.checksValues coordinate
          rw [runtimeChecks]
          exact List.mem_append_left [value] member
      have poppedBound : RuntimeDataBounded formula popped := by
        apply extendedBound.before_of_checks_append
            (extendClauseResult_target_append popped) []
        simpa [extended] using extendClauseResult_checks popped
      have first := startBound.descriptor
        blockDescriptor21_mem
        sourceBound
      have compare := slotCompareSteps_le_phase formula .currentGate value
        (Nat.le_of_lt (startBound.checksValues value (by
          rw [checks']
          simp)))
      have block := poppedBound.descriptor
        blockDescriptor22_mem
        sourceBound
      have restBound :=
        inductionHypothesis extended extendedChecks extendedBound
          tailFinalBound
      have prefixRaw :=
        Nat.add_le_add (Nat.add_le_add first compare) block
      have prefixBound :=
        Nat.le_trans prefixRaw
          (Nat.le_of_eq (three_phase_identity (completionPhase formula)))
      simp only [clauseFoldLoopCost]
      rw [newest]
      dsimp only [extended] at restBound ⊢
      calc
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
                (CNFToNANDWorkspace.capacity formula) source runtime
                blockDescriptors[21].primitives +
              slotCompareSteps .currentGate
                (CNFToNANDWorkspace.capacity formula) value +
            TargetEmitterRuntimeProgramBound.programWorkEnvelope
                (CNFToNANDWorkspace.capacity formula) source popped
                blockDescriptors[22].primitives +
            clauseFoldLoopCost
              (CNFToNANDWorkspace.capacity formula) source marker rest
              (extendClauseResult popped) ≤
          3 * completionPhase formula +
            3 * (rest.length + 1) * completionPhase formula := by
          exact Nat.add_le_add prefixBound restBound
        _ = (3 + 3 * (rest.length + 1)) *
              completionPhase formula := by
          rw [Nat.add_mul]
        _ = 3 * ((rest.length + 1) + 1) *
              completionPhase formula := by
          rw [three_successor_coefficient]
        _ = 3 * ((value :: rest).length + 1) *
              completionPhase formula := by
          simp

private theorem clauseFoldCost_le_phases
    (formula : CNFFormula) (source : List WorkSymbol)
    (sourceBound :
      source.length ≤ dataMajorant (encodeCNF formula).length)
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks =
        prior ++ marker :: pending.reverse)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (clauseFoldRuntime pending.length runtime)) :
    clauseFoldCost
        (CNFToNANDWorkspace.capacity formula) source marker
        pending runtime ≤
      3 * (pending.length + 1) * completionPhase formula := by
  cases pending with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      let popped := popCoordinateResult runtime prior marker
      have newest : popNewestResult runtime = popped :=
        popNewestResult_of_checks runtime prior marker checks'
      have pushBound :
          RuntimeDataBounded formula (pushTotalGateResult popped) := by
        simpa [clauseFoldRuntime, newest, popped] using finalBound
      have poppedBound : RuntimeDataBounded formula popped := by
        apply pushBound.before_of_checks_append
            (pushTotalGateResult_target_append popped)
            [popped.registers.currentGate]
        simp [pushTotalGateResult]
      have first := startBound.descriptor
        blockDescriptor19_mem
        sourceBound
      have compare := slotCompareSteps_le_phase formula .currentGate marker
        (Nat.le_of_lt (startBound.checksValues marker (by
          rw [checks']
          simp)))
      have last := poppedBound.descriptor
        blockDescriptor24_mem
        sourceBound
      simp only [clauseFoldCost]
      rw [newest]
      calc
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
                (CNFToNANDWorkspace.capacity formula) source runtime
                blockDescriptors[19].primitives +
              slotCompareSteps .currentGate
                (CNFToNANDWorkspace.capacity formula) marker +
            TargetEmitterRuntimeProgramBound.programWorkEnvelope
              (CNFToNANDWorkspace.capacity formula) source popped
              blockDescriptors[24].primitives ≤
            completionPhase formula + completionPhase formula +
              completionPhase formula :=
          Nat.add_le_add (Nat.add_le_add first compare) last
        _ = 3 * completionPhase formula :=
          three_phase_identity (completionPhase formula)
  | cons value rest =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have newest : popNewestResult runtime = popped :=
        popNewestResult_of_checks runtime
          (prior ++ marker :: rest.reverse) value checks'
      let seeded := seedClauseResult popped
      have seededChecks :
          seeded.checks = prior ++ marker :: rest.reverse := by
        simpa [seeded, popped, popCoordinateResult] using
          seedClauseResult_checks popped
      have runtimeChecks : runtime.checks = seeded.checks ++ [value] := by
        rw [checks', seededChecks]
      have loopFinalBound :
          RuntimeDataBounded formula
            (clauseFoldLoopRuntime rest.length seeded) := by
        simpa [clauseFoldRuntime, newest, seeded] using finalBound
      have seededBound : RuntimeDataBounded formula seeded := by
        apply loopFinalBound.before
            (clauseFoldLoopRuntime_target_append rest.length seeded)
        · exact Nat.le_trans
            (show seeded.checks.length ≤ runtime.checks.length by
              rw [runtimeChecks, List.length_append]
              omega)
            startBound.checksLength
        · intro coordinate member
          apply startBound.checksValues coordinate
          rw [runtimeChecks]
          exact List.mem_append_left [value] member
      have poppedBound : RuntimeDataBounded formula popped := by
        apply seededBound.before_of_checks_append
            (seedClauseResult_target_append popped) []
        simpa [seeded] using seedClauseResult_checks popped
      have first := startBound.descriptor
        blockDescriptor19_mem
        sourceBound
      have compare := slotCompareSteps_le_phase formula .currentGate value
        (Nat.le_of_lt (startBound.checksValues value (by
          rw [checks']
          simp)))
      have block := poppedBound.descriptor
        blockDescriptor20_mem
        sourceBound
      have loopBound :=
        clauseFoldLoopCost_le_phases formula source sourceBound prior
          marker rest seeded seededChecks seededBound loopFinalBound
      have prefixRaw :=
        Nat.add_le_add (Nat.add_le_add first compare) block
      have prefixBound :=
        Nat.le_trans prefixRaw
          (Nat.le_of_eq (three_phase_identity (completionPhase formula)))
      simp only [clauseFoldCost]
      rw [newest]
      dsimp only [seeded] at loopBound ⊢
      calc
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
                (CNFToNANDWorkspace.capacity formula) source runtime
                blockDescriptors[19].primitives +
              slotCompareSteps .currentGate
                (CNFToNANDWorkspace.capacity formula) value +
            TargetEmitterRuntimeProgramBound.programWorkEnvelope
                (CNFToNANDWorkspace.capacity formula) source popped
                blockDescriptors[20].primitives +
            clauseFoldLoopCost
              (CNFToNANDWorkspace.capacity formula) source marker rest
              (seedClauseResult popped) ≤
          3 * completionPhase formula +
            3 * (rest.length + 1) * completionPhase formula := by
          exact Nat.add_le_add prefixBound loopBound
        _ = (3 + 3 * (rest.length + 1)) *
              completionPhase formula := by
          rw [Nat.add_mul]
        _ = 3 * ((rest.length + 1) + 1) *
              completionPhase formula := by
          rw [three_successor_coefficient]
        _ = 3 * ((value :: rest).length + 1) *
              completionPhase formula := by
          simp

private theorem clause_length_le_literal_tokens_length
    (clause : List CNFLiteral) :
    clause.length ≤ (encodeLiteralListTokens clause).length := by
  induction clause with
  | nil =>
      simp [encodeLiteralListTokens]
  | cons literal rest inductionHypothesis =>
      rw [encodeLiteralListTokens, List.length_append]
      simp only [List.length_cons]
      have literalPositive :
          1 ≤ (encodeLiteralTokens literal).length := by
        simp [encodeLiteralTokens]
      omega

private theorem clausePathComponents_le_phases
    (separator literals finishRead finishRestore fold phase
      literalTokens clauseCount clauseTokens : Nat)
    (separatorBound : separator ≤ 2 * phase)
    (literalsBound : literals ≤ 4 * literalTokens * phase)
    (finishBound : finishRead + finishRestore ≤ phase)
    (foldBound : fold ≤ 3 * (clauseCount + 1) * phase)
    (coefficient :
      2 + 4 * literalTokens + 1 + 3 * (clauseCount + 1) ≤
        8 * clauseTokens) :
    separator + literals + finishRead + fold + finishRestore ≤
      8 * clauseTokens * phase := by
  have componentRaw :=
    Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add separatorBound literalsBound)
        finishBound)
      foldBound
  have scaled := Nat.mul_le_mul_right phase coefficient
  calc
    separator + literals + finishRead + fold + finishRestore =
        (separator + literals) + (finishRead + finishRestore) + fold := by
      ac_rfl
    _ ≤
        (2 * phase + 4 * literalTokens * phase) + phase +
          3 * (clauseCount + 1) * phase := componentRaw
    _ =
        (2 + 4 * literalTokens + 1 + 3 * (clauseCount + 1)) *
          phase := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    _ ≤ 8 * clauseTokens * phase := by
      simpa only [Nat.mul_assoc] using scaled

private theorem clausePathRuntime_bounds
    (formula : CNFFormula) (clause : List CNFLiteral)
    (runtime : Runtime)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (clauseRuntime formula.variableCount clause runtime))
    (checksHeadroom :
      runtime.checks.length + clause.length + 1 ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 2)
    (gateBound :
      runtime.registers.currentGate <
        CNFToNANDWorkspace.capacity formula)
    (literalBudget :
      runtime.registers.outputIndex + 2 * clause.length ≤
        runtime.registers.currentGate) :
    let initialized := pushTotalGateResult runtime
    let listed :=
      literalListRuntime formula.variableCount clause initialized
    let coordinates :=
      literalListCoordinates formula.variableCount clause initialized
    let pending := coordinates.reverse
    listed.checks =
        runtime.checks ++ listed.registers.currentGate :: pending.reverse ∧
      RuntimeDataBounded formula initialized ∧
      RuntimeDataBounded formula listed ∧
      RuntimeDataBounded formula
        (clauseFoldRuntime pending.length listed) := by
  let initialized := pushTotalGateResult runtime
  let listed :=
    literalListRuntime formula.variableCount clause initialized
  let coordinates :=
    literalListCoordinates formula.variableCount clause initialized
  let pending := coordinates.reverse
  have coordinatesLength : coordinates.length = clause.length := by
    simpa [coordinates] using
      literalListCoordinates_length formula.variableCount clause initialized
  have initializedChecks :
      initialized.checks =
        runtime.checks ++ [runtime.registers.currentGate] := by
    rfl
  have listedChecks :
      listed.checks =
        runtime.checks ++
          listed.registers.currentGate :: pending.reverse := by
    rw [show pending.reverse = coordinates by simp [pending]]
    rw [literalListRuntime_checks, initializedChecks]
    simp [listed, initialized, coordinates,
      pushTotalGateResult, literalListRuntime_currentGate,
      List.append_assoc]
  have listedLength :
      listed.checks.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 2 := by
    rw [literalListRuntime_checks, initializedChecks,
      List.length_append, List.length_append, coordinatesLength]
    simp only [List.length_singleton]
    omega
  have coordinateValues :
      ∀ coordinate, coordinate ∈ coordinates →
        coordinate < CNFToNANDWorkspace.capacity formula := by
    intro coordinate member
    have belowGate :=
      literalListCoordinates_lt_currentGate formula.variableCount
        clause initialized (by
          simpa [initialized, pushTotalGateResult] using literalBudget)
        coordinate (by simpa [coordinates] using member)
    exact Nat.lt_trans (by
      simpa [initialized, pushTotalGateResult] using belowGate) gateBound
  have listedValues :
      ∀ value, value ∈ listed.checks →
        value < CNFToNANDWorkspace.capacity formula := by
    intro value member
    rw [literalListRuntime_checks, initializedChecks] at member
    rcases List.mem_append.mp member with prefixMember | coordinate
    · rcases List.mem_append.mp prefixMember with old | gateMember
      · exact startBound.checksValues value old
      · have gateEq : value = runtime.registers.currentGate := by
          simpa using gateMember
        simpa [gateEq] using gateBound
    · exact coordinateValues value coordinate
  have pendingLength : pending.length = clause.length := by
    simp [pending, coordinatesLength]
  have foldFinalBound :
      RuntimeDataBounded formula
        (clauseFoldRuntime pending.length listed) := by
    simpa [clauseRuntime, listed, initialized, pendingLength] using finalBound
  have listedBound : RuntimeDataBounded formula listed := by
    apply foldFinalBound.before
        (clauseFoldRuntime_target_append pending.length listed)
    · exact listedLength
    · exact listedValues
  have initializedBound : RuntimeDataBounded formula initialized := by
    apply listedBound.before_of_checks_append
        (literalListRuntime_target_append
          formula.variableCount clause initialized)
        coordinates
    simpa [listed, coordinates] using
      literalListRuntime_checks formula.variableCount clause initialized
  change listed.checks =
      runtime.checks ++ listed.registers.currentGate :: pending.reverse ∧
    RuntimeDataBounded formula initialized ∧
    RuntimeDataBounded formula listed ∧
    RuntimeDataBounded formula
      (clauseFoldRuntime pending.length listed)
  exact ⟨listedChecks, initializedBound, listedBound, foldFinalBound⟩

private theorem clausePathScanBounds
    (formula : CNFFormula) (processed : List CNFToken)
    (clause : List CNFLiteral) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (successor : CNFToken) (successorTail : List CNFToken)
    (separatorTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .sep :: successor :: successorTail)
    (literalTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        (processed ++ [.sep]) ++ encodeLiteralListTokens clause ++
          .finish :: next :: tail)
    (finishTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        ((processed ++ [.sep]) ++ encodeLiteralListTokens clause) ++
          .finish :: next :: tail)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (clauseRuntime formula.variableCount clause runtime))
    (checksHeadroom :
      runtime.checks.length + clause.length + 1 ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 2)
    (gateBound :
      runtime.registers.currentGate <
        CNFToNANDWorkspace.capacity formula)
    (inputBound :
      runtime.registers.inputCount ≤
        CNFToNANDWorkspace.capacity formula)
    (literalBudget :
      runtime.registers.outputIndex + 2 * clause.length ≤
        runtime.registers.currentGate) :
    let initialized := pushTotalGateResult runtime
    let clauseProcessed := processed ++ [.sep]
    let listed :=
      literalListRuntime formula.variableCount clause initialized
    let finishProcessed :=
      clauseProcessed ++ encodeLiteralListTokens clause
    clauseSeparatorCost formula processed successor successorTail runtime ≤
        2 * completionPhase formula ∧
      literalListCost formula clauseProcessed clause .finish
          (next :: tail) initialized ≤
        4 * (encodeLiteralListTokens clause).length *
          completionPhase formula ∧
      directTokenCost formula finishProcessed .finish ≤
        completionPhase formula := by
  let initialized := pushTotalGateResult runtime
  let clauseProcessed := processed ++ [.sep]
  let listed :=
    literalListRuntime formula.variableCount clause initialized
  let coordinates :=
    literalListCoordinates formula.variableCount clause initialized
  let pending := coordinates.reverse
  let finishProcessed :=
    clauseProcessed ++ encodeLiteralListTokens clause
  have runtimeBounds :=
    clausePathRuntime_bounds formula clause runtime startBound finalBound
      checksHeadroom gateBound literalBudget
  change
    listed.checks =
        runtime.checks ++ listed.registers.currentGate :: pending.reverse ∧
      RuntimeDataBounded formula initialized ∧
      RuntimeDataBounded formula listed ∧
      RuntimeDataBounded formula
        (clauseFoldRuntime pending.length listed) at runtimeBounds
  rcases runtimeBounds with
    ⟨_, initializedBound, listedBound, _⟩
  have separatorBound :=
    clauseSeparatorCost_le_two_phases formula processed successor
      successorTail runtime separatorTokens startBound
  have literalsBound :=
    literalListCost_le_phases formula clauseProcessed clause .finish
      (next :: tail) initialized literalTokens
      (by simpa [initialized, pushTotalGateResult] using inputBound)
      initializedBound listedBound
  have finishProcessedBound :=
    processed_length_le_of_tokens formula finishProcessed .finish
      (next :: tail) finishTokens
  have finishBound :=
    directTokenCost_le_phase formula finishProcessed .finish
      finishProcessedBound
  change
    clauseSeparatorCost formula processed successor successorTail runtime ≤
        2 * completionPhase formula ∧
      literalListCost formula clauseProcessed clause .finish
          (next :: tail) initialized ≤
        4 * (encodeLiteralListTokens clause).length *
          completionPhase formula ∧
      directTokenCost formula finishProcessed .finish ≤
        completionPhase formula
  exact ⟨separatorBound, literalsBound, finishBound⟩

private theorem clausePathFoldRuntime_bounds
    (formula : CNFFormula) (clause : List CNFLiteral)
    (runtime : Runtime)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (clauseRuntime formula.variableCount clause runtime))
    (checksHeadroom :
      runtime.checks.length + clause.length + 1 ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 2)
    (gateBound :
      runtime.registers.currentGate <
        CNFToNANDWorkspace.capacity formula)
    (literalBudget :
      runtime.registers.outputIndex + 2 * clause.length ≤
        runtime.registers.currentGate) :
    let initialized := pushTotalGateResult runtime
    let listed :=
      literalListRuntime formula.variableCount clause initialized
    let coordinates :=
      literalListCoordinates formula.variableCount clause initialized
    let pending := coordinates.reverse
    listed.checks =
        runtime.checks ++ listed.registers.currentGate :: pending.reverse ∧
      RuntimeDataBounded formula listed ∧
      RuntimeDataBounded formula
        (clauseFoldRuntime pending.length listed) := by
  let initialized := pushTotalGateResult runtime
  let listed :=
    literalListRuntime formula.variableCount clause initialized
  let coordinates :=
    literalListCoordinates formula.variableCount clause initialized
  let pending := coordinates.reverse
  have runtimeBounds :=
    clausePathRuntime_bounds formula clause runtime startBound finalBound
      checksHeadroom gateBound literalBudget
  change
    listed.checks =
        runtime.checks ++ listed.registers.currentGate :: pending.reverse ∧
      RuntimeDataBounded formula initialized ∧
      RuntimeDataBounded formula listed ∧
      RuntimeDataBounded formula
        (clauseFoldRuntime pending.length listed) at runtimeBounds
  rcases runtimeBounds with
    ⟨listedChecks, _, listedBound, foldFinalBound⟩
  change listed.checks =
      runtime.checks ++ listed.registers.currentGate :: pending.reverse ∧
    RuntimeDataBounded formula listed ∧
    RuntimeDataBounded formula
      (clauseFoldRuntime pending.length listed)
  exact ⟨listedChecks, listedBound, foldFinalBound⟩

private theorem clausePathFinishSource_length
    (formula : CNFFormula) (processed : List CNFToken)
    (clause : List CNFLiteral) (next : CNFToken)
    (tail : List CNFToken)
    (finishTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        ((processed ++ [.sep]) ++ encodeLiteralListTokens clause) ++
          .finish :: next :: tail) :
    let finishProcessed :=
      (processed ++ [.sep]) ++ encodeLiteralListTokens clause
    let finishSource :=
      markedSource (CNFToNANDWorkspace.formulaTokens formula)
        finishProcessed .finish (next :: tail)
    finishSource.length ≤ dataMajorant (encodeCNF formula).length := by
  let finishProcessed :=
    (processed ++ [.sep]) ++ encodeLiteralListTokens clause
  let finishSource :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      finishProcessed .finish (next :: tail)
  change finishSource.length ≤ dataMajorant (encodeCNF formula).length
  simpa [finishSource] using
    markedSource_length_le_dataMajorant formula finishProcessed .finish
      (next :: tail) finishTokens

private theorem clausePathPending_length
    (formula : CNFFormula) (clause : List CNFLiteral)
    (runtime : Runtime) :
    let initialized := pushTotalGateResult runtime
    let coordinates :=
      literalListCoordinates formula.variableCount clause initialized
    let pending := coordinates.reverse
    pending.length = clause.length := by
  let initialized := pushTotalGateResult runtime
  let coordinates :=
    literalListCoordinates formula.variableCount clause initialized
  let pending := coordinates.reverse
  change pending.length = clause.length
  simpa [pending, coordinates] using
    literalListCoordinates_length formula.variableCount clause initialized

private theorem clausePathFoldBound
    (formula : CNFFormula) (processed : List CNFToken)
    (clause : List CNFLiteral) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (finishTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        ((processed ++ [.sep]) ++ encodeLiteralListTokens clause) ++
          .finish :: next :: tail)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (clauseRuntime formula.variableCount clause runtime))
    (checksHeadroom :
      runtime.checks.length + clause.length + 1 ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 2)
    (gateBound :
      runtime.registers.currentGate <
        CNFToNANDWorkspace.capacity formula)
    (literalBudget :
      runtime.registers.outputIndex + 2 * clause.length ≤
        runtime.registers.currentGate) :
    let initialized := pushTotalGateResult runtime
    let clauseProcessed := processed ++ [.sep]
    let listed :=
      literalListRuntime formula.variableCount clause initialized
    let coordinates :=
      literalListCoordinates formula.variableCount clause initialized
    let pending := coordinates.reverse
    let finishProcessed :=
      clauseProcessed ++ encodeLiteralListTokens clause
    let finishSource :=
      markedSource (CNFToNANDWorkspace.formulaTokens formula)
        finishProcessed .finish (next :: tail)
    clauseFoldCost (CNFToNANDWorkspace.capacity formula)
        finishSource listed.registers.currentGate pending listed ≤
      3 * (clause.length + 1) * completionPhase formula := by
  let initialized := pushTotalGateResult runtime
  let clauseProcessed := processed ++ [.sep]
  let listed :=
    literalListRuntime formula.variableCount clause initialized
  let coordinates :=
    literalListCoordinates formula.variableCount clause initialized
  let pending := coordinates.reverse
  let finishProcessed :=
    clauseProcessed ++ encodeLiteralListTokens clause
  let finishSource :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      finishProcessed .finish (next :: tail)
  have foldRuntimeBounds :=
    clausePathFoldRuntime_bounds formula clause runtime startBound finalBound
      checksHeadroom gateBound literalBudget
  change
    listed.checks =
        runtime.checks ++ listed.registers.currentGate :: pending.reverse ∧
      RuntimeDataBounded formula listed ∧
      RuntimeDataBounded formula
        (clauseFoldRuntime pending.length listed) at foldRuntimeBounds
  rcases foldRuntimeBounds with
    ⟨listedChecks, listedBound, foldFinalBound⟩
  have sourceBound :=
    clausePathFinishSource_length formula processed clause next tail
      finishTokens
  change finishSource.length ≤
    dataMajorant (encodeCNF formula).length at sourceBound
  have pendingLength :=
    clausePathPending_length formula clause runtime
  change pending.length = clause.length at pendingLength
  have rawBound :=
    clauseFoldCost_le_phases formula finishSource sourceBound
      runtime.checks listed.registers.currentGate pending listed
      listedChecks listedBound foldFinalBound
  rw [pendingLength] at rawBound
  exact rawBound

private theorem clausePathLocalBounds
    (formula : CNFFormula) (processed : List CNFToken)
    (clause : List CNFLiteral) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (successor : CNFToken) (successorTail : List CNFToken)
    (separatorTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .sep :: successor :: successorTail)
    (literalTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        (processed ++ [.sep]) ++ encodeLiteralListTokens clause ++
          .finish :: next :: tail)
    (finishTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        ((processed ++ [.sep]) ++ encodeLiteralListTokens clause) ++
          .finish :: next :: tail)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (clauseRuntime formula.variableCount clause runtime))
    (checksHeadroom :
      runtime.checks.length + clause.length + 1 ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 2)
    (gateBound :
      runtime.registers.currentGate <
        CNFToNANDWorkspace.capacity formula)
    (inputBound :
      runtime.registers.inputCount ≤
        CNFToNANDWorkspace.capacity formula)
    (literalBudget :
      runtime.registers.outputIndex + 2 * clause.length ≤
        runtime.registers.currentGate) :
    let initialized := pushTotalGateResult runtime
    let clauseProcessed := processed ++ [.sep]
    let listed :=
      literalListRuntime formula.variableCount clause initialized
    let coordinates :=
      literalListCoordinates formula.variableCount clause initialized
    let pending := coordinates.reverse
    let finishProcessed :=
      clauseProcessed ++ encodeLiteralListTokens clause
    let finishSource :=
      markedSource (CNFToNANDWorkspace.formulaTokens formula)
        finishProcessed .finish (next :: tail)
    clauseSeparatorCost formula processed successor successorTail runtime ≤
        2 * completionPhase formula ∧
      literalListCost formula clauseProcessed clause .finish
          (next :: tail) initialized ≤
        4 * (encodeLiteralListTokens clause).length *
          completionPhase formula ∧
      directTokenCost formula finishProcessed .finish ≤
        completionPhase formula ∧
      clauseFoldCost (CNFToNANDWorkspace.capacity formula)
          finishSource listed.registers.currentGate pending listed ≤
        3 * (clause.length + 1) * completionPhase formula := by
  let initialized := pushTotalGateResult runtime
  let clauseProcessed := processed ++ [.sep]
  let listed :=
    literalListRuntime formula.variableCount clause initialized
  let coordinates :=
    literalListCoordinates formula.variableCount clause initialized
  let pending := coordinates.reverse
  let finishProcessed :=
    clauseProcessed ++ encodeLiteralListTokens clause
  let finishSource :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      finishProcessed .finish (next :: tail)
  have scanBounds :=
    clausePathScanBounds formula processed clause next tail runtime
      successor successorTail separatorTokens literalTokens finishTokens
      startBound finalBound checksHeadroom gateBound inputBound literalBudget
  change
    clauseSeparatorCost formula processed successor successorTail runtime ≤
        2 * completionPhase formula ∧
      literalListCost formula clauseProcessed clause .finish
          (next :: tail) initialized ≤
        4 * (encodeLiteralListTokens clause).length *
          completionPhase formula ∧
      directTokenCost formula finishProcessed .finish ≤
        completionPhase formula at scanBounds
  rcases scanBounds with ⟨separatorBound, literalsBound, finishBound⟩
  have foldBound :=
    clausePathFoldBound formula processed clause next tail runtime
      finishTokens startBound finalBound checksHeadroom gateBound literalBudget
  change
    clauseFoldCost (CNFToNANDWorkspace.capacity formula)
        finishSource listed.registers.currentGate pending listed ≤
      3 * (clause.length + 1) * completionPhase formula at foldBound
  change
    clauseSeparatorCost formula processed successor successorTail runtime ≤
        2 * completionPhase formula ∧
      literalListCost formula clauseProcessed clause .finish
          (next :: tail) initialized ≤
        4 * (encodeLiteralListTokens clause).length *
          completionPhase formula ∧
      directTokenCost formula finishProcessed .finish ≤
        completionPhase formula ∧
      clauseFoldCost (CNFToNANDWorkspace.capacity formula)
          finishSource listed.registers.currentGate pending listed ≤
        3 * (clause.length + 1) * completionPhase formula
  exact ⟨separatorBound, literalsBound, finishBound, foldBound⟩

private theorem clausePathUnfoldedCost_le_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (clause : List CNFLiteral) (next : CNFToken)
    (tail : List CNFToken) (runtime : Runtime)
    (successor : CNFToken) (successorTail : List CNFToken)
    (separatorTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .sep :: successor :: successorTail)
    (literalTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        (processed ++ [.sep]) ++ encodeLiteralListTokens clause ++
          .finish :: next :: tail)
    (finishTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        ((processed ++ [.sep]) ++ encodeLiteralListTokens clause) ++
          .finish :: next :: tail)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (clauseRuntime formula.variableCount clause runtime))
    (checksHeadroom :
      runtime.checks.length + clause.length + 1 ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 2)
    (gateBound :
      runtime.registers.currentGate <
        CNFToNANDWorkspace.capacity formula)
    (inputBound :
      runtime.registers.inputCount ≤
        CNFToNANDWorkspace.capacity formula)
    (literalBudget :
      runtime.registers.outputIndex + 2 * clause.length ≤
        runtime.registers.currentGate) :
    let initialized := pushTotalGateResult runtime
    let clauseProcessed := processed ++ [.sep]
    let listed :=
      literalListRuntime formula.variableCount clause initialized
    let coordinates :=
      literalListCoordinates formula.variableCount clause initialized
    let pending := coordinates.reverse
    let finishProcessed :=
      clauseProcessed ++ encodeLiteralListTokens clause
    let finishSource :=
      markedSource (CNFToNANDWorkspace.formulaTokens formula)
        finishProcessed .finish (next :: tail)
    clauseSeparatorCost formula processed successor successorTail runtime +
          literalListCost formula clauseProcessed clause .finish
            (next :: tail) initialized +
        CNFToNANDControllerCountTrace.tokenReadInstallSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          finishProcessed .finish +
      clauseFoldCost (CNFToNANDWorkspace.capacity formula)
        finishSource listed.registers.currentGate pending listed +
      CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
        (CNFToNANDWorkspace.formulaTokens formula)
        finishProcessed .finish ≤
      8 * (encodeClauseTokens clause).length * completionPhase formula := by
  let initialized := pushTotalGateResult runtime
  let clauseProcessed := processed ++ [.sep]
  let listed :=
    literalListRuntime formula.variableCount clause initialized
  let coordinates :=
    literalListCoordinates formula.variableCount clause initialized
  let pending := coordinates.reverse
  let finishProcessed :=
    clauseProcessed ++ encodeLiteralListTokens clause
  let finishSource :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      finishProcessed .finish (next :: tail)
  have localBounds :=
    clausePathLocalBounds formula processed clause next tail runtime
      successor successorTail separatorTokens literalTokens finishTokens
      startBound finalBound checksHeadroom gateBound inputBound literalBudget
  change
    clauseSeparatorCost formula processed successor successorTail runtime ≤
        2 * completionPhase formula ∧
      literalListCost formula clauseProcessed clause .finish
          (next :: tail) initialized ≤
        4 * (encodeLiteralListTokens clause).length *
          completionPhase formula ∧
      directTokenCost formula finishProcessed .finish ≤
        completionPhase formula ∧
      clauseFoldCost (CNFToNANDWorkspace.capacity formula)
          finishSource listed.registers.currentGate pending listed ≤
        3 * (clause.length + 1) * completionPhase formula at localBounds
  rcases localBounds with
    ⟨separatorBound, literalsBound, finishBound, foldBound⟩
  have clauseTokensLength :
      (encodeClauseTokens clause).length =
        (encodeLiteralListTokens clause).length + 2 := by
    simp [encodeClauseTokens]
  have clauseLength := clause_length_le_literal_tokens_length clause
  have coefficient :
      2 + 4 * (encodeLiteralListTokens clause).length + 1 +
          3 * (clause.length + 1) ≤
        8 * (encodeClauseTokens clause).length := by
    rw [clauseTokensLength]
    exact clausePath_coefficient
      (encodeLiteralListTokens clause).length clause.length clauseLength
  unfold directTokenCost at finishBound
  change
    clauseSeparatorCost formula processed successor successorTail runtime +
          literalListCost formula clauseProcessed clause .finish
            (next :: tail) initialized +
        CNFToNANDControllerCountTrace.tokenReadInstallSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          finishProcessed .finish +
      clauseFoldCost (CNFToNANDWorkspace.capacity formula)
        finishSource listed.registers.currentGate pending listed +
      CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
        (CNFToNANDWorkspace.formulaTokens formula)
        finishProcessed .finish ≤
      8 * (encodeClauseTokens clause).length * completionPhase formula
  exact
    clausePathComponents_le_phases
      (clauseSeparatorCost formula processed successor successorTail runtime)
      (literalListCost formula clauseProcessed clause .finish
        (next :: tail) initialized)
      (CNFToNANDControllerCountTrace.tokenReadInstallSteps
        (CNFToNANDWorkspace.formulaTokens formula) finishProcessed .finish)
      (CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
        (CNFToNANDWorkspace.formulaTokens formula) finishProcessed .finish)
      (clauseFoldCost (CNFToNANDWorkspace.capacity formula)
        finishSource listed.registers.currentGate pending listed)
      (completionPhase formula)
      (encodeLiteralListTokens clause).length clause.length
      (encodeClauseTokens clause).length separatorBound literalsBound
      finishBound foldBound coefficient

private theorem clausePathCost_le_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (state : GrammarState) (clause : List CNFLiteral)
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeClauseTokens clause ++ next :: tail)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (clauseRuntime formula.variableCount clause runtime))
    (checksHeadroom :
      runtime.checks.length + clause.length + 1 ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 2)
    (gateBound :
      runtime.registers.currentGate <
        CNFToNANDWorkspace.capacity formula)
    (inputBound :
      runtime.registers.inputCount ≤
        CNFToNANDWorkspace.capacity formula)
    (literalBudget :
      runtime.registers.outputIndex + 2 * clause.length ≤
        runtime.registers.currentGate) :
    clausePathCost formula processed state clause next tail runtime ≤
      8 * (encodeClauseTokens clause).length *
        completionPhase formula := by
  let initialized := pushTotalGateResult runtime
  let clauseProcessed := processed ++ [.sep]
  let listed :=
    literalListRuntime formula.variableCount clause initialized
  let coordinates :=
    literalListCoordinates formula.variableCount clause initialized
  let pending := coordinates.reverse
  let finishProcessed :=
    clauseProcessed ++ encodeLiteralListTokens clause
  let finishSource :=
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
      finishProcessed .finish (next :: tail)
  let remainder :=
    encodeLiteralListTokens clause ++ .finish :: next :: tail
  have remainderNonempty : remainder ≠ [] := by
    simp [remainder]
  obtain ⟨successor, successorTail, remainderEq⟩ :=
    List.exists_cons_of_ne_nil remainderNonempty
  have separatorTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ .sep :: successor :: successorTail := by
    simpa [encodeClauseTokens, remainder, remainderEq,
      List.append_assoc] using tokens
  have literalTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        clauseProcessed ++ encodeLiteralListTokens clause ++
          .finish :: next :: tail := by
    simpa [encodeClauseTokens, clauseProcessed,
      List.append_assoc] using tokens
  have finishTokens :
      CNFToNANDWorkspace.formulaTokens formula =
        finishProcessed ++ .finish :: next :: tail := by
    simpa [finishProcessed, List.append_assoc] using literalTokens
  have unfoldedBound :=
    clausePathUnfoldedCost_le_phases formula processed clause next tail
      runtime successor successorTail separatorTokens literalTokens
      finishTokens startBound finalBound checksHeadroom gateBound inputBound
      literalBudget
  change
    clauseSeparatorCost formula processed successor successorTail runtime +
          literalListCost formula clauseProcessed clause .finish
            (next :: tail) initialized +
        CNFToNANDControllerCountTrace.tokenReadInstallSteps
          (CNFToNANDWorkspace.formulaTokens formula)
          finishProcessed .finish +
      clauseFoldCost (CNFToNANDWorkspace.capacity formula)
        finishSource listed.registers.currentGate pending listed +
      CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
        (CNFToNANDWorkspace.formulaTokens formula)
        finishProcessed .finish ≤
      8 * (encodeClauseTokens clause).length * completionPhase formula at unfoldedBound
  unfold clausePathCost
  dsimp only
  rw [show remainder.headD .f = successor by
    rw [remainderEq]
    rfl]
  rw [show remainder.tail = successorTail by
    rw [remainderEq]
    rfl]
  rw [show pushTotalGateResult runtime = initialized by rfl]
  rw [show processed ++ [.sep] = clauseProcessed by rfl]
  rw [show
    literalListRuntime formula.variableCount clause initialized =
      listed by rfl]
  rw [show
    literalListCoordinates formula.variableCount clause initialized =
      coordinates by rfl]
  rw [show
    clauseProcessed ++ encodeLiteralListTokens clause =
      finishProcessed by rfl]
  rw [show
    markedSource (CNFToNANDWorkspace.formulaTokens formula)
        finishProcessed .finish (next :: tail) = finishSource by rfl]
  exact unfoldedBound

private theorem clauseListPathCost_le_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (state : GrammarState) (clauses : List (List CNFLiteral))
    (next : CNFToken) (tail : List CNFToken)
    (runtime : Runtime)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ encodeClauseListTokens clauses ++ next :: tail)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (clauseListRuntime formula.variableCount clauses runtime))
    (checksTokenHeadroom :
      runtime.checks.length +
          (encodeClauseListTokens clauses).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 1)
    (gateBound :
      runtime.registers.currentGate <
        CNFToNANDWorkspace.capacity formula)
    (inputBound :
      runtime.registers.inputCount ≤
        CNFToNANDWorkspace.capacity formula)
    (gateBudget :
      runtime.registers.outputIndex +
          clauseListGateCount formula.variableCount clauses ≤
        runtime.registers.currentGate) :
    clauseListPathCost formula processed state clauses next tail runtime ≤
      8 * (encodeClauseListTokens clauses).length *
        completionPhase formula := by
  induction clauses generalizing processed state runtime with
  | nil =>
      simp [clauseListPathCost, encodeClauseListTokens]
  | cons clause rest inductionHypothesis =>
      let remainder :=
        encodeClauseListTokens rest ++ next :: tail
      have remainderNonempty : remainder ≠ [] := by
        simp [remainder]
      obtain ⟨successor, successorTail, remainderEq⟩ :=
        List.exists_cons_of_ne_nil remainderNonempty
      let nextRuntime :=
        clauseRuntime formula.variableCount clause runtime
      have clauseTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            processed ++ encodeClauseTokens clause ++
              successor :: successorTail := by
        rw [encodeClauseListTokens] at tokens
        simpa [remainder, remainderEq, List.append_assoc] using tokens
      have recursiveTokens :
          CNFToNANDWorkspace.formulaTokens formula =
            (processed ++ encodeClauseTokens clause) ++
              encodeClauseListTokens rest ++ next :: tail := by
        rw [encodeClauseListTokens] at tokens
        simpa [List.append_assoc] using tokens
      have tailFinalBound :
          RuntimeDataBounded formula
            (clauseListRuntime formula.variableCount rest nextRuntime) := by
        simpa [clauseListRuntime, nextRuntime] using finalBound
      have nextRuntimeBound : RuntimeDataBounded formula nextRuntime := by
        apply tailFinalBound.before_of_checks_append
            (clauseListRuntime_target_append
              formula.variableCount rest nextRuntime)
            (clauseListCoordinates formula.variableCount rest nextRuntime)
        exact clauseListRuntime_checks
          formula.variableCount rest nextRuntime
      have clauseLength := clause_length_le_literal_tokens_length clause
      have clauseChecksHeadroom :
          runtime.checks.length + clause.length + 1 ≤
            (CNFToNANDWorkspace.formulaTokens formula).length + 2 := by
        have clauseTokenLength :
            clause.length + 1 ≤ (encodeClauseTokens clause).length := by
          simp [encodeClauseTokens]
          omega
        rw [encodeClauseListTokens, List.length_append] at checksTokenHeadroom
        omega
      have clauseBudget :
          runtime.registers.outputIndex + 2 * clause.length ≤
            runtime.registers.currentGate := by
        simp only [clauseListGateCount, clauseGateCount] at gateBudget
        omega
      have firstBound :=
        clausePathCost_le_phases formula processed state clause successor
          successorTail runtime clauseTokens startBound nextRuntimeBound
          clauseChecksHeadroom gateBound inputBound clauseBudget
      have nextChecks :
          nextRuntime.checks.length = runtime.checks.length + 1 := by
        rw [show
          nextRuntime.checks = runtime.checks ++
              [clauseCoordinate formula.variableCount clause runtime] by
            simpa [nextRuntime] using
              clauseRuntime_checks formula.variableCount clause runtime]
        simp
      have nextHeadroom :
          nextRuntime.checks.length +
              (encodeClauseListTokens rest).length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length + 1 := by
        rw [encodeClauseListTokens, List.length_append] at checksTokenHeadroom
        rw [nextChecks]
        have clauseNonempty : 1 ≤ (encodeClauseTokens clause).length := by
          simp [encodeClauseTokens]
        omega
      have nextGateBound :
          nextRuntime.registers.currentGate <
            CNFToNANDWorkspace.capacity formula := by
        simpa [nextRuntime, clauseRuntime_currentGate] using gateBound
      have nextInputBound :
          nextRuntime.registers.inputCount ≤
            CNFToNANDWorkspace.capacity formula := by
        simpa [nextRuntime, clauseRuntime_inputCount] using inputBound
      have nextGateBudget :
          nextRuntime.registers.outputIndex +
              clauseListGateCount formula.variableCount rest ≤
            nextRuntime.registers.currentGate := by
        dsimp only [nextRuntime]
        rw [clauseRuntime_outputIndex, clauseRuntime_currentGate]
        simp only [clauseListGateCount] at gateBudget
        omega
      have restBound :=
        inductionHypothesis
          (processed ++ encodeClauseTokens clause) .clausesNonempty
          nextRuntime recursiveTokens nextRuntimeBound tailFinalBound
          nextHeadroom nextGateBound nextInputBound nextGateBudget
      simp only [clauseListPathCost]
      rw [show remainder.headD .f = successor by
        rw [remainderEq]
        rfl]
      rw [show remainder.tail = successorTail by
        rw [remainderEq]
        rfl]
      change
        clausePathCost formula processed state clause successor
              successorTail runtime +
            clauseListPathCost formula
              (processed ++ encodeClauseTokens clause)
              .clausesNonempty rest next tail nextRuntime ≤
          8 * (encodeClauseListTokens (clause :: rest)).length *
            completionPhase formula
      calc
        clausePathCost formula processed state clause successor
                successorTail runtime +
              clauseListPathCost formula
                (processed ++ encodeClauseTokens clause)
                .clausesNonempty rest next tail nextRuntime ≤
            8 * (encodeClauseTokens clause).length *
                completionPhase formula +
              8 * (encodeClauseListTokens rest).length *
                completionPhase formula :=
          Nat.add_le_add firstBound restBound
        _ =
            (8 * (encodeClauseTokens clause).length +
                8 * (encodeClauseListTokens rest).length) *
              completionPhase formula := by
          rw [Nat.add_mul]
        _ =
            8 * ((encodeClauseTokens clause).length +
                (encodeClauseListTokens rest).length) *
              completionPhase formula := by
          rw [Nat.mul_add]
        _ =
            8 * (encodeClauseListTokens (clause :: rest)).length *
              completionPhase formula := by
          simp [encodeClauseListTokens]

private theorem formulaSeedTailCost_le_two_phases
    (formula : CNFFormula) (source : List WorkSymbol)
    (sourceBound :
      source.length ≤ dataMajorant (encodeCNF formula).length)
    (runtime : Runtime)
    (scratchBound :
      runtime.scratch ≤ CNFToNANDWorkspace.capacity formula)
    (bounded : RuntimeDataBounded formula runtime) :
    formulaSeedTailCost
        (CNFToNANDWorkspace.capacity formula) source runtime ≤
      2 * completionPhase formula := by
  have compare := slotCompareSteps_le_phase formula .currentGate
    runtime.scratch scratchBound
  cases sourceCase : runtimeClauseSource runtime with
  | constantFalse =>
      have block := bounded.descriptor
        blockDescriptor26_mem
        sourceBound
      unfold formulaSeedTailCost
      rw [sourceCase]
      simpa only [two_phase_identity] using
        Nat.add_le_add compare block
  | gateScratch =>
      have block := bounded.descriptor
        blockDescriptor27_mem
        sourceBound
      unfold formulaSeedTailCost
      rw [sourceCase]
      simpa only [two_phase_identity] using
        Nat.add_le_add compare block

private theorem formulaExtendTailCost_le_two_phases
    (formula : CNFFormula) (source : List WorkSymbol)
    (sourceBound :
      source.length ≤ dataMajorant (encodeCNF formula).length)
    (runtime : Runtime)
    (scratchBound :
      runtime.scratch ≤ CNFToNANDWorkspace.capacity formula)
    (bounded : RuntimeDataBounded formula runtime) :
    formulaExtendTailCost
        (CNFToNANDWorkspace.capacity formula) source runtime ≤
      2 * completionPhase formula := by
  have compare := slotCompareSteps_le_phase formula .currentGate
    runtime.scratch scratchBound
  cases sourceCase : runtimeClauseSource runtime with
  | constantFalse =>
      have block := bounded.descriptor
        blockDescriptor29_mem
        sourceBound
      unfold formulaExtendTailCost
      rw [sourceCase]
      simpa only [two_phase_identity] using
        Nat.add_le_add compare block
  | gateScratch =>
      have block := bounded.descriptor
        blockDescriptor30_mem
        sourceBound
      unfold formulaExtendTailCost
      rw [sourceCase]
      simpa only [two_phase_identity] using
        Nat.add_le_add compare block

private theorem formulaFoldLoopCost_le_phases
    (formula : CNFFormula) (source : List WorkSymbol)
    (sourceBound :
      source.length ≤ dataMajorant (encodeCNF formula).length)
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks =
        prior ++ marker :: pending.reverse)
    (carrierBound :
      runtime.registers.carrierWidth <
        CNFToNANDWorkspace.capacity formula)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (formulaFoldLoopRuntime pending.length runtime)) :
    formulaFoldLoopCost
        (CNFToNANDWorkspace.capacity formula) source pending runtime ≤
      (4 * pending.length + 2) * completionPhase formula := by
  induction pending generalizing runtime with
  | nil =>
      have block := startBound.descriptor
        blockDescriptor28_mem
        sourceBound
      have compare := slotCompareSteps_le_phase formula .carrierWidth
        runtime.registers.carrierWidth (Nat.le_of_lt carrierBound)
      simp only [formulaFoldLoopCost]
      simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add,
          two_phase_identity] using
        Nat.add_le_add block compare
  | cons value rest inductionHypothesis =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have newest : popNewestResult runtime = popped :=
        popNewestResult_of_checks runtime
          (prior ++ marker :: rest.reverse) value checks'
      let extended :=
        extendFormulaResult (runtimeClauseSource popped) popped
      have extendedChecks :
          extended.checks = prior ++ marker :: rest.reverse := by
        dsimp only [extended]
        rw [extendFormulaResult_checks]
        simp [popped, popCoordinateResult]
      have runtimeChecks : runtime.checks = extended.checks ++ [value] := by
        rw [checks', extendedChecks]
      have tailFinalBound :
          RuntimeDataBounded formula
            (formulaFoldLoopRuntime rest.length extended) := by
        simpa [formulaFoldLoopRuntime, newest, extended] using finalBound
      have extendedBound : RuntimeDataBounded formula extended := by
        apply tailFinalBound.before
            (formulaFoldLoopRuntime_target_append rest.length extended)
        · exact Nat.le_trans
            (show extended.checks.length ≤ runtime.checks.length by
              rw [runtimeChecks, List.length_append]
              omega)
            startBound.checksLength
        · intro coordinate member
          apply startBound.checksValues coordinate
          rw [runtimeChecks]
          exact List.mem_append_left [value] member
      have poppedBound : RuntimeDataBounded formula popped := by
        apply extendedBound.before_of_checks_append
            (extendFormulaResult_target_append
              (runtimeClauseSource popped) popped) []
        simpa [extended] using
          extendFormulaResult_checks (runtimeClauseSource popped) popped
      have poppedScratch : popped.scratch = value := by
        simp [popped, popCoordinateResult]
      have valueBound :
          value ≤ CNFToNANDWorkspace.capacity formula := by
        exact Nat.le_of_lt (startBound.checksValues value (by
          rw [checks']
          simp))
      have block := startBound.descriptor
        blockDescriptor28_mem
        sourceBound
      have compare := slotCompareSteps_le_phase formula .carrierWidth
        popped.scratch (by simpa [poppedScratch] using valueBound)
      have extendTail :=
        formulaExtendTailCost_le_two_phases formula source sourceBound
          popped (by simpa [poppedScratch] using valueBound) poppedBound
      have extendedCarrier :
          extended.registers.carrierWidth <
            CNFToNANDWorkspace.capacity formula := by
        dsimp only [extended]
        rw [extendFormulaResult_carrierWidth]
        simpa [popped, popCoordinateResult] using carrierBound
      have restBound :=
        inductionHypothesis extended extendedChecks extendedCarrier
          extendedBound tailFinalBound
      have prefixRaw :
          TargetEmitterRuntimeProgramBound.programWorkEnvelope
                  (CNFToNANDWorkspace.capacity formula) source runtime
                  blockDescriptors[28].primitives +
                slotCompareSteps .carrierWidth
                  (CNFToNANDWorkspace.capacity formula) popped.scratch +
              formulaExtendTailCost
                (CNFToNANDWorkspace.capacity formula) source popped ≤
            completionPhase formula + completionPhase formula +
              2 * completionPhase formula := by
        exact Nat.add_le_add (Nat.add_le_add block compare) extendTail
      have prefixBound :
          TargetEmitterRuntimeProgramBound.programWorkEnvelope
                  (CNFToNANDWorkspace.capacity formula) source runtime
                  blockDescriptors[28].primitives +
                slotCompareSteps .carrierWidth
                  (CNFToNANDWorkspace.capacity formula) popped.scratch +
              formulaExtendTailCost
                (CNFToNANDWorkspace.capacity formula) source popped ≤
            4 * completionPhase formula := by
        calc
          _ ≤ completionPhase formula + completionPhase formula +
                2 * completionPhase formula := prefixRaw
          _ = 4 * completionPhase formula :=
            four_phase_identity (completionPhase formula)
      simp only [formulaFoldLoopCost]
      rw [newest]
      dsimp only [extended] at restBound ⊢
      calc
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
                (CNFToNANDWorkspace.capacity formula) source runtime
                blockDescriptors[28].primitives +
              slotCompareSteps .carrierWidth
                (CNFToNANDWorkspace.capacity formula) popped.scratch +
            formulaExtendTailCost
              (CNFToNANDWorkspace.capacity formula) source popped +
            formulaFoldLoopCost
              (CNFToNANDWorkspace.capacity formula) source rest
              (extendFormulaResult (runtimeClauseSource popped) popped) ≤
          4 * completionPhase formula +
            (4 * rest.length + 2) * completionPhase formula := by
          exact Nat.add_le_add prefixBound restBound
        _ = (4 + (4 * rest.length + 2)) *
              completionPhase formula := by
          exact
            (Nat.add_mul 4 (4 * rest.length + 2)
              (completionPhase formula)).symm
        _ = (4 * (rest.length + 1) + 2) *
              completionPhase formula := by
          rw [formulaLoop_successor_coefficient]
        _ = (4 * (value :: rest).length + 2) *
              completionPhase formula := by
          simp

private theorem formulaFoldCost_le_phases
    (formula : CNFFormula) (source : List WorkSymbol)
    (sourceBound :
      source.length ≤ dataMajorant (encodeCNF formula).length)
    (prior : List Nat) (marker : Nat)
    (pending : List Nat) (runtime : Runtime)
    (checks :
      runtime.checks =
        prior ++ marker :: pending.reverse)
    (carrierBound :
      runtime.registers.carrierWidth <
        CNFToNANDWorkspace.capacity formula)
    (startBound : RuntimeDataBounded formula runtime)
    (finalBound :
      RuntimeDataBounded formula
        (formulaFoldRuntime pending.length runtime)) :
    formulaFoldCost
        (CNFToNANDWorkspace.capacity formula) source pending runtime ≤
      (4 * pending.length + 3) * completionPhase formula := by
  cases pending with
  | nil =>
      have checks' : runtime.checks = prior ++ [marker] := by
        simpa using checks
      let popped := popCoordinateResult runtime prior marker
      have newest : popNewestResult runtime = popped :=
        popNewestResult_of_checks runtime prior marker checks'
      have emptyBound :
          RuntimeDataBounded formula (emptyFormulaResult popped) := by
        simpa [formulaFoldRuntime, newest, popped] using finalBound
      have poppedBound : RuntimeDataBounded formula popped := by
        apply emptyBound.before_of_checks_append
            (emptyFormulaResult_target_append popped) []
        simp [emptyFormulaResult, emitGateResult, emitSourceResult]
      have first := startBound.descriptor
        blockDescriptor25_mem
        sourceBound
      have compare := slotCompareSteps_le_phase formula .carrierWidth
        runtime.registers.carrierWidth (Nat.le_of_lt carrierBound)
      have last := poppedBound.descriptor
        blockDescriptor31_mem
        sourceBound
      simp only [formulaFoldCost]
      rw [newest]
      calc
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
                (CNFToNANDWorkspace.capacity formula) source runtime
                blockDescriptors[25].primitives +
              slotCompareSteps .carrierWidth
                (CNFToNANDWorkspace.capacity formula)
                runtime.registers.carrierWidth +
            TargetEmitterRuntimeProgramBound.programWorkEnvelope
              (CNFToNANDWorkspace.capacity formula) source popped
              blockDescriptors[31].primitives ≤
            completionPhase formula + completionPhase formula +
              completionPhase formula :=
          Nat.add_le_add (Nat.add_le_add first compare) last
        _ = 3 * completionPhase formula :=
          three_phase_identity (completionPhase formula)
  | cons value rest =>
      have checks' :
          runtime.checks =
            (prior ++ marker :: rest.reverse) ++ [value] := by
        simpa [List.reverse_cons, List.append_assoc] using checks
      let popped :=
        popCoordinateResult runtime
          (prior ++ marker :: rest.reverse) value
      have newest : popNewestResult runtime = popped :=
        popNewestResult_of_checks runtime
          (prior ++ marker :: rest.reverse) value checks'
      let seeded :=
        seedFormulaResult (runtimeClauseSource popped) popped
      have seededChecks :
          seeded.checks = prior ++ marker :: rest.reverse := by
        dsimp only [seeded]
        rw [seedFormulaResult_checks]
        simp [popped, popCoordinateResult]
      have runtimeChecks : runtime.checks = seeded.checks ++ [value] := by
        rw [checks', seededChecks]
      have loopFinalBound :
          RuntimeDataBounded formula
            (formulaFoldLoopRuntime rest.length seeded) := by
        simpa [formulaFoldRuntime, newest, seeded] using finalBound
      have seededBound : RuntimeDataBounded formula seeded := by
        apply loopFinalBound.before
            (formulaFoldLoopRuntime_target_append rest.length seeded)
        · exact Nat.le_trans
            (show seeded.checks.length ≤ runtime.checks.length by
              rw [runtimeChecks, List.length_append]
              omega)
            startBound.checksLength
        · intro coordinate member
          apply startBound.checksValues coordinate
          rw [runtimeChecks]
          exact List.mem_append_left [value] member
      have poppedBound : RuntimeDataBounded formula popped := by
        apply seededBound.before_of_checks_append
            (seedFormulaResult_target_append
              (runtimeClauseSource popped) popped) []
        simpa [seeded] using
          seedFormulaResult_checks (runtimeClauseSource popped) popped
      have poppedScratch : popped.scratch = value := by
        simp [popped, popCoordinateResult]
      have valueBound :
          value ≤ CNFToNANDWorkspace.capacity formula :=
        Nat.le_of_lt (startBound.checksValues value (by
          rw [checks']
          simp))
      have first := startBound.descriptor
        blockDescriptor25_mem
        sourceBound
      have compare := slotCompareSteps_le_phase formula .carrierWidth
        popped.scratch (by simpa [poppedScratch] using valueBound)
      have seedTail :=
        formulaSeedTailCost_le_two_phases formula source sourceBound
          popped (by simpa [poppedScratch] using valueBound) poppedBound
      have seededCarrier :
          seeded.registers.carrierWidth <
            CNFToNANDWorkspace.capacity formula := by
        dsimp only [seeded]
        rw [seedFormulaResult_carrierWidth]
        simpa [popped, popCoordinateResult] using carrierBound
      have loopBound :=
        formulaFoldLoopCost_le_phases formula source sourceBound prior
          marker rest seeded seededChecks seededCarrier seededBound
          loopFinalBound
      have prefixRaw :
          TargetEmitterRuntimeProgramBound.programWorkEnvelope
                  (CNFToNANDWorkspace.capacity formula) source runtime
                  blockDescriptors[25].primitives +
                slotCompareSteps .carrierWidth
                  (CNFToNANDWorkspace.capacity formula) popped.scratch +
              formulaSeedTailCost
                (CNFToNANDWorkspace.capacity formula) source popped ≤
            completionPhase formula + completionPhase formula +
              2 * completionPhase formula := by
        exact Nat.add_le_add (Nat.add_le_add first compare) seedTail
      have prefixBound :
          TargetEmitterRuntimeProgramBound.programWorkEnvelope
                  (CNFToNANDWorkspace.capacity formula) source runtime
                  blockDescriptors[25].primitives +
                slotCompareSteps .carrierWidth
                  (CNFToNANDWorkspace.capacity formula) popped.scratch +
              formulaSeedTailCost
                (CNFToNANDWorkspace.capacity formula) source popped ≤
            4 * completionPhase formula := by
        calc
          _ ≤ completionPhase formula + completionPhase formula +
                2 * completionPhase formula := prefixRaw
          _ = 4 * completionPhase formula :=
            four_phase_identity (completionPhase formula)
      simp only [formulaFoldCost]
      rw [newest]
      dsimp only [seeded] at loopBound ⊢
      have coefficient := formulaFold_successor_coefficient rest.length
      have scaled :=
        Nat.mul_le_mul_right (completionPhase formula) coefficient
      calc
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
                (CNFToNANDWorkspace.capacity formula) source runtime
                blockDescriptors[25].primitives +
              slotCompareSteps .carrierWidth
                (CNFToNANDWorkspace.capacity formula) popped.scratch +
            formulaSeedTailCost
              (CNFToNANDWorkspace.capacity formula) source popped +
            formulaFoldLoopCost
              (CNFToNANDWorkspace.capacity formula) source rest
              (seedFormulaResult (runtimeClauseSource popped) popped) ≤
          4 * completionPhase formula +
            (4 * rest.length + 2) * completionPhase formula := by
          exact Nat.add_le_add prefixBound loopBound
        _ = (4 + (4 * rest.length + 2)) *
              completionPhase formula := by
          exact
            (Nat.add_mul 4 (4 * rest.length + 2)
              (completionPhase formula)).symm
        _ ≤ (4 * (rest.length + 1) + 3) *
              completionPhase formula := by
          simpa only [Nat.mul_assoc] using scaled
        _ = (4 * (value :: rest).length + 3) *
              completionPhase formula := by
          simp

private theorem emitWidthCost_le_phases
    (formula : CNFFormula) :
    ∀ (count : Nat) (processed : List CNFToken),
      processed.length + (count + 1) ≤
          (CNFToNANDWorkspace.formulaTokens formula).length →
      emitWidthCost formula count processed ≤
        (count + 1) * completionPhase formula
  | 0, processed, headroom => by
      have processedBound :
          processed.length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        omega
      have direct :=
        directTokenCost_le_phase formula processed .f processedBound
      simpa [emitWidthCost, directTokenCost] using direct
  | count + 1, processed, headroom => by
      have processedBound :
          processed.length ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        omega
      have direct :=
        directTokenCost_le_phase formula processed CNFToken.t processedBound
      have tailHeadroom :
          (processed ++ [CNFToken.t]).length + (count + 1) ≤
            (CNFToNANDWorkspace.formulaTokens formula).length := by
        simp only [List.length_append, List.length_singleton]
        omega
      have tailBound :=
        emitWidthCost_le_phases formula count (processed ++ [CNFToken.t])
          tailHeadroom
      simp only [emitWidthCost]
      unfold directTokenCost at direct
      calc
        CNFToNANDControllerCountTrace.tokenReadInstallSteps
                (CNFToNANDWorkspace.formulaTokens formula) processed CNFToken.t +
              CNFToNANDControllerCountTrace.tokenRestoreAdvanceSteps
                (CNFToNANDWorkspace.formulaTokens formula) processed CNFToken.t +
            emitWidthCost formula count (processed ++ [CNFToken.t]) ≤
          completionPhase formula +
            (count + 1) * completionPhase formula :=
          Nat.add_le_add direct tailBound
        _ = (1 + (count + 1)) * completionPhase formula := by
          simpa only [Nat.one_mul] using
            (Nat.add_mul 1 (count + 1)
              (completionPhase formula)).symm
        _ = ((count + 1) + 1) * completionPhase formula := by
          rw [Nat.add_comm 1 (count + 1)]

private theorem endAndInstallCost_le_four_phases
    (formula : CNFFormula) (processed : List CNFToken)
    (tokens :
      CNFToNANDWorkspace.formulaTokens formula =
        processed ++ [.finish]) :
    endAndInstallCost formula processed ≤
      4 * completionPhase formula := by
  have processedBound :=
    processed_length_le_of_tokens formula processed .finish [] tokens
  have finishBound :=
    directTokenCost_le_phase formula processed .finish processedBound
  have endBound :=
    smallSteps_le_phase formula
      CNFToNANDControllerCountTrace.programEndSteps (by decide)
  have rewindBound := emitRewindSteps_le_phase formula
  have installBound :=
    smallSteps_le_phase formula emitInstallVersionSteps (by decide)
  have combined :=
    Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add finishBound endBound)
        rewindBound)
      installBound
  unfold endAndInstallCost emitFinishCost
  unfold directTokenCost at combined
  simpa only [four_single_phase_identity] using combined

private theorem clauseCount_le_clauseTokensLength
    (clauses : List (List CNFLiteral)) :
    clauses.length ≤ (encodeClauseListTokens clauses).length := by
  induction clauses with
  | nil =>
      simp [encodeClauseListTokens]
  | cons clause rest inductionHypothesis =>
      rw [encodeClauseListTokens, List.length_append]
      simp only [List.length_cons]
      have clausePositive : 1 ≤ (encodeClauseTokens clause).length := by
        simp [encodeClauseTokens]
      omega

private theorem emitInitialRuntime_dataBounded
    (formula : CNFFormula) :
    RuntimeDataBounded formula (emitInitialRuntime formula) := by
  refine ⟨completedRuntime_target_append formula, ?_, ?_⟩
  · simp [emitInitialRuntime]
  · intro value member
    simp [emitInitialRuntime] at member
    subst value
    exact formulaStackMarker_lt_capacity formula

private theorem clauseListRuntime_dataBounded
    (formula : CNFFormula) :
    RuntimeDataBounded formula
      (clauseListRuntime formula.variableCount formula.clauses
        (emitInitialRuntime formula)) := by
  let initial := emitInitialRuntime formula
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses initial
  let coordinates :=
    clauseListCoordinates formula.variableCount formula.clauses initial
  have foldAppend :
      TargetAppend clauses
        (formulaFoldRuntime formula.clauses.length clauses) :=
    formulaFoldRuntime_target_append formula.clauses.length clauses
  have suffixAppend :
      TargetAppend
        (formulaFoldRuntime formula.clauses.length clauses)
        (circuitSuffixResult
          (formulaFoldRuntime formula.clauses.length clauses)) :=
    circuitSuffixResult_target_append _
  have target : TargetAppend clauses (completedRuntime formula) := by
    simpa [completedRuntime, formulaRuntime, clauses, initial] using
      targetAppend_trans foldAppend suffixAppend
  have checks : clauses.checks = initial.checks ++ coordinates := by
    simpa [clauses, coordinates] using
      clauseListRuntime_checks formula.variableCount formula.clauses initial
  have coordinatesLength : coordinates.length = formula.clauses.length := by
    simpa [coordinates] using
      clauseListCoordinates_length formula.variableCount formula.clauses initial
  have clauseCountBound :=
    clauseCount_le_clauseTokensLength formula.clauses
  have checksLength :
      clauses.checks.length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 2 := by
    rw [checks, List.length_append, coordinatesLength]
    simp [initial, emitInitialRuntime,
      CNFToNANDWorkspace.formulaTokens, encodeFormulaTokens,
      encodeCNFTokens]
    omega
  have initialBound := emitInitialRuntime_dataBounded formula
  have gateBudget :
      initial.registers.outputIndex +
          clauseListGateCount formula.variableCount formula.clauses ≤
        initial.registers.currentGate := by
    change
      0 + clauseListGateCount formula.variableCount formula.clauses ≤
        CNFToNANDWorkspace.compilerGateCount formula
    rw [compilerGateCount_eq_structural]
    omega
  have gateBound :
      initial.registers.currentGate <
        CNFToNANDWorkspace.capacity formula := by
    simpa [initial, emitInitialRuntime,
      CNFToNANDWorkspace.workspaceRegisters_currentGate] using
      CNFToNANDWorkspace.compilerGateCount_lt_capacity formula
  refine ⟨target, checksLength, ?_⟩
  intro value member
  rw [checks] at member
  rcases List.mem_append.mp member with old | coordinate
  · exact initialBound.checksValues value old
  · rcases
        clauseListCoordinates_classified formula.variableCount
          formula.clauses initial gateBudget value
          (by simpa [coordinates] using coordinate) with
      equal | less
    · rw [equal]
      exact gateBound
    · exact Nat.lt_trans less gateBound

private theorem formulaRuntime_dataBounded
    (formula : CNFFormula) :
    RuntimeDataBounded formula (formulaRuntime formula) := by
  have completedBound := completedRuntime_dataBounded formula
  apply completedBound.before_of_checks_append
      (by
        simpa [completedRuntime] using
          circuitSuffixResult_target_append (formulaRuntime formula))
      []
  rw [completedRuntime_checks_eq_nil, formulaRuntime_checks_eq_nil]
  simp

private theorem formulaTokens_length_eq
    (formula : CNFFormula) :
    (CNFToNANDWorkspace.formulaTokens formula).length =
      formula.variableCount + 1 +
        (encodeClauseListTokens formula.clauses).length + 1 := by
  simp [CNFToNANDWorkspace.formulaTokens, encodeFormulaTokens,
    encodeCNFTokens, CookLevin.encodeUnaryTokens_length]
  omega

private theorem formulaSuffixPending_length
    (formula : CNFFormula) :
    let initial := emitInitialRuntime formula
    let coordinates :=
      clauseListCoordinates formula.variableCount formula.clauses initial
    let pending := coordinates.reverse
    pending.length = formula.clauses.length := by
  let initial := emitInitialRuntime formula
  let coordinates :=
    clauseListCoordinates formula.variableCount formula.clauses initial
  let pending := coordinates.reverse
  change pending.length = formula.clauses.length
  simp [pending, coordinates, clauseListCoordinates_length]

private theorem formulaSuffixChecks
    (formula : CNFFormula) :
    let initial := emitInitialRuntime formula
    let clauses :=
      clauseListRuntime formula.variableCount formula.clauses initial
    let coordinates :=
      clauseListCoordinates formula.variableCount formula.clauses initial
    let pending := coordinates.reverse
    let marker := CNFToNANDWorkspace.formulaStackMarker formula
    clauses.checks = [] ++ marker :: pending.reverse := by
  let initial := emitInitialRuntime formula
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses initial
  let coordinates :=
    clauseListCoordinates formula.variableCount formula.clauses initial
  let pending := coordinates.reverse
  let marker := CNFToNANDWorkspace.formulaStackMarker formula
  change clauses.checks = [] ++ marker :: pending.reverse
  rw [show pending.reverse = coordinates by simp [pending]]
  simpa [clauses, coordinates, initial, marker,
    emitInitialRuntime] using
    (clauseListRuntime_checks formula.variableCount
      formula.clauses initial)

private theorem formulaSuffixCarrierBound
    (formula : CNFFormula) :
    let initial := emitInitialRuntime formula
    let clauses :=
      clauseListRuntime formula.variableCount formula.clauses initial
    clauses.registers.carrierWidth <
      CNFToNANDWorkspace.capacity formula := by
  let initial := emitInitialRuntime formula
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses initial
  change clauses.registers.carrierWidth <
    CNFToNANDWorkspace.capacity formula
  rw [clauseListRuntime_carrierWidth]
  simpa [initial, emitInitialRuntime,
    CNFToNANDWorkspace.workspaceRegisters_carrierWidth_eq_formulaStackMarker] using
    formulaStackMarker_lt_capacity formula

private theorem formulaSuffixFoldRuntime_dataBounded
    (formula : CNFFormula) :
    let initial := emitInitialRuntime formula
    let clauses :=
      clauseListRuntime formula.variableCount formula.clauses initial
    let coordinates :=
      clauseListCoordinates formula.variableCount formula.clauses initial
    let pending := coordinates.reverse
    RuntimeDataBounded formula
      (formulaFoldRuntime pending.length clauses) := by
  let initial := emitInitialRuntime formula
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses initial
  let coordinates :=
    clauseListCoordinates formula.variableCount formula.clauses initial
  let pending := coordinates.reverse
  change RuntimeDataBounded formula
    (formulaFoldRuntime pending.length clauses)
  have pendingLength := formulaSuffixPending_length formula
  change pending.length = formula.clauses.length at pendingLength
  rw [pendingLength]
  simpa [formulaRuntime, clauses, initial] using
    formulaRuntime_dataBounded formula

private theorem formulaSuffixFoldCost_le_phases
    (formula : CNFFormula) :
    let initial := emitInitialRuntime formula
    let clauses :=
      clauseListRuntime formula.variableCount formula.clauses initial
    let coordinates :=
      clauseListCoordinates formula.variableCount formula.clauses initial
    let pending := coordinates.reverse
    formulaFoldCost (CNFToNANDWorkspace.capacity formula)
        (versionMarkedSource formula) pending clauses ≤
      (4 * formula.clauses.length + 3) * completionPhase formula := by
  let initial := emitInitialRuntime formula
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses initial
  let coordinates :=
    clauseListCoordinates formula.variableCount formula.clauses initial
  let pending := coordinates.reverse
  let marker := CNFToNANDWorkspace.formulaStackMarker formula
  change
    formulaFoldCost (CNFToNANDWorkspace.capacity formula)
        (versionMarkedSource formula) pending clauses ≤
      (4 * formula.clauses.length + 3) * completionPhase formula
  have clausesBound := clauseListRuntime_dataBounded formula
  change RuntimeDataBounded formula clauses at clausesBound
  have checks := formulaSuffixChecks formula
  change clauses.checks = [] ++ marker :: pending.reverse at checks
  have carrierBound := formulaSuffixCarrierBound formula
  change clauses.registers.carrierWidth <
    CNFToNANDWorkspace.capacity formula at carrierBound
  have foldedBound := formulaSuffixFoldRuntime_dataBounded formula
  change RuntimeDataBounded formula
    (formulaFoldRuntime pending.length clauses) at foldedBound
  have foldBound :=
    formulaFoldCost_le_phases formula (versionMarkedSource formula)
      (versionMarkedSource_length_le_dataMajorant formula)
      [] marker pending clauses checks carrierBound clausesBound foldedBound
  have pendingLength := formulaSuffixPending_length formula
  change pending.length = formula.clauses.length at pendingLength
  rw [pendingLength] at foldBound
  exact foldBound

private theorem formulaSuffixDescriptorCost_le_phase
    (formula : CNFFormula) :
    let initial := emitInitialRuntime formula
    let clauses :=
      clauseListRuntime formula.variableCount formula.clauses initial
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
        (CNFToNANDWorkspace.capacity formula)
        (versionMarkedSource formula)
        (formulaFoldRuntime formula.clauses.length clauses)
        blockDescriptors[32].primitives ≤
      completionPhase formula := by
  let initial := emitInitialRuntime formula
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses initial
  change
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
        (CNFToNANDWorkspace.capacity formula)
        (versionMarkedSource formula)
        (formulaFoldRuntime formula.clauses.length clauses)
        blockDescriptors[32].primitives ≤
      completionPhase formula
  have descriptor :=
    versionDescriptorCost_le_phase formula (formulaRuntime formula)
      blockDescriptors[32] blockDescriptor32_mem
      (formulaRuntime_dataBounded formula)
  simpa [formulaRuntime, clauses, initial] using descriptor

private theorem formulaSuffixComponents_le_phases
    (fold descriptor finalizer phase clauseCount : Nat)
    (foldBound : fold ≤ (4 * clauseCount + 3) * phase)
    (descriptorBound : descriptor ≤ phase)
    (finalizerBound : finalizer ≤ phase) :
    fold + descriptor + finalizer ≤
      (4 * clauseCount + 5) * phase := by
  have combined :=
    Nat.add_le_add
      (Nat.add_le_add foldBound descriptorBound)
      finalizerBound
  calc
    fold + descriptor + finalizer ≤
        (4 * clauseCount + 3) * phase + phase + phase := combined
    _ = (4 * clauseCount + 5) * phase := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega

private theorem formulaSuffixCost_le_phases
    (formula : CNFFormula) :
    formulaSuffixCost formula ≤
      (4 * formula.clauses.length + 5) * completionPhase formula := by
  let initial := emitInitialRuntime formula
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses initial
  let coordinates :=
    clauseListCoordinates formula.variableCount formula.clauses initial
  let pending := coordinates.reverse
  have foldBound := formulaSuffixFoldCost_le_phases formula
  change
    formulaFoldCost (CNFToNANDWorkspace.capacity formula)
        (versionMarkedSource formula) pending clauses ≤
      (4 * formula.clauses.length + 3) * completionPhase formula at foldBound
  have descriptorBound := formulaSuffixDescriptorCost_le_phase formula
  change
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
        (CNFToNANDWorkspace.capacity formula)
        (versionMarkedSource formula)
        (formulaFoldRuntime formula.clauses.length clauses)
        blockDescriptors[32].primitives ≤
      completionPhase formula at descriptorBound
  have finalizerBound := finalizerPathSteps_le_phase formula
  unfold formulaSuffixCost
  dsimp only
  change
    formulaFoldCost (CNFToNANDWorkspace.capacity formula)
          (versionMarkedSource formula) pending clauses +
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          (CNFToNANDWorkspace.capacity formula)
          (versionMarkedSource formula)
          (formulaFoldRuntime formula.clauses.length clauses)
          blockDescriptors[32].primitives +
      finalizerPathSteps (versionMarkedSource formula) ≤
        (4 * formula.clauses.length + 5) * completionPhase formula
  exact
    formulaSuffixComponents_le_phases
      (formulaFoldCost (CNFToNANDWorkspace.capacity formula)
        (versionMarkedSource formula) pending clauses)
      (TargetEmitterRuntimeProgramBound.programWorkEnvelope
        (CNFToNANDWorkspace.capacity formula)
        (versionMarkedSource formula)
        (formulaFoldRuntime formula.clauses.length clauses)
        blockDescriptors[32].primitives)
      (finalizerPathSteps (versionMarkedSource formula))
      (completionPhase formula) formula.clauses.length
      foldBound descriptorBound finalizerBound

private theorem emitTraversalCost_le_phases
    (formula : CNFFormula) :
    emitTraversalCost formula ≤
      (1 + (formula.variableCount + 1) +
          8 * (encodeClauseListTokens formula.clauses).length) *
        completionPhase formula := by
  let initial := emitInitialRuntime formula
  let clauses :=
    clauseListRuntime formula.variableCount formula.clauses initial
  have tokenLength := formulaTokens_length_eq formula
  have headerBound := emitHeaderScanSteps_le_phase formula
  have widthHeadroom :
      ([] : List CNFToken).length + (formula.variableCount + 1) ≤
        (CNFToNANDWorkspace.formulaTokens formula).length := by
    rw [tokenLength]
    simp only [List.length_nil, Nat.zero_add]
    omega
  have widthBound :=
    emitWidthCost_le_phases formula formula.variableCount []
      widthHeadroom
  have initialBound := emitInitialRuntime_dataBounded formula
  change RuntimeDataBounded formula initial at initialBound
  have clausesBound := clauseListRuntime_dataBounded formula
  change RuntimeDataBounded formula clauses at clausesBound
  have checksHeadroom :
      initial.checks.length +
          (encodeClauseListTokens formula.clauses).length ≤
        (CNFToNANDWorkspace.formulaTokens formula).length + 1 := by
    have initialChecks : initial.checks.length = 1 := by
      simp [initial, emitInitialRuntime]
    rw [initialChecks, tokenLength]
    omega
  have gateBound :
      initial.registers.currentGate <
        CNFToNANDWorkspace.capacity formula := by
    simpa [initial, emitInitialRuntime,
      CNFToNANDWorkspace.workspaceRegisters_currentGate] using
      CNFToNANDWorkspace.compilerGateCount_lt_capacity formula
  have inputBound :
      initial.registers.inputCount ≤
        CNFToNANDWorkspace.capacity formula := by
    simpa [initial] using (emitInitialRuntime_fits formula).inputCount
  have gateBudget :
      initial.registers.outputIndex +
          clauseListGateCount formula.variableCount formula.clauses ≤
        initial.registers.currentGate := by
    change
      0 + clauseListGateCount formula.variableCount formula.clauses ≤
        CNFToNANDWorkspace.compilerGateCount formula
    rw [compilerGateCount_eq_structural]
    omega
  have clausesBoundCost :=
    clauseListPathCost_le_phases formula
      (encodeUnaryTokens formula.variableCount) .clausesEmpty
      formula.clauses .finish [] initial rfl initialBound clausesBound
      checksHeadroom gateBound inputBound gateBudget
  have combined :=
    Nat.add_le_add
      (Nat.add_le_add headerBound widthBound)
      clausesBoundCost
  unfold emitTraversalCost
  change
    emitHeaderScanSteps formula +
          emitWidthCost formula formula.variableCount [] +
        clauseListPathCost formula
          (encodeUnaryTokens formula.variableCount) .clausesEmpty
          formula.clauses .finish [] initial ≤
      (1 + (formula.variableCount + 1) +
          8 * (encodeClauseListTokens formula.clauses).length) *
        completionPhase formula
  calc
    emitHeaderScanSteps formula +
          emitWidthCost formula formula.variableCount [] +
        clauseListPathCost formula
          (encodeUnaryTokens formula.variableCount) .clausesEmpty
          formula.clauses .finish [] initial ≤
      completionPhase formula +
          (formula.variableCount + 1) * completionPhase formula +
        8 * (encodeClauseListTokens formula.clauses).length *
          completionPhase formula := combined
    _ =
        (1 + (formula.variableCount + 1) +
            8 * (encodeClauseListTokens formula.clauses).length) *
          completionPhase formula := by
      simp only [Nat.add_mul, Nat.one_mul]

private theorem completion_cost_coefficient
    (variableCount clauseTokens clauseCount tokenCount : Nat)
    (tokenLength :
      tokenCount = variableCount + 1 + clauseTokens + 1)
    (clauseCountBound : clauseCount ≤ clauseTokens) :
    (1 + (variableCount + 1) + 8 * clauseTokens) + 4 +
        (4 * clauseCount + 5) ≤
      12 * tokenCount := by
  omega

private theorem completionComponents_le_phases
    (traversal endCost suffix phase variableCount clauseTokens
      clauseCount tokenCount : Nat)
    (traversalBound :
      traversal ≤
        (1 + (variableCount + 1) + 8 * clauseTokens) * phase)
    (endBound : endCost ≤ 4 * phase)
    (suffixBound : suffix ≤ (4 * clauseCount + 5) * phase)
    (coefficient :
      (1 + (variableCount + 1) + 8 * clauseTokens) + 4 +
          (4 * clauseCount + 5) ≤
        12 * tokenCount) :
    traversal + endCost + suffix ≤ 12 * tokenCount * phase := by
  have components :=
    Nat.add_le_add
      (Nat.add_le_add traversalBound endBound)
      suffixBound
  have scaled := Nat.mul_le_mul_right phase coefficient
  calc
    traversal + endCost + suffix ≤
        (1 + (variableCount + 1) + 8 * clauseTokens) * phase +
            4 * phase +
          (4 * clauseCount + 5) * phase := components
    _ =
        ((1 + (variableCount + 1) + 8 * clauseTokens) + 4 +
            (4 * clauseCount + 5)) * phase := by
      simp only [Nat.add_mul]
    _ ≤ 12 * tokenCount * phase := by
      simpa only [Nat.mul_assoc] using scaled

private theorem completionEnvelope_le_linear_phases
    (formula : CNFFormula) :
    completionEnvelope formula ≤
      12 * (CNFToNANDWorkspace.formulaTokens formula).length *
        completionPhase formula := by
  have traversalBound := emitTraversalCost_le_phases formula
  have endBound :=
    endAndInstallCost_le_four_phases formula
      (encodeUnaryTokens formula.variableCount ++
        encodeClauseListTokens formula.clauses)
      rfl
  have suffixBound := formulaSuffixCost_le_phases formula
  have tokenLength := formulaTokens_length_eq formula
  have clauseCountBound :=
    clauseCount_le_clauseTokensLength formula.clauses
  have coefficient :=
    completion_cost_coefficient formula.variableCount
      (encodeClauseListTokens formula.clauses).length
      formula.clauses.length
      (CNFToNANDWorkspace.formulaTokens formula).length
      tokenLength clauseCountBound
  unfold completionEnvelope
  exact
    completionComponents_le_phases
      (emitTraversalCost formula)
      (endAndInstallCost formula
        (encodeUnaryTokens formula.variableCount ++
          encodeClauseListTokens formula.clauses))
      (formulaSuffixCost formula) (completionPhase formula)
      formula.variableCount
      (encodeClauseListTokens formula.clauses).length
      formula.clauses.length
      (CNFToNANDWorkspace.formulaTokens formula).length
      traversalBound endBound suffixBound coefficient

private theorem twelve_le_2048 : 12 ≤ 2048 := by decide

/-- The completed emitting traversal fits its reserved quadratic share of
the controller's common polynomial work allocation. -/
theorem completionEnvelope_le_allocated (formula : CNFFormula) :
    completionEnvelope formula ≤
      2048 *
        shiftedSize (encodeCNF formula).length *
        shiftedSize (encodeCNF formula).length *
        phaseUnit (encodeCNF formula).length := by
  have linear := completionEnvelope_le_linear_phases formula
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
      12 * (CNFToNANDWorkspace.formulaTokens formula).length ≤
        2048 *
          shiftedSize (encodeCNF formula).length *
          shiftedSize (encodeCNF formula).length := by
    let size := shiftedSize (encodeCNF formula).length
    have linearCoefficient :
        12 * (CNFToNANDWorkspace.formulaTokens formula).length ≤
          12 * size := by
      exact Nat.mul_le_mul_left 12 (by simpa [size] using tokenSize)
    have squareCoefficient :
        12 * size ≤ 12 * (size * size) :=
      Nat.mul_le_mul_left 12 (by simpa [size] using sizeSquare)
    have allocatedCoefficient :
        12 * (size * size) ≤ 2048 * (size * size) :=
      Nat.mul_le_mul_right (size * size) twelve_le_2048
    calc
      12 * (CNFToNANDWorkspace.formulaTokens formula).length ≤
          12 * size := linearCoefficient
      _ ≤ 12 * (size * size) := squareCoefficient
      _ ≤ 2048 * (size * size) := allocatedCoefficient
      _ =
          2048 * shiftedSize (encodeCNF formula).length *
            shiftedSize (encodeCNF formula).length := by
        dsimp [size]
        ac_rfl
  have scaled :=
    Nat.mul_le_mul_right
      (phaseUnit (encodeCNF formula).length) coefficient
  exact Nat.le_trans linear scaled

end PNP.Concrete.CNFToNANDControllerCompletionTrace

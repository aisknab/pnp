/-
Copyright (c) 2026 PNP Labs.

Exact controller paths for the four check-stack branch nodes used by the
locked-NAND target emitter.

The stack is physically farthest-first and logically append-at-the-right.
Consequently a successful pop exposes the newest check and drives the
right-fold prefix blocks.  An empty pop follows the literal reject edge
selected by the fixed controller graph; it is not an interpreter failure.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerInitialTrace

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerCheckTrace

open PNP.Concrete
open WorkMachineProgramPath
open TargetEmitterController

abbrev LedgerFits :=
  TargetEmitterRuntimeCheckStack.CheckStack.LedgerFits

def emptyPathSteps (capacity : Nat) : Nat :=
  TargetEmitterCheckStack.Pop.emptyWorkSteps capacity + 1

def nonemptyPathSteps
    (capacity : Nat) (prior : List Nat) (value : Nat) : Nat :=
  TargetEmitterCheckStack.Pop.nonemptyWorkSteps capacity
      (TargetEmitterCheckStack.recordsWord prior).length value + 1

private theorem localAcceptRun_of_exact
    (node : WorkMachineProgramGraph.Node) (steps : Nat)
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

private theorem localRejectRun_of_exact
    (node : WorkMachineProgramGraph.Node) (steps : Nat)
    (initial final : WorkConfiguration)
    (initialState :
      initial.state = node.program.startState)
    (finalState :
      final.state = node.program.rejectState)
    (exactRun :
      workRunExact? node.program steps initial = some final) :
    LocalRejectRun node steps initial.tape final.tape := by
  rcases initial with ⟨initialStateValue, initialTape⟩
  rcases final with ⟨finalStateValue, finalTape⟩
  change initialStateValue = node.program.startState at initialState
  change finalStateValue = node.program.rejectState at finalState
  subst initialStateValue
  subst finalStateValue
  exact exactRun

private theorem pop_empty_path_of_node
    (node : WorkMachineProgramGraph.Node)
    (continuation : WorkMachineProgramGraph.Endpoint)
    (member : node ∈ graph.nodes)
    (programEq :
      node.program = TargetEmitterCheckStack.Pop.machine)
    (rejectEq : node.onReject = continuation)
    (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState
        capacity 0 registers []
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node node.reference) continuation
          (emptyPathSteps capacity)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.rejectState
        capacity 0 registers []
        (sourceHead :: sourceTail) target actualFinal := by
  rcases
      TargetEmitterRuntimeCheckStack.CheckStack.pop_empty_exact
        capacity registers sourceHead sourceTail target actual
        fits allowed represents with
    ⟨actualFinal, exactRun, finalRepresents⟩
  have initialState :
      actual.state = node.program.startState := by
    rw [programEq]
    exact TargetEmitterRuntime.Represents.state_eq represents
  have finalState :
      actualFinal.state = node.program.rejectState := by
    rw [programEq]
    exact TargetEmitterRuntime.Represents.state_eq finalRepresents
  have nodeRun :
      workRunExact? node.program
          (TargetEmitterCheckStack.Pop.emptyWorkSteps capacity)
          actual =
        some actualFinal := by
    rw [programEq]
    exact exactRun
  have localRun :
      LocalRejectRun node
        (TargetEmitterCheckStack.Pop.emptyWorkSteps capacity)
        actual.tape actualFinal.tape :=
    localRejectRun_of_exact node
      (TargetEmitterCheckStack.Pop.emptyWorkSteps capacity)
      actual actualFinal initialState finalState nodeRun
  have tail :
      AcceptPath graph continuation continuation 0
        actualFinal.tape actualFinal.tape :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.stepReject node continuation
      (TargetEmitterCheckStack.Pop.emptyWorkSteps capacity) 0
      actual.tape actualFinal.tape actualFinal.tape
      member localRun (by simpa [rejectEq] using tail)
  refine ⟨actualFinal, ?_, finalRepresents⟩
  simpa [emptyPathSteps] using path

private theorem pop_nonempty_path_of_node
    (node : WorkMachineProgramGraph.Node)
    (continuation : WorkMachineProgramGraph.Endpoint)
    (member : node ∈ graph.nodes)
    (programEq :
      node.program = TargetEmitterCheckStack.Pop.machine)
    (acceptEq : node.onAccept = continuation)
    (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState
        capacity 0 registers (prior ++ [value])
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node node.reference) continuation
          (nonemptyPathSteps capacity prior value)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.acceptState
        capacity value registers prior
        (sourceHead :: sourceTail) target actualFinal := by
  rcases
      TargetEmitterRuntimeCheckStack.CheckStack.pop_nonempty_exact
        capacity value registers prior sourceHead sourceTail
        target actual fits valueBound allowed represents with
    ⟨actualFinal, exactRun, finalRepresents⟩
  have initialState :
      actual.state = node.program.startState := by
    rw [programEq]
    exact TargetEmitterRuntime.Represents.state_eq represents
  have finalState :
      actualFinal.state = node.program.acceptState := by
    rw [programEq]
    exact TargetEmitterRuntime.Represents.state_eq finalRepresents
  have nodeRun :
      workRunExact? node.program
          (TargetEmitterCheckStack.Pop.nonemptyWorkSteps capacity
            (TargetEmitterCheckStack.recordsWord prior).length value)
          actual =
        some actualFinal := by
    rw [programEq]
    exact exactRun
  have localRun :
      LocalAcceptRun node
        (TargetEmitterCheckStack.Pop.nonemptyWorkSteps capacity
          (TargetEmitterCheckStack.recordsWord prior).length value)
        actual.tape actualFinal.tape :=
    localAcceptRun_of_exact node
      (TargetEmitterCheckStack.Pop.nonemptyWorkSteps capacity
        (TargetEmitterCheckStack.recordsWord prior).length value)
      actual actualFinal initialState finalState nodeRun
  have tail :
      AcceptPath graph continuation continuation 0
        actualFinal.tape actualFinal.tape :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.step node continuation
      (TargetEmitterCheckStack.Pop.nonemptyWorkSteps capacity
        (TargetEmitterCheckStack.recordsWord prior).length value) 0
      actual.tape actualFinal.tape actualFinal.tape
      member localRun (by simpa [acceptEq] using tail)
  refine ⟨actualFinal, ?_, finalRepresents⟩
  simpa [nonemptyPathSteps] using path

private theorem rawInitialPopNode_member :
    rawInitialPopNode ∈ graph.nodes := by
  apply controlNode_member_nodes
  simp [controlNodes]

private theorem rawLoopPopNode_member :
    rawLoopPopNode ∈ graph.nodes := by
  apply controlNode_member_nodes
  simp [controlNodes]

private theorem normalizedInitialPopNode_member :
    normalizedInitialPopNode ∈ graph.nodes := by
  apply controlNode_member_nodes
  simp [controlNodes]

private theorem normalizedLoopPopNode_member :
    normalizedLoopPopNode ∈ graph.nodes := by
  apply controlNode_member_nodes
  simp [controlNodes]

theorem rawInitialPop_empty_path
    (capacity : Nat) (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState capacity 0 registers []
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node rawInitialPopRef)
          (.node rawFinalZeroRef) (emptyPathSteps capacity)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.rejectState capacity 0 registers []
        (sourceHead :: sourceTail) target actualFinal := by
  simpa [rawInitialPopNode, rawInitialPopRef, controlNode,
    controlRef, WorkMachineProgramGraph.Node.reference] using
    (pop_empty_path_of_node rawInitialPopNode
      (.node rawFinalZeroRef) rawInitialPopNode_member rfl rfl
      capacity registers sourceHead sourceTail target actual
      fits allowed represents)

theorem rawInitialPop_nonempty_path
    (capacity value : Nat) (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState capacity 0 registers
        (prior ++ [value]) (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node rawInitialPopRef)
          (.node rawFirstPrefixRef)
          (nonemptyPathSteps capacity prior value)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.acceptState capacity value registers prior
        (sourceHead :: sourceTail) target actualFinal := by
  simpa [rawInitialPopNode, rawInitialPopRef, controlNode,
    controlRef, WorkMachineProgramGraph.Node.reference] using
    (pop_nonempty_path_of_node rawInitialPopNode
      (.node rawFirstPrefixRef) rawInitialPopNode_member rfl rfl
      capacity value registers prior sourceHead sourceTail target
      actual fits valueBound allowed represents)

theorem rawLoopPop_empty_path
    (capacity : Nat) (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState capacity 0 registers []
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node rawLoopPopRef)
          (.node rawFinalRef) (emptyPathSteps capacity)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.rejectState capacity 0 registers []
        (sourceHead :: sourceTail) target actualFinal := by
  simpa [rawLoopPopNode, rawLoopPopRef, controlNode,
    controlRef, WorkMachineProgramGraph.Node.reference] using
    (pop_empty_path_of_node rawLoopPopNode
      (.node rawFinalRef) rawLoopPopNode_member rfl rfl
      capacity registers sourceHead sourceTail target actual
      fits allowed represents)

theorem rawLoopPop_nonempty_path
    (capacity value : Nat) (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState capacity 0 registers
        (prior ++ [value]) (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node rawLoopPopRef)
          (.node rawNextPrefixRef)
          (nonemptyPathSteps capacity prior value)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.acceptState capacity value registers prior
        (sourceHead :: sourceTail) target actualFinal := by
  simpa [rawLoopPopNode, rawLoopPopRef, controlNode,
    controlRef, WorkMachineProgramGraph.Node.reference] using
    (pop_nonempty_path_of_node rawLoopPopNode
      (.node rawNextPrefixRef) rawLoopPopNode_member rfl rfl
      capacity value registers prior sourceHead sourceTail target
      actual fits valueBound allowed represents)

theorem normalizedInitialPop_empty_path
    (capacity : Nat) (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState capacity 0 registers []
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node normalizedInitialPopRef) .reject
          (emptyPathSteps capacity) actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.rejectState capacity 0 registers []
        (sourceHead :: sourceTail) target actualFinal := by
  simpa [normalizedInitialPopNode, normalizedInitialPopRef,
    controlNode, controlRef,
    WorkMachineProgramGraph.Node.reference] using
    (pop_empty_path_of_node normalizedInitialPopNode .reject
      normalizedInitialPopNode_member rfl rfl capacity registers
      sourceHead sourceTail target actual fits allowed represents)

theorem normalizedInitialPop_nonempty_path
    (capacity value : Nat) (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState capacity 0 registers
        (prior ++ [value]) (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node normalizedInitialPopRef)
          (.node normalizedFirstPrefixRef)
          (nonemptyPathSteps capacity prior value)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.acceptState capacity value registers prior
        (sourceHead :: sourceTail) target actualFinal := by
  simpa [normalizedInitialPopNode, normalizedInitialPopRef,
    controlNode, controlRef,
    WorkMachineProgramGraph.Node.reference] using
    (pop_nonempty_path_of_node normalizedInitialPopNode
      (.node normalizedFirstPrefixRef)
      normalizedInitialPopNode_member rfl rfl
      capacity value registers prior sourceHead sourceTail target
      actual fits valueBound allowed represents)

theorem normalizedLoopPop_empty_path
    (capacity : Nat) (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState capacity 0 registers []
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node normalizedLoopPopRef)
          (.node normalizedFinalRef) (emptyPathSteps capacity)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.rejectState capacity 0 registers []
        (sourceHead :: sourceTail) target actualFinal := by
  simpa [normalizedLoopPopNode, normalizedLoopPopRef,
    controlNode, controlRef,
    WorkMachineProgramGraph.Node.reference] using
    (pop_empty_path_of_node normalizedLoopPopNode
      (.node normalizedFinalRef) normalizedLoopPopNode_member rfl rfl
      capacity registers sourceHead sourceTail target actual
      fits allowed represents)

theorem normalizedLoopPop_nonempty_path
    (capacity value : Nat) (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState capacity 0 registers
        (prior ++ [value]) (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      AcceptPath graph (.node normalizedLoopPopRef)
          (.node normalizedNextPrefixRef)
          (nonemptyPathSteps capacity prior value)
          actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.acceptState capacity value registers prior
        (sourceHead :: sourceTail) target actualFinal := by
  simpa [normalizedLoopPopNode, normalizedLoopPopRef,
    controlNode, controlRef,
    WorkMachineProgramGraph.Node.reference] using
    (pop_nonempty_path_of_node normalizedLoopPopNode
      (.node normalizedNextPrefixRef) normalizedLoopPopNode_member rfl rfl
      capacity value registers prior sourceHead sourceTail target
      actual fits valueBound allowed represents)

end PNP.Concrete.LockedNAND.TargetEmitterControllerCheckTrace

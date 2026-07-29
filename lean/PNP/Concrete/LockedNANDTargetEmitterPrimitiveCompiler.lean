/-
Copyright (c) 2026 PNP Labs.

Closed primitive-to-machine compiler for the grammar-only locked-NAND target
emitter.

Every successful compiler case selects one audited fixed work-machine table.
The compiler runs only while materializing the finite controller graph; the
resulting machine contains literal renamed rules and bridge destinations, not
an interpreter or host-side primitive lookup.
-/

import PNP.Concrete.LockedNANDTargetEmitterPlan
import PNP.Concrete.LockedNANDTargetEmitterCursorAppender
import PNP.Concrete.LockedNANDTargetEmitterScratchReset
import PNP.Concrete.LockedNANDTargetEmitterScratchAddSlot
import PNP.Concrete.LockedNANDTargetEmitterMarkedSourceReload
import PNP.Concrete.LockedNANDTargetEmitterScratchIncrement
import PNP.Concrete.LockedNANDTargetEmitterNatLoop
import PNP.Concrete.LockedNANDTargetEmitterCursorNatLoop
import PNP.Concrete.LockedNANDTargetEmitterCheckStack
import PNP.Concrete.LockedNANDTargetEmitterScratchCompareSlot
import PNP.Concrete.LockedNANDTargetEmitterSlotIncrement
import PNP.Concrete.WorkMachineProgramGraph

namespace PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler

open PNP.Concrete
open TargetEmitterPlan

abbrev Slot := TargetEmitterLedger.Slot

def counterSlot : Counter → Option Slot
  | .inputCount => some .inputCount
  | .normalizedGateCount => some .normalizedGateCount
  | .carrierWidth => some .carrierWidth
  | .baseline => some .baseline
  | .currentGate => some .currentGate
  | .outputIndex => some .outputIndex
  | .captured | .scratch => none

theorem counterSlot_inputCount :
    counterSlot .inputCount = some .inputCount := by
  rfl

theorem counterSlot_normalizedGateCount :
    counterSlot .normalizedGateCount =
      some .normalizedGateCount := by
  rfl

theorem counterSlot_carrierWidth :
    counterSlot .carrierWidth = some .carrierWidth := by
  rfl

theorem counterSlot_baseline :
    counterSlot .baseline = some .baseline := by
  rfl

theorem counterSlot_currentGate :
    counterSlot .currentGate = some .currentGate := by
  rfl

theorem counterSlot_outputIndex :
    counterSlot .outputIndex = some .outputIndex := by
  rfl

theorem counterSlot_captured :
    counterSlot .captured = none := by
  rfl

theorem counterSlot_scratch :
    counterSlot .scratch = none := by
  rfl

/-- Select the one fixed local table implementing a closed primitive.  An
invalid register constructor is rejected during graph materialization. -/
def primitiveMachine : Primitive → Option WorkMachine
  | .append .plain token =>
      some (TargetEmitter.machineFor token)
  | .append .marked token =>
      some (TargetEmitterCursorAppender.machineFor token)
  | .resetScratch =>
      some TargetEmitterScratchReset.machine
  | .addRegister counter => do
      let slot ← counterSlot counter
      pure (TargetEmitterScratchAddSlot.machineFor slot)
  | .reloadCaptured =>
      some TargetEmitterMarkedSourceReload.machine
  | .incrementScratch =>
      some TargetEmitterScratchIncrement.machine
  | .emitScratchNat .plain =>
      some TargetEmitterNatLoop.machine
  | .emitScratchNat .marked =>
      some TargetEmitterCursorNatLoop.machine
  | .pushCheck =>
      some TargetEmitterCheckStack.Push.machine
  | .popCheck =>
      some TargetEmitterCheckStack.Pop.machine
  | .compareRegister counter => do
      let slot ← counterSlot counter
      pure (TargetEmitterScratchCompareSlot.machineFor slot)
  | .incrementRegister counter => do
      let slot ← counterSlot counter
      pure (TargetEmitterSlotIncrement.machineFor slot)

def primitiveRuleCount (primitive : Primitive) : Option Nat :=
  (primitiveMachine primitive).map (fun program =>
    program.rules.length)

def compileProgram : List Primitive → Option (List WorkMachine)
  | [] => some []
  | primitive :: rest => do
      let program ← primitiveMachine primitive
      let tail ← compileProgram rest
      pure (program :: tail)

theorem compileProgram_nil :
    compileProgram [] = some [] := by
  rfl

theorem compileProgram_cons
    (primitive : Primitive) (rest : List Primitive) :
    compileProgram (primitive :: rest) =
      (do
        let program ← primitiveMachine primitive
        let tail ← compileProgram rest
        pure (program :: tail)) := by
  rfl

theorem compileProgram_append
    (first second : List Primitive)
    (firstMachines secondMachines : List WorkMachine)
    (firstCompiled :
      compileProgram first = some firstMachines)
    (secondCompiled :
      compileProgram second = some secondMachines) :
    compileProgram (first ++ second) =
      some (firstMachines ++ secondMachines) := by
  induction first generalizing firstMachines with
  | nil =>
      change some [] = some firstMachines at firstCompiled
      have firstEq : firstMachines = [] := by
        exact (Option.some.inj firstCompiled).symm
      subst firstMachines
      simpa using secondCompiled
  | cons primitive rest inductionHypothesis =>
      cases machineEq : primitiveMachine primitive with
      | none =>
          simp [compileProgram, machineEq] at firstCompiled
      | some program =>
          cases tailEq : compileProgram rest with
          | none =>
              simp [compileProgram, machineEq, tailEq] at firstCompiled
          | some tail =>
              simp only [compileProgram, machineEq, tailEq]
                at firstCompiled
              have machinesEq :
                  firstMachines = program :: tail :=
                (Option.some.inj firstCompiled).symm
              subst firstMachines
              change
                compileProgram (primitive :: (rest ++ second)) =
                  some (program :: (tail ++ secondMachines))
              rw [compileProgram_cons, machineEq,
                inductionHypothesis tail tailEq]
              rfl

/-! ### Structural graph certificates -/

private theorem wellFormed_of_interfaces
    (program : WorkMachine)
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
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := program
        onAccept := .accept
        onReject := .reject } := by
  exact
    ⟨pairwise,
      WorkMachineProgramGraph.noRuleAt_of_findWorkRule_none
        program program.acceptState noAccept,
      WorkMachineProgramGraph.noRuleAt_of_findWorkRule_none
        program program.rejectState noReject,
      acceptNeReject⟩

private theorem plainAppender_wellFormed (token : Token) :
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := TargetEmitter.machineFor token
        onAccept := .accept
        onReject := .reject } := by
  apply wellFormed_of_interfaces
  · change
      TargetEmitter.rules.Pairwise
        TargetEmitter.QueryDistinct
    exact TargetEmitter.rules_pairwise
  · intro symbol
    exact TargetEmitter.no_rule_at_accept symbol
  · intro symbol
    exact TargetEmitter.no_rule_at_reject symbol
  · exact TargetEmitter.accept_ne_reject

private theorem markedAppender_wellFormed (token : Token) :
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := TargetEmitterCursorAppender.machineFor token
        onAccept := .accept
        onReject := .reject } := by
  apply wellFormed_of_interfaces
  · change
      TargetEmitterCursorAppender.rules.Pairwise
        TargetEmitterCursorAppender.QueryDistinct
    exact TargetEmitterCursorAppender.rules_pairwise
  · intro symbol
    exact TargetEmitterCursorAppender.no_rule_at_done token symbol
  · intro symbol
    exact TargetEmitterCursorAppender.no_rule_at_reject symbol
  · exact TargetEmitterCursorAppender.machine_accept_ne_reject token

private theorem scratchReset_wellFormed :
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := TargetEmitterScratchReset.machine
        onAccept := .accept
        onReject := .reject } := by
  apply wellFormed_of_interfaces
  · change
      TargetEmitterScratchReset.rules.Pairwise
        TargetEmitterScratchReset.QueryDistinct
    exact TargetEmitterScratchReset.rules_pairwise
  · exact TargetEmitterScratchReset.no_rule_at_accept
  · exact TargetEmitterScratchReset.no_rule_at_reject
  · exact TargetEmitterScratchReset.accept_ne_reject

private theorem scratchAddSlot_wellFormed (slot : Slot) :
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := TargetEmitterScratchAddSlot.machineFor slot
        onAccept := .accept
        onReject := .reject } := by
  apply wellFormed_of_interfaces
  · change
      TargetEmitterScratchAddSlot.rules.Pairwise
        TargetEmitterScratchAddSlot.QueryDistinct
    exact TargetEmitterScratchAddSlot.rules_pairwise
  · exact TargetEmitterScratchAddSlot.no_rule_at_accept
  · exact TargetEmitterScratchAddSlot.no_rule_at_reject
  · exact TargetEmitterScratchAddSlot.accept_ne_reject slot

private theorem markedSourceReload_wellFormed :
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := TargetEmitterMarkedSourceReload.machine
        onAccept := .accept
        onReject := .reject } := by
  apply wellFormed_of_interfaces
  · change
      TargetEmitterMarkedSourceReload.rules.Pairwise
        TargetEmitterMarkedSourceReload.QueryDistinct
    exact TargetEmitterMarkedSourceReload.rules_pairwise
  · exact TargetEmitterMarkedSourceReload.no_rule_at_accept
  · exact TargetEmitterMarkedSourceReload.no_rule_at_reject
  · exact TargetEmitterMarkedSourceReload.accept_ne_reject

private theorem scratchIncrement_wellFormed :
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := TargetEmitterScratchIncrement.machine
        onAccept := .accept
        onReject := .reject } := by
  apply wellFormed_of_interfaces
  · change
      TargetEmitterScratchIncrement.rules.Pairwise
        TargetEmitterScratchIncrement.QueryDistinct
    exact TargetEmitterScratchIncrement.rules_pairwise
  · exact TargetEmitterScratchIncrement.no_rule_at_accept
  · exact TargetEmitterScratchIncrement.no_rule_at_reject
  · exact TargetEmitterScratchIncrement.accept_ne_reject

private theorem natLoop_wellFormed :
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := TargetEmitterNatLoop.machine
        onAccept := .accept
        onReject := .reject } := by
  apply wellFormed_of_interfaces
  · change
      TargetEmitterNatLoop.rules.Pairwise
        TargetEmitterNatLoop.QueryDistinct
    exact TargetEmitterNatLoop.rules_pairwise
  · exact TargetEmitterNatLoop.no_rule_at_accept
  · exact TargetEmitterNatLoop.no_rule_at_reject
  · exact TargetEmitterNatLoop.machine_accept_ne_reject

private theorem cursorNatLoop_wellFormed :
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := TargetEmitterCursorNatLoop.machine
        onAccept := .accept
        onReject := .reject } := by
  apply wellFormed_of_interfaces
  · change
      TargetEmitterCursorNatLoop.rules.Pairwise
        TargetEmitterCursorNatLoop.QueryDistinct
    exact TargetEmitterCursorNatLoop.rules_pairwise
  · exact TargetEmitterCursorNatLoop.no_rule_at_accept
  · exact TargetEmitterCursorNatLoop.no_rule_at_reject
  · exact TargetEmitterCursorNatLoop.machine_accept_ne_reject

private theorem stackPush_wellFormed :
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := TargetEmitterCheckStack.Push.machine
        onAccept := .accept
        onReject := .reject } := by
  apply wellFormed_of_interfaces
  · change
      TargetEmitterCheckStack.Push.rules.Pairwise
        TargetEmitterCheckStack.QueryDistinct
    exact TargetEmitterCheckStack.Push.rules_pairwise
  · exact TargetEmitterCheckStack.Push.no_rule_at_accept
  · exact TargetEmitterCheckStack.Push.no_rule_at_reject
  · exact TargetEmitterCheckStack.Push.accept_ne_reject

private theorem stackPop_wellFormed :
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := TargetEmitterCheckStack.Pop.machine
        onAccept := .accept
        onReject := .reject } := by
  apply wellFormed_of_interfaces
  · change
      TargetEmitterCheckStack.Pop.rules.Pairwise
        TargetEmitterCheckStack.QueryDistinct
    exact TargetEmitterCheckStack.Pop.rules_pairwise
  · exact TargetEmitterCheckStack.Pop.no_rule_at_accept
  · exact TargetEmitterCheckStack.Pop.no_rule_at_reject
  · exact TargetEmitterCheckStack.Pop.accept_ne_reject

private theorem scratchCompareSlot_wellFormed (slot : Slot) :
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := TargetEmitterScratchCompareSlot.machineFor slot
        onAccept := .accept
        onReject := .reject } := by
  apply wellFormed_of_interfaces
  · change
      TargetEmitterScratchCompareSlot.rules.Pairwise
        TargetEmitterScratchCompareSlot.QueryDistinct
    exact TargetEmitterScratchCompareSlot.rules_pairwise
  · exact TargetEmitterScratchCompareSlot.no_rule_at_accept
  · exact TargetEmitterScratchCompareSlot.no_rule_at_reject
  · exact TargetEmitterScratchCompareSlot.accept_ne_reject slot

private theorem slotIncrement_wellFormed (slot : Slot) :
    WorkMachineProgramGraph.Node.WellFormed
      { name := 0
        program := TargetEmitterSlotIncrement.machineFor slot
        onAccept := .accept
        onReject := .reject } := by
  apply wellFormed_of_interfaces
  · change
      TargetEmitterSlotIncrement.rules.Pairwise
        TargetEmitterSlotIncrement.QueryDistinct
    exact TargetEmitterSlotIncrement.rules_pairwise
  · exact TargetEmitterSlotIncrement.no_rule_at_accept
  · exact TargetEmitterSlotIncrement.no_rule_at_reject
  · exact TargetEmitterSlotIncrement.accept_ne_reject slot

theorem primitiveMachine_wellFormed
    (primitive : Primitive) :
    match primitiveMachine primitive with
    | none => True
    | some program =>
        WorkMachineProgramGraph.Node.WellFormed
          { name := 0
            program := program
            onAccept := .accept
            onReject := .reject } := by
  cases primitive with
  | append mode token =>
      cases mode with
      | plain => exact plainAppender_wellFormed token
      | marked => exact markedAppender_wellFormed token
  | resetScratch =>
      exact scratchReset_wellFormed
  | addRegister counter =>
      cases counter <;>
        simp only [primitiveMachine, counterSlot] <;>
        first
        | exact True.intro
        | exact scratchAddSlot_wellFormed _
  | reloadCaptured =>
      exact markedSourceReload_wellFormed
  | incrementScratch =>
      exact scratchIncrement_wellFormed
  | emitScratchNat mode =>
      cases mode with
      | plain => exact natLoop_wellFormed
      | marked => exact cursorNatLoop_wellFormed
  | pushCheck =>
      exact stackPush_wellFormed
  | popCheck =>
      exact stackPop_wellFormed
  | compareRegister counter =>
      cases counter <;>
        simp only [primitiveMachine, counterSlot] <;>
        first
        | exact True.intro
        | exact scratchCompareSlot_wellFormed _
  | incrementRegister counter =>
      cases counter <;>
        simp only [primitiveMachine, counterSlot] <;>
        first
        | exact True.intro
        | exact slotIncrement_wellFormed _

theorem primitiveMachine_wellFormed_of_eq
    (primitive : Primitive) (program : WorkMachine)
    (compiled : primitiveMachine primitive = some program)
    (name : Nat) (onAccept onReject :
      WorkMachineProgramGraph.Endpoint) :
    WorkMachineProgramGraph.Node.WellFormed
      { name := name
        program := program
        onAccept := onAccept
        onReject := onReject } := by
  have certified := primitiveMachine_wellFormed primitive
  rw [compiled] at certified
  simpa [WorkMachineProgramGraph.Node.WellFormed] using
    certified

theorem primitiveMachine_append_plain (token : Token) :
    primitiveMachine (.append .plain token) =
      some (TargetEmitter.machineFor token) := by
  rfl

theorem primitiveMachine_append_marked (token : Token) :
    primitiveMachine (.append .marked token) =
      some (TargetEmitterCursorAppender.machineFor token) := by
  rfl

theorem primitiveMachine_compare_baseline :
    primitiveMachine (.compareRegister .baseline) =
      some
        (TargetEmitterScratchCompareSlot.machineFor .baseline) := by
  rfl

theorem primitiveMachine_increment_outputIndex :
    primitiveMachine (.incrementRegister .outputIndex) =
      some (TargetEmitterSlotIncrement.machineFor .outputIndex) := by
  rfl

theorem primitiveMachine_add_captured_rejected :
    primitiveMachine (.addRegister .captured) = none := by
  rfl

theorem primitiveMachine_compare_scratch_rejected :
    primitiveMachine (.compareRegister .scratch) = none := by
  rfl

theorem primitiveMachine_increment_captured_rejected :
    primitiveMachine (.incrementRegister .captured) = none := by
  rfl

end PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler

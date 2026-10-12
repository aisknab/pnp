/-
Copyright (c) 2026 PNP Labs.

Construct the protected search countdown from the internally read width
and internally counted clauses. Both words are traversed by the actual
finite prepend loop; no outside iteration budget is accepted.
-/

import PNP.Concrete.NormalizerExplorationLoader

namespace PNP.Concrete.NormalizerBlocks.Exploration
open BitRegister

def startBudget : Block 28 := .seq (.action (.copy 2 20)) (.action (.clear 0))
def budgetStarted (r : State) : State :=
  r.withRegisters {r.registers with remaining := r.core.parent.currentIndex, input := []}
theorem startBudget_exec (r : State) : Exec startBudget r.store 2 (budgetStarted r).store :=
  Exec.seq (.action _ _) (.action _ _)

def prependCount : Block 28 := liftCore ParentQuery.prependLoop
def countPrepended (r : State) : State :=
  r.withRegisters (ParentQuery.prepended r.registers.remaining r.registers)
def prependCountFuel (r : State) : Nat := 3 * r.registers.remaining.length + 1
theorem prependCount_exec (r : State) :
    Exec prependCount r.store (prependCountFuel r) (countPrepended r).store :=
  liftCore_exec _ r _ _ (ParentQuery.prepend_exec r.registers.remaining r.registers)

def reloadWidth : Block 28 := .action (.copy 2 17)
def widthReloaded (r : State) : State :=
  r.withRegisters {r.registers with remaining := r.core.parent.targetIndex}
theorem reloadWidth_exec (r : State) : Exec reloadWidth r.store 1 (widthReloaded r).store := .action _ _

def saveBudget : Block 28 :=
  .action (.copy (Frame.frameIndex 27 (0 : Fin 1)) (Frame.index 1 (0 : Fin 27)))
def budgetSaved (r : State) : State := {r with remaining := r.registers.input}
theorem saveBudget_exec (r : State) : Exec saveBudget r.store 1 (budgetSaved r).store := by
  have input : r.core.store.get (0 : Fin 27) = r.registers.input := rfl
  have checked := Exec.action
    (.copy (Frame.frameIndex 27 (0 : Fin 1)) (Frame.index 1 (0 : Fin 27))) r.store
  simpa only [saveBudget, Action.update, Action.instruction, Instruction.update,
    State.store, Frame.get_core, Frame.set_frame, State.frame, budgetSaved,
    Store.set, Store.indexCases, input] using checked

def budgetLeft (r : State) : State := countPrepended (budgetStarted r)
def budgetRight (r : State) : State := countPrepended (widthReloaded (budgetLeft r))
def budgeted (r : State) : State := budgetSaved (budgetRight r)
def buildBudget : Block 28 :=
  .seq startBudget (.seq prependCount (.seq reloadWidth (.seq prependCount saveBudget)))
def budgetFuel (r : State) : Nat :=
  2 + (prependCountFuel (budgetStarted r) + (1 + (prependCountFuel (widthReloaded (budgetLeft r)) + 1)))
theorem buildBudget_exec (r : State) : Exec buildBudget r.store (budgetFuel r) (budgeted r).store :=
  Exec.seq (startBudget_exec r) <| Exec.seq (prependCount_exec (budgetStarted r)) <|
    Exec.seq (reloadWidth_exec (budgetLeft r)) <|
      Exec.seq (prependCount_exec (widthReloaded (budgetLeft r))) (saveBudget_exec (budgetRight r))

theorem budgeted_fields (r : State) :
    (budgeted r).remaining = List.replicate
      (r.core.parent.currentIndex.length + r.core.parent.targetIndex.length) true ∧
      (budgeted r).core.parent.targetIndex = r.core.parent.targetIndex ∧
        (budgeted r).core.parent.currentIndex = r.core.parent.currentIndex ∧
          (budgeted r).core.parent.graph.core.formula = r.core.parent.graph.core.formula ∧
            (budgeted r).core.parent.graph.core.matching = r.core.parent.graph.core.matching ∧
              (budgeted r).core.trace = r.core.trace := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  change List.replicate r.core.parent.targetIndex.length true ++
    (List.replicate r.core.parent.currentIndex.length true ++ []) = _
  rw [List.append_nil, List.replicate_append_replicate, Nat.add_comm]

theorem budgetFuel_eq (r : State) :
    budgetFuel r = 3 * r.core.parent.currentIndex.length + 3 * r.core.parent.targetIndex.length + 6 := by
  change 2 + ((3 * r.core.parent.currentIndex.length + 1) +
    (1 + ((3 * r.core.parent.targetIndex.length + 1) + 1))) = _
  omega

end PNP.Concrete.NormalizerBlocks.Exploration

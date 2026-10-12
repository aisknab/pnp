/-
Copyright (c) 2026 PNP Labs.

Choose the first matching literal position, then the middle position, and
otherwise the last position. This is the source rule for a three-literal
clause, implemented with two actual bounded reads and comparisons.
-/
import PNP.Concrete.NormalizerCacheSlotProbe

namespace PNP.Concrete.NormalizerBlocks.CacheSlot
open BitRegister Occurrence

def emitted (position : Nat) (r : State) : State :=
  r.withRegisters {r.registers with output := TableOwner.answer (some position)}
def emitFirst : Block 16 := DenseClauses.liftCore (TraceCount.emit true)
def emitMiddle : Block 16 := .seq emitFirst (.action (.push 8 true))
def emitLast : Block 16 := .seq emitMiddle (.action (.push 8 true))
theorem emitFirst_exec (r : State) : Exec emitFirst r.store 2 (emitted 0 r).store :=
  DenseClauses.liftCore_exec _ r _ _ (TraceCount.emit_exec true r.registers)
theorem emitMiddle_exec (r : State) : Exec emitMiddle r.store 3 (emitted 1 r).store :=
  Exec.seq (emitFirst_exec r) (.action _ _)
theorem emitLast_exec (r : State) : Exec emitLast r.store 4 (emitted 2 r).store :=
  Exec.seq (emitMiddle_exec r) (.action _ _)

def secondChoice : Block 16 := .branch 8 emitLast emitLast emitMiddle
def secondChosen (r : State) : State :=
  if ForwardEdge.present r.registers.output then emitted 1 r else emitted 2 r
def secondChoiceFuel (r : State) : Nat := 1 + if ForwardEdge.present r.registers.output then 3 else 4
theorem secondChoice_exec (r : State) :
    Exec secondChoice r.store (secondChoiceFuel r) (secondChosen r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 16) r.store emitLast emitMiddle
    4 3 (emitted 2 r).store (emitted 1 r).store (emitLast_exec r) (emitMiddle_exec r)
  change Exec secondChoice r.store (1 + if ForwardEdge.present r.registers.output then 3 else 4)
    (if ForwardEdge.present r.registers.output then (emitted 1 r).store else (emitted 2 r).store) at checked
  cases h : ForwardEdge.present r.registers.output <;>
    simpa only [secondChoice, secondChoiceFuel, secondChosen, h, Bool.false_eq_true, ite_false, ite_true] using checked
theorem secondChoiceFuel_bound (r : State) : secondChoiceFuel r ≤ 5 := by
  unfold secondChoiceFuel
  cases ForwardEdge.present r.registers.output <;> decide

def second : Block 16 := .seq probe secondChoice
def secondResult (r : State) : State := secondChosen (probed r)
def secondFuel (r : State) : Nat := probeFuel r + secondChoiceFuel (probed r)
theorem second_exec (r : State) : Exec second r.store (secondFuel r) (secondResult r).store :=
  Exec.seq (probe_exec r) (secondChoice_exec (probed r))
theorem secondFuel_bound (r : State) : secondFuel r ≤ 7 * r.core.pending.length + 35 := by
  have read := probeFuel_bound r
  have choice := secondChoiceFuel_bound (probed r)
  unfold secondFuel
  omega

def firstChoice : Block 16 := .branch 8 second second emitFirst
def firstChosen (r : State) : State :=
  if ForwardEdge.present r.registers.output then emitted 0 r else secondResult r
def firstChoiceFuel (r : State) : Nat :=
  1 + if ForwardEdge.present r.registers.output then 2 else secondFuel r
theorem firstChoice_exec (r : State) :
    Exec firstChoice r.store (firstChoiceFuel r) (firstChosen r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 16) r.store second emitFirst
    (secondFuel r) 2 (secondResult r).store (emitted 0 r).store (second_exec r) (emitFirst_exec r)
  change Exec firstChoice r.store (1 + if ForwardEdge.present r.registers.output then 2 else secondFuel r)
    (if ForwardEdge.present r.registers.output then (emitted 0 r).store else (secondResult r).store) at checked
  cases h : ForwardEdge.present r.registers.output <;>
    simpa only [firstChoice, firstChoiceFuel, firstChosen, h, Bool.false_eq_true, ite_false, ite_true] using checked
theorem firstChoiceFuel_bound (r : State) : firstChoiceFuel r ≤ 7 * r.core.pending.length + 36 := by
  have bound := secondFuel_bound r
  unfold firstChoiceFuel
  cases ForwardEdge.present r.registers.output <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

def choose : Block 16 := .seq probe firstChoice
def chosen (r : State) : State := firstChosen (probed r)
def chooseFuel (r : State) : Nat := probeFuel r + firstChoiceFuel (probed r)
theorem choose_exec (r : State) : Exec choose r.store (chooseFuel r) (chosen r).store :=
  Exec.seq (probe_exec r) (firstChoice_exec (probed r))
theorem chooseFuel_bound (r : State) : chooseFuel r ≤ 14 * r.core.pending.length + 66 := by
  have first := probeFuel_bound r
  have next := probed_pending_bound r
  have rest := firstChoiceFuel_bound (probed r)
  unfold chooseFuel
  omega
theorem chosen_fields (r : State) :
    (chosen r).formula = r.formula ∧ (chosen r).remaining = r.remaining ∧
    (chosen r).index = r.index ∧ (chosen r).core.variables = r.core.variables ∧
    (chosen r).core.buffer = r.core.buffer := by
  unfold chosen firstChosen
  split
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · unfold secondResult secondChosen
    split <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem chosen_output_length (r : State) : (chosen r).registers.output.length ≤ 3 := by
  unfold chosen firstChosen
  split
  · change 1 ≤ 3
    omega
  · unfold secondResult secondChosen
    split
    · change 2 ≤ 3
      omega
    · change 3 ≤ 3
      omega

def value (first middle target : Nat) : Nat := if first == target then 0 else if middle == target then 1 else 2
theorem chosen_canonical (r : State) (first middle : CNFLiteral) (suffix : BitString) (target : Nat)
    (pending : r.core.pending = NANDFrontend.literalBits first.positive first.variableIndex ++
      NANDFrontend.literalBits middle.positive middle.variableIndex ++ suffix)
    (index : r.index = List.replicate target true) :
    (chosen r).registers.output = TableOwner.answer (some (value first.variableIndex middle.variableIndex target)) := by
  have firstRead := probed_canonical r first
    (NANDFrontend.literalBits middle.positive middle.variableIndex ++ suffix) target
    (pending.trans (List.append_assoc _ _ _)) index
  have firstFlag : ForwardEdge.present (probed r).registers.output = (first.variableIndex == target) := by
    rw [firstRead.1]
    rfl
  have middleRead := probed_canonical (probed r) middle suffix target firstRead.2
    ((probed_fields r).2.2.1.trans index)
  have middleFlag : ForwardEdge.present (probed (probed r)).registers.output = (middle.variableIndex == target) := by
    rw [middleRead.1]
    rfl
  unfold chosen firstChosen
  rw [firstFlag]
  cases hf : first.variableIndex == target <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · unfold secondResult secondChosen
    rw [middleFlag]
    cases hm : middle.variableIndex == target <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, value, hf, hm] <;> rfl
  · simp only [value, hf, ite_true]
    rfl

end PNP.Concrete.NormalizerBlocks.CacheSlot

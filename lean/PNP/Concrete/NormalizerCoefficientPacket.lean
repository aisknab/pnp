/-
Copyright (c) 2026 PNP Labs.

Serialize an ordered coefficient list with its actual unary count.
The two reversals preserve repeated rows and the exact source list order.
-/
import PNP.Concrete.NormalizerCoefficientCompanion

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence

def reverseRoutine : Routine where
  block := liftCore ClauseQuery.reverseLoop
  result r := r.withRegisters {r.registers with excess := [], output := r.registers.excess.reverse ++ r.registers.output}
  fuel r := 4 * r.registers.excess.length + 1
  bound := .linear 4 1
  exec r := liftCore_exec _ r _ _ (ClauseQuery.reverse_exec r.registers r.registers.excess)
  cost r n bounded := by
    have size := Store.get_length_le r.store (3 : Fin 24) bounded
    change r.registers.excess.length ≤ n at size
    change 4 * r.registers.excess.length + 1 ≤ 4 * n + 1
    omega
def prepareFinish : Routine where
  block := .seq (.action (.copy 3 11)) (.action (.clear 8))
  result r := r.withRegisters {r.registers with excess := r.buffer,output := []}
  fuel _ := 2
  bound := .constant 2
  exec _ := Exec.seq (.action _ _) (.action _ _)
  cost _ _ _ := Nat.le_refl 2
def prepareCount : Routine where
  block := .seq (.action (.push 8 false)) (.action (.copy 3 10))
  result r := r.withRegisters {r.registers with excess := r.count,output := false::r.registers.output}
  fuel _ := 2
  bound := .constant 2
  exec _ := Exec.seq (.action _ _) (.action _ _)
  cost _ _ _ := Nat.le_refl 2
def finish : Routine :=
  Routine.seq prepareFinish (Routine.seq reverseRoutine (Routine.seq prepareCount reverseRoutine))
theorem finish_result (r : State) :
    finish.result r = r.withRegisters {r.registers with excess := [], output := r.count.reverse ++ false::r.buffer.reverse} := by
  change r.withRegisters {r.registers with excess := [], output := r.count.reverse ++ false::(r.buffer.reverse ++ [])} = _
  rw [List.append_nil]
theorem finish_output (r : State) :
    (finish.result r).registers.output = r.count.reverse ++ false::r.buffer.reverse := by
  rw [finish_result]
  rfl
theorem finish_data (r : State) : (finish.result r).data = r.data := by rw [finish_result]; rfl

def started (r : State) : State :=
  r.withDense {r.core.core with core := {r.core.core.core with variables := [],buffer := []}}
def start : Routine where
  block := .seq (.action (.clear 10)) (.action (.clear 11))
  result := started
  fuel _ := 2
  bound := .constant 2
  exec _ := Exec.seq (.action _ _) (.action _ _)
  cost _ _ _ := Nat.le_refl 2
theorem start_data (r : State) : (start.result r).data = r.data := rfl
theorem start_indices (r : State) :
    (start.result r).variableIndex = r.variableIndex ∧
    (start.result r).auxiliary = r.auxiliary := ⟨rfl,rfl⟩
def packet (routine : Routine) : Routine := Routine.seq start (Routine.seq routine finish)
def encodeRows (rows : List Row) : BitString :=
  List.replicate rows.length true ++ false::stream rows
theorem reverse_replicate (n : Nat) : (List.replicate n true).reverse = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ,List.reverse_cons,ih]
      have joined := replicate_sum n 1
      change List.replicate n true ++ List.replicate 1 true = List.replicate (n+1) true
      exact joined.symm
theorem packet_output (routine : Routine) (r : State) (rows : List Row)
    (emitted : Emits (started r) (routine.result (started r)) rows) :
    ((packet routine).result r).registers.output = encodeRows rows := by
  have count := emitted.1
  have bytes := emitted.2
  change (routine.result (started r)).count = List.replicate rows.length true ++ [] at count
  change (routine.result (started r)).buffer = (stream rows).reverse ++ [] at bytes
  rw [List.append_nil] at count bytes
  change (finish.result (routine.result (started r))).registers.output = _
  rw [finish_output,count,bytes,reverse_replicate,List.reverse_reverse]
  rfl
theorem packet_data (routine : Routine) (kept : ∀ r, (routine.result r).data = r.data) (r : State) :
    ((packet routine).result r).data = r.data :=
  Routine.seq_data _ _ start_data (Routine.seq_data _ _ kept finish_data) r

end PNP.Concrete.NormalizerBlocks.Coefficient

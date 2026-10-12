/-
Copyright (c) 2026 PNP Labs.

Append one complete row packet to the outer reversed buffer. Only the new
packet is traversed; previous output is retained without rescanning it.
-/
import PNP.Concrete.NormalizerSystemRowsState

namespace PNP.Concrete.NormalizerBlocks.SystemRows
open BitRegister Occurrence

def prepareAppend : Block 29 := .seq (.action (.copy 3 8)) (.action (.copy 8 28))
def appendPrepared (r : State) : State :=
  r.withCore (r.core.withRegisters {r.registers with excess := r.registers.output,output := r.buffer})
theorem prepareAppend_exec (r : State) : Exec prepareAppend r.store 2 (appendPrepared r).store :=
  Exec.seq (.action _ _) (.action _ _)
def appendReversed (r : State) : State :=
  (appendPrepared r).withCore (Coefficient.reverseRoutine.result (appendPrepared r).core)
def saveAppend : Block 29 := .seq (.action (.copy 28 8)) (.action (.push 27 true))
def appended (r : State) : State :=
  {core := r.core.withRegisters {r.registers with excess := [],output := r.registers.output.reverse ++ r.buffer},
   rows := r.rows,remaining := r.remaining,counter := r.counter,count := true::r.count,
   buffer := r.registers.output.reverse ++ r.buffer}
theorem saveAppend_exec (r : State) :
    Exec saveAppend (appendReversed r).store 2 (appended r).store :=
  Exec.seq (.action _ _) (.action _ _)
def append : Block 29 :=
  .seq prepareAppend (.seq (liftCore Coefficient.reverseRoutine.block) saveAppend)
def appendFuel (r : State) : Nat := 4 * r.registers.output.length + 5
theorem append_exec (r : State) : Exec append r.store (appendFuel r) (appended r).store := by
  have reversed := liftCore_exec _ (appendPrepared r) _ _ (Coefficient.reverseRoutine.exec _)
  have checked := Exec.seq (prepareAppend_exec r) (Exec.seq reversed (saveAppend_exec r))
  change Exec append r.store (2 + ((4 * r.registers.output.length + 1) + 2)) (appended r).store at checked
  have cost : 2 + ((4 * r.registers.output.length + 1) + 2) = appendFuel r := by unfold appendFuel; omega
  rw [cost] at checked
  exact checked
theorem appended_shared (r : State) : (appended r).shared = r.shared := rfl
theorem appended_frame (r : State) :
    (appended r).rows = r.rows ∧ (appended r).remaining = r.remaining ∧
    (appended r).counter = r.counter ∧ (appended r).count = true::r.count ∧
    (appended r).buffer = r.registers.output.reverse ++ r.buffer := ⟨rfl,rfl,rfl,rfl,rfl⟩

def emit (routine : Coefficient.Routine) : Block 29 := .seq (run routine) append
def emitted (routine : Coefficient.Routine) (r : State) : State := appended (result routine r)
def emitFuel (routine : Coefficient.Routine) (r : State) : Nat :=
  fuel routine r + appendFuel (result routine r)
theorem emit_exec (routine : Coefficient.Routine) (r : State) :
    Exec (emit routine) r.store (emitFuel routine r) (emitted routine r).store :=
  Exec.seq (run_exec routine r) (append_exec (result routine r))
theorem emitted_shared (routine : Coefficient.Routine)
    (kept : ∀ r, (routine.result r).data = r.data) (r : State) :
    (emitted routine r).shared = r.shared :=
  (appended_shared (result routine r)).trans (result_shared routine kept r)
theorem emitted_frame (routine : Coefficient.Routine) (r : State) :
    (emitted routine r).rows = r.rows ∧ (emitted routine r).remaining = r.remaining ∧
    (emitted routine r).counter = r.counter ∧ (emitted routine r).count = true::r.count ∧
    (emitted routine r).buffer = (result routine r).registers.output.reverse ++ r.buffer :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem emitFuel_bound (routine : Coefficient.Routine) (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    emitFuel routine r ≤ 4*n + 5*routine.bound.eval n + 24 := by
  have work := fuel_bound routine r n fixed index
  have output := result_output_bound routine r n fixed index
  unfold emitFuel appendFuel
  omega
theorem emitted_buffer_length (routine : Coefficient.Routine) (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    (emitted routine r).buffer.length ≤ n + routine.bound.eval n + r.buffer.length := by
  have output := result_output_bound routine r n fixed index
  rw [(emitted_frame routine r).2.2.2.2,List.length_append,List.length_reverse]
  omega

end PNP.Concrete.NormalizerBlocks.SystemRows

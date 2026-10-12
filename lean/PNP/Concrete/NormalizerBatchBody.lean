/-
Copyright (c) 2026 PNP Labs.

One fixed eleven-register update-driver body. The two extra registers retain
the pending encoded updates and the current table while the verified
nine-register header and writer blocks execute. No function-valued instruction
or data-dependent program is introduced.
-/

import PNP.Concrete.NormalizerBatchHeaders
import PNP.Concrete.NormalizerRegisterFrame

namespace PNP.Concrete.NormalizerBlocks.TableBatch

open BitRegister

structure State where
  core : Occurrence.Registers
  pending : BitString
  table : BitString
deriving Repr

def State.frame (r : State) : Store 2 := .cons r.pending (.cons r.table .nil)
def State.store (r : State) : Store 11 := Frame.join r.core.store r.frame

def reset : Block 11 :=
  .seq (.action (.copy 0 9)) (.seq (.action (.clear 1)) (.seq (.action (.clear 2))
    (.seq (.action (.clear 3)) (.seq (.action (.clear 4)) (.seq (.action (.clear 5))
      (.seq (.action (.clear 6)) (.seq (.action (.clear 7)) (.action (.clear 8)))))))))

def resetState (r : State) : State := ⟨Occurrence.initialRegisters r.pending, r.pending, r.table⟩

theorem reset_exec (r : State) : Exec reset r.store 9 (resetState r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))))))))

def parse : Block 11 := .seq reset (Frame.block 2 TableWrite.headers)
def parsed (r : State) : State := ⟨TableWrite.prepared r.pending, r.pending, r.table⟩
def parseFuel (r : State) : Nat := 9 + TableWrite.headerFuel r.pending

theorem parse_exec (r : State) : Exec parse r.store (parseFuel r) (parsed r).store :=
  Exec.seq (reset_exec r) (Frame.execution (TableWrite.headers_exec r.pending) r.frame)

def setup : Block 11 := .seq (.action (.copy 9 0)) (.action (.copy 0 10))
def ready (r : State) : State := ⟨{r.core with input := r.table}, r.core.input, r.table⟩

theorem setup_exec (r : State) : Exec setup r.store 2 (ready r).store :=
  Exec.seq (.action _ _) (.action _ _)

def write : Block 11 := Frame.block 2 (.seq TableWrite.loop TableWrite.pack)
def written (r : State) : State :=
  ⟨TableWrite.packed (TableWrite.queryResult r.core).state, r.pending, r.table⟩
def writeFuel (r : State) : Nat :=
  (TableWrite.queryResult r.core).fuel + TableWrite.packFuel (TableWrite.queryResult r.core).state

theorem write_exec (r : State) : Exec write r.store (writeFuel r) (written r).store :=
  Frame.execution (Exec.seq (TableWrite.query_exec r.core)
    (TableWrite.pack_exec (TableWrite.queryResult r.core).state)) r.frame

def save : Block 11 := .action (.copy 10 8)
def saved (r : State) : State := ⟨r.core, r.pending, r.core.output⟩

theorem save_exec (r : State) : Exec save r.store 1 (saved r).store := .action _ _

def staged (r : State) : State := ready (parsed r)
def body : Block 11 := .seq parse (.seq setup (.seq write save))
def result (r : State) : State := saved (written (staged r))
def bodyFuel (r : State) : Nat := parseFuel r + (2 + (writeFuel (staged r) + 1))

theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (result r).store :=
  Exec.seq (parse_exec r) (Exec.seq (setup_exec (parsed r))
    (Exec.seq (write_exec (staged r)) (save_exec (written (staged r)))))

theorem pending_bound (r : State) : (result r).pending.length ≤ r.pending.length :=
  TableWrite.prepared_input_bound r.pending

theorem pending_strict (r : State) (nonempty : r.pending ≠ []) :
    (result r).pending.length < r.pending.length :=
  TableWrite.prepared_input_strict r.pending nonempty

theorem buffer_bound (r : State) :
    (TableWrite.queryResult (staged r).core).state.excess.length ≤
      r.table.length + 18 * r.pending.length + 40 := by
  have growth := TableWrite.query_growth_bound (staged r).core
  change (TableWrite.queryResult (staged r).core).state.excess.length ≤
    (TableWrite.prepared r.pending).excess.length + r.table.length +
      2 * (TableWrite.prepared r.pending).target.length + 8 at growth
  rw [TableWrite.prepared_excess] at growth
  have value := TableWrite.prepared_target_bound r.pending
  simp only [List.length_nil] at growth
  omega

theorem table_growth (r : State) :
    (result r).table.length ≤ r.table.length + 18 * r.pending.length + 40 := by
  simpa only [result, saved, written, TableWrite.packed, List.length_reverse] using buffer_bound r

def costBound (pending table : Nat) : Nat :=
  (36 * pending + 82) * (table + 1) + 80 * pending + 4 * table + 191

theorem bodyFuel_bound (r : State) : bodyFuel r ≤ costBound r.pending.length r.table.length := by
  have parsed := TableWrite.headerFuel_bound r.pending
  have value := TableWrite.prepared_target_bound r.pending
  have scan : (TableWrite.queryResult (staged r).core).fuel ≤
      (4 * (TableWrite.prepared r.pending).target.length + 18) * (r.table.length + 1) + 1 :=
    TableWrite.query_fuel_bound (staged r).core
  have factor : 4 * (TableWrite.prepared r.pending).target.length + 18 ≤ 36 * r.pending.length + 82 := by omega
  have product := Nat.mul_le_mul factor (Nat.le_refl (r.table.length + 1))
  have buffer := buffer_bound r
  simp only [bodyFuel, parseFuel, writeFuel, TableWrite.packFuel, costBound]
  omega

end PNP.Concrete.NormalizerBlocks.TableBatch

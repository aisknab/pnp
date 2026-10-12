/-
Copyright (c) 2026 PNP Labs.

The E-row filter reads the actual mode cell and compares the complete runtime
row and failure indices. Only unmatched, nonfailed rows are retained.
-/
import PNP.Concrete.NormalizerCoefficientEntry

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence

def boolRoutine (value : Bool) : Routine where
  block := liftCore (TraceCount.emit value)
  result r := r.withRegisters (TraceCount.emitted value r.registers)
  fuel _ := 2
  bound := .constant 2
  exec r := liftCore_exec _ r _ _ (TraceCount.emit_exec value _)
  cost _ _ _ := Nat.le_refl 2
def prepareRowComparison : Routine where
  block := .seq (.action (.copy 1 22)) (.seq (.action (.copy 2 20)) (.action (.clear 3)))
  result r := r.withRegisters {r.registers with target := r.row,remaining := r.failed,excess := []}
  fuel _ := 3
  bound := .constant 3
  exec _ := Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  cost _ _ _ := Nat.le_refl 3
def counterComparison : Routine where
  block := liftCore TraceCount.block
  result r := r.withRegisters (TraceCount.result r.registers)
  fuel r := TraceCount.fuel r.registers
  bound := .linear 4 5
  exec r := liftCore_exec _ r _ _ (TraceCount.block_exec _)
  cost r n bounded := by
    have cost := TraceCount.fuel_bound r.registers
    have size := Store.get_length_le r.store (1 : Fin 24) bounded
    change r.registers.target.length ≤ n at size
    change TraceCount.fuel r.registers ≤ 4*n+5
    omega
def sameRows : Routine := Routine.seq prepareRowComparison counterComparison
theorem sameRows_output (r : State) :
    (sameRows.result r).registers.output = [r.row.length == r.failed.length] :=
  TraceCount.result_output (prepareRowComparison.result r).registers rfl
theorem sameRows_data (r : State) : (sameRows.result r).data = r.data := rfl
def differentRows : Routine := Routine.seq sameRows (compareSign false)
theorem differentRows_output (r : State) :
    (differentRows.result r).registers.output = [!(r.row.length == r.failed.length)] := by
  change [decide (ForwardEdge.present (sameRows.result r).registers.output = false)] = _
  rw [sameRows_output]
  cases r.row.length == r.failed.length <;> rfl
theorem differentRows_data (r : State) : (differentRows.result r).data = r.data := rfl

attribute [local irreducible] differentRows
def eligibleRow : Routine :=
  Routine.seq (queryRoutine .mode .row) (Routine.choose 8 differentRows (boolRoutine false))
def eligibleValue (cell : Option Nat) (row failed : Nat) : Bool :=
  cell.isNone && !(row == failed)
theorem eligibleRow_data (r : State) : (eligibleRow.result r).data = r.data :=
  Routine.seq_data _ _ (queried_data .mode .row)
    (Routine.choose_data 8 _ _ differentRows_data (by intro r; rfl)) r
theorem eligibleRow_canonical (r : State) (modes : MatchingTable.Entries) (row failed : Nat)
    (table : r.core.target = MatchingTable.encode modes)
    (rowRead : r.row = List.replicate row true)
    (failedRead : r.failed = List.replicate failed true) :
    (eligibleRow.result r).registers.output = [eligibleValue (MatchingTable.read modes row) row failed] := by
  let before := (queryRoutine .mode .row).result r
  have read := query_canonical .mode .row r modes row table rowRead
  change before.registers.output = TableOwner.answer (MatchingTable.read modes row) at read
  change ((Routine.choose 8 differentRows (boolRoutine false)).result before).registers.output = _
  rw [choose_output_result,read]
  cases h : MatchingTable.read modes row with
  | none =>
      change (differentRows.result before).registers.output = [!(row == failed)]
      rw [differentRows_output]
      change [!(r.row.length == r.failed.length)] = _
      rw [rowRead,failedRead,List.length_replicate,List.length_replicate]
  | some value => rfl
theorem eligibleValue_iff (cell : Option Nat) (row failed : Nat) :
    eligibleValue cell row failed = true ↔ cell = none ∧ row ≠ failed := by
  cases cell with
  | none =>
      change (!(row == failed)) = true ↔ (none : Option Nat) = none ∧ row ≠ failed
      by_cases h : row = failed
      · subst failed
        have same : (row == row) = true := beq_iff_eq.mpr rfl
        rw [same]
        simp only [Bool.not_true,Bool.false_eq_true,ne_eq,not_true_eq_false,and_false]
      · have different : (row == failed) = false := beq_eq_false_iff_ne.mpr h
        rw [different]
        exact ⟨fun _ => ⟨rfl,h⟩,fun _ => rfl⟩
  | some value =>
      change false = true ↔ (some value : Option Nat) = none ∧ row ≠ failed
      simp only [Bool.false_eq_true,Option.some_ne_none,false_and]

end PNP.Concrete.NormalizerBlocks.Coefficient

/-
Copyright (c) 2026 PNP Labs.

Exact complete seen-table construction from trace nodes. The phase clears
any old buffer, consumes the actual trace and serializes the derived table.
Its polynomial bound covers scan, growth and final reversal together.
-/
import PNP.Concrete.NormalizerSeenScan

namespace PNP.Concrete.NormalizerBlocks.SeenTrace
open BitRegister

theorem scan_buffer (fuel : Nat) (r : State) (trace : List TraceData.Row)
    (read : r.core.pending = TraceData.encode trace) (enough : r.core.pending.length < fuel) :
    (scan fuel r).state.buffer = (bytes (value trace)).reverse ++ r.buffer := by
  induction trace generalizing fuel r with
  | nil =>
      rw [scan_empty fuel r read]
      rfl
  | cons row rest ih =>
      have nonempty : r.core.pending ≠ [] := by
        rw [read]
        change (row.1.positive :: _) ≠ []
        intro h
        cases h
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          rw [scan_step fuel r nonempty]
          have step := body_canonical r row (TraceData.encode rest) read
          have remaining : (bodyResult r).core.pending.length < fuel := by
            have shorter := body_shorter r nonempty
            omega
          rw [ih fuel (bodyResult r) step.1 remaining, step.2]
          simp only [value, List.map_cons, bytes_cons, List.reverse_append, List.append_assoc]

theorem whole_buffer (r : State) (trace : List TraceData.Row) (read : r.core.pending = TraceData.encode trace) :
    (whole r).state.buffer = (bytes (value trace)).reverse ++ r.buffer :=
  scan_buffer _ r trace read (Nat.lt_succ_self _)

def prepareFinish : Block 23 := .action (.copy 3 21)
def finishPrepared (r : State) : State := r.withRegisters {r.registers with excess := r.buffer}
theorem prepareFinish_exec (r : State) : Exec prepareFinish r.store 1 (finishPrepared r).store := .action _ _

def pack : Block 23 := TracePath.liftCore ClauseQuery.pack
def packed (r : State) : State := r.withRegisters (ClauseQuery.packed r.registers)
theorem pack_exec (r : State) : Exec pack r.store (ClauseQuery.packFuel r.registers) (packed r).store :=
  TracePath.liftCore_exec _ r _ _ (ClauseQuery.pack_exec r.registers)

def finish : Block 23 := .seq prepareFinish pack
def finished (r : State) : State := packed (finishPrepared r)
def finishFuel (r : State) : Nat := 4 * r.buffer.length + 13
theorem finish_exec (r : State) : Exec finish r.store (finishFuel r) (finished r).store := by
  have checked := Exec.seq (prepareFinish_exec r) (pack_exec (finishPrepared r))
  change Exec finish r.store (1 + (4 * r.buffer.length + 12)) (finished r).store at checked
  have cost : 1 + (4 * r.buffer.length + 12) = finishFuel r := by unfold finishFuel; omega
  rw [cost] at checked
  exact checked
theorem finished_output (r : State) : (finished r).registers.output = r.buffer.reverse ++ [true, false] := rfl

def front : Block 23 := .seq TracePath.resetPath loop
def frontResult (r : State) : State := (whole (TracePath.pathReset r)).state
def frontFuel (r : State) : Nat := 3 + (whole (TracePath.pathReset r)).fuel
theorem front_exec (r : State) : Exec front r.store (frontFuel r) (frontResult r).store :=
  Exec.seq (TracePath.resetPath_exec r) (whole_exec (TracePath.pathReset r))

def phase : Block 23 := .seq front finish
def phaseResult (r : State) : State := finished (frontResult r)
def phaseFuel (r : State) : Nat := frontFuel r + finishFuel (frontResult r)
theorem phase_exec (r : State) : Exec phase r.store (phaseFuel r) (phaseResult r).store :=
  Exec.seq (front_exec r) (finish_exec (frontResult r))

theorem frontFuel_bound (r : State) :
    frontFuel r ≤ (28 * r.core.pending.length + 80) * (r.core.pending.length + 1) + 4 := by
  have checked := whole_fuel_bound (TracePath.pathReset r)
  change (whole (TracePath.pathReset r)).fuel ≤ (28 * r.core.pending.length + 80) * (r.core.pending.length + 1) + 1 at checked
  unfold frontFuel
  omega

theorem phaseFuel_bound (r : State) (bound : Nat) (bounded : r.store.Bounded bound) :
    phaseFuel r ≤ 4 * bound + 5 * ((28 * r.core.pending.length + 80) * (r.core.pending.length + 1) + 4) + 13 := by
  have frontBound := (front_exec r).bounded bound bounded
  have buffer := Store.get_length_le (frontResult r).store (21 : Fin 23) frontBound
  change (frontResult r).buffer.length ≤ bound + frontFuel r at buffer
  have first := frontFuel_bound r
  unfold phaseFuel finishFuel
  omega

theorem phase_preserves (r : State) :
    (phaseResult r).core.graph.core.formula = r.core.graph.core.formula ∧
      (phaseResult r).core.graph.core.matching = r.core.graph.core.matching :=
  scan_preserves ((TracePath.pathReset r).core.pending.length + 1) (TracePath.pathReset r)

theorem phase_canonical (r : State) (trace : List TraceData.Row)
    (read : r.core.pending = TraceData.encode trace) :
    (phaseResult r).registers.output = MatchingTable.encode (value trace) := by
  rw [phaseResult, finished_output]
  have checked := whole_buffer (TracePath.pathReset r) trace read
  change (frontResult r).buffer = (bytes (value trace)).reverse ++ [] at checked
  rw [checked, List.append_nil, List.reverse_reverse, encode_bytes]

end PNP.Concrete.NormalizerBlocks.SeenTrace

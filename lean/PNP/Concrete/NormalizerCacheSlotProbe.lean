/-
Copyright (c) 2026 PNP Labs.

Read and compare an actual encoded literal with a protected unary index.
The comparison is a finite counter computation, not a supplied predicate.
Malformed words terminate under the same bound as canonical inputs.
-/
import PNP.Concrete.NormalizerDenseRead
import PNP.Concrete.NormalizerTraceCount

namespace PNP.Concrete.NormalizerBlocks.CacheSlot
open BitRegister Occurrence
abbrev State := DenseClauses.State

def readLiteral : Block 16 := DenseClauses.liftCompact CompactClause.readLiteral
def literalRead (r : State) : State := r.withCompact (CompactClause.literalRead r.core)
theorem readLiteral_exec (r : State) :
    Exec readLiteral r.store (CompactClause.readFuel r.core) (literalRead r).store :=
  DenseClauses.liftCompact_exec _ r _ _ (CompactClause.readLiteral_exec r.core)

def loadComparison : Block 16 := .seq (.action (.copy 2 15)) (.action (.clear 3))
def comparisonLoaded (r : State) : State :=
  r.withRegisters {r.registers with remaining := r.index, excess := []}
theorem loadComparison_exec (r : State) :
    Exec loadComparison r.store 2 (comparisonLoaded r).store :=
  Exec.seq (.action _ _) (.action _ _)
def comparison : Block 16 := .seq loadComparison (DenseClauses.liftCore TraceCount.block)
def compared (r : State) : State :=
  (comparisonLoaded r).withRegisters (TraceCount.result (comparisonLoaded r).registers)
def comparisonFuel (r : State) : Nat := 2 + TraceCount.fuel (comparisonLoaded r).registers
theorem comparison_exec (r : State) :
    Exec comparison r.store (comparisonFuel r) (compared r).store :=
  Exec.seq (loadComparison_exec r)
    (DenseClauses.liftCore_exec _ (comparisonLoaded r) _ _ (TraceCount.block_exec _))
theorem compared_output (r : State) :
    (compared r).registers.output = [r.registers.target.length == r.index.length] :=
  TraceCount.result_output (comparisonLoaded r).registers rfl
theorem comparisonFuel_bound (r : State) : comparisonFuel r ≤ 4 * r.registers.target.length + 7 := by
  have bound := TraceCount.fuel_bound (comparisonLoaded r).registers
  change TraceCount.fuel (comparisonLoaded r).registers ≤ 4 * r.registers.target.length + 5 at bound
  unfold comparisonFuel
  omega

def probe : Block 16 := .seq readLiteral comparison
def probed (r : State) : State := compared (literalRead r)
def probeFuel (r : State) : Nat := CompactClause.readFuel r.core + comparisonFuel (literalRead r)
theorem probe_exec (r : State) : Exec probe r.store (probeFuel r) (probed r).store :=
  Exec.seq (readLiteral_exec r) (comparison_exec (literalRead r))
theorem probed_fields (r : State) :
    (probed r).formula = r.formula ∧ (probed r).remaining = r.remaining ∧
    (probed r).index = r.index ∧ (probed r).core.variables = r.core.variables ∧
    (probed r).core.buffer = r.core.buffer ∧
    (probed r).core.pending = CompactClause.next r.core.pending := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem probed_output (r : State) :
    (probed r).registers.output = [(CompactClause.index r.core.pending).length == r.index.length] := by
  exact compared_output (literalRead r)
theorem probeFuel_bound (r : State) : probeFuel r ≤ 7 * r.core.pending.length + 30 := by
  have read := CompactClause.readFuel_bound r.core
  have compare := comparisonFuel_bound (literalRead r)
  have size := CompactClause.index_bound r.core.pending
  change comparisonFuel (literalRead r) ≤ 4 * (CompactClause.index r.core.pending).length + 7 at compare
  unfold probeFuel
  omega
theorem probed_pending_bound (r : State) : (probed r).core.pending.length ≤ r.core.pending.length := by
  rw [(probed_fields r).2.2.2.2.2]
  cases h : r.core.pending with
  | nil => exact Nat.le_refl _
  | cons bit rest =>
      have shorter := CompactClause.next_shorter r.core.pending (by rw [h]; intro impossible; cases impossible)
      rw [h] at shorter
      exact Nat.le_of_lt shorter
theorem probed_canonical (r : State) (literal : CNFLiteral) (suffix : BitString) (target : Nat)
    (pending : r.core.pending = NANDFrontend.literalBits literal.positive literal.variableIndex ++ suffix)
    (index : r.index = List.replicate target true) :
    (probed r).registers.output = [literal.variableIndex == target] ∧
      (probed r).core.pending = suffix := by
  have read := CompactClause.read_canonical r.core literal suffix pending
  constructor
  · rw [probed, compared_output]
    change [(CompactClause.literalRead r.core).core.target.length == r.index.length] = _
    rw [read.1, index, List.length_replicate, List.length_replicate]
  · exact read.2.1

end PNP.Concrete.NormalizerBlocks.CacheSlot

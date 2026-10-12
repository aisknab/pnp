/-
Copyright (c) 2026 PNP Labs.

Read an optional natural-valued table cell from protected encoded bytes.
Both the indexed clause selection and the unary-value decoding execute
finite instructions. The table, traversal cursor and output buffer survive.
-/
import PNP.Concrete.NormalizerCacheOwnerFold
import PNP.Concrete.NormalizerMatchingValueCanonical

namespace PNP.Concrete.NormalizerBlocks.CacheCell
open BitRegister Occurrence
abbrev State := DenseClauses.State

def read : Block 16 :=
  .seq DenseClauses.query (.seq (DenseClauses.liftCore GraphQuery.handoff)
    (DenseClauses.liftCore MatchingValue.block))
def result (r : State) : State :=
  r.withRegisters (MatchingValue.result (DenseClauses.queried r).registers.output)
def fuel (r : State) : Nat :=
  DenseClauses.queryFuel r + (9 + MatchingValue.sourceSteps (DenseClauses.queried r).registers.output)
theorem read_exec (r : State) : Exec read r.store (fuel r) (result r).store :=
  Exec.seq (DenseClauses.query_exec r)
    (Exec.seq (DenseClauses.liftCore_exec _ (DenseClauses.queried r) _ _ (GraphQuery.handoff_exec _))
      (DenseClauses.liftCore_exec _ ((DenseClauses.queried r).withRegisters
        (initialRegisters (DenseClauses.queried r).registers.output)) _ _ (MatchingValue.block_exec _)))
theorem result_fields (r : State) :
    (result r).formula = r.formula ∧ (result r).remaining = r.remaining ∧
    (result r).index = r.index ∧ (result r).core.variables = r.core.variables ∧
    (result r).core.buffer = r.core.buffer := ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem fuel_bound (r : State) : fuel r ≤ 755 * r.formula.length + 83 * r.index.length + 1171 := by
  have query := DenseClauses.queryFuel_bound r
  have size := DenseClauses.query_output_bound r
  have decode := MatchingValue.sourceSteps_bound (DenseClauses.queried r).registers.output
  change MatchingValue.sourceSteps (DenseClauses.queried r).registers.output + 1 ≤
    3 * (DenseClauses.queried r).registers.output.length + 11 at decode
  unfold fuel
  omega
theorem output_bound (r : State) :
    (result r).registers.output.length ≤ 756 * r.formula.length + 84 * r.index.length + 1151 := by
  have decode := MatchingValue.polynomial_output_length (DenseClauses.queried r).registers.output
  rw [MatchingValue.polynomial_output] at decode
  change (result r).registers.output.length ≤
    (DenseClauses.queried r).registers.output.length +
      (3 * (DenseClauses.queried r).registers.output.length + 11) at decode
  have size := DenseClauses.query_output_bound r
  omega
theorem canonical (r : State) (table : MatchingTable.Entries) (index : Nat)
    (tableRead : r.formula = MatchingTable.encode table)
    (indexRead : r.index = List.replicate index true) :
    (result r).registers.output = TableOwner.answer (MatchingTable.read table index) := by
  have query := DenseClauses.query_canonical r index (MatchingTable.clauses table) indexRead tableRead
  rw [MatchingTable.clauses_read] at query
  change (MatchingValue.result (DenseClauses.queried r).registers.output).output = _
  rw [query,← MatchingValue.polynomial_output,MatchingValue.polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.CacheCell

/-
Copyright (c) 2026 PNP Labs.

Protected controller state for the source mode table: dense formula and
selected variables, original matching, dense row counter and matched target.
The matching entry is read by an actual indexed scan and unary decoder.
-/
import PNP.Concrete.NormalizerCacheSlotChoose
import PNP.Concrete.NormalizerCacheOwnerQuery
import PNP.Concrete.NormalizerMatchingValueCanonical

namespace PNP.Concrete.NormalizerBlocks.CacheMode
open BitRegister Occurrence

structure State where
  core : DenseClauses.State
  matching : BitString
  counter : BitString
  target : BitString
def State.frame (r : State) : Store 3 :=
  .cons r.matching (.cons r.counter (.cons r.target .nil))
def State.store (r : State) : Store 19 := Frame.join r.core.store r.frame
def State.registers (r : State) : Registers := r.core.registers
def State.withDense (r : State) (core : DenseClauses.State) : State := {r with core := core}
def State.withRegisters (r : State) (core : Registers) : State := r.withDense (r.core.withRegisters core)
def liftDense (body : Block 16) : Block 19 := Frame.block 3 body
theorem liftDense_exec (body : Block 16) (r : State) (fuel : Nat) (after : DenseClauses.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (liftDense body) r.store fuel (r.withDense after).store :=
  Frame.execution checked r.frame
def liftCore (body : Block 9) : Block 19 := liftDense (DenseClauses.liftCore body)
theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.registers.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withRegisters after).store :=
  liftDense_exec _ r _ _ (DenseClauses.liftCore_exec _ r.core _ _ checked)

def loadMatching : Block 19 := .action (.copy 0 16)
def matchingLoaded (r : State) : State := r.withRegisters {r.registers with input := r.matching}
theorem loadMatching_exec (r : State) : Exec loadMatching r.store 1 (matchingLoaded r).store := .action _ _
def resetMatching : Block 19 := liftDense DenseClauses.resetQuery
def matchingReset (r : State) : State := r.withDense (DenseClauses.queryReset r.core)
def setupMatching : Block 19 := liftDense DenseClauses.setupQuery
def matchingSetup (r : State) : State := r.withDense (DenseClauses.querySetup r.core)
def prepareMatching : Block 19 := .seq loadMatching (.seq resetMatching setupMatching)
def matchingPrepared (r : State) : State := r.withRegisters (GraphQuery.prepared [] r.core.index r.matching)
theorem prepareMatching_exec (r : State) : Exec prepareMatching r.store 13 (matchingPrepared r).store :=
  Exec.seq (loadMatching_exec r)
    (Exec.seq (liftDense_exec _ (matchingLoaded r) _ _ (DenseClauses.resetQuery_exec _))
      (liftDense_exec _ (matchingReset (matchingLoaded r)) _ _ (DenseClauses.setupQuery_exec _)))
def selectMatching : Block 19 := .seq prepareMatching (liftCore GraphQuery.selection)
def matchingSelected (r : State) : State :=
  r.withRegisters (GraphQuery.selected (GraphQuery.prepared [] r.core.index r.matching))
def selectionFuel (r : State) : Nat := 13 + GraphQuery.selectionFuel (GraphQuery.prepared [] r.core.index r.matching)
theorem selectMatching_exec (r : State) :
    Exec selectMatching r.store (selectionFuel r) (matchingSelected r).store :=
  Exec.seq (prepareMatching_exec r)
    (liftCore_exec _ (matchingPrepared r) _ _ (GraphQuery.selection_exec _))
theorem selectionFuel_bound (r : State) :
    selectionFuel r ≤ 188 * r.matching.length + 20 * r.core.index.length + 297 := by
  have checked := DenseClauses.selectionFuel_bound r.core.index r.matching
  unfold selectionFuel
  omega
theorem selection_output_bound (r : State) :
    (matchingSelected r).registers.output.length ≤
      189 * r.matching.length + 21 * r.core.index.length + 285 :=
  DenseClauses.query_output_bound {r.core with formula := r.matching}

def readMatching : Block 19 :=
  .seq selectMatching (.seq (liftCore GraphQuery.handoff) (liftCore MatchingValue.block))
def matchingRead (r : State) : State :=
  r.withRegisters (MatchingValue.result (matchingSelected r).registers.output)
def readFuel (r : State) : Nat :=
  selectionFuel r + (9 + MatchingValue.sourceSteps (matchingSelected r).registers.output)
theorem readMatching_exec (r : State) :
    Exec readMatching r.store (readFuel r) (matchingRead r).store :=
  Exec.seq (selectMatching_exec r)
    (Exec.seq (liftCore_exec _ (matchingSelected r) _ _ (GraphQuery.handoff_exec _))
      (liftCore_exec _ ((matchingSelected r).withRegisters (initialRegisters (matchingSelected r).registers.output))
        _ _ (MatchingValue.block_exec _)))
theorem readFuel_bound (r : State) :
    readFuel r ≤ 755 * r.matching.length + 83 * r.core.index.length + 1171 := by
  have scan := selectionFuel_bound r
  have size := selection_output_bound r
  have decoded := MatchingValue.sourceSteps_bound (matchingSelected r).registers.output
  change MatchingValue.sourceSteps (matchingSelected r).registers.output + 1 ≤
    3 * (matchingSelected r).registers.output.length + 11 at decoded
  unfold readFuel
  omega
theorem matchingRead_fields (r : State) :
    (matchingRead r).core.formula = r.core.formula ∧
    (matchingRead r).core.remaining = r.core.remaining ∧
    (matchingRead r).core.index = r.core.index ∧
    (matchingRead r).core.core.variables = r.core.core.variables ∧
    (matchingRead r).core.core.buffer = r.core.core.buffer ∧
    (matchingRead r).matching = r.matching ∧
    (matchingRead r).counter = r.counter ∧ (matchingRead r).target = r.target :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem matchingRead_canonical (r : State) (index : Nat) (table : MatchingTable.Entries)
    (indexRead : r.core.index = List.replicate index true)
    (matching : r.matching = MatchingTable.encode table) :
    (matchingRead r).registers.output = TableOwner.answer (MatchingTable.read table index) := by
  have selected := GraphQuery.selected_canonical 0 index (MatchingTable.clauses table)
  have query : (matchingSelected r).registers.output =
      Occurrence.encodeQuery 0 (MatchingTable.entryClause (MatchingTable.read table index)) := by
    change (GraphQuery.selected (GraphQuery.prepared [] r.core.index r.matching)).output = _
    rw [indexRead, matching]
    exact selected.trans (congrArg (Occurrence.encodeQuery 0) (MatchingTable.clauses_read table index))
  change (MatchingValue.result (matchingSelected r).registers.output).output = _
  rw [query, ← MatchingValue.polynomial_output, MatchingValue.polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.CacheMode

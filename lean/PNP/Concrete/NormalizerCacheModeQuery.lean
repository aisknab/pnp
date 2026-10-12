/-
Copyright (c) 2026 PNP Labs.

Derive the selected dense variable from an actual matching row, then read
the saved dense clause at its runtime ordinal and choose its literal slot.
Protected matching, formula, cursor and output buffer survive both scans.
-/
import PNP.Concrete.NormalizerCacheModeRead
import PNP.Concrete.NormalizerCacheSlotCall

namespace PNP.Concrete.NormalizerBlocks.CacheMode
open BitRegister Occurrence

def transport : Block 19 := .seq readMatching (liftDense CacheOwner.choose)
def transported (r : State) : State :=
  (matchingRead r).withDense (CacheOwner.chosen (matchingRead r).core)
def transportFuel (r : State) : Nat :=
  readFuel r + CacheOwner.chooseFuel (matchingRead r).core
theorem transport_exec (r : State) :
    Exec transport r.store (transportFuel r) (transported r).store :=
  Exec.seq (readMatching_exec r)
    (liftDense_exec _ (matchingRead r) _ _ (CacheOwner.choose_exec _))
theorem transported_fields (r : State) :
    (transported r).core.formula = r.core.formula ∧
    (transported r).core.remaining = r.core.remaining ∧
    (transported r).core.core.variables = r.core.core.variables ∧
    (transported r).core.core.buffer = r.core.core.buffer ∧
    (transported r).matching = r.matching ∧ (transported r).counter = r.counter := by
  have fields := CacheOwner.chosen_fields (matchingRead r).core
  exact ⟨fields.1,fields.2.1,fields.2.2.1,fields.2.2.2,rfl,rfl⟩
theorem transportFuel_bound (r : State) :
    transportFuel r ≤ 755 * r.matching.length + 83 * r.core.index.length +
      12 * r.core.core.variables.length + 1197 := by
  have read := readFuel_bound r
  have dense := CacheOwner.chooseFuel_bound (matchingRead r).core
  change CacheOwner.chooseFuel (matchingRead r).core ≤ 12 * r.core.core.variables.length + 26 at dense
  unfold transportFuel
  omega
def transportedValue (table : MatchingTable.Entries) (variables : List CNFLiteral) (index : Nat) : Option Nat :=
  (MatchingTable.read table index).bind (TableOwner.vertexOwner variables)
theorem transported_canonical (r : State) (index : Nat) (table : MatchingTable.Entries) (variables : List CNFLiteral)
    (indexRead : r.core.index = List.replicate index true)
    (matching : r.matching = MatchingTable.encode table)
    (selected : r.core.core.variables = SearchVertices.encodeVertices variables) :
    (transported r).registers.output = TableOwner.answer (transportedValue table variables index) :=
  CacheOwner.chosen_canonical (matchingRead r).core (MatchingTable.read table index) variables
    (matchingRead_canonical r index table indexRead matching) selected

def loadClause : Block 19 :=
  .seq (.action (.copy 18 8)) (.seq (.action (.pop 18)) (.action (.copy 15 17)))
def clauseLoaded (r : State) : State :=
  {r with core := {r.core with index := r.counter}, target := r.registers.output.tail}
theorem loadClause_exec (r : State) : Exec loadClause r.store 3 (clauseLoaded r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def readClause : Block 19 := .seq loadClause (liftDense DenseClauses.query)
def clauseRead (r : State) : State :=
  (clauseLoaded r).withDense (DenseClauses.queried (clauseLoaded r).core)
def readClauseFuel (r : State) : Nat := 3 + DenseClauses.queryFuel (clauseLoaded r).core
theorem readClause_exec (r : State) :
    Exec readClause r.store (readClauseFuel r) (clauseRead r).store :=
  Exec.seq (loadClause_exec r)
    (liftDense_exec _ (clauseLoaded r) _ _ (DenseClauses.query_exec _))
def loadTarget : Block 19 := .action (.copy 15 18)
def targetLoaded (r : State) : State := r.withDense {r.core with index := r.target}
theorem loadTarget_exec (r : State) : Exec loadTarget r.store 1 (targetLoaded r).store := .action _ _
def chooseSlot : Block 19 :=
  .seq readClause (.seq loadTarget (liftDense CacheSlot.call))
def slotChosen (r : State) : State :=
  (targetLoaded (clauseRead r)).withDense (CacheSlot.called (targetLoaded (clauseRead r)).core)
def chooseSlotFuel (r : State) : Nat :=
  readClauseFuel r + (1 + CacheSlot.callFuel (targetLoaded (clauseRead r)).core)
theorem chooseSlot_exec (r : State) :
    Exec chooseSlot r.store (chooseSlotFuel r) (slotChosen r).store :=
  Exec.seq (readClause_exec r)
    (Exec.seq (loadTarget_exec (clauseRead r))
      (liftDense_exec _ (targetLoaded (clauseRead r)) _ _ (CacheSlot.call_exec _)))
theorem slotChosen_fields (r : State) :
    (slotChosen r).core.formula = r.core.formula ∧
    (slotChosen r).core.remaining = r.core.remaining ∧
    (slotChosen r).core.core.variables = r.core.core.variables ∧
    (slotChosen r).core.core.buffer = r.core.core.buffer ∧
    (slotChosen r).matching = r.matching ∧ (slotChosen r).counter = r.counter := by
  have fields := CacheSlot.called_fields (targetLoaded (clauseRead r)).core
  exact ⟨fields.1,fields.2.1,fields.2.2.2.1,fields.2.2.2.2,rfl,rfl⟩
theorem chooseSlotFuel_bound (r : State) :
    chooseSlotFuel r ≤ 2834 * r.core.formula.length + 314 * r.counter.length + 4359 := by
  have read := DenseClauses.queryFuel_bound (clauseLoaded r).core
  have size := DenseClauses.query_output_bound (clauseLoaded r).core
  have choice := CacheSlot.callFuel_bound (targetLoaded (clauseRead r)).core
  change DenseClauses.queryFuel (clauseLoaded r).core ≤
    188 * r.core.formula.length + 20 * r.counter.length + 297 at read
  change (clauseRead r).registers.output.length ≤
    189 * r.core.formula.length + 21 * r.counter.length + 285 at size
  change CacheSlot.callFuel (targetLoaded (clauseRead r)).core ≤
    14 * (clauseRead r).registers.output.length + 68 at choice
  unfold chooseSlotFuel readClauseFuel
  omega
theorem slotChosen_output_length (r : State) : (slotChosen r).registers.output.length ≤ 3 :=
  CacheSlot.called_output_length (targetLoaded (clauseRead r)).core
theorem slotChosen_canonical (r : State) (row target : Nat) (formula : List (List CNFLiteral))
    (counter : r.counter = List.replicate row true)
    (dense : r.core.formula = GraphQuery.clauseData formula)
    (found : r.registers.output = TableOwner.answer (some target)) :
    (slotChosen r).registers.output =
      TableOwner.answer (some (CacheSlot.encodedValue (formula[row]?.getD []) target)) := by
  apply CacheSlot.called_canonical (targetLoaded (clauseRead r)).core (formula[row]?.getD []) target
  · exact DenseClauses.query_canonical (clauseLoaded r).core row formula counter dense
  · change r.registers.output.tail = List.replicate target true
    rw [found]
    rfl

end PNP.Concrete.NormalizerBlocks.CacheMode

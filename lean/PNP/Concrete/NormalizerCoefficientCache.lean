/-
Copyright (c) 2026 PNP Labs.

Uniform owner, slot and mode queries for source coefficient construction.
The existing owner/slot readers are reused. Mode lookup reads the third
protected table without overwriting the formula or any other cache field.
-/
import PNP.Concrete.NormalizerCacheSigmaRead

namespace PNP.Concrete.NormalizerBlocks.CoefficientCache
open BitRegister Occurrence
abbrev State := CacheSigma.State

def loadMode : Block 19 := .action (.copy 0 18)
def modeLoaded (r : State) : State := r.withRegisters {r.registers with input := r.target}
theorem loadMode_exec (r : State) : Exec loadMode r.store 1 (modeLoaded r).store := .action _ _
def prepareMode : Block 19 := .seq loadMode (.seq CacheMode.resetMatching CacheMode.setupMatching)
def modePrepared (r : State) : State :=
  r.withRegisters (GraphQuery.prepared [] r.core.index r.target)
theorem prepareMode_exec (r : State) : Exec prepareMode r.store 13 (modePrepared r).store :=
  Exec.seq (loadMode_exec r)
    (Exec.seq (CacheMode.liftDense_exec _ (modeLoaded r) _ _ (DenseClauses.resetQuery_exec _))
      (CacheMode.liftDense_exec _ (CacheMode.matchingReset (modeLoaded r)) _ _ (DenseClauses.setupQuery_exec _)))
def selectMode : Block 19 := .seq prepareMode (CacheMode.liftCore GraphQuery.selection)
def modeSelected (r : State) : State :=
  r.withRegisters (GraphQuery.selected (GraphQuery.prepared [] r.core.index r.target))
def modeSelectionFuel (r : State) : Nat :=
  13 + GraphQuery.selectionFuel (GraphQuery.prepared [] r.core.index r.target)
theorem selectMode_exec (r : State) :
    Exec selectMode r.store (modeSelectionFuel r) (modeSelected r).store :=
  Exec.seq (prepareMode_exec r)
    (CacheMode.liftCore_exec _ (modePrepared r) _ _ (GraphQuery.selection_exec _))
def readMode : Block 19 := .seq selectMode
  (.seq (CacheMode.liftCore GraphQuery.handoff) (CacheMode.liftCore MatchingValue.block))
def modeRead (r : State) : State :=
  r.withRegisters (MatchingValue.result (modeSelected r).registers.output)
def modeFuel (r : State) : Nat :=
  modeSelectionFuel r + (9 + MatchingValue.sourceSteps (modeSelected r).registers.output)
theorem readMode_exec (r : State) : Exec readMode r.store (modeFuel r) (modeRead r).store :=
  Exec.seq (selectMode_exec r)
    (Exec.seq (CacheMode.liftCore_exec _ (modeSelected r) _ _ (GraphQuery.handoff_exec _))
      (CacheMode.liftCore_exec _
        ((modeSelected r).withRegisters (initialRegisters (modeSelected r).registers.output))
        _ _ (MatchingValue.block_exec _)))
theorem modeSelectionFuel_bound (r : State) :
    modeSelectionFuel r ≤ 188 * r.target.length + 20 * r.core.index.length + 297 := by
  have cost := DenseClauses.selectionFuel_bound r.core.index r.target
  unfold modeSelectionFuel
  omega
theorem modeSelected_output_bound (r : State) :
    (modeSelected r).registers.output.length ≤ 189 * r.target.length + 21 * r.core.index.length + 285 :=
  DenseClauses.query_output_bound {r.core with formula := r.target}
theorem modeFuel_bound (r : State) :
    modeFuel r ≤ 755 * r.target.length + 83 * r.core.index.length + 1171 := by
  have select := modeSelectionFuel_bound r
  have size := modeSelected_output_bound r
  have decode := MatchingValue.sourceSteps_bound (modeSelected r).registers.output
  change MatchingValue.sourceSteps (modeSelected r).registers.output + 1 ≤
    3 * (modeSelected r).registers.output.length + 11 at decode
  unfold modeFuel
  omega
theorem modeRead_output_bound (r : State) :
    (modeRead r).registers.output.length ≤ 756 * r.target.length + 84 * r.core.index.length + 1151 := by
  have decode := MatchingValue.polynomial_output_length (modeSelected r).registers.output
  rw [MatchingValue.polynomial_output] at decode
  change (modeRead r).registers.output.length ≤ (modeSelected r).registers.output.length +
    (3 * (modeSelected r).registers.output.length + 11) at decode
  have size := modeSelected_output_bound r
  omega
theorem modeRead_canonical (r : State) (index : Nat) (entries : MatchingTable.Entries)
    (indexRead : r.core.index = List.replicate index true)
    (tableRead : r.target = MatchingTable.encode entries) :
    (modeRead r).registers.output = TableOwner.answer (MatchingTable.read entries index) := by
  have selected := GraphQuery.selected_canonical 0 index (MatchingTable.clauses entries)
  have query : (modeSelected r).registers.output =
      Occurrence.encodeQuery 0 (MatchingTable.entryClause (MatchingTable.read entries index)) := by
    change (GraphQuery.selected (GraphQuery.prepared [] r.core.index r.target)).output = _
    rw [indexRead,tableRead]
    exact selected.trans (congrArg (Occurrence.encodeQuery 0) (MatchingTable.clauses_read entries index))
  change (MatchingValue.result (modeSelected r).registers.output).output = _
  rw [query,← MatchingValue.polynomial_output,MatchingValue.polynomial_canonical]

inductive Kind where
  | owner | slot | mode
def table : Kind → State → BitString
  | .owner,r => r.matching
  | .slot,r => r.counter
  | .mode,r => r.target
def read : Kind → Block 19
  | .owner => CacheSigma.readTable false
  | .slot => CacheSigma.readTable true
  | .mode => readMode
def result : Kind → State → State
  | .owner,r => CacheSigma.tableRead false r
  | .slot,r => CacheSigma.tableRead true r
  | .mode,r => modeRead r
def fuel : Kind → State → Nat
  | .owner,r => CacheSigma.readFuel false r
  | .slot,r => CacheSigma.readFuel true r
  | .mode,r => modeFuel r
theorem read_exec (kind : Kind) (r : State) :
    Exec (read kind) r.store (fuel kind r) (result kind r).store := by
  cases kind with
  | owner => exact CacheSigma.readTable_exec false r
  | slot => exact CacheSigma.readTable_exec true r
  | mode => exact readMode_exec r
theorem result_fields (kind : Kind) (r : State) :
    (result kind r).core.formula = r.core.formula ∧
    (result kind r).core.remaining = r.core.remaining ∧
    (result kind r).core.index = r.core.index ∧
    (result kind r).core.core.variables = r.core.core.variables ∧
    (result kind r).core.core.buffer = r.core.core.buffer ∧
    (result kind r).matching = r.matching ∧ (result kind r).counter = r.counter ∧
    (result kind r).target = r.target := by
  cases kind <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem fuel_bound (kind : Kind) (r : State) :
    fuel kind r ≤ 755 * (table kind r).length + 83 * r.core.index.length + 1171 := by
  cases kind with
  | owner => exact CacheSigma.readFuel_bound false r
  | slot => exact CacheSigma.readFuel_bound true r
  | mode => exact modeFuel_bound r
theorem output_bound (kind : Kind) (r : State) :
    (result kind r).registers.output.length ≤ 756 * (table kind r).length + 84 * r.core.index.length + 1151 := by
  cases kind with
  | owner => exact CacheSigma.tableRead_output_bound false r
  | slot => exact CacheSigma.tableRead_output_bound true r
  | mode => exact modeRead_output_bound r
theorem canonical (kind : Kind) (r : State) (index : Nat) (entries : MatchingTable.Entries)
    (indexRead : r.core.index = List.replicate index true)
    (tableRead : table kind r = MatchingTable.encode entries) :
    (result kind r).registers.output = TableOwner.answer (MatchingTable.read entries index) := by
  cases kind with
  | owner => exact CacheSigma.tableRead_canonical false r index entries indexRead tableRead
  | slot => exact CacheSigma.tableRead_canonical true r index entries indexRead tableRead
  | mode => exact modeRead_canonical r index entries indexRead tableRead

end PNP.Concrete.NormalizerBlocks.CoefficientCache

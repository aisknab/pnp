/-
Copyright (c) 2026 PNP Labs.

Protected cached owner/slot access for candidate evaluation. A fixed
register selector chooses which stored table to read; the queried cell
is decoded by the same concrete unary scanner used for source caches.
-/
import PNP.Concrete.NormalizerCacheLiteralQuery
import PNP.Concrete.NormalizerCacheModeRead

namespace PNP.Concrete.NormalizerBlocks.CacheSigma
open BitRegister Occurrence
abbrev State := CacheMode.State

def table (slots : Bool) (r : State) : BitString := if slots then r.counter else r.matching
def loadTable (slots : Bool) : Block 19 := .action (.copy 0 (if slots then 17 else 16))
def tableLoaded (slots : Bool) (r : State) : State :=
  r.withRegisters {r.registers with input := table slots r}
theorem loadTable_exec (slots : Bool) (r : State) :
    Exec (loadTable slots) r.store 1 (tableLoaded slots r).store := by
  cases slots <;> exact .action _ _
def prepareTable (slots : Bool) : Block 19 :=
  .seq (loadTable slots) (.seq CacheMode.resetMatching CacheMode.setupMatching)
def tablePrepared (slots : Bool) (r : State) : State :=
  r.withRegisters (GraphQuery.prepared [] r.core.index (table slots r))
theorem prepareTable_exec (slots : Bool) (r : State) :
    Exec (prepareTable slots) r.store 13 (tablePrepared slots r).store :=
  Exec.seq (loadTable_exec slots r)
    (Exec.seq (CacheMode.liftDense_exec _ (tableLoaded slots r) _ _ (DenseClauses.resetQuery_exec _))
      (CacheMode.liftDense_exec _ (CacheMode.matchingReset (tableLoaded slots r))
        _ _ (DenseClauses.setupQuery_exec _)))
def selectTable (slots : Bool) : Block 19 :=
  .seq (prepareTable slots) (CacheMode.liftCore GraphQuery.selection)
def tableSelected (slots : Bool) (r : State) : State :=
  r.withRegisters (GraphQuery.selected (GraphQuery.prepared [] r.core.index (table slots r)))
def selectionFuel (slots : Bool) (r : State) : Nat :=
  13 + GraphQuery.selectionFuel (GraphQuery.prepared [] r.core.index (table slots r))
theorem selectTable_exec (slots : Bool) (r : State) :
    Exec (selectTable slots) r.store (selectionFuel slots r) (tableSelected slots r).store :=
  Exec.seq (prepareTable_exec slots r)
    (CacheMode.liftCore_exec _ (tablePrepared slots r) _ _ (GraphQuery.selection_exec _))
theorem selectionFuel_bound (slots : Bool) (r : State) :
    selectionFuel slots r ≤ 188 * (table slots r).length + 20 * r.core.index.length + 297 := by
  have bound := DenseClauses.selectionFuel_bound r.core.index (table slots r)
  unfold selectionFuel
  omega
theorem selected_output_bound (slots : Bool) (r : State) :
    (tableSelected slots r).registers.output.length ≤
      189 * (table slots r).length + 21 * r.core.index.length + 285 :=
  DenseClauses.query_output_bound {r.core with formula := table slots r}

def readTable (slots : Bool) : Block 19 :=
  .seq (selectTable slots) (.seq (CacheMode.liftCore GraphQuery.handoff)
    (CacheMode.liftCore MatchingValue.block))
def tableRead (slots : Bool) (r : State) : State :=
  r.withRegisters (MatchingValue.result (tableSelected slots r).registers.output)
def readFuel (slots : Bool) (r : State) : Nat :=
  selectionFuel slots r + (9 + MatchingValue.sourceSteps (tableSelected slots r).registers.output)
theorem readTable_exec (slots : Bool) (r : State) :
    Exec (readTable slots) r.store (readFuel slots r) (tableRead slots r).store :=
  Exec.seq (selectTable_exec slots r)
    (Exec.seq (CacheMode.liftCore_exec _ (tableSelected slots r) _ _ (GraphQuery.handoff_exec _))
      (CacheMode.liftCore_exec _
        ((tableSelected slots r).withRegisters (initialRegisters (tableSelected slots r).registers.output))
        _ _ (MatchingValue.block_exec _)))
theorem readFuel_bound (slots : Bool) (r : State) :
    readFuel slots r ≤ 755 * (table slots r).length + 83 * r.core.index.length + 1171 := by
  have select := selectionFuel_bound slots r
  have size := selected_output_bound slots r
  have decode := MatchingValue.sourceSteps_bound (tableSelected slots r).registers.output
  change MatchingValue.sourceSteps (tableSelected slots r).registers.output + 1 ≤
    3 * (tableSelected slots r).registers.output.length + 11 at decode
  unfold readFuel
  omega
theorem tableRead_output_bound (slots : Bool) (r : State) :
    (tableRead slots r).registers.output.length ≤
      756 * (table slots r).length + 84 * r.core.index.length + 1151 := by
  have decode := MatchingValue.polynomial_output_length (tableSelected slots r).registers.output
  rw [MatchingValue.polynomial_output] at decode
  change (tableRead slots r).registers.output.length ≤
    (tableSelected slots r).registers.output.length +
      (3 * (tableSelected slots r).registers.output.length + 11) at decode
  have size := selected_output_bound slots r
  omega
theorem tableRead_fields (slots : Bool) (r : State) :
    (tableRead slots r).core.formula = r.core.formula ∧
    (tableRead slots r).core.remaining = r.core.remaining ∧
    (tableRead slots r).core.index = r.core.index ∧
    (tableRead slots r).core.core.variables = r.core.core.variables ∧
    (tableRead slots r).core.core.buffer = r.core.core.buffer ∧
    (tableRead slots r).matching = r.matching ∧
    (tableRead slots r).counter = r.counter ∧
    (tableRead slots r).target = r.target := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem tableRead_canonical (slots : Bool) (r : State) (index : Nat) (entries : MatchingTable.Entries)
    (indexRead : r.core.index = List.replicate index true)
    (tableBytes : table slots r = MatchingTable.encode entries) :
    (tableRead slots r).registers.output = TableOwner.answer (MatchingTable.read entries index) := by
  have selected := GraphQuery.selected_canonical 0 index (MatchingTable.clauses entries)
  have query : (tableSelected slots r).registers.output =
      Occurrence.encodeQuery 0 (MatchingTable.entryClause (MatchingTable.read entries index)) := by
    change (GraphQuery.selected (GraphQuery.prepared [] r.core.index (table slots r))).output = _
    rw [indexRead,tableBytes]
    exact selected.trans (congrArg (Occurrence.encodeQuery 0) (MatchingTable.clauses_read entries index))
  change (MatchingValue.result (tableSelected slots r).registers.output).output = _
  rw [query,← MatchingValue.polynomial_output,MatchingValue.polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.CacheSigma

/-
Copyright (c) 2026 PNP Labs.

Protected views for applying a returned path to a matching table. The
path decoder reuses the core prefix while a separate register retains the
original table; only the derived ordered updates reach the batch writer.
-/
import PNP.Concrete.NormalizerPairPolynomial

namespace PNP.Concrete.NormalizerBlocks.Augmentation
open BitRegister

structure State where
  pairs : PathPairs.State
  table : BitString
def State.frame (r : State) : Store 1 := .cons r.table .nil
def State.store (r : State) : Store 13 := Frame.join r.pairs.store r.frame
def State.withPairs (r : State) (pairs : PathPairs.State) : State := {r with pairs := pairs}
def State.batch (r : State) : TableBatch.State := ⟨r.pairs.core, r.pairs.pending, r.pairs.firstIndex⟩
def State.batchFrame (r : State) : Store 2 := .cons r.pairs.buffer (.cons r.table .nil)
def State.withBatch (r : State) (batch : TableBatch.State) : State :=
  {r with pairs := {r.pairs with core := batch.core, pending := batch.pending, firstIndex := batch.table}}
theorem State.batch_store (r : State) : r.store = Frame.join r.batch.store r.batchFrame := rfl
theorem State.withBatch_store (r : State) (batch : TableBatch.State) :
    (r.withBatch batch).store = Frame.join batch.store r.batchFrame := rfl

def liftPairs (body : Block 12) : Block 13 := Frame.block 1 body
theorem liftPairs_exec (body : Block 12) (r : State) (fuel : Nat) (after : PathPairs.State)
    (checked : Exec body r.pairs.store fuel after.store) :
    Exec (liftPairs body) r.store fuel (r.withPairs after).store :=
  Frame.execution checked r.frame
def liftBatch (body : Block 11) : Block 13 := Frame.block 2 body
theorem liftBatch_exec (body : Block 11) (r : State) (fuel : Nat) (after : TableBatch.State)
    (checked : Exec body r.batch.store fuel after.store) :
    Exec (liftBatch body) r.store fuel (r.withBatch after).store := by
  rw [State.batch_store, State.withBatch_store]
  exact Frame.execution checked r.batchFrame

def saveTable : Block 13 := .action (.copy 12 10)
def tableSaved (r : State) : State := {r with table := r.pairs.firstIndex}
theorem saveTable_exec (r : State) : Exec saveTable r.store 1 (tableSaved r).store := .action _ _
def derivePairs : Block 13 := liftPairs PathPairs.phase
def pairsDerived (r : State) : State := r.withPairs (PathPairs.phaseResult r.pairs)
def pairsFuel (r : State) : Nat := PathPairs.phaseFuel r.pairs
theorem derivePairs_exec (r : State) :
    Exec derivePairs r.store (pairsFuel r) (pairsDerived r).store :=
  liftPairs_exec _ r _ _ (PathPairs.phase_exec r.pairs)

def prepareBatch : Block 13 := .seq (.action (.copy 9 8)) (.action (.copy 10 12))
def batchPrepared (r : State) : State := r.withBatch ⟨r.pairs.core, r.pairs.core.output, r.table⟩
theorem prepareBatch_exec (r : State) : Exec prepareBatch r.store 2 (batchPrepared r).store :=
  Exec.seq (.action _ _) (.action _ _)
def applyUpdates : Block 13 := liftBatch TableBatch.loop
def updatesApplied (r : State) : State := r.withBatch (TableBatch.whole r.batch).state
def updatesFuel (r : State) : Nat := (TableBatch.whole r.batch).fuel
theorem applyUpdates_exec (r : State) :
    Exec applyUpdates r.store (updatesFuel r) (updatesApplied r).store :=
  liftBatch_exec _ r _ _ (TableBatch.whole_exec r.batch)
def finish : Block 13 := .action (.copy 8 10)
def finished (r : State) : State := r.withPairs {r.pairs with core := {r.pairs.core with output := r.pairs.firstIndex}}
theorem finish_exec (r : State) : Exec finish r.store 1 (finished r).store := .action _ _

def prepared (r : State) : State := batchPrepared (pairsDerived (tableSaved r))
def prepare : Block 13 := .seq saveTable (.seq derivePairs prepareBatch)
def prepareFuel (r : State) : Nat := 1 + (pairsFuel (tableSaved r) + 2)
theorem prepare_exec (r : State) : Exec prepare r.store (prepareFuel r) (prepared r).store :=
  Exec.seq (saveTable_exec r) (Exec.seq (derivePairs_exec (tableSaved r)) (prepareBatch_exec (pairsDerived (tableSaved r))))
def phase : Block 13 := .seq prepare (.seq applyUpdates finish)
def phaseResult (r : State) : State := finished (updatesApplied (prepared r))
def phaseFuel (r : State) : Nat := prepareFuel r + (updatesFuel (prepared r) + 1)
theorem phase_exec (r : State) : Exec phase r.store (phaseFuel r) (phaseResult r).store :=
  Exec.seq (prepare_exec r) (Exec.seq (applyUpdates_exec (prepared r)) (finish_exec (updatesApplied (prepared r))))

theorem phase_canonical (r : State) (xs : List CNFLiteral) (entries : MatchingTable.Entries)
    (path : r.pairs.pending = PathData.encode xs)
    (table : r.pairs.firstIndex = MatchingTable.encode entries) :
    (phaseResult r).pairs.core.output = MatchingTable.encode (MatchingTable.writeAll entries (PathPairs.value xs)) := by
  have pairs := PathPairs.phase_canonical r.pairs xs path
  have pending : (prepared r).batch.pending = TableBatch.encodeUpdates (PathPairs.value xs) := pairs
  have oldTable : (prepared r).batch.table = MatchingTable.encode entries := table
  exact TableBatch.run_canonical (PathPairs.value xs) _ (prepared r).batch entries pending oldTable
    (Or.inl (Nat.lt_succ_self _))

end PNP.Concrete.NormalizerBlocks.Augmentation

import PNP.Concrete.NormalizerBatchLoop

namespace PNP.Concrete.NormalizerBlocks

example (r : TableBatch.State) :
    Exec TableBatch.loop r.store (TableBatch.whole r).fuel (TableBatch.whole r).state.store := TableBatch.whole_exec r
example (r : TableBatch.State) : (TableBatch.whole r).state.pending = [] := TableBatch.whole_stopped r
example (r : TableBatch.State) :
    (TableBatch.whole r).state.table.length ≤ TableBatch.tableBound r.pending.length r.table.length :=
  (TableBatch.whole_bounds r).1
example (r : TableBatch.State) :
    (TableBatch.whole r).fuel ≤ TableBatch.totalCostBound r.pending.length r.table.length :=
  (TableBatch.whole_bounds r).2

#print axioms TableBatch.run_exec
#print axioms TableBatch.run_stopped
#print axioms TableBatch.costBound_mono
#print axioms TableBatch.run_bounds
#print axioms TableBatch.whole_exec
#print axioms TableBatch.whole_stopped
#print axioms TableBatch.whole_bounds

end PNP.Concrete.NormalizerBlocks

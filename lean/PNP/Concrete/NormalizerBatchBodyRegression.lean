import PNP.Concrete.NormalizerBatchBody

namespace PNP.Concrete.NormalizerBlocks

example (r : TableBatch.State) :
    Exec TableBatch.body r.store (TableBatch.bodyFuel r) (TableBatch.result r).store := TableBatch.body_exec r
example (r : TableBatch.State) (nonempty : r.pending ≠ []) :
    (TableBatch.result r).pending.length < r.pending.length := TableBatch.pending_strict r nonempty
example (r : TableBatch.State) :
    (TableBatch.result r).table.length ≤ r.table.length + 18 * r.pending.length + 40 := TableBatch.table_growth r
example (r : TableBatch.State) :
    TableBatch.bodyFuel r ≤ TableBatch.costBound r.pending.length r.table.length := TableBatch.bodyFuel_bound r

#print axioms TableBatch.reset_exec
#print axioms TableBatch.parse_exec
#print axioms TableBatch.setup_exec
#print axioms TableBatch.write_exec
#print axioms TableBatch.save_exec
#print axioms TableBatch.body_exec
#print axioms TableBatch.pending_bound
#print axioms TableBatch.pending_strict
#print axioms TableBatch.buffer_bound
#print axioms TableBatch.table_growth
#print axioms TableBatch.bodyFuel_bound

end PNP.Concrete.NormalizerBlocks

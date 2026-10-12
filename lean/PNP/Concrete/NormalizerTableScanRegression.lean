import PNP.Concrete.NormalizerTableScan

namespace PNP.Concrete.NormalizerBlocks

example (r : Occurrence.Registers) :
    Exec TableWrite.pair r.store (TableWrite.pairResult r).fuel
      (TableWrite.pairResult r).state.store := TableWrite.pair_exec r
example (r : Occurrence.Registers) :
    (TableWrite.pairResult r).state.active = [] ∨
      (TableWrite.pairResult r).state.input.length < r.input.length := TableWrite.pair_progress r
example (r : Occurrence.Registers) :
    Exec TableWrite.loop r.store (TableWrite.queryResult r).fuel
      (TableWrite.queryResult r).state.store := TableWrite.query_exec r
example (r : Occurrence.Registers) :
    (TableWrite.queryResult r).fuel ≤ (4 * r.target.length + 18) * (r.input.length + 1) + 1 :=
  TableWrite.query_fuel_bound r
example (r : Occurrence.Registers) : (TableWrite.queryResult r).state.active = [] :=
  TableWrite.query_stopped r

#print axioms TableWrite.pair_exec
#print axioms TableWrite.pair_fuel_bound
#print axioms TableWrite.pair_progress
#print axioms TableWrite.pair_target
#print axioms TableWrite.scan_exec
#print axioms TableWrite.scan_fuel_bound
#print axioms TableWrite.scan_stopped
#print axioms TableWrite.query_exec
#print axioms TableWrite.query_fuel_bound
#print axioms TableWrite.query_stopped

end PNP.Concrete.NormalizerBlocks

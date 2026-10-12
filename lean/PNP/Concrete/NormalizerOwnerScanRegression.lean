import PNP.Concrete.NormalizerOwnerScan

namespace PNP.Concrete.NormalizerBlocks

example (r : Occurrence.Registers) :
    Exec TableOwner.loop r.store (TableOwner.queryResult r).fuel (TableOwner.queryResult r).state.store :=
  TableOwner.query_exec r
example (r : Occurrence.Registers) :
    (TableOwner.queryResult r).fuel ≤ 12 * (r.input.length + 1) + 1 := TableOwner.query_fuel_bound r
example (r : Occurrence.Registers) : (TableOwner.queryResult r).state.active = [] := TableOwner.query_stopped r
example (r : Occurrence.Registers) :
    (TableOwner.pairResult r).state.active = [] ∨
      (TableOwner.pairResult r).state.input.length < r.input.length := TableOwner.pair_progress r

#print axioms TableOwner.pair_exec
#print axioms TableOwner.pair_fuel_bound
#print axioms TableOwner.pair_progress
#print axioms TableOwner.scan_exec
#print axioms TableOwner.scan_fuel_bound
#print axioms TableOwner.scan_stopped
#print axioms TableOwner.query_exec
#print axioms TableOwner.query_fuel_bound
#print axioms TableOwner.query_stopped

end PNP.Concrete.NormalizerBlocks

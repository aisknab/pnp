import PNP.Concrete.NormalizerOccurrenceScan

namespace PNP.Concrete.NormalizerBlocks

example (r : Occurrence.Registers) :
    Exec Occurrence.pair r.store (Occurrence.pairResult r).fuel (Occurrence.pairResult r).state.store :=
  Occurrence.pair_exec r
example (r : Occurrence.Registers) : (Occurrence.pairResult r).fuel ≤ 11 := Occurrence.pair_fuel_bound r
example (r : Occurrence.Registers) :
    (Occurrence.pairResult r).state.active = [] ∨
      (Occurrence.pairResult r).state.input.length < r.input.length := Occurrence.pair_progress r
example (r : Occurrence.Registers) :
    Exec Occurrence.loop r.store (Occurrence.queryResult r).fuel (Occurrence.queryResult r).state.store :=
  Occurrence.query_exec r
example (r : Occurrence.Registers) :
    (Occurrence.queryResult r).fuel ≤ 12 * (r.input.length + 1) + 1 := Occurrence.query_fuel_bound r
example (r : Occurrence.Registers) : (Occurrence.queryResult r).state.active = [] := Occurrence.query_stopped r

#print axioms Occurrence.pair_exec
#print axioms Occurrence.pair_fuel_bound
#print axioms Occurrence.pair_progress
#print axioms Occurrence.scan_exec
#print axioms Occurrence.scan_fuel_bound
#print axioms Occurrence.scan_stopped
#print axioms Occurrence.query_exec
#print axioms Occurrence.query_fuel_bound
#print axioms Occurrence.query_stopped

end PNP.Concrete.NormalizerBlocks

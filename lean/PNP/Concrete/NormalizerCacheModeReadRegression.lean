import PNP.Concrete.NormalizerCacheModeRead

namespace PNP.Concrete.NormalizerBlocks

example (r : CacheMode.State) :
    Exec CacheMode.readMatching r.store (CacheMode.readFuel r) (CacheMode.matchingRead r).store :=
  CacheMode.readMatching_exec r
example (r : CacheMode.State) (i : r.core.index = [true])
    (m : r.matching = MatchingTable.encode [some 4,none,some 9]) :
    (CacheMode.matchingRead r).registers.output = [false] :=
  CacheMode.matchingRead_canonical r 1 [some 4,none,some 9] i m
example (r : CacheMode.State) (i : r.core.index = [true,true])
    (m : r.matching = MatchingTable.encode [some 4,none,some 9]) :
    (CacheMode.matchingRead r).registers.output = TableOwner.answer (some 9) :=
  CacheMode.matchingRead_canonical r 2 [some 4,none,some 9] i m
example (r : CacheMode.State) (i : r.core.index = [true])
    (m : r.matching = MatchingTable.encode [some 4]) :
    (CacheMode.matchingRead r).registers.output = [false] :=
  CacheMode.matchingRead_canonical r 1 [some 4] i m

#print axioms CacheMode.liftDense_exec
#print axioms CacheMode.liftCore_exec
#print axioms CacheMode.prepareMatching_exec
#print axioms CacheMode.selectMatching_exec
#print axioms CacheMode.selectionFuel_bound
#print axioms CacheMode.selection_output_bound
#print axioms CacheMode.readMatching_exec
#print axioms CacheMode.readFuel_bound
#print axioms CacheMode.matchingRead_fields
#print axioms CacheMode.matchingRead_canonical

end PNP.Concrete.NormalizerBlocks

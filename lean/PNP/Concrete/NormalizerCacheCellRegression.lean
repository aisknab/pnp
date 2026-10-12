import PNP.Concrete.NormalizerCacheCell

namespace PNP.Concrete.NormalizerBlocks

example (r : DenseClauses.State) : Exec CacheCell.read r.store (CacheCell.fuel r) (CacheCell.result r).store :=
  CacheCell.read_exec r
example (r : DenseClauses.State) (t : r.formula = MatchingTable.encode [some 2,none,some 1]) (i : r.index = [true]) :
    (CacheCell.result r).registers.output = [false] :=
  CacheCell.canonical r [some 2,none,some 1] 1 t i
example (r : DenseClauses.State) (t : r.formula = MatchingTable.encode [some 2,none,some 1]) (i : r.index = [true,true]) :
    (CacheCell.result r).registers.output = TableOwner.answer (some 1) :=
  CacheCell.canonical r [some 2,none,some 1] 2 t i

#print axioms CacheCell.read_exec
#print axioms CacheCell.result_fields
#print axioms CacheCell.fuel_bound
#print axioms CacheCell.output_bound
#print axioms CacheCell.canonical

end PNP.Concrete.NormalizerBlocks

import PNP.Concrete.NormalizerTableGrowth

namespace PNP.Concrete.NormalizerBlocks

example (r : Occurrence.Registers) :
    TableWrite.potential (TableWrite.pairResult r).state ≤ TableWrite.potential r := TableWrite.pair_potential r
example (fuel : Nat) (r : Occurrence.Registers) :
    TableWrite.potential (TableWrite.scan fuel r).state ≤ TableWrite.potential r := TableWrite.scan_potential fuel r
example (r : Occurrence.Registers) :
    (TableWrite.queryResult r).state.excess.length ≤
      r.excess.length + r.input.length + 2 * r.target.length + 8 := TableWrite.query_growth_bound r
example (r : Occurrence.Registers) :
    (TableWrite.packed (TableWrite.queryResult r).state).output.length ≤
      r.excess.length + r.input.length + 2 * r.target.length + 8 := TableWrite.packed_query_growth_bound r

#print axioms TableWrite.token_growth
#print axioms TableWrite.pair_potential
#print axioms TableWrite.scan_potential
#print axioms TableWrite.query_buffer_bound
#print axioms TableWrite.credit_bound
#print axioms TableWrite.query_growth_bound
#print axioms TableWrite.packed_query_growth_bound

end PNP.Concrete.NormalizerBlocks

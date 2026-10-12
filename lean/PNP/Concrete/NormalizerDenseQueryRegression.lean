import PNP.Concrete.NormalizerDenseQuery

namespace PNP.Concrete.NormalizerBlocks

example (r : DenseClauses.State)
    (index : r.index = [true])
    (formula : r.formula = GraphQuery.clauseData [[⟨true,9⟩],[⟨false,3⟩,⟨true,2⟩]]) :
    (DenseClauses.queried r).registers.output = Occurrence.encodeQuery 0 [⟨false,3⟩,⟨true,2⟩] :=
  DenseClauses.query_canonical r 1 _ index formula

example (r : DenseClauses.State)
    (index : r.index = [true,true])
    (formula : r.formula = GraphQuery.clauseData [[⟨true,9⟩]]) :
    (DenseClauses.queried r).registers.output = Occurrence.encodeQuery 0 [] :=
  DenseClauses.query_canonical r 2 _ index formula

example (r : DenseClauses.State) :
    (DenseClauses.queried r).core.variables = r.core.variables ∧
      (DenseClauses.queried r).core.buffer = r.core.buffer :=
  (DenseClauses.queried_fields r).2.2.2

#print axioms DenseClauses.prepareQuery_exec
#print axioms DenseClauses.query_exec
#print axioms DenseClauses.selectionFuel_bound
#print axioms DenseClauses.queryFuel_bound
#print axioms DenseClauses.queried_fields
#print axioms DenseClauses.query_output_bound
#print axioms DenseClauses.query_canonical

end PNP.Concrete.NormalizerBlocks

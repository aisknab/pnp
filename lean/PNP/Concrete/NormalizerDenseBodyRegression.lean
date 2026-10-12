import PNP.Concrete.NormalizerDenseBody

namespace PNP.Concrete.NormalizerBlocks

example (r : DenseClauses.State)
    (remaining : r.remaining = SearchVertices.encodeVertices [⟨true,1⟩])
    (variables : r.core.variables = SearchVertices.encodeVertices [⟨false,7⟩])
    (formula : r.formula = GraphQuery.clauseData [[⟨true,2⟩],[⟨false,7⟩]]) :
    (DenseClauses.bodyResult r).core.buffer =
      (DenseClauses.clauseBits [⟨false,0⟩]).reverse ++ r.core.buffer :=
  (DenseClauses.body_canonical r ⟨true,1⟩ [] [⟨false,7⟩]
    [[⟨true,2⟩],[⟨false,7⟩]] remaining variables formula).2

example (r : DenseClauses.State) :
    (DenseClauses.bodyResult r).formula = r.formula ∧
      (DenseClauses.bodyResult r).core.variables = r.core.variables :=
  ⟨(DenseClauses.body_fields r).1,(DenseClauses.body_fields r).2.2⟩

#print axioms DenseClauses.body_exec
#print axioms DenseClauses.body_fields
#print axioms DenseClauses.bodyFuel_bound
#print axioms DenseClauses.body_canonical

end PNP.Concrete.NormalizerBlocks

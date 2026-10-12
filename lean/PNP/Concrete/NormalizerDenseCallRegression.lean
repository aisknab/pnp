import PNP.Concrete.NormalizerDenseCall

namespace PNP.Concrete.NormalizerBlocks

example (r : DenseClauses.State)
    (remaining : r.remaining = SearchVertices.encodeVertices [⟨true,1⟩,⟨true,0⟩])
    (variables : r.core.variables = SearchVertices.encodeVertices [⟨false,7⟩])
    (formula : r.formula = GraphQuery.clauseData [[⟨true,3⟩],[⟨false,7⟩]]) :
    (DenseClauses.called r).registers.output =
      GraphQuery.clauseData [[⟨false,0⟩],[]] :=
  DenseClauses.called_canonical [[⟨true,3⟩],[⟨false,7⟩]] [⟨false,7⟩]
    [⟨true,1⟩,⟨true,0⟩] r remaining variables formula

example (r : DenseClauses.State) (formula : List (List CNFLiteral)) (vertices : List CNFLiteral)
    (remaining : r.remaining = SearchVertices.encodeVertices [])
    (variables : r.core.variables = SearchVertices.encodeVertices vertices)
    (original : r.formula = GraphQuery.clauseData formula) :
    (DenseClauses.called r).registers.output = GraphQuery.clauseData [] :=
  DenseClauses.called_canonical formula vertices [] r remaining variables original

example (r : DenseClauses.State) (bound : Nat) (bounded : r.store.Bounded bound) :
    DenseClauses.callSteps r ≤ DenseClauses.callBound.eval bound :=
  DenseClauses.callSteps_bound r bound bounded

#print axioms DenseClauses.front_exec
#print axioms DenseClauses.finish_exec
#print axioms DenseClauses.call_exec
#print axioms DenseClauses.called_canonical
#print axioms DenseClauses.called_fields
#print axioms DenseClauses.frontSteps_bound
#print axioms DenseClauses.callSteps_bound

end PNP.Concrete.NormalizerBlocks

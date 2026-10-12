import PNP.Concrete.NormalizerGraphQuery

namespace PNP.Concrete.NormalizerBlocks

example (target index : Nat) (clauses : List (List CNFLiteral)) :
    (GraphQuery.result (GraphQuery.prepared (List.replicate target true)
      (List.replicate index true) (GraphQuery.clauseData clauses))).output =
      Occurrence.answer ((clauses[index]?.getD []).find? (fun literal => literal.variableIndex == target)) :=
  GraphQuery.result_canonical target index clauses
example (target index data : BitString) :
    GraphQuery.fuel (GraphQuery.prepared target index data) + 1 ≤
      188 * data.length + 20 * target.length + 20 * index.length + 284 :=
  GraphQuery.prepared_fuel_bound target index data
example : (GraphQuery.result (GraphQuery.prepared [] [true]
    (GraphQuery.clauseData [[], [⟨false, 0⟩]]))).output = [true, false] := by
  change (GraphQuery.result (GraphQuery.prepared (List.replicate 0 true) (List.replicate 1 true) _)).output = _
  rw [GraphQuery.result_canonical]
  rfl
example : (GraphQuery.result (GraphQuery.prepared [] [true]
    (GraphQuery.clauseData []))).output = [false] := by
  change (GraphQuery.result (GraphQuery.prepared (List.replicate 0 true) (List.replicate 1 true) _)).output = _
  rw [GraphQuery.result_canonical]
  rfl

#print axioms GraphQuery.handoff_exec
#print axioms GraphQuery.selection_exec
#print axioms GraphQuery.block_exec
#print axioms GraphQuery.fuel_bound
#print axioms GraphQuery.prepared_bounded
#print axioms GraphQuery.prepared_fuel_bound
#print axioms GraphQuery.selected_canonical
#print axioms GraphQuery.result_canonical

end PNP.Concrete.NormalizerBlocks

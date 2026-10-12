import PNP.Concrete.NormalizerClauseCountCanonical

namespace PNP.Concrete.NormalizerBlocks
open ClauseCount
example : count (GraphQuery.clauseData []) = 0 := by decide
example : count (GraphQuery.clauseData [[], []]) = 2 := by decide
example : count (GraphQuery.clauseData [[⟨true, 3⟩, ⟨false, 0⟩], []]) = 2 := by decide
example : count (GraphQuery.clauseData [[⟨false, 8⟩]]) = 1 := by decide

#print axioms ClauseCount.count_unary
#print axioms ClauseCount.count_literal
#print axioms ClauseCount.count_literals
#print axioms ClauseCount.count_clause
#print axioms ClauseCount.count_clauses
#print axioms ClauseCount.count_formula

end PNP.Concrete.NormalizerBlocks

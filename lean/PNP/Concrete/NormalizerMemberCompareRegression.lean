import PNP.Concrete.NormalizerMemberCompare

namespace PNP.Concrete.NormalizerBlocks

example : TraceMember.same ⟨true, 3⟩ ⟨false, 3⟩ = false := rfl
example : TraceMember.same ⟨true, 3⟩ ⟨true, 3⟩ = true := rfl
example : TraceMember.same ⟨false, 2⟩ ⟨false, 3⟩ = false := rfl
example (r : TraceMember.State) : TraceMember.comparisonFuel r ≤ 4 * r.currentIndex.length + 12 :=
  TraceMember.comparisonFuel_bound r

#print axioms TraceMember.prepare_exec
#print axioms TraceMember.countQuery_exec
#print axioms TraceMember.counted_output
#print axioms TraceMember.filter_exec
#print axioms TraceMember.filtered_output
#print axioms TraceMember.comparison_exec
#print axioms TraceMember.comparisonFuel_bound
#print axioms TraceMember.comparison_output
#print axioms TraceMember.comparison_preserves

end PNP.Concrete.NormalizerBlocks

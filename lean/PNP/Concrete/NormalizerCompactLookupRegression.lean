import PNP.Concrete.NormalizerCompactLookup

namespace PNP.Concrete.NormalizerBlocks
open Occurrence

example (r : CompactClause.State) (read : r.core.target = [true,true,true])
    (variables : r.variables = SearchVertices.encodeVertices [⟨false,7⟩,⟨false,3⟩]) :
    (CompactClause.looked r).core.output = [true,true] := by
  rw [CompactClause.lookup_canonical r 3 _ read variables]
  rfl

example (r : CompactClause.State) (read : r.core.target = [true,true])
    (variables : r.variables = SearchVertices.encodeVertices [⟨false,7⟩,⟨false,3⟩]) :
    (CompactClause.looked r).core.output = [false] := by
  rw [CompactClause.lookup_canonical r 2 _ read variables]
  rfl

example (r : CompactClause.State) :
    (CompactClause.looked r).pending = r.pending ∧
      (CompactClause.looked r).buffer = r.buffer :=
  ⟨(CompactClause.lookup_fields r).1,(CompactClause.lookup_fields r).2.2.1⟩

#print axioms CompactClause.resetOwner_exec
#print axioms CompactClause.lookup_exec
#print axioms CompactClause.lookupFuel_bound
#print axioms CompactClause.lookup_fields
#print axioms CompactClause.lookup_canonical
#print axioms CompactClause.preparedOwner_bounded
#print axioms CompactClause.lookup_output_bound

end PNP.Concrete.NormalizerBlocks

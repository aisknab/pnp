import PNP.Concrete.NormalizerDenseAppend

namespace PNP.Concrete.NormalizerBlocks

example (r : DenseClauses.State)
    (selected : r.registers.output = Occurrence.encodeQuery 0 [⟨true,7⟩,⟨false,3⟩])
    (variables : r.core.variables = SearchVertices.encodeVertices [⟨false,7⟩]) :
    (DenseClauses.appended r).core.buffer =
      (DenseClauses.clauseBits [⟨true,0⟩]).reverse ++ r.core.buffer :=
  DenseClauses.appended_buffer r [⟨false,7⟩] [⟨true,7⟩,⟨false,3⟩] selected variables

example (r : DenseClauses.State)
    (selected : r.registers.output = Occurrence.encodeQuery 0 [⟨false,3⟩])
    (variables : r.core.variables = SearchVertices.encodeVertices []) :
    (DenseClauses.appended r).core.buffer =
      (DenseClauses.clauseBits []).reverse ++ r.core.buffer :=
  DenseClauses.appended_buffer r [] [⟨false,3⟩] selected variables

example (r : DenseClauses.State) :
    (DenseClauses.appended r).remaining = r.remaining ∧
      (DenseClauses.appended r).core.variables = r.core.variables :=
  ⟨(DenseClauses.appended_fields r).2.1,(DenseClauses.appended_fields r).2.2.2⟩

#print axioms DenseClauses.clauseBits_data
#print axioms DenseClauses.clauseBits_reverse_append
#print axioms DenseClauses.compact_exec
#print axioms DenseClauses.appendClause_exec
#print axioms DenseClauses.appended_fields
#print axioms DenseClauses.appendFuel_bound
#print axioms DenseClauses.appended_buffer

end PNP.Concrete.NormalizerBlocks

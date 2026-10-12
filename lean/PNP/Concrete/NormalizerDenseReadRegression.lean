import PNP.Concrete.NormalizerDenseRead

namespace PNP.Concrete.NormalizerBlocks

example (r : DenseClauses.State) (remaining :
    r.remaining = SearchVertices.encodeVertices [⟨true,7⟩,⟨true,2⟩]) :
    (DenseClauses.entryRead r).index = List.replicate 7 true ∧
      (DenseClauses.entryRead r).remaining = SearchVertices.encodeVertices [⟨true,2⟩] :=
  DenseClauses.read_canonical r ⟨true,7⟩ [⟨true,2⟩] remaining

example (r : DenseClauses.State) :
    (DenseClauses.entryRead r).formula = r.formula ∧
      (DenseClauses.entryRead r).core.variables = r.core.variables ∧
      (DenseClauses.entryRead r).core.buffer = r.core.buffer :=
  (DenseClauses.read_fields r).2.2

example (r : DenseClauses.State) (nonempty : r.remaining ≠ []) :
    (DenseClauses.entryRead r).remaining.length < r.remaining.length :=
  DenseClauses.read_progress r nonempty

#print axioms DenseClauses.liftCompact_exec
#print axioms DenseClauses.liftCore_exec
#print axioms DenseClauses.readEntry_exec
#print axioms DenseClauses.read_fields
#print axioms DenseClauses.readFuel_bound
#print axioms DenseClauses.read_progress
#print axioms DenseClauses.read_index_bound
#print axioms DenseClauses.read_canonical

end PNP.Concrete.NormalizerBlocks

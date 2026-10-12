import PNP.Concrete.NormalizerCompactEmission

namespace PNP.Concrete.NormalizerBlocks

example (r : CompactClause.State) (sign : ForwardEdge.present r.positive = false)
    (answer : r.core.output = [true,true,true]) :
    (CompactClause.chosen r).buffer = (NANDFrontend.literalBits false 2).reverse ++ r.buffer :=
  CompactClause.chosen_buffer r false (some 2) sign answer

example (r : CompactClause.State) (answer : r.core.output = [false]) :
    (CompactClause.chosen r).buffer = r.buffer := by
  simpa only [Option.map_none, CompactClause.literalOutput, List.reverse_nil, List.nil_append] using
    CompactClause.chosen_buffer r (ForwardEdge.present r.positive) none rfl answer

example :
    CompactClause.compactLiteral [⟨false,7⟩,⟨false,3⟩] ⟨false,3⟩ = some ⟨false,1⟩ := rfl

example :
    CompactClause.compactLiteral [⟨false,7⟩,⟨false,3⟩] ⟨true,2⟩ = none := rfl

#print axioms CompactClause.emitCore_exec
#print axioms CompactClause.emit_exec
#print axioms CompactClause.emitted_buffer
#print axioms CompactClause.choose_exec
#print axioms CompactClause.chosen_fields
#print axioms CompactClause.chooseFuel_bound
#print axioms CompactClause.chosen_buffer

end PNP.Concrete.NormalizerBlocks

import PNP.Concrete.NormalizerExtractRange

namespace PNP.Concrete.NormalizerBlocks
open Extraction
example (r : State) (unseen : List CNFLiteral) (trace : List TraceData.Row)
    (data : Layout r unseen [] trace) : SelectionFrom unseen trace (whole r).state := whole_range r unseen trace data
example : ParentWithin [] none := by intro vertex impossible; cases impossible
example : ParentWithin [(⟨false, 3⟩, none)] (some ⟨false, 3⟩) := by
  intro vertex equal
  exact ⟨(⟨false, 3⟩, none), List.mem_cons_self, Option.some.inj equal⟩
example (r : State) (vertex : CNFLiteral) (parent : Option CNFLiteral) (rest : List CNFLiteral)
    (selected : Selected r vertex parent rest) : observation r = answer (some ((vertex, parent), rest)) :=
  selected.observation

#print axioms Extraction.query_layout
#print axioms Extraction.body_missing_layout
#print axioms Extraction.joined_vertices
#print axioms Extraction.body_selected_layout
#print axioms Extraction.scan_range
#print axioms Extraction.whole_range
#print axioms Extraction.Selected.observation
#print axioms Extraction.Selected.sizes

end PNP.Concrete.NormalizerBlocks

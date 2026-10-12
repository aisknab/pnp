import PNP.Concrete.NormalizerParentSemantics

namespace PNP.Concrete.NormalizerBlocks

example (r : ParentQuery.State) (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row)
    (data : ParentQuery.Canonical r target clauses entries) (tr : r.pending = TraceData.encode trace)
    (initial : r.output = ParentQuery.answer none) :
    (ParentQuery.whole r).state.output = ParentQuery.answer
      ((trace.find? (fun e => EdgeKinds.value e.1 target clauses entries)).map (fun e => some e.1)) :=
  ParentQuery.whole_canonical r target clauses entries trace data tr initial
example : ParentQuery.answer none ≠ ParentQuery.answer (some none) := by decide
example : ParentQuery.answer (some none) ≠ ParentQuery.answer (some (some ⟨false, 0⟩)) := by decide
example : TraceData.next (TraceData.row (⟨true, 2⟩, some ⟨false, 4⟩) [false, true]) = [false, true] :=
  TraceData.next_canonical _ _

#print axioms ParentQuery.canonical_body
#print axioms ParentQuery.edge_canonical
#print axioms ParentQuery.row_edge
#print axioms ParentQuery.body_row
#print axioms ParentQuery.scan_canonical
#print axioms ParentQuery.whole_canonical

end PNP.Concrete.NormalizerBlocks

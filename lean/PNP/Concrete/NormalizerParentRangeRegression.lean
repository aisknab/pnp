import PNP.Concrete.NormalizerParentRange

namespace PNP.Concrete.NormalizerBlocks
example : ParentQuery.AnswerFrom [] (ParentQuery.answer none) := .unavailable
example : ParentQuery.AnswerFrom [] (ParentQuery.answer (some none)) := .root
example : ParentQuery.AnswerFrom [(⟨false, 7⟩, none)] (ParentQuery.answer (some (some ⟨false, 7⟩))) :=
  .predecessor _ List.mem_cons_self
example (r : ParentQuery.State) (trace : List TraceData.Row) (read : r.pending = TraceData.encode trace) :
    ParentQuery.AnswerFrom trace (ParentQuery.phaseResult r).output := ParentQuery.phase_from r trace read
example (r : Extraction.State) (trace : List TraceData.Row) (read : r.trace = TraceData.encode trace) :
    ParentQuery.AnswerFrom trace (Extraction.queried r).parent.output := Extraction.query_from r trace read

#print axioms ParentQuery.body_from
#print axioms ParentQuery.scan_from
#print axioms ParentQuery.phase_from
#print axioms ParentQuery.AnswerFrom.available
#print axioms ParentQuery.AnswerFrom.unavailable_eq
#print axioms Eligibility.phase_from
#print axioms Extraction.query_from

end PNP.Concrete.NormalizerBlocks

import PNP.Concrete.NormalizerParentPhase

namespace PNP.Concrete.NormalizerBlocks

example (r : ParentQuery.State) : (ParentQuery.phaseResult r).pending = [] := ParentQuery.phase_stopped r
example (r : ParentQuery.State) : ParentQuery.stepBound (ParentQuery.firstResult r) ≤ ParentQuery.stepBound r :=
  ParentQuery.first_bound r
example (r : ParentQuery.State) (v : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row)
    (data : ParentQuery.Canonical r v clauses entries) (tr : r.pending = TraceData.encode trace) :
    (ParentQuery.phaseResult r).output = ParentQuery.answer (ParentQuery.value v clauses entries trace) :=
  ParentQuery.phase_canonical r v clauses entries trace data tr
example : ParentQuery.answer (some none) = [true, false] := rfl

#print axioms ParentQuery.defaultAnswer_exec
#print axioms ParentQuery.acceptRoot_exec
#print axioms ParentQuery.selectRoot_exec
#print axioms ParentQuery.firstPhase_exec
#print axioms ParentQuery.first_preserves
#print axioms ParentQuery.firstFuel_bound
#print axioms ParentQuery.phase_exec
#print axioms ParentQuery.phaseFuel_bound
#print axioms ParentQuery.phase_stopped
#print axioms ParentQuery.phase_canonical

end PNP.Concrete.NormalizerBlocks

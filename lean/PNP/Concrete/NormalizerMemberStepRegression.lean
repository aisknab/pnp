import PNP.Concrete.NormalizerMemberStep

namespace PNP.Concrete.NormalizerBlocks

example (r : TraceMember.State) : TraceMember.bodyFuel r ≤ 28 * r.pending.length + 80 := TraceMember.bodyFuel_bound r
example (r : TraceMember.State) (h : r.pending ≠ []) :
    (TraceMember.bodyResult r).pending = [] ∨ (TraceMember.bodyResult r).pending.length < r.pending.length :=
  TraceMember.body_progress r h
example : TraceData.next (TraceData.row (⟨false, 8⟩, some ⟨true, 12⟩) [true, false]) = [true, false] :=
  TraceData.next_canonical _ _
example (r : TraceMember.State) : (TraceMember.bodyResult r).targetTag = r.targetTag := (TraceMember.body_preserves r).2.1

#print axioms TraceMember.accept_exec
#print axioms TraceMember.choose_exec
#print axioms TraceMember.body_exec
#print axioms TraceMember.bodyFuel_bound
#print axioms TraceMember.body_preserves
#print axioms TraceMember.body_progress
#print axioms TraceMember.stepBound_mono
#print axioms TraceMember.row_comparison
#print axioms TraceMember.body_row

end PNP.Concrete.NormalizerBlocks

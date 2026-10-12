import PNP.Concrete.NormalizerMemberCanonical

namespace PNP.Concrete.NormalizerBlocks

example : TraceMember.value ⟨true, 2⟩ [(⟨false, 2⟩, none)] = false := rfl
example : TraceMember.value ⟨false, 2⟩ [(⟨true, 2⟩, none), (⟨false, 2⟩, some ⟨true, 9⟩)] = true := rfl
example : TraceMember.value ⟨true, 9⟩ [(⟨false, 2⟩, some ⟨true, 9⟩)] = false := rfl
example (r : TraceMember.State) (v : CNFLiteral) (trace : List TraceData.Row)
    (index : r.targetIndex = List.replicate v.variableIndex true)
    (tag : ForwardEdge.present r.targetTag = v.positive) (tr : r.pending = TraceData.encode trace) :
    (TraceMember.phaseResult r).output = [TraceMember.value v trace] :=
  TraceMember.phase_canonical r v trace index tag tr

#print axioms TraceMember.scan_canonical
#print axioms TraceMember.whole_canonical
#print axioms TraceMember.phase_exec
#print axioms TraceMember.phaseFuel_bound
#print axioms TraceMember.phase_stopped
#print axioms TraceMember.phase_preserves
#print axioms TraceMember.phase_canonical

end PNP.Concrete.NormalizerBlocks

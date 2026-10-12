import PNP.Concrete.NormalizerCutSelectionState
namespace PNP.Concrete.NormalizerBlocks
example (r : CutSelection.State) : (CutSelection.queried r).trace = r.trace :=
  (CutSelection.queried_frame r).1
example (r : CutSelection.State) (tag : Bool) :
    (CutSelection.emitted tag r).core.targetIndex = r.core.targetIndex :=
  (CutSelection.emitted_frame tag r).2.2.1
#print axioms CutSelection.liftMember_exec
#print axioms CutSelection.query_exec
#print axioms CutSelection.queried_frame
#print axioms CutSelection.queryFuel_bound
#print axioms CutSelection.emit_exec
#print axioms CutSelection.emitted_buffer
#print axioms CutSelection.emitted_frame
#print axioms CutSelection.choose_exec
end PNP.Concrete.NormalizerBlocks

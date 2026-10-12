import PNP.Concrete.NormalizerCutState
namespace PNP.Concrete.NormalizerBlocks
example (input : BitString) :
    (CutDriver.initialized input).trace = (CutTrace.result input).registers.output :=
  (CutDriver.initialized_fields input).2
example (r : CutDriver.State) (after : CutSelection.State) :
    (r.withSelection after).core.table = r.core.table := (CutDriver.withSelection_frame r after).2.2.1
#print axioms CutDriver.State.selection_store
#print axioms CutDriver.State.withSelection_store
#print axioms CutDriver.liftSelection_exec
#print axioms CutDriver.selection_bounded
#print axioms CutDriver.withSelection_frame
#print axioms CutDriver.trace_exec
#print axioms CutDriver.initialize_exec
end PNP.Concrete.NormalizerBlocks

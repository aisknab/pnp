import PNP.Concrete.NormalizerPreparedState

namespace PNP.Concrete.NormalizerBlocks

example (r : CutDriver.State) (after : DenseClauses.State) :
    (PreparedDriver.withDense r after).core.width = r.core.width ∧
      (PreparedDriver.withDense r after).variables = r.variables :=
  ⟨(PreparedDriver.withDense_frame r after).1,(PreparedDriver.withDense_frame r after).2.2.2.2.2⟩

example (r : CutDriver.State) (after : DenseClauses.State) :
    PreparedDriver.denseView (PreparedDriver.withDense r after) = after :=
  PreparedDriver.denseView_withDense r after

#print axioms PreparedDriver.graphDense_store
#print axioms PreparedDriver.denseGraph_store
#print axioms PreparedDriver.denseView_store
#print axioms PreparedDriver.withDense_store
#print axioms PreparedDriver.withDense_frame
#print axioms PreparedDriver.liftDense_exec
#print axioms PreparedDriver.denseView_bounded

end PNP.Concrete.NormalizerBlocks

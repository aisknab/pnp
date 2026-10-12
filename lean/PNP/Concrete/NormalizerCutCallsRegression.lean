import PNP.Concrete.NormalizerCutCalls
namespace PNP.Concrete.NormalizerBlocks
example (r : CutDriver.State) :
    (CutDriver.clauseReady r).registers.target =
      List.replicate (ClauseCount.count r.core.formula) true :=
  CutDriver.clauseReady_target r
example (tag : Bool) (r : CutDriver.State) :
    (CutDriver.selected tag r).trace = r.trace := (CutDriver.selected_frame tag r).2.2.2.1
#print axioms CutDriver.prepareClauses_exec
#print axioms CutDriver.clausePrepSteps_bound
#print axioms CutDriver.clauseReady_target
#print axioms CutDriver.clauseReady_frame
#print axioms CutDriver.prepareVariables_exec
#print axioms CutDriver.variableReady_frame
#print axioms CutDriver.select_exec
#print axioms CutDriver.selectSteps_bound
#print axioms CutDriver.selected_output
#print axioms CutDriver.selected_frame
#print axioms CutDriver.saveClauses_exec
#print axioms CutDriver.saveVariables_exec
end PNP.Concrete.NormalizerBlocks

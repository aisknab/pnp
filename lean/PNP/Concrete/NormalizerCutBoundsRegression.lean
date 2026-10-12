import PNP.Concrete.NormalizerCutBounds
namespace PNP.Concrete.NormalizerBlocks
example (input : BitString) :
    CutDriver.prepareSteps input ≤ CutDriver.prepareFuel.eval input.length :=
  CutDriver.prepareSteps_bound input
example (input : BitString) :
    (CutDriver.prepared input).store.Bounded (CutDriver.prepareSize.eval input.length) :=
  CutDriver.prepared_bounded input
#print axioms CutDriver.initial_bounded
#print axioms CutDriver.initializeSteps_bound
#print axioms CutDriver.initialized_bounded
#print axioms CutDriver.clausesSteps_input_bound
#print axioms CutDriver.afterClauses_bounded
#print axioms CutDriver.variablesSteps_input_bound
#print axioms CutDriver.prepareSteps_bound
#print axioms CutDriver.prepared_bounded
end PNP.Concrete.NormalizerBlocks

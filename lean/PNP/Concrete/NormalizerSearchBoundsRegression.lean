import PNP.Concrete.NormalizerSearchBounds
namespace PNP.Concrete.NormalizerBlocks
example : Search.seenBudget.eval 0 = 1118 := by decide
example : Search.selectBudget.eval 0 = 21025 := by decide
example : Search.pathBudget.eval 0 = 10850 := by decide
example : Search.decideBudget.eval 0 = 10861 := by decide
#print axioms Search.seenBudget_eval
#print axioms Search.selectBudget_eval
#print axioms Search.pathBudget_eval
#print axioms Search.decideBudget_eval
#print axioms Search.deriveSeenFuel_bound
#print axioms Search.selectFuel_bound
#print axioms Search.reconstructFuel_bound
#print axioms Search.decideFuel_bound
end PNP.Concrete.NormalizerBlocks

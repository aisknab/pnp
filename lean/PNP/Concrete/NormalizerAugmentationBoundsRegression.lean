import PNP.Concrete.NormalizerAugmentationBounds
namespace PNP.Concrete.NormalizerBlocks
example : Augmentation.pairBudget.eval 0 = 658 := by decide
example : Augmentation.prepareBudget.eval 0 = 661 := by decide
example (r : Augmentation.State) (bound : Nat) (checked : r.store.Bounded bound) :
    Augmentation.phaseFuel r ≤ Augmentation.phaseBudget.eval bound := Augmentation.phaseFuel_bound r bound checked
#print axioms Augmentation.pairsFuel_bound
#print axioms Augmentation.prepareFuel_bound
#print axioms Augmentation.prepared_bounded
#print axioms Augmentation.updatesFuel_bound
#print axioms Augmentation.phaseFuel_bound
end PNP.Concrete.NormalizerBlocks

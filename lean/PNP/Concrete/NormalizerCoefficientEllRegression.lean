import PNP.Concrete.NormalizerCoefficientEll
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example : Coefficient.ellRows 4 (some 1) none = [(4,false),(4,true)] := rfl
example : Coefficient.ellRows 4 (some 2) (some 2) = [(4,true)] := rfl
example (r : Coefficient.State) (n : Nat) (h : r.store.Bounded n) :
    Coefficient.ellTerms.fuel r ≤ Coefficient.ellTerms.bound.eval n := Coefficient.ellTerms.cost r n h
#print axioms Coefficient.stream_append
#print axioms Coefficient.emits_trans
#print axioms Coefficient.variableRow_emits
#print axioms Coefficient.auxiliaryRow_emits
#print axioms Coefficient.captureOwner
#print axioms Coefficient.captureOwner_index
#print axioms Coefficient.ownerAuxiliary_emits
#print axioms Coefficient.ellTerms
#print axioms Coefficient.ellTerms_data
#print axioms Coefficient.doubleEll_emits
#print axioms Coefficient.ellTerms_emits
end PNP.Concrete.NormalizerBlocks

import PNP.Concrete.NormalizerCoefficientAnchor
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : Coefficient.State) : (Coefficient.bTerms.result r).data = r.data := Coefficient.bTerms_data r
example (r : Coefficient.State) (n : Nat) (h : r.store.Bounded n) :
    Coefficient.bTerms.fuel r ≤ Coefficient.bTerms.bound.eval n := Coefficient.bTerms.cost r n h
example (index : Coefficient.Index) (position : Nat) (r : Coefficient.State) :
    ((Coefficient.readVariable index position).result r).data = r.data :=
  Coefficient.readVariable_data index position r
#print axioms Coefficient.literalRoutine
#print axioms Coefficient.readLiteral
#print axioms Coefficient.readLiteral_data
#print axioms Coefficient.readLiteral_canonical
#print axioms Coefficient.readVariable_canonical
#print axioms Coefficient.anchorEll
#print axioms Coefficient.bTerms
#print axioms Coefficient.bTerms_data
#print axioms Coefficient.anchorEll_emits
#print axioms Coefficient.bTerms_emits
end PNP.Concrete.NormalizerBlocks

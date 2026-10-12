import PNP.Concrete.NormalizerCoefficientAuxiliary
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : Coefficient.State) : (Coefficient.auxiliaryTerms.result r).data = r.data :=
  Coefficient.auxiliaryTerms_data r
example (r : Coefficient.State) (n : Nat) (h : r.store.Bounded n) :
    Coefficient.auxiliaryTerms.fuel r ≤ Coefficient.auxiliaryTerms.bound.eval n :=
  Coefficient.auxiliaryTerms.cost r n h
example (ctx : Coefficient.Context) (anchor : ctx.Literal ctx.failed 0)
    (r : Coefficient.State) (encoded : ctx.Encoded r) (row : Nat)
    (middle : ctx.Literal row 1) (rowRead : r.row = List.replicate row true) :
    Coefficient.Emits r (Coefficient.auxiliaryTerms.result r) (ctx.auxiliaryRows anchor middle) :=
  Coefficient.auxiliaryTerms_emits ctx anchor r encoded row middle rowRead
#print axioms Coefficient.copyAuxiliary
#print axioms Coefficient.currentAuxiliary
#print axioms Coefficient.currentAuxiliary_emits
#print axioms Coefficient.extendedAuxiliary
#print axioms Coefficient.auxiliaryTerms
#print axioms Coefficient.auxiliaryTerms_data
#print axioms Coefficient.extendedAuxiliary_emits
#print axioms Coefficient.auxiliaryTerms_emits
end PNP.Concrete.NormalizerBlocks

import PNP.Concrete.NormalizerCoefficientScratch
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : Coefficient.State) : (Coefficient.cleared r).data = r.data := Coefficient.cleared_data r
example (routine : Coefficient.Routine) (r : Coefficient.State) (n : Nat)
    (h : r.data.Bounded n) :
    (Coefficient.fresh routine).fuel r ≤ 18 + routine.bound.eval n :=
  Coefficient.fresh_fuel_bound routine r n h
example (routine : Coefficient.Routine) (r : Coefficient.State) (n : Nat)
    (h : r.data.Bounded n) :
    ((Coefficient.fresh routine).result r).store.Bounded (n + routine.bound.eval n) :=
  Coefficient.fresh_result_bounded routine r n h
#print axioms Coefficient.wipe_exec
#print axioms Coefficient.wiped_store
#print axioms Coefficient.resetScratch
#print axioms Coefficient.cleared_data
#print axioms Coefficient.data_bounded
#print axioms Coefficient.cleared_bounded
#print axioms Coefficient.fresh
#print axioms Coefficient.fresh_exec
#print axioms Coefficient.fresh_fuel_bound
#print axioms Coefficient.fresh_result_bounded
end PNP.Concrete.NormalizerBlocks

import PNP.Concrete.NormalizerCoefficientBasicRows
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : Coefficient.State) : (Coefficient.variableRow.result r).data = r.data :=
  Coefficient.variableRow_data r
example (r : Coefficient.State) : (Coefficient.auxiliaryRow.result r).data = r.data :=
  Coefficient.auxiliaryRow_data r
example (r : Coefficient.State) (n : Nat) (h : r.store.Bounded n) :
    Coefficient.variableRow.fuel r ≤ Coefficient.variableRow.bound.eval n :=
  Coefficient.variableRow.cost r n h
#print axioms Coefficient.queryOrdinal_output
#print axioms Coefficient.ownerRow_buffers
#print axioms Coefficient.variableRow
#print axioms Coefficient.variableRow_result
#print axioms Coefficient.variableRow_data
#print axioms Coefficient.variableRow_buffers
#print axioms Coefficient.auxiliaryRow
#print axioms Coefficient.auxiliaryRow_data
#print axioms Coefficient.auxiliaryRow_buffers
#print axioms Coefficient.extraRow_buffers
end PNP.Concrete.NormalizerBlocks

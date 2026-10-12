import PNP.Concrete.NormalizerCoefficientTruth
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : Coefficient.State) (position : Nat) :
    ((Coefficient.literalTruth position).result r).data = r.data :=
  Coefficient.literalTruth_data position r
example (r : Coefficient.State) (position n : Nat) (h : r.store.Bounded n) :
    (Coefficient.literalTruth position).fuel r ≤ (Coefficient.literalTruth position).bound.eval n :=
  (Coefficient.literalTruth position).cost r n h
example (r : Coefficient.State) :
    (Coefficient.truthAtLiteral.result r).registers.output =
      [decide (r.assignment[r.registers.target.length]?.getD false =
        ForwardEdge.present r.registers.output)] := Coefficient.truthAtLiteral_output r
#print axioms Coefficient.prepareTruth
#print axioms Coefficient.bitRoutine
#print axioms Coefficient.compareSign
#print axioms Coefficient.compareTruth_result
#print axioms Coefficient.truthAtLiteral
#print axioms Coefficient.truthAtLiteral_output
#print axioms Coefficient.truthAtLiteral_data
#print axioms Coefficient.literalTruth
#print axioms Coefficient.literalTruth_data
#print axioms Coefficient.literalTruth_canonical
end PNP.Concrete.NormalizerBlocks

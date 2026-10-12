import PNP.Concrete.NativeNormalization.MeasuredPrepared

namespace PNP.Concrete.NativeNormalization.MeasuredPreparedPolynomial

open PNP.Concrete

/-- Source-level work only; encoding and concrete execution remain separate obligations. -/
def workPolynomial : NatPolynomial :=
  let B : NatPolynomial := .add (.mul (.constant 21) .variable) (.constant 9)
  let scan : NatPolynomial :=
    .add (.add (.add MeasuredFrontendCost.scanWorkPolynomial
      (.mul (.mul (.constant 6) B) B)) (.mul (.constant 7) B)) (.constant 7)
  let selection : NatPolynomial :=
    .add (.add (.mul (.mul (.constant 3) B) B)
      (.mul (.add (.mul (.constant 2) B) (.constant 3)) B)) (.constant 3)
  let cut : NatPolynomial :=
    .add (.add (.add (.add MeasuredMatchingPolynomial.workPolynomial scan)
      selection) selection) (.constant 1)
  .add (.add cut (.mul (.add (.mul (.constant 13) B) (.constant 27)) B)) (.constant 2)

theorem workPolynomial_eval (n : Nat) :
    workPolynomial.eval n = MeasuredPrepared.prepareBound (21*n+9) := rfl

theorem decoded_prepare_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (MeasuredPrepared.prepare (NativeTseitin.frontend F)).cost ≤
      workPolynomial.eval bits.length := by
  rw [workPolynomial_eval]
  exact MeasuredPrepared.decoded_prepare_cost bits F decoded


end PNP.Concrete.NativeNormalization.MeasuredPreparedPolynomial

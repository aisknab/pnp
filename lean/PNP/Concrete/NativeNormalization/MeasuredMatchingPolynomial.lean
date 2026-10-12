import PNP.Concrete.NativeNormalization.MeasuredMatchingLoop

namespace PNP.Concrete.NativeNormalization.MeasuredMatchingPolynomial

open PNP.Concrete MeasuredMatchingLoop

/-- Explicit source-work polynomial; this is not a concrete machine-time theorem. -/
def workPolynomial : NatPolynomial :=
  let B : NatPolynomial := .add (.mul (.constant 21) .variable) (.constant 9)
  let square : NatPolynomial := .mul (.mul (.constant 3) B) B
  let twice : NatPolynomial := .mul (.constant 2) B
  let thrice : NatPolynomial := .mul (.constant 3) B
  let scanCore : NatPolynomial :=
    .add (.mul B (.add (.mul
      (.add (.add (.mul (.add twice (.constant 18)) B) B) (.constant 10)) B)
      (.constant 2))) (.constant 1)
  let scan : NatPolynomial :=
    .add (.add (.add scanCore (.mul (.mul (.constant 6) B) B))
      (.mul (.constant 7) B)) (.constant 7)
  let owner : NatPolynomial :=
    .add (.add square (.mul (.add B (.constant 4)) B)) (.constant 3)
  let candidate : NatPolynomial :=
    .add (.add square (.mul (.add (.add owner twice) (.constant 3)) B)) (.constant 3)
  let search : NatPolynomial :=
    .add (.add (.add scan candidate) thrice) (.constant 3)
  let update : NatPolynomial :=
    .add (.add square (.mul (.add thrice (.constant 6)) B)) (.constant 3)
  let round : NatPolynomial :=
    .add (.add (.add search twice) update) (.constant 3)
  .add (.add (.add square thrice) (.mul (.add B (.constant 1)) round)) (.constant 5)

theorem workPolynomial_eval (n : Nat) :
    workPolynomial.eval n = fullBound (21*n+9) := rfl

theorem decoded_fullTable_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (fullTable (NativeTseitin.frontend F)).cost ≤ workPolynomial.eval bits.length := by
  rw [workPolynomial_eval]
  exact decoded_fullTable_cost bits F decoded


end PNP.Concrete.NativeNormalization.MeasuredMatchingPolynomial

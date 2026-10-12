import PNP.Concrete.NativeNormalization.MeasuredRun

namespace PNP.Concrete.NativeNormalization.MeasuredRunPolynomial

open PNP.Concrete

def workPolynomial : NatPolynomial :=
  let B : NatPolynomial := .add (.mul (.constant 21) .variable) (.constant 9)
  let L : NatPolynomial := .add B (.constant 1)
  let square : NatPolynomial := .mul (.mul (.constant 3) B) B
  let sigma : NatPolynomial := .add (.add (.add B B) L) (.constant 1)
  let truth : NatPolynomial :=
    .add (.mul (.constant 3) (.add (.add L sigma) (.constant 1))) (.constant 2)
  let search : NatPolynomial :=
    .add (.add square (.mul (.add truth (.constant 2)) B)) (.constant 3)
  let assignment : NatPolynomial :=
    .add (.add square (.mul (.add (.add (.add B B) L) (.constant 3)) B)) (.constant 3)
  let ell : NatPolynomial :=
    .add (.add (.add B (.add (.add B B) (.constant 2))) B) (.add B (.constant 2))
  let ell : NatPolynomial := .add ell (.constant 3)
  let b : NatPolynomial := .add (.add L ell) (.constant 3)
  let literal : NatPolynomial := .add (.add (.add (.add L ell) sigma) b) (.constant 5)
  let auxiliary : NatPolynomial :=
    .add (.add (.add B (.add B (.constant 2))) literal) (.constant 2)
  let companion : NatPolynomial := .add (.add (.add B literal) auxiliary) (.constant 8)
  let rows : NatPolynomial :=
    .add (.add square (.mul (.constant 5) B)) (.constant 3)
  let remaining : NatPolynomial :=
    .add (.add square (.mul (.add B (.constant 5)) B)) (.constant 3)
  let assembly : NatPolynomial :=
    .add (.add (.add (.add (.add b rows)
      (.mul (.add companion (.constant 4)) (.mul (.constant 2) B))) remaining)
      (.mul (.add literal (.constant 4)) B)) (.constant 3)
  let run : NatPolynomial := .add (.add (.add search assignment) assembly) (.constant 1)
  .add (.add MeasuredSourceCachePolynomial.workPolynomial run) (.constant 1)

theorem workPolynomial_eval (m : Nat) :
    workPolynomial.eval m = MeasuredRun.sourceBound (21*m+9) := rfl

theorem decoded_fromSource_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (MeasuredRun.fromSource F).cost ≤ workPolynomial.eval bits.length := by
  rw [workPolynomial_eval]
  exact MeasuredRun.decoded_fromSource_cost bits F decoded


end PNP.Concrete.NativeNormalization.MeasuredRunPolynomial

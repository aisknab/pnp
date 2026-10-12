import PNP.Concrete.NativeNormalization.MeasuredSourceRecovery

namespace PNP.Concrete.NativeNormalization.MeasuredRecoveryPolynomial

open PNP.Concrete MeasuredSourceRecovery

def sizePolynomial : NatPolynomial := .add (.mul (.constant 21) .variable) (.constant 9)

def finishPolynomial : NatPolynomial :=
  let B := sizePolynomial
  let square : NatPolynomial := .mul (.mul (.constant 3) B) B
  let owner : NatPolynomial :=
    .add (.add square (.mul (.add B (.constant 4)) B)) (.constant 3)
  let bit : NatPolynomial :=
    .add (.add (.add owner (.mul (.constant 4) B)) B) (.constant 16)
  let cut : NatPolynomial :=
    .add (.add square (.mul (.add bit (.constant 2)) B)) (.constant 3)
  let project : NatPolynomial :=
    .add (.add square (.mul (.add B (.constant 3)) B)) (.constant 3)
  .add (.add cut project) (.constant 1)

theorem finishPolynomial_eval (m : Nat) :
    finishPolynomial.eval m = finishBound (21*m+9) (21*m+9) := rfl

def candidatePolynomial : NatPolynomial :=
  let B := sizePolynomial
  let L : NatPolynomial := .add B (.constant 1)
  let square : NatPolynomial := .mul (.mul (.constant 3) B) B
  let assignment : NatPolynomial :=
    .add (.add square (.mul (.add (.add (.add B B) L) (.constant 3)) B)) (.constant 3)
  .add (.add assignment finishPolynomial) (.constant 1)

theorem candidatePolynomial_eval (m : Nat) :
    candidatePolynomial.eval m = candidateBound (21*m+9) := rfl

def witnessPolynomial : NatPolynomial :=
  let B := sizePolynomial
  let L : NatPolynomial := .add B (.constant 1)
  let R : NatPolynomial := .add (.mul (.constant 2) B) (.constant 4)
  let square : NatPolynomial := .mul (.mul (.constant 3) B) B
  let ell : NatPolynomial :=
    .add (.add (.add (.add B (.add (.add B B) (.constant 2))) B)
      (.add B (.constant 2))) (.constant 3)
  let b : NatPolynomial := .add (.add L ell) (.constant 3)
  let sigma : NatPolynomial := .add (.add (.add B B) L) (.constant 1)
  let bit : NatPolynomial :=
    .add (.add (.add (.add ell (.mul (.add R (.constant 2)) (.constant 2)))
      (.constant 1)) sigma) (.constant 2)
  let recover : NatPolynomial :=
    .add (.add (.add (.add b (.mul (.add R (.constant 2)) (.constant 3)))
      square) (.mul (.add bit (.constant 2)) B)) (.constant 4)
  .add (.add recover finishPolynomial) (.constant 1)

theorem witnessPolynomial_eval (m : Nat) :
    witnessPolynomial.eval m = witnessBound (21*m+9) := rfl

theorem decoded_candidate_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) (b : Cache F) :
    (candidate F b).cost ≤ candidatePolynomial.eval bits.length := by
  rw [candidatePolynomial_eval]
  exact decoded_candidate_cost bits F decoded b

theorem decoded_witness_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) (b : Cache F) (failed : Fin b.rows) (a : BitString) :
    (witness F b failed a).cost ≤ witnessPolynomial.eval bits.length := by
  rw [witnessPolynomial_eval]
  exact decoded_witness_cost bits F decoded b failed a


end PNP.Concrete.NativeNormalization.MeasuredRecoveryPolynomial

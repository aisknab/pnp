import PNP.Concrete.NativeNormalization.MeasuredSourceCache

namespace PNP.Concrete.NativeNormalization.MeasuredSourceCachePolynomial

open PNP.Concrete MeasuredOperations

def workPolynomial : NatPolynomial :=
  let B : NatPolynomial := .add (.mul (.constant 21) .variable) (.constant 9)
  let L : NatPolynomial := .add B (.constant 4)
  let owner : NatPolynomial :=
    .add (.add (.mul (.mul (.constant 3) B) B) (.mul (.add B (.constant 4)) B)) (.constant 3)
  let partner : NatPolynomial := .add (.add owner (.mul (.constant 3) B)) (.constant 4)
  let slot : NatPolynomial := .add (.add partner (.mul (.constant 2) B)) (.constant 12)
  let mode : NatPolynomial := .add (.mul (.constant 6) B) (.constant 16)
  let literals : NatPolynomial := .mul (.add (.mul (.constant 3) L) (.constant 3)) B
  let owners : NatPolynomial := .mul (.add partner (.constant 2)) B
  let slots : NatPolynomial := .mul (.add slot (.constant 2)) B
  let modes : NatPolynomial := .mul (.add mode (.constant 2)) B
  let cache : NatPolynomial :=
    .add (.add (.add (.add (.add (.mul (.mul (.constant 6) B) B)
      literals) owners) slots) modes) (.constant 7)
  .add (.add (.add MeasuredPreparedPolynomial.workPolynomial cache) B) (.constant 3)

theorem workPolynomial_eval (n : Nat) :
    workPolynomial.eval n = MeasuredSourceCache.buildBound (21*n+9) := rfl

theorem decoded_fromSource_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (MeasuredSourceCache.fromSource F).cost ≤ workPolynomial.eval bits.length := by
  rw [workPolynomial_eval]
  exact MeasuredSourceCache.decoded_fromSource_cost bits F decoded

theorem decoded_cached_read_bounds (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    Bounded (MeasuredCache.operations (MeasuredSourceCache.fromSource F).value.data)
      (21*bits.length+9+1) (21*bits.length+9) (21*bits.length+9) (21*bits.length+9) := by
  have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
  exact MeasuredSourceCache.cached_operations_bounded (MeasuredSourceCache.fromSource F).value
    (21*bits.length+9) (by omega)


end PNP.Concrete.NativeNormalization.MeasuredSourceCachePolynomial

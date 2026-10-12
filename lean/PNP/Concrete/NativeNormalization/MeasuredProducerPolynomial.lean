import PNP.Concrete.NativeNormalization.MeasuredProducer

namespace PNP.Concrete.NativeNormalization.MeasuredProducerPolynomial

open PNP.Concrete MeasuredProducer

def constructionPolynomial : NatPolynomial :=
  .add (.add MeasuredRunPolynomial.workPolynomial MeasuredRecoveryPolynomial.finishPolynomial)
    (.constant 2)

theorem constructionPolynomial_eval (m : Nat) :
    constructionPolynomial.eval m = produceBound (21*m+9) := rfl

def CallbackBound (m : Nat) : Result → Prop
  | .model _ => True
  | .system _ _ recover => ∀ a, (recover a).cost ≤ MeasuredRecoveryPolynomial.witnessPolynomial.eval m

theorem decoded_construction_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (produce F).cost ≤ constructionPolynomial.eval bits.length := by
  rw [constructionPolynomial_eval]
  exact decoded_produce_cost bits F decoded

theorem decoded_callback_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) : CallbackBound bits.length (produce F).value := by
  have h := decoded_recovery_bound bits F decoded
  cases he : (produce F).value with
  | model a => trivial
  | system c D recover =>
      rw [he] at h
      simpa only [CallbackBound,RecoveryBound,MeasuredRecoveryPolynomial.witnessPolynomial_eval] using h

/-- Construction and recovery are separately bounded; decoding/conversion and bit-level
machine refinement remain outside this account. No witness-search assertion is present. -/
theorem decoded_verified_program (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    Correct F (produce F).value ∧
      (produce F).cost ≤ constructionPolynomial.eval bits.length ∧
      CallbackBound bits.length (produce F).value :=
  ⟨produce_correct F,decoded_construction_polynomial bits F decoded,
    decoded_callback_polynomial bits F decoded⟩


end PNP.Concrete.NativeNormalization.MeasuredProducerPolynomial

import PNP.Concrete.NativeNormalization.MeasuredDecoder
import PNP.Concrete.NativeNormalization.MeasuredProducerPolynomial

namespace PNP.Concrete.NativeNormalization.MeasuredEncodedProducer

open PNP.Concrete MeasuredReach NativeSparseSystem

inductive Result where
  | malformed
  | success (result : MeasuredProducer.Result)

def Correct (bits : BitString) : Result → Prop
  | .malformed => decodeEncodedCNF bits = none
  | .success r => ∃ F, decodeEncodedCNF bits = some F ∧ MeasuredProducer.Correct F r

/-- Strict decoding is performed once. The source-operation account now includes
its materialization work; frontend construction is still an explicit open cost. -/
def convert (bits : BitString) : Measured Result :=
  let parsed := MeasuredDecoder.decode bits
  match parsed.value with
  | none => ⟨.malformed,parsed.cost+1⟩
  | some F =>
      let produced := MeasuredProducer.produce F
      ⟨.success produced.value,parsed.cost+produced.cost+1⟩

theorem convert_correct (bits : BitString) : Correct bits (convert bits).value := by
  cases hd : (MeasuredDecoder.decode bits).value with
  | none =>
      simp only [convert,hd,Correct]
      exact (MeasuredDecoder.decode_value bits).symm.trans hd
  | some F =>
      have decoded : decodeEncodedCNF bits = some F :=
        (MeasuredDecoder.decode_value bits).symm.trans hd
      simpa only [convert,hd,Correct] using
        (show ∃ G, decodeEncodedCNF bits = some G ∧ MeasuredProducer.Correct G (MeasuredProducer.produce F).value from
          ⟨F,decoded,MeasuredProducer.produce_correct F⟩)

theorem malformed_iff (bits : BitString) :
    (convert bits).value = .malformed ↔ decodeEncodedCNF bits = none := by
  rw [← MeasuredDecoder.decode_value bits]
  cases hd : (MeasuredDecoder.decode bits).value <;> simp [convert,hd]

def accountedWorkPolynomial : NatPolynomial :=
  .add (.add MeasuredDecoder.workPolynomial MeasuredProducerPolynomial.constructionPolynomial)
    (.constant 1)

theorem accountedWorkPolynomial_eval (m : Nat) :
    accountedWorkPolynomial.eval m =
      MeasuredDecoder.workPolynomial.eval m+
      MeasuredProducerPolynomial.constructionPolynomial.eval m+1 := rfl

theorem convert_accounted_polynomial (bits : BitString) :
    (convert bits).cost ≤ accountedWorkPolynomial.eval bits.length := by
  have hd := MeasuredDecoder.decode_polynomial bits
  rw [accountedWorkPolynomial_eval]
  cases hp : (MeasuredDecoder.decode bits).value with
  | none =>
      simp only [convert,hp]
      omega
  | some F =>
      have decoded : decodeEncodedCNF bits = some F :=
        (MeasuredDecoder.decode_value bits).symm.trans hp
      have hc := MeasuredProducerPolynomial.decoded_construction_polynomial bits F decoded
      simp only [convert,hp]
      omega

def RecoveryBound (m : Nat) : Result → Prop
  | .malformed => True
  | .success r => MeasuredProducerPolynomial.CallbackBound m r

theorem convert_recovery_bound (bits : BitString) :
    RecoveryBound bits.length (convert bits).value := by
  cases hp : (MeasuredDecoder.decode bits).value with
  | none => simp only [convert,hp,RecoveryBound]
  | some F =>
      have decoded : decodeEncodedCNF bits = some F :=
        (MeasuredDecoder.decode_value bits).symm.trans hp
      simpa only [convert,hp,RecoveryBound] using
        MeasuredProducerPolynomial.decoded_callback_polynomial bits F decoded

/-- Exact all-input semantics plus the current source-work account. This is not
a total runtime theorem: frontend construction and concrete refinement remain open. -/
theorem convert_verified (bits : BitString) :
    Correct bits (convert bits).value ∧
      (convert bits).cost ≤ accountedWorkPolynomial.eval bits.length ∧
      RecoveryBound bits.length (convert bits).value :=
  ⟨convert_correct bits,convert_accounted_polynomial bits,convert_recovery_bound bits⟩

theorem model_sound (bits a : BitString)
    (h : (convert bits).value = .success (.model a)) : CNFSAT bits := by
  have hc := convert_correct bits
  rw [h] at hc
  obtain ⟨F,hd,hs⟩ := hc
  exact ⟨F,hd,a,hs⟩

theorem system_iff (bits : BitString) (c : Nat) (D : System c)
    (liftModel : BitString → Measured BitString)
    (h : (convert bits).value = .success (.system c D liftModel)) :
    CNFSAT bits ↔ ∃ a : BitString, a.length = 2*c ∧ D.Satisfied (MeasuredBits.rowValues c a) := by
  have hc := convert_correct bits
  rw [h] at hc
  obtain ⟨F,hd,hs⟩ := hc
  constructor
  · rintro ⟨G,hg,ha⟩
    have equal : G = F := Option.some.inj (hg.symm.trans hd)
    subst G
    exact hs.1.mp ha
  · intro ha
    exact ⟨F,hd,hs.1.mpr ha⟩

theorem system_recovery (bits : BitString) (c : Nat) (D : System c)
    (liftModel : BitString → Measured BitString)
    (h : (convert bits).value = .success (.system c D liftModel))
    (a : BitString) (ha : D.Satisfied (MeasuredBits.rowValues c a)) :
    ∃ F, decodeEncodedCNF bits = some F ∧ F.Satisfied (liftModel a).value := by
  have hc := convert_correct bits
  rw [h] at hc
  obtain ⟨F,hd,hs⟩ := hc
  exact ⟨F,hd,hs.2.1 a ha⟩


end PNP.Concrete.NativeNormalization.MeasuredEncodedProducer

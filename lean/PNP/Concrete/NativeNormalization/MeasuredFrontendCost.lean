import PNP.Concrete.NativeNormalization.MeasuredMatching
import PNP.Concrete.NativeNormalization.NativeFrontendBounds

namespace PNP.Concrete.NativeNormalization.MeasuredFrontendCost

open PNP.Concrete NativeTseitin MatchingCache

/-- Reuse the public exact schedule length and decoder bounds; no private core names. -/
theorem frontend_encoded_counts (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (frontend F).variableCount ≤ 6*bits.length+3 ∧
    (frontend F).clauses.length ≤ 15*bits.length+6 := by
  have width := CNFCore.decoded_width_bound bits F decoded
  have plan := CNFToNAND.formulaPlan_length_le_encoded_bits bits F decoded
  rw [CNFToNAND.formulaPlan_length_exact] at plan
  have counts := NativeFrontend.frontend_counts_bound F
  constructor <;> omega

def scanEnvelope (B : Nat) : Nat :=
  B*((((2*B+18)*B+B+10)*B)+2)+1

theorem scan_le_envelope (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) :
    (MeasuredMatching.scan F T).cost ≤ scanEnvelope B := by
  have base := MeasuredMatching.scan_cost F T shape
  have hc : F.clauses.length ≤ B := by omega
  have hv : F.clauses.length+F.variableCount ≤ B := size
  have he : 2*F.clauses.length+15+3 ≤ 2*B+18 := by omega
  have hp := Nat.mul_le_mul he hv
  have middle :
      (2*F.clauses.length+15+3)*(F.clauses.length+F.variableCount)+
        (F.clauses.length+3)+7 ≤ (2*B+18)*B+B+10 := by omega
  have inner := Nat.add_le_add_right (Nat.mul_le_mul middle hv) 2
  exact Nat.le_trans base (Nat.add_le_add_right (Nat.mul_le_mul hv inner) 1)

/-- This bounds one graph pass on an already materialized matching table.
The matching-construction loop, encoders and concrete-machine simulation remain open. -/
theorem decoded_frontend_scan_cost (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F)
    (T : Table (frontend F).clauses.length (frontend F).variableCount) :
    (MeasuredMatching.scan (frontend F) T).cost ≤ scanEnvelope (21*bits.length+9) := by
  have shape : ∀ i, (CNFCore.clause (frontend F) i).length ≤ 3 := by
    intro i
    exact Nat.le_of_eq (frontend_shape F _ (CNFCore.source_member (frontend F) i)).1
  have sizes := frontend_encoded_counts bits F decoded
  exact scan_le_envelope (frontend F) T shape (21*bits.length+9) (by omega)

def scanWorkPolynomial : NatPolynomial :=
  let size : NatPolynomial := .add (.mul (.constant 21) .variable) (.constant 9)
  let factor : NatPolynomial := .add (.mul (.constant 2) size) (.constant 18)
  let pass : NatPolynomial := .add (.add (.mul factor size) size) (.constant 10)
  .add (.mul size (.add (.mul pass size) (.constant 2))) (.constant 1)

theorem scanWorkPolynomial_eval (n : Nat) :
    scanWorkPolynomial.eval n = scanEnvelope (21*n+9) := rfl

theorem decoded_frontend_scan_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F)
    (T : Table (frontend F).clauses.length (frontend F).variableCount) :
    (MeasuredMatching.scan (frontend F) T).cost ≤ scanWorkPolynomial.eval bits.length := by
  rw [scanWorkPolynomial_eval]
  exact decoded_frontend_scan_cost bits F decoded T


end PNP.Concrete.NativeNormalization.MeasuredFrontendCost

import PNP.Concrete.ResidualReduction.SourceOriginalSuccessorOutput
import PNP.Concrete.ResidualReduction.SourcePolynomialSelector

/-! One original-input-size bound for all construction phases. The chart packet
does not inherit a caller-chosen size: its row count and width come from the
original family. The final compiler lift will account for physical word copies. -/

namespace PNP.Concrete.ResidualReduction.SourceOriginalSuccessorBounds
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceWitnessSelection
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorChart (family)
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (codec)

theorem charted_bound_mono {a b : Nat} (h : a ≤ b) :
    SourceChartedSuccessorBounds.bound a ≤ SourceChartedSuccessorBounds.bound b := by
  have scalar := SourceChartedSuccessorBounds.scalar_bound_mono h
  have square := Nat.mul_le_mul (Nat.add_le_add_right h 1) (Nat.add_le_add_right h 1)
  unfold SourceChartedSuccessorBounds.bound
  omega

theorem packet_bound {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) :
    (SourceChartedSuccessorInput.packet (family F w c) c.1 w.normals).length ≤
      4 * (codec.encode ⟨n + 1,F⟩).length + 5 := by
  have packet := SourceChartedSuccessorInput.packet_length (family F w c) c.1 w.normals
  have normals := SourceChartedSuccessorBounds.normals_length w.normals
  have familyLength := SourceChartFamily.output_length F w.weights c.1 c.2
  have original := SourceMatrixEncoding.codec_length (n + 1) F
  have dimension := SourceMatrixEncoding.dimension_bound (n + 1) F
  have pivot := c.1.isLt
  change ((SourceEncoding.familyCodec (n + 1)).encode (family F w c)).length =
    (2 * n + 6) * F.length + 1 at familyLength
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc] at original familyLength
  omega

theorem prepare_bound {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) :
    SourceOriginalSuccessorApply.prepareFuel F w c ≤ 32 * (codec.encode ⟨n + 1,F⟩).length + 76 := by
  have normals := SourceChartedSuccessorBounds.normals_length w.normals
  have dimension := SourceMatrixEncoding.dimension_bound (n + 1) F
  have pivot := c.1.isLt
  unfold SourceOriginalSuccessorApply.prepareFuel SourceOriginalSuccessorChoice.normalBytes
  omega

theorem apply_bound {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) :
    let L := (codec.encode ⟨n + 1,F⟩).length
    SourceOriginalSuccessorApply.fuel F w c ≤ 32 * L + 76 + SourceChartedSuccessorBounds.bound (4 * L + 5) := by
  dsimp only
  have prepare := prepare_bound F w c
  have execute := SourceChartedSuccessorBounds.source_bound (family F w c) c.1 w.normals
  have size := charted_bound_mono (packet_bound F w c)
  unfold SourceOriginalSuccessorApply.fuel
  omega

def postBudget (L : Nat) : Nat :=
  SourceChartedSuccessorBounds.bound (4 * L + 5) + 70 * (L * L) + 250 * L + 500
def constructFuel {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) : Nat :=
  SourceOriginalSuccessorChoice.fuel F w + (SourceOriginalSuccessorChart.chosenFuel F c +
    (1 + (53 + (SourceOriginalSuccessorApply.fuel F w c + SourceOriginalSuccessorOutput.fuel F w c))))

theorem positive_bound {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) :
    1 + (SourceOriginalSuccessorInput.headersFuel (n + 1) F.length + (1 + constructFuel F w c)) ≤
      postBudget (codec.encode ⟨n + 1,F⟩).length := by
  have dimension := SourceMatrixEncoding.dimension_bound (n + 1) F
  have rows := SourceMatrixEncoding.rowCount_bound (n + 1) F
  have pivot := c.1.isLt
  have choice := SourceOriginalSuccessorChoice.fuel_bound F w
  have chart := SourceOriginalSuccessorChart.chosenFuel_bound F c
  have applyRun := apply_bound F w c
  have output := SourceOriginalSuccessorOutput.fuel_bound F w c
  dsimp only at chart applyRun
  simp only [SourceOriginalSuccessorInput.headersFuel,constructFuel,postBudget,
    Nat.add_mul,Nat.mul_assoc] at *
  omega

theorem absent_chart_bound {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) :
    1 + (SourceOriginalSuccessorInput.headersFuel (n + 1) F.length +
      (1 + (SourceOriginalSuccessorChoice.fuel F w + ((5 * (n + 1) + 12) + 51)))) ≤
      postBudget (codec.encode ⟨n + 1,F⟩).length := by
  have dimension := SourceMatrixEncoding.dimension_bound (n + 1) F
  have rows := SourceMatrixEncoding.rowCount_bound (n + 1) F
  have choice := SourceOriginalSuccessorChoice.fuel_bound F w
  simp only [SourceOriginalSuccessorInput.headersFuel,postBudget]
  omega

theorem zero_bound (F : Family 0) :
    1 + (SourceOriginalSuccessorInput.headersFuel 0 F.length + 51) ≤
      postBudget (codec.encode ⟨0,F⟩).length := by
  have rows := SourceMatrixEncoding.rowCount_bound 0 F
  simp only [SourceOriginalSuccessorInput.headersFuel,postBudget]
  omega

theorem failure_bound (L : Nat) : 51 ≤ postBudget L := by unfold postBudget; omega

def cubic (x : NatPolynomial) : NatPolynomial :=
  .add (.add (.mul (.constant 22) (.mul (.mul x x) x))
    (.mul (.constant 191) (.mul x x))) (.add (.mul (.constant 1426) x) (.constant 1737))
def postPolynomial : NatPolynomial :=
  .add (cubic (.linear 4 5)) (.add (.mul (.constant 70) (.mul .variable .variable)) (.linear 250 500))
theorem postPolynomial_eval (L : Nat) : postPolynomial.eval L = postBudget L := by
  simp only [postPolynomial,cubic,NatPolynomial.eval_add,NatPolynomial.eval_mul,
    NatPolynomial.eval_constant,NatPolynomial.eval_variable,NatPolynomial.eval_linear,
    postBudget,SourceChartedSuccessorBounds.bound_cubic]
  omega

def sourceFuel : NatPolynomial := .add SourcePolynomialSelector.sourceFuel (.add postPolynomial (.constant 51))
theorem sourceFuel_eval (L : Nat) :
    sourceFuel.eval L = SourceRawSelector.sourceBudget L + 51 + postBudget L + 1 := by
  simp only [sourceFuel,NatPolynomial.eval_add,NatPolynomial.eval_constant,
    SourcePolynomialSelector.sourceFuel_eval,postPolynomial_eval]
  omega

end PNP.Concrete.ResidualReduction.SourceOriginalSuccessorBounds

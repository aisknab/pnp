import PNP.Concrete.ResidualReduction.SourceMatrixPacket

namespace PNP.Concrete.ResidualReduction.SourceMatrixPacket
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixConstruction

def budget (n rows : Nat) : Nat := payloadBudget n rows + headerFuel n rows
theorem fuel_bound {n : Nat} (F : Family n) : fuel n F.length ≤ budget n F.length :=
  Nat.add_le_add_right (payloadFuel_bound F) _

theorem budget_mono {n N rows R : Nat} (dimension : n ≤ N) (count : rows ≤ R) :
    budget n rows ≤ budget N R := by
  have coefficient : 24 * n + 62 ≤ 24 * N + 62 := by omega
  have rowWork := Nat.mul_le_mul coefficient count
  have columnWork := Nat.mul_le_mul (Nat.add_le_add_right rowWork 6) dimension
  have allWork := Nat.mul_le_mul (Nat.add_le_add_right columnWork 7) dimension
  have data := Nat.mul_le_mul (Nat.add_le_add_right count 1) (Nat.mul_le_mul dimension dimension)
  have header := Nat.mul_le_mul (show 3 * n + 4 ≤ 3 * N + 4 by omega) dimension
  have square := Nat.mul_le_mul dimension dimension
  unfold budget payloadBudget headerFuel
  omega

/-- Bound the actual prepared constructor by the original family packet
length. This is not yet an all-input machine theorem: raw validation must
construct the prepared state and its cost must also be included. -/
theorem original_input_fuel_bound (n : Nat) (F : Family n) :
    fuel n F.length ≤ budget (SourceMatrixEncoding.codec.encode ⟨n, F⟩).length
      (SourceMatrixEncoding.codec.encode ⟨n, F⟩).length :=
  Nat.le_trans (fuel_bound F) (budget_mono (SourceMatrixEncoding.dimension_bound n F)
    (SourceMatrixEncoding.rowCount_bound n F))

end PNP.Concrete.ResidualReduction.SourceMatrixPacket

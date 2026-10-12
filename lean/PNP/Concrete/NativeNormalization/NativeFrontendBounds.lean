import PNP.Concrete.NativeNormalization.NativeFrontend
import PNP.Concrete.LockedNANDRawBuilder

namespace PNP.Concrete.NativeNormalization.NativeFrontend

open PNP.Concrete CNFCore NativeBasis NativeEquations NativeSparseSystem NativeTseitin

/-- Explicit data-size bounds in source literal and clause counts, not runtime. -/
theorem frontend_counts_bound (F : CNFFormula) :
    (frontend F).variableCount ≤
      F.variableCount + 4 * CNFToNAND.literalCount F + 2 * F.clauses.length + 3 ∧
    (frontend F).clauses.length ≤
      12 * CNFToNAND.literalCount F + 6 * F.clauses.length + 6 := by
  have hg := CNFToNAND.compileFormula_gateCount_le F
  change (LockedNAND.rawProgramGates (CNFToNAND.compiledFormulaCircuit F).program).length ≤
    4 * CNFToNAND.literalCount F + 2 * F.clauses.length + 1 at hg
  rw [LockedNAND.RawBuilder.rawProgramGates_length] at hg
  obtain ⟨hw, hc, _⟩ := formula_shape (CNFToNAND.compiledFormulaCircuit F)
  change (frontend F).variableCount = _ at hw
  change (frontend F).clauses.length = _ at hc
  constructor <;> omega

theorem retained_rows_bound (F : CNFFormula) :
    (positions (frontend F)).length ≤
      12 * CNFToNAND.literalCount F + 6 * F.clauses.length + 6 := by
  have h := List.length_filter_le (kept (frontend F))
    (List.finRange (frontend F).clauses.length)
  have hl : (positions (frontend F)).length ≤ (frontend F).clauses.length := by
    simpa [positions] using h
  exact Nat.le_trans hl (frontend_counts_bound F).2

theorem produced_system_bound (F : CNFFormula) (c : Nat) (D : System c)
    (liftModel : RowValues c → BitString)
    (h : produce F = .system c D liftModel) :
    c ≤ 12 * CNFToNAND.literalCount F + 6 * F.clauses.length + 6 ∧
    D.coefficientCount ≤
      240 * CNFToNAND.literalCount F + 120 * F.clauses.length + 123 := by
  have hc := produce_correct F
  rw [h] at hc
  obtain ⟨_, _, he, hb⟩ := hc
  have hr := retained_rows_bound F
  have hd := hb.2.2.2.2.2
  omega


end PNP.Concrete.NativeNormalization.NativeFrontend

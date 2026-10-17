import PNP.Concrete.ResidualReduction.SourceTailPolynomialAffine
import PNP.Concrete.ResidualReduction.SourceComputedTailEncoding

/-! Derive the complete candidate polynomial from its encoded tail form.
The branch bit and every affine coefficient are consumed from the input.
No successful equality, precomputed polynomial or semantic callback is used. -/

namespace PNP.Concrete.ResidualReduction.SourceTailPolynomial
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceScalarState

def plane : Block 16 := .seq SourceScalarRow.selected SourceTailPolynomialAffine.block
def planeFuel (n : Nat) : Nat := SourceScalarRow.selectedFuel n + SourceTailPolynomialAffine.fuel n

theorem plane_exec {n : Nat} (a b u : Affine n) (suffix savedStream : BitString) :
    Exec plane (full (work (affineWord a ++ (affineWord b ++ (affineWord u ++ suffix))))
      emptySaved (data savedStream (zero n))) (planeFuel n)
      (state suffix (TailForm.plane a b u).polynomial) := by
  have product := SourceScalarRow.selected_exec a b (zero n) (affineWord u ++ suffix) savedStream
  rw [add_zero_left] at product
  have affine := SourceTailPolynomialAffine.block_exec u (qProduct a b) suffix (affineWord u ++ suffix)
  exact Exec.seq product affine

def block : Block 16 := .branch 0 .skip
  (.seq (.action (.pop 0)) SourceTailPolynomialAffine.block)
  (.seq (.action (.pop 0)) plane)
def fuel {n : Nat} : TailForm n → Nat
  | .affine _ => 2 + SourceTailPolynomialAffine.fuel n
  | .plane _ _ _ => 2 + planeFuel n

theorem block_exec {n : Nat} (t : TailForm n) (suffix savedStream : BitString) :
    Exec block (full (work ((SourceComputedTailEncoding.codec n).encode t ++ suffix))
      emptySaved (data savedStream (zero n))) (fuel t) (state suffix t.polynomial) := by
  cases t with
  | affine u =>
    have pop : Exec (.action (.pop (0 : Fin 16)))
        (full (work (false :: (affineWord u ++ suffix))) emptySaved (data savedStream (zero n))) 1
        (full (work (affineWord u ++ suffix)) emptySaved (data savedStream (zero n))) := .action _ _
    have affine := SourceTailPolynomialAffine.block_exec u (zero n) suffix savedStream
    rw [add_zero_left] at affine
    have checked := Exec.zero (source := (0 : Fin 16)) (empty := .skip)
      (one := .seq (.action (.pop 0)) plane) rfl (Exec.seq pop affine)
    have cost : fuel (TailForm.affine u) = 1 + (1 + SourceTailPolynomialAffine.fuel n) := by
      simp only [fuel]
      omega
    simpa only [block,cost,SourceComputedTailEncoding.affine_bytes,List.cons_append,
      TailForm.polynomial] using checked
  | plane a b u =>
    have pop : Exec (.action (.pop (0 : Fin 16)))
        (full (work (true :: (affineWord a ++ (affineWord b ++ (affineWord u ++ suffix)))))
          emptySaved (data savedStream (zero n))) 1
        (full (work (affineWord a ++ (affineWord b ++ (affineWord u ++ suffix))))
          emptySaved (data savedStream (zero n))) := .action _ _
    have checked := Exec.one (source := (0 : Fin 16)) (empty := .skip)
      (zero := .seq (.action (.pop 0)) SourceTailPolynomialAffine.block) rfl
      (Exec.seq pop (plane_exec a b u suffix savedStream))
    have cost : fuel (TailForm.plane a b u) = 1 + (1 + planeFuel n) := by
      simp only [fuel]
      omega
    simpa only [block,cost,SourceComputedTailEncoding.plane_bytes,List.cons_append,
      List.append_assoc] using checked

theorem affine_fuel {n : Nat} (u : Affine n) :
    fuel (.affine u) = 22 * quadraticBits n + 22 * n + 38 := by
  rw [fuel,SourceTailPolynomialAffine.fuel_exact]
  omega
theorem plane_fuel {n : Nat} (a b u : Affine n) :
    fuel (.plane a b u) = 44 * quadraticBits n + 50 * n + 83 := by
  simp only [fuel,planeFuel,SourceTailPolynomialAffine.fuel_exact,
    SourceScalarRow.selectedFuel,SourceScalarRow.loadFuel,SourceScalarRow.addFuel,
    SourcePlaneRemainderInstructions.productFuel_exact]
  omega
theorem fuel_bound {n : Nat} (t : TailForm n) :
    fuel t ≤ 44 * quadraticBits n + 50 * n + 83 := by
  cases t with
  | affine u => rw [affine_fuel]; omega
  | plane a b u => rw [plane_fuel]; exact Nat.le_refl _

end PNP.Concrete.ResidualReduction.SourceTailPolynomial

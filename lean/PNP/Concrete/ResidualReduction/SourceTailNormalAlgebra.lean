import PNP.Concrete.ResidualReduction.SourceChartAffine
import PNP.Concrete.ResidualReduction.SourceMenuBytes
import PNP.Concrete.ResidualReduction.SourceScalarTail

/-! Homogeneous normalization commutes with deleting a variable coefficient.
Thus the exact selected tail normal is obtained by deleting the pivot from
the original factor and replacing its constant coefficient with false. -/

namespace PNP.Concrete.ResidualReduction.SourceTailNormalAlgebra
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceMenuBytes
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra

theorem cut_homogeneous (n : Nat) (k : Fin (n + 1)) (f : Affine (n + 1)) :
    cut n k (homogeneousRow f) = ((cut n k f).1,homogeneousRow (cut n k f).2) := by
  induction n with
  | zero =>
    rcases f with ⟨b,c⟩
    rw [homogeneous_cons]
    rfl
  | succ n ih =>
    by_cases hz : k.val = 0
    · have hk : k = 0 := Fin.ext hz
      subst k
      rcases f with ⟨b,f⟩
      simp only [homogeneous_cons,cut_zero]
    · let j : Fin (n + 1) := ⟨k.val - 1,by omega⟩
      have hk : j.succ = k := Fin.ext (by simp only [Fin.val_succ,j]; omega)
      rw [← hk]
      rcases f with ⟨b,f⟩
      simp only [homogeneous_cons,cut_succ,ih]
      rfl

theorem tailNormal_eq {n : Nat} (k : Fin (n + 1)) (f : Affine (n + 1)) :
    tailNormal k f = homogeneousRow (cut n k f).2 := by
  simp only [tailNormal,cut_homogeneous]

theorem homogeneous_word {n : Nat} (f : Affine n) :
    affineWord (homogeneousRow f) = normalWord f ++ [false] := by
  rw [SourceMenuBytes.homogeneous_bytes]
  have same : CoefficientComparison.normalBits f = normalWord f := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rcases f with ⟨b,f⟩
      exact congrArg (List.cons b) (ih f)
  rw [same]

theorem tailNormal_word {n : Nat} (k : Fin (n + 1)) (f : Affine (n + 1)) :
    affineWord (tailNormal k f) = normalWord (cut n k f).2 ++ [false] := by
  rw [tailNormal_eq,homogeneous_word]

end PNP.Concrete.ResidualReduction.SourceTailNormalAlgebra

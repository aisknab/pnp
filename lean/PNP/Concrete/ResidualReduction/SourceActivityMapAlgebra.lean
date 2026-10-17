import PNP.Concrete.ResidualReduction.SourcePolarRowAlgebra
import PNP.Concrete.ResidualReduction.SourceActivityMatrix

/-! Exact activity coefficients on an arbitrary affine direction map. The
variable coefficients of both pullbacks are used with the ORIGINAL source
constants, not their translated pullback constants. This distinction permits
nonzero map origins without changing the meaning of a direction. -/

namespace PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourcePolarRowAlgebra
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra

def value (a0 b0 a b : Bool) : Bool :=
  Bool.xor (Bool.xor a a0 && Bool.xor b b0) (a0 && b0)
theorem eval_linear_constant {n : Nat} (a : Affine n) (x : Point n) :
    aEval a x = Bool.xor (linearEval a x) (aConstant a) := by
  simp only [linearEval, homogeneousRow_eval, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
theorem activity_value {n : Nat} (r : Row n) (x : Point n) :
    activity r x = value (aConstant r.left) (aConstant r.right)
      (linearEval r.left x) (linearEval r.right x) := by
  simp only [activity, Row.eval, eval_zero_constant]
  simp only [value, eval_linear_constant]
theorem coefficient_value {n : Nat} (r : Row n) (s : Space n) (j : Fin s.parameters) :
    activityCoefficients r s j = value (aConstant r.left) (aConstant r.right)
      (bitAt (affineWord (pullback r.left s.forms)) j.val)
      (bitAt (affineWord (pullback r.right s.forms)) j.val) := by
  simp only [activityCoefficients, activity_value, Space.direction, linearEval_pullback_unit]

def bits (a0 b0 : Bool) : {k : Nat} → Affine k → Affine k → BitString
  | 0, _, _ => []
  | _ + 1, (a, f), (b, g) => value a0 b0 a b :: bits a0 b0 f g
theorem bits_length {k : Nat} (a0 b0 : Bool) (f g : Affine k) :
    (bits a0 b0 f g).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rcases f with ⟨a, f⟩; rcases g with ⟨b, g⟩; exact congrArg Nat.succ (ih f g)
theorem bits_finRange {k : Nat} (a0 b0 : Bool) (f g : Affine k) :
    bits a0 b0 f g = (List.finRange k).map fun j =>
      value a0 b0 (bitAt (affineWord f) j.val) (bitAt (affineWord g) j.val) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases f with ⟨a, f⟩; rcases g with ⟨b, g⟩
    simp only [bits, List.finRange_succ, List.map_cons, List.map_map,
      Function.comp_def, Fin.val_zero, Fin.val_succ, affineWord_cons, bitAt, ih]
theorem bits_pullback {n : Nat} (r : Row n) (s : Space n) :
    bits (aConstant r.left) (aConstant r.right) (pullback r.left s.forms) (pullback r.right s.forms) =
      (List.finRange s.parameters).map (activityCoefficients r s) := by
  rw [bits_finRange]
  apply List.map_congr_left
  intro j _
  exact (coefficient_value r s j).symm

def sourceBits {n : Nat} (F : Family n) (s : Space n) : BitString :=
  F.flatMap fun r => bits (aConstant r.left) (aConstant r.right)
    (pullback r.left s.forms) (pullback r.right s.forms)
theorem sourceBits_length {n : Nat} (F : Family n) (s : Space n) :
    (sourceBits F s).length = F.length * s.parameters := by
  induction F with
  | nil => simp only [sourceBits, List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons r F ih =>
    simp only [sourceBits, List.flatMap_cons, List.length_append, bits_length] at *
    rw [ih]
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

def coefficientMatrixBits {m k : Nat} (M : Matrix m k) : BitString :=
  (List.finRange m).flatMap fun i => (List.finRange k).map (M i)
theorem sourceBits_matrix {n : Nat} (F : Family n) (s : Space n) :
    sourceBits F s = coefficientMatrixBits (activityMatrix s F) := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    change bits (aConstant r.left) (aConstant r.right)
      (pullback r.left s.forms) (pullback r.right s.forms) ++ sourceBits F s = _
    rw [bits_pullback, ih]
    simp only [coefficientMatrixBits, List.length_cons, List.finRange_succ, List.flatMap_cons,
      List.flatMap_map, activityMatrix, Fin.cases_zero, Fin.cases_succ]

theorem constant_suffix {n : Nat} (a : Affine n) :
    affineWord a = normalWord a ++ [aConstant a] := word_split a

end PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra

import PNP.Concrete.ResidualReduction.SourceScalarState

/-! The existing semantic affine projection is exactly the diagonal/constant
projection of the triangular coefficient representation, for every quadratic.
This identity does not assume zero polar form and does not evaluate assignments. -/

namespace PNP.Concrete.ResidualReduction.SourceQuadraticDiagonalAlgebra
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra

theorem affinePart_zero (c : Bool) : affinePart (n := 0) c = c := by
  simp only [affinePart,linearForm,coefficientForm,aAdd,aConst,qEval,Bool.false_xor]

theorem affinePart_cons {n : Nat} (a : Affine n) (q : Quadratic n) :
    affinePart (n := n + 1) (a,q) = (aConstant a,affinePart q) := by
  simp only [affinePart,linearForm,coefficientForm,aAdd,aConst,unitPoint_zero,unitPoint_succ,
    zeroPoint,qEval,Bool.and_true,Bool.and_false,Bool.false_xor,eval_zero_constant,
    Bool.xor_assoc,Bool.xor_self,Bool.xor_false]

def diagonal : {n : Nat} → Quadratic n → Affine n
  | 0,c => c
  | _ + 1,(a,q) => (aConstant a,diagonal q)
def constant : {n : Nat} → Quadratic n → Bool
  | 0,c => c
  | _ + 1,(_,q) => constant q

theorem diagonal_eq {n : Nat} (q : Quadratic n) : diagonal q = affinePart q := by
  induction n with
  | zero => exact (affinePart_zero q).symm
  | succ n ih =>
    rcases q with ⟨a,q⟩
    rw [affinePart_cons]
    change (aConstant a,diagonal q) = (aConstant a,affinePart q)
    rw [ih]

theorem diagonal_constant {n : Nat} (q : Quadratic n) :
    aConstant (diagonal q) = constant q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases q with ⟨a,q⟩
    exact ih q

theorem constant_eval {n : Nat} (q : Quadratic n) :
    constant q = qEval q (zeroPoint n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases q with ⟨a,q⟩
    simpa only [constant,qEval,zeroPoint,Bool.and_false,Bool.false_xor] using ih q

theorem output_split {n : Nat} (q : Quadratic n) :
    affineWord (affinePart q) = normalWord (diagonal q) ++ [constant q] := by
  rw [← diagonal_eq,word_split,diagonal_constant]

theorem normal_cons {n : Nat} (a : Affine n) (q : Quadratic n) :
    normalWord (diagonal (n := n + 1) (a,q)) = aConstant a :: normalWord (diagonal q) := rfl

theorem dimension_bound (n : Nat) : n + 1 ≤ quadraticBits n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [quadraticBits,affineBits]
    omega

end PNP.Concrete.ResidualReduction.SourceQuadraticDiagonalAlgebra

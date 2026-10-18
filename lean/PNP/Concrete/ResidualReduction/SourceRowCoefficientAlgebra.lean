import PNP.Concrete.ResidualReduction.SourceScalarInitialization
import PNP.Concrete.ResidualReduction.SourceMenuBytes

/-! Full-affine byte identities for exact row contraction. Constants are
included in equality, and complementing a candidate changes its constant only. -/

namespace PNP.Concrete.ResidualReduction.SourceRowCoefficientAlgebra
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete.ResidualReduction.SourceMenuBytes

theorem nonzero_append (xs ys : BitString) :
    nonzero (xs ++ ys) = (nonzero xs || nonzero ys) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.cons_append,nonzero_cons,ih,Bool.or_assoc]

theorem nonzero_reverse (xs : BitString) : nonzero xs.reverse = nonzero xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.reverse_cons,nonzero_append,nonzero_cons,nonzero_nil,Bool.or_false,ih]
    exact Bool.or_comm _ _

theorem equal_word {n : Nat} (a b : Affine n) :
    aEq a b = !nonzero (List.zipWith Bool.xor (affineWord a) (affineWord b)) := by
  induction n with
  | zero => cases a <;> cases b <;> rfl
  | succ n ih =>
    rcases a with ⟨u,a⟩
    rcases b with ⟨v,b⟩
    change ((u == v) && aEq a b) = !(Bool.xor u v ||
      nonzero (List.zipWith Bool.xor (affineWord a) (affineWord b)))
    rw [ih]
    cases u <;> cases v <;> rfl

theorem zero_word (n : Nat) : affineWord (aConst n false) = List.replicate (n + 1) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false :: affineWord (aConst n false) = false :: List.replicate (n + 1) false
    rw [ih]

theorem toggle_word {n : Nat} (f : Affine n) :
    affineWord (aAdd f (aConst n true)) = normalWord f ++ [!aConstant f] := by
  induction n with
  | zero => cases f <;> rfl
  | succ n ih =>
    rcases f with ⟨b,f⟩
    change Bool.xor b false :: affineWord (aAdd f (aConst n true)) =
      b :: (normalWord f ++ [!aConstant f])
    rw [Bool.xor_false,ih]

end PNP.Concrete.ResidualReduction.SourceRowCoefficientAlgebra

import PNP.Concrete.ResidualReduction.CoefficientComparison
import PNP.Concrete.ResidualReduction.MatrixRowInstructions

/-! Exact coefficient bytes for the source-derived candidate menu. Constants
are discarded, but no source coefficient or ordering choice is supplied. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuBytes
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.CoefficientComparison
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain

def nonzero (word : BitString) : Bool := word.any id

theorem nonzero_nil : nonzero [] = false := rfl
theorem nonzero_cons (b : Bool) (word : BitString) :
    nonzero (b :: word) = (b || nonzero word) := rfl

theorem homogeneous_zero (c : Affine 0) : homogeneousRow c = false := by
  cases c <;> rfl

theorem homogeneous_cons {n : Nat} (b : Bool) (a : Affine n) :
    homogeneousRow (n := n + 1) (b, a) = (b, homogeneousRow a) := by
  change (Bool.xor b false, aAdd a (aConst n (aConstant a))) =
    (b, homogeneousRow a)
  rw [Bool.xor_false]
  rfl

theorem normalBits_homogeneous {n : Nat} (a : Affine n) :
    normalBits (homogeneousRow a) = normalBits a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    rw [homogeneous_cons]
    change b :: normalBits (homogeneousRow a) = b :: normalBits a
    rw [ih a]

theorem normalBits_add {n : Nat} (a b : Affine n) :
    normalBits (aAdd a b) = List.zipWith Bool.xor (normalBits a) (normalBits b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨u, a⟩
    rcases b with ⟨v, b⟩
    change Bool.xor u v :: normalBits (aAdd a b) =
      Bool.xor u v :: List.zipWith Bool.xor (normalBits a) (normalBits b)
    rw [ih a b]

theorem homogeneous_add {n : Nat} (a b : Affine n) :
    aAdd (homogeneousRow a) (homogeneousRow b) = homogeneousRow (aAdd a b) := by
  induction n with
  | zero => rw [homogeneous_zero, homogeneous_zero, homogeneous_zero]; rfl
  | succ n ih =>
    rcases a with ⟨u, a⟩
    rcases b with ⟨v, b⟩
    rw [homogeneous_cons, homogeneous_cons]
    change (Bool.xor u v, aAdd (homogeneousRow a) (homogeneousRow b)) =
      homogeneousRow (n := n + 1) (Bool.xor u v, aAdd a b)
    rw [homogeneous_cons, ih a b]

theorem homogeneous_bytes {n : Nat} (a : Affine n) :
    affineWord (homogeneousRow a) = normalBits a ++ [false] := by
  induction n with
  | zero => rw [homogeneous_zero]; rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    rw [homogeneous_cons]
    change b :: affineWord (homogeneousRow a) = b :: (normalBits a ++ [false])
    rw [ih a]

theorem homogeneous_sum_bytes {n : Nat} (a b : Affine n) :
    affineWord (aAdd (homogeneousRow a) (homogeneousRow b)) =
      List.zipWith Bool.xor (normalBits a) (normalBits b) ++ [false] := by
  rw [homogeneous_add, homogeneous_bytes, normalBits_add]

theorem zero_test {n : Nat} (a : Affine n) :
    aEq (homogeneousRow a) (aConst n false) = !nonzero (normalBits a) := by
  induction n with
  | zero => rw [homogeneous_zero]; rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    rw [homogeneous_cons]
    change ((b == false) && aEq (homogeneousRow a) (aConst n false)) =
      !(b || nonzero (normalBits a))
    rw [ih a]
    cases b <;> rfl

theorem equality_test {n : Nat} (a b : Affine n) :
    aEq (homogeneousRow a) (homogeneousRow b) =
      !nonzero (List.zipWith Bool.xor (normalBits a) (normalBits b)) := by
  induction n with
  | zero => rw [homogeneous_zero, homogeneous_zero]; rfl
  | succ n ih =>
    rcases a with ⟨u, a⟩
    rcases b with ⟨v, b⟩
    rw [homogeneous_cons, homogeneous_cons]
    change ((u == v) && aEq (homogeneousRow a) (homogeneousRow b)) =
      !(Bool.xor u v || nonzero (List.zipWith Bool.xor (normalBits a) (normalBits b)))
    rw [ih a b]
    cases u <;> cases v <;> rfl

def eligible (left right : BitString) : Bool :=
  nonzero left && nonzero right && nonzero (List.zipWith Bool.xor left right)

/-- Reverse record order is the input order for the right-fold insertion
algorithm. Coefficient order inside every record is still unchanged. -/
theorem reversed_row_bytes {n : Nat} (r : Row n) :
    matrixBits (rowNormals r).reverse =
      if eligible (normalBits r.left) (normalBits r.right) then
        (List.zipWith Bool.xor (normalBits r.left) (normalBits r.right) ++ [false]) ++
          ((normalBits r.right ++ [false]) ++ (normalBits r.left ++ [false]))
      else [] := by
  dsimp only [rowNormals]
  rw [zero_test, zero_test, equality_test]
  cases ha : nonzero (normalBits r.left) <;>
    cases hb : nonzero (normalBits r.right) <;>
    cases hc : nonzero (List.zipWith Bool.xor (normalBits r.left) (normalBits r.right))
  all_goals simp only [ha, hb, hc, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, eligible,
    Bool.and_false, Bool.and_true, List.reverse_nil, matrixBits]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    matrixBits, homogeneous_bytes, homogeneous_sum_bytes, List.append_nil]

end PNP.Concrete.ResidualReduction.SourceMenuBytes

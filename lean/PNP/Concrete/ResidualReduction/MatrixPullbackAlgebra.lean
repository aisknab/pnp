import PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

/-! Constructive coefficient identities for the literal pivot-map routine.
The accumulator visits rows from left to right; these identities connect that
order to the existing recursively defined pullback without replacing its data
by an extensionally equivalent but differently encoded solution map. -/

namespace PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions

theorem add_zero_left {k : Nat} (f : Affine k) : aAdd (aConst k false) f = f := by
  induction k with
  | zero => cases f <;> rfl
  | succ k ih =>
    rcases f with ⟨b, f⟩
    change (Bool.xor false b, aAdd (aConst k false) f) = (b, f)
    rw [Bool.false_xor, ih]

theorem add_zero_right {k : Nat} (f : Affine k) : aAdd f (aConst k false) = f := by
  induction k with
  | zero => cases f <;> rfl
  | succ k ih =>
    rcases f with ⟨b, f⟩
    change (Bool.xor b false, aAdd f (aConst k false)) = (b, f)
    rw [Bool.xor_false, ih]

theorem scale_false {k : Nat} (f : Affine k) : aScale false f = aConst k false := by
  induction k with
  | zero => cases f <;> rfl
  | succ k ih =>
    rcases f with ⟨b, f⟩
    change (false && b, aScale false f) = (false, aConst k false)
    rw [Bool.false_and, ih]

theorem scale_true {k : Nat} (f : Affine k) : aScale true f = f := by
  induction k with
  | zero => cases f <;> rfl
  | succ k ih =>
    rcases f with ⟨b, f⟩
    change (true && b, aScale true f) = (b, f)
    rw [Bool.true_and, ih]

private theorem xor_reorder : ∀ x y z : Bool,
    Bool.xor x (Bool.xor y z) = Bool.xor (Bool.xor y x) z := by decide

theorem add_reorder {k : Nat} (x y z : Affine k) :
    aAdd x (aAdd y z) = aAdd (aAdd y x) z := by
  induction k with
  | zero => exact xor_reorder x y z
  | succ k ih =>
    rcases x with ⟨a, x⟩; rcases y with ⟨b, y⟩; rcases z with ⟨c, z⟩
    exact Prod.ext (xor_reorder a b c) (ih x y z)

theorem word_add {k : Nat} (f g : Affine k) :
    affineWord (aAdd f g) = List.zipWith Bool.xor (affineWord f) (affineWord g) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases f with ⟨b, f⟩; rcases g with ⟨c, g⟩
    exact congrArg (List.cons (Bool.xor b c)) (ih f g)

def normalWord : {k : Nat} → Affine k → BitString
  | 0, _ => []
  | _ + 1, (b, f) => b :: normalWord f

theorem normalWord_length {k : Nat} (f : Affine k) : (normalWord f).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases f with ⟨b, f⟩
    exact congrArg Nat.succ (ih f)

theorem word_split {k : Nat} (f : Affine k) :
    affineWord f = normalWord f ++ [aConstant f] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases f with ⟨b, f⟩
    exact congrArg (List.cons b) (ih f)

theorem word_constant_add {k : Nat} (c : Bool) (f : Affine k) :
    affineWord (aAdd (aConst k c) f) = normalWord f ++ [Bool.xor c (aConstant f)] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases f with ⟨b, f⟩
    change Bool.xor false b :: affineWord (aAdd (aConst k c) f) =
      b :: (normalWord f ++ [Bool.xor c (aConstant f)])
    rw [Bool.false_xor, ih]

def selectedSum : {n k : Nat} → Affine n → AffineMap n k → Affine k → Affine k
  | 0, _, _, _, acc => acc
  | _ + 1, _, (b, p), (f, m), acc =>
    selectedSum p m (if b then aAdd f acc else acc)

theorem selectedSum_result {n k : Nat} (p : Affine n) (m : AffineMap n k)
    (acc : Affine k) :
    aAdd (aConst k (aConstant p)) (selectedSum p m acc) = aAdd (pullback p m) acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨b, p⟩; rcases m with ⟨f, m⟩
    cases b with
    | false =>
      simpa only [selectedSum, Bool.false_eq_true, if_false, aConstant,
        pullback, scale_false, add_zero_left] using ih p m acc
    | true =>
      simpa only [selectedSum, if_true, aConstant, pullback, scale_true,
        add_reorder] using ih p m (aAdd f acc)

end PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra

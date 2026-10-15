import PNP.Concrete.ResidualReduction.SourceActivityMatrix

namespace PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections

/-- The first m coordinates hold weights; the last n hold a covector.
    The dimension n+m follows recursion on the prefix length m. -/
def splitPoint : (m : Nat) → {n : Nat} → Point (n + m) → Point m × Point n
  | 0, _, x => ((), x)
  | m + 1, _, (b, x) =>
    let (u, v) := splitPoint m x
    ((b, u), v)

def appendPoint : (m : Nat) → {n : Nat} → Point m → Point n → Point (n + m)
  | 0, _, _, y => y
  | m + 1, _, (b, x), y => (b, appendPoint m x y)

theorem split_append (m : Nat) {n : Nat} (x : Point m) (y : Point n) :
    splitPoint m (appendPoint m x y) = (x, y) := by
  induction m with
  | zero => cases x; rfl
  | succ m ih =>
    rcases x with ⟨b, x⟩
    simp only [appendPoint, splitPoint, ih]

theorem append_split (m : Nat) {n : Nat} (x : Point (n + m)) :
    appendPoint m (splitPoint m x).1 (splitPoint m x).2 = x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨b, x⟩
    simp only [splitPoint, appendPoint, ih]

theorem split_zero (m n : Nat) :
    splitPoint m (zeroPoint (n + m)) = (zeroPoint m, zeroPoint n) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change ((false, (splitPoint m (zeroPoint (n + m))).1),
      (splitPoint m (zeroPoint (n + m))).2) = ((false, zeroPoint m), zeroPoint n)
    rw [ih]

theorem split_xor (m : Nat) {n : Nat} (x y : Point (n + m)) :
    splitPoint m (pXor x y) =
      (pXor (splitPoint m x).1 (splitPoint m y).1,
       pXor (splitPoint m x).2 (splitPoint m y).2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨a, x⟩
    rcases y with ⟨b, y⟩
    simp only [splitPoint, pXor, ih]

theorem xor_interchange : ∀ a b c d : Bool,
    Bool.xor (Bool.xor a b) (Bool.xor c d) =
      Bool.xor (Bool.xor a c) (Bool.xor b d) := by decide

theorem and_xor : ∀ a b c : Bool,
    (a && Bool.xor b c) = Bool.xor (a && b) (a && c) := by decide

theorem xor_and : ∀ a b c : Bool,
    (Bool.xor a b && c) = Bool.xor (a && c) (b && c) := by decide

theorem xor_false_iff : ∀ a b : Bool, Bool.xor a b = false ↔ a = b := by decide

def pointDot : {n : Nat} → Point n → Point n → Bool
  | 0, _, _ => false
  | _ + 1, (a, x), (b, y) => Bool.xor (a && b) (pointDot x y)

theorem pointDot_zero_left {n : Nat} (x : Point n) :
    pointDot (zeroPoint n) x = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨b, x⟩
    simp only [zeroPoint, pointDot, Bool.false_and, Bool.false_xor, ih]

theorem pointDot_zero_right {n : Nat} (x : Point n) :
    pointDot x (zeroPoint n) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨b, x⟩
    simp only [zeroPoint, pointDot, Bool.and_false, Bool.false_xor, ih]

theorem pointDot_additive_left {n : Nat} (x y z : Point n) :
    pointDot (pXor x y) z = Bool.xor (pointDot x z) (pointDot y z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨a, x⟩
    rcases y with ⟨b, y⟩
    rcases z with ⟨c, z⟩
    simp only [pXor, pointDot, xor_and, ih]
    exact xor_interchange _ _ _ _

theorem pointDot_additive_right {n : Nat} (x y z : Point n) :
    pointDot x (pXor y z) = Bool.xor (pointDot x y) (pointDot x z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨a, x⟩
    rcases y with ⟨b, y⟩
    rcases z with ⟨c, z⟩
    simp only [pXor, pointDot, and_xor, ih]
    exact xor_interchange _ _ _ _

def coefficientForm : {n : Nat} → (Fin n → Bool) → Affine n
  | 0, _ => false
  | _ + 1, f => (f 0, coefficientForm (fun i => f i.succ))

theorem coefficientForm_eval {n : Nat} (f : Fin n → Bool) (x : Point n) :
    aEval (coefficientForm f) x = rowDot f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨b, x⟩
    simp only [coefficientForm, aEval, rowDot, ih]

theorem coefficientForm_constant {n : Nat} (f : Fin n → Bool) :
    aConstant (coefficientForm f) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [coefficientForm, aConstant, ih]

def linearForm {n : Nat} (f : Point n → Bool) : Affine n :=
  coefficientForm (fun i => f (unitPoint n i))

theorem linearForm_constant {n : Nat} (f : Point n → Bool) :
    aConstant (linearForm f) = false := coefficientForm_constant _

theorem linearForm_eval {n : Nat} (f : Point n → Bool)
    (hzero : f (zeroPoint n) = false)
    (hadd : ∀ x y, f (pXor x y) = Bool.xor (f x) (f y)) (x : Point n) :
    aEval (linearForm f) x = f x := by
  rw [linearForm, coefficientForm_eval]
  exact additive_coefficient_exact f hzero hadd x

theorem rowDot_false {n : Nat} (x : Point n) :
    rowDot (fun _ => false) x = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨b, x⟩
    simp only [rowDot, Bool.false_and, Bool.false_xor, ih]

theorem additive_units_zero {n : Nat} (f : Point n → Bool)
    (hzero : f (zeroPoint n) = false)
    (hadd : ∀ x y, f (pXor x y) = Bool.xor (f x) (f y))
    (hunit : ∀ i, f (unitPoint n i) = false) (x : Point n) : f x = false := by
  have he : (fun i => f (unitPoint n i)) = (fun _ => false) := funext hunit
  rw [← additive_coefficient_exact f hzero hadd x, he]
  exact rowDot_false x

def bilinearCoefficients {m n : Nat} (f : Point m → Point n → Bool) : Matrix m n :=
  fun i j => f (unitPoint m i) (unitPoint n j)

theorem bilinear_as_rowDot {m n : Nat} (M : Matrix m n) (x : Point m) (y : Point n) :
    bilinearEval M x y = rowDot (fun i => rowDot (M i) y) x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨b, x⟩
    simp only [bilinearEval, rowDot, ih, Bool.and_comm]

theorem bilinearCoefficients_eval {m n : Nat} (f : Point m → Point n → Bool)
    (hzl : ∀ y, f (zeroPoint m) y = false)
    (hzr : ∀ x, f x (zeroPoint n) = false)
    (hal : ∀ x x' y, f (pXor x x') y = Bool.xor (f x y) (f x' y))
    (har : ∀ x y y', f x (pXor y y') = Bool.xor (f x y) (f x y'))
    (x : Point m) (y : Point n) :
    bilinearEval (bilinearCoefficients f) x y = f x y := by
  rw [bilinear_as_rowDot]
  have he : (fun i => rowDot (bilinearCoefficients f i) y) =
      (fun i => f (unitPoint m i) y) := by
    funext i
    exact additive_coefficient_exact (f (unitPoint m i)) (hzr _) (har _) y
  rw [he]
  exact additive_coefficient_exact (fun z => f z y) (hzl y) (fun a b => hal a b y) x

end PNP.Concrete.ResidualReduction.SourceLine

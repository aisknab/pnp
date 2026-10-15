import Std

/-! Finite Boolean coefficient data for an exact, checked source contraction.
No assignment enumeration is used by the coefficient constructors or equality checks. -/

namespace PNP.Concrete.ResidualReduction.FactoredContraction

def Tuple (Z : Type) : Nat → Type
  | 0 => Z
  | n + 1 => Bool × Tuple Z n

abbrev Point (n : Nat) := Tuple Unit n
abbrev Affine (n : Nat) := Tuple Bool n

def Quadratic : Nat → Type
  | 0 => Bool
  | n + 1 => Affine n × Quadratic n

def aEval : {n : Nat} → Affine n → Point n → Bool
  | 0, c, _ => c
  | _ + 1, (d, a), (b, x) => Bool.xor (d && b) (aEval a x)

def aConstant : {n : Nat} → Affine n → Bool
  | 0, c => c
  | _ + 1, (_, a) => aConstant a

def aConst : (n : Nat) → Bool → Affine n
  | 0, c => c
  | n + 1, c => (false, aConst n c)

def aAdd : {n : Nat} → Affine n → Affine n → Affine n
  | 0, a, b => Bool.xor a b
  | _ + 1, (a, f), (b, g) => (Bool.xor a b, aAdd f g)

def aScale : {n : Nat} → Bool → Affine n → Affine n
  | 0, b, c => b && c
  | _ + 1, b, (d, a) => (b && d, aScale b a)

def aEq : {n : Nat} → Affine n → Affine n → Bool
  | 0, a, b => !(Bool.xor a b)
  | _ + 1, (a, f), (b, g) => (a == b) && aEq f g

def qEval : {n : Nat} → Quadratic n → Point n → Bool
  | 0, c, _ => c
  | _ + 1, (d, q), (b, x) => Bool.xor (aEval d x && b) (qEval q x)

def qAdd : {n : Nat} → Quadratic n → Quadratic n → Quadratic n
  | 0, a, b => Bool.xor a b
  | _ + 1, (a, p), (b, q) => (aAdd a b, qAdd p q)

def qOfAffine : {n : Nat} → Affine n → Quadratic n
  | 0, c => c
  | n + 1, (d, a) => (aConst n d, qOfAffine a)

def qProduct : {n : Nat} → Affine n → Affine n → Quadratic n
  | 0, a, b => a && b
  | n + 1, (d, a), (e, b) =>
    (aAdd (aScale d b) (aAdd (aScale e a) (aConst n (d && e))),
     qProduct a b)

def qEq : {n : Nat} → Quadratic n → Quadratic n → Bool
  | 0, a, b => !(Bool.xor a b)
  | _ + 1, (a, p), (b, q) => aEq a b && qEq p q

private theorem addIdentity :
    ∀ a b x u v : Bool,
      Bool.xor ((Bool.xor a b) && x) (Bool.xor u v) =
        Bool.xor (Bool.xor (a && x) u) (Bool.xor (b && x) v) := by
  decide

private theorem scaleIdentity :
    ∀ b d x u : Bool,
      Bool.xor ((b && d) && x) (b && u) =
        (b && Bool.xor (d && x) u) := by
  decide

private theorem productIdentity :
    ∀ d e x a b : Bool,
      Bool.xor ((Bool.xor (d && b) (Bool.xor (e && a) (d && e))) && x)
        (a && b) =
      ((Bool.xor (d && x) a) && (Bool.xor (e && x) b)) := by
  decide

theorem aConst_eval (n : Nat) (b : Bool) (x : Point n) :
    aEval (aConst n b) x = b := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨h, x⟩
    simpa [aConst, aEval] using ih b x

theorem aAdd_eval {n : Nat} (f g : Affine n) (x : Point n) :
    aEval (aAdd f g) x = Bool.xor (aEval f x) (aEval g x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases f with ⟨a, f⟩
    rcases g with ⟨b, g⟩
    rcases x with ⟨h, x⟩
    simp only [aAdd, aEval, ih]
    exact addIdentity a b h (aEval f x) (aEval g x)

theorem aScale_eval {n : Nat} (b : Bool) (f : Affine n) (x : Point n) :
    aEval (aScale b f) x = (b && aEval f x) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rcases f with ⟨d, f⟩
    rcases x with ⟨h, x⟩
    simp only [aScale, aEval, ih]
    exact scaleIdentity b d h (aEval f x)

theorem aEq_true_iff {n : Nat} (f g : Affine n) :
    aEq f g = true ↔ f = g := by
  induction n with
  | zero =>
    change (!Bool.xor f g) = true ↔ @Eq Bool f g
    cases f <;> cases g <;> decide
  | succ n ih =>
    rcases f with ⟨a, f⟩
    rcases g with ⟨b, g⟩
    change ((a == b) && aEq f g) = true ↔ ((a, f) : Bool × Affine n) = (b, g)
    simp [ih]

theorem qAdd_eval {n : Nat} (p q : Quadratic n) (x : Point n) :
    qEval (qAdd p q) x = Bool.xor (qEval p x) (qEval q x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨a, p⟩
    rcases q with ⟨b, q⟩
    rcases x with ⟨h, x⟩
    simp only [qAdd, qEval, aAdd_eval, ih]
    exact addIdentity (aEval a x) (aEval b x) h (qEval p x) (qEval q x)

theorem qOfAffine_eval {n : Nat} (f : Affine n) (x : Point n) :
    qEval (qOfAffine f) x = aEval f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases f with ⟨d, f⟩
    rcases x with ⟨h, x⟩
    simp only [qOfAffine, qEval, aEval, aConst_eval, ih]

theorem qProduct_eval {n : Nat} (f g : Affine n) (x : Point n) :
    qEval (qProduct f g) x = (aEval f x && aEval g x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases f with ⟨d, f⟩
    rcases g with ⟨e, g⟩
    rcases x with ⟨h, x⟩
    simp only [qProduct, qEval, aEval, aAdd_eval, aScale_eval, aConst_eval, ih]
    exact productIdentity d e h (aEval f x) (aEval g x)

theorem qEq_true_iff {n : Nat} (p q : Quadratic n) :
    qEq p q = true ↔ p = q := by
  induction n with
  | zero =>
    change (!Bool.xor p q) = true ↔ @Eq Bool p q
    cases p <;> cases q <;> decide
  | succ n ih =>
    rcases p with ⟨a, p⟩
    rcases q with ⟨b, q⟩
    change (aEq a b && qEq p q) = true ↔ ((a, p) : Affine n × Quadratic n) = (b, q)
    simp [aEq_true_iff, ih]

def pXor : {n : Nat} → Point n → Point n → Point n
  | 0, _, _ => ()
  | _ + 1, (a, x), (b, y) => (Bool.xor a b, pXor x y)

private theorem xorSwap :
    ∀ a b c : Bool, Bool.xor a (Bool.xor b c) = Bool.xor b (Bool.xor a c) := by
  decide

private theorem affineXorIdentity :
    ∀ d x y a b c : Bool,
      Bool.xor (d && Bool.xor x y) (Bool.xor (Bool.xor a b) c) =
        Bool.xor (Bool.xor (Bool.xor (d && x) a) (Bool.xor (d && y) b)) c := by
  decide

theorem pXor_twice {n : Nat} (x v : Point n) :
    pXor (pXor x v) v = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    rcases x with ⟨a, x⟩
    rcases v with ⟨b, v⟩
    simp [pXor, ih]

theorem aEval_xor {n : Nat} (f : Affine n) (x v : Point n) :
    aEval f (pXor x v) =
      Bool.xor (Bool.xor (aEval f x) (aEval f v)) (aConstant f) := by
  induction n with
  | zero => cases f <;> rfl
  | succ n ih =>
    rcases f with ⟨d, f⟩
    rcases x with ⟨a, x⟩
    rcases v with ⟨b, v⟩
    simp only [pXor, aEval, aConstant, ih]
    exact affineXorIdentity d a b (aEval f x) (aEval f v) (aConstant f)

def shear {n : Nat} (v : Point n) (x : Point (n + 1)) : Point (n + 1) :=
  (x.1, if x.1 then pXor x.2 v else x.2)

def aShear {n : Nat} (v : Point n) (f : Affine (n + 1)) : Affine (n + 1) :=
  (Bool.xor f.1 (Bool.xor (aEval f.2 v) (aConstant f.2)), f.2)

private theorem shearIdentity :
    ∀ h a b c : Bool,
      Bool.xor (Bool.xor h (Bool.xor b c)) a =
        Bool.xor h (Bool.xor (Bool.xor a b) c) := by
  decide

theorem shear_involution {n : Nat} (v : Point n) (x : Point (n + 1)) :
    shear v (shear v x) = x := by
  rcases x with ⟨b, x⟩
  cases b <;> simp [shear, pXor_twice]

theorem aShear_eval {n : Nat} (v : Point n) (f : Affine (n + 1))
    (x : Point (n + 1)) :
    aEval (aShear v f) x = aEval f (shear v x) := by
  rcases f with ⟨d, f⟩
  rcases x with ⟨b, x⟩
  cases b with
  | false => simp [aShear, shear, aEval]
  | true =>
    simpa [aShear, shear, aEval, aEval_xor] using
      shearIdentity d (aEval f x) (aEval f v) (aConstant f)

def cut {Z : Type} : (n : Nat) → Fin (n + 1) →
    Tuple Z (n + 1) → Bool × Tuple Z n
  | 0, _, x => x
  | n + 1, k, x =>
    if hk : k.val = 0 then x
    else
      let k' : Fin (n + 1) := ⟨k.val - 1, by omega⟩
      let t := cut n k' x.2
      (t.1, (x.1, t.2))

def insert {Z : Type} : (n : Nat) → Fin (n + 1) →
    Bool × Tuple Z n → Tuple Z (n + 1)
  | 0, _, x => x
  | n + 1, k, x =>
    if hk : k.val = 0 then x
    else
      let k' : Fin (n + 1) := ⟨k.val - 1, by omega⟩
      (x.2.1, insert n k' (x.1, x.2.2))

theorem insert_cut {Z : Type} (n : Nat) (k : Fin (n + 1))
    (x : Tuple Z (n + 1)) : insert n k (cut n k x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hk : k.val = 0
    · simp [cut, insert, hk]
    · simp [cut, insert, hk, ih] <;> rfl

theorem cut_insert {Z : Type} (n : Nat) (k : Fin (n + 1))
    (x : Bool × Tuple Z n) : cut n k (insert n k x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hk : k.val = 0
    · simp [cut, insert, hk]
    · simp [cut, insert, hk, ih] <;> rfl

theorem aEval_cut (n : Nat) (k : Fin (n + 1))
    (f : Affine (n + 1)) (x : Point (n + 1)) :
    aEval (n := n + 1) (cut n k f) (cut n k x) = aEval f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hk : k.val = 0
    · simp [cut, hk]
    · let k' : Fin (n + 1) := ⟨k.val - 1, by omega⟩
      simp only [cut, hk]
      change Bool.xor ((cut n k' f.2).1 && (cut n k' x.2).1)
          (Bool.xor (f.1 && x.1)
            (aEval (cut n k' f.2).2 (cut n k' x.2).2)) =
        Bool.xor (f.1 && x.1) (aEval f.2 x.2)
      rw [xorSwap]
      change Bool.xor (f.1 && x.1)
          (aEval (n := n + 1) (cut n k' f.2) (cut n k' x.2)) =
        Bool.xor (f.1 && x.1) (aEval f.2 x.2)
      rw [ih]

def affineBits (n : Nat) : Nat := n + 1

def quadraticBits : Nat → Nat
  | 0 => 1
  | n + 1 => affineBits n + quadraticBits n

theorem quadraticBits_exact (n : Nat) :
    2 * quadraticBits n = n * (n + 1) + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.mul_add, Nat.mul_one] at ih
    simp only [quadraticBits, affineBits]
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]
    omega

end PNP.Concrete.ResidualReduction.FactoredContraction

import PNP.SignedTernary.Field

namespace PNP.SignedTernary.Linear
open PNP.SignedTernary.Field

abbrev Vec := Point

def zero : (n : Nat) → Vec n
  | 0 => ()
  | n+1 => (.z,zero n)

def plus : {n : Nat} → Vec n → Vec n → Vec n
  | 0, _, _ => ()
  | _+1, x, y => (add x.1 y.1,plus x.2 y.2)

def scale : {n : Nat} → F3 → Vec n → Vec n
  | 0, _, _ => ()
  | _+1, c, x => (mul c x.1,scale c x.2)

def minus {n : Nat} (x y : Vec n) : Vec n := plus x (scale .t y)

def dot : {n : Nat} → Vec n → Vec n → F3
  | 0, _, _ => .z
  | _+1, x, y => add (mul x.1 y.1) (dot x.2 y.2)

def norm {n : Nat} (x : Vec n) : F3 := dot x x

def Signed : {n : Nat} → Vec n → Prop
  | 0, _ => True
  | _+1, x => x.1 ≠ .z ∧ Signed x.2

def signedNorm : Nat → F3
  | 0 => .z
  | n+1 => add .o (signedNorm n)

theorem plus_zero {n : Nat} (x : Vec n) : plus x (zero n) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    rcases x with ⟨a,x⟩
    simp only [plus, zero, add_zero, ih]

theorem scale_zero {n : Nat} (x : Vec n) : scale .z x = zero n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [scale, zero_mul, ih, zero]

theorem scale_one {n : Nat} (x : Vec n) : scale .o x = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih => rcases x with ⟨a,x⟩; simp only [scale, one_mul, ih]

theorem scale_scale {n : Nat} (a b : F3) (x : Vec n) :
    scale a (scale b x) = scale (mul a b) x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [scale, ih, mul_assoc]

theorem dot_comm {n : Nat} (x y : Vec n) : dot x y = dot y x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [dot, mul_comm, ih]

theorem dot_plus {n : Nat} (x y z : Vec n) :
    dot x (plus y z) = add (dot x y) (dot x z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dot, plus, mul_add, ih]
    exact add_shuffle _ _ _ _

theorem dot_plus_left {n : Nat} (x y z : Vec n) :
    dot (plus x y) z = add (dot x z) (dot y z) := by
  rw [dot_comm, dot_plus, dot_comm z x, dot_comm z y]

theorem dot_scale {n : Nat} (x y : Vec n) (c : F3) :
    dot x (scale c y) = mul c (dot x y) := by
  induction n with
  | zero => exact (mul_zero c).symm
  | succ n ih =>
    simp only [dot, scale, ih, mul_add]
    congr 1
    rw [← mul_assoc, mul_comm x.1 c, mul_assoc]

theorem dot_scale_left {n : Nat} (x y : Vec n) (c : F3) :
    dot (scale c x) y = mul c (dot x y) := by
  rw [dot_comm, dot_scale, dot_comm y x]

theorem norm_scale {n : Nat} (x : Vec n) (c : F3) :
    norm (scale c x) = mul (mul c c) (norm x) := by
  unfold norm
  rw [dot_scale_left, dot_scale, ← mul_assoc]

theorem norm_plus {n : Nat} (x y : Vec n) :
    norm (plus x y) = add (norm x) (add (norm y) (mul .t (dot x y))) := by
  unfold norm
  rw [dot_plus_left, dot_plus, dot_plus, dot_comm y x]
  generalize dot x x = a
  generalize dot y y = b
  generalize dot x y = c
  cases a <;> cases b <;> cases c <;> rfl

theorem norm_minus {n : Nat} (x y : Vec n) :
    norm (minus x y) = add (norm x) (add (norm y) (dot x y)) := by
  simp only [minus, norm_plus, norm_scale, dot_scale]
  generalize norm x = a
  generalize norm y = b
  generalize dot x y = c
  cases a <;> cases b <;> cases c <;> rfl

theorem signed_norm {n : Nat} (x : Vec n) (h : Signed x) :
    norm x = signedNorm n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hx : x.1 ≠ .z ∧ Signed x.2 := h
    have hh : mul x.1 x.1 = .o := by
      cases he : x.1 with
      | z => exact False.elim (hx.1 he)
      | o => rfl
      | t => rfl
    change add (mul x.1 x.1) (norm x.2) = add .o (signedNorm n)
    rw [hh, ih x.2 hx.2]

def Isometry {n m : Nat} (f : Vec n → Vec m) : Prop :=
  ∀ x, norm (f x) = norm x

end PNP.SignedTernary.Linear

namespace PNP.SignedTernary.Linear
open PNP.SignedTernary.Field

@[reducible] def Rows (n : Nat) : Nat → Type
  | 0 => Unit
  | m+1 => Vec n × Rows n m

def applyRows : {n m : Nat} → Rows n m → Vec n → Vec m
  | _, 0, _, _ => ()
  | _, _+1, A, x => (dot A.1 x, applyRows A.2 x)

theorem applyRows_plus {n m : Nat} (A : Rows n m) (x y : Vec n) :
    applyRows A (plus x y) = plus (applyRows A x) (applyRows A y) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [applyRows, dot_plus, ih, plus]

theorem applyRows_scale {n m : Nat} (A : Rows n m) (c : F3) (x : Vec n) :
    applyRows A (scale c x) = scale c (applyRows A x) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [applyRows, dot_scale, ih, scale]

end PNP.SignedTernary.Linear

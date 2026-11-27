import PNP.SignedTernary.Gate

namespace PNP.SignedTernary.Marker
open PNP.SignedTernary.Field PNP.SignedTernary.Linear PNP.SignedTernary.Gate

def ones : Vec 4 := v4 .o .o .o .o

def nullDirection : Vec 4 := v4 .o .o .t .t

def constant4 (a : F3) : Vec 4 := v4 a a a a

def project (c : Vec 4) : Vec 4 :=
  minus c (scale (dot nullDirection c) nullDirection)

def relay (c : Vec 4) (s : F3) : Vec 4 :=
  plus c (scale (add s (neg (dot ones c))) ones)

def sentinel (c : Vec 4) : F3 := dot ones c

theorem reflection_norm (c : Vec 4) (s : F3) :
    add (mul (sentinel c) (sentinel c)) (norm (relay c s)) =
      add (norm c) (mul s s) := by
  unfold relay sentinel
  rw [norm_plus, norm_scale]
  change add (mul (dot ones c) (dot ones c))
    (add (norm c) (add (mul (mul (add s (neg (dot ones c)))
      (add s (neg (dot ones c)))) .o)
      (mul .t (dot c (scale (add s (neg (dot ones c))) ones))))) =
      add (norm c) (mul s s)
  rw [mul_one, dot_scale, dot_comm c ones]
  generalize norm c = q
  generalize dot ones c = d
  cases q <;> cases d <;> cases s <;> rfl

theorem projection_norm (c : Vec 4) :
    norm (project c) =
      add (norm c) (neg (mul (dot nullDirection c) (dot nullDirection c))) := by
  unfold project
  rw [norm_minus, norm_scale, dot_scale, dot_comm c nullDirection]
  change add (norm c) (add (mul (mul (dot nullDirection c) (dot nullDirection c)) .o)
    (mul (dot nullDirection c) (dot nullDirection c))) = _
  rw [mul_one]
  generalize norm c = q
  generalize dot nullDirection c = d
  cases q <;> cases d <;> rfl

theorem projection_fixed (c : Vec 4) (h : dot nullDirection c = .z) :
    project c = c := by
  rw [project, h, scale_zero]
  exact plus_zero c

theorem projection_norm_iff (c : Vec 4) :
    norm (project c) = norm c ↔ dot nullDirection c = .z := by
  rw [projection_norm, scalar_add_eq_self]
  generalize dot nullDirection c = d
  cases d <;> decide

theorem sentinel_forces_constant (c : Vec 4) (hc : Signed c)
    (hk : dot nullDirection c = .z) (hs : sentinel c ≠ .z) : AllEqual4 c := by
  rcases c with ⟨a,b,c,d,e⟩
  cases e
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [AllEqual4, Signed, sentinel, ones, nullDirection, v4, dot, add, mul]

theorem equal_constant (c : Vec 4) (h : AllEqual4 c) : c = constant4 c.1 := by
  rcases c with ⟨a,b,c,d,e⟩
  cases e
  obtain ⟨hb,hc,hd⟩ := h
  change b = a at hb
  change c = a at hc
  change d = a at hd
  subst b; subst c; subst d
  rfl

theorem constant_projection (a : F3) : project (constant4 a) = constant4 a := by
  cases a <;> rfl

theorem constant_relay (a s : F3) : relay (constant4 a) s = constant4 s := by
  cases a <;> cases s <;> rfl

theorem constant_sentinel (a : F3) : sentinel (constant4 a) = a := by
  cases a <;> rfl

theorem constant_signed (a : F3) (h : a ≠ .z) : Signed (constant4 a) :=
  ⟨h,h,h,h,True.intro⟩

theorem signed_neg_iff {n : Nat} (x : Vec n) :
    Signed (scale .t x) ↔ Signed x := by
  induction n with
  | zero => exact Iff.rfl
  | succ n ih =>
    change (mul .t x.1 ≠ .z ∧ Signed (scale .t x.2)) ↔
      (x.1 ≠ .z ∧ Signed x.2)
    rw [ih]
    cases x.1 <;> simp [mul]

theorem scale_join {n m : Nat} (a : F3) (x : Vec n) (y : Vec m) :
    scale a (join x y) = join (scale a x) (scale a y) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [join, scale, ih]

theorem zero_plus_vec {n : Nat} (x : Vec n) : plus (zero n) x = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih => rcases x with ⟨a,x⟩; simp only [zero, plus, zero_add, ih]

theorem applyRows_zero {n m : Nat} (A : Rows n m) : applyRows A (zero n) = zero m := by
  have h := applyRows_scale A .z (zero n)
  simpa only [scale_zero] using h

end PNP.SignedTernary.Marker

import PNP.SignedTernary.Linear

namespace PNP.SignedTernary.Gate
open PNP.SignedTernary.Field PNP.SignedTernary.Linear

def combine : {m n : Nat} → Rows m n → Vec n → Vec m
  | m, 0, _, _ => zero m
  | _, _+1, C, x => plus (scale x.1 C.1) (combine C.2 x.2)

def AllOrthogonal {m : Nat} (v : Vec m) : {n : Nat} → Rows m n → Prop
  | 0, _ => True
  | _+1, C => dot v C.1 = .z ∧ AllOrthogonal v C.2

def Orthonormal : {m n : Nat} → Rows m n → Prop
  | _, 0, _ => True
  | _, _+1, C => norm C.1 = .o ∧ AllOrthogonal C.1 C.2 ∧ Orthonormal C.2

theorem dot_zero {n : Nat} (v : Vec n) : dot v (zero n) = .z := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [dot, zero, mul_zero, zero_add, ih]

theorem orthogonal_combine {m n : Nat} (v : Vec m) (C : Rows m n)
    (h : AllOrthogonal v C) (x : Vec n) : dot v (combine C x) = .z := by
  induction n with
  | zero => exact dot_zero v
  | succ n ih =>
    simp only [combine, dot_plus, dot_scale, h.1, mul_zero, ih C.2 h.2 x.2, add]

theorem combine_isometry {m n : Nat} (C : Rows m n) (h : Orthonormal C) :
    Isometry (combine C) := by
  intro x
  induction n with
  | zero =>
    change norm (zero m) = .z
    exact dot_zero (zero m)
  | succ n ih =>
    rw [combine, norm_plus, norm_scale, h.1, mul_one,
      dot_scale_left, orthogonal_combine C.1 C.2 h.2.1 x.2, mul_zero, mul_zero,
      add_zero, ih C.2 h.2.2 x.2]
    rfl

def heads : {m n : Nat} → Rows (n+1) m → Vec m
  | 0, _, _ => ()
  | _+1, _, A => (A.1.1, heads A.2)

def tails : {m n : Nat} → Rows (n+1) m → Rows n m
  | 0, _, _ => ()
  | _+1, _, A => (A.1.2, tails A.2)

def columns : {m n : Nat} → Rows n m → Rows m n
  | _, 0, _ => ()
  | _, _+1, A => (heads A, columns (tails A))

theorem apply_zero_width {m : Nat} (A : Rows 0 m) (x : Vec 0) :
    applyRows A x = zero m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [applyRows, dot, zero, ih]

theorem apply_cons {m n : Nat} (A : Rows (n+1) m) (a : F3) (x : Vec n) :
    applyRows A (a,x) = plus (scale a (heads A)) (applyRows (tails A) x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [applyRows, dot, heads, tails, plus, scale, ih]
    rw [mul_comm A.1.1 a]

theorem combine_columns {m n : Nat} (A : Rows n m) (x : Vec n) :
    combine (columns A) x = applyRows A x := by
  induction n with
  | zero => exact (apply_zero_width A x).symm
  | succ n ih =>
    rcases x with ⟨a,x⟩
    rw [columns, combine, ih, apply_cons]

theorem checked_columns_isometry {m n : Nat} (A : Rows n m)
    (h : Orthonormal (columns A)) : Isometry (applyRows A) := by
  intro x
  rw [← combine_columns]
  exact combine_isometry (columns A) h x

def join : {n m : Nat} → Vec n → Vec m → Vec (m+n)
  | 0, _, _, y => y
  | _+1, _, x, y => (x.1, join x.2 y)

theorem norm_join {n m : Nat} (x : Vec n) (y : Vec m) :
    norm (join x y) = add (norm x) (norm y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change add (mul x.1 x.1) (norm (join x.2 y)) =
      add (add (mul x.1 x.1) (norm x.2)) (norm y)
    rw [ih, add_assoc]

theorem signed_join {n m : Nat} (x : Vec n) (y : Vec m) :
    Signed (join x y) ↔ Signed x ∧ Signed y := by
  induction n with
  | zero => exact ⟨fun h => ⟨True.intro,h⟩,fun h => h.2⟩
  | succ n ih =>
    change (x.1 ≠ .z ∧ Signed (join x.2 y)) ↔
      (x.1 ≠ .z ∧ Signed x.2) ∧ Signed y
    rw [ih]
    exact ⟨fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩,fun h => ⟨h.1.1,h.1.2,h.2⟩⟩

theorem dot_combine {m n : Nat} (v : Vec m) (C : Rows m n) (x : Vec n) :
    dot v (combine C x) = dot (applyRows C v) x := by
  induction n with
  | zero => exact dot_zero v
  | succ n ih =>
    simp only [combine, dot_plus, dot_scale, ih, applyRows, dot]
    rw [mul_comm x.1 (dot v C.1), dot_comm v C.1]

theorem dot_apply {m n : Nat} (A : Rows n m) (u : Vec m) (x : Vec n) :
    dot u (applyRows A x) = dot (applyRows (columns A) u) x := by
  rw [← combine_columns, dot_combine]

end PNP.SignedTernary.Gate

namespace PNP.SignedTernary.Gate
open PNP.SignedTernary.Field PNP.SignedTernary.Linear

def v4 (a b c d : F3) : Vec 4 := (a,(b,(c,(d,()))))

def v8 (a b c d e f g h : F3) : Vec 8 :=
  (a,(b,(c,(d,(e,(f,(g,(h,()))))))))

def gateRows : Rows 8 8 :=
  (v8 .z .z .z .z .o .o .o .o,
  (v8 .t .o .o .z .o .o .t .t,
  (v8 .o .t .z .o .t .t .o .o,
  (v8 .z .o .z .z .z .o .o .o,
  (v8 .z .o .z .z .o .z .o .o,
  (v8 .z .o .o .t .o .o .t .t,
  (v8 .t .t .o .t .t .t .z .t,
  (v8 .t .t .o .t .t .t .t .z,()))))))))

def gate (x : Vec 8) : Vec 8 := applyRows gateRows x

theorem gate_columns_orthonormal : Orthonormal (columns gateRows) := by
  simp only [gateRows, v8, columns, heads, tails, Orthonormal, AllOrthogonal,
    norm, dot, add, mul]
  decide

theorem gate_isometry : Isometry gate :=
  checked_columns_isometry gateRows gate_columns_orthonormal

def knobInput (a b c d : F3) : Vec 8 := v8 .o .o .o .o a b c d

def commonKnob (a : F3) : Vec 8 := knobInput a a a a

def forcedOutput (a : F3) : Vec 8 := v8 a .o .o .o .o .o .o .o

def VisibleSigned (x : Vec 8) : Prop :=
  x.1 ≠ .z ∧ x.2.1 ≠ .z ∧ x.2.2.1 ≠ .z

theorem visible_forces_equal (a b c d : F3)
    (ha : a ≠ .z) (hb : b ≠ .z) (hc : c ≠ .z) (hd : d ≠ .z)
    (h : VisibleSigned (gate (knobInput a b c d))) :
    b = a ∧ c = a ∧ d = a := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [VisibleSigned, gate, knobInput, gateRows, v8,
      applyRows, dot, add, mul]

theorem common_knob_output (a : F3) :
    gate (commonKnob a) = forcedOutput a := by
  cases a <;> rfl

theorem forced_output_signed (a : F3) (ha : a ≠ .z) :
    Signed (forcedOutput a) := by
  change a ≠ .z ∧ F3.o ≠ .z ∧ F3.o ≠ .z ∧ F3.o ≠ .z ∧
    F3.o ≠ .z ∧ F3.o ≠ .z ∧ F3.o ≠ .z ∧ F3.o ≠ .z ∧ True
  exact ⟨ha,by decide⟩

theorem complete_four_to_seven (a b c d : F3)
    (ha : a ≠ .z) (hb : b ≠ .z) (hc : c ≠ .z) (hd : d ≠ .z)
    (h : VisibleSigned (gate (knobInput a b c d))) :
    knobInput a b c d = commonKnob a ∧
    gate (knobInput a b c d) = forcedOutput a ∧
    Signed (gate (knobInput a b c d)) := by
  obtain ⟨hba,hca,hda⟩ := visible_forces_equal a b c d ha hb hc hd h
  subst b; subst c; subst d
  exact ⟨rfl,common_knob_output a,by change Signed (gate (commonKnob a)); rw [common_knob_output]; exact forced_output_signed a ha⟩

end PNP.SignedTernary.Gate

namespace PNP.SignedTernary.Gate
open PNP.SignedTernary.Field PNP.SignedTernary.Linear

theorem scalar_add_eq_self (a b : F3) : add a b = a ↔ b = .z := by
  cases a <;> cases b <;> decide

def AllEqual4 (x : Vec 4) : Prop :=
  x.2.1 = x.1 ∧ x.2.2.1 = x.1 ∧ x.2.2.2.1 = x.1

theorem add_right_cancel (a b c : F3) (h : add a c = add b c) : a = b := by
  cases a <;> cases b <;> cases c <;> cases h <;> rfl

end PNP.SignedTernary.Gate

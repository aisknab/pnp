import PNP.SignedTernary.Matrix.Layout

set_option autoImplicit false

namespace PNP.SignedTernary.Encoding
open PNP.SignedTernary.Field PNP.SignedTernary.Linear PNP.SignedTernary.Gate PNP.SignedTernary.Network
open PNP.Concrete (BitString CNFSAT)

def AdditiveScalar {n : Nat} (f : Vec n → F3) : Prop :=
  ∀ x y, f (plus x y) = add (f x) (f y)

def AdditiveMap {n m : Nat} (f : Vec n → Vec m) : Prop :=
  ∀ x y, f (plus x y) = plus (f x) (f y)

theorem scalar_zero {n : Nat} (f : Vec n → F3) (hf : AdditiveScalar f) :
    f (zero n) = .z := by
  have h := hf (zero n) (zero n)
  rw [plus_zero] at h
  cases he : f (zero n) <;> simp_all [add]

theorem scale_two {n : Nat} (x : Vec n) : scale .t x = plus x x := by
  have h := scale_add_scalar .o .o x
  simpa only [add,scale_one] using h

theorem scalar_scale {n : Nat} (f : Vec n → F3) (hf : AdditiveScalar f)
    (a : F3) (x : Vec n) : f (scale a x) = mul a (f x) := by
  cases a with
  | z => rw [scale_zero,scalar_zero f hf,zero_mul]
  | o => rw [scale_one,one_mul]
  | t =>
    rw [scale_two,hf]
    cases f x <;> rfl

/-- Coefficients are evaluated at actual coordinate unit words, in order. -/
def rowOf : (n : Nat) → (Vec n → F3) → Vec n
  | 0, _ => ()
  | n+1, f => (f (.o,zero n),rowOf n (fun x => f (.z,x)))

theorem rowOf_spec (n : Nat) (f : Vec n → F3) (hf : AdditiveScalar f) (x : Vec n) :
    dot (rowOf n f) x = f x := by
  induction n with
  | zero => cases x; exact (scalar_zero f hf).symm
  | succ n ih =>
    have ht : AdditiveScalar (fun y : Vec n => f (.z,y)) := by
      intro y z
      exact hf (.z,y) (.z,z)
    change add (mul (f (.o,zero n)) x.1)
      (dot (rowOf n (fun y => f (.z,y))) x.2) = f x
    rw [ih _ ht]
    have he := hf (scale x.1 (.o,zero n)) (.z,x.2)
    rw [scalar_scale f hf] at he
    have hx : plus (scale x.1 (.o,zero n)) (.z,x.2) = x := by
      simp only [scale,mul_one,scale_zero_vec,plus,add_zero,PNP.SignedTernary.Marker.zero_plus_vec]
    rw [hx] at he
    rw [mul_comm]
    exact he.symm

def matrixOf {n : Nat} : (m : Nat) → (Vec n → Vec m) → Rows n m
  | 0, _ => ()
  | m+1, f => (rowOf n (fun x => (f x).1),matrixOf m (fun x => (f x).2))

theorem matrixOf_spec {n : Nat} (m : Nat) (f : Vec n → Vec m) (hf : AdditiveMap f)
    (x : Vec n) : applyRows (matrixOf m f) x = f x := by
  induction m with
  | zero => cases f x; rfl
  | succ m ih =>
    have hh : AdditiveScalar (fun y => (f y).1) := fun y z => congrArg Prod.fst (hf y z)
    have ht : AdditiveMap (fun y => (f y).2) := fun y z => congrArg Prod.snd (hf y z)
    change (dot (rowOf n (fun y => (f y).1)) x,
      applyRows (matrixOf m (fun y => (f y).2)) x) = f x
    rw [rowOf_spec n _ hh,ih _ ht]

def coord : {n : Nat} → Vec n → Fin n → F3
  | 0, _, i => nomatch i
  | _+1, x, i => Fin.cases x.1 (fun j => coord x.2 j) i

def unit : (n : Nat) → Fin n → Vec n
  | 0, i => nomatch i
  | n+1, i => Fin.cases (.o,zero n) (fun j => (.z,unit n j)) i

def rowAt {n : Nat} : {m : Nat} → Rows n m → Fin m → Vec n
  | 0, _, i => nomatch i
  | _+1, R, i => Fin.cases R.1 (fun j => rowAt R.2 j) i

theorem rowOf_coord (n : Nat) (f : Vec n → F3) (j : Fin n) :
    coord (rowOf n f) j = f (unit n j) := by
  induction n with
  | zero => nomatch j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · exact ih (fun x => f (.z,x)) j

theorem matrixOf_entry {n : Nat} (m : Nat) (f : Vec n → Vec m) (i : Fin m) (j : Fin n) :
    coord (rowAt (matrixOf m f) i) j = coord (f (unit n j)) i := by
  induction m with
  | zero => nomatch i
  | succ m ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact rowOf_coord n (fun x => (f x).1) j
    · exact ih (fun x => (f x).2) i

def physicalMatrix {n m : Nat} (L : Rows n m) : Rows (inputWidth n m) (inputWidth n m) :=
  matrixOf (inputWidth n m) (squareMap L)

theorem physicalMatrix_apply {n m : Nat} (L : Rows n m) (x : Vec (inputWidth n m)) :
    applyRows (physicalMatrix L) x = squareMap L x :=
  matrixOf_spec _ _ (squareMap_plus L) x

theorem physicalMatrix_entry {n m : Nat} (L : Rows n m)
    (i j : Fin (inputWidth n m)) :
    coord (rowAt (physicalMatrix L) i) j = coord (squareMap L (unit _ j)) i :=
  matrixOf_entry _ _ i j

def literalMatrix (raw : BitString) :=
  physicalMatrix (sourceMatrix raw)

def LiteralMatrixDonor (raw : BitString) : Prop :=
  ∃ x, Signed x ∧ Signed (applyRows (literalMatrix raw) x)

/-- The literal square row matrix acts exactly as the proved physical program. -/
theorem literalMatrix_apply (raw : BitString)
    (x : Vec (inputWidth (PNP.SignedTernary.Network.parsedSites (PNP.Concrete.decodeEncodedCNF raw)).length
      (PNP.SignedTernary.CNF.rawForms raw).length)) :
    applyRows (literalMatrix raw) x = squareMap (sourceMatrix raw) x :=
  physicalMatrix_apply _ x

/-- Strict all-bitstring CNFSAT, now at an actual square-matrix donor endpoint. -/
theorem literalMatrix_iff_CNFSAT (raw : BitString) :
    LiteralMatrixDonor raw ↔ CNFSAT raw := by
  have h : LiteralMatrixDonor raw ↔
      ∃ x, Signed x ∧ Signed (squareMap (sourceMatrix raw) x) := by
    constructor
    · rintro ⟨x,hx,ho⟩
      rw [literalMatrix_apply] at ho
      exact ⟨x,hx,ho⟩
    · rintro ⟨x,hx,ho⟩
      refine ⟨x,hx,?_⟩
      rw [literalMatrix_apply]
      exact ho
  exact h.trans ((squareMap_donor_iff _).trans (terminal_iff_CNFSAT raw))

end PNP.SignedTernary.Encoding

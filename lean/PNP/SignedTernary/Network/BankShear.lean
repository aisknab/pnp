import PNP.SignedTernary.Network.GroundRows
import PNP.SignedTernary.Relay
import PNP.SignedTernary.Marker

namespace PNP.SignedTernary.Network
open PNP.SignedTernary.Field PNP.SignedTernary.Linear PNP.SignedTernary.Gate PNP.SignedTernary.Relay

abbrev Banks (m : Nat) := Vec m × (Vec m × Vec m)

def bankTotal {m : Nat} (z : Banks m) := plus z.1 (plus z.2.1 z.2.2)

def bankNorm {m : Nat} (z : Banks m) := add (norm z.1) (add (norm z.2.1) (norm z.2.2))

def BanksSigned {m : Nat} (z : Banks m) := Signed z.1 ∧ Signed z.2.1 ∧ Signed z.2.2

def shiftBanks {m : Nat} (z : Banks m) (t : Vec m) : Banks m :=
  (plus z.1 t,(plus z.2.1 t,plus z.2.2 t))

theorem scalar_triple (a : F3) : add a (add a a) = .z := by cases a <;> rfl

set_option maxHeartbeats 3000000 in
theorem three_shift_scalar (a b c e p q r : F3) :
    add (add a (add e (mul .t p)))
      (add (add b (add e (mul .t q))) (add c (add e (mul .t r)))) =
    add (add a (add b c)) (mul .t (add p (add q r))) := by
  cases a <;> cases b <;> cases c <;> cases e <;> cases p <;> cases q <;> cases r <;> rfl

theorem bank_shift_norm {m : Nat} (z : Banks m) (t : Vec m) :
    bankNorm (shiftBanks z t) = add (bankNorm z) (mul .t (dot (bankTotal z) t)) := by
  simp only [bankNorm,shiftBanks,norm_plus,bankTotal,dot_plus_left]
  exact three_shift_scalar _ _ _ _ _ _ _

def shear {n m : Nat} (R : Rows n m) (h : Vec n) (z : Banks m) : Vec n × Banks m :=
  let d := applyRows (columns R) (bankTotal z)
  (minus h d,shiftBanks z (applyRows R (plus h d)))

theorem shear_norm {n m : Nat} (R : Rows n m) (h : Vec n) (z : Banks m) :
    add (norm (shear R h z).1) (bankNorm (shear R h z).2) =
      add (norm h) (bankNorm z) := by
  simp only [shear,norm_minus,bank_shift_norm]
  rw [dot_apply R (bankTotal z) (plus h (applyRows (columns R) (bankTotal z))),dot_plus]
  rw [dot_comm (applyRows (columns R) (bankTotal z)) h]
  change add (add (norm h) (add (norm (applyRows (columns R) (bankTotal z)))
    (dot h (applyRows (columns R) (bankTotal z)))))
    (add (bankNorm z) (mul .t (add (dot h (applyRows (columns R) (bankTotal z)))
      (norm (applyRows (columns R) (bankTotal z)))))) = _
  generalize norm h = a
  generalize norm (applyRows (columns R) (bankTotal z)) = b
  generalize dot h (applyRows (columns R) (bankTotal z)) = c
  generalize bankNorm z = e
  cases a <;> cases b <;> cases c <;> cases e <;> rfl

def constant : (n : Nat) → F3 → Vec n
  | 0, _ => ()
  | n+1, a => (a,constant n a)

theorem constant_positive (n : Nat) : constant n .o = positive n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [constant,positive,ih]

theorem triple_constants (n : Nat) (a : F3) :
    bankTotal (constant n a,(constant n a,constant n a)) = zero n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (add a (add a a),bankTotal (constant n a,(constant n a,constant n a))) = _
    rw [scalar_triple,ih]
    rfl

theorem applyRows_zero {n m : Nat} (R : Rows n m) :
    applyRows R (zero n) = zero m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [applyRows,dot_zero,zero,ih]

theorem scale_zero_vec (c : F3) (n : Nat) : scale c (zero n) = zero n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [scale,zero,mul_zero,ih]

def anchoredRows : {n m : Nat} → Rows n m → Rows (n+1) m
  | _, 0, _ => ()
  | _, _+1, L => ((.t,L.1),anchoredRows L.2)

theorem anchored_cancel {n m : Nat} (L : Rows n m) (a : F3) (x : Vec n) :
    plus (constant m a) (applyRows (anchoredRows L) (a,x)) = applyRows L x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [constant,applyRows,anchoredRows,plus,dot,ih]
    congr 1
    generalize dot L.1 x = b
    cases a <;> cases b <;> rfl

theorem shear_constant_banks {n m : Nat} (L : Rows n m) (a : F3) (x : Vec n) :
    shear (anchoredRows L) (a,x) (constant m a,(constant m a,constant m a)) =
      ((a,x),(applyRows L x,(applyRows L x,applyRows L x))) := by
  simp only [shear,triple_constants,applyRows_zero,minus,scale_zero_vec,plus_zero,
    shiftBanks,anchored_cancel]

/-- One row uses exactly three relay-bank pins; this recursion exposes the physical grouping. -/
def stages : Nat → Nat
  | 0 => 0
  | m+1 => stages m + 3

theorem stage_count (m : Nat) : stages m = 3*m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [stages,ih]; omega

def splitBanks : (m : Nat) → Vec (stages m) → Banks m
  | 0, _ => ((),((),()))
  | m+1, z =>
      let b := splitBanks m z.2.2.2
      ((z.1,b.1),((z.2.1,b.2.1),(z.2.2.1,b.2.2)))

theorem splitBanks_norm (m : Nat) (z : Vec (stages m)) :
    bankNorm (splitBanks m z) = norm z := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change add (add (mul z.1 z.1) (norm (splitBanks m z.2.2.2).1))
      (add (add (mul z.2.1 z.2.1) (norm (splitBanks m z.2.2.2).2.1))
      (add (mul z.2.2.1 z.2.2.1) (norm (splitBanks m z.2.2.2).2.2))) =
      add (mul z.1 z.1) (add (mul z.2.1 z.2.1)
        (add (mul z.2.2.1 z.2.2.1) (norm z.2.2.2)))
    rw [← ih]
    simp only [bankNorm,add_assoc,PNP.SignedTernary.Relay.add_left_comm]

theorem splitBanks_positive (m : Nat) :
    splitBanks m (positive (stages m)) =
      (positive m,(positive m,positive m)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [stages,positive,splitBanks,ih]

end PNP.SignedTernary.Network

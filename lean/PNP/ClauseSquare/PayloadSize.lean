import PNP.ClauseSquare.InputLength

set_option autoImplicit false
namespace PNP.ClauseSquare.EncodedCost
open PNP.Concrete PNP.ClauseSquare
open PNP.SignedTernary.CNF (readWord readWord_at readWord_length)

/-- Concatenate fixed-width numbered blocks in index-increasing order. -/
def blocks : Nat → (Nat → BitString) → BitString
  | 0,_ => []
  | k+1,f => f 0 ++ blocks k (fun i => f (i+1))

theorem blocks_length (k b : Nat) (f : Nat → BitString)
    (hw : ∀ i, i<k → (f i).length=b) : (blocks k f).length=k*b := by
  induction k generalizing f with
  | zero => exact (Nat.zero_mul _).symm
  | succ k ih =>
    rw [blocks,List.length_append,hw 0 (Nat.zero_lt_succ _),ih (fun i => f (i+1))
      (fun i hi => hw (i+1) (by omega)),Nat.succ_mul]; omega

theorem read_append_left (a b : BitString) (i : Nat) (hi : i<a.length) :
    assignmentAt (a++b) i = assignmentAt a i := by
  induction a generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero _ hi)
  | cons v vs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

theorem read_append_right (a b : BitString) (j : Nat) :
    assignmentAt (a++b) (a.length+j) = assignmentAt b j := by
  induction a with
  | nil => rw [List.length_nil,Nat.zero_add]; rfl
  | cons v vs ih =>
    rw [List.length_cons,Nat.succ_add]; exact ih

theorem blocks_at (k b : Nat) (f : Nat → BitString)
    (hw : ∀ i, i<k → (f i).length=b) (i j : Nat) (hi : i<k) (hj : j<b) :
    assignmentAt (blocks k f) (i*b+j) = assignmentAt (f i) j := by
  induction k generalizing f i with
  | zero => exact False.elim (Nat.not_lt_zero _ hi)
  | succ k ih =>
    cases i with
    | zero =>
      rw [Nat.zero_mul,Nat.zero_add,blocks]; apply read_append_left
      rw [hw 0 (Nat.zero_lt_succ _)]; exact hj
    | succ i =>
      have shift : (i+1)*b+j=(f 0).length+(i*b+j) := by
        rw [hw 0 (Nat.zero_lt_succ _),Nat.succ_mul]; omega
      rw [blocks,shift,read_append_right]
      exact ih (fun a => f (a+1)) (fun a ha => hw (a+1) (by omega)) i (Nat.lt_of_succ_lt_succ hi)

/-- Block zero is the constant matrix; block i+1 is the slope of original bit i. -/
def coefficient {n : Nat} : Nat → Term n → Bool
  | 0,t => t.bias
  | i+1,t => axisBit t i

def denseColumn (s : Raw) (b j : Nat) : BitString :=
  readWord s.d (fun r => (packedColumn (coefficient b) j s.rows).testBit r.val)

def denseBlock (s : Raw) (b : Nat) : BitString := blocks s.d (denseColumn s b)

/-- Unframed, all coefficients present. Block, column, then low-to-high row; dimensions are external. -/
def payload (s : Raw) : BitString := blocks (s.n+1) (denseBlock s)

theorem column_length (s : Raw) (b j : Nat) : (denseColumn s b j).length=s.d :=
  readWord_length _ _

theorem block_length_exact (s : Raw) (b : Nat) : (denseBlock s b).length=s.d*s.d :=
  blocks_length _ _ _ (fun j _ => column_length s b j)

theorem exact_payload_length (s : Raw) : (payload s).length=(s.n+1)*s.d*s.d := by
  rw [payload,blocks_length _ _ _ (fun b _ => block_length_exact s b),Nat.mul_assoc]

/-- Every addressed bit is the genuine column coefficient, including zero entries. -/
theorem payload_bit (s : Raw) (b j r : Nat) (hb : b<s.n+1) (hj : j<s.d) (hr : r<s.d) :
    assignmentAt (payload s) (b*(s.d*s.d)+(j*s.d+r)) =
      some (entry (coefficient b) (rowAt s.rows r) j) := by
  have hprod : (j+1)*s.d ≤ s.d*s.d := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hj)
  rw [Nat.succ_mul] at hprod
  rw [payload,blocks_at (s.n+1) _ _ (fun a _ => block_length_exact s a) b (j*s.d+r) hb (by omega)]
  rw [denseBlock,blocks_at s.d s.d _ (fun c _ => column_length s b c) j r hj hr]
  unfold denseColumn
  rw [readWord_at,dif_pos hr,packed_column_bit]

theorem coefficient_budget (bits : BitString) :
    ((compile bits).n+1)*(compile bits).d*(compile bits).d ≤ (bits.length+1)^3 := by
  obtain ⟨hn,hd⟩ := all_input_axes bits
  have e := Nat.mul_le_mul (Nat.mul_le_mul (Nat.succ_le_succ hn) hd) hd
  have cube (z : Nat) : z^3=z*z*z := by
    rw [Nat.pow_succ,Nat.pow_succ,Nat.pow_one]
  rw [cube]; exact e

theorem payload_length_cubic (bits : BitString) :
    (payload (compile bits)).length ≤ (bits.length+1)^3 := by
  rw [exact_payload_length]; exact coefficient_budget bits

/-- A repository-standard polynomial for coefficient SIZE only; it is not a time field. -/
def sizePolynomial : NatPolynomial :=
  let u : NatPolynomial := .add .variable (.constant 1)
  .mul (.mul u u) u

theorem sizePolynomial_eval (l : Nat) : sizePolynomial.eval l=(l+1)^3 := by
  change (l+1)*(l+1)*(l+1) = (l+1)^3
  rw [Nat.pow_succ,Nat.pow_succ,Nat.pow_one]

theorem payload_polynomial (bits : BitString) :
    (payload (compile bits)).length ≤ sizePolynomial.eval bits.length := by
  rw [sizePolynomial_eval]; exact payload_length_cubic _

theorem malformed_payload (bits : BitString) (hd : decodeEncodedCNF bits=none) :
    payload (compile bits) = [true] := by
  rw [compile,hd]; rfl

theorem empty_input_exact : (payload (compile [])).length=sizePolynomial.eval 0 := rfl

end PNP.ClauseSquare.EncodedCost

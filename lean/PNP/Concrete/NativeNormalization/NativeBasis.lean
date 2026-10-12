import Std

namespace PNP.Concrete.NativeNormalization.NativeBasis

local infixl:65 " ⊕ᵦ " => Bool.xor

inductive Slot where
  | first | middle | last
deriving DecidableEq, BEq, Repr

structure Literal (n : Nat) where
  index : Fin n
  positive : Bool
deriving DecidableEq, Repr

/-- Internal incidence data. The source adapter must construct these fields;
none is an assumed span, model or algebraic correctness certificate. -/
structure Selection (n c : Nat) where
  literal : Fin c → Slot → Literal n
  owner : Fin n → Fin c
  slot : Fin n → Slot
  mode : Fin c → Option Slot
  ownerVariable : ∀ j, (literal (owner j) (slot j)).index = j
  ownerMode : ∀ j, mode (owner j) = some (slot j)

/-- Original homogeneous coordinates, or independent values on chosen rows. -/
structure Values (n c : Nat) where
  e : Bool
  x : Fin n → Bool
  t : Fin c → Bool

theorem Values.ext {a b : Values n c}
    (he : a.e = b.e) (hx : ∀ j, a.x j = b.x j) (ht : ∀ i, a.t i = b.t i) : a = b := by
  cases a with | mk ae ax ats =>
    cases b with | mk be bx bt =>
      dsimp at he hx ht
      have ex := funext hx
      have et := funext ht
      cases he
      cases ex
      cases et
      rfl

def sigma (S : Selection n c) (j : Fin n) : Bool :=
  (S.literal (S.owner j) (S.slot j)).positive

/-- Homogeneous form that is true exactly when this literal is false at e = true. -/
def falseForm (S : Selection n c) (i : Fin c) (k : Slot) (w : Values n c) : Bool :=
  w.x (S.literal i k).index ⊕ᵦ ((S.literal i k).positive && w.e)

def ell (S : Selection n c) (w : Values n c) (j : Fin n) : Bool :=
  w.x j ⊕ᵦ (sigma S j && w.e)

theorem owner_form (S : Selection n c) (w : Values n c) (j : Fin n) :
    falseForm S (S.owner j) (S.slot j) w = ell S w j := by
  simp only [falseForm, ell, sigma, S.ownerVariable]

def selected (S : Selection n c) (w : Values n c) (r : Fin c × Bool) : Bool :=
  if r.2 then
    match S.mode r.1 with
    | some .last => falseForm S r.1 .last w
    | _ => w.t r.1
  else
    match S.mode r.1 with
    | some .middle | some .last => falseForm S r.1 .middle w ⊕ᵦ w.t r.1
    | _ => falseForm S r.1 .first w

/-- Variable row, one auxiliary row per clause, and the failed-clause first row. -/
def encode (S : Selection n c) (failed : Fin c) (w : Values n c) : Values n c :=
  { e := falseForm S failed .first w
    x := fun j => if S.slot j = .middle then ell S w j ⊕ᵦ w.t (S.owner j) else ell S w j
    t := fun i => if S.mode i = some .last then falseForm S i .middle w ⊕ᵦ w.t i else w.t i }

def ellFrom (S : Selection n c) (b : Values n c) (j : Fin n) : Bool :=
  if S.slot j = .middle then b.x j ⊕ᵦ b.t (S.owner j) else b.x j

def anchor (S : Selection n c) (failed : Fin c) : Fin n :=
  (S.literal failed .first).index

def decodeE (S : Selection n c) (failed : Fin c) (b : Values n c) : Bool :=
  b.e ⊕ᵦ ellFrom S b (anchor S failed)

def decodeX (S : Selection n c) (failed : Fin c) (b : Values n c) (j : Fin n) : Bool :=
  ellFrom S b j ⊕ᵦ (sigma S j && decodeE S failed b)

def decodeT (S : Selection n c) (failed : Fin c) (b : Values n c) (i : Fin c) : Bool :=
  if S.mode i = some .last then
    b.t i ⊕ᵦ (decodeX S failed b (S.literal i .middle).index ⊕ᵦ
      ((S.literal i .middle).positive && decodeE S failed b))
  else b.t i

def decode (S : Selection n c) (failed : Fin c) (b : Values n c) : Values n c :=
  ⟨decodeE S failed b, decodeX S failed b, decodeT S failed b⟩

private theorem xor_cancel (a b : Bool) : (a ⊕ᵦ b) ⊕ᵦ b = a := by
  cases a <;> cases b <;> rfl
private theorem xor_cancel_left (a b : Bool) : (a ⊕ᵦ b) ⊕ᵦ a = b := by
  cases a <;> cases b <;> rfl
private theorem xor_cancel_middle (a b : Bool) : a ⊕ᵦ (b ⊕ᵦ a) = b := by
  cases a <;> cases b <;> rfl
private theorem restore_e (x s p e : Bool) (h : s ≠ p) :
    (x ⊕ᵦ (p && e)) ⊕ᵦ (x ⊕ᵦ (s && e)) = e := by
  cases x <;> cases s <;> cases p <;> cases e <;> simp_all
private theorem restore_extra (l z s p : Bool) (h : s ≠ p) :
    (l ⊕ᵦ (s && (z ⊕ᵦ l))) ⊕ᵦ (p && (z ⊕ᵦ l)) = z := by
  cases l <;> cases z <;> cases s <;> cases p <;> simp_all

theorem ellFrom_encode (S : Selection n c) (failed : Fin c)
    (w : Values n c) (j : Fin n) :
    ellFrom S (encode S failed w) j = ell S w j := by
  cases hs : S.slot j <;> simp [ellFrom, encode, S.ownerMode, hs]

theorem decodeE_encode (S : Selection n c) (failed : Fin c)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (w : Values n c) : decodeE S failed (encode S failed w) = w.e := by
  unfold decodeE
  rw [ellFrom_encode]
  exact restore_e _ _ _ _ bad

theorem decodeX_encode (S : Selection n c) (failed : Fin c)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (w : Values n c) (j : Fin n) :
    decodeX S failed (encode S failed w) j = w.x j := by
  unfold decodeX
  rw [ellFrom_encode, decodeE_encode S failed bad]
  exact xor_cancel _ _

theorem decodeT_encode (S : Selection n c) (failed : Fin c)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (w : Values n c) (i : Fin c) :
    decodeT S failed (encode S failed w) i = w.t i := by
  unfold decodeT
  rw [decodeX_encode S failed bad, decodeE_encode S failed bad]
  by_cases h : S.mode i = some .last
  · simp only [h, if_pos, encode]
    exact xor_cancel_left _ _
  · simp [h, encode]

/-- Every original coordinate is reconstructed from actual chosen row values. -/
theorem decode_encode (S : Selection n c) (failed : Fin c)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (w : Values n c) : decode S failed (encode S failed w) = w := by
  exact Values.ext (decodeE_encode S failed bad w) (decodeX_encode S failed bad w)
    (decodeT_encode S failed bad w)

theorem ell_decode (S : Selection n c) (failed : Fin c)
    (b : Values n c) (j : Fin n) :
    ell S (decode S failed b) j = ellFrom S b j := by
  exact xor_cancel _ _

/-- Arbitrary chosen-row values are independent, not merely a spanning image. -/
theorem encode_decode (S : Selection n c) (failed : Fin c)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (b : Values n c) : encode S failed (decode S failed b) = b := by
  apply Values.ext
  · exact restore_extra _ _ _ _ bad
  · intro j
    change (if S.slot j = .middle then ell S (decode S failed b) j ⊕ᵦ
      decodeT S failed b (S.owner j) else ell S (decode S failed b) j) = b.x j
    rw [ell_decode]
    cases hs : S.slot j <;>
      simp [ellFrom, decodeT, S.ownerMode, hs]
  · intro i
    change (if S.mode i = some .last then
      falseForm S i .middle (decode S failed b) ⊕ᵦ decodeT S failed b i
      else decodeT S failed b i) = b.t i
    by_cases h : S.mode i = some .last
    · simp only [h, if_pos, falseForm, decode, decodeT]
      exact xor_cancel_middle _ _
    · simp [h, decodeT]

abbrev Label (n c : Nat) := Sum (Fin n) (Sum (Fin c) Unit)

def value (b : Values n c) : Label n c → Bool
  | .inl j => b.x j
  | .inr (.inl i) => b.t i
  | .inr (.inr _) => b.e

def fromFn (f : Label n c → Bool) : Values n c :=
  ⟨f (.inr (.inr ())), fun j => f (.inl j), fun i => f (.inr (.inl i))⟩

theorem value_fromFn (f : Label n c → Bool) (k : Label n c) :
    value (fromFn f) k = f k := by
  cases k with
  | inl j => rfl
  | inr k => cases k with
    | inl i => rfl
    | inr u => cases u; rfl

def row (S : Selection n c) (failed : Fin c) : Label n c → Fin c × Bool
  | .inl j => (S.owner j, decide (S.slot j = .last))
  | .inr (.inl i) => (i, decide (S.mode i ≠ some .last))
  | .inr (.inr _) => (failed, false)

/-- Every coordinate used by encode is an actual selected factor row. -/
theorem encode_actual (S : Selection n c) (failed : Fin c)
    (unmatched : S.mode failed = none) (w : Values n c) (k : Label n c) :
    value (encode S failed w) k = selected S w (row S failed k) := by
  cases k with
  | inl j =>
      have ho := owner_form S w j
      cases hs : S.slot j <;>
        simp [value, encode, row, selected, S.ownerMode, hs] <;>
        simpa [hs] using ho.symm
  | inr k =>
      cases k with
      | inl i =>
          cases hm : S.mode i with
          | none => simp [value, encode, row, selected, hm]
          | some s => cases s <;> simp [value, encode, row, selected, hm]
      | inr u => simp [value, encode, row, selected, unmatched]

def pick (S : Selection n c) (failed : Fin c)
    (u : Fin c × Bool → Bool) : Values n c :=
  fromFn (fun k => u (row S failed k))

theorem pick_selected (S : Selection n c) (failed : Fin c)
    (unmatched : S.mode failed = none) (w : Values n c) :
    pick S failed (selected S w) = encode S failed w := by
  apply Values.ext
  · exact (encode_actual S failed unmatched w (.inr (.inr ()))).symm
  · intro j; exact (encode_actual S failed unmatched w (.inl j)).symm
  · intro i; exact (encode_actual S failed unmatched w (.inr (.inl i))).symm

theorem reconstruct_selected (S : Selection n c) (failed : Fin c)
    (unmatched : S.mode failed = none)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (w : Values n c) : decode S failed (pick S failed (selected S w)) = w := by
  rw [pick_selected S failed unmatched, decode_encode S failed bad]

theorem selected_basis_surjective (S : Selection n c) (failed : Fin c)
    (unmatched : S.mode failed = none)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (b : Values n c) : pick S failed (selected S (decode S failed b)) = b := by
  rw [pick_selected S failed unmatched, encode_decode S failed bad]

/-- Chosen row labels never collide, including the failed-clause extra row. -/
theorem row_injective (S : Selection n c) (failed : Fin c)
    (unmatched : S.mode failed = none)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (a b : Label n c) (h : row S failed a = row S failed b) : a = b := by
  have all : ∀ v : Values n c, value v a = value v b := by
    intro v
    rw [← encode_decode S failed bad v]
    rw [encode_actual S failed unmatched, encode_actual S failed unmatched, h]
  let f : Label n c → Bool := fun k => decide (k = a)
  have eq := all (fromFn f)
  rw [value_fromFn, value_fromFn] at eq
  have hb : decide (b = a) = true := by simpa [f] using eq.symm
  exact (of_decide_eq_true hb).symm


end PNP.Concrete.NativeNormalization.NativeBasis

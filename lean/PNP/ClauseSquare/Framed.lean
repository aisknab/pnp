import PNP.ClauseSquare.PayloadSize

set_option autoImplicit false
namespace PNP.ClauseSquare.Framed

open PNP.Concrete
open PNP.ClauseSquare.EncodedCost
open PNP.SignedTernary.CNF (readWord readWord_at)

/-- Only shape and coefficient bits, independent of the source syntax. -/
structure Bank where
  n : Nat
  d : Nat
  data : BitString
  shape : data.length = (n+1)*d*d

/-- Unary number terminated by a zero; the suffix is literal data. -/
def header : Nat → BitString → BitString
  | 0, rest => false :: rest
  | n+1, rest => true :: header n rest

def readHeader : BitString → Option (Nat × BitString)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
    match readHeader rest with
    | none => none
    | some (n, data) => some (n+1, data)

theorem read_header (n : Nat) (rest : BitString) :
    readHeader (header n rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [header,readHeader,ih]

theorem header_of_read {word : BitString} {n : Nat} {rest : BitString}
    (h : readHeader word = some (n,rest)) : word = header n rest := by
  induction word generalizing n rest with
  | nil => cases h
  | cons b bs ih =>
    cases b with
    | false =>
      change some (0,bs) = some (n,rest) at h
      cases h; rfl
    | true =>
      unfold readHeader at h
      cases e : readHeader bs with
      | none => rw [e] at h; cases h
      | some p =>
        obtain ⟨k,t⟩ := p
        rw [e] at h
        cases h
        exact congrArg (fun u => true :: u) (ih e)

theorem header_append (n : Nat) (data tail : BitString) :
    header n data ++ tail = header n (data ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun s => true :: s) ih

theorem header_length (n : Nat) (data : BitString) :
    (header n data).length = n+1+data.length := by
  induction n with
  | zero => rw [header,List.length_cons]; omega
  | succ n ih => rw [header,List.length_cons,ih]; omega

def encode (b : Bank) : BitString := header b.n (header b.d b.data)

def shapeRead (n d : Nat) (data : BitString) : Option Bank :=
  if h : data.length = (n+1)*d*d then some ⟨n,d,data,h⟩ else none

def decode (word : BitString) : Option Bank :=
  match readHeader word with
  | none => none
  | some (n,rest) =>
    match readHeader rest with
    | none => none
    | some (d,data) => shapeRead n d data

theorem decode_encode (b : Bank) : decode (encode b) = some b := by
  cases b with
  | mk n d data h => simp only [encode,decode,read_header,shapeRead,dif_pos h]

theorem encode_of_decode {word : BitString} {b : Bank} (h : decode word = some b) :
    encode b = word := by
  unfold decode at h
  cases e : readHeader word with
  | none => rw [e] at h; cases h
  | some p =>
    obtain ⟨n,rest⟩ := p
    rw [e] at h
    change (match readHeader rest with | none => none | some (d,data) => shapeRead n d data) = some b at h
    cases f : readHeader rest with
    | none => rw [f] at h; cases h
    | some u =>
      obtain ⟨d,data⟩ := u
      rw [f] at h
      change shapeRead n d data = some b at h
      unfold shapeRead at h
      split at h
      · cases h
        exact (congrArg (header n) (header_of_read f).symm).trans (header_of_read e).symm
      · cases h

theorem decode_wrong_length (n d : Nat) (data : BitString)
    (bad : data.length ≠ (n+1)*d*d) :
    decode (header n (header d data)) = none := by
  simp only [decode,read_header,shapeRead,dif_neg bad]

theorem decode_trailing (b : Bank) (x : Bool) (tail : BitString) :
    decode (encode b ++ x :: tail) = none := by
  rw [encode,header_append,header_append]
  apply decode_wrong_length
  rw [List.length_append,List.length_cons,b.shape]
  omega

theorem encode_injective {a b : Bank} (h : encode a = encode b) : a=b := by
  have u := congrArg decode h
  rw [decode_encode,decode_encode] at u
  exact Option.some.inj u

theorem encoded_length (b : Bank) :
    (encode b).length = (b.n+1)*b.d*b.d + b.n+b.d+2 := by
  rw [encode,header_length,header_length,b.shape]; omega

/-- Numeric interpretation of the raw data: C, then D₀,...; columns first, low row bit first. -/
def bit (b : Bank) (k j i : Nat) : Bool :=
  (assignmentAt b.data (k*(b.d*b.d)+(j*b.d+i))).getD false

def column (b : Bank) (k j : Nat) : Nat := pack (readWord b.d (fun i => bit b k j i.val))

def selected (b : Bank) (a j : Nat) : Nat :=
  column b 0 j ^^^ xorSelected b.n (fun i => column b (i+1) j) a.testBit

def product (b : Bank) (a z : Nat) : Nat := xorSelected b.d (selected b a) z.testBit

def Admits (b : Bank) (a : Nat) : Prop :=
  a < 2^b.n ∧ ∃ z : Nat, z≠0 ∧ z<2^b.d ∧ product b a z=0

/-- A bona fide finite exhaustive checker; no polynomial evaluation time is asserted. -/
def check (b : Bank) : Bool :=
  (List.range (2^b.n)).any (fun a =>
    (List.range (2^b.d)).any (fun z => decide (z≠0 ∧ product b a z=0)))

def accept (target : BitString) : Bool :=
  match decode target with
  | none => false
  | some b => check b

theorem check_iff (b : Bank) : check b=true ↔ ∃ a, Admits b a := by
  simp only [check,List.any_eq_true,List.mem_range,decide_eq_true_eq,Admits]
  constructor
  · rintro ⟨a,ha,z,hz,hn,h0⟩; exact ⟨a,ha,z,hn,hz,h0⟩
  · rintro ⟨a,ha,z,hn,hz,h0⟩; exact ⟨a,ha,z,hz,hn,h0⟩

theorem rejected_ill_formed (target : BitString) (h : decode target=none) :
    accept target=false := by rw [accept,h]

/-- A target-only condition retaining the physical numbered head's actual word. -/
def acceptsWord (target w : BitString) : Prop :=
  match decode target with
  | none => False
  | some b => ∃ a, Admits b a ∧ readWord b.n (fun i => a.testBit i.val)=w

/-- This is the sole entrance of source data into the target. -/
def ofSource (s : Raw) : Bank := ⟨s.n,s.d,payload s,exact_payload_length s⟩

def emit (bits : BitString) : BitString := encode (ofSource (compile bits))

theorem decode_emit (bits : BitString) :
    decode (emit bits) = some (ofSource (compile bits)) := decode_encode _

theorem bit_ofSource (s : Raw) (k j i : Nat) (hk : k<s.n+1) (hj : j<s.d) (hi : i<s.d) :
    bit (ofSource s) k j i = entry (coefficient k) (rowAt s.rows i) j := by
  change (assignmentAt (payload s) (k*(s.d*s.d)+(j*s.d+i))).getD false = _
  rw [payload_bit s k j i hk hj hi]; rfl

theorem column_ofSource (s : Raw) (hs : s.rows.length=s.d) (k j : Nat)
    (hk : k<s.n+1) (hj : j<s.d) :
    column (ofSource s) k j = packedColumn (coefficient k) j s.rows := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [column,pack_spec,readWord_at]
  change (if h : i<s.d then some (bit (ofSource s) k j i) else none).getD false = _
  by_cases hi : i<s.d
  · rw [dif_pos hi,packed_column_bit]; exact bit_ofSource s k j i hk hj hi
  · rw [dif_neg hi]
    have hb := column_bound (coefficient k) j s.rows
    rw [hs] at hb
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb
      (Nat.pow_le_pow_right (by decide : 0<2) (by omega : s.d≤i)))).symm

theorem xor_congr_to (k : Nat) (u v : Nat→Nat) (w t : Word)
    (hu : ∀ i, i<k → u i=v i) (hw : ∀ i, i<k → w i=t i) :
    xorSelected k u w = xorSelected k v t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [xorSelected]
    rw [ih (fun i h => hu i (Nat.lt_trans h (Nat.lt_succ_self _)))
           (fun i h => hw i (Nat.lt_trans h (Nat.lt_succ_self _))),
        hu k (Nat.lt_succ_self _),hw k (Nat.lt_succ_self _)]

theorem selected_ofSource (s : Raw) (hs : s.rows.length=s.d) (a j : Nat) (hj : j<s.d) :
    selected (ofSource s) a j = chosen s (numberedHead s.n a) j := by
  change (column (ofSource s) 0 j ^^^ xorSelected s.n _ _) =
    (packedColumn Term.bias j s.rows ^^^ xorSelected s.n _ _)
  rw [column_ofSource s hs 0 j (Nat.zero_lt_succ _) hj]
  apply congrArg (fun z => packedColumn Term.bias j s.rows ^^^ z)
  apply xor_congr_to
  · intro i hi
    exact column_ofSource s hs (i+1) j (Nat.succ_lt_succ hi) hj
  · intro i hi
    exact (wire_hit (numberedHead s.n a) hi).symm

theorem product_ofSource (s : Raw) (hs : s.rows.length=s.d) (a z : Nat) :
    product (ofSource s) a z = action s (numberedHead s.n a) z := by
  apply xor_congr_to
  · intro j hj; exact selected_ofSource s hs a j hj
  · intro _ _; rfl

theorem admits_source (s : Raw) (hs : s.rows.length=s.d) (a : Nat) :
    Admits (ofSource s) a ↔ NumberedKernel s a := by
  change (a<2^s.n ∧ ∃ z, z≠0 ∧ z<2^s.d ∧ product (ofSource s) a z=0) ↔
    (a<2^s.n ∧ ∃ z, z≠0 ∧ z<2^s.d ∧ action s (numberedHead s.n a) z=0)
  simp only [product_ofSource s hs]

theorem source_square (bits : BitString) : (compile bits).rows.length=(compile bits).d :=
  always_square _

theorem strict_iff_target (bits : BitString) : CNFSAT bits ↔ accept (emit bits)=true := by
  rw [accept,decode_emit,check_iff,strict_all_numbered]
  exact exists_congr (fun a => (admits_source _ (source_square bits) a).symm)

theorem strict_same_word (bits w : BitString) :
    (∃ F, decodeEncodedCNF bits=some F ∧ F.Satisfied w) ↔ acceptsWord (emit bits) w := by
  rw [acceptsWord,decode_emit,strict_same_mask_word]
  exact exists_congr (fun a => and_congr_left (fun _ => (admits_source _ (source_square bits) a).symm))

theorem emit_length (bits : BitString) :
    (emit bits).length ≤ (bits.length+1)^3 + 2*bits.length+3 := by
  rw [emit,encoded_length]
  obtain ⟨hn,hd⟩ := all_input_axes bits
  have h := coefficient_budget bits
  change ((compile bits).n+1)*(compile bits).d*(compile bits).d + (compile bits).n + (compile bits).d + 2 ≤ _
  omega

/-- Exact characterization of parses, not just a left-inverse contract. -/
theorem decoded_iff {w : BitString} {b : Bank} : decode w=some b ↔ w=encode b := by
  constructor
  · intro h; exact (encode_of_decode h).symm
  · intro h; rw [h,decode_encode]

theorem target_characterization (w : BitString) :
    accept w=true ↔ ∃ b, w=encode b ∧ ∃ a, Admits b a := by
  constructor
  · intro h
    cases e : decode w with
    | none => rw [rejected_ill_formed _ e] at h; cases h
    | some b =>
      rw [accept,e] at h
      exact ⟨b,decoded_iff.mp e,(check_iff _).mp h⟩
  · rintro ⟨b,rfl,h⟩
    rw [accept,decode_encode]
    exact (check_iff _).mpr h

theorem reject_zero_dimension (b : Bank) (hd : b.d=0) : check b=false := by
  cases h : check b with
  | false => rfl
  | true =>
    obtain ⟨_,_,z,hn,hz,_⟩ := (check_iff b).mp h
    rw [hd,Nat.pow_zero] at hz
    have z0 : z=0 := by omega
    exact False.elim (hn z0)

theorem frame_malformed_source (bits : BitString) (h : decodeEncodedCNF bits=none) :
    emit bits=[false,true,false,true] := by
  obtain ⟨hn,hd⟩ := malformed_shape bits h
  change header (compile bits).n (header (compile bits).d (payload (compile bits))) = _
  rw [hn,hd,malformed_payload bits h]; rfl

/-- Physical component formula in an arbitrary independently encoded bank. -/
theorem column_row (b : Bank) (k j r : Nat) (hr : r<b.d) :
    (column b k j).testBit r = bit b k j r := by
  rw [column,pack_spec,readWord_at,dif_pos hr]; rfl

theorem selected_row (b : Bank) (a j r : Nat) (hr : r<b.d) :
    (selected b a j).testBit r =
      (bit b 0 j r ^^ dot b.n (fun i => bit b (i+1) j r) a.testBit) := by
  rw [selected,Nat.testBit_xor,column_row _ _ _ _ hr,selected_bit]
  have e : (fun i => (column b (i+1) j).testBit r) = fun i => bit b (i+1) j r :=
    funext (fun i => column_row _ _ _ _ hr)
  rw [e]

theorem product_row (b : Bank) (a z r : Nat) (hr : r<b.d) :
    (product b a z).testBit r =
      dot b.d (fun j => bit b 0 j r ^^ dot b.n (fun i => bit b (i+1) j r) a.testBit) z.testBit := by
  rw [product,selected_bit]
  have e : (fun j => (selected b a j).testBit r) =
      fun j => bit b 0 j r ^^ dot b.n (fun i => bit b (i+1) j r) a.testBit :=
    funext (fun j => selected_row _ _ _ _ hr)
  rw [e]

end PNP.ClauseSquare.Framed

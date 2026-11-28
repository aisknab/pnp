import PNP.ClauseSquare.Raw

set_option autoImplicit false
namespace PNP.ClauseSquare
open Concrete
open SignedTernary.CNF (readWord readWord_at readWord_length)

def pack : BitString → Nat
  | [] => 0
  | b::bs => 2*pack bs + b.toNat

theorem low_bit (m : Nat) (b : Bool) : (2*m+b.toNat).testBit 0 = b := by
  rw [Nat.testBit_zero]
  cases b with
  | false =>
    change decide ((2*m+0)%2=1)=false
    exact decide_eq_false (by omega)
  | true =>
    change decide ((2*m+1)%2=1)=true
    exact decide_eq_true (by omega)

theorem next_bit (m j : Nat) (b : Bool) : (2*m+b.toNat).testBit (j+1) = m.testBit j := by
  rw [Nat.testBit_succ]
  have e : (2*m+b.toNat)/2=m := by
    cases b with
    | false => change (2*m+0)/2=m; omega
    | true => change (2*m+1)/2=m; omega
  rw [e]

theorem pack_spec (w : BitString) (j : Nat) : (pack w).testBit j = (assignmentAt w j).getD false := by
  induction w generalizing j with
  | nil => exact Nat.zero_testBit _
  | cons b bs ih =>
    cases j with
    | zero => exact low_bit _ _
    | succ j => exact (next_bit _ j _).trans (ih j)

theorem packed_word {n : Nat} (v : Head n) (j : Nat) :
    (pack (readWord n v)).testBit j = wire v j := by
  rw [pack_spec,readWord_at]
  unfold wire; split <;> rfl

theorem packed_bound (w : BitString) : pack w < 2^w.length := by
  induction w with
  | nil => decide
  | cons b bs ih =>
    rw [pack,List.length_cons,Nat.pow_succ]
    cases b with
    | false => change 2*pack bs+0 < _; omega
    | true => change 2*pack bs+1 < _; omega

def rowAt {n : Nat} : List (List (Term n)) → Nat → List (Term n)
  | [], _ => []
  | r::_, 0 => r
  | _::rs, j+1 => rowAt rs j

def packedColumn {n : Nat} (f : Term n → Bool) (j : Nat) : List (List (Term n)) → Nat
  | [] => 0
  | r::rs => 2*packedColumn f j rs + (entry f r j).toNat

theorem packed_column_bit {n : Nat} (f : Term n → Bool) (j : Nat) (rs : List (List (Term n))) (i : Nat) :
    (packedColumn f j rs).testBit i = entry f (rowAt rs i) j := by
  induction rs generalizing i with
  | nil => exact Nat.zero_testBit _
  | cons r rs ih =>
    cases i with
    | zero => exact low_bit _ _
    | succ i => exact (next_bit _ i _).trans (ih i)

def xorSelected : Nat → (Nat → Nat) → Word → Nat
  | 0,_,_ => 0
  | k+1,cs,w => xorSelected k cs w ^^^ (if w k then cs k else 0)

theorem selected_bit (d : Nat) (cs : Nat → Nat) (w : Word) (i : Nat) :
    (xorSelected d cs w).testBit i = dot d (fun j => (cs j).testBit i) w := by
  induction d with
  | zero => exact Nat.zero_testBit _
  | succ d ih =>
    rw [xorSelected,Nat.testBit_xor,ih,dot]
    cases h : w d with
    | true => simp only [if_true,Bool.and_true]
    | false => simp only [Bool.false_eq_true,if_false,Nat.zero_testBit,Bool.and_false]

def chosen (s : Raw) (x : Head s.n) (j : Nat) : Nat :=
  packedColumn Term.bias j s.rows ^^^
    xorSelected s.n (fun i => packedColumn (fun t => axisBit t i) j s.rows) (wire x)

theorem chosen_bit (s : Raw) (x : Head s.n) (j i : Nat) :
    (chosen s x j).testBit i = entry (val x) (rowAt s.rows i) j := by
  rw [chosen,Nat.testBit_xor,packed_column_bit,selected_bit,choose_entry]
  have e : (fun k => (packedColumn (fun t => axisBit t k) j s.rows).testBit i) =
      fun k => entry (fun t => axisBit t k) (rowAt s.rows i) j := by
    funext k; exact packed_column_bit _ _ _ _
  rw [e]

def action (s : Raw) (x : Head s.n) (z : Nat) : Nat :=
  xorSelected s.d (chosen s x) z.testBit

theorem action_bit (s : Raw) (x : Head s.n) (z i : Nat) :
    (action s x z).testBit i = dot s.d (entry (val x) (rowAt s.rows i)) z.testBit := by
  rw [action,selected_bit]
  have e : (fun j => (chosen s x j).testBit i) = entry (val x) (rowAt s.rows i) := by
    funext j; exact chosen_bit _ _ _ _
  rw [e]

theorem rows_at {n : Nat} (d : Nat) (x : Head n) (z : Word) (rs : List (List (Term n))) :
    KernelRows d x z rs ↔ ∀ i, dot d (entry (val x) (rowAt rs i)) z = false := by
  induction rs with
  | nil => exact ⟨fun _ _ => dot_zero _ _,fun _ => True.intro⟩
  | cons r rs ih =>
    constructor
    · rintro ⟨hr,hs⟩ i
      cases i with
      | zero => exact hr
      | succ i => exact ih.mp hs i
    · intro h
      exact ⟨h 0,ih.mpr (fun i => h (i+1))⟩

theorem action_zero (s : Raw) (x : Head s.n) (z : Nat) :
    action s x z = 0 ↔ KernelRows s.d x z.testBit s.rows := by
  rw [rows_at]
  constructor
  · intro h i; rw [← action_bit,h,Nat.zero_testBit]
  · intro h; apply Nat.eq_of_testBit_eq
    intro i; rw [action_bit,h i,Nat.zero_testBit]

def MaskWitness (s : Raw) (x : Head s.n) : Prop :=
  ∃ z : Nat, z≠0 ∧ z<2^s.d ∧ action s x z=0

theorem mask_witness (s : Raw) (x : Head s.n) : s.NullWitness x ↔ MaskWitness s x := by
  constructor
  · rintro ⟨t,⟨j,hj⟩,ht⟩
    let z := pack (readWord s.d t)
    have spec : z.testBit=wire t := funext (packed_word t)
    refine ⟨z,?_,?_,(action_zero s x z).mpr ?_⟩
    · intro bad
      have a := packed_word t j.val
      change z.testBit j.val = _ at a
      rw [bad,Nat.zero_testBit,wire_hit _ j.isLt,hj] at a
      cases a
    · have hb := packed_bound (readWord s.d t); rw [readWord_length] at hb; exact hb
    · rw [spec]; exact ht
  · rintro ⟨z,hn,hb,hz⟩
    let t : Head s.d := fun j => z.testBit j.val
    have outside : ∀ i, s.d≤i → z.testBit i=false := by
      intro i hi
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0<2) hi))
    have spec : wire t=z.testBit := by
      funext i
      by_cases e : i<s.d
      · rw [wire_hit _ e]
      · change (if h : i<s.d then t ⟨i,h⟩ else false) = _
        rw [dif_neg e,outside i (by omega)]
    obtain ⟨j,hj⟩ := Nat.exists_testBit_of_ne_zero hn
    have inside : j<s.d := by
      by_cases e : j<s.d
      · exact e
      · rw [outside j (by omega)] at hj; cases hj
    refine ⟨t,⟨⟨j,inside⟩,hj⟩,?_⟩
    rw [spec]; exact (action_zero s x z).mp hz

theorem all_original_masks (bits : BitString) :
    CNFSAT bits ↔ ∃ x : Head (compile bits).n, MaskWitness (compile bits) x := by
  rw [all_original]
  exact exists_congr (fun x => mask_witness _ x)

theorem packed_same_word (bits w : BitString) :
    (∃ F, decodeEncodedCNF bits=some F ∧ F.Satisfied w) ↔
      ∃ x : Head (compile bits).n, readWord _ x=w ∧ MaskWitness (compile bits) x := by
  rw [exact_original_word]
  exact exists_congr (fun x => and_congr_right (fun _ => mask_witness _ x))

end PNP.ClauseSquare

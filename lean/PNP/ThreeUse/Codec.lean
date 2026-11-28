import PNP.ThreeUse.FiniteTable

/-!
# Canonical binary group-word encoding

The decoder reads unary counts and indices, three target bits, and signed tokens. It rejects out-of-range labels and trailing bits without consulting any source formula.
-/

set_option autoImplicit false

namespace PNP.ThreeUse.Encoding
open PNP.Concrete

structure Packet where
  width : Nat
  rows : List (Row Nat)

def unary : Nat → BitString
  | 0 => [false]
  | n+1 => true :: unary n

def takeN : BitString → Option (Nat × BitString)
  | [] => none
  | false :: tail => some (0, tail)
  | true :: tail => do
    let (n, r)←takeN tail
    return (n+1, r)

theorem unary_spec (n : Nat) (tail : BitString) : takeN (unary n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [unary, List.cons_append, takeN, ih]; rfl

def out (g : G) : BitString := [g.a, g.b, g.c]

def tok (t : Tok Nat) : BitString := t.2 :: unary t.1

def word : Word Nat → BitString
  | [] => []
  | x :: xs => tok x ++ word xs

def row (e : Row Nat) : BitString := out e.out ++ unary e.w.length ++ word e.w

def dump : List (Row Nat) → BitString
  | [] => []
  | e :: es => row e ++ dump es

def encode (p : Packet) : BitString := unary p.width ++ unary p.rows.length ++ dump p.rows

def takeWord : Nat → BitString → Option (Word Nat × BitString)
  | 0, bs => some ([], bs)
  | _+1, [] => none
  | n+1, s :: bs => do
    let (a, rest)←takeN bs
    let (ts, tail)←takeWord n rest
    return ((a, s) :: ts, tail)

theorem word_spec (w : Word Nat) (tail : BitString) : takeWord w.length (word w ++ tail) = some (w, tail) := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    rcases t with ⟨a, s⟩
    change takeWord (w.length+1) (((s :: unary a) ++ word w) ++ tail) = _
    rw [List.append_assoc, List.cons_append, takeWord, unary_spec]; simp only [Option.bind_eq_bind, Option.bind_some, ih]; rfl

def takeRows : Nat → BitString → Option (List (Row Nat) × BitString)
  | 0, bs => some ([], bs)
  | n+1, a :: b :: c :: bs => do
    let (k, rest)←takeN bs
    let (w, rs)←takeWord k rest
    let (es, tail)←takeRows n rs
    return (⟨w, ⟨a, b, c⟩⟩ :: es, tail)
  | _+1, _ => none

theorem rows_spec (es : List (Row Nat)) (tail : BitString) : takeRows es.length (dump es ++ tail) = some (es, tail) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨w, ⟨a, b, c⟩⟩
    rw [List.length_cons, dump, row, List.append_assoc, List.append_assoc, List.append_assoc]
    change takeRows (es.length+1) (a :: b :: c :: (unary w.length ++ (word w ++ (dump es ++ tail)))) = _
    rw [takeRows, unary_spec]; simp only [Option.bind_eq_bind, Option.bind_some, word_spec, ih]; rfl

def ranged (p : Packet) : Bool := (labels p.rows).all fun i => decide (i<p.width)

theorem ranged_iff (p : Packet) : ranged p = true ↔ ∀ i, i ∈ labels p.rows → i<p.width := by
  unfold ranged; rw [List.all_eq_true]; simp only [decide_eq_true_eq]

def parse (bs : BitString) : Option (Packet × BitString) := do
  let (n, rest)←takeN bs
  let (m, mid)←takeN rest
  let (es, tail)←takeRows m mid
  return (⟨n, es⟩, tail)

theorem parse_spec (p : Packet) (tail : BitString) : parse (encode p ++ tail) = some (p, tail) := by
  rcases p with ⟨n, es⟩
  unfold parse encode; simp only [List.append_assoc, unary_spec, Option.bind_eq_bind, Option.bind_some, rows_spec]; rfl
/-- Only canonical, fully consumed, in-range descriptions survive. No source or
table of origin labels is provided to the decoder. -/
def decode (bs : BitString) : Option Packet :=
  match parse bs with
  | some (p, []) => if ranged p && decide (encode p = bs) then some p else none
  | _ => none

theorem decode_spec (p : Packet) (h : ranged p = true) : decode (encode p) = some p := by
  have z := parse_spec p []; rw [List.append_nil] at z
  unfold decode; rw [z]; change (if ranged p && decide (encode p = encode p) then some p else none) = some p
  rw [h, decide_eq_true rfl]; rfl

theorem decode_sound {bs : BitString} {p : Packet} (h : decode bs = some p) :
    ranged p = true ∧ encode p = bs := by
  unfold decode at h
  cases e : parse bs with
  | none => rw [e] at h; contradiction
  | some pr =>
    rw [e] at h; rcases pr with ⟨q, ts⟩; cases ts with
    | cons t ts => contradiction
    | nil =>
      change (if ranged q && decide (encode q = bs) then some q else none) = some p at h
      by_cases g : (ranged q && decide (encode q = bs)) = true
      · rw [if_pos g] at h; cases h; obtain ⟨a, b⟩ := Bool.and_eq_true_iff.mp g; exact ⟨a, of_decide_eq_true b⟩
      · rw [if_neg g] at h; contradiction

theorem decode_iff (bs : BitString) (p : Packet) :
    decode bs = some p ↔ ranged p = true ∧ bs = encode p := by
  constructor
  · intro h; have a := decode_sound h; exact ⟨a.1, a.2.symm⟩
  · rintro ⟨h, rfl⟩; exact decode_spec p h

theorem reject_trailing (p : Packet) (b : Bool) (rest : BitString) : decode (encode p ++ b :: rest) = none := by
  unfold decode; rw [parse_spec]
end PNP.ThreeUse.Encoding

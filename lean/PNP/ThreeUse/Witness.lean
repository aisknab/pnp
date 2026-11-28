import PNP.ThreeUse.Encoding

/-!
# Finite binary witnesses and source readback

The verifier uses only the target code and exactly three bits per declared label. Any accepted witness for an emitted target determines a satisfying word for the original strict input.
-/

set_option autoImplicit false

namespace PNP.ThreeUse.Encoding
open PNP.Concrete

def markedB : List (Row Nat) → Bool
  | [] => false
  | r :: rs => decide (r.out = mark) && decide (r.w.length = 4) &&
    rs.all (fun s => decide (s.out = one) && decide (s.w.length ≤ 12))

theorem markedB_iff (rs : List (Row Nat)) : markedB rs = true ↔ marked rs := by
  cases rs with
  | nil =>
    constructor
    · intro h; contradiction
    · rintro ⟨_, _, eq, _⟩; contradiction
  | cons r rs =>
    unfold markedB
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq, List.all_eq_true]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨r, rs, rfl, a, b, c⟩
    · rintro ⟨_, _, eq, a, b, c⟩; cases eq; exact ⟨⟨a, b⟩, c⟩

def shapeB (p : Packet) : Bool :=
  (List.range p.width).all (fun i => decide (hits i (labels p.rows) = 3)) &&
  p.rows.all (fun r => decide (r.w.map Prod.fst).Nodup) && markedB p.rows

theorem shapeB_iff (p : Packet) : shapeB p = true ↔ restricted p := by
  unfold shapeB restricted
  simp only [Bool.and_eq_true_iff, List.all_eq_true, decide_eq_true_eq, List.mem_range, markedB_iff]
  exact and_assoc

def witness : Nat → (Nat → G) → BitString
  | 0, _ => []
  | n+1, v => out (v 0) ++ witness n (fun i => v (i+1))

def loadVal : Nat → BitString → G
  | 0, a :: b :: c :: _ => ⟨a, b, c⟩
  | i+1, _ :: _ :: _ :: rest => loadVal i rest
  | _, _ => one

theorem witness_len (n : Nat) (v : Nat → G) : (witness n v).length = 3*n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [witness, List.length_append, ih]; change 3+_ = 3*(n+1); omega

theorem load_witness (n : Nat) (v : Nat → G) (i : Nat) (hi : i<n) : loadVal i (witness n v) = v i := by
  induction n generalizing v i with
  | zero => cases hi
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (fun t => v (t+1)) i (by omega)

/-- The verifier reads only output bytes and exactly three witness bits per declared slot. -/
def verify (bs w : BitString) : Bool :=
  match decode bs with
  | none => false
  | some p => shapeB p && decide (w.length = 3*p.width) &&
    p.rows.all (fun r => decide (eval (fun i => loadVal i w) r.w = r.out))

theorem witness_spec (bs : BitString) : ThreeUseSAT bs ↔ ∃ w, verify bs w = true := by
  constructor
  · rintro ⟨p, hd, cl, fin⟩
    obtain ⟨v, ok⟩ := (finite_iff _).mpr fin
    let w := witness p.width v
    refine ⟨w, ?_⟩
    have valid : holds (fun i => loadVal i w) p.rows := holds_agree _ _ _ (fun i hi =>
      load_witness _ _ _ ((ranged_iff _).mp (decode_sound hd).1 i hi)) ok
    unfold verify; rw [hd]; simp only [Bool.and_eq_true_iff, decide_eq_true_eq, List.all_eq_true]
    exact ⟨⟨(shapeB_iff _).mpr cl, witness_len _ _⟩, valid⟩
  · rintro ⟨w, hw⟩
    unfold verify at hw
    cases hd : decode bs with
    | none => rw [hd] at hw; contradiction
    | some p =>
      rw [hd] at hw; simp only [Bool.and_eq_true_iff, decide_eq_true_eq, List.all_eq_true] at hw
      exact ⟨p, hd, (shapeB_iff _).mp hw.1.1, (finite_iff _).mp ⟨_, hw.2⟩⟩

theorem source_witness (bits : BitString) : CNFSAT bits ↔ ∃ w, verify (compile bits) w = true :=
  (strict_restricted _).trans (witness_spec _)

theorem witness_replay (bits w : BitString) (h : verify (compile bits) w = true) :
    w.length = 3*(pack bits).width ∧ ∃ f, decodeEncodedCNF bits = some f ∧
      f.Satisfied (sourceWord bits (fun p => loadVal p.2 w)) := by
  unfold verify at h
  have hd : decode (compile bits) = some (pack bits) := decode_spec _ (pack_range _)
  rw [hd] at h; simp only [Bool.and_eq_true_iff, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.2, numbered_replay bits (fun k => loadVal k w) h.2⟩

theorem witness_bound (bits w : BitString) (h : verify (compile bits) w = true) :
    w.length ≤ 144*(bits.length+1) := by
  have eq := (witness_replay bits w h).1
  have wd : (pack bits).width ≤ 48*(bits.length+1) := macro_slots bits
  omega

theorem source_short_witness (bits : BitString) : CNFSAT bits ↔
    ∃ w : BitString, w.length ≤ 144*(bits.length+1) ∧ verify (compile bits) w = true := by
  constructor
  · intro h; obtain ⟨w, ok⟩ := (source_witness _).mp h; exact ⟨w, witness_bound _ _ ok, ok⟩
  · rintro ⟨w, _, ok⟩; exact (source_witness _).mpr ⟨w, ok⟩
end PNP.ThreeUse.Encoding

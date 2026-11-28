import PNP.ThreeUse.SourceCounts

/-!
# Size of the numeric bit representation

Count every unary index and header bit; combine the slot and row bounds to obtain a polynomial in the input bit length.
-/

set_option autoImplicit false

namespace PNP.ThreeUse.Encoding
open PNP.Concrete

def sumW : Word Nat → Nat
  | [] => 0
  | x :: xs => x.1+sumW xs

def sumIDs : List (Row Nat) → Nat
  | [] => 0
  | e :: es => sumW e.w+sumIDs es

theorem unary_length (n : Nat) : (unary n).length = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [unary, List.length_cons, ih]

theorem word_length (w : Word Nat) : (word w).length = sumW w+2*w.length := by
  induction w with
  | nil => rfl
  | cons x xs ih => rw [word, List.length_append, tok, List.length_cons, unary_length, ih, sumW, List.length_cons]; omega

theorem row_length (e : Row Nat) : (row e).length = 4+3*e.w.length+sumW e.w := by
  rw [row, List.length_append, List.length_append, unary_length, word_length]; change 3+(_+1)+(_+2*_) = _; omega

theorem dump_length (es : List (Row Nat)) : (dump es).length = 4*es.length+3*slots es+sumIDs es := by
  induction es with
  | nil => rfl
  | cons e es ih => rw [dump, List.length_append, row_length, ih, slots, sumIDs, List.length_cons]; omega

theorem exact_length (p : Packet) : (encode p).length = p.width+2+5*p.rows.length+3*slots p.rows+sumIDs p.rows := by
  rw [encode, List.length_append, List.length_append, unary_length, unary_length, dump_length]; omega

theorem sum_w_bound (n : Nat) (w : Word Nat) (h : ∀ i, i ∈ w.map Prod.fst → i<n) : sumW w ≤ n*w.length := by
  induction w with
  | nil => rw [sumW, List.length_nil, Nat.mul_zero]; exact Nat.le_refl _
  | cons x xs ih =>
    have a := h _ List.mem_cons_self
    have b := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    rw [sumW, List.length_cons, Nat.mul_succ]; omega

theorem sum_ids_bound (n : Nat) (rs : List (Row Nat)) (h : ∀ i, i ∈ labels rs → i<n) : sumIDs rs ≤ n*slots rs := by
  induction rs with
  | nil => change 0 ≤ n*0; exact Nat.zero_le _
  | cons r rs ih =>
    have a := sum_w_bound n r.w (fun i hi => h i (List.mem_append_left _ hi))
    have b := ih (fun i hi => h i (List.mem_append_right _ hi))
    rw [sumIDs, slots, Nat.mul_add]; exact Nat.add_le_add a b

theorem pack_counts (bits : BitString) :
    (pack bits).width = slots (macroRows (normalized bits)) ∧
    (pack bits).rows.length = (macroRows (normalized bits)).length+(pack bits).width ∧
    slots (pack bits).rows = 3*(pack bits).width := by
  refine ⟨rfl, ?_, ?_⟩
  · change (List.map _ (splitRows (macroRows (normalized bits)))).length = _
    rw [List.length_map, split_count]; rfl
  · exact (num_tokens _ _).trans (split_tokens _)

theorem byte_bound (bits : BitString) : (compile bits).length ≤ 8000*((bits.length+1)*(bits.length+1)) := by
  let n := bits.length+1
  let p := pack bits
  have n1 : 1 ≤ n := by dsimp [n]; omega
  have wk : p.width ≤ 48*n := macro_slots bits
  have ck := macro_bound bits
  have sizes := pack_counts bits
  have sk : slots p.rows ≤ 144*n := by rw [sizes.2.2]; change 3*p.width ≤ _; omega
  have rk : p.rows.length ≤ 52*n := by
    rw [sizes.2.1]; change (macroRows (normalized bits)).length+p.width ≤ _
    change (macroRows (normalized bits)).length ≤ 4*n at ck; omega
  have lim := sum_ids_bound p.width p.rows ((ranged_iff p).mp (pack_range bits))
  have mult : p.width*slots p.rows ≤ 6912*(n*n) := by
    calc
      _ ≤ (48*n)*(144*n) := Nat.mul_le_mul wk sk
      _ = 6912*(n*n) := by rw [Nat.mul_mul_mul_comm]
  have sq : n ≤ n*n := calc
    n = n*1 := (Nat.mul_one _).symm
    _ ≤ n*n := Nat.mul_le_mul_left n n1
  change (encode p).length ≤ 8000*(n*n)
  rw [exact_length]; omega
end PNP.ThreeUse.Encoding

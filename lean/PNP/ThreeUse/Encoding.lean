import PNP.ThreeUse.EncodedLength
import PNP.ThreeUse.Restriction

/-!
# An exact encoded reduction

The degree-three occurrence constraint gives the exact sum of unary label sizes. Source equivalence and the bit-length bound apply to the same encoder; no running-time bound is asserted.
-/

set_option autoImplicit false

namespace PNP.ThreeUse.Encoding
open PNP.Concrete

def natSum : List Nat → Nat
  | [] => 0
  | x :: xs => x+natSum xs

theorem sum_append (xs ys : List Nat) : natSum (xs ++ ys) = natSum xs+natSum ys := by
  induction xs with
  | nil => exact (Nat.zero_add _).symm
  | cons x xs ih => rw [List.cons_append, natSum, natSum, ih, Nat.add_assoc]

theorem sum_word (w : Word Nat) : natSum (w.map Prod.fst) = sumW w := by
  induction w with
  | nil => rfl
  | cons t w ih => exact congrArg (Nat.add t.1) ih

theorem sum_labels (rs : List (Row Nat)) : natSum (labels rs) = sumIDs rs := by
  induction rs with
  | nil => rfl
  | cons e rs ih => rw [labels, sum_append, sum_word, ih, sumIDs]

def tri : Nat → Nat
  | 0 => 0
  | n+1 => tri n+n

def hist : Nat → List Nat → Nat
  | 0, _ => 0
  | n+1, xs => hist n xs+n*hits n xs

theorem hist_nil (n : Nat) : hist n [] = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [hist, ih, hits, Nat.mul_zero]

theorem hist_cons (n x : Nat) (xs : List Nat) :
    hist n (x :: xs) = hist n xs+(if x<n then x else 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hist, hist, ih, hits, Nat.mul_add, hit]
    by_cases e : x = n
    · subst x; rw [if_pos rfl, Nat.mul_one, if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_succ_self _)]; omega
    · rw [if_neg e, Nat.mul_zero]
      by_cases g : x<n
      · rw [if_pos g, if_pos (by omega : x<n+1)]; omega
      · rw [if_neg g, if_neg (by omega : ¬x<n+1)]; omega

theorem hist_all (n : Nat) (xs : List Nat) (h : ∀ i, i ∈ xs → i<n) : hist n xs = natSum xs := by
  induction xs with
  | nil => exact hist_nil _
  | cons x xs ih => rw [hist_cons, if_pos (h _ List.mem_cons_self), ih (fun i hi => h _ (List.mem_cons_of_mem _ hi)), natSum, Nat.add_comm]

theorem hist_three (n : Nat) (xs : List Nat) (h : ∀ i, i<n → hits i xs = 3) : hist n xs = 3*tri n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hist, h n (by omega), ih (fun i hi => h i (by omega)), tri]; omega

theorem tri_double (n : Nat) : 2*tri n+n = n*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 2*(tri n+n)+(n+1) = (n+1)*(n+1)
    rw [Nat.mul_succ (n+1) n, Nat.succ_mul n n]; omega

theorem sum_slots_exact (bits : BitString) : sumIDs (pack bits).rows = 3*tri (pack bits).width := by
  rw [←sum_labels, ←hist_all (pack bits).width _ ((ranged_iff _).mp (pack_range bits))]
  exact hist_three _ _ (all_three bits)

def rawRows (bits : BitString) : Nat := (macroRows (normalized bits)).length
/-- Twice the entire bit count. This is not just a bound on abstract tuple cardinality. -/
theorem emitted_exact (bits : BitString) :
    2*(compile bits).length = 3*((pack bits).width*(pack bits).width)+27*(pack bits).width+10*rawRows bits+4 := by
  change 2*(encode (pack bits)).length = _
  rw [exact_length, sum_slots_exact, (pack_counts bits).2.1, (pack_counts bits).2.2]
  unfold rawRows
  have t := tri_double (pack bits).width; omega

/-- Exact semantic and encoded-size bridge on the same byte function. -/
theorem source_encoded (bits : BitString) :
    (CNFSAT bits ↔ ThreeUseSAT (compile bits)) ∧ decode (compile bits) = some (pack bits) ∧
    (compile bits).length ≤ 8000*((bits.length+1)*(bits.length+1)) ∧
    2*(compile bits).length = 3*((pack bits).width*(pack bits).width)+27*(pack bits).width+10*rawRows bits+4 :=
  ⟨strict_restricted bits, decode_spec _ (pack_range _), byte_bound bits, emitted_exact bits⟩
end PNP.ThreeUse.Encoding

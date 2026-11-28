import PNP.ThreeUse.Numbering
import PNP.ClauseSquare.InputLength

/-!
# Counting source slots and emitted occurrences

Bound the number of macro words and slots directly from the original strict encoding, including the invalid-input case.
-/

set_option autoImplicit false

namespace PNP.ThreeUse.Encoding
open PNP.Concrete

private abbrev totalLit := PNP.ClauseSquare.EncodedCost.allOccurrences

def occ {α : Type} : List (List α) → Nat
  | [] => 0
  | c :: cs => c.length+occ cs

theorem norm_len (n : Nat) (c : List CNFLiteral) : (normalize n c).length ≤ c.length := by
  induction c with
  | nil => exact Nat.le_refl _
  | cons l c ih =>
    rw [normalize, List.length_cons]
    split
    · rw [List.length_cons]; omega
    · omega

theorem norm_occ (n : Nat) (cs : List (List CNFLiteral)) : occ (cs.map (normalize n)) ≤ totalLit cs := by
  induction cs with
  | nil => exact Nat.le_refl _
  | cons c cs ih => exact Nat.add_le_add (norm_len _ _) ih

theorem walk_count (r : Nat) (p : List Lit) (s : Sig) (ls : List Lit) :
    (walk r p s ls).length = 1+3*ls.length := by
  induction ls generalizing p s with
  | nil => rfl
  | cons l ls ih =>
    change (walk r (l :: p) (.acc r (l :: p), false) ls).length+1+1+1 = 1+3*(ls.length+1)
    rw [ih]; omega

theorem clause_count (r : Nat) (c : List Lit) : (clause r c).length ≤ 1+3*c.length := by
  cases c with
  | nil => exact Nat.le_refl _
  | cons l ls => change (walk r [l] (.p l.i, l.pos) ls).length ≤ _; rw [walk_count, List.length_cons]; omega

theorem bank_count (cs : List (List Lit)) : (bank cs).length ≤ cs.length+3*occ cs := by
  induction cs with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
    rw [bank, List.length_append, List.length_cons, occ]; have k := clause_count cs.length c; omega

theorem macro_bound (bits : BitString) : (macroRows (normalized bits)).length ≤ 4*(bits.length+1) := by
  have m := bank_count (normalized bits)
  change (bank (normalized bits)).length+1 ≤ _
  cases hd : decodeEncodedCNF bits with
  | none =>
    have e : normalized bits = [[]] := by unfold normalized; rw [hd]
    rw [e]; change 2 ≤ _; omega
  | some f =>
    have e : normalized bits = f.clauses.map (normalize f.variableCount) := by unfold normalized; rw [hd]
    rw [e, List.length_map] at m
    rw [e]
    have n := norm_occ f.variableCount f.clauses
    have h := PNP.ClauseSquare.EncodedCost.accepted_length bits f hd
    change bits.length = 2*f.variableCount+5+4*f.clauses.length+4*totalLit f.clauses+2*_ at h
    omega

theorem sum_shapes {α : Type} (rs : List (Row α)) (h : ∀ r, r ∈ rs → r.w.length ≤ 12) :
    slots rs ≤ 12*rs.length := by
  induction rs with
  | nil => exact Nat.le_refl _
  | cons r rs ih =>
    have a := h _ List.mem_cons_self
    have b := ih (fun x hx => h _ (List.mem_cons_of_mem _ hx))
    rw [slots, List.length_cons]; omega

theorem macro_slots (bits : BitString) : slots (macroRows (normalized bits)) ≤ 48*(bits.length+1) := by
  have m := macro_bound bits
  have a : ∀ e, e ∈ macroRows (normalized bits) → e.w.length ≤ 12 := by
    intro e he; obtain h|h := List.mem_cons.mp he
    · subst e; change 4 ≤ 12; decide
    · exact (bank_shape _ _ h).2
  have b := sum_shapes _ a; omega

theorem labels_len {α : Type} (rs : List (Row α)) : (labels rs).length = slots rs := by
  induction rs with
  | nil => rfl
  | cons e rs ih => rw [labels, List.length_append, List.length_map, ih, slots]

theorem tag_count {α : Type} (rs : List (Row α)) : (tagged rs).length = rs.length := by
  induction rs with
  | nil => rfl
  | cons e rs ih => rw [tagged, List.length_cons, List.length_cons, ih]

theorem tag_tokens {α : Type} (rs : List (Row α)) : slots (tagged rs) = slots rs := by
  induction rs with
  | nil => rfl
  | cons e rs ih => change (tagWord (slots rs) e.w).length+slots (tagged rs) = e.w.length+slots rs; rw [tag_len, ih]

theorem chain_rows {α : Type} (f p : α) (ls : List α) : (chain f p ls).length = ls.length+1 := by
  induction ls generalizing p with
  | nil => rfl
  | cons a ls ih => change (chain f a ls).length+1 = ls.length+1+1; rw [ih]

theorem ring_rows {α : Type} (ls : List α) : (ring ls).length = ls.length := by
  cases ls with
  | nil => rfl
  | cons a ls => exact chain_rows _ _ _

theorem hit_comm {α : Type} [DecidableEq α] (x y : α) : hit x y = hit y x := by
  unfold hit; by_cases e : x = y
  · subst y; rfl
  · rw [if_neg (Ne.symm e), if_neg e]

def ringsN {α : Type} [DecidableEq α] (ps : List (Port α)) (os : List α) : Nat :=
  (os.flatMap (fun a => ring (bucket ps a))).length

theorem rings_cons {α : Type} [DecidableEq α] (ps : List (Port α)) (a : α) (os : List α) :
    ringsN ps (a :: os) = hits a (ps.map Prod.fst)+ringsN ps os := by
  unfold ringsN; rw [List.flatMap_cons, List.length_append, ring_rows, bucket_len]

theorem rings_add {α : Type} [DecidableEq α] (q : Port α) (ps : List (Port α)) (os : List α) :
    ringsN (q :: ps) os = ringsN ps os+hits q.1 os := by
  induction os with
  | nil => rfl
  | cons a os ih =>
    rw [rings_cons, rings_cons, List.map_cons, hits, ih, hits, hit_comm a q.1]; omega

theorem all_rings_count {α : Type} [DecidableEq α] (ps : List (Port α)) (os : List α)
    (h : ∀ p, p ∈ ps → hits p.1 os = 1) : ringsN ps os = ps.length := by
  induction ps with
  | nil =>
    induction os with
    | nil => rfl
    | cons a os ih => rw [rings_cons]; change 0+ringsN [] os = 0; rw [ih (fun _ e => nomatch e)]; rfl
  | cons p ps ih =>
    rw [rings_add, ih (fun q hq => h _ (List.mem_cons_of_mem _ hq)), h p List.mem_cons_self, List.length_cons]

theorem tie_count {α : Type} [DecidableEq α] (ts : List (Port α)) : (ties ts).length = ts.length := by
  apply all_rings_count
  intro p hp
  have mem : p.1 ∈ groups ts := (unique_mem _ _).mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have positive := (hit_mem _ _).mp mem
  have top := uniqSingle (ts.map Prod.fst) p.1
  change hits p.1 (groups ts) ≤ 1 at top; omega

theorem split_count {α : Type} [DecidableEq α] (rs : List (Row α)) :
    (splitRows rs).length = rs.length+slots rs := by
  rw [splitRows, List.length_append, tag_count, tie_count, labels_len, tag_tokens]

theorem chain_two {α : Type} (f p : α) (ls : List α) : ∀ r, r ∈ chain f p ls → r.w.length = 2 := by
  induction ls generalizing p with
  | nil => intro e he; obtain a|z := List.mem_cons.mp he; subst e; rfl; cases z
  | cons a ls ih => intro e he; obtain g|z := List.mem_cons.mp he; subst e; rfl; exact ih _ _ z

theorem tie_tokens {α : Type} [DecidableEq α] (ts : List (Port α)) : slots (ties ts) = 2*ts.length := by
  have count0 (rs : List (Row (Port α))) (hs : ∀ r, r ∈ rs → r.w.length = 2) : slots rs = 2*rs.length := by
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      rw [slots, List.length_cons, hs _ List.mem_cons_self, ih (fun e he => hs _ (List.mem_cons_of_mem _ he))]; omega
  rw [←tie_count ts]
  apply count0
  intro e he; obtain ⟨a, _, hr⟩ := List.mem_flatMap.mp he
  cases h : bucket ts a with
  | nil => rw [h] at hr; cases hr
  | cons q qs => rw [h] at hr; exact chain_two _ _ _ _ hr

theorem tokens_append {α : Type} (rs ss : List (Row α)) : slots (rs ++ ss) = slots rs+slots ss := by
  induction rs with
  | nil => exact (Nat.zero_add _).symm
  | cons r rs ih => rw [List.cons_append, slots, slots, ih, Nat.add_assoc]

theorem split_tokens {α : Type} [DecidableEq α] (rs : List (Row α)) : slots (splitRows rs) = 3*slots rs := by
  rw [splitRows, tokens_append, tie_tokens, labels_len, tag_tokens]; omega

theorem num_tokens {α β : Type} (f : α → β) (rs : List (Row α)) : slots (relabel f rs) = slots rs := by
  rw [←labels_len, renamed_labels, List.length_map, labels_len]
end PNP.ThreeUse.Encoding

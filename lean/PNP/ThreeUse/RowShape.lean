import PNP.ThreeUse.OccurrenceDegree
import PNP.ThreeUse.Source

/-!
# Length and marker of the emitted words

The leading word has length four and the required central value. Every other word has the identity as target and length at most twelve.
-/

set_option autoImplicit false

namespace PNP.ThreeUse
open PNP.Concrete

def plain {ι : Type} (r : Row ι) : Prop := r.out = one ∧ r.w.length ≤ 12

theorem neg_len {α : Type} (w : Word α) : (negWord w).length = w.length := by
  induction w with
  | nil => rfl
  | cons t w ih => rcases t with ⟨x, s⟩; rw [negWord, List.length_append, ih]; rfl

theorem comm_len {α : Type} (p q : Word α) : (comm p q).length = 2*(p.length+q.length) := by
  unfold comm; simp only [List.length_append, neg_len]; omega

theorem tw_len (a p : Name) (u : Bool) : (twist a p u).length ≤ 2 := by
  cases u with
  | false => change 1 ≤ 2; decide
  | true => change 2 ≤ 2; decide

theorem pin_len (s : Sig) : (pin s).length ≤ 12 := by
  rw [pin, comm_len]; change 2*((twist .A s.1 s.2).length+1) ≤ 12; have h := tw_len .A s.1 s.2; omega

theorem gate_len (s : Sig) (l : Lit) (u : Name) : (gate s l u).length ≤ 12 := by
  rw [gate, List.length_append, times, comm_len, comm_len]
  change 2*((twist .A s.1 s.2).length+(twist .B (.q l.i) l.pos).length)+4 ≤ 12
  have a := tw_len .A s.1 s.2; have b := tw_len .B (.q l.i) l.pos; omega

theorem walk_shape (r : Nat) (p : List Lit) (s : Sig) (ls : List Lit) : ∀ e, e ∈ walk r p s ls → plain e := by
  induction ls generalizing p s with
  | nil =>
    intro e he
    obtain h|rest := List.mem_cons.mp he
    · subst e; exact ⟨rfl, pin_len s⟩
    · cases rest
  | cons l ls ih =>
    intro e he
    obtain h|rest := List.mem_cons.mp he
    · subst e; exact ⟨rfl, by change 4 ≤ 12; decide⟩
    obtain h|rest := List.mem_cons.mp rest
    · subst e; exact ⟨rfl, by change 8 ≤ 12; decide⟩
    obtain h|rest := List.mem_cons.mp rest
    · subst e; exact ⟨rfl, gate_len _ _ _⟩
    · exact ih _ _ _ rest

theorem clause_shape (r : Nat) (c : List Lit) : ∀ e, e ∈ clause r c → plain e := by
  cases c with
  | nil =>
    intro e he; obtain h|rest := List.mem_cons.mp he
    · subst e; exact ⟨rfl, by decide⟩
    · cases rest
  | cons l ls => exact walk_shape _ _ _ _

theorem bank_shape (cs : List (List Lit)) : ∀ e, e ∈ bank cs → plain e := by
  induction cs with
  | nil => intro e he; cases he
  | cons c cs ih =>
    intro e he; rcases List.mem_append.mp he with a|b
    · exact clause_shape _ _ _ a
    · exact ih _ b

theorem tag_len {α : Type} (n : Nat) (w : Word α) : (tagWord n w).length = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih => rcases a with ⟨i, s⟩; rw [tagWord, List.length_cons, List.length_cons, ih]

theorem tagged_shape {α : Type} (rs : List (Row α)) (h : ∀ r, r ∈ rs → plain r) : ∀ r, r ∈ tagged rs → plain r := by
  induction rs with
  | nil => intro e he; cases he
  | cons x rs ih =>
    intro e he; rcases List.mem_cons.mp he with fst|rest
    · subst e; have ok := h x List.mem_cons_self
      refine ⟨ok.1, ?_⟩
      change (tagWord (slots rs) x.w).length ≤ 12
      rw [tag_len]; exact ok.2
    · exact ih (fun a ha => h _ (List.mem_cons_of_mem _ ha)) _ rest

theorem chain_shape {α : Type} (f p : α) (ls : List α) : ∀ e, e ∈ chain f p ls → plain e := by
  induction ls generalizing p with
  | nil =>
    intro e he; rcases List.mem_cons.mp he with g|g
    · subst e; exact ⟨rfl, by change 2 ≤ 12; decide⟩
    · cases g
  | cons a ls ih =>
    intro e he; rcases List.mem_cons.mp he with g|g
    · subst e; exact ⟨rfl, by change 2 ≤ 12; decide⟩
    · exact ih _ _ g

theorem ring_shape {α : Type} (ls : List α) : ∀ e, e ∈ ring ls → plain e := by
  cases ls with
  | nil => intro e he; cases he
  | cons a ls => exact chain_shape _ _ _

theorem target_shape (bits : BitString) : ∃ head tail, targetRows bits = head :: tail ∧
    head.out = mark ∧ head.w.length = 4 ∧ ∀ e, e ∈ tail → plain e := by
  let es := bank (normalized bits)
  refine ⟨⟨tagWord (slots es) frameW, mark⟩, tagged es ++ ties (labels (tagged (frame :: es))), rfl, rfl, ?_, ?_⟩
  · exact tag_len _ _
  · intro e he; rcases List.mem_append.mp he with orig|extra
    · exact tagged_shape es (bank_shape _) e orig
    · obtain ⟨_, _, hr⟩ := List.mem_flatMap.mp extra; exact ring_shape _ _ hr

theorem every_used_exactly_three (bits : BitString) (p : Port Name) (hp : p ∈ labels (targetRows bits)) :
    hits p (labels (targetRows bits)) = 3 := by
  have g : 0<hits p (labels (targetRows bits)) := (hit_mem _ _).mp hp
  have h := third_uses (macroRows (normalized bits)) p
  change hits p (labels (targetRows bits)) = _ at h
  split at h
  · exact h
  · omega

/-- Both semantic and representation conclusions concern the same literal bank. -/
theorem strict_three (bits : BitString) :
    (CNFSAT bits ↔ feasible (targetRows bits)) ∧
    (∀ p, p ∈ labels (targetRows bits) → hits p (labels (targetRows bits)) = 3) ∧
    (∃ head tail, targetRows bits = head :: tail ∧ head.out = mark ∧ head.w.length = 4 ∧ ∀ e, e ∈ tail → plain e) :=
  ⟨raw_iff bits, every_used_exactly_three bits, target_shape bits⟩
end PNP.ThreeUse

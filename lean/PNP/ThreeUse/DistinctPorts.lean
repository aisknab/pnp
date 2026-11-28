import PNP.ThreeUse.RowShape

/-!
# Distinct occurrence labels within each word

The original tagged words have distinct physical ports. Balance of the original commutators rules out a singleton equality cycle that would otherwise repeat a port in one equation.
-/

set_option autoImplicit false

namespace PNP.ThreeUse
open PNP.Concrete

def Balanced {α : Type} [DecidableEq α] (w : Word α) : Prop := ∀ p, hits (p, false) w = hits (p, true) w

theorem inv_hits {α : Type} [DecidableEq α] (w : Word α) (p : α) (s : Bool) :
    hits (p, s) (negWord w) = hits (p, !s) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨x, t⟩
    rw [negWord, hits_app, ih, hits, hits, hits]
    have e : hit (p, s) (x, !t) = hit (p, !s) (x, t) := by
      unfold hit; by_cases k : x = p
      · subst x; cases s <;> cases t <;> simp only [Prod.mk.injEq, Bool.not_true, Bool.not_false, true_and, if_true, Bool.false_eq_true, Bool.true_eq_false, if_false]
      · rw [if_neg (fun z => k (congrArg Prod.fst z)), if_neg (fun z => k (congrArg Prod.fst z))]
    rw [e]; omega

theorem comm_balance {α : Type} [DecidableEq α] (p q : Word α) : Balanced (comm p q) := by
  intro x; unfold comm
  simp only [hits_app, inv_hits, Bool.not_true, Bool.not_false]; omega

theorem app_balance {α : Type} [DecidableEq α] {p q : Word α} (hp : Balanced p) (hq : Balanced q) : Balanced (p ++ q) := by
  intro x; rw [hits_app, hits_app, hp x, hq x]

theorem walk_balance (c : Nat) (p : List Lit) (s : Sig) (ls : List Lit) : ∀ e, e ∈ walk c p s ls → Balanced e.w := by
  induction ls generalizing p s with
  | nil =>
    intro e he; obtain g|z := List.mem_cons.mp he
    · subst e; apply comm_balance
    · cases z
  | cons l ls ih =>
    intro e he; obtain g|z := List.mem_cons.mp he
    · subst e; apply comm_balance
    obtain g|z := List.mem_cons.mp z
    · subst e; exact app_balance (comm_balance _ _) (comm_balance _ _)
    obtain g|z := List.mem_cons.mp z
    · subst e; exact app_balance (comm_balance _ _) (comm_balance _ _)
    · exact ih _ _ _ z

theorem clause_balance (c : Nat) (ls : List Lit) : ∀ e, e ∈ clause c ls → Balanced e.w := by
  cases ls with
  | nil => intro e he; obtain g|z := List.mem_cons.mp he; subst e; apply comm_balance; cases z
  | cons l ls => exact walk_balance _ _ _ _

theorem sys_balance (ls : List (List Lit)) : ∀ e, e ∈ macroRows ls → Balanced e.w := by
  have all : ∀ e, e ∈ bank ls → Balanced e.w := by
    induction ls with
    | nil => intro _ he; cases he
    | cons c cs ih =>
      intro e he; obtain x|y := List.mem_append.mp he
      · exact clause_balance _ _ _ x
      · exact ih _ y
  intro e he; obtain x|y := List.mem_cons.mp he
  · subst e; apply comm_balance
  · exact all _ y

theorem hit_parts {α : Type} [DecidableEq α] (p : α) (w : Word α) :
    hits p (w.map Prod.fst) = hits (p, false) w + hits (p, true) w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rcases x with ⟨a, s⟩
    rw [List.map_cons, hits, hits, hits, ih]
    by_cases e : a = p
    · subst a; cases s <;> simp only [hit, Prod.mk.injEq, true_and, if_true, if_false, Bool.true_eq_false, Bool.false_eq_true] <;> omega
    · have h (s t : Bool) : (a, s)≠(p, t) := fun k => e (congrArg Prod.fst k)
      rw [hit, if_neg e, hit, if_neg (h _ _), hit, if_neg (h _ _)]; omega

theorem macro_even {α : Type} [DecidableEq α] (rs : List (Row α)) (h : ∀ e, e ∈ rs → Balanced e.w) (p : α) :
    ∃ k, hits p (labels rs) = 2*k := by
  induction rs with
  | nil => exact ⟨0, rfl⟩
  | cons r rs ih =>
    obtain ⟨k, hk⟩ := ih (fun e he => h _ (List.mem_cons_of_mem _ he))
    refine ⟨k+hits (p, true) r.w, ?_⟩
    change hits p (r.w.map Prod.fst ++ labels rs) = _
    rw [hits_app, hk, hit_parts, h _ List.mem_cons_self p]; omega

theorem tag_owners {α : Type} (n : Nat) (w : Word α) :
    ((tagWord n w).map Prod.fst).map Prod.fst = w.map Prod.fst := by
  induction w with
  | nil => rfl
  | cons z w ih => rcases z with ⟨a, s⟩; change a :: _ = a :: _; exact congrArg (List.cons a) ih

theorem all_owners {α : Type} (rs : List (Row α)) :
    (labels (tagged rs)).map Prod.fst = labels rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => change List.map _ ((_ ++ _) : List (Port _)) = _; rw [List.map_append, tag_owners, ih]; rfl

theorem bucket_len {α : Type} [DecidableEq α] (ps : List (Port α)) (a : α) :
    (bucket ps a).length = hits a (ps.map Prod.fst) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    unfold bucket at ih ⊢; rw [List.map_cons, hits, hit]
    by_cases e : p.1 = a
    · rw [List.filter_cons_of_pos (p := fun t : Port α => decide (t.1 = a)) (a := p) (decide_eq_true e), List.length_cons, if_pos e, ih]; omega
    · rw [List.filter_cons_of_neg (p := fun t : Port α => decide (t.1 = a)) (a := p) (fun k => e (of_decide_eq_true k)), if_neg e, ih, Nat.zero_add]

def Simple {α : Type} (w : Word α) : Prop := (w.map Prod.fst).Nodup

theorem single_nodup {α : Type} [DecidableEq α] (xs : List α) (h : ∀ p, hits p xs ≤ 1) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    apply List.nodup_cons.mpr; constructor
    · intro bad
      have k := h x
      change hit x x+hits x xs ≤ 1 at k
      rw [hit, if_pos rfl] at k; have l := (hit_mem _ _).mp bad; omega
    · apply ih; intro p; have t := h p; change hit p x+hits p xs ≤ 1 at t; omega

theorem tie_simple {α : Type} {a b : α} (g : a≠b) : Simple (tie a b).w := by
  change ([a, b] : List α).Nodup
  apply List.nodup_cons.mpr; constructor
  · intro m; obtain e|r := List.mem_cons.mp m
    · exact g e
    · cases r
  · apply List.nodup_cons.mpr; constructor
    · intro h; cases h
    · exact List.nodup_nil

theorem chain_simple {α : Type} (f p : α) (ls : List α) (nod : (p :: ls).Nodup) (fresh : f∉p :: ls) :
    ∀ e, e ∈ chain f p ls → Simple e.w := by
  induction ls generalizing p with
  | nil =>
    intro e he; obtain g|z := List.mem_cons.mp he
    · subst e; apply tie_simple; intro eq; subst p; exact fresh List.mem_cons_self
    · cases z
  | cons a ls ih =>
    intro e he; obtain g|z := List.mem_cons.mp he
    · subst e; apply tie_simple; intro eq; subst p; exact (List.nodup_cons.mp nod).1 List.mem_cons_self
    · exact ih a (List.nodup_cons.mp nod).2 (fun hf => fresh (List.mem_cons_of_mem _ hf)) _ z

theorem ring_simple {α : Type} (ls : List α) (nod : ls.Nodup) (even : ∃ k, ls.length = 2*k) :
    ∀ e, e ∈ ring ls → Simple e.w := by
  cases ls with
  | nil => intro e he; cases he
  | cons a ls =>
    cases ls with
    | nil => obtain ⟨k, hk⟩ := even; change 1 = 2*k at hk; exfalso; omega
    | cons b bs =>
      intro e he; obtain g|z := List.mem_cons.mp he
      · subst e; apply tie_simple; intro eq; subst b; exact (List.nodup_cons.mp nod).1 List.mem_cons_self
      · exact chain_simple a b bs (List.nodup_cons.mp nod).2 (List.nodup_cons.mp nod).1 _ z

theorem tagged_simple {α : Type} [DecidableEq α] (rs : List (Row α)) : ∀ e, e ∈ tagged rs → Simple e.w := by
  induction rs with
  | nil => intro e he; cases he
  | cons r rs ih =>
    intro e he; obtain g|z := List.mem_cons.mp he
    · subst e; exact single_nodup _ (tagSingle _ _)
    · exact ih _ z

theorem target_simple (bits : BitString) : ∀ e, e ∈ targetRows bits → Simple e.w := by
  intro e he; let cs := normalized bits; let rs := macroRows cs; let ts := labels (tagged rs)
  change e ∈ tagged rs ++ ties ts at he; obtain raw|rest := List.mem_append.mp he
  · exact tagged_simple _ _ raw
  · obtain ⟨a, _, hr⟩ := List.mem_flatMap.mp rest
    apply ring_simple (bucket ts a) _ _ e hr
    · apply single_nodup; intro p; rw [bucket_hits]
      by_cases k : a = p.1
      · rw [if_pos k]; exact allSingle rs p
      · rw [if_neg k]; decide
    · obtain ⟨k, hk⟩ := macro_even rs (sys_balance cs) a
      exact ⟨k, (bucket_len ts a).trans ((congrArg (hits a) (all_owners rs)).trans hk)⟩

end PNP.ThreeUse

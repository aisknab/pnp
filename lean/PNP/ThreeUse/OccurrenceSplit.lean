import PNP.ThreeUse.Group

/-!
# Equality cycles for occurrence copies

Replace each use of a symbol by a distinct occurrence and connect the copies of the same symbol by equality equations. Both extension and projection preserve the original group word equations.
-/

set_option autoImplicit false

namespace PNP.ThreeUse

abbrev Port (ι : Type) := ι × Nat

def labels {ι : Type} : List (Row ι) → List ι
  | [] => []
  | e :: es => e.w.map Prod.fst ++ labels es

def slots {ι : Type} : List (Row ι) → Nat
  | [] => 0
  | e :: es => e.w.length+slots es

def tagWord {ι : Type} (base : Nat) : Word ι → Word (Port ι)
  | [] => []
  | (a, s) :: ts => ((a, base+ts.length), s) :: tagWord base ts

def tagged {ι : Type} : List (Row ι) → List (Row (Port ι))
  | [] => []
  | e :: es => ⟨tagWord (slots es) e.w, e.out⟩ :: tagged es

def tie {α : Type} (u v : α) : Row α := zero [(u, false), (v, true)]

theorem tie_iff {α : Type} (v : α → G) (a b : α) : eval v (tie a b).w = (tie a b).out ↔ v a = v b := by
  change gmul (v a) (gmul (ginv (v b)) one) = one ↔ _
  rw [rid, inv_cancel]

def chain {α : Type} (first prev : α) : List α → List (Row α)
  | [] => [tie prev first]
  | t :: ts => tie prev t :: chain first t ts

def ring {α : Type} : List α → List (Row α)
  | [] => []
  | a :: as_ => chain a a as_

theorem chain_sound {α : Type} (v : α → G) (first prev : α) (ts : List α)
    (h : holds v (chain first prev ts)) : ∀ t, t ∈ ts → v t = v prev := by
  induction ts generalizing prev with
  | nil => intro t ht; cases ht
  | cons t ts ih =>
    obtain ⟨eq, ht⟩ := (holds_cons _ _ _).mp h
    have e := ((tie_iff _ _ _).mp eq).symm
    intro u hu; rcases List.mem_cons.mp hu with g|g
    · subst u; exact e
    · exact (ih t ht u g).trans e

theorem chain_complete {α : Type} (v : α → G) (first prev : α) (ts : List α) (y : G)
    (hf : v first = y) (hp : v prev = y) (all : ∀ t, t ∈ ts → v t = y) : holds v (chain first prev ts) := by
  induction ts generalizing prev with
  | nil =>
    apply (holds_cons _ _ _).mpr; refine ⟨(tie_iff _ _ _).mpr (hp.trans hf.symm), ?_⟩
    intro t h; cases h
  | cons t ts ih =>
    have u := all t List.mem_cons_self
    exact (holds_cons _ _ _).mpr ⟨(tie_iff _ _ _).mpr (hp.trans u.symm),
      ih t u (fun x hx => all x (List.mem_cons_of_mem _ hx))⟩

theorem ring_complete {α : Type} (v : α → G) (ts : List α) (y : G) (all : ∀ t, t ∈ ts → v t = y) :
    holds v (ring ts) := by
  cases ts with
  | nil => intro t h; cases h
  | cons a ts =>
    have ha := all a List.mem_cons_self
    exact chain_complete _ _ _ _ _ ha ha (fun x hx => all x (List.mem_cons_of_mem _ hx))

def unique {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => let u := unique xs; if x ∈ u then u else x :: u

theorem unique_mem {α : Type} [DecidableEq α] (x : α) (xs : List α) : x ∈ unique xs ↔ x ∈ xs := by
  induction xs with
  | nil => rfl
  | cons a as_ ih =>
    change x ∈ (if a ∈ unique as_ then unique as_ else a :: unique as_) ↔ _
    by_cases h : a ∈ unique as_
    · rw [if_pos h, List.mem_cons]; constructor
      · intro g; exact Or.inr (ih.mp g)
      · rintro (e|e)
        · subst x; exact h
        · exact ih.mpr e
    · rw [if_neg h, List.mem_cons, List.mem_cons, ih]

def bucket {ι : Type} [DecidableEq ι] (ts : List (Port ι)) (a : ι) : List (Port ι) :=
  ts.filter fun p => decide (p.1 = a)

theorem bucket_iff {ι : Type} [DecidableEq ι] (ts : List (Port ι)) (a : ι) (p : Port ι) :
    p ∈ bucket ts a ↔ p ∈ ts ∧ p.1 = a := by
  unfold bucket; rw [List.mem_filter, decide_eq_true_eq]

def groups {ι : Type} [DecidableEq ι] (ts : List (Port ι)) : List ι := unique (ts.map Prod.fst)

def ties {ι : Type} [DecidableEq ι] (ts : List (Port ι)) : List (Row (Port ι)) :=
  (groups ts).flatMap fun a => ring (bucket ts a)

def splitRows {ι : Type} [DecidableEq ι] (es : List (Row ι)) : List (Row (Port ι)) :=
  tagged es ++ ties (labels (tagged es))

def collapse {ι : Type} [DecidableEq ι] (ts : List (Port ι)) (v : Port ι → G) (a : ι) : G :=
  match bucket ts a with
  | [] => one
  | t :: _ => v t

theorem homogenize {ι : Type} [DecidableEq ι] (ts : List (Port ι)) (v : Port ι → G)
    (ok : holds v (ties ts)) (p : Port ι) (hp : p ∈ ts) : v p = collapse ts v p.1 := by
  have gp : p.1 ∈ groups ts := (unique_mem _ _).mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hr : holds v (ring (bucket ts p.1)) := fun e he => ok e (List.mem_flatMap.mpr ⟨p.1, gp, he⟩)
  have hb := (bucket_iff ts p.1 p).mpr ⟨hp, rfl⟩
  unfold collapse
  cases e : bucket ts p.1 with
  | nil => rw [e] at hb; cases hb
  | cons a as_ =>
    rw [e] at hr hb; rcases List.mem_cons.mp hb with h|h
    · subst a; rfl
    · exact chain_sound _ _ _ _ hr _ h

theorem tag_eval {ι : Type} (v : Port ι → G) (u : ι → G) (base : Nat) (w : Word ι)
    (h : ∀ t, t ∈ tagWord base w → v t.1 = u t.1.1) : eval v (tagWord base w) = eval u w := by
  induction w with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨a, s⟩
    have first := h ((a, base+xs.length), s) List.mem_cons_self
    have rest := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    rw [tagWord, eval, eval, rest]
    simp only [wt, first]

theorem tag_holds {ι : Type} (v : Port ι → G) (u : ι → G) (rs : List (Row ι))
    (ok : ∀ p, p ∈ labels (tagged rs) → v p = u p.1) : holds v (tagged rs) ↔ holds u rs := by
  induction rs with
  | nil => constructor <;> intro _ e he <;> cases he
  | cons r rs ih =>
    rw [tagged, holds_cons, holds_cons]
    have val := tag_eval v u (slots rs) r.w (fun t ht => ok t.1
      (List.mem_append_left _ (List.mem_map.mpr ⟨t, ht, rfl⟩)))
    have ihrest := ih (fun p hp => ok p (List.mem_append_right _ hp))
    exact and_congr (congrArg (fun g => g = r.out) val |> Iff.of_eq) ihrest

def lift {ι : Type} (v : ι → G) (p : Port ι) : G := v p.1

theorem split_lift {ι : Type} [DecidableEq ι] (rs : List (Row ι)) (v : ι → G) (ok : holds v rs) :
    holds (lift v) (splitRows rs) := by
  apply (holds_append _ _ _).mpr; constructor
  · exact (tag_holds _ _ _ (fun _ _ => rfl)).mpr ok
  · intro e he; obtain ⟨a, _, hr⟩ := List.mem_flatMap.mp he
    apply ring_complete (lift v) (bucket (labels (tagged rs)) a) (v a) _ e hr
    intro p hp; exact congrArg v ((bucket_iff _ _ _).mp hp).2

theorem split_project {ι : Type} [DecidableEq ι] (rs : List (Row ι)) (v : Port ι → G)
    (ok : holds v (splitRows rs)) : holds (collapse (labels (tagged rs)) v) rs := by
  obtain ⟨orig, eqs⟩ := (holds_append _ _ _).mp ok
  exact (tag_holds _ _ _ (homogenize _ _ eqs)).mp orig

theorem split_iff {ι : Type} [DecidableEq ι] (rs : List (Row ι)) : feasible (splitRows rs) ↔ feasible rs := by
  constructor
  · rintro ⟨v, h⟩; exact ⟨_, split_project _ _ h⟩
  · rintro ⟨v, h⟩; exact ⟨_, split_lift _ _ h⟩

end PNP.ThreeUse

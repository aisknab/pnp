import PNP.ThreeUse.OccurrenceSplit

/-!
# Exactly three uses for each occurrence

An occurrence is read once in its original word and twice by its equality cycle. The count covers the entire emitted list, including wraparound.
-/

set_option autoImplicit false

namespace PNP.ThreeUse

def hit {α : Type} [DecidableEq α] (p x : α) : Nat := if x = p then 1 else 0

def hits {α : Type} [DecidableEq α] (p : α) : List α → Nat
  | [] => 0
  | x :: xs => hit p x+hits p xs

theorem hits_app {α : Type} [DecidableEq α] (p : α) (a b : List α) :
    hits p (a ++ b) = hits p a+hits p b := by
  induction a with
  | nil => simp only [List.nil_append, hits, Nat.zero_add]
  | cons x xs ih => rw [List.cons_append, hits, hits, ih, Nat.add_assoc]

theorem hit_mem {α : Type} [DecidableEq α] (p : α) (xs : List α) : p ∈ xs ↔ 0<hits p xs := by
  induction xs with
  | nil => constructor <;> intro h <;> cases h
  | cons a xs ih =>
    change p ∈ a :: xs ↔ 0<hit p a+hits p xs
    by_cases e : a = p
    · subst a; rw [hit, if_pos rfl]; constructor
      · intro; omega
      · intro; exact List.mem_cons_self
    · rw [hit, if_neg e, Nat.zero_add, List.mem_cons]; constructor
      · rintro (no|yes)
        · exact False.elim (e no.symm)
        · exact ih.mp yes
      · intro h; exact Or.inr (ih.mpr h)

theorem none_hits {α : Type} [DecidableEq α] {p : α} {ls : List α} (h : p∉ls) : hits p ls = 0 := by
  have neg : ¬0<hits p ls := fun hp => h ((hit_mem p ls).mpr hp); omega

theorem tagBounds {ι : Type} (base : Nat) (w : Word ι) (p : Port ι) (h : p ∈ (tagWord base w).map Prod.fst) :
    base ≤ p.2 ∧ p.2<base+w.length := by
  induction w with
  | nil => cases h
  | cons x xs ih =>
    rcases x with ⟨a, s⟩
    change p ∈ (a, base+xs.length) :: (tagWord base xs).map Prod.fst at h
    rcases List.mem_cons.mp h with eq|el
    · subst p; change base ≤ base+xs.length ∧ base+xs.length<base+(xs.length+1)
      constructor <;> omega
    · obtain ⟨lo, hi⟩ := ih el
      exact ⟨lo, by simp only [List.length_cons]; omega⟩

theorem tagSingle {ι : Type} [DecidableEq ι] (base : Nat) (w : Word ι) (p : Port ι) :
    hits p ((tagWord base w).map Prod.fst) ≤ 1 := by
  induction w with
  | nil => change 0 ≤ 1; decide
  | cons x xs ih =>
    rcases x with ⟨a, s⟩
    change hit p (a, base+xs.length)+hits p ((tagWord base xs).map Prod.fst) ≤ 1
    by_cases e : (a, base+xs.length) = p
    · subst p; rw [hit, if_pos rfl]
      have h : (a, base+xs.length)∉(tagWord base xs).map Prod.fst := by
        intro z; have q := (tagBounds base xs _ z).2; exact (Nat.lt_irrefl _) q
      rw [none_hits h]; decide
    · rw [hit, if_neg e, Nat.zero_add]; exact ih

theorem allBounds {ι : Type} (rs : List (Row ι)) (p : Port ι) (h : p ∈ labels (tagged rs)) : p.2<slots rs := by
  induction rs with
  | nil => cases h
  | cons r rs ih =>
    rcases List.mem_append.mp h with e|e
    · have u := (tagBounds _ _ _ e).2
      change p.2<r.w.length+slots rs; omega
    · have u := ih e; change p.2<r.w.length+slots rs; omega

theorem allSingle {ι : Type} [DecidableEq ι] (rs : List (Row ι)) (p : Port ι) :
    hits p (labels (tagged rs)) ≤ 1 := by
  induction rs with
  | nil => change 0 ≤ 1; decide
  | cons r rs ih =>
    change hits p (((tagWord (slots rs) r.w).map Prod.fst) ++ labels (tagged rs)) ≤ 1
    rw [hits_app]
    by_cases e : p.2<slots rs
    · have no : p∉(tagWord (slots rs) r.w).map Prod.fst := by
        intro v; exact Nat.not_le_of_gt e (tagBounds _ _ _ v).1
      rw [none_hits no, Nat.zero_add]; exact ih
    · have no : p∉labels (tagged rs) := fun h => e (allBounds _ _ h)
      rw [none_hits no, Nat.add_zero]; exact tagSingle _ _ _

theorem uniqSingle {α : Type} [DecidableEq α] (os : List α) (p : α) : hits p (unique os) ≤ 1 := by
  induction os with
  | nil => change 0 ≤ 1; decide
  | cons a rest ih =>
    change hits p (if a ∈ unique rest then unique rest else a :: unique rest) ≤ 1
    by_cases e : a ∈ unique rest
    · rw [if_pos e]; exact ih
    · rw [if_neg e, hits, hit]
      by_cases k : a = p
      · subst a; rw [if_pos rfl, none_hits e]; decide
      · rw [if_neg k, Nat.zero_add]; exact ih

theorem lab_app {ι : Type} (a b : List (Row ι)) : labels (a ++ b) = labels a ++ labels b := by
  induction a with
  | nil => rfl
  | cons r rs ih => rw [List.cons_append, labels, labels, ih, List.append_assoc]

theorem chain_hits {α : Type} [DecidableEq α] (p f a : α) (ts : List α) :
    hits p (labels (chain f a ts)) = hit p a+2*hits p ts+hit p f := by
  induction ts generalizing a with
  | nil =>
    change hit p a+(hit p f+0) = hit p a+2*0+hit p f
    omega
  | cons t ts ih =>
    change hit p a+(hit p t+hits p (labels (chain f t ts))) = hit p a+2*(hit p t+hits p ts)+hit p f
    rw [ih]; omega

theorem ring_hits {α : Type} [DecidableEq α] (p : α) (ts : List α) :
    hits p (labels (ring ts)) = 2*hits p ts := by
  cases ts with
  | nil => rfl
  | cons a ts => change hits p (labels (chain a a ts)) = 2*(hit p a+hits p ts); rw [chain_hits]; omega

theorem bucket_hits {ι : Type} [DecidableEq ι] (ts : List (Port ι)) (a : ι) (p : Port ι) :
    hits p (bucket ts a) = if a = p.1 then hits p ts else 0 := by
  by_cases e : a = p.1
  · subst a; rw [if_pos rfl]
    induction ts with
    | nil => rfl
    | cons x xs ih =>
      unfold bucket at ih
      by_cases k : x.1 = p.1
      · change hits p (List.filter _ (x :: xs)) = _
        rw [List.filter_cons_of_pos (p := fun a : Port ι => decide (a.1 = p.1)) (a := x) (decide_eq_true k), hits, hits, ih]
      · change hits p (List.filter _ (x :: xs)) = _
        rw [List.filter_cons_of_neg (p := fun a : Port ι => decide (a.1 = p.1)) (a := x) (fun e => k (of_decide_eq_true e)), ih, hits, hit, if_neg (fun z => k (congrArg Prod.fst z)), Nat.zero_add]
  · rw [if_neg e]; apply none_hits; intro yes; exact e ((bucket_iff _ _ _).mp yes).2.symm

theorem all_rings_hits {ι : Type} [DecidableEq ι] (ts : List (Port ι)) (os : List ι) (p : Port ι) :
    hits p (labels (os.flatMap (fun a => ring (bucket ts a)))) = 2*(hits p ts)*(hits p.1 os) := by
  induction os with
  | nil => rw [hits, Nat.mul_zero]; rfl
  | cons a os ih =>
    rw [List.flatMap_cons, lab_app, hits_app, ring_hits, bucket_hits, ih, hits, hit]
    by_cases e : a = p.1
    · rw [if_pos e, if_pos e, Nat.mul_add, Nat.mul_one]
    · simp only [if_neg e, Nat.mul_zero, Nat.zero_add]

theorem third_uses {ι : Type} [DecidableEq ι] (rs : List (Row ι)) (p : Port ι) :
    hits p (labels (splitRows rs)) = if p ∈ labels (tagged rs) then 3 else 0 := by
  let ts := labels (tagged rs)
  change hits p (labels (tagged rs ++ ties ts)) = if p ∈ ts then 3 else 0
  rw [lab_app, hits_app]; change hits p ts+hits p (labels ((groups ts).flatMap (fun a => ring (bucket ts a)))) = _
  rw [all_rings_hits]
  by_cases e : p ∈ ts
  · have eq : hits p ts = 1 := by have h := (hit_mem p ts).mp e; have k := allSingle rs p; change hits p ts ≤ 1 at k; omega
    have eg : p.1 ∈ groups ts := (unique_mem _ _).mpr (List.mem_map.mpr ⟨p, e, rfl⟩)
    have ng : hits p.1 (groups ts) = 1 := by have h := (hit_mem _ _).mp eg; have k := uniqSingle (ts.map Prod.fst) p.1; change hits p.1 (groups ts) ≤ 1 at k; omega
    rw [if_pos e, eq, ng]
  · rw [if_neg e, none_hits e]; simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero]

end PNP.ThreeUse

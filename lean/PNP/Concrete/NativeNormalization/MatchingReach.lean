import Std

/- Source-derived reachability for finite normalization.
   This file does not decide SAT or prove the complete matching producer. -/
namespace PNP.Concrete.NativeNormalization

variable {α : Type} [DecidableEq α]

def extractMap (f : α → Option β) : List α → Option ((α × β) × List α)
  | [] => none
  | x :: xs =>
    match f x with
    | some b => some ((x, b), xs)
    | none =>
      match extractMap f xs with
      | none => none
      | some (pair, rest) => some (pair, x :: rest)

omit [DecidableEq α] in
theorem extractMap_none (f : α → Option β) (xs : List α) :
    extractMap f xs = none ↔ ∀ x ∈ xs, f x = none := by
  induction xs with
  | nil => simp [extractMap]
  | cons a xs ih =>
    cases h : f a with
    | some b => simp [extractMap, h]
    | none =>
      cases e : extractMap f xs with
      | none =>
        constructor
        · intro _ x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h
          · exact ih.mp e x hx
        · intro _
          simp [extractMap, h, e]
      | some r =>
        constructor
        · simp [extractMap, h, e]
        · intro hf
          have hn : extractMap f xs = none := ih.mpr (by
            intro x hx
            exact hf x (List.mem_cons_of_mem a hx))
          simp [e] at hn

omit [DecidableEq α] in
theorem extractMap_some (f : α → Option β) (xs : List α)
    (h : extractMap f xs = some ((v, b), rest)) :
    f v = some b ∧ xs.Perm (v :: rest) := by
  induction xs generalizing rest with
  | nil => simp [extractMap] at h
  | cons a xs ih =>
    cases e : f a with
    | some q =>
      simp only [extractMap, e] at h
      cases h
      exact ⟨e, List.Perm.refl _⟩
    | none =>
      cases k : extractMap f xs with
      | none => simp [extractMap, e, k] at h
      | some r =>
        rcases r with ⟨⟨w, q⟩, ys⟩
        simp only [extractMap, e, k] at h
        cases h
        obtain ⟨hv, hp⟩ := ih k
        exact ⟨hv, (hp.cons a).trans (List.Perm.swap v a ys)⟩

abbrev Trace (α : Type) := List (α × Option α)

def nodes (tr : Trace α) : List α := tr.map Prod.fst

def parent (seed : α → Bool) (edge : α → α → Bool) (tr : Trace α)
    (v : α) : Option (Option α) :=
  if seed v then some none
  else (tr.find? (fun p => edge p.1 v)).map (fun p => some p.1)

def eligible (seed : α → Bool) (edge : α → α → Bool) (tr : Trace α)
    (v : α) : Option (Option α) :=
  if v ∈ nodes tr then none else parent seed edge tr v

def explore (seed : α → Bool) (edge : α → α → Bool) :
    Nat → List α → Trace α → Trace α
  | 0, _, tr => tr
  | fuel + 1, unseen, tr =>
    match extractMap (eligible seed edge tr) unseen with
    | none => tr
    | some ((v, p), rest) => explore seed edge fuel rest ((v, p) :: tr)

inductive Reach (seed : α → Bool) (edge : α → α → Bool) : α → Prop
  | root {v} : seed v = true → Reach seed edge v
  | step {u v} : Reach seed edge u → edge u v = true → Reach seed edge v

inductive Valid (seed : α → Bool) (edge : α → α → Bool) : Trace α → Prop
  | nil : Valid seed edge []
  | root {tr v} : Valid seed edge tr → seed v = true →
      v ∉ nodes tr → Valid seed edge ((v, none) :: tr)
  | step {tr u v} : Valid seed edge tr → u ∈ nodes tr →
      edge u v = true → v ∉ nodes tr → Valid seed edge ((v, some u) :: tr)

omit [DecidableEq α] in
theorem parent_none (seed : α → Bool) (edge : α → α → Bool)
    (tr : Trace α) (v : α) :
    parent seed edge tr v = none ↔
      seed v = false ∧ ∀ u ∈ nodes tr, edge u v = false := by
  unfold parent
  cases hs : seed v with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro h
      have hf : tr.find? (fun p => edge p.1 v) = none := by
        cases e : tr.find? (fun p => edge p.1 v) with
        | none => rfl
        | some p => simp [e] at h
      refine ⟨True.intro, ?_⟩
      intro u hu
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
      have hn := List.find?_eq_none.mp hf p hp
      cases hval : edge p.1 v <;> simp_all
    · rintro ⟨_, h⟩
      have hf : tr.find? (fun p => edge p.1 v) = none := List.find?_eq_none.mpr (by
        intro p hp
        have hv := h p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
        simp [hv])
      simp [hf]

omit [DecidableEq α] in
theorem parent_some (seed : α → Bool) (edge : α → α → Bool)
    (tr : Trace α) (v : α) (h : parent seed edge tr v = some p) :
    match p with
    | none => seed v = true
    | some u => u ∈ nodes tr ∧ edge u v = true := by
  unfold parent at h
  cases hs : seed v with
  | true =>
    simp only [hs, ↓reduceIte] at h
    cases h
    rfl
  | false =>
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
    cases e : tr.find? (fun p => edge p.1 v) with
    | none => simp [e] at h
    | some q =>
      simp only [e, Option.map_some, Option.some.injEq] at h
      subst p
      have hm := List.mem_of_find?_eq_some e
      have ht : edge q.1 v = true := by
        exact List.find?_some (p := fun w : α × Option α => edge w.1 v) e
      exact ⟨List.mem_map.mpr ⟨q, hm, rfl⟩, ht⟩

theorem eligible_valid (seed : α → Bool) (edge : α → α → Bool)
    (tr : Trace α) (hv : Valid seed edge tr)
    (h : eligible seed edge tr v = some p) :
    Valid seed edge ((v, p) :: tr) := by
  unfold eligible at h
  split at h
  · simp at h
  · rename_i fresh
    have hp := parent_some seed edge tr v h
    cases p with
    | none => exact Valid.root hv hp fresh
    | some u => exact Valid.step hv hp.1 hp.2 fresh

theorem explore_valid (seed : α → Bool) (edge : α → α → Bool)
    (fuel : Nat) (unseen : List α) (tr : Trace α) (hv : Valid seed edge tr) :
    Valid seed edge (explore seed edge fuel unseen tr) := by
  induction fuel generalizing unseen tr with
  | zero => exact hv
  | succ fuel ih =>
    cases h : extractMap (eligible seed edge tr) unseen with
    | none => simpa only [explore, h] using hv
    | some r =>
      rcases r with ⟨⟨v, p⟩, rest⟩
      have hchoice := (extractMap_some _ _ h).1
      simpa only [explore, h] using ih rest ((v, p) :: tr) (eligible_valid _ _ _ hv hchoice)

omit [DecidableEq α] in
theorem Valid.sound {seed : α → Bool} {edge : α → α → Bool} {tr : Trace α}
    (h : Valid seed edge tr) : ∀ v ∈ nodes tr, Reach seed edge v := by
  induction h with
  | nil => simp [nodes]
  | @root tr v valid hs fresh ih =>
    intro w hw
    simp only [nodes, List.map_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact Reach.root hs
    · exact ih w hw
  | @step tr u v valid hu he fresh ih =>
    intro w hw
    simp only [nodes, List.map_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact Reach.step (ih u hu) he
    · exact ih w hw

omit [DecidableEq α] in
theorem Valid.nodup {seed : α → Bool} {edge : α → α → Bool} {tr : Trace α}
    (h : Valid seed edge tr) : (nodes tr).Nodup := by
  induction h with
  | nil => simp [nodes]
  | root _ _ fresh ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩
  | step _ _ _ fresh ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩

def Closed (seed : α → Bool) (edge : α → α → Bool) (tr : Trace α) : Prop :=
  (∀ v, seed v = true → v ∈ nodes tr) ∧
  (∀ u v, u ∈ nodes tr → edge u v = true → v ∈ nodes tr)

theorem explore_closed (seed : α → Bool) (edge : α → α → Bool)
    (fuel : Nat) (unseen : List α) (tr : Trace α)
    (bound : unseen.length ≤ fuel)
    (cover : ∀ v, v ∈ unseen ∨ v ∈ nodes tr) :
    Closed seed edge (explore seed edge fuel unseen tr) := by
  induction fuel generalizing unseen tr with
  | zero =>
    have he : unseen = [] := by
      cases unseen with
      | nil => rfl
      | cons a xs => simp only [List.length_cons] at bound; omega
    subst unseen
    have all : ∀ v, v ∈ nodes tr := by
      intro v
      exact (cover v).resolve_left (by simp)
    exact ⟨fun v _ => all v, fun _ v _ _ => all v⟩
  | succ fuel ih =>
    cases h : extractMap (eligible seed edge tr) unseen with
    | none =>
      simp only [explore, h]
      have hn := (extractMap_none _ _).mp h
      have holds : ∀ v, v ∉ nodes tr →
          seed v = false ∧ ∀ u ∈ nodes tr, edge u v = false := by
        intro v fresh
        have hin := (cover v).resolve_right fresh
        have e := hn v hin
        simp only [eligible, if_neg fresh] at e
        exact (parent_none seed edge tr v).mp e
      refine ⟨?_, ?_⟩
      · intro v hs
        change v ∈ nodes tr
        by_cases hv : v ∈ nodes tr
        · exact hv
        · have hf := (holds v hv).1
          simp [hs] at hf
      · intro u v hu he
        change v ∈ nodes tr
        change u ∈ nodes tr at hu
        by_cases hv : v ∈ nodes tr
        · exact hv
        · have hf := (holds v hv).2 u hu
          simp [he] at hf
    | some r =>
      rcases r with ⟨⟨v, p⟩, rest⟩
      have perm := (extractMap_some _ _ h).2
      have len := perm.length_eq
      have small : rest.length ≤ fuel := by simp only [List.length_cons] at len; omega
      have nextCover : ∀ w, w ∈ rest ∨ w ∈ nodes ((v, p) :: tr) := by
        intro w
        rcases cover w with old | old
        · have hm := perm.mem_iff.mp old
          rcases List.mem_cons.mp hm with rfl | hm
          · exact Or.inr (by simp [nodes])
          · exact Or.inl hm
        · exact Or.inr (by simp only [nodes, List.map_cons, List.mem_cons]; exact Or.inr old)
      simpa only [explore, h] using ih rest ((v, p) :: tr) small nextCover

def reachableTrace (n : Nat) (seed : Fin n → Bool) (edge : Fin n → Fin n → Bool) :
    Trace (Fin n) :=
  explore seed edge n (List.finRange n) []

theorem reachableTrace_valid (n : Nat) (seed : Fin n → Bool)
    (edge : Fin n → Fin n → Bool) : Valid seed edge (reachableTrace n seed edge) :=
  explore_valid seed edge n (List.finRange n) [] Valid.nil

theorem reachableTrace_closed (n : Nat) (seed : Fin n → Bool)
    (edge : Fin n → Fin n → Bool) : Closed seed edge (reachableTrace n seed edge) := by
  apply explore_closed
  · simp
  · intro v
    exact Or.inl (List.mem_finRange v)

theorem reachable_iff (n : Nat) (seed : Fin n → Bool)
    (edge : Fin n → Fin n → Bool) (v : Fin n) :
    v ∈ nodes (reachableTrace n seed edge) ↔ Reach seed edge v := by
  constructor
  · exact (reachableTrace_valid n seed edge).sound v
  · intro hv
    induction hv with
    | root hs => exact (reachableTrace_closed n seed edge).1 _ hs
    | step _ he ih => exact (reachableTrace_closed n seed edge).2 _ _ ih he

theorem reachableTrace_nodup (n : Nat) (seed : Fin n → Bool)
    (edge : Fin n → Fin n → Bool) :
    (nodes (reachableTrace n seed edge)).Nodup :=
  (reachableTrace_valid n seed edge).nodup


theorem explore_length (seed : α → Bool) (edge : α → α → Bool)
    (fuel : Nat) (unseen : List α) (tr : Trace α) :
    (explore seed edge fuel unseen tr).length ≤ fuel + tr.length := by
  induction fuel generalizing unseen tr with
  | zero => simp [explore]
  | succ fuel ih =>
    cases h : extractMap (eligible seed edge tr) unseen with
    | none => simp [explore, h]
    | some r =>
      rcases r with ⟨⟨v, p⟩, rest⟩
      have hlen := ih rest ((v, p) :: tr)
      simp only [List.length_cons] at hlen
      simpa only [explore, h] using (show
        (explore seed edge fuel rest ((v, p) :: tr)).length ≤
          fuel + 1 + tr.length by omega)

theorem reachableTrace_length (n : Nat) (seed : Fin n → Bool)
    (edge : Fin n → Fin n → Bool) :
    (reachableTrace n seed edge).length ≤ n := by
  simpa [reachableTrace] using explore_length seed edge n (List.finRange n) []

/-- Reverse paths store their terminal vertex first and an actual seed last. -/
inductive ReversePath (seed : α → Bool) (edge : α → α → Bool) : α → List α → Prop
  | root {v} : seed v = true → ReversePath seed edge v [v]
  | step {u v path} : ReversePath seed edge u path → edge u v = true →
      ReversePath seed edge v (v :: path)

def pathTo : Trace α → α → Option (List α)
  | [], _ => none
  | (w, p) :: tr, v =>
    if v = w then
      match p with
      | none => some [v]
      | some u => (pathTo tr u).map (v :: ·)
    else pathTo tr v

theorem Valid.path {seed : α → Bool} {edge : α → α → Bool} {tr : Trace α}
    (h : Valid seed edge tr) :
    ∀ v ∈ nodes tr, ∃ path,
      pathTo tr v = some path ∧ ReversePath seed edge v path ∧
      path.Nodup ∧ path.length ≤ tr.length ∧ ∀ x ∈ path, x ∈ nodes tr := by
  induction h with
  | nil => simp [nodes]
  | @root tr w valid hs fresh ih =>
    intro v hv
    by_cases eq : v = w
    · subst v
      refine ⟨[w], ?_, ReversePath.root hs, ?_, ?_, ?_⟩
      · simp [pathTo]
      · simp
      · simp
      · intro x hx
        have he : x = w := by simpa using hx
        subst x
        simp [nodes]
    · have hin : v ∈ nodes tr := by
        exact (List.mem_cons.mp hv).resolve_left eq
      obtain ⟨path, hp, hr, hn, hl, hm⟩ := ih v hin
      refine ⟨path, ?_, hr, hn, ?_, ?_⟩
      · simp [pathTo, eq, hp]
      · simp only [List.length_cons]; omega
      · intro x hx
        exact List.mem_cons_of_mem w (hm x hx)
  | @step tr u w valid hu he fresh ih =>
    intro v hv
    by_cases eq : v = w
    · subst v
      obtain ⟨path, hp, hr, hn, hl, hm⟩ := ih u hu
      refine ⟨w :: path, ?_, ReversePath.step hr he, ?_, ?_, ?_⟩
      · simp [pathTo, hp]
      · exact List.nodup_cons.mpr ⟨fun hw => fresh (hm w hw), hn⟩
      · simp only [List.length_cons]; omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem w (hm x hx)
    · have hin : v ∈ nodes tr := by
        exact (List.mem_cons.mp hv).resolve_left eq
      obtain ⟨path, hp, hr, hn, hl, hm⟩ := ih v hin
      refine ⟨path, ?_, hr, hn, ?_, ?_⟩
      · simp [pathTo, eq, hp]
      · simp only [List.length_cons]; omega
      · intro x hx
        exact List.mem_cons_of_mem w (hm x hx)

theorem reachablePath (n : Nat) (seed : Fin n → Bool)
    (edge : Fin n → Fin n → Bool) (v : Fin n) (hv : Reach seed edge v) :
    ∃ path, pathTo (reachableTrace n seed edge) v = some path ∧
      ReversePath seed edge v path ∧ path.Nodup ∧ path.length ≤ n := by
  obtain ⟨path, hp, hr, hn, hl, _⟩ :=
    (reachableTrace_valid n seed edge).path v ((reachable_iff n seed edge v).mpr hv)
  exact ⟨path, hp, hr, hn, Nat.le_trans hl (reachableTrace_length n seed edge)⟩


end PNP.Concrete.NativeNormalization

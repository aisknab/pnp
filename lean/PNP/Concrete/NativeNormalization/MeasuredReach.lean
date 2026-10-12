import PNP.Concrete.NativeNormalization.MatchingReach

namespace PNP.Concrete.NativeNormalization.MeasuredReach

/-- Explicit source-level work, not a claim about concrete tape transitions. -/
structure Measured (α : Type) where
  value : α
  cost : Nat
deriving Repr

def find (test : α → Measured Bool) : List α → Measured (Option α)
  | [] => ⟨none, 1⟩
  | a :: rest =>
      let checked := test a
      if checked.value then ⟨some a, checked.cost + 1⟩
      else
        let tail := find test rest
        ⟨tail.value, checked.cost + tail.cost + 1⟩

theorem find_value (test : α → Measured Bool) (xs : List α) :
    (find test xs).value = xs.find? (fun a => (test a).value) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases h : (test a).value <;> simp [find, List.find?, h, ih]

theorem find_cost (test : α → Measured Bool) (xs : List α) (B : Nat)
    (bound : ∀ a, (test a).cost ≤ B) :
    (find test xs).cost ≤ (B+1)*xs.length+1 := by
  induction xs with
  | nil => simp [find]
  | cons a xs ih =>
      have ha := bound a
      cases h : (test a).value <;>
        simp only [find, h, Bool.false_eq_true, if_false, if_true,
          List.length_cons, Nat.mul_succ] <;> omega

def extract (test : α → Measured (Option β)) :
    List α → Measured (Option ((α × β) × List α))
  | [] => ⟨none, 1⟩
  | a :: rest =>
      let checked := test a
      match checked.value with
      | some b => ⟨some ((a,b),rest), checked.cost+1⟩
      | none =>
          let tail := extract test rest
          ⟨tail.value.map (fun p => (p.1,a::p.2)), checked.cost+tail.cost+2⟩

theorem extract_value (test : α → Measured (Option β)) (xs : List α) :
    (extract test xs).value = extractMap (fun a => (test a).value) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases h : (test a).value with
      | some b => simp [extract, extractMap, h]
      | none =>
          simp only [extract, h, extractMap, ih]
          cases extractMap (fun a => (test a).value) xs <;> rfl

theorem extract_cost (test : α → Measured (Option β)) (xs : List α) (B : Nat)
    (bound : ∀ a, (test a).cost ≤ B) :
    (extract test xs).cost ≤ (B+2)*xs.length+1 := by
  induction xs with
  | nil => simp [extract]
  | cons a xs ih =>
      have ha := bound a
      cases h : (test a).value <;>
        simp only [extract, h, List.length_cons, Nat.mul_succ] <;> omega

/-- Fused membership avoids constructing a mapped copy of the trace. -/
def nodeMember [DecidableEq α] : Trace α → α → Measured Bool
  | [], _ => ⟨false, 1⟩
  | p :: tr, v =>
      if v = p.1 then ⟨true, 2⟩
      else
        let tail := nodeMember tr v
        ⟨tail.value, tail.cost+2⟩

theorem nodeMember_value [DecidableEq α] (tr : Trace α) (v : α) :
    (nodeMember tr v).value = decide (v ∈ nodes tr) := by
  induction tr with
  | nil => simp [nodeMember, nodes]
  | cons p tr ih =>
      by_cases h : v = p.1 <;> simp [nodeMember, h, nodes, ih]

theorem nodeMember_cost [DecidableEq α] (tr : Trace α) (v : α) :
    (nodeMember tr v).cost ≤ 2*tr.length+1 := by
  induction tr with
  | nil => simp [nodeMember]
  | cons p tr ih =>
      by_cases h : v = p.1 <;>
        simp only [nodeMember, h, if_true, if_false, List.length_cons, Nat.mul_succ] <;> omega

def parent (seed : α → Measured Bool) (edge : α → α → Measured Bool)
    (tr : Trace α) (v : α) : Measured (Option (Option α)) :=
  let root := seed v
  if root.value then ⟨some none, root.cost+1⟩
  else
    let found := find (fun p : α × Option α => edge p.1 v) tr
    ⟨found.value.map (fun p => some p.1), root.cost+found.cost+2⟩

theorem parent_value (seed : α → Measured Bool) (edge : α → α → Measured Bool)
    (tr : Trace α) (v : α) :
    (parent seed edge tr v).value =
      PNP.Concrete.NativeNormalization.parent (fun a => (seed a).value) (fun a b => (edge a b).value) tr v := by
  cases h : (seed v).value <;>
    simp [parent, PNP.Concrete.NativeNormalization.parent, find_value, h]

theorem parent_cost (seed : α → Measured Bool) (edge : α → α → Measured Bool)
    (tr : Trace α) (v : α) (S E : Nat)
    (hs : ∀ a, (seed a).cost ≤ S) (he : ∀ a b, (edge a b).cost ≤ E) :
    (parent seed edge tr v).cost ≤ S+(E+1)*tr.length+3 := by
  have hr := hs v
  have hf := find_cost (fun p : α × Option α => edge p.1 v) tr E (fun p => he p.1 v)
  cases h : (seed v).value <;>
    simp only [parent, h, Bool.false_eq_true, if_true, if_false] <;> omega

def eligible [DecidableEq α] (seed : α → Measured Bool) (edge : α → α → Measured Bool)
    (tr : Trace α) (v : α) : Measured (Option (Option α)) :=
  let seen := nodeMember tr v
  if seen.value then ⟨none, seen.cost+1⟩
  else
    let found := parent seed edge tr v
    ⟨found.value, seen.cost+found.cost+1⟩

theorem eligible_value [DecidableEq α] (seed : α → Measured Bool)
    (edge : α → α → Measured Bool) (tr : Trace α) (v : α) :
    (eligible seed edge tr v).value =
      PNP.Concrete.NativeNormalization.eligible (fun a => (seed a).value) (fun a b => (edge a b).value) tr v := by
  by_cases h : v ∈ nodes tr <;>
    simp [eligible, PNP.Concrete.NativeNormalization.eligible, nodeMember_value, parent_value, h]

theorem eligible_cost [DecidableEq α] (seed : α → Measured Bool)
    (edge : α → α → Measured Bool) (tr : Trace α) (v : α) (S E : Nat)
    (hs : ∀ a, (seed a).cost ≤ S) (he : ∀ a b, (edge a b).cost ≤ E) :
    (eligible seed edge tr v).cost ≤ (E+3)*tr.length+S+5 := by
  have hm := nodeMember_cost tr v
  have hp := parent_cost seed edge tr v S E hs he
  cases h : (nodeMember tr v).value <;>
    simp only [eligible, h, Bool.false_eq_true, if_true, if_false]
  all_goals
    simp only [Nat.add_mul, Nat.one_mul] at *
    omega


end PNP.Concrete.NativeNormalization.MeasuredReach

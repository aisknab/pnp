import PNP.Concrete.NativeNormalization.MeasuredMatchingPolynomial

namespace PNP.Concrete.NativeNormalization.MeasuredSelection

open MeasuredReach

def filter (f : α → Measured Bool) : List α → Measured (List α)
  | [] => ⟨[],1⟩
  | a::xs =>
      let head := f a
      let tail := filter f xs
      ⟨if head.value then a::tail.value else tail.value,head.cost+tail.cost+2⟩

theorem filter_value (f : α → Measured Bool) (xs : List α) :
    (filter f xs).value = xs.filter (fun a => (f a).value) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : (f a).value <;> simp [filter,h,ih]

theorem filter_cost (f : α → Measured Bool) (xs : List α) (A : Nat)
    (bound : ∀ a, (f a).cost ≤ A) :
    (filter f xs).cost ≤ (A+2)*xs.length+1 := by
  induction xs with
  | nil => simp [filter]
  | cons a xs ih =>
      have h := bound a
      simp only [filter,List.length_cons]
      rw [Nat.mul_succ]
      omega

theorem filter_length (f : α → Measured Bool) (xs : List α) :
    (filter f xs).value.length ≤ xs.length := by
  rw [filter_value]
  exact List.length_filter_le _ _

def filterMap (f : α → Measured (Option β)) : List α → Measured (List β)
  | [] => ⟨[],1⟩
  | a::xs =>
      let head := f a
      let tail := filterMap f xs
      ⟨match head.value with | none => tail.value | some b => b::tail.value,
        head.cost+tail.cost+2⟩

theorem filterMap_value (f : α → Measured (Option β)) (xs : List α) :
    (filterMap f xs).value = xs.filterMap (fun a => (f a).value) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : (f a).value <;> simp [filterMap,h,ih]

theorem filterMap_cost (f : α → Measured (Option β)) (xs : List α) (A : Nat)
    (bound : ∀ a, (f a).cost ≤ A) :
    (filterMap f xs).cost ≤ (A+2)*xs.length+1 := by
  induction xs with
  | nil => simp [filterMap]
  | cons a xs ih =>
      have h := bound a
      simp only [filterMap,List.length_cons]
      rw [Nat.mul_succ]
      omega

theorem filterMap_length (f : α → Measured (Option β)) (xs : List α) :
    (filterMap f xs).value.length ≤ xs.length := by
  induction xs with
  | nil => simp [filterMap]
  | cons a xs ih =>
      cases h : (f a).value <;> simp only [filterMap,h,List.length_cons] <;> omega

def contains [DecidableEq α] (v : α) : List α → Measured Bool
  | [] => ⟨false,1⟩
  | a::xs =>
      if v = a then ⟨true,2⟩ else
        let tail := contains v xs
        ⟨tail.value,tail.cost+2⟩

theorem contains_value [DecidableEq α] (v : α) (xs : List α) :
    (contains v xs).value = decide (v ∈ xs) := by
  induction xs with
  | nil => simp [contains]
  | cons a xs ih => by_cases h : v = a <;> simp [contains,h,ih]

theorem contains_cost [DecidableEq α] (v : α) (xs : List α) :
    (contains v xs).cost ≤ 2*xs.length+1 := by
  induction xs with
  | nil => simp [contains]
  | cons a xs ih =>
      by_cases h : v = a
      · simp only [contains,h,ite_true,List.length_cons]
        omega
      · simp only [contains,h,ite_false,List.length_cons]
        omega

/-- Match List.idxOf, including returning the list length on a miss. -/
def position [BEq α] (v : α) : List α → Measured Nat
  | [] => ⟨0,1⟩
  | a::xs =>
      if a == v then ⟨0,2⟩ else
        let tail := position v xs
        ⟨tail.value+1,tail.cost+2⟩

theorem position_value [BEq α] (v : α) (xs : List α) :
    (position v xs).value = xs.idxOf v := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : (a == v) <;> simp [position,List.idxOf_cons,h,ih]

theorem position_cost [BEq α] (v : α) (xs : List α) :
    (position v xs).cost ≤ 2*xs.length+1 := by
  induction xs with
  | nil => simp [position]
  | cons a xs ih =>
      cases h : (a == v) <;> simp only [position,h,Bool.false_eq_true,ite_false,ite_true,List.length_cons] <;> omega


end PNP.Concrete.NativeNormalization.MeasuredSelection

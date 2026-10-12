import PNP.Concrete.NativeNormalization.MeasuredSearch

namespace PNP.Concrete.NativeNormalization.MeasuredAugment

open Matching MatchingCache MeasuredReach

def decodePairs : List (Vertex c n) → Measured (List (Fin c × Fin n))
  | .inr v :: .inl i :: rest =>
      let tail := decodePairs rest
      ⟨(i,v)::tail.value,tail.cost+3⟩
  | _ => ⟨[],1⟩

theorem decodePairs_value : (xs : List (Vertex c n)) →
    (decodePairs xs).value = Matching.readPairs xs
  | [] => rfl
  | [a] => by cases a <;> rfl
  | .inl i :: b :: rest => rfl
  | .inr v :: .inr w :: rest => rfl
  | .inr v :: .inl i :: rest => by
      simp only [decodePairs,Matching.readPairs,decodePairs_value rest]

theorem decodePairs_cost : (xs : List (Vertex c n)) →
    (decodePairs xs).cost ≤ 2*xs.length+1
  | [] => by simp [decodePairs]
  | [a] => by cases a <;> simp [decodePairs]
  | .inl i :: b :: rest => by simp [decodePairs]
  | .inr v :: .inr w :: rest => by simp [decodePairs]
  | .inr v :: .inl i :: rest => by
      have h := decodePairs_cost rest
      simp only [decodePairs,List.length_cons]
      omega

theorem decodePairs_length : (xs : List (Vertex c n)) →
    (decodePairs xs).value.length ≤ xs.length
  | [] => by simp [decodePairs]
  | [a] => by cases a <;> simp [decodePairs]
  | .inl i :: b :: rest => by simp [decodePairs]
  | .inr v :: .inr w :: rest => by simp [decodePairs]
  | .inr v :: .inl i :: rest => by
      have h := decodePairs_length rest
      simp only [decodePairs,List.length_cons]
      omega

/-- The final write to an index wins, even for arbitrary repeated-index lists. -/
def latest : List (Fin c × Fin n) → Fin c → Measured (Option (Fin n))
  | [], _ => ⟨none,1⟩
  | (i,v)::rest, j =>
      let tail := latest rest j
      match tail.value with
      | some w => ⟨some w,tail.cost+1⟩
      | none => if j = i then ⟨some v,tail.cost+2⟩ else ⟨none,tail.cost+2⟩

theorem latest_augment (xs : List (Fin c × Fin n)) (m : Fin c → Option (Fin n))
    (j : Fin c) :
    Matching.augment xs m j = (latest xs j).value.orElse (fun _ => m j) := by
  induction xs generalizing m with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨i,v⟩
      simp only [Matching.augment]
      rw [ih]
      cases h : (latest rest j).value with
      | some w => simp [latest,h]
      | none =>
          by_cases hj : j = i
          · subst i
            simp [latest,h,Matching.put]
          · simp [latest,h,hj,Matching.put]

theorem latest_cost (xs : List (Fin c × Fin n)) (j : Fin c) :
    (latest xs j).cost ≤ 2*xs.length+1 := by
  induction xs with
  | nil => simp [latest]
  | cons p rest ih =>
      rcases p with ⟨i,v⟩
      cases h : (latest rest j).value with
      | some w =>
          simp only [latest,h,List.length_cons]
          omega
      | none =>
          by_cases hj : j = i
          · subst i
            simp only [latest,h,ite_true,List.length_cons]
            omega
          · simp only [latest,h,if_neg hj,List.length_cons]
            omega

def readUpdated (T : Table c n) (xs : List (Fin c × Fin n)) (j : Fin c) :
    Measured (Option (Fin n)) :=
  let written := latest xs j
  match written.value with
  | some v => ⟨some v,written.cost+1⟩
  | none =>
      let old := MeasuredMatching.readMatching T j
      ⟨old.value,written.cost+old.cost+1⟩

theorem readUpdated_value (T : Table c n) (xs : List (Fin c × Fin n)) (j : Fin c) :
    (readUpdated T xs j).value = Matching.augment xs T.get j := by
  rw [latest_augment]
  cases h : (latest xs j).value <;>
    simp [readUpdated,h,MeasuredMatching.readMatching_value]

theorem readUpdated_cost (T : Table c n) (xs : List (Fin c × Fin n)) (j : Fin c) :
    (readUpdated T xs j).cost ≤ 2*xs.length+c+4 := by
  have hw := latest_cost xs j
  have hr := MeasuredMatching.readMatching_cost T j
  cases h : (latest xs j).value <;>
    simp only [readUpdated,h] <;> omega

theorem table_eq_of_entries {a b : Table c n} (h : a.entries = b.entries) : a = b := by
  cases a
  cases b
  cases h
  rfl

def tabulate (c n : Nat) (f : Fin c → Measured (Option (Fin n))) : Measured (Table c n) :=
  let indexes := MeasuredCollections.range c
  let cells := MeasuredCollections.map f indexes.value
  ⟨⟨cells.value,by
      simp only [cells,MeasuredCollections.map_value,List.length_map,
        indexes,MeasuredCollections.range_value,List.length_finRange]⟩,
    indexes.cost+cells.cost+1⟩

theorem tabulate_value (c n : Nat) (f : Fin c → Measured (Option (Fin n))) :
    (tabulate c n f).value = Table.ofFunction (fun i => (f i).value) := by
  apply table_eq_of_entries
  simp only [tabulate,MeasuredCollections.map_value,MeasuredCollections.range_value,
    Table.ofFunction,List.finRange,List.map_ofFn,Function.comp_def]

theorem tabulate_cost (c n : Nat) (f : Fin c → Measured (Option (Fin n)))
    (B A : Nat) (hc : c ≤ B) (hf : ∀ i, (f i).cost ≤ A) :
    (tabulate c n f).cost ≤ 3*B*B+(A+2)*B+3 := by
  have hr := MeasuredCollections.range_cost c
  have hm := MeasuredCollections.map_cost f (MeasuredCollections.range c).value A hf
  rw [MeasuredCollections.range_value,List.length_finRange] at hm
  have hcc := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hc hc)
  have hp := Nat.mul_le_mul_left (A+2) hc
  simp only [tabulate,MeasuredCollections.range_value]
  simp only [Nat.mul_assoc] at *
  omega

def update (T : Table c n) (xs : List (Fin c × Fin n)) : Measured (Table c n) :=
  tabulate c n (readUpdated T xs)

theorem update_value (T : Table c n) (xs : List (Fin c × Fin n)) :
    (update T xs).value = Table.ofFunction (Matching.augment xs T.get) := by
  simp only [update,tabulate_value,readUpdated_value]

def updateBound (B : Nat) : Nat := 3*B*B+(3*B+6)*B+3

theorem update_cost (T : Table c n) (xs : List (Fin c × Fin n)) (B : Nat)
    (hc : c ≤ B) (hx : xs.length ≤ B) :
    (update T xs).cost ≤ updateBound B := by
  have h := tabulate_cost c n (readUpdated T xs) B (3*B+4) hc (by
    intro i
    have hi := readUpdated_cost T xs i
    omega)
  simpa only [update,updateBound,Nat.add_assoc] using h

def emptyTable (c n : Nat) : Measured (Table c n) :=
  tabulate c n (fun _ => ⟨none,1⟩)

theorem emptyTable_value (c n : Nat) :
    (emptyTable c n).value = Table.ofFunction (fun _ => none) := by
  simp only [emptyTable,tabulate_value]

theorem emptyTable_cost (c n B : Nat) (hc : c ≤ B) :
    (emptyTable c n).cost ≤ 3*B*B+3*B+3 :=
  tabulate_cost c n (fun _ => ⟨none,1⟩) B 1 hc (fun _ => Nat.le_refl _)


end PNP.Concrete.NativeNormalization.MeasuredAugment

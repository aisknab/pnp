import PNP.Concrete.NativeNormalization.MeasuredFrontendCost

namespace PNP.Concrete.NativeNormalization.MeasuredCollections

open MeasuredReach Matching

def map (f : α → Measured β) : List α → Measured (List β)
  | [] => ⟨[],1⟩
  | a::xs =>
      let head := f a
      let tail := map f xs
      ⟨head.value::tail.value,head.cost+tail.cost+2⟩

theorem map_value (f : α → Measured β) (xs : List α) :
    (map f xs).value = xs.map (fun a => (f a).value) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [map,ih]

theorem map_cost (f : α → Measured β) (xs : List α) (B : Nat)
    (bound : ∀ a, (f a).cost ≤ B) :
    (map f xs).cost ≤ (B+2)*xs.length+1 := by
  induction xs with
  | nil => simp [map]
  | cons a xs ih =>
      have h := bound a
      simp only [map,List.length_cons]
      rw [Nat.mul_succ]
      omega

def append : List α → List α → Measured (List α)
  | [], ys => ⟨ys,1⟩
  | a::xs, ys =>
      let tail := append xs ys
      ⟨a::tail.value,tail.cost+1⟩

theorem append_value (xs ys : List α) : (append xs ys).value = xs++ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [append,ih]

theorem append_cost (xs ys : List α) : (append xs ys).cost = xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [append,ih]

/-- Each shifted index is explicitly visited; no generated range is a free input. -/
def range : (n : Nat) → Measured (List (Fin n))
  | 0 => ⟨[],1⟩
  | n+1 =>
      let previous := range n
      let shifted := map (fun i : Fin n => (⟨i.succ,1⟩ : Measured (Fin (n+1)))) previous.value
      ⟨0::shifted.value,previous.cost+shifted.cost+2⟩

theorem range_value (n : Nat) : (range n).value = List.finRange n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [range,map_value,ih,List.finRange,List.ofFn_succ,List.map_ofFn,Function.comp_def]

theorem range_cost (n : Nat) : (range n).cost ≤ 3*n*n+1 := by
  induction n with
  | zero => simp [range]
  | succ n ih =>
      have hm := map_cost (fun i : Fin n => (⟨i.succ,1⟩ : Measured (Fin (n+1))))
        (range n).value 1 (fun _ => Nat.le_refl _)
      rw [range_value,List.length_finRange] at hm
      simp only [range,range_value]
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul] at *
      omega

def vertices (c n : Nat) : Measured (List (Vertex c n)) :=
  let leftRange := range c
  let rightRange := range n
  let left := map (fun i : Fin c => (⟨Sum.inl i,1⟩ : Measured (Vertex c n))) leftRange.value
  let right := map (fun i : Fin n => (⟨Sum.inr i,1⟩ : Measured (Vertex c n))) rightRange.value
  let joined := append left.value right.value
  ⟨joined.value,leftRange.cost+rightRange.cost+left.cost+right.cost+joined.cost+1⟩

theorem vertices_value (c n : Nat) : (vertices c n).value = Matching.vertices c n := by
  simp only [vertices,append_value,map_value,range_value,Matching.vertices]

theorem vertices_cost (c n B : Nat) (hc : c ≤ B) (hn : n ≤ B) :
    (vertices c n).cost ≤ 6*B*B+7*B+6 := by
  have hrc := range_cost c
  have hrn := range_cost n
  have hl := map_cost (fun i : Fin c => (⟨Sum.inl i,1⟩ : Measured (Vertex c n)))
    (range c).value 1 (fun _ => Nat.le_refl _)
  have hr := map_cost (fun i : Fin n => (⟨Sum.inr i,1⟩ : Measured (Vertex c n)))
    (range n).value 1 (fun _ => Nat.le_refl _)
  rw [range_value,List.length_finRange] at hl hr
  have hcc := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hc hc)
  have hnn := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hn hn)
  simp only [vertices,append_cost,map_value,List.length_map,range_value,List.length_finRange]
  simp only [Nat.mul_assoc] at *
  omega


end PNP.Concrete.NativeNormalization.MeasuredCollections

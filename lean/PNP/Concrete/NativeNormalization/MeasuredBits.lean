import PNP.Concrete.NativeNormalization.MeasuredRunPolynomial

namespace PNP.Concrete.NativeNormalization.MeasuredBits

open PNP.Concrete MeasuredReach NativeEquations

theorem lookup_assignmentAt (a : BitString) (k : Nat) :
    (MeasuredMatching.lookup a k).value = assignmentAt a k := by
  induction a generalizing k with
  | nil => rfl
  | cons b a ih =>
      cases k with
      | zero => rfl
      | succ k => simpa [MeasuredMatching.lookup,assignmentAt] using ih k

theorem lookup_index_cost (xs : List α) (k : Nat) :
    (MeasuredMatching.lookup xs k).cost ≤ k+1 := by
  induction xs generalizing k with
  | nil => simp [MeasuredMatching.lookup]
  | cons x xs ih =>
      cases k with
      | zero => simp [MeasuredMatching.lookup]
      | succ k =>
          have h := ih k
          simp only [MeasuredMatching.lookup]
          omega

def read (a : BitString) (k : Nat) : Measured Bool :=
  let found := MeasuredMatching.lookup a k
  ⟨found.value.getD false,found.cost+1⟩

theorem read_value (a : BitString) (k : Nat) :
    (read a k).value = (assignmentAt a k).getD false := by
  simp only [read,lookup_assignmentAt]

theorem read_getElem (a : BitString) (k : Nat) :
    (read a k).value = (a[k]?).getD false := by
  simp only [read,MeasuredMatching.lookup_value]

theorem read_length_cost (a : BitString) (k : Nat) : (read a k).cost ≤ a.length+2 := by
  have h := MeasuredMatching.lookup_cost a k
  simp only [read]
  omega

theorem read_index_cost (a : BitString) (k : Nat) : (read a k).cost ≤ k+2 := by
  have h := lookup_index_cost a k
  simp only [read]
  omega

/-- Two consecutive bits per row index, false-labelled row first. Missing bits default false. -/
def rowValues (c : Nat) (a : BitString) : RowValues c :=
  fun r => (a[2*r.1.val+(if r.2 then 1 else 0)]?).getD false

def readRow (a : BitString) (r : Row c) : Measured Bool :=
  let bit := read a (2*r.1.val+(if r.2 then 1 else 0))
  ⟨bit.value,bit.cost+3⟩

theorem readRow_value (a : BitString) (r : Row c) :
    (readRow a r).value = rowValues c a r := by
  simp only [readRow,read_getElem,rowValues]

/-- The inspected prefix is bounded by the row index, even for an overlong input list. -/
theorem readRow_cost (a : BitString) (r : Row c) (B : Nat) (hc : c ≤ B) :
    (readRow a r).cost ≤ 2*B+4 := by
  have hi := r.1.isLt
  have h := read_index_cost a (2*r.1.val+(if r.2 then 1 else 0))
  cases hb : r.2 <;> simp only [readRow,hb,Bool.false_eq_true,if_true,if_false] at * <;> omega

def project (n : Nat) (a : BitString) : Measured BitString :=
  let indices := MeasuredCollections.range n
  let bits := MeasuredCollections.map (fun i : Fin n => read a i.val) indices.value
  ⟨bits.value,indices.cost+bits.cost+1⟩

theorem project_value (n : Nat) (a : BitString) :
    (project n a).value = List.ofFn (fun i : Fin n => NativeTseitin.readValues a i.val) := by
  simp only [project,MeasuredCollections.map_value,MeasuredCollections.range_value,
    read_getElem,NativeTseitin.readValues]
  simp [List.finRange,List.map_ofFn,Function.comp_def]

theorem project_length (n : Nat) (a : BitString) : (project n a).value.length = n := by
  rw [project_value,List.length_ofFn]

def projectBound (B : Nat) : Nat := 3*B*B+(B+3)*B+3

theorem project_cost (n : Nat) (a : BitString) (B : Nat) (hn : n ≤ B) :
    (project n a).cost ≤ projectBound B := by
  have hr := MeasuredCollections.range_cost n
  have bound : ∀ i : Fin n, (read a i.val).cost ≤ B+1 := by
    intro i
    have h := read_index_cost a i.val
    have hi := i.isLt
    omega
  have hm := MeasuredCollections.map_cost (fun i : Fin n => read a i.val)
    (MeasuredCollections.range n).value (B+1) bound
  rw [MeasuredCollections.range_value,List.length_finRange] at hm
  have hnn := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hn hn)
  have hlinear := Nat.mul_le_mul_left (B+3) hn
  simp only [project,projectBound]
  simp only [MeasuredCollections.range_value,Nat.add_assoc,Nat.reduceAdd,Nat.mul_assoc] at *
  omega

theorem recoverOriginal_value (F : CNFFormula) (a : BitString) :
    (project F.variableCount a).value = NativeTseitin.recoverOriginal F a := by
  rw [project_value]
  rfl


end PNP.Concrete.NativeNormalization.MeasuredBits

import PNP.Concrete.NativeNormalization.MeasuredBits

namespace PNP.Concrete.NativeNormalization.MeasuredCutRecovery

open PNP.Concrete MeasuredReach NativeContext

def occurrence (F : CNFFormula) (i : Fin F.clauses.length) (v : Fin F.variableCount) :
    Measured (Option CNFLiteral) :=
  let clause := MeasuredMatching.readClause F i
  let found := MeasuredReach.find (fun l : CNFLiteral => ⟨l.variableIndex == v.val,1⟩) clause.value
  ⟨found.value,clause.cost+found.cost+1⟩

theorem occurrence_value (F : CNFFormula) (i : Fin F.clauses.length) (v : Fin F.variableCount) :
    (occurrence F i v).value = CNFCore.occurrence F i v := by
  simp only [occurrence,MeasuredReach.find_value,MeasuredMatching.readClause_value,CNFCore.occurrence]

theorem occurrence_cost (F : CNFFormula) (i : Fin F.clauses.length) (v : Fin F.variableCount)
    (L : Nat) (hl : (CNFCore.clause F i).length ≤ L) :
    (occurrence F i v).cost ≤ F.clauses.length+2*L+4 := by
  have hc := MeasuredMatching.readClause_cost F i
  have hf := MeasuredReach.find_cost
    (fun l : CNFLiteral => (⟨l.variableIndex == v.val,1⟩ : Measured Bool))
    (MeasuredMatching.readClause F i).value 1 (fun _ => Nat.le_refl _)
  rw [MeasuredMatching.readClause_value] at hf
  simp only [occurrence,MeasuredMatching.readClause_value]
  omega

def preferred {F : CNFFormula} (C : CutData F) (v : Fin F.variableCount) : Measured Bool :=
  let owner := MeasuredSearch.owner (MeasuredAccess.table C) v
  match owner.value with
  | none => ⟨false,owner.cost+1⟩
  | some i =>
      let literal := occurrence F i v
      ⟨(literal.value.map CNFLiteral.positive).getD false,owner.cost+literal.cost+2⟩

theorem preferred_value {F : CNFFormula} (C : CutData F) (v : Fin F.variableCount) :
    (preferred C v).value = C.preferred v := by
  cases h : Matching.owner C.matchAt v <;>
    simp only [preferred,MeasuredSearch.owner_value,MeasuredAccess.table_get,CutData.preferred,
      h,occurrence_value]

def preferredBound (B : Nat) : Nat := MeasuredSearch.ownerBound B+B+12

theorem preferred_cost {F : CNFFormula} (C : CutData F) (v : Fin F.variableCount)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) :
    (preferred C v).cost ≤ preferredBound B := by
  have ho := MeasuredSearch.owner_cost (MeasuredAccess.table C) v B (by omega)
  cases h : (MeasuredSearch.owner (MeasuredAccess.table C) v).value with
  | none =>
      simp only [preferred,h,preferredBound]
      omega
  | some i =>
      have hl := occurrence_cost F i v 3 (shape i)
      simp only [preferred,h,preferredBound]
      omega

def bit {F : CNFFormula} (C : CutData F) (a : BitString) (v : Fin F.variableCount) :
    Measured Bool :=
  let inside := MeasuredSelection.contains v C.variableData
  if inside.value then
    let position := MeasuredSelection.position v C.variableData
    let found := MeasuredBits.read a position.value
    ⟨found.value,inside.cost+position.cost+found.cost+2⟩
  else
    let found := preferred C v
    ⟨found.value,inside.cost+found.cost+1⟩

theorem bit_value {F : CNFFormula} (C : CutData F) (a : BitString) (v : Fin F.variableCount) :
    (bit C a v).value =
      if v ∈ C.variableData then (assignmentAt a (C.variableData.idxOf v)).getD false
      else C.preferred v := by
  by_cases h : v ∈ C.variableData <;>
    simp [bit,MeasuredSelection.contains_value,MeasuredSelection.position_value,
      MeasuredBits.read_value,preferred_value,h]

def bitBound (B A : Nat) : Nat := MeasuredSearch.ownerBound B+4*B+A+16

theorem bit_cost {F : CNFFormula} (C : CutData F) (a : BitString) (v : Fin F.variableCount)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) :
    (bit C a v).cost ≤ bitBound B a.length := by
  have hn := MeasuredAccess.variableData_bound C
  have hi := MeasuredSelection.contains_cost v C.variableData
  have hp := MeasuredSelection.position_cost v C.variableData
  have hr := MeasuredBits.read_length_cost a (MeasuredSelection.position v C.variableData).value
  have hf := preferred_cost C v shape B size
  unfold bit
  dsimp only
  split <;> dsimp only <;> unfold bitBound preferredBound at * <;> omega

def recover {F : CNFFormula} (C : CutData F) (a : BitString) : Measured BitString :=
  let indices := MeasuredCollections.range F.variableCount
  let bits := MeasuredCollections.map (bit C a) indices.value
  ⟨bits.value,indices.cost+bits.cost+1⟩

theorem recover_value {F : CNFFormula} (C : CutData F) (a : BitString) :
    (recover C a).value = C.recover a := by
  simp only [recover,MeasuredCollections.map_value,MeasuredCollections.range_value,
    bit_value,CutData.recover]
  simp [List.finRange,List.map_ofFn,Function.comp_def]

theorem recover_length {F : CNFFormula} (C : CutData F) (a : BitString) :
    (recover C a).value.length = F.variableCount := by
  rw [recover_value]
  simp only [CutData.recover,List.length_ofFn]

def recoverBound (B A : Nat) : Nat := 3*B*B+(bitBound B A+2)*B+3

theorem recover_cost {F : CNFFormula} (C : CutData F) (a : BitString)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B A : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) (ha : a.length ≤ A) :
    (recover C a).cost ≤ recoverBound B A := by
  have hn : F.variableCount ≤ B := by omega
  have hr := MeasuredCollections.range_cost F.variableCount
  have bound : ∀ v, (bit C a v).cost ≤ bitBound B A := by
    intro v
    have h := bit_cost C a v shape B size
    unfold bitBound at *
    omega
  have hm := MeasuredCollections.map_cost (bit C a)
    (MeasuredCollections.range F.variableCount).value (bitBound B A) bound
  rw [MeasuredCollections.range_value,List.length_finRange] at hm
  have hnn := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hn hn)
  have hlinear := Nat.mul_le_mul_left (bitBound B A+2) hn
  simp only [recover,recoverBound]
  simp only [MeasuredCollections.range_value,Nat.mul_assoc] at *
  omega


end PNP.Concrete.NativeNormalization.MeasuredCutRecovery

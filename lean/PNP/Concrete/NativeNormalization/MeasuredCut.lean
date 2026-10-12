import PNP.Concrete.NativeNormalization.MeasuredSelection

namespace PNP.Concrete.NativeNormalization.MeasuredCut

open PNP.Concrete Matching MatchingCache MeasuredReach NativeContext

def selectRange (n : Nat) (f : Fin n → Measured Bool) : Measured (List (Fin n)) :=
  let indexes := MeasuredCollections.range n
  let chosen := MeasuredSelection.filter f indexes.value
  ⟨chosen.value,indexes.cost+chosen.cost+1⟩

theorem selectRange_value (n : Nat) (f : Fin n → Measured Bool) :
    (selectRange n f).value = (List.finRange n).filter (fun i => (f i).value) := by
  simp only [selectRange,MeasuredSelection.filter_value,MeasuredCollections.range_value]

theorem selectRange_length (n : Nat) (f : Fin n → Measured Bool) :
    (selectRange n f).value.length ≤ n := by
  rw [selectRange_value]
  simpa only [List.length_finRange] using
    (List.length_filter_le (fun i => (f i).value) (List.finRange n))

theorem selectRange_cost (n : Nat) (f : Fin n → Measured Bool) (B A : Nat)
    (size : n ≤ B) (bound : ∀ i, (f i).cost ≤ A) :
    (selectRange n f).cost ≤ 3*B*B+(A+2)*B+3 := by
  have hr := MeasuredCollections.range_cost n
  have hf := MeasuredSelection.filter_cost f (MeasuredCollections.range n).value A bound
  rw [MeasuredCollections.range_value,List.length_finRange] at hf
  have hsq := Nat.mul_le_mul_left 3 (Nat.mul_le_mul size size)
  have hm := Nat.mul_le_mul_left (A+2) size
  simp only [selectRange,MeasuredCollections.range_value]
  simp only [Nat.mul_assoc] at *
  omega

theorem matching_entries (F : CNFFormula) :
    (MeasuredMatchingLoop.fullTable F).value.entries = List.ofFn (CNFCore.matching F) := by
  rw [MeasuredMatchingLoop.fullTable_value,MatchingCache.fullTable_entries]
  rfl

theorem final_trace (F : CNFFormula) :
    (MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value = CNFCore.trace F := by
  rw [MeasuredSearch.scan_value,MeasuredMatchingLoop.fullTable_get]
  rfl

/-- Selection is computed from the terminal source-derived trace, never supplied. -/
def prepare (F : CNFFormula) : Measured (CutData F) :=
  let matched := MeasuredMatchingLoop.fullTable F
  let scanned := MeasuredSearch.scan F matched.value
  let clauses := selectRange F.clauses.length (fun i => nodeMember scanned.value (.inl i))
  let variables := selectRange F.variableCount (fun v => nodeMember scanned.value (.inr v))
  let data : CutData F :=
    { matchingData := matched.value.entries
      matching_eq := matching_entries F
      nodeData := scanned.value
      node_eq := final_trace F
      clauseData := clauses.value
      clause_eq := by
        simp only [clauses,selectRange_value,nodeMember_value,scanned,matched,final_trace]
        unfold CNFCore.positions
        apply congrArg (fun p : Fin F.clauses.length → Bool => (List.finRange F.clauses.length).filter p)
        funext i
        by_cases h : Sum.inl i ∈ nodes (CNFCore.trace F) <;> simp [CNFCore.kept,h]
      variableData := variables.value
      variable_eq := by
        simp only [variables,selectRange_value,nodeMember_value,scanned,matched,final_trace]
        unfold CNFCore.variables
        apply congrArg (fun p : Fin F.variableCount → Bool => (List.finRange F.variableCount).filter p)
        funext v
        by_cases h : Sum.inr v ∈ nodes (CNFCore.trace F) <;> simp [CNFCore.inside,h] }
  ⟨data,matched.cost+scanned.cost+clauses.cost+variables.cost+1⟩

theorem cutData_unique {F : CNFFormula} (C D : CutData F) : C = D := by
  rcases C with ⟨cm,hm,ct,ht,cc,hc,cv,hv⟩
  rcases D with ⟨dm,hm',dt,ht',dc,hc',dv,hv'⟩
  have em : cm = dm := hm.trans hm'.symm
  have et : ct = dt := ht.trans ht'.symm
  have ec : cc = dc := hc.trans hc'.symm
  have ev : cv = dv := hv.trans hv'.symm
  cases em
  cases et
  cases ec
  cases ev
  rfl

theorem prepare_value (F : CNFFormula) :
    (prepare F).value = NativeContext.prepareCut F :=
  cutData_unique _ _

def selectionBound (B : Nat) : Nat := 3*B*B+(2*B+3)*B+3
def cutBound (B : Nat) : Nat :=
  MeasuredMatchingLoop.fullBound B+MeasuredSearch.scanBound B+
    selectionBound B+selectionBound B+1

theorem prepare_cost (F : CNFFormula)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) :
    (prepare F).cost ≤ cutBound B := by
  have hm := MeasuredMatchingLoop.fullTable_cost F shape B size
  have hs := MeasuredSearch.scan_cost F (MeasuredMatchingLoop.fullTable F).value shape B size
  have ht : (MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value.length ≤ B := by
    rw [MeasuredSearch.scan_value]
    exact Nat.le_trans (Matching.scan_length _ _) size
  have hc := selectRange_cost F.clauses.length
    (fun i => nodeMember (MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value
      (.inl i)) B (2*B+1) (by omega) (by
        intro i
        have h := nodeMember_cost
          (MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value (.inl i)
        omega)
  have hv := selectRange_cost F.variableCount
    (fun v => nodeMember (MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value
      (.inr v)) B (2*B+1) (by omega) (by
        intro v
        have h := nodeMember_cost
          (MeasuredSearch.scan F (MeasuredMatchingLoop.fullTable F).value).value (.inr v)
        omega)
  rw [show 2*B+1+2=2*B+3 by omega] at hc hv
  simp only [prepare,cutBound,selectionBound]
  omega

theorem decoded_prepare_cost (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (prepare (NativeTseitin.frontend F)).cost ≤ cutBound (21*bits.length+9) := by
  have shape : ∀ i, (CNFCore.clause (NativeTseitin.frontend F) i).length ≤ 3 := by
    intro i
    exact Nat.le_of_eq
      (NativeTseitin.frontend_shape F _ (CNFCore.source_member (NativeTseitin.frontend F) i)).1
  have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
  exact prepare_cost (NativeTseitin.frontend F) shape (21*bits.length+9) (by omega)


end PNP.Concrete.NativeNormalization.MeasuredCut

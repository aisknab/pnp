import PNP.Concrete.NativeNormalization.MeasuredCut

namespace PNP.Concrete.NativeNormalization.MeasuredPrepared

open PNP.Concrete MeasuredReach NativeContext

def compactLiteral {F : CNFFormula} (C : CutData F) (l : CNFLiteral) :
    Measured (Option CNFLiteral) :=
  if valid : l.variableIndex < F.variableCount then
    let v : Fin F.variableCount := ⟨l.variableIndex,valid⟩
    let present := MeasuredSelection.contains v C.variableData
    if present.value then
      let index := MeasuredSelection.position v C.variableData
      ⟨some ⟨l.positive,index.value⟩,present.cost+index.cost+3⟩
    else ⟨none,present.cost+2⟩
  else ⟨none,1⟩

theorem compactLiteral_value {F : CNFFormula} (C : CutData F) (l : CNFLiteral) :
    (compactLiteral C l).value = C.compactLiteral l := by
  by_cases h : l.variableIndex < F.variableCount
  · by_cases active : (⟨l.variableIndex,h⟩ : Fin F.variableCount) ∈ C.variableData
    · simp [compactLiteral,NativeContext.CutData.compactLiteral,h,
        MeasuredSelection.contains_value,MeasuredSelection.position_value,active]
    · simp [compactLiteral,NativeContext.CutData.compactLiteral,h,
        MeasuredSelection.contains_value,active]
  · simp [compactLiteral,NativeContext.CutData.compactLiteral,h]

theorem compactLiteral_cost {F : CNFFormula} (C : CutData F) (l : CNFLiteral) :
    (compactLiteral C l).cost ≤ 4*C.variableData.length+5 := by
  by_cases valid : l.variableIndex < F.variableCount
  · have hm := MeasuredSelection.contains_cost
      (⟨l.variableIndex,valid⟩ : Fin F.variableCount) C.variableData
    have hi := MeasuredSelection.position_cost
      (⟨l.variableIndex,valid⟩ : Fin F.variableCount) C.variableData
    simp only [compactLiteral,dif_pos valid]
    cases (MeasuredSelection.contains
      (⟨l.variableIndex,valid⟩ : Fin F.variableCount) C.variableData).value <;>
      simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  · simp only [compactLiteral,dif_neg valid]
    omega

def compactClause {F : CNFFormula} (C : CutData F) (ls : List CNFLiteral) :
    Measured (List CNFLiteral) :=
  MeasuredSelection.filterMap (compactLiteral C) ls

theorem compactClause_value {F : CNFFormula} (C : CutData F) (ls : List CNFLiteral) :
    (compactClause C ls).value = C.compactClause ls := by
  simp only [compactClause,MeasuredSelection.filterMap_value,compactLiteral_value,
    NativeContext.CutData.compactClause]

theorem compactClause_cost {F : CNFFormula} (C : CutData F) (ls : List CNFLiteral) :
    (compactClause C ls).cost ≤ (4*C.variableData.length+7)*ls.length+1 := by
  have h := MeasuredSelection.filterMap_cost (compactLiteral C) ls
    (4*C.variableData.length+5) (compactLiteral_cost C)
  simpa only [compactClause,Nat.add_assoc] using h

theorem compactClause_length {F : CNFFormula} (C : CutData F) (ls : List CNFLiteral) :
    (compactClause C ls).value.length ≤ ls.length :=
  MeasuredSelection.filterMap_length (compactLiteral C) ls

def readAndCompact {F : CNFFormula} (C : CutData F) (i : Fin F.clauses.length) :
    Measured (List CNFLiteral) :=
  let original := MeasuredMatching.readClause F i
  let dense := compactClause C original.value
  ⟨dense.value,original.cost+dense.cost+1⟩

theorem readAndCompact_value {F : CNFFormula} (C : CutData F) (i : Fin F.clauses.length) :
    (readAndCompact C i).value = C.compactClause (CNFCore.clause F i) := by
  simp only [readAndCompact,compactClause_value,MeasuredMatching.readClause_value]

theorem readAndCompact_cost {F : CNFFormula} (C : CutData F)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) (i : Fin F.clauses.length) :
    (readAndCompact C i).cost ≤ 13*B+25 := by
  have hr := MeasuredMatching.readClause_cost F i
  have hc := compactClause_cost C (MeasuredMatching.readClause F i).value
  rw [MeasuredMatching.readClause_value] at hc
  have hv : C.variableData.length ≤ F.variableCount := by
    rw [C.variable_eq]
    exact CNFCore.variables_bound F
  have hp := Nat.mul_le_mul (show 4*C.variableData.length+7 ≤ 4*B+7 by omega) (shape i)
  simp only [readAndCompact,MeasuredMatching.readClause_value]
  omega

def denseClauses {F : CNFFormula} (C : CutData F) : Measured (List (List CNFLiteral)) :=
  MeasuredCollections.map (readAndCompact C) C.clauseData

theorem denseClauses_value {F : CNFFormula} (C : CutData F) :
    (denseClauses C).value = C.denseClauses := by
  simp only [denseClauses,MeasuredCollections.map_value,readAndCompact_value,
    NativeContext.CutData.denseClauses]

theorem denseClauses_cost {F : CNFFormula} (C : CutData F)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) :
    (denseClauses C).cost ≤ (13*B+27)*B+1 := by
  have hc : C.clauseData.length ≤ F.clauses.length := by
    rw [C.clause_eq,CNFCore.positions]
    simpa only [List.length_finRange] using
      (List.length_filter_le (CNFCore.kept F) (List.finRange F.clauses.length))
  have hm := MeasuredCollections.map_cost (readAndCompact C) C.clauseData
    (13*B+25) (readAndCompact_cost C shape B size)
  rw [show 13*B+25+2=13*B+27 by omega] at hm
  have hp := Nat.mul_le_mul_left (13*B+27) (show C.clauseData.length ≤ B by omega)
  exact Nat.le_trans hm (Nat.add_le_add_right hp 1)

/-- Construct the matching, retained families and dense literal data internally. -/
def prepare (F : CNFFormula) : Measured (Prepared F) :=
  let cut := MeasuredCut.prepare F
  let literals := denseClauses cut.value
  let data : Prepared F :=
    { toCutData := cut.value
      literals := literals.value
      literals_eq := (denseClauses_value cut.value).trans cut.value.denseClauses_eq }
  ⟨data,cut.cost+literals.cost+1⟩

theorem prepared_unique {F : CNFFormula} (C D : Prepared F) : C = D := by
  rcases C with ⟨cc,cl,hc⟩
  rcases D with ⟨dc,dl,hd⟩
  have ec := MeasuredCut.cutData_unique cc dc
  have el : cl = dl := hc.trans hd.symm
  cases ec
  cases el
  rfl

theorem prepare_value (F : CNFFormula) :
    (prepare F).value = NativeContext.prepare F :=
  prepared_unique _ _

def prepareBound (B : Nat) : Nat := MeasuredCut.cutBound B+(13*B+27)*B+2

theorem prepare_cost (F : CNFFormula)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) :
    (prepare F).cost ≤ prepareBound B := by
  have hc := MeasuredCut.prepare_cost F shape B size
  have hd := denseClauses_cost (MeasuredCut.prepare F).value shape B size
  simp only [prepare,prepareBound]
  omega

theorem decoded_prepare_cost (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (prepare (NativeTseitin.frontend F)).cost ≤ prepareBound (21*bits.length+9) := by
  have shape : ∀ i, (CNFCore.clause (NativeTseitin.frontend F) i).length ≤ 3 := by
    intro i
    exact Nat.le_of_eq
      (NativeTseitin.frontend_shape F _ (CNFCore.source_member (NativeTseitin.frontend F) i)).1
  have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
  exact prepare_cost (NativeTseitin.frontend F) shape (21*bits.length+9) (by omega)


end PNP.Concrete.NativeNormalization.MeasuredPrepared

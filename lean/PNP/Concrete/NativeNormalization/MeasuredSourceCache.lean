import PNP.Concrete.NativeNormalization.MeasuredCache

namespace PNP.Concrete.NativeNormalization.MeasuredSourceCache

open PNP.Concrete MeasuredReach NativeContext NativeSource NativeBasis MeasuredOperations

/-- Runtime dimensions come from stored lists. The canonical view below is for proofs only. -/
structure Built (F : CNFFormula) (three : ThreeCore F) where
  context : Prepared F
  columns : Nat
  rows : Nat
  columns_eq : columns = (CNFCore.variables F).length
  rows_eq : rows = (CNFCore.positions F).length
  data : MeasuredCache.Cache
    (NativeDimensionCache.transportSelection columns_eq.symm rows_eq.symm (context.rawSelection three))

def build (F : CNFFormula) (three : ThreeCore F) : Measured (Built F three) :=
  let C := MeasuredPrepared.prepare F
  let columns := MeasuredAccess.length C.value.variableData
  let rows := MeasuredAccess.length C.value.clauseData
  have hn : columns.value = (CNFCore.variables F).length :=
    (MeasuredAccess.length_value C.value.variableData).trans (congrArg List.length C.value.variable_eq)
  have hc : rows.value = (CNFCore.positions F).length :=
    (MeasuredAccess.length_value C.value.clauseData).trans (congrArg List.length C.value.clause_eq)
  let ops := MeasuredOperations.transport hn.symm hc.symm (MeasuredOperations.source C.value three)
  let cached := MeasuredCache.build ops
  ⟨⟨C.value,columns.value,rows.value,hn,hc,cached.value⟩,
    C.cost+columns.cost+rows.cost+cached.cost+1⟩

/-- Do not use this proof-facing view to replace the cached runtime dimensions. -/
def canonicalSelection {F : CNFFormula} {three : ThreeCore F} (b : Built F three) :
    Selection (CNFCore.variables F).length (CNFCore.positions F).length :=
  NativeDimensionCache.transportSelection b.columns_eq b.rows_eq (MeasuredCache.selection b.data)

theorem canonicalSelection_eq {F : CNFFormula} {three : ThreeCore F} (b : Built F three) :
    canonicalSelection b = selection F three := by
  unfold canonicalSelection
  rw [MeasuredCache.selection_eq]
  exact (MeasuredOperations.transport_roundtrip b.columns_eq.symm b.rows_eq.symm
    (b.context.rawSelection three)).trans (b.context.rawSelection_eq three)

theorem build_selection (F : CNFFormula) (three : ThreeCore F) :
    canonicalSelection (build F three).value = NativeSourceCache.cacheSelection (selection F three) := by
  rw [canonicalSelection_eq,NativeSourceCache.cacheSelection_eq]

theorem cached_operations_bounded {F : CNFFormula} {three : ThreeCore F} (b : Built F three)
    (B : Nat) (size : F.clauses.length+F.variableCount ≤ B) :
    Bounded (MeasuredCache.operations b.data) (B+1) B B B := by
  apply MeasuredCache.operations_bounded
  · rw [b.columns_eq]
    have h := CNFCore.variables_bound F
    omega
  · have h := MeasuredAccess.clauseData_bound b.context.toCutData
    rw [b.context.clause_eq] at h
    rw [b.rows_eq]
    omega

def selectionBound (B : Nat) : Nat :=
  MeasuredCache.cacheBound B (B+4) (MeasuredChoice.partnerBound B) (MeasuredChoice.slotBound B) (6*B+16)

def buildBound (B : Nat) : Nat := MeasuredPrepared.prepareBound B+selectionBound B+B+3

theorem build_cost (F : CNFFormula) (three : ThreeCore F)
    (shape : ∀ i, (CNFCore.clause F i).length ≤ 3) (B : Nat)
    (size : F.clauses.length+F.variableCount ≤ B) : (build F three).cost ≤ buildBound B := by
  let C := MeasuredPrepared.prepare F
  let columns := MeasuredAccess.length C.value.variableData
  let rows := MeasuredAccess.length C.value.clauseData
  have hn : columns.value = (CNFCore.variables F).length :=
    (MeasuredAccess.length_value C.value.variableData).trans (congrArg List.length C.value.variable_eq)
  have hc : rows.value = (CNFCore.positions F).length :=
    (MeasuredAccess.length_value C.value.clauseData).trans (congrArg List.length C.value.clause_eq)
  let ops := MeasuredOperations.transport hn.symm hc.symm (MeasuredOperations.source C.value three)
  have hp : C.cost ≤ MeasuredPrepared.prepareBound B :=
    MeasuredPrepared.prepare_cost F shape B size
  have hnc := MeasuredAccess.variableData_bound C.value.toCutData
  have hcc := MeasuredAccess.clauseData_bound C.value.toCutData
  have hnl := MeasuredAccess.length_cost C.value.variableData
  have hcl := MeasuredAccess.length_cost C.value.clauseData
  have ho := MeasuredOperations.transport_bounded hn.symm hc.symm
    (MeasuredOperations.source C.value three) (B+4)
    (MeasuredChoice.partnerBound B) (MeasuredChoice.slotBound B) (6*B+16)
    (MeasuredOperations.source_bounded C.value three B size)
  have hb := MeasuredCache.build_cost ops B (B+4)
    (MeasuredChoice.partnerBound B) (MeasuredChoice.slotBound B) (6*B+16)
    (by
      simp only [columns,MeasuredAccess.length_value]
      omega)
    (by
      simp only [rows,MeasuredAccess.length_value]
      omega) ho
  change C.cost+columns.cost+rows.cost+(MeasuredCache.build ops).cost+1 ≤ buildBound B
  simp only [buildBound,selectionBound,columns,rows]
  omega

/-- The source wrapper generates its own ThreeCore evidence after conversion. -/
def fromSource (F : CNFFormula) :
    Measured (Built (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)) :=
  build (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)

theorem fromSource_selection (F : CNFFormula) :
    canonicalSelection (fromSource F).value = NativeSourceCache.cacheSelection
      (selection (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)) :=
  build_selection _ _

theorem decoded_fromSource_cost (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (fromSource F).cost ≤ buildBound (21*bits.length+9) := by
  have shape : ∀ i, (CNFCore.clause (NativeTseitin.frontend F) i).length ≤ 3 := by
    intro i
    exact Nat.le_of_eq
      (NativeTseitin.frontend_shape F _ (CNFCore.source_member (NativeTseitin.frontend F) i)).1
  have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
  exact build_cost (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)
    shape (21*bits.length+9) (by omega)


end PNP.Concrete.NativeNormalization.MeasuredSourceCache

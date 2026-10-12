import PNP.Concrete.NativeNormalization.NativeSourceCache
import PNP.Concrete.NativeNormalization.MatchingCache

namespace PNP.Concrete.NativeNormalization.NativeContext

open PNP.Concrete CNFCore Matching NativeSource NativeBasis

/-- Stored source facts with equality proofs, constructed internally from the source. -/
structure CutData (F : CNFFormula) where
  matchingData : List (Option (Fin F.variableCount))
  matching_eq : matchingData = List.ofFn (matching F)
  nodeData : Trace (Vertex F.clauses.length F.variableCount)
  node_eq : nodeData = trace F
  clauseData : List (Fin F.clauses.length)
  clause_eq : clauseData = positions F
  variableData : List (Fin F.variableCount)
  variable_eq : variableData = variables F

def prepareCut (F : CNFFormula) : CutData F :=
  let m := (MatchingCache.fullTable (incidence F)).entries
  have hmList : m = List.ofFn (matching F) := MatchingCache.fullTable_entries (incidence F)
  let mFn := fun i : Fin F.clauses.length =>
    m[i.val]'(by rw [hmList, List.length_ofFn]; exact i.isLt)
  have hm : mFn = matching F := by
    funext i
    simp only [mFn, hmList, List.getElem_ofFn]
  let tr := scan (incidence F) mFn
  have ht : tr = trace F := by simp only [tr, hm, trace]
  let cs := (List.finRange F.clauses.length).filter
    (fun i => decide (Sum.inl i ∈ nodes tr))
  let vs := (List.finRange F.variableCount).filter
    (fun v => decide (Sum.inr v ∈ nodes tr))
  { matchingData := m
    matching_eq := hmList
    nodeData := tr
    node_eq := ht
    clauseData := cs
    clause_eq := by
      dsimp only [cs]
      rw [ht]
      rfl
    variableData := vs
    variable_eq := by
      dsimp only [vs]
      rw [ht]
      rfl }

def CutData.matchAt {F : CNFFormula} (C : CutData F)
    (i : Fin F.clauses.length) : Option (Fin F.variableCount) :=
  C.matchingData[i.val]'(by rw [C.matching_eq, List.length_ofFn]; exact i.isLt)

theorem CutData.matchAt_eq {F : CNFFormula} (C : CutData F)
    (i : Fin F.clauses.length) : C.matchAt i = matching F i := by
  simp [CutData.matchAt, C.matching_eq]

def CutData.atClause {F : CNFFormula} (C : CutData F)
    (i : Fin (positions F).length) : Fin F.clauses.length :=
  C.clauseData[i.val]'(by rw [C.clause_eq]; exact i.isLt)

theorem CutData.atClause_eq {F : CNFFormula} (C : CutData F)
    (i : Fin (positions F).length) : C.atClause i = CNFCore.atClause F i := by
  simp [CutData.atClause, C.clause_eq, CNFCore.atClause]

def CutData.atVariable {F : CNFFormula} (C : CutData F)
    (v : Fin (variables F).length) : Fin F.variableCount :=
  C.variableData[v.val]'(by rw [C.variable_eq]; exact v.isLt)

theorem CutData.atVariable_eq {F : CNFFormula} (C : CutData F)
    (v : Fin (variables F).length) : C.atVariable v = CNFCore.atVariable F v := by
  simp [CutData.atVariable, C.variable_eq, CNFCore.atVariable]

def CutData.compactLiteral {F : CNFFormula} (C : CutData F)
    (l : CNFLiteral) : Option CNFLiteral :=
  if h : l.variableIndex < F.variableCount then
    let v : Fin F.variableCount := ⟨l.variableIndex,h⟩
    if v ∈ C.variableData then some ⟨l.positive, C.variableData.idxOf v⟩ else none
  else none

theorem CutData.compactLiteral_eq {F : CNFFormula} (C : CutData F) (l : CNFLiteral) :
    C.compactLiteral l = CNFCore.compactLiteral F l := by
  simp [CutData.compactLiteral, CNFCore.compactLiteral, C.variable_eq, variables_mem]

def CutData.compactClause {F : CNFFormula} (C : CutData F)
    (ls : List CNFLiteral) : List CNFLiteral :=
  ls.filterMap C.compactLiteral

theorem CutData.compactClause_eq {F : CNFFormula} (C : CutData F) (ls : List CNFLiteral) :
    C.compactClause ls = CNFCore.compactClause F ls := by
  simp only [CutData.compactClause, CNFCore.compactClause]
  congr 1
  funext l
  exact C.compactLiteral_eq l

def CutData.denseClauses {F : CNFFormula} (C : CutData F) : List (List CNFLiteral) :=
  C.clauseData.map (fun i => C.compactClause (clause F i))

theorem CutData.denseClauses_eq {F : CNFFormula} (C : CutData F) :
    C.denseClauses = (compact F).clauses := by
  simp only [CutData.denseClauses, C.clause_eq, CutData.compactClause_eq, compact_clauses]

def CutData.transported {F : CNFFormula} (C : CutData F)
    (i : Fin (positions F).length) : Option (Fin (variables F).length) :=
  match hm : C.matchAt (C.atClause i) with
  | none => none
  | some v => some ⟨C.variableData.idxOf v, by
      rw [C.variable_eq]
      apply PNP.Concrete.NormalizerBlocks.ConstructiveLists.finiteIndexBound
      apply (variables_mem F v).mpr
      apply matched_inside F i v
      simpa only [CutData.matchAt_eq, CutData.atClause_eq] using hm⟩

theorem CutData.transported_eq {F : CNFFormula} (C : CutData F)
    (i : Fin (positions F).length) : C.transported i = CNFCore.transported F i := by
  unfold CutData.transported CNFCore.transported
  split
  · rename_i h
    have hh : matching F (CNFCore.atClause F i) = none := by
      simpa only [CutData.matchAt_eq, CutData.atClause_eq] using h
    split
    · rfl
    · rename_i v hv
      rw [hh] at hv
      cases hv
  · rename_i v h
    have hh : matching F (CNFCore.atClause F i) = some v := by
      simpa only [CutData.matchAt_eq, CutData.atClause_eq] using h
    split
    · rename_i hn
      rw [hh] at hn
      cases hn
    · rename_i u hu
      have eq : u = v := Option.some.inj (hu.symm.trans hh)
      subst u
      congr 1
      apply Fin.ext
      simp only [C.variable_eq, denseVariable]

def CutData.partner {F : CNFFormula} (C : CutData F)
    (v : Fin (variables F).length) : Fin (positions F).length :=
  match hm : owner C.matchAt (C.atVariable v) with
  | none => False.elim (core_owner_exists F v (by
      simpa only [CutData.atVariable_eq, show C.matchAt = matching F from
        funext C.matchAt_eq] using hm))
  | some i => ⟨C.clauseData.idxOf i, by
      rw [C.clause_eq]
      apply PNP.Concrete.NormalizerBlocks.ConstructiveLists.finiteIndexBound
      apply (positions_mem F i).mpr
      apply core_owner_kept F v i
      simpa only [CutData.atVariable_eq, show C.matchAt = matching F from
        funext C.matchAt_eq] using hm⟩

theorem CutData.partner_eq {F : CNFFormula} (C : CutData F)
    (v : Fin (variables F).length) : C.partner v = CNFCore.partner F v := by
  unfold CutData.partner CNFCore.partner
  split
  · rename_i h
    have hh : owner (matching F) (CNFCore.atVariable F v) = none := by
      simpa only [CutData.atVariable_eq, show C.matchAt = matching F from
        funext C.matchAt_eq] using h
    exact False.elim (core_owner_exists F v hh)
  · rename_i i h
    have hh : owner (matching F) (CNFCore.atVariable F v) = some i := by
      simpa only [CutData.atVariable_eq, show C.matchAt = matching F from
        funext C.matchAt_eq] using h
    split
    · rename_i hn
      exact False.elim (core_owner_exists F v hn)
    · rename_i j hj
      have eq : j = i := Option.some.inj (hj.symm.trans hh)
      subst j
      apply Fin.ext
      simp only [C.clause_eq, denseClause]

/-- Literal data is materialized once as well; getters never rebuild the compact core. -/
structure Prepared (F : CNFFormula) extends CutData F where
  literals : List (List CNFLiteral)
  literals_eq : literals = (compact F).clauses

def prepare (F : CNFFormula) : Prepared F :=
  let C := prepareCut F
  { toCutData := C
    literals := C.denseClauses
    literals_eq := C.denseClauses_eq }

def Prepared.denseLiterals {F : CNFFormula} (C : Prepared F)
    (i : Fin (positions F).length) : List CNFLiteral :=
  C.literals[i.val]'(by
    rw [C.literals_eq, compact_clauses, List.length_map]
    exact i.isLt)

theorem Prepared.denseLiterals_eq {F : CNFFormula} (C : Prepared F)
    (i : Fin (positions F).length) : C.denseLiterals i = CNFCore.denseLiterals F i := by
  simp only [Prepared.denseLiterals, C.literals_eq, denseLiterals_at]

def Prepared.literal {F : CNFFormula} (C : Prepared F) (three : ThreeCore F)
    (i : Fin (positions F).length) (s : Slot) : Literal (variables F).length :=
  let l := (C.denseLiterals i)[slotIndex s]'(by
    rw [C.denseLiterals_eq]
    exact slotIndex_lt F three i s)
  ⟨⟨l.variableIndex, by
    have he : l = originalLiteral F three i s := by
      simp only [l, Prepared.denseLiterals_eq, originalLiteral]
    rw [he]
    exact originalLiteral_bound F three i s⟩, l.positive⟩

theorem Prepared.literal_eq {F : CNFFormula} (C : Prepared F) (three : ThreeCore F)
    (i : Fin (positions F).length) (s : Slot) : C.literal three i s = NativeSource.literal F three i s := by
  simp only [Prepared.literal, Prepared.denseLiterals_eq, NativeSource.literal, originalLiteral]

def Prepared.rawSelection {F : CNFFormula} (C : Prepared F) (three : ThreeCore F) :
    Selection (variables F).length (positions F).length :=
  have hl : C.literal three = NativeSource.literal F three := by
    funext i s
    exact C.literal_eq three i s
  { literal := C.literal three
    owner := C.toCutData.partner
    slot := fun v => chooseSlot (C.literal three (C.toCutData.partner v)) v
    mode := fun i => (C.toCutData.transported i).map (chooseSlot (C.literal three i))
    ownerVariable := by
      intro v
      simp only [hl, CutData.partner_eq]
      exact (selection F three).ownerVariable v
    ownerMode := by
      intro v
      simp only [CutData.transported_eq, CutData.partner_eq, hl]
      exact (selection F three).ownerMode v }

theorem Prepared.rawSelection_eq {F : CNFFormula} (C : Prepared F) (three : ThreeCore F) :
    C.rawSelection three = selection F three := by
  have hl : C.literal three = NativeSource.literal F three := by
    funext i s
    exact C.literal_eq three i s
  have hp : C.toCutData.partner = partner F := funext C.toCutData.partner_eq
  have ht : C.toCutData.transported = transported F := funext C.toCutData.transported_eq
  simp only [Prepared.rawSelection, selection, hl, hp, ht]


def CutData.preferred {F : CNFFormula} (C : CutData F)
    (v : Fin F.variableCount) : Bool :=
  match owner C.matchAt v with
  | none => false
  | some i => ((occurrence F i v).map CNFLiteral.positive).getD false

theorem CutData.preferred_eq {F : CNFFormula} (C : CutData F)
    (v : Fin F.variableCount) : C.preferred v = CNFCore.preferred F v := by
  simp only [CutData.preferred, CNFCore.preferred,
    show C.matchAt = matching F from funext C.matchAt_eq]
  rfl

def CutData.projectValues {F : CNFFormula} (C : CutData F) (a : BitString) : BitString :=
  C.variableData.map (fun v => (assignmentAt a v.val).getD false)

theorem CutData.projectValues_eq {F : CNFFormula} (C : CutData F) (a : BitString) :
    C.projectValues a = CNFCore.projectValues F a := by
  simp only [CutData.projectValues, C.variable_eq, CNFCore.projectValues]

def CutData.recover {F : CNFFormula} (C : CutData F) (a : BitString) : BitString :=
  List.ofFn fun v : Fin F.variableCount =>
    if v ∈ C.variableData then (assignmentAt a (C.variableData.idxOf v)).getD false
    else C.preferred v

theorem CutData.recover_eq {F : CNFFormula} (C : CutData F) (a : BitString) :
    C.recover a = CNFCore.recover F a := by
  unfold CutData.recover CNFCore.recover CNFCore.lift
  apply congrArg List.ofFn
  funext v
  rw [C.variable_eq, C.preferred_eq]
  by_cases hv : inside F v = true
  · have hm := (variables_mem F v).mpr hv
    simp [liftValue, hv, hm, expandValues, assignmentAt_fn, v.isLt]
  · have hm : v ∉ variables F := fun h => hv ((variables_mem F v).mp h)
    simp [liftValue, hv, hm]



end PNP.Concrete.NativeNormalization.NativeContext

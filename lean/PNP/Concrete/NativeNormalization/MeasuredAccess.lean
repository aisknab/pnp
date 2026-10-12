import PNP.Concrete.NativeNormalization.MeasuredPreparedPolynomial

namespace PNP.Concrete.NativeNormalization.MeasuredAccess

open PNP.Concrete MeasuredReach NativeContext NativeSource NativeBasis

def length : List α → Measured Nat
  | [] => ⟨0,1⟩
  | _::xs => let tail := length xs; ⟨tail.value+1,tail.cost+1⟩

theorem length_value (xs : List α) : (length xs).value = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [length,ih]

theorem length_cost (xs : List α) : (length xs).cost = xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [length,ih]

/-- Explicit in-bounds list traversal, with no default value or unchecked access. -/
def get : (xs : List α) → (i : Nat) → i < xs.length → Measured α
  | [], i, h => False.elim (Nat.not_lt_zero i h)
  | a::_, 0, _ => ⟨a,1⟩
  | _::xs, i+1, h =>
      let tail := get xs i (Nat.lt_of_succ_lt_succ h)
      ⟨tail.value,tail.cost+1⟩

theorem get_value (xs : List α) (i : Nat) (h : i < xs.length) :
    (get xs i h).value = xs[i] := by
  induction xs generalizing i with
  | nil => simp at h
  | cons a xs ih =>
      cases i with
      | zero => rfl
      | succ i => simp only [get,List.getElem_cons_succ,ih]

theorem get_cost (xs : List α) (i : Nat) (h : i < xs.length) :
    (get xs i h).cost = i+1 := by
  induction xs generalizing i with
  | nil => simp at h
  | cons a xs ih =>
      cases i with
      | zero => rfl
      | succ i => simp only [get,ih]

theorem get_cost_le (xs : List α) (i : Nat) (h : i < xs.length) :
    (get xs i h).cost ≤ xs.length := by
  rw [get_cost]
  omega

theorem clauseData_bound {F : CNFFormula} (C : CutData F) :
    C.clauseData.length ≤ F.clauses.length := by
  rw [C.clause_eq,CNFCore.positions]
  simpa only [List.length_finRange] using
    (List.length_filter_le (CNFCore.kept F) (List.finRange F.clauses.length))

theorem variableData_bound {F : CNFFormula} (C : CutData F) :
    C.variableData.length ≤ F.variableCount := by
  rw [C.variable_eq]
  exact CNFCore.variables_bound F

def matchAt {F : CNFFormula} (C : CutData F) (i : Fin F.clauses.length) :
    Measured (Option (Fin F.variableCount)) :=
  get C.matchingData i.val (by rw [C.matching_eq,List.length_ofFn]; exact i.isLt)

theorem matchAt_value {F : CNFFormula} (C : CutData F) (i : Fin F.clauses.length) :
    (matchAt C i).value = C.matchAt i := by
  simp only [matchAt,get_value,NativeContext.CutData.matchAt]

theorem matchAt_cost {F : CNFFormula} (C : CutData F) (i : Fin F.clauses.length) :
    (matchAt C i).cost ≤ F.clauses.length := by
  simp only [matchAt,get_cost]
  exact i.isLt

def atClause {F : CNFFormula} (C : CutData F) (i : Fin (CNFCore.positions F).length) :
    Measured (Fin F.clauses.length) :=
  get C.clauseData i.val (by rw [C.clause_eq]; exact i.isLt)

theorem atClause_value {F : CNFFormula} (C : CutData F) (i : Fin (CNFCore.positions F).length) :
    (atClause C i).value = C.atClause i := by
  simp only [atClause,get_value,NativeContext.CutData.atClause]

theorem atClause_cost {F : CNFFormula} (C : CutData F) (i : Fin (CNFCore.positions F).length) :
    (atClause C i).cost ≤ F.clauses.length := by
  have h := get_cost_le C.clauseData i.val (by rw [C.clause_eq]; exact i.isLt)
  exact Nat.le_trans h (clauseData_bound C)

def atVariable {F : CNFFormula} (C : CutData F) (v : Fin (CNFCore.variables F).length) :
    Measured (Fin F.variableCount) :=
  get C.variableData v.val (by rw [C.variable_eq]; exact v.isLt)

theorem atVariable_value {F : CNFFormula} (C : CutData F) (v : Fin (CNFCore.variables F).length) :
    (atVariable C v).value = C.atVariable v := by
  simp only [atVariable,get_value,NativeContext.CutData.atVariable]

theorem atVariable_cost {F : CNFFormula} (C : CutData F) (v : Fin (CNFCore.variables F).length) :
    (atVariable C v).cost ≤ F.variableCount := by
  have h := get_cost_le C.variableData v.val (by rw [C.variable_eq]; exact v.isLt)
  exact Nat.le_trans h (variableData_bound C)

def table {F : CNFFormula} (C : CutData F) :
    MatchingCache.Table F.clauses.length F.variableCount :=
  ⟨C.matchingData,by rw [C.matching_eq,List.length_ofFn]⟩

theorem table_get {F : CNFFormula} (C : CutData F) :
    (table C).get = C.matchAt := by
  funext i
  rfl

def denseLiterals {F : CNFFormula} (C : Prepared F) (i : Fin (CNFCore.positions F).length) :
    Measured (List CNFLiteral) :=
  get C.literals i.val (by
    rw [C.literals_eq,CNFCore.compact_clauses,List.length_map]
    exact i.isLt)

theorem denseLiterals_value {F : CNFFormula} (C : Prepared F)
    (i : Fin (CNFCore.positions F).length) :
    (denseLiterals C i).value = C.denseLiterals i := by
  simp only [denseLiterals,get_value,NativeContext.Prepared.denseLiterals]

theorem denseLiterals_cost {F : CNFFormula} (C : Prepared F)
    (i : Fin (CNFCore.positions F).length) :
    (denseLiterals C i).cost ≤ F.clauses.length := by
  have h := clauseData_bound C.toCutData
  have hi : i.val < C.clauseData.length := by rw [C.clause_eq]; exact i.isLt
  simp only [denseLiterals,get_cost]
  omega

def literal {F : CNFFormula} (C : Prepared F) (three : ThreeCore F)
    (i : Fin (CNFCore.positions F).length) (s : Slot) :
    Measured (Literal (CNFCore.variables F).length) :=
  let ls := denseLiterals C i
  let l := get ls.value (slotIndex s) (by
    simp only [ls,denseLiterals_value,NativeContext.Prepared.denseLiterals_eq]
    exact slotIndex_lt F three i s)
  ⟨⟨⟨l.value.variableIndex,by
      have he : l.value = originalLiteral F three i s := by
        simp only [l,get_value,ls,denseLiterals_value,
          NativeContext.Prepared.denseLiterals_eq,originalLiteral]
      rw [he]
      exact originalLiteral_bound F three i s⟩,l.value.positive⟩,
    ls.cost+l.cost+1⟩

theorem literal_value {F : CNFFormula} (C : Prepared F) (three : ThreeCore F)
    (i : Fin (CNFCore.positions F).length) (s : Slot) :
    (literal C three i s).value = C.literal three i s := by
  simp only [literal,get_value,denseLiterals_value,NativeContext.Prepared.literal]

theorem literal_cost {F : CNFFormula} (C : Prepared F) (three : ThreeCore F)
    (i : Fin (CNFCore.positions F).length) (s : Slot) :
    (literal C three i s).cost ≤ F.clauses.length+4 := by
  have hd := denseLiterals_cost C i
  have hs : slotIndex s ≤ 2 := by cases s <;> decide
  simp only [literal,get_cost]
  omega


end PNP.Concrete.NativeNormalization.MeasuredAccess

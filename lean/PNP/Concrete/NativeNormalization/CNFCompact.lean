import PNP.Concrete.NativeNormalization.CNFCore

namespace PNP.Concrete.NativeNormalization.CNFCore

open PNP.Concrete Matching

/-- The actual reachable variables, not the source's unused declared positions. -/
def variables (F : CNFFormula) : List (Fin F.variableCount) :=
  (List.finRange F.variableCount).filter (inside F)

@[simp] theorem variables_mem (F : CNFFormula) (v : Fin F.variableCount) :
    v ∈ variables F ↔ inside F v = true := by simp [variables]

theorem variables_nodup (F : CNFFormula) : (variables F).Nodup :=
  (finRange_nodup F.variableCount).filter _

theorem variables_bound (F : CNFFormula) : (variables F).length ≤ F.variableCount := by
  have h := List.length_filter_le (inside F) (List.finRange F.variableCount)
  simpa [variables] using h

theorem lookup_idxOf {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (h : x ∈ xs) : xs[xs.idxOf x]? = some x := by
  exact PNP.Concrete.NormalizerBlocks.ConstructiveLists.lookup xs x h

/-- Invalid source literals are false and disappear; valid core indices are dense. -/
def compactLiteral (F : CNFFormula) (l : CNFLiteral) : Option CNFLiteral :=
  if h : l.variableIndex < F.variableCount then
    let v : Fin F.variableCount := ⟨l.variableIndex,h⟩
    if inside F v then some ⟨l.positive, (variables F).idxOf v⟩ else none
  else none

def compactClause (F : CNFFormula) (ls : List CNFLiteral) : List CNFLiteral :=
  ls.filterMap (compactLiteral F)

def compact (F : CNFFormula) : CNFFormula :=
  { variableCount := (variables F).length
    clauses := (residual F).clauses.map (compactClause F) }

def projectValues (F : CNFFormula) (a : BitString) : BitString :=
  (variables F).map fun v => (assignmentAt a v.val).getD false

def expandValues (F : CNFFormula) (a : BitString) : BitString :=
  List.ofFn fun v : Fin F.variableCount =>
    (assignmentAt a ((variables F).idxOf v)).getD false

def recover (F : CNFFormula) (a : BitString) : BitString :=
  lift F (expandValues F a)

theorem compactLiteral_of_inside (F : CNFFormula) (l : CNFLiteral)
    (h : l.variableIndex < F.variableCount)
    (hv : inside F ⟨l.variableIndex,h⟩ = true) :
    compactLiteral F l = some ⟨l.positive,
      (variables F).idxOf (⟨l.variableIndex,h⟩ : Fin F.variableCount)⟩ := by
  simp [compactLiteral, h, hv]

theorem compactLiteral_some (F : CNFFormula) (l k : CNFLiteral)
    (h : compactLiteral F l = some k) :
    ∃ v : Fin F.variableCount,
      l.variableIndex = v.val ∧ inside F v = true ∧
      k.positive = l.positive ∧ k.variableIndex = (variables F).idxOf v := by
  unfold compactLiteral at h
  split at h
  · rename_i valid
    dsimp only at h
    split at h
    · rename_i active
      cases h
      exact ⟨⟨l.variableIndex,valid⟩, rfl, active, rfl, rfl⟩
    · cases h
  · cases h

theorem compactLiteral_bound (F : CNFFormula) (l k : CNFLiteral)
    (h : compactLiteral F l = some k) : k.variableIndex < (compact F).variableCount := by
  obtain ⟨v, _, hv, _, hk⟩ := compactLiteral_some F l k h
  rw [hk]
  exact PNP.Concrete.NormalizerBlocks.ConstructiveLists.finiteIndexBound _ _ ((variables_mem F v).mpr hv)

theorem project_lookup (F : CNFFormula) (a : BitString)
    (v : Fin F.variableCount) (hv : inside F v = true) :
    assignmentAt (projectValues F a) ((variables F).idxOf v) =
      some ((assignmentAt a v.val).getD false) := by
  rw [assignmentAt_get]
  unfold projectValues
  rw [List.getElem?_map, lookup_idxOf _ _ ((variables_mem F v).mpr hv)]
  rfl

theorem compact_kept_clause (F : CNFFormula) (a : BitString)
    (width : a.length = F.variableCount) (i : Fin F.clauses.length)
    (hi : kept F i = true) (h : ClauseSatisfied (clause F i) a) :
    ClauseSatisfied (compactClause F (clause F i)) (projectValues F a) := by
  obtain ⟨l, mem, hl⟩ := (clauseSatisfied_iff _ _).mp h
  have hb : l.variableIndex < F.variableCount := by
    rw [← width]
    exact assignmentAt_bound a l.variableIndex l.positive hl
  let v : Fin F.variableCount := ⟨l.variableIndex,hb⟩
  have hv := kept_neighbor_inside F i v hi (incidence_of_mem F i v l mem rfl)
  let k : CNFLiteral := ⟨l.positive, (variables F).idxOf v⟩
  have hk : compactLiteral F l = some k := compactLiteral_of_inside F l hb hv
  refine (clauseSatisfied_iff _ _).mpr ⟨k, List.mem_filterMap.mpr ⟨l,mem,hk⟩, ?_⟩
  change assignmentAt (projectValues F a) ((variables F).idxOf v) = some l.positive
  rw [project_lookup F a v hv]
  have ha : assignmentAt a v.val = some l.positive := hl
  simp [ha]

theorem compact_project_satisfied (F : CNFFormula) (a : BitString)
    (h : F.Satisfied a) : (compact F).Satisfied (projectValues F a) := by
  refine ⟨by simp [projectValues, compact], (clausesSatisfied_iff _ _).mpr ?_⟩
  intro ls mem
  obtain ⟨cs, hcs, eq⟩ := List.mem_map.mp mem
  obtain ⟨i, hi, ci⟩ := (residual_member F cs).mp hcs
  rw [← eq, ← ci]
  exact compact_kept_clause F a h.1 i hi
    ((clausesSatisfied_iff _ _).mp h.2 _ (source_member F i))

theorem compact_clause_expand (F : CNFFormula) (a : BitString)
    (ls : List CNFLiteral) (h : ClauseSatisfied (compactClause F ls) a) :
    ClauseSatisfied ls (expandValues F a) := by
  obtain ⟨k, mem, hk⟩ := (clauseSatisfied_iff _ _).mp h
  obtain ⟨l, ml, hl⟩ := List.mem_filterMap.mp mem
  obtain ⟨v, idx, _, sign, ki⟩ := compactLiteral_some F l k hl
  refine (clauseSatisfied_iff _ _).mpr ⟨l, ml, ?_⟩
  change assignmentAt (expandValues F a) l.variableIndex = some l.positive
  unfold expandValues
  rw [idx, assignmentAt_fn]
  have ha : assignmentAt a ((variables F).idxOf v) = some l.positive := by
    simpa only [LiteralSatisfied, ki, sign] using hk
  simp [v.isLt, ha]

theorem compact_expand_satisfied (F : CNFFormula) (a : BitString)
    (h : (compact F).Satisfied a) :
    (residual F).Satisfied (expandValues F a) := by
  refine ⟨by simp [expandValues, residual], (clausesSatisfied_iff _ _).mpr ?_⟩
  intro ls mem
  apply compact_clause_expand F a ls
  exact (clausesSatisfied_iff _ _).mp h.2 _
    (List.mem_map.mpr ⟨ls,mem,rfl⟩)

theorem recover_satisfied (F : CNFFormula) (a : BitString)
    (h : (compact F).Satisfied a) : F.Satisfied (recover F a) :=
  lift_satisfied F _ (compact_expand_satisfied F a h)

/-- The complete compact-core semantic interface has only the source as input. -/
theorem compact_satisfiable_iff (F : CNFFormula) :
    F.Satisfiable ↔ (compact F).Satisfiable := by
  constructor
  · rintro ⟨a,h⟩
    exact ⟨projectValues F a, compact_project_satisfied F a h⟩
  · rintro ⟨a,h⟩
    exact ⟨recover F a, recover_satisfied F a h⟩

/-- Every retained compact variable has an actual matched kept clause. -/
theorem variables_matched (F : CNFFormula) (v : Fin F.variableCount)
    (mem : v ∈ variables F) :
    ∃ i : Fin F.clauses.length, matching F i = some v ∧ kept F i = true := by
  have hv := (inside_iff F v).mp ((variables_mem F v).mp mem)
  obtain ⟨i, hm, hi⟩ := (terminal_cut F).2.2.1 v hv
  exact ⟨i, hm, (kept_iff F i).mpr hi⟩

theorem compact_wellformed (F : CNFFormula) :
    ∀ ls ∈ (compact F).clauses, ∀ l ∈ ls, l.variableIndex < (compact F).variableCount := by
  intro ls mem l ml
  obtain ⟨cs, _, eq⟩ := List.mem_map.mp mem
  rw [← eq] at ml
  obtain ⟨original, _, h⟩ := List.mem_filterMap.mp ml
  exact compactLiteral_bound F original l h

/-- The dense source width fits the actual encoded input, not a numeric-ID assumption. -/
theorem compact_decoded_width_bound (bits : BitString) (F : CNFFormula)
    (h : decodeEncodedCNF bits = some F) : (compact F).variableCount ≤ bits.length :=
  Nat.le_trans (variables_bound F) (decoded_width_bound bits F h)


end PNP.Concrete.NativeNormalization.CNFCore

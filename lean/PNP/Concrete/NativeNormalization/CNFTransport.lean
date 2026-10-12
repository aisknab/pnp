import PNP.Concrete.NativeNormalization.CNFCompact

namespace PNP.Concrete.NativeNormalization.CNFCore

open PNP.Concrete Matching

/-- Stable source positions, not a set of clause values. -/
def positions (F : CNFFormula) : List (Fin F.clauses.length) :=
  (List.finRange F.clauses.length).filter (kept F)

def atClause (F : CNFFormula) (i : Fin (positions F).length) :
    Fin F.clauses.length := (positions F)[i.val]

def atVariable (F : CNFFormula) (v : Fin (variables F).length) :
    Fin F.variableCount := (variables F)[v.val]

@[simp] theorem positions_mem (F : CNFFormula) (i : Fin F.clauses.length) :
    i ∈ positions F ↔ kept F i = true := by simp [positions]

theorem positions_nodup (F : CNFFormula) : (positions F).Nodup :=
  (finRange_nodup F.clauses.length).filter _

theorem atClause_kept (F : CNFFormula) (i : Fin (positions F).length) :
    kept F (atClause F i) = true :=
  (positions_mem F _).mp (List.getElem_mem i.isLt)

theorem atVariable_inside (F : CNFFormula) (v : Fin (variables F).length) :
    inside F (atVariable F v) = true :=
  (variables_mem F _).mp (List.getElem_mem v.isLt)

theorem atClause_injective (F : CNFFormula) (i j : Fin (positions F).length)
    (h : atClause F i = atClause F j) : i = j := by
  exact Fin.ext ((List.getElem_inj (positions_nodup F)).mp h)

theorem atVariable_injective (F : CNFFormula) (i j : Fin (variables F).length)
    (h : atVariable F i = atVariable F j) : i = j := by
  exact Fin.ext ((List.getElem_inj (variables_nodup F)).mp h)

def denseClause (F : CNFFormula) (i : Fin F.clauses.length)
    (hi : kept F i = true) : Fin (positions F).length :=
  ⟨(positions F).idxOf i, PNP.Concrete.NormalizerBlocks.ConstructiveLists.finiteIndexBound _ _ ((positions_mem F i).mpr hi)⟩

def denseVariable (F : CNFFormula) (v : Fin F.variableCount)
    (hv : inside F v = true) : Fin (variables F).length :=
  ⟨(variables F).idxOf v, PNP.Concrete.NormalizerBlocks.ConstructiveLists.finiteIndexBound _ _ ((variables_mem F v).mpr hv)⟩

theorem get_idxOf {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (h : x ∈ xs) :
    xs[xs.idxOf x]'(List.idxOf_lt_length_of_mem h) = x := by
  have hx := lookup_idxOf xs x h
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h)] at hx
  exact Option.some.inj hx

theorem at_denseClause (F : CNFFormula) (i : Fin F.clauses.length)
    (hi : kept F i = true) : atClause F (denseClause F i hi) = i :=
  get_idxOf _ _ ((positions_mem F i).mpr hi)

theorem at_denseVariable (F : CNFFormula) (v : Fin F.variableCount)
    (hv : inside F v = true) : atVariable F (denseVariable F v hv) = v :=
  get_idxOf _ _ ((variables_mem F v).mpr hv)

theorem matched_inside (F : CNFFormula) (i : Fin (positions F).length)
    (v : Fin F.variableCount) (hm : matching F (atClause F i) = some v) :
    inside F v = true :=
  kept_neighbor_inside F _ v (atClause_kept F i) ((matching_valid F).incident _ v hm)

/-- A genuine matching on the retained clause and variable coordinates. -/
def transported (F : CNFFormula) (i : Fin (positions F).length) :
    Option (Fin (variables F).length) :=
  match hm : matching F (atClause F i) with
  | none => none
  | some v => some (denseVariable F v (matched_inside F i v hm))

theorem transported_some_original (F : CNFFormula) (i : Fin (positions F).length)
    (v : Fin (variables F).length) (h : transported F i = some v) :
    matching F (atClause F i) = some (atVariable F v) := by
  unfold transported at h
  split at h
  · cases h
  · rename_i u hu
    cases h
    rw [at_denseVariable]
    exact hu

theorem transported_original_some (F : CNFFormula) (i : Fin (positions F).length)
    (v : Fin (variables F).length)
    (h : matching F (atClause F i) = some (atVariable F v)) :
    transported F i = some v := by
  unfold transported
  split
  · rename_i hn
    rw [h] at hn
    cases hn
  · rename_i u hu
    have eq : u = atVariable F v := Option.some.inj (hu.symm.trans h)
    congr 1
    apply atVariable_injective
    rw [at_denseVariable, eq]

theorem transported_injective (F : CNFFormula)
    (i j : Fin (positions F).length) (v : Fin (variables F).length)
    (hi : transported F i = some v) (hj : transported F j = some v) : i = j := by
  apply atClause_injective
  exact (matching_valid F).injective _ _ _ (transported_some_original F i v hi)
    (transported_some_original F j v hj)

theorem core_owner_kept (F : CNFFormula) (v : Fin (variables F).length)
    (i : Fin F.clauses.length) (h : owner (matching F) (atVariable F v) = some i) :
    kept F i = true := by
  have hm := owner_some (matching F) (atVariable F v) h
  exact (kept_iff F i).mpr (((terminal_cut F).2.2.2.1 i (atVariable F v) hm).mpr
    ((inside_iff F _).mp (atVariable_inside F v)))

theorem core_owner_exists (F : CNFFormula) (v : Fin (variables F).length) :
    owner (matching F) (atVariable F v) ≠ none := by
  obtain ⟨i, hm, _⟩ := variables_matched F (atVariable F v) (List.getElem_mem v.isLt)
  rw [owner_of_matched F i _ hm]
  intro h
  cases h

/-- Every retained variable's actual matching partner, computed without choice. -/
def partner (F : CNFFormula) (v : Fin (variables F).length) :
    Fin (positions F).length :=
  match h : owner (matching F) (atVariable F v) with
  | none => False.elim (core_owner_exists F v h)
  | some i => denseClause F i (core_owner_kept F v i h)

theorem partner_correct (F : CNFFormula) (v : Fin (variables F).length) :
    transported F (partner F v) = some v := by
  apply transported_original_some
  unfold partner
  split
  · rename_i h
    exact False.elim (core_owner_exists F v h)
  · rename_i i hi
    rw [at_denseClause]
    exact owner_some (matching F) (atVariable F v) hi

theorem partner_injective (F : CNFFormula) (v w : Fin (variables F).length)
    (h : partner F v = partner F w) : v = w := by
  have hv := partner_correct F v
  rw [h, partner_correct F w] at hv
  exact (Option.some.inj hv).symm

theorem partner_of_transported (F : CNFFormula) (i : Fin (positions F).length)
    (v : Fin (variables F).length) (h : transported F i = some v) :
    partner F v = i :=
  transported_injective F _ _ v (partner_correct F v) h

def denseLiterals (F : CNFFormula) (i : Fin (positions F).length) : List CNFLiteral :=
  compactClause F (clause F (atClause F i))

theorem compact_clauses (F : CNFFormula) :
    (compact F).clauses =
      (positions F).map (fun i => compactClause F (clause F i)) := by
  simp [compact, residual, positions, List.map_map]

theorem denseLiterals_at (F : CNFFormula) (i : Fin (positions F).length) :
    (compact F).clauses[i.val]'(by rw [compact_clauses, List.length_map]; exact i.isLt) =
      denseLiterals F i := by
  simp [compact_clauses, denseLiterals, atClause]

/-- Incidence and sign come from an actual occurrence surviving compaction. -/
theorem transported_occurrence (F : CNFFormula) (i : Fin (positions F).length)
    (v : Fin (variables F).length) (h : transported F i = some v) :
    ∃ l, l ∈ denseLiterals F i ∧ l.variableIndex = v.val ∧
      l.positive = preferred F (atVariable F v) := by
  have hm := transported_some_original F i v h
  obtain ⟨l, mem, idx, sign⟩ := preferred_witness F (atClause F i) (atVariable F v) hm
  have valid : l.variableIndex < F.variableCount := by rw [idx]; exact (atVariable F v).isLt
  let u : Fin F.variableCount := ⟨l.variableIndex,valid⟩
  have eu : u = atVariable F v := Fin.ext idx
  have active : inside F u = true := by rw [eu]; exact atVariable_inside F v
  let k : CNFLiteral := ⟨l.positive,(variables F).idxOf u⟩
  have hk : compactLiteral F l = some k := compactLiteral_of_inside F l valid active
  refine ⟨k, List.mem_filterMap.mpr ⟨l,mem,hk⟩, ?_, ?_⟩
  · have den : denseVariable F u active = v := by
      apply atVariable_injective
      rw [at_denseVariable, eu]
    exact congrArg Fin.val den
  · exact sign.symm

/-- No list-value deduplication is used, even for identical clauses. -/
theorem dense_positions_length (F : CNFFormula) :
    (compact F).clauses.length = (positions F).length := by
  rw [compact_clauses, List.length_map]


end PNP.Concrete.NativeNormalization.CNFCore

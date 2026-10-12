import PNP.Concrete.NativeNormalization.MatchingUpdate
import PNP.Concrete.CNF

namespace PNP.Concrete.NativeNormalization.CNFCore

open PNP.Concrete Matching

/-- Actual source clauses, retaining their positions even when equal. -/
def clause (F : CNFFormula) (i : Fin F.clauses.length) : List CNFLiteral :=
  F.clauses[i.val]

/-- Only actual valid-width occurrences are graph edges. -/
def occurrence (F : CNFFormula) (i : Fin F.clauses.length)
    (v : Fin F.variableCount) : Option CNFLiteral :=
  (clause F i).find? fun l => l.variableIndex == v.val

def incidence (F : CNFFormula) (i : Fin F.clauses.length)
    (v : Fin F.variableCount) : Bool :=
  (occurrence F i v).isSome

def matching (F : CNFFormula) := fullMatching (incidence F)
def trace (F : CNFFormula) := scan (incidence F) (matching F)

def kept (F : CNFFormula) (i : Fin F.clauses.length) : Bool :=
  decide (Sum.inl i ∈ nodes (trace F))

def inside (F : CNFFormula) (v : Fin F.variableCount) : Bool :=
  decide (Sum.inr v ∈ nodes (trace F))

@[simp] theorem kept_iff (F : CNFFormula) (i : Fin F.clauses.length) :
    kept F i = true ↔ Sum.inl i ∈ nodes (trace F) := by simp [kept]

@[simp] theorem inside_iff (F : CNFFormula) (v : Fin F.variableCount) :
    inside F v = true ↔ Sum.inr v ∈ nodes (trace F) := by simp [inside]

theorem matching_valid (F : CNFFormula) : IsMatching (incidence F) (matching F) :=
  (fullMatching_valid_terminal (incidence F)).1

theorem terminal_cut (F : CNFFormula) :
    Cut (incidence F) (matching F) (trace F) := fullMatching_cut (incidence F)

theorem occurrence_some (F : CNFFormula) (i : Fin F.clauses.length)
    (v : Fin F.variableCount) (l : CNFLiteral)
    (h : occurrence F i v = some l) :
    l ∈ clause F i ∧ l.variableIndex = v.val := by
  exact ⟨List.mem_of_find?_eq_some h, by
    have := List.find?_some (p := fun l : CNFLiteral => l.variableIndex == v.val) h
    simpa using this⟩

theorem incidence_of_mem (F : CNFFormula) (i : Fin F.clauses.length)
    (v : Fin F.variableCount) (l : CNFLiteral)
    (mem : l ∈ clause F i) (eq : l.variableIndex = v.val) :
    incidence F i v = true := by
  cases h : occurrence F i v with
  | none =>
      have no := (List.find?_eq_none.mp h) l mem
      have present : (l.variableIndex == v.val) = true := by
        change decide (l.variableIndex = v.val) = true
        exact decide_eq_true eq
      exact False.elim (no present)
  | some found => simp [incidence, h]

theorem incidence_witness (F : CNFFormula) (i : Fin F.clauses.length)
    (v : Fin F.variableCount) (h : incidence F i v = true) :
    ∃ l, occurrence F i v = some l := by
  cases found : occurrence F i v with
  | none => simp [incidence, found] at h
  | some l => exact ⟨l, rfl⟩

theorem kept_neighbor_inside (F : CNFFormula) (i : Fin F.clauses.length)
    (v : Fin F.variableCount) (hi : kept F i = true)
    (edge : incidence F i v = true) : inside F v = true := by
  exact (inside_iff F v).mpr ((terminal_cut F).2.1 i v ((kept_iff F i).mp hi) edge)

theorem outside_matched (F : CNFFormula) (i : Fin F.clauses.length)
    (hi : kept F i ≠ true) :
    ∃ v, matching F i = some v ∧ inside F v ≠ true := by
  have hn : Sum.inl i ∉ nodes (trace F) := fun h => hi ((kept_iff F i).mpr h)
  obtain ⟨v, hm, hv⟩ := (terminal_cut F).2.2.2.2 i hn
  exact ⟨v, hm, fun h => hv ((inside_iff F v).mp h)⟩

theorem owner_of_matched (F : CNFFormula) (i : Fin F.clauses.length)
    (v : Fin F.variableCount) (hm : matching F i = some v) :
    owner (matching F) v = some i := by
  cases h : owner (matching F) v with
  | none => exact False.elim (((owner_none (matching F) v).mp h) i hm)
  | some j =>
      have hj := owner_some (matching F) v h
      have eq := (matching_valid F).injective j i v hj hm
      subst j
      rfl

/-- A sign from an actual matched occurrence; false is used only off the matching. -/
def preferred (F : CNFFormula) (v : Fin F.variableCount) : Bool :=
  match owner (matching F) v with
  | none => false
  | some i => ((occurrence F i v).map CNFLiteral.positive).getD false

theorem preferred_witness (F : CNFFormula) (i : Fin F.clauses.length)
    (v : Fin F.variableCount) (hm : matching F i = some v) :
    ∃ l, l ∈ clause F i ∧ l.variableIndex = v.val ∧ preferred F v = l.positive := by
  obtain ⟨l, hl⟩ := incidence_witness F i v ((matching_valid F).incident i v hm)
  obtain ⟨mem, idx⟩ := occurrence_some F i v l hl
  refine ⟨l, mem, idx, ?_⟩
  simp [preferred, owner_of_matched F i v hm, hl]

/-- The retained clauses use the original variable numbering and width. -/
def residual (F : CNFFormula) : CNFFormula :=
  { variableCount := F.variableCount
    clauses := ((List.finRange F.clauses.length).filter (kept F)).map (clause F) }

/-- Preserve core values, complete every outside clause through its distinct matched variable. -/
def liftValue (F : CNFFormula) (a : BitString) (v : Fin F.variableCount) : Bool :=
  if inside F v then (assignmentAt a v.val).getD false else preferred F v

def lift (F : CNFFormula) (a : BitString) : BitString := List.ofFn (liftValue F a)

def candidate (F : CNFFormula) : BitString := List.ofFn (preferred F)

theorem assignmentAt_get (a : BitString) (k : Nat) :
    assignmentAt a k = a[k]? := by
  induction a generalizing k with
  | nil => simp [assignmentAt]
  | cons b a ih =>
      cases k with
      | zero => rfl
      | succ k => simpa [assignmentAt] using ih k

theorem assignmentAt_fn {n : Nat} (f : Fin n → Bool) (k : Nat) :
    assignmentAt (List.ofFn f) k = if h : k < n then some (f ⟨k,h⟩) else none := by
  rw [assignmentAt_get, List.getElem?_ofFn]

theorem assignmentAt_bound (a : BitString) (k : Nat) (b : Bool)
    (h : assignmentAt a k = some b) : k < a.length := by
  induction a generalizing k with
  | nil => simp [assignmentAt] at h
  | cons x a ih =>
      cases k with
      | zero => simp
      | succ k =>
          have hk := ih k h
          simpa using Nat.succ_lt_succ hk

theorem clauseSatisfied_iff (ls : List CNFLiteral) (a : BitString) :
    ClauseSatisfied ls a ↔ ∃ l, l ∈ ls ∧ LiteralSatisfied l a := by
  induction ls with
  | nil => simp [ClauseSatisfied]
  | cons l ls ih => simp [ClauseSatisfied, ih, or_and_right, exists_or]

theorem clausesSatisfied_iff (ls : List (List CNFLiteral)) (a : BitString) :
    ClausesSatisfied ls a ↔ ∀ l ∈ ls, ClauseSatisfied l a := by
  induction ls with
  | nil => simp [ClausesSatisfied]
  | cons l ls ih => simp [ClausesSatisfied, ih]

theorem source_member (F : CNFFormula) (i : Fin F.clauses.length) :
    clause F i ∈ F.clauses := List.getElem_mem i.isLt

theorem source_index (F : CNFFormula) (ls : List CNFLiteral) (h : ls ∈ F.clauses) :
    ∃ i : Fin F.clauses.length, clause F i = ls := by
  obtain ⟨k, hk, eq⟩ := List.mem_iff_getElem.mp h
  exact ⟨⟨k,hk⟩, eq⟩

theorem residual_member (F : CNFFormula) (ls : List CNFLiteral) :
    ls ∈ (residual F).clauses ↔
      ∃ i : Fin F.clauses.length, kept F i = true ∧ clause F i = ls := by
  simp [residual, List.mem_map, List.mem_filter]

theorem project_satisfied (F : CNFFormula) (a : BitString)
    (h : F.Satisfied a) : (residual F).Satisfied a := by
  refine ⟨h.1, (clausesSatisfied_iff _ _).mpr ?_⟩
  intro ls mem
  obtain ⟨i, _, eq⟩ := (residual_member F ls).mp mem
  rw [← eq]
  exact (clausesSatisfied_iff _ _).mp h.2 _ (source_member F i)

theorem lift_kept_clause (F : CNFFormula) (a : BitString)
    (width : a.length = F.variableCount) (i : Fin F.clauses.length)
    (hi : kept F i = true) (sat : ClauseSatisfied (clause F i) a) :
    ClauseSatisfied (clause F i) (lift F a) := by
  obtain ⟨l, mem, hs⟩ := (clauseSatisfied_iff _ _).mp sat
  have hb : l.variableIndex < F.variableCount := by
    rw [← width]
    exact assignmentAt_bound a l.variableIndex l.positive hs
  let v : Fin F.variableCount := ⟨l.variableIndex,hb⟩
  have hv := kept_neighbor_inside F i v hi (incidence_of_mem F i v l mem rfl)
  refine (clauseSatisfied_iff _ _).mpr ⟨l, mem, ?_⟩
  change assignmentAt (List.ofFn (liftValue F a)) l.variableIndex = some l.positive
  rw [assignmentAt_fn]
  have hav : assignmentAt a v.val = some l.positive := hs
  simpa only [dif_pos hb] using
    congrArg some (show liftValue F a v = l.positive by simp [liftValue, hv, hav])

theorem lift_outside_clause (F : CNFFormula) (a : BitString)
    (i : Fin F.clauses.length) (hi : kept F i ≠ true) :
    ClauseSatisfied (clause F i) (lift F a) := by
  obtain ⟨v, hm, hv⟩ := outside_matched F i hi
  obtain ⟨l, mem, idx, sign⟩ := preferred_witness F i v hm
  refine (clauseSatisfied_iff _ _).mpr ⟨l, mem, ?_⟩
  change assignmentAt (List.ofFn (liftValue F a)) l.variableIndex = some l.positive
  rw [idx, assignmentAt_fn]
  simp [v.isLt, liftValue, hv, sign]

/-- No matching, cut, family, path or correctness certificate is supplied. -/
theorem lift_satisfied (F : CNFFormula) (a : BitString)
    (h : (residual F).Satisfied a) : F.Satisfied (lift F a) := by
  refine ⟨by simp [lift], (clausesSatisfied_iff _ _).mpr ?_⟩
  intro ls mem
  obtain ⟨i, eq⟩ := source_index F ls mem
  rw [← eq]
  by_cases hi : kept F i = true
  · apply lift_kept_clause F a h.1 i hi
    exact (clausesSatisfied_iff _ _).mp h.2 _ ((residual_member F _).mpr ⟨i,hi,rfl⟩)
  · exact lift_outside_clause F a i hi

/-- Exact source equivalence for every formula, including malformed-width literals. -/
theorem satisfiable_iff (F : CNFFormula) :
    F.Satisfiable ↔ (residual F).Satisfiable := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, project_satisfied F a h⟩
  · rintro ⟨a, h⟩
    exact ⟨lift F a, lift_satisfied F a h⟩

theorem candidate_matched_clause (F : CNFFormula)
    (i : Fin F.clauses.length) (v : Fin F.variableCount)
    (hm : matching F i = some v) :
    ClauseSatisfied (clause F i) (candidate F) := by
  obtain ⟨l, mem, idx, sign⟩ := preferred_witness F i v hm
  refine (clauseSatisfied_iff _ _).mpr ⟨l, mem, ?_⟩
  change assignmentAt (List.ofFn (preferred F)) l.variableIndex = some l.positive
  rw [idx, assignmentAt_fn]
  simp [v.isLt, sign]

/-- The native basis construction may use a failed clause only after this fact. -/
theorem failed_clause_unmatched (F : CNFFormula) (i : Fin F.clauses.length)
    (h : ¬ ClauseSatisfied (clause F i) (candidate F)) :
    matching F i = none ∧ kept F i = true := by
  have hm : matching F i = none := by
    cases he : matching F i with
    | none => rfl
    | some v => exact False.elim (h (candidate_matched_clause F i v he))
  exact ⟨hm, (kept_iff F i).mpr ((terminal_cut F).1 i hm)⟩

/-- In the existing concrete encoding, the declared width is explicitly unary. -/
theorem decoded_width_bound (bits : BitString) (F : CNFFormula)
    (h : decodeEncodedCNF bits = some F) : F.variableCount ≤ bits.length := by
  unfold decodeEncodedCNF at h
  cases ht : decodeFormulaTokenPairs bits with
  | none => rw [ht] at h; cases h
  | some tokens =>
      rw [ht] at h
      have hw := decodeCNFTokens_variable_succ_le tokens F h
      have hb := decodeFormulaTokenPairs_length bits tokens ht
      omega


end PNP.Concrete.NativeNormalization.CNFCore

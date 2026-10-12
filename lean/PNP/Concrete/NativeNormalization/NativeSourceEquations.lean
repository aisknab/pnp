import PNP.Concrete.NativeNormalization.NativeEquations

namespace PNP.Concrete.NativeNormalization.NativeSourceEquations

open PNP.Concrete CNFCore NativeBasis NativeSource NativeEquations

theorem original_slots (F : CNFFormula) (three : ThreeCore F)
    (i : Fin (positions F).length) (l : CNFLiteral) (h : l ∈ denseLiterals F i) :
    ∃ s, originalLiteral F three i s = l := by
  obtain ⟨k, hk, eq⟩ := List.mem_iff_getElem.mp h
  have bound : k < 3 := by rw [← three i]; exact hk
  have casesK : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases casesK with h0 | h1 | h2
  · subst k; exact ⟨.first, eq⟩
  · subst k; exact ⟨.middle, eq⟩
  · subst k; exact ⟨.last, eq⟩

theorem clause_iff (F : CNFFormula) (three : ThreeCore F)
    (x : Fin (variables F).length → Bool) (i : Fin (positions F).length) :
    ClauseSatisfied (denseLiterals F i) (List.ofFn x) ↔
      clauseTrue (selection F three) x i = true := by
  constructor
  · intro h
    obtain ⟨l, mem, hl⟩ := (clauseSatisfied_iff _ _).mp h
    obtain ⟨s, eq⟩ := original_slots F three i l mem
    rw [← eq] at hl
    apply (clauseTrue_iff _ _ _).mpr
    refine ⟨s, ?_⟩
    change assignmentAt (List.ofFn x) (originalLiteral F three i s).variableIndex =
      some (originalLiteral F three i s).positive at hl
    rw [assignmentAt_fn, dif_pos (originalLiteral_bound F three i s)] at hl
    exact Option.some.inj hl
  · exact clause_model F three x i

theorem compact_iff (F : CNFFormula) (three : ThreeCore F)
    (x : Fin (variables F).length → Bool) :
    (compact F).Satisfied (List.ofFn x) ↔
      ∀ i, clauseTrue (selection F three) x i = true := by
  constructor
  · intro h i
    apply (clause_iff F three x i).mp
    apply (clausesSatisfied_iff _ _).mp h.2
    rw [← denseLiterals_at]
    exact List.getElem_mem _
  · exact compact_model F three x

def vector (n : Nat) (a : BitString) : Fin n → Bool :=
  fun j => (a[j.val]?).getD false

theorem vector_list (n : Nat) (a : BitString) (h : a.length = n) :
    List.ofFn (vector n a) = a := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [vector, List.getElem?_eq_getElem hj]

/-- Explicit source assignment projection and native auxiliary extension. -/
def projectSolution (F : CNFFormula) (three : ThreeCore F)
    (a : BitString) : RowValues (positions F).length :=
  selected (selection F three)
    (extend (selection F three) (vector (variables F).length (projectValues F a)))

/-- Explicit recovery to the original declared source width. -/
def recoverSolution (F : CNFFormula) (three : ThreeCore F)
    (failed : Fin (positions F).length) (u : RowValues (positions F).length) : BitString :=
  recover F (List.ofFn (recovered (selection F three) failed u).x)

theorem project_solution (F : CNFFormula) (three : ThreeCore F)
    (failed : Fin (positions F).length) (hf : firstFailed F three = some failed)
    (a : BitString) (ha : F.Satisfied a) :
    NormalizedSatisfied (selection F three) failed (projectSolution F three a) := by
  have badClause := firstFailed_some F three failed hf
  have hp := compact_project_satisfied F a ha
  have hm : (compact F).Satisfied
      (List.ofFn (vector (variables F).length (projectValues F a))) := by
    rw [vector_list (variables F).length (projectValues F a) hp.1]
    exact hp
  exact native_to_normalized _ _ (failed_unmatched F three failed badClause)
    (failed_first _ failed badClause) _
    (extend_satisfied _ _ ((compact_iff F three _).mp hm))

theorem recover_solution (F : CNFFormula) (three : ThreeCore F)
    (failed : Fin (positions F).length) (hf : firstFailed F three = some failed)
    (u : RowValues (positions F).length)
    (hu : NormalizedSatisfied (selection F three) failed u) :
    F.Satisfied (recoverSolution F three failed u) := by
  have badClause := firstFailed_some F three failed hf
  have hn := normalized_to_native _ _ (failed_unmatched F three failed badClause)
    (failed_first _ failed badClause) u hu
  exact recover_satisfied F _ (compact_model F three _ (native_clause _ _ hn))

/-- The complete logical equivalence is source-derived; no matching, model,
transversal, span, coverage certificate or image-completeness premise is supplied. -/
theorem source_normalized_iff (F : CNFFormula) (three : ThreeCore F)
    (failed : Fin (positions F).length) (hf : firstFailed F three = some failed) :
    F.Satisfiable ↔ ∃ u, NormalizedSatisfied (selection F three) failed u := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨projectSolution F three a, project_solution F three failed hf a ha⟩
  · rintro ⟨u, hu⟩
    exact ⟨recoverSolution F three failed u, recover_solution F three failed hf u hu⟩

inductive Conversion (n c : Nat) where
  | notThree
  | model (assignment : BitString)
  | normalized (data : Selection n c) (failed : Fin c)

/-- This producer accepts only the original source. The unsupported-shape
branch remains explicit and is never interpreted as unsatisfiability. -/
def convert (F : CNFFormula) : Conversion (variables F).length (positions F).length :=
  match build F with
  | .notThree => .notThree
  | .model a => .model a
  | .basis S i => .normalized S i

def ConversionCorrect (F : CNFFormula) :
    Conversion (variables F).length (positions F).length → Prop
  | .notThree => ¬ ThreeCore F
  | .model a => F.Satisfied a
  | .normalized S i =>
      (∃ three : ThreeCore F, S = selection F three ∧ firstFailed F three = some i) ∧
      (F.Satisfiable ↔ ∃ u, NormalizedSatisfied S i u) ∧
      (∀ u, NormalizedSatisfied S i u →
        F.Satisfied (recover F (List.ofFn (recovered S i u).x)))

theorem convert_correct (F : CNFFormula) : ConversionCorrect F (convert F) := by
  have h := build_correct F
  unfold convert
  cases hb : build F with
  | notThree => simpa only [hb, Correct, ConversionCorrect] using h
  | model a => simpa only [hb, Correct, ConversionCorrect] using h
  | basis S i =>
      rw [hb] at h
      obtain ⟨⟨three, rfl, hi⟩, _⟩ := h
      exact ⟨⟨three, rfl, hi⟩, source_normalized_iff F three i hi,
        recover_solution F three i hi⟩


end PNP.Concrete.NativeNormalization.NativeSourceEquations

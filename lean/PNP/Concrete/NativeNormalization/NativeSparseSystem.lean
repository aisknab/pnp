import PNP.Concrete.NativeNormalization.NativeCoefficients

namespace PNP.Concrete.NativeNormalization.NativeSparseSystem

open PNP.Concrete CNFCore NativeBasis NativeSource NativeEquations
open NativeSourceEquations NativeCoefficients

/-- Internal matching coverage, proved below from the source-built selection. -/
def ModeComplete (S : Selection n c) : Prop :=
  ∀ i s, S.mode i = some s → ∃ j, S.owner j = i ∧ S.slot j = s

theorem source_mode_complete (F : CNFFormula) (three : ThreeCore F) :
    ModeComplete (selection F three) := by
  intro i s hm
  change (transported F i).map (chooseSlot (literal F three i)) = some s at hm
  cases ht : transported F i with
  | none => simp [ht] at hm
  | some j =>
      have hs : chooseSlot (literal F three i) j = s := by simpa [ht] using hm
      have ho := partner_of_transported F i j ht
      refine ⟨j, ho, ?_⟩
      change chooseSlot (literal F three (partner F j)) j = s
      rw [ho]
      exact hs

theorem matched_row_basis (S : Selection n c) (failed : Fin c)
    (complete : ModeComplete S) (i : Fin c) (s : Slot)
    (hm : S.mode i = some s) (b : Bool) :
    ∃ k, row S failed k = (i,b) := by
  obtain ⟨j, hj, hs⟩ := complete i s hm
  cases s with
  | first =>
      cases b
      · exact ⟨.inl j, by simp [row, hj, hs]⟩
      · exact ⟨.inr (.inl i), by simp [row, hm]⟩
  | middle =>
      cases b
      · exact ⟨.inl j, by simp [row, hj, hs]⟩
      · exact ⟨.inr (.inl i), by simp [row, hm]⟩
  | last =>
      cases b
      · exact ⟨.inr (.inl i), by simp [row, hm]⟩
      · exact ⟨.inl j, by simp [row, hj, hs]⟩

/-- Exactly the unmatched, nonfailed first rows lie outside the selected basis. -/
theorem nonbasis_iff (S : Selection n c) (failed : Fin c)
    (complete : ModeComplete S) (i : Fin c) (b : Bool) :
    (∀ k, row S failed k ≠ (i,b)) ↔
      b = false ∧ S.mode i = none ∧ i ≠ failed := by
  constructor
  · intro h
    have hm : S.mode i = none := by
      cases hm : S.mode i with
      | none => rfl
      | some s =>
          obtain ⟨k, hk⟩ := matched_row_basis S failed complete i s hm b
          exact False.elim (h k hk)
    have hb : b = false := by
      cases b
      · rfl
      · exact False.elim (h (.inr (.inl i)) (by simp [row, hm]))
    have hi : i ≠ failed := by
      intro hi
      apply h (.inr (.inr ()))
      subst i
      simp [row, hb]
    exact ⟨hb, hm, hi⟩
  · rintro ⟨rfl, hm, hi⟩ k eq
    cases k with
    | inl j =>
        have ho : S.owner j = i := congrArg Prod.fst eq
        have hmode := S.ownerMode j
        rw [ho, hm] at hmode
        cases hmode
    | inr k =>
        cases k with
        | inl j =>
            have hj : j = i := congrArg Prod.fst eq
            subst j
            simp [row, hm] at eq
        | inr u =>
            have hf : failed = i := congrArg Prod.fst eq
            exact hi hf.symm

def remaining (S : Selection n c) (failed : Fin c) : List (Fin c) :=
  (List.finRange c).filter (fun i => decide (S.mode i = none ∧ i ≠ failed))

theorem remaining_mem (S : Selection n c) (failed i : Fin c) :
    i ∈ remaining S failed ↔ S.mode i = none ∧ i ≠ failed := by
  simp [remaining]

theorem remaining_length (S : Selection n c) (failed : Fin c) :
    (remaining S failed).length ≤ c := by
  simpa only [remaining, List.length_finRange] using
    (List.length_filter_le (fun i => decide (S.mode i = none ∧ i ≠ failed)) (List.finRange c))

def allRows (c : Nat) : List (Row c) :=
  (List.finRange c).flatMap (fun i => [(i,false),(i,true)])

theorem allRows_mem (r : Row c) : r ∈ allRows c := by
  refine List.mem_flatMap.mpr ⟨r.1, List.mem_finRange _, ?_⟩
  rcases r with ⟨i,b⟩
  cases b <;> simp

private theorem double_length (xs : List α) (f g : α → β) :
    (xs.flatMap (fun x => [f x,g x])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, Nat.mul_add] <;> omega

theorem allRows_length (c : Nat) : (allRows c).length = 2*c := by
  simpa only [allRows, List.length_finRange] using
    (double_length (List.finRange c) (fun i => (i,false)) (fun i => (i,true)))

/-- Actual finite data, not an oracle or a list of supplied correctness certificates. -/
structure System (c : Nat) where
  b : Coefficients c
  a : List (Row c × Coefficients c)
  e : List (Coefficients c)
deriving Repr

def assemble (S : Selection n c) (failed : Fin c) : System c :=
  { b := bTerms S failed
    a := (allRows c).map (fun r => (r, aTerms S failed r))
    e := (remaining S failed).map (imageTerms S failed) }

def System.Satisfied (D : System c) (u : RowValues c) : Prop :=
  eval u D.b = true ∧
    (∀ terms ∈ D.e, eval u terms = false) ∧
    (∀ entry ∈ D.a, (u entry.1 && !(eval u entry.2)) = false)

theorem assembled_iff (S : Selection n c) (failed : Fin c)
    (complete : ModeComplete S) (u : RowValues c) :
    (assemble S failed).Satisfied u ↔ NormalizedSatisfied S failed u := by
  constructor
  · rintro ⟨hb, he, hq⟩
    refine ⟨by simpa only [assemble, eval_bTerms] using hb, ?_, ?_⟩
    · rintro ⟨i,b⟩ hr
      obtain ⟨rfl, hm, hi⟩ := (nonbasis_iff S failed complete i b).mp hr
      have mem : imageTerms S failed i ∈ (assemble S failed).e :=
        List.mem_map.mpr ⟨i, (remaining_mem S failed i).mpr ⟨hm,hi⟩, rfl⟩
      simpa only [eval_imageTerms S failed u i hm] using he _ mem
    · intro r
      have mem : (r,aTerms S failed r) ∈ (assemble S failed).a :=
        List.mem_map.mpr ⟨r, allRows_mem r, rfl⟩
      simpa only [eval_aTerms, qRow] using hq _ mem
  · rintro ⟨hb, he, hq⟩
    refine ⟨by simpa only [assemble, eval_bTerms] using hb, ?_, ?_⟩
    · intro terms mem
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp mem
      obtain ⟨hm, hn⟩ := (remaining_mem S failed i).mp hi
      rw [eval_imageTerms S failed u i hm]
      exact he (i,false) ((nonbasis_iff S failed complete i false).mpr ⟨rfl,hm,hn⟩)
    · intro entry mem
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp mem
      simpa only [eval_aTerms, qRow] using hq r

theorem source_assembled_iff (F : CNFFormula) (three : ThreeCore F)
    (failed : Fin (positions F).length) (hf : firstFailed F three = some failed) :
    F.Satisfiable ↔ ∃ u, (assemble (selection F three) failed).Satisfied u := by
  rw [source_normalized_iff F three failed hf]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (assembled_iff _ _ (source_mode_complete F three) u).mpr hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, (assembled_iff _ _ (source_mode_complete F three) u).mp hu⟩

theorem source_assembled_recovery (F : CNFFormula) (three : ThreeCore F)
    (failed : Fin (positions F).length) (hf : firstFailed F three = some failed)
    (u : RowValues (positions F).length)
    (hu : (assemble (selection F three) failed).Satisfied u) :
    F.Satisfied (recoverSolution F three failed u) :=
  recover_solution F three failed hf u
    ((assembled_iff _ _ (source_mode_complete F three) u).mp hu)

theorem assembled_row_counts (S : Selection n c) (failed : Fin c) :
    (assemble S failed).a.length = 2*c ∧ (assemble S failed).e.length ≤ c := by
  exact ⟨by simp [assemble, allRows_length], by simpa [assemble] using remaining_length S failed⟩

theorem assembled_row_bounds (S : Selection n c) (failed : Fin c) :
    (assemble S failed).b.length ≤ 3 ∧
    (∀ entry ∈ (assemble S failed).a, entry.2.length ≤ 7) ∧
    (∀ terms ∈ (assemble S failed).e, terms.length ≤ 6) := by
  refine ⟨bTerms_length S failed, ?_, ?_⟩
  · intro entry mem
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp mem
    exact aTerms_length S failed r
  · intro terms mem
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
    exact imageTerms_length S failed i

def System.coefficientCount (D : System c) : Nat :=
  D.b.length + (D.a.map (fun entry => entry.2.length)).sum + (D.e.map List.length).sum

private theorem sum_map_bound (xs : List α) (f : α → Nat) (k : Nat)
    (h : ∀ x ∈ xs, f x ≤ k) : (xs.map f).sum ≤ k * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (by intro y hy; exact h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- Total stored coefficient occurrences are linear in the retained clause count.
This is a data-size theorem, not a concrete machine runtime theorem. -/
theorem assembled_size_bound (S : Selection n c) (failed : Fin c) :
    (assemble S failed).coefficientCount ≤ 20*c+3 := by
  obtain ⟨hb, ha, he⟩ := assembled_row_bounds S failed
  obtain ⟨na, ne⟩ := assembled_row_counts S failed
  have sa := sum_map_bound (assemble S failed).a (fun entry => entry.2.length) 7 ha
  have se := sum_map_bound (assemble S failed).e List.length 6 he
  unfold System.coefficientCount
  rw [na] at sa
  omega

/-- The finite output data and explicit source-model recovery are constructed
from the original source alone. -/
inductive Output (c : Nat) where
  | notThree
  | model (assignment : BitString)
  | system (data : System c) (recoverModel : RowValues c → BitString)

def produce (F : CNFFormula) : Output (positions F).length :=
  match build F with
  | .notThree => .notThree
  | .model a => .model a
  | .basis S i => .system (assemble S i)
      (fun u => recover F (List.ofFn (recovered S i u).x))

def OutputCorrect (F : CNFFormula) : Output (positions F).length → Prop
  | .notThree => ¬ ThreeCore F
  | .model a => F.Satisfied a
  | .system D liftModel =>
      (F.Satisfiable ↔ ∃ u, D.Satisfied u) ∧
      (∀ u, D.Satisfied u → F.Satisfied (liftModel u)) ∧
      D.b.length ≤ 3 ∧
      (∀ entry ∈ D.a, entry.2.length ≤ 7) ∧
      (∀ terms ∈ D.e, terms.length ≤ 6) ∧
      D.a.length = 2*(positions F).length ∧
      D.e.length ≤ (positions F).length ∧
      D.coefficientCount ≤ 20*(positions F).length+3

theorem produce_correct (F : CNFFormula) : OutputCorrect F (produce F) := by
  have h := build_correct F
  unfold produce
  cases hb : build F with
  | notThree => simpa only [hb, Correct, OutputCorrect] using h
  | model a => simpa only [hb, Correct, OutputCorrect] using h
  | basis S i =>
      rw [hb] at h
      obtain ⟨⟨three, rfl, hi⟩, _⟩ := h
      obtain ⟨hb, ha, he⟩ := assembled_row_bounds (selection F three) i
      obtain ⟨na, ne⟩ := assembled_row_counts (selection F three) i
      exact ⟨source_assembled_iff F three i hi, source_assembled_recovery F three i hi,
        hb, ha, he, na, ne, assembled_size_bound (selection F three) i⟩


end PNP.Concrete.NativeNormalization.NativeSparseSystem

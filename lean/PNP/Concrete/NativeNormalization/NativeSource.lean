import PNP.Concrete.NativeNormalization.CNFTransport
import PNP.Concrete.NativeNormalization.NativeBasis

namespace PNP.Concrete.NativeNormalization.NativeSource

open PNP.Concrete CNFCore NativeBasis

def ThreeCore (F : CNFFormula) : Prop :=
  ∀ i : Fin (positions F).length, (denseLiterals F i).length = 3

instance (F : CNFFormula) : Decidable (ThreeCore F) :=
  inferInstanceAs (Decidable (∀ i : Fin (positions F).length, (denseLiterals F i).length = 3))

def slotIndex : Slot → Nat
  | .first => 0 | .middle => 1 | .last => 2

theorem slotIndex_lt (F : CNFFormula) (three : ThreeCore F)
    (i : Fin (positions F).length) (s : Slot) :
    slotIndex s < (denseLiterals F i).length := by
  rw [three i]
  cases s <;> decide

def originalLiteral (F : CNFFormula) (three : ThreeCore F)
    (i : Fin (positions F).length) (s : Slot) : CNFLiteral :=
  (denseLiterals F i)[slotIndex s]'(slotIndex_lt F three i s)

theorem originalLiteral_mem (F : CNFFormula) (three : ThreeCore F)
    (i : Fin (positions F).length) (s : Slot) :
    originalLiteral F three i s ∈ denseLiterals F i :=
  List.getElem_mem (slotIndex_lt F three i s)

theorem originalLiteral_bound (F : CNFFormula) (three : ThreeCore F)
    (i : Fin (positions F).length) (s : Slot) :
    (originalLiteral F three i s).variableIndex < (variables F).length := by
  apply compact_wellformed F (denseLiterals F i)
  · rw [← denseLiterals_at]
    exact List.getElem_mem _
  · exact originalLiteral_mem F three i s

def literal (F : CNFFormula) (three : ThreeCore F)
    (i : Fin (positions F).length) (s : Slot) : Literal (variables F).length :=
  ⟨⟨(originalLiteral F three i s).variableIndex, originalLiteral_bound F three i s⟩,
    (originalLiteral F three i s).positive⟩

theorem occurrence_slot (F : CNFFormula) (three : ThreeCore F)
    (i : Fin (positions F).length) (v : Fin (variables F).length)
    (h : transported F i = some v) :
    (literal F three i .first).index = v ∨
    (literal F three i .middle).index = v ∨
    (literal F three i .last).index = v := by
  obtain ⟨l, mem, idx, _⟩ := transported_occurrence F i v h
  obtain ⟨k, hk, eq⟩ := List.mem_iff_getElem.mp mem
  have bound : k < 3 := by rw [← three i]; exact hk
  have casesK : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases casesK with h0 | h1 | h2
  · subst k
    left
    apply Fin.ext
    exact congrArg CNFLiteral.variableIndex eq |>.trans idx
  · subst k
    right; left
    apply Fin.ext
    exact congrArg CNFLiteral.variableIndex eq |>.trans idx
  · subst k
    right; right
    apply Fin.ext
    exact congrArg CNFLiteral.variableIndex eq |>.trans idx

def chooseSlot (ls : Slot → Literal n) (v : Fin n) : Slot :=
  if (ls .first).index = v then .first
  else if (ls .middle).index = v then .middle else .last

theorem chooseSlot_correct (ls : Slot → Literal n) (v : Fin n)
    (h : (ls .first).index = v ∨ (ls .middle).index = v ∨ (ls .last).index = v) :
    (ls (chooseSlot ls v)).index = v := by
  unfold chooseSlot
  split
  · assumption
  · split
    · assumption
    · rcases h with h | h | h <;> simp_all

/-- Fully computed matching data, including an actual slot in each owner's clause. -/
def selection (F : CNFFormula) (three : ThreeCore F) :
    Selection (variables F).length (positions F).length :=
  { literal := literal F three
    owner := partner F
    slot := fun v => chooseSlot (literal F three (partner F v)) v
    mode := fun i => (transported F i).map (chooseSlot (literal F three i))
    ownerVariable := fun v => chooseSlot_correct _ v
      (occurrence_slot F three _ v (partner_correct F v))
    ownerMode := by intro v; simp [partner_correct] }

def clauseTrue (S : Selection n c) (x : Fin n → Bool) (i : Fin c) : Bool :=
  decide (x (S.literal i .first).index = (S.literal i .first).positive) ||
    (decide (x (S.literal i .middle).index = (S.literal i .middle).positive) ||
      decide (x (S.literal i .last).index = (S.literal i .last).positive))

theorem clauseTrue_iff (S : Selection n c) (x : Fin n → Bool) (i : Fin c) :
    clauseTrue S x i = true ↔ ∃ s, x (S.literal i s).index = (S.literal i s).positive := by
  constructor
  · intro h
    simp only [clauseTrue, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h | h
    · exact ⟨.first,h⟩
    · exact ⟨.middle,h⟩
    · exact ⟨.last,h⟩
  · rintro ⟨s,h⟩
    cases s <;> simp [clauseTrue, h]

theorem owner_clause_true (S : Selection n c) (v : Fin n) :
    clauseTrue S (sigma S) (S.owner v) = true := by
  apply (clauseTrue_iff _ _ _).mpr
  refine ⟨S.slot v, ?_⟩
  rw [S.ownerVariable]
  rfl

theorem failed_unmatched (F : CNFFormula) (three : ThreeCore F)
    (i : Fin (positions F).length)
    (h : clauseTrue (selection F three) (sigma (selection F three)) i = false) :
    (selection F three).mode i = none := by
  change (transported F i).map _ = none
  cases hm : transported F i with
  | none => rfl
  | some v =>
      have owner := partner_of_transported F i v hm
      have ht := owner_clause_true (selection F three) v
      change clauseTrue (selection F three) (sigma (selection F three)) (partner F v) = true at ht
      rw [owner, h] at ht
      cases ht

theorem failed_first (S : Selection n c) (i : Fin c)
    (h : clauseTrue S (sigma S) i = false) :
    sigma S (anchor S i) ≠ (S.literal i .first).positive := by
  intro eq
  have ht := (clauseTrue_iff S (sigma S) i).mpr ⟨.first,eq⟩
  rw [h] at ht
  cases ht

theorem clause_model (F : CNFFormula) (three : ThreeCore F)
    (x : Fin (variables F).length → Bool) (i : Fin (positions F).length)
    (h : clauseTrue (selection F three) x i = true) :
    ClauseSatisfied (denseLiterals F i) (List.ofFn x) := by
  obtain ⟨s, hs⟩ := (clauseTrue_iff _ _ _).mp h
  refine (clauseSatisfied_iff _ _).mpr
    ⟨originalLiteral F three i s, originalLiteral_mem F three i s, ?_⟩
  change assignmentAt (List.ofFn x) (originalLiteral F three i s).variableIndex =
    some (originalLiteral F three i s).positive
  rw [assignmentAt_fn]
  simp only [dif_pos (originalLiteral_bound F three i s)]
  exact congrArg some hs

theorem compact_model (F : CNFFormula) (three : ThreeCore F)
    (x : Fin (variables F).length → Bool)
    (h : ∀ i, clauseTrue (selection F three) x i = true) :
    (compact F).Satisfied (List.ofFn x) := by
  refine ⟨by simp [compact], (clausesSatisfied_iff _ _).mpr ?_⟩
  intro ls mem
  obtain ⟨k, hk, eq⟩ := List.mem_iff_getElem.mp mem
  have hb : k < (positions F).length := by rw [← dense_positions_length]; exact hk
  let i : Fin (positions F).length := ⟨k,hb⟩
  have hi : denseLiterals F i = ls := by rw [← denseLiterals_at]; exact eq
  rw [← hi]
  exact clause_model F three x i (h i)

/-- Search only for a failed clause of the explicitly constructed candidate. -/
def firstFailed (F : CNFFormula) (three : ThreeCore F) :
    Option (Fin (positions F).length) :=
  (List.finRange (positions F).length).find?
    (fun i => !(clauseTrue (selection F three) (sigma (selection F three)) i))

theorem firstFailed_some (F : CNFFormula) (three : ThreeCore F)
    (i : Fin (positions F).length) (h : firstFailed F three = some i) :
    clauseTrue (selection F three) (sigma (selection F three)) i = false := by
  have ht := List.find?_some (p := fun i =>
    !(clauseTrue (selection F three) (sigma (selection F three)) i)) h
  simpa using ht

theorem firstFailed_none (F : CNFFormula) (three : ThreeCore F)
    (h : firstFailed F three = none) :
    F.Satisfied (recover F (List.ofFn (sigma (selection F three)))) := by
  apply recover_satisfied
  apply compact_model F three
  intro i
  have ht := (List.find?_eq_none.mp h) i (List.mem_finRange i)
  simpa using ht

/-- Source-only failed-branch theorem: no matching, good transversal or span is supplied. -/
theorem source_basis (F : CNFFormula) (three : ThreeCore F)
    (i : Fin (positions F).length) (h : firstFailed F three = some i) :
    (∀ w, decode (selection F three) i
      (pick (selection F three) i (selected (selection F three) w)) = w) ∧
    (∀ b, pick (selection F three) i
      (selected (selection F three) (decode (selection F three) i b)) = b) ∧
    (∀ a b, row (selection F three) i a = row (selection F three) i b → a = b) := by
  have failed := firstFailed_some F three i h
  have um := failed_unmatched F three i failed
  have bad := failed_first (selection F three) i failed
  exact ⟨reconstruct_selected _ i um bad, selected_basis_surjective _ i um bad,
    row_injective _ i um bad⟩

inductive Output (n c : Nat) where
  | notThree
  | model (assignment : BitString)
  | basis (data : Selection n c) (failed : Fin c)

/-- The shape test is explicit. notThree is NOT an unsatisfiability claim. -/
def build (F : CNFFormula) : Output (variables F).length (positions F).length :=
  if h : ThreeCore F then
    match firstFailed F h with
    | none => .model (recover F (List.ofFn (sigma (selection F h))))
    | some i => .basis (selection F h) i
  else .notThree

def Correct (F : CNFFormula) : Output (variables F).length (positions F).length → Prop
  | .notThree => ¬ ThreeCore F
  | .model a => F.Satisfied a
  | .basis S i =>
      (∃ h : ThreeCore F, S = selection F h ∧ firstFailed F h = some i) ∧
      (∀ w, decode S i (pick S i (selected S w)) = w) ∧
      (∀ b, pick S i (selected S (decode S i b)) = b) ∧
      (∀ a b, row S i a = row S i b → a = b)

/-- Every branch is checked against the original concrete source. -/
theorem build_correct (F : CNFFormula) : Correct F (build F) := by
  unfold build
  split
  · rename_i three
    split
    · rename_i none
      exact firstFailed_none F three none
    · rename_i i hi
      exact ⟨⟨three,rfl,hi⟩, source_basis F three i hi⟩
  · assumption


end PNP.Concrete.NativeNormalization.NativeSource

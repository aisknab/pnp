/-
Copyright (c) 2026 PNP Labs.

Complete bounded physical search from the original circuit alone. Every
selected support up to the fixed limit has one scheduled representative.
A result is a strict equivalent whole-circuit gain or exact bounded causal
silence, never an unconditional global minimum or full-profile certificate.
-/

import PNP.NANDBoundedWindowSchedule

namespace PNP.DirectWire.BoundedWindowSchedule

variable {inputs gates outputs : Nat}
variable (candidate : Candidate inputs gates outputs)

/-- Retain the actual successful search result so the chosen window is not searched twice. -/
structure FoundIn (words : List (List (Fin gates))) where
  word : List (Fin gates)
  listed : word ∈ words
  witness : PhysicalWindowSearch.Found candidate (recordsOf word)

namespace FoundIn

variable {candidate} {words : List (List (Fin gates))}

def result (found : FoundIn candidate words) : Implementation inputs outputs :=
  found.witness.result

def gain (found : FoundIn candidate words) :
    StrictEquivalentGain candidate.toImplementation found.result :=
  found.witness.gain

theorem strict_residual_descent (found : FoundIn candidate words) :
    residualSlack found.result < residualSlack candidate.toImplementation :=
  found.witness.strict_residual_descent

theorem support_bound (limit : Nat)
    (found : FoundIn candidate (windowsFrom gates limit 0)) :
    (extractTerminalSupport candidate (recordsOf found.word)).gateCount ≤ limit :=
  Nat.le_trans (recordsOf_count_le candidate found.word)
    (windowsFrom_sound gates limit 0 found.word found.listed).1

theorem proper_of_limit_lt (limit : Nat)
    (found : FoundIn candidate (windowsFrom gates limit 0)) (properLimit : limit < gates) :
    (extractTerminalSupport candidate (recordsOf found.word)).gateCount < gates :=
  Nat.lt_of_le_of_lt (found.support_bound limit) properLimit

end FoundIn

/-- Search each scheduled support once; retain the first discovered replacement. -/
def scan : (words : List (List (Fin gates))) → Option (FoundIn candidate words)
  | [] => none
  | word :: remaining =>
      match computed : PhysicalWindowSearch.search candidate (recordsOf word) with
      | some offered => some ⟨word, List.mem_cons_self, ⟨offered, computed⟩⟩
      | none => (scan remaining).map fun found =>
          ⟨found.word, List.mem_cons_of_mem word found.listed, found.witness⟩

theorem scan_none_iff (words : List (List (Fin gates))) :
    scan candidate words = none ↔
      ∀ word, word ∈ words → PhysicalWindowSearch.search candidate (recordsOf word) = none := by
  induction words with
  | nil =>
      constructor
      · intro _ word absent
        cases absent
      · intro _
        rfl
  | cons head tail ih =>
      cases headFound : PhysicalWindowSearch.search candidate (recordsOf head) with
      | some offered =>
          constructor
          · intro impossible
            unfold scan at impossible
            split at impossible
            · cases impossible
            · rename_i computed
              have conflict := headFound.symm.trans computed
              cases conflict
          · intro quiet
            have impossible := quiet head List.mem_cons_self
            rw [headFound] at impossible
            cases impossible
      | none =>
          constructor
          · intro empty
            have tailEmpty : scan candidate tail = none := by
              cases tailFound : scan candidate tail with
              | none => rfl
              | some found =>
                  unfold scan at empty
                  split at empty
                  · rename_i offered computed
                    have conflict := headFound.symm.trans computed
                    cases conflict
                  · rw [tailFound] at empty
                    cases empty
            intro word present
            rcases List.mem_cons.mp present with same | remaining
            · subst word
              exact headFound
            · exact ih.mp tailEmpty word remaining
          · intro quiet
            have tailEmpty := ih.mpr
              (fun word present => quiet word (List.mem_cons_of_mem head present))
            unfold scan
            split
            · rename_i offered computed
              have conflict := headFound.symm.trans computed
              cases conflict
            · rw [tailEmpty]
              rfl

/-- Absence of a strictly smaller candidate in every physical window up to the
limit, with the exact source-derived causal caps. No global minimality claim. -/
def BoundedQuiet (limit : Nat) : Prop :=
  ∀ (width : Nat) (records : List (TerminalPrimitiveRecord inputs gates outputs width)),
    (extractTerminalSupport candidate records).gateCount ≤ limit →
      ∀ offered, ¬PhysicalWindowSearch.Valid candidate records offered

/-- The generated schedule is complete even for noncanonical record ledgers. -/
theorem scan_schedule_none_iff (limit : Nat) :
    scan candidate (windowsFrom gates limit 0) = none ↔ BoundedQuiet candidate limit := by
  constructor
  · intro noneAt width records bounded offered valid
    obtain ⟨word, listed, same⟩ := schedule_covers candidate limit records bounded
    obtain ⟨transported, validTransported⟩ :=
      valid_exists_of_selected_eq candidate records (recordsOf word) same.symm ⟨offered, valid⟩
    have localNone := (scan_none_iff candidate _).mp noneAt word listed
    exact (PhysicalWindowSearch.search_none_iff candidate (recordsOf word)).mp
      localNone transported validTransported
  · intro quiet
    apply (scan_none_iff candidate _).mpr
    intro word listed
    apply (PhysicalWindowSearch.search_none_iff candidate (recordsOf word)).mpr
    exact quiet 0 (recordsOf word)
      (Nat.le_trans (recordsOf_count_le candidate word)
        (windowsFrom_sound gates limit 0 word listed).1)

/-- A concrete successful window or exact bounded-class exhaustion. -/
inductive Outcome (limit : Nat) where
  | gain (found : FoundIn candidate (windowsFrom gates limit 0))
  | quiet (noBoundedGain : BoundedQuiet candidate limit)

/-- The caller supplies only the source and fixed schema limit, not a support family. -/
def run (limit : Nat) : Outcome candidate limit :=
  match computed : scan candidate (windowsFrom gates limit 0) with
  | some found => .gain found
  | none => .quiet ((scan_schedule_none_iff candidate limit).mp computed)

/-- Exact all-window candidate demand, an upper envelope for a short-circuiting scan. -/
def candidateDemand (limit : Nat) : Nat :=
  ((windowsFrom gates limit 0).map fun word =>
    (PhysicalWindowSearch.candidateUniverse candidate (recordsOf word)).length).sum

private theorem sum_map_le {alpha : Type} (items : List alpha) (cost : alpha → Nat)
    (bound : Nat) (each : ∀ item, item ∈ items → cost item ≤ bound) :
    (items.map cost).sum ≤ items.length * bound := by
  induction items with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons head tail ih =>
      have first := each head List.mem_cons_self
      have rest := ih (fun item present => each item (List.mem_cons_of_mem head present))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add first rest) (Nat.le_of_eq (Nat.add_comm _ _))

/-- Candidate-count polynomial for a fixed schema, not a complete runtime theorem. -/
theorem candidateDemand_le (limit : Nat) :
    candidateDemand candidate limit ≤
      (gates + 1) ^ limit * PhysicalWindowSearch.fixedWindowBudget limit := by
  have bound := sum_map_le (windowsFrom gates limit 0)
    (fun word => (PhysicalWindowSearch.candidateUniverse candidate (recordsOf word)).length)
    (PhysicalWindowSearch.fixedWindowBudget limit) (fun word listed =>
      PhysicalWindowSearch.candidateUniverse_length_le candidate (recordsOf word) limit
        (Nat.le_trans (recordsOf_count_le candidate word)
          (windowsFrom_sound gates limit 0 word listed).1))
  exact Nat.le_trans bound
    (Nat.mul_le_mul_right _ (windowsFrom_length_le gates limit 0))

end PNP.DirectWire.BoundedWindowSchedule

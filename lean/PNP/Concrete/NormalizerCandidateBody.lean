/-
Copyright (c) 2026 PNP Labs.

A fixed candidate step: skip an owned variable; otherwise query the stored
trace-node table, selecting the variable only when it is present there.
The branch consumes the remaining counter or clears it on the first hit.
-/

import PNP.Concrete.NormalizerCandidateLookup

namespace PNP.Concrete.NormalizerBlocks.Candidate

open BitRegister

def advance : Block 13 := .seq (.action (.pop 11)) (.action (.push 1 true))
def advanced (r : State) : State :=
  ⟨{r.core with target := true :: r.core.target}, r.matching, r.seen, r.remaining.tail, r.output⟩

theorem advance_exec (r : State) : Exec advance r.store 2 (advanced r).store :=
  Exec.seq (.action _ _) (.action _ _)

def choose : Block 13 :=
  .seq (.action (.copy 12 1)) (.seq (.action (.push 12 true)) (.action (.clear 11)))
def chosen (r : State) : State := ⟨r.core, r.matching, r.seen, [], true :: r.core.target⟩

theorem choose_exec (r : State) : Exec choose r.store 3 (chosen r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def finish : Block 13 := .branch 8 advance advance choose
def finishResult (r : State) : Result :=
  match r.core.output with
  | [] => ⟨3, advanced r⟩
  | false :: _ => ⟨3, advanced r⟩
  | true :: _ => ⟨4, chosen r⟩

theorem finish_exec (r : State) :
    Exec finish r.store (finishResult r).fuel (finishResult r).state.store := by
  cases output : r.core.output with
  | nil => simpa only [finish, finishResult, output] using
      Exec.empty (source := (8 : Fin 13)) (before := r.store) output (advance_exec r)
  | cons bit rest =>
      cases bit
      · simpa only [finish, finishResult, output] using
          Exec.zero (source := (8 : Fin 13)) (before := r.store) output (advance_exec r)
      · simpa only [finish, finishResult, output] using
          Exec.one (source := (8 : Fin 13)) (before := r.store) output (choose_exec r)

def decision : Block 13 := .branch 8 advance (.seq readSeen finish) advance
def decisionResult (r : State) : Result :=
  match r.core.output with
  | [] => ⟨3, advanced r⟩
  | false :: _ =>
      let tail := finishResult (seenResult r)
      ⟨1 + (seenFuel r + tail.fuel), tail.state⟩
  | true :: _ => ⟨3, advanced r⟩

theorem decision_exec (r : State) :
    Exec decision r.store (decisionResult r).fuel (decisionResult r).state.store := by
  cases output : r.core.output with
  | nil => simpa only [decision, decisionResult, output] using
      Exec.empty (source := (8 : Fin 13)) (before := r.store) output (advance_exec r)
  | cons bit rest =>
      cases bit
      · simpa only [decision, decisionResult, output] using
          Exec.zero (source := (8 : Fin 13)) (before := r.store) output (Exec.seq (readSeen_exec r) (finish_exec (seenResult r)))
      · simpa only [decision, decisionResult, output] using
          Exec.one (source := (8 : Fin 13)) (before := r.store) output (advance_exec r)

def body : Block 13 := .seq readMatching decision
def result (r : State) : State := (decisionResult (matchingResult r)).state
def bodyFuel (r : State) : Nat := matchingFuel r + (decisionResult (matchingResult r)).fuel

theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (result r).store :=
  Exec.seq (readMatching_exec r) (decision_exec (matchingResult r))

theorem finish_frame (r : State) :
    (finishResult r).state.matching = r.matching ∧ (finishResult r).state.seen = r.seen := by
  simp only [finishResult]
  split <;> exact ⟨rfl, rfl⟩

theorem decision_frame (r : State) :
    (decisionResult r).state.matching = r.matching ∧ (decisionResult r).state.seen = r.seen := by
  simp only [decisionResult]
  split
  · exact ⟨rfl, rfl⟩
  · exact finish_frame (seenResult r)
  · exact ⟨rfl, rfl⟩

theorem result_frame (r : State) : (result r).matching = r.matching ∧ (result r).seen = r.seen :=
  decision_frame (matchingResult r)

theorem finish_remaining_strict (r : State) (nonempty : r.remaining ≠ []) :
    (finishResult r).state.remaining.length < r.remaining.length := by
  have positive : 0 < r.remaining.length := by
    cases remaining : r.remaining with
    | nil => exact False.elim (nonempty remaining)
    | cons bit rest => exact Nat.zero_lt_succ rest.length
  simp only [finishResult]
  split <;> simp only [advanced, chosen, List.length_tail, List.length_nil] <;> omega

theorem decision_remaining_strict (r : State) (nonempty : r.remaining ≠ []) :
    (decisionResult r).state.remaining.length < r.remaining.length := by
  have positive : 0 < r.remaining.length := by
    cases remaining : r.remaining with
    | nil => exact False.elim (nonempty remaining)
    | cons bit rest => exact Nat.zero_lt_succ rest.length
  simp only [decisionResult]
  split
  · simp only [advanced, List.length_tail]; omega
  · exact finish_remaining_strict (seenResult r) nonempty
  · simp only [advanced, List.length_tail]; omega

theorem remaining_strict (r : State) (nonempty : r.remaining ≠ []) :
    (result r).remaining.length < r.remaining.length :=
  decision_remaining_strict (matchingResult r) nonempty

theorem finish_fuel_bound (r : State) : (finishResult r).fuel ≤ 4 := by
  simp only [finishResult]
  split
  · change 3 ≤ 4; decide
  · change 3 ≤ 4; decide
  · change 4 ≤ 4; decide

theorem decision_fuel_bound (r : State) : (decisionResult r).fuel ≤ 12 * r.seen.length + 28 := by
  have scan := seenFuel_bound r
  have tail := finish_fuel_bound (seenResult r)
  simp only [decisionResult]
  split
  · change 3 ≤ 12 * r.seen.length + 28; omega
  · change 1 + (seenFuel r + (finishResult (seenResult r)).fuel) ≤ 12 * r.seen.length + 28; omega
  · change 3 ≤ 12 * r.seen.length + 28; omega

theorem bodyFuel_bound (r : State) : bodyFuel r ≤ 12 * r.matching.length + 12 * r.seen.length + 51 := by
  have first := matchingFuel_bound r
  have tail : (decisionResult (matchingResult r)).fuel ≤ 12 * r.seen.length + 28 :=
    decision_fuel_bound (matchingResult r)
  simp only [bodyFuel]
  omega

end PNP.Concrete.NormalizerBlocks.Candidate

/-
Copyright (c) 2026 PNP Labs.

Uniform finite candidate iteration. Every live step consumes the candidate
counter or selects an answer and clears it. The two lookup tables remain
unchanged, so one shared linear-per-iteration budget bounds the complete loop.
-/

import PNP.Concrete.NormalizerCandidateBody

namespace PNP.Concrete.NormalizerBlocks.Candidate

open BitRegister

def loop : Block 13 := .loop 11 body

def run : Nat → State → Result
  | 0, r => ⟨1, r⟩
  | fuel + 1, r =>
      match r.remaining with
      | [] => ⟨1, r⟩
      | _ :: _ =>
          let tail := run fuel (result r)
          ⟨1 + (bodyFuel r + tail.fuel), tail.state⟩

theorem run_exec (fuel : Nat) (r : State)
    (enough : r.remaining.length < fuel ∨ r.remaining = []) :
    Exec loop r.store (run fuel r).fuel (run fuel r).state.store := by
  induction fuel generalizing r with
  | zero =>
      have stopped := enough.resolve_left (Nat.not_lt_zero _)
      exact Exec.loopStop stopped
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simpa only [run, remaining, loop] using
          (Exec.loopStop (source := (11 : Fin 13)) (body := body) (store := r.store) remaining)
      | cons bit rest =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro bad; cases bad
          have length : r.remaining.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have smaller := remaining_strict r nonempty
          have tail := ih (result r) (Or.inl (Nat.lt_of_lt_of_le smaller length))
          simpa only [loop, run, remaining] using
            Exec.loopStep (source := (11 : Fin 13)) (body := body) (before := r.store)
              remaining (body_exec r) tail

theorem run_stopped (fuel : Nat) (r : State)
    (enough : r.remaining.length < fuel ∨ r.remaining = []) :
    (run fuel r).state.remaining = [] := by
  induction fuel generalizing r with
  | zero => exact enough.resolve_left (Nat.not_lt_zero _)
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simp only [run, remaining]
      | cons bit rest =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro bad; cases bad
          have length : r.remaining.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have smaller := remaining_strict r nonempty
          simpa only [run, remaining] using ih (result r) (Or.inl (Nat.lt_of_lt_of_le smaller length))

theorem run_frame (fuel : Nat) (r : State) :
    (run fuel r).state.matching = r.matching ∧ (run fuel r).state.seen = r.seen := by
  induction fuel generalizing r with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => constructor <;> simp only [run, remaining]
      | cons bit rest =>
          have current := result_frame r
          have tail := ih (result r)
          simpa only [run, remaining] using ⟨tail.1.trans current.1, tail.2.trans current.2⟩

theorem run_fuel_bound (fuel : Nat) (r : State) :
    (run fuel r).fuel ≤ (12 * r.matching.length + 12 * r.seen.length + 52) * fuel + 1 := by
  induction fuel generalizing r with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simp only [run, remaining]; omega
      | cons bit rest =>
          have current := bodyFuel_bound r
          have frame := result_frame r
          have tail := ih (result r)
          rw [frame.1, frame.2] at tail
          simp only [run, remaining, Nat.mul_succ]
          omega

def whole (r : State) : Result := run (r.remaining.length + 1) r

theorem whole_exec (r : State) : Exec loop r.store (whole r).fuel (whole r).state.store :=
  run_exec _ r (Or.inl (Nat.lt_succ_self _))

theorem whole_stopped (r : State) : (whole r).state.remaining = [] :=
  run_stopped _ r (Or.inl (Nat.lt_succ_self _))

theorem whole_fuel_bound (r : State) :
    (whole r).fuel ≤ (12 * r.matching.length + 12 * r.seen.length + 52) * (r.remaining.length + 1) + 1 :=
  run_fuel_bound _ r

end PNP.Concrete.NormalizerBlocks.Candidate

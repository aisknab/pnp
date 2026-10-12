/-
Copyright (c) 2026 PNP Labs.

Complete finite-control clause compaction. The loop consumes the actual
literal stream and preserves the selected-variable list. Its cost bound is
polynomial in the encoded cursor and selected-list sizes, on all raw data.
-/
import PNP.Concrete.NormalizerCompactStep

namespace PNP.Concrete.NormalizerBlocks.CompactClause
open BitRegister Occurrence

structure ScanResult where
  fuel : Nat
  state : State

def loop : Block 13 := .loop 9 step
def scan : Nat → State → ScanResult
  | 0, r => ⟨1,r⟩
  | fuel + 1, r =>
      match r.pending with
      | [] => ⟨1,r⟩
      | _ :: _ =>
          let tail := scan fuel (stepped r)
          ⟨1 + (stepFuel r + tail.fuel),tail.state⟩

theorem scan_stopped (fuel : Nat) (r : State) (stopped : r.pending = []) :
    scan fuel r = ⟨1,r⟩ := by
  cases fuel <;> simp only [scan, stopped]

theorem scan_exec (fuel : Nat) (r : State)
    (enough : r.pending.length < fuel ∨ r.pending = []) :
    Exec loop r.store (scan fuel r).fuel (scan fuel r).state.store := by
  induction fuel generalizing r with
  | zero =>
      have empty : r.pending = [] := enough.resolve_left (Nat.not_lt_zero _)
      exact Exec.loopStop empty
  | succ fuel ih =>
      cases pending : r.pending with
      | nil => simpa only [loop, scan, pending] using
          (Exec.loopStop (source := (9 : Fin 13)) (body := step) (store := r.store) pending)
      | cons bit rest =>
          have size : r.pending.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => rw [pending] at h; cases h
          have nonempty : r.pending ≠ [] := by rw [pending]; intro impossible; cases impossible
          have tail := ih (stepped r)
            (Or.inl (Nat.lt_of_lt_of_le (step_progress r nonempty) size))
          simpa only [loop, scan, pending] using
            Exec.loopStep (source := (9 : Fin 13)) (body := step) (before := r.store)
              pending (step_exec r) tail

theorem scan_variables (fuel : Nat) (r : State) :
    (scan fuel r).state.variables = r.variables := by
  induction fuel generalizing r with
  | zero => rfl
  | succ fuel ih =>
      cases pending : r.pending with
      | nil => rw [scan_stopped _ r pending]
      | cons bit rest =>
          simpa only [scan, pending] using (ih (stepped r)).trans (stepped_variables r)

theorem scan_fuel_bound (fuel : Nat) (r : State) :
    (scan fuel r).fuel ≤
      (7 * r.pending.length + 64 * r.variables.length + 119) * fuel + 1 := by
  induction fuel generalizing r with
  | zero => simp only [scan, Nat.mul_zero, Nat.zero_add]; exact Nat.le_refl _
  | succ fuel ih =>
      cases pending : r.pending with
      | nil => simp only [scan, pending]; omega
      | cons bit rest =>
          have nonempty : r.pending ≠ [] := by rw [pending]; intro impossible; cases impossible
          have smaller := step_progress r nonempty
          have step := stepFuel_bound r
          have tail := ih (stepped r)
          rw [stepped_variables] at tail
          have factor : 7 * (stepped r).pending.length + 64 * r.variables.length + 119 ≤
              7 * r.pending.length + 64 * r.variables.length + 119 := by omega
          have product := Nat.mul_le_mul_right fuel factor
          rw [pending] at product step
          simp only [scan, pending, Nat.mul_succ]
          omega

def whole (r : State) : ScanResult := scan (r.pending.length + 1) r
theorem whole_exec (r : State) : Exec loop r.store (whole r).fuel (whole r).state.store :=
  scan_exec _ r (Or.inl (Nat.lt_succ_self _))
theorem whole_variables (r : State) : (whole r).state.variables = r.variables :=
  scan_variables _ r
theorem whole_fuel_bound (r : State) :
    (whole r).fuel ≤
      (7 * r.pending.length + 64 * r.variables.length + 119) * (r.pending.length + 1) + 1 :=
  scan_fuel_bound _ r

def callBound : NatPolynomial := .add (.mul (.linear 71 119) (.linear 1 1)) (.constant 1)
theorem callBound_eval (bound : Nat) :
    callBound.eval bound = (71 * bound + 119) * (bound + 1) + 1 := by
  change (71 * bound + 119) * (1 * bound + 1) + 1 = _
  rw [Nat.one_mul]

theorem whole_fuel_bounded (r : State) (bound : Nat) (bounded : r.store.Bounded bound) :
    (whole r).fuel ≤ callBound.eval bound := by
  have pending := Store.get_length_le r.store (9 : Fin 13) bounded
  have variables := Store.get_length_le r.store (10 : Fin 13) bounded
  change r.pending.length ≤ bound at pending
  change r.variables.length ≤ bound at variables
  have fuel := whole_fuel_bound r
  have product := Nat.mul_le_mul
    (show 7 * r.pending.length + 64 * r.variables.length + 119 ≤ 71 * bound + 119 by omega)
    (show r.pending.length + 1 ≤ bound + 1 by omega)
  rw [callBound_eval]
  omega

end PNP.Concrete.NormalizerBlocks.CompactClause

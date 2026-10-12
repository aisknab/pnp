/-
Copyright (c) 2026 PNP Labs.

Total suffix-based path reconstruction over arbitrary raw words. An
external fuel parameter proves the finite loop; it is not machine input.
The closed run derives enough fuel from the actual trace length.
-/
import PNP.Concrete.NormalizerPathStep

namespace PNP.Concrete.NormalizerBlocks.TracePath
open BitRegister

structure ScanResult where
  fuel : Nat
  state : State

def loop : Block 23 := .loop 16 body
def scan : Nat → State → ScanResult
  | 0, r => ⟨1, r⟩
  | fuel + 1, r =>
      match r.core.pending with
      | [] => ⟨1, r⟩
      | _ :: _ =>
          let tail := scan fuel (bodyResult r)
          ⟨1 + (bodyFuel r + tail.fuel), tail.state⟩

theorem scan_empty (fuel : Nat) (r : State) (empty : r.core.pending = []) :
    scan fuel r = ⟨1, r⟩ := by
  cases fuel <;> simp only [scan, empty]

theorem scan_step (fuel : Nat) (r : State) (nonempty : r.core.pending ≠ []) :
    scan (fuel + 1) r =
      ⟨1 + (bodyFuel r + (scan fuel (bodyResult r)).fuel), (scan fuel (bodyResult r)).state⟩ := by
  cases pending : r.core.pending with
  | nil => exact False.elim (nonempty pending)
  | cons bit rest => simp only [scan, pending]

theorem body_shorter (r : State) (nonempty : r.core.pending ≠ []) :
    (bodyResult r).core.pending.length < r.core.pending.length := by
  cases body_progress r nonempty with
  | inr shorter => exact shorter
  | inl stopped =>
      rw [stopped]
      cases pending : r.core.pending with
      | nil => exact False.elim (nonempty pending)
      | cons bit rest => simp only [List.length_nil, List.length_cons]; omega

theorem scan_exec (fuel : Nat) (r : State)
    (enough : r.core.pending.length < fuel ∨ r.core.pending = []) :
    Exec loop r.store (scan fuel r).fuel (scan fuel r).state.store := by
  induction fuel generalizing r with
  | zero =>
      have empty := enough.resolve_left (Nat.not_lt_zero _)
      exact Exec.loopStop empty
  | succ fuel ih =>
      cases pending : r.core.pending with
      | nil =>
          simpa only [loop, scan, pending] using
            (Exec.loopStop (source := (16 : Fin 23)) (body := body) (store := r.store) pending)
      | cons bit rest =>
          have nonempty : r.core.pending ≠ [] := by rw [pending]; intro h; cases h
          have size : r.core.pending.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have nextEnough : (bodyResult r).core.pending.length < fuel :=
            Nat.lt_of_lt_of_le (body_shorter r nonempty) size
          simpa only [loop, scan, pending] using
            Exec.loopStep (source := (16 : Fin 23)) (body := body) (before := r.store)
              pending (body_exec r) (ih (bodyResult r) (Or.inl nextEnough))

theorem scan_fuel_bound (fuel : Nat) (r : State) :
    (scan fuel r).fuel ≤ (stepBound r + 1) * fuel + 1 := by
  induction fuel generalizing r with
  | zero => simp only [scan, Nat.mul_zero]; exact Nat.le_refl _
  | succ fuel ih =>
      cases pending : r.core.pending with
      | nil => simp only [scan, pending]; omega
      | cons bit rest =>
          have nonempty : r.core.pending ≠ [] := by rw [pending]; intro h; cases h
          have first := bodyFuel_bound r
          have tail := ih (bodyResult r)
          have mono := Nat.mul_le_mul_right fuel (Nat.add_le_add_right (stepBound_mono r nonempty) 1)
          simp only [scan, pending, Nat.mul_succ]
          omega

theorem scan_stopped (fuel : Nat) (r : State)
    (enough : r.core.pending.length < fuel ∨ r.core.pending = []) : (scan fuel r).state.core.pending = [] := by
  induction fuel generalizing r with
  | zero => exact enough.resolve_left (Nat.not_lt_zero _)
  | succ fuel ih =>
      cases pending : r.core.pending with
      | nil => simp only [scan, pending]
      | cons bit rest =>
          have nonempty : r.core.pending ≠ [] := by rw [pending]; intro h; cases h
          have size : r.core.pending.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have nextEnough : (bodyResult r).core.pending.length < fuel :=
            Nat.lt_of_lt_of_le (body_shorter r nonempty) size
          simpa only [scan, pending] using ih (bodyResult r) (Or.inl nextEnough)

theorem scan_preserves (fuel : Nat) (r : State) :
    (scan fuel r).state.core.graph.core.formula = r.core.graph.core.formula ∧
      (scan fuel r).state.core.graph.core.matching = r.core.graph.core.matching := by
  induction fuel generalizing r with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
      cases pending : r.core.pending with
      | nil => simp only [scan, pending] <;> trivial
      | cons bit rest =>
          have first := body_preserves r
          have tail := ih (bodyResult r)
          simp only [scan, pending]
          exact ⟨tail.1.trans first.1, tail.2.trans first.2⟩

def whole (r : State) : ScanResult := scan (r.core.pending.length + 1) r
theorem whole_exec (r : State) : Exec loop r.store (whole r).fuel (whole r).state.store :=
  scan_exec _ r (Or.inl (Nat.lt_succ_self _))
theorem whole_fuel_bound (r : State) :
    (whole r).fuel ≤ (47 * r.core.pending.length + 125) * (r.core.pending.length + 1) + 1 :=
  scan_fuel_bound _ r
theorem whole_stopped (r : State) : (whole r).state.core.pending = [] :=
  scan_stopped _ r (Or.inl (Nat.lt_succ_self _))

end PNP.Concrete.NormalizerBlocks.TracePath

/-
Copyright (c) 2026 PNP Labs.

Whole ordered extraction loop with a decreasing raw cursor. A fixed
budget derived from the actual pending byte length suffices for every raw
state. The finite machine stops early at the first eligible vertex.
-/

import PNP.Concrete.NormalizerExtractStep

namespace PNP.Concrete.NormalizerBlocks.Extraction
open BitRegister

structure ScanResult where
  fuel : Nat
  state : State

def loop : Block 27 := .loop 25 body
def scan : Nat → State → ScanResult
  | 0, r => ⟨1, r⟩
  | fuel + 1, r =>
      match r.active with
      | [] => ⟨1, r⟩
      | _ :: _ =>
          let tail := scan fuel (bodyResult r)
          ⟨1 + (bodyFuel r + tail.fuel), tail.state⟩

theorem scan_empty (fuel : Nat) (r : State) (empty : r.active = []) : scan fuel r = ⟨1, r⟩ := by
  cases fuel <;> simp only [scan, empty]

theorem scan_step (fuel : Nat) (r : State) (nonempty : r.active ≠ []) :
    scan (fuel + 1) r =
      ⟨1 + (bodyFuel r + (scan fuel (bodyResult r)).fuel), (scan fuel (bodyResult r)).state⟩ := by
  cases active : r.active with
  | nil => exact False.elim (nonempty active)
  | cons bit rest => simp only [scan, active]

theorem scan_exec (fuel : Nat) (r : State) (enough : r.pending.length < fuel ∨ r.active = []) :
    Exec loop r.store (scan fuel r).fuel (scan fuel r).state.store := by
  induction fuel generalizing r with
  | zero =>
      have empty := enough.resolve_left (Nat.not_lt_zero _)
      exact Exec.loopStop empty
  | succ fuel ih =>
      cases active : r.active with
      | nil =>
          simpa only [loop, scan, active] using
            (Exec.loopStop (source := (25 : Fin 27)) (body := body) (store := r.store) active)
      | cons bit rest =>
          have nonempty : r.active ≠ [] := by rw [active]; intro h; cases h
          have size : r.pending.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have nextEnough : (bodyResult r).pending.length < fuel ∨ (bodyResult r).active = [] := by
            cases body_progress r with
            | inl stopped => exact Or.inr stopped
            | inr smaller => exact Or.inl (Nat.lt_of_lt_of_le smaller size)
          simpa only [loop, scan, active] using
            Exec.loopStep (source := (25 : Fin 27)) (body := body) (before := r.store)
              active (body_exec r) (ih (bodyResult r) nextEnough)

theorem scan_fuel_bound (fuel : Nat) (r : State) :
    (scan fuel r).fuel ≤ (stepBound r + 1) * fuel + 1 := by
  induction fuel generalizing r with
  | zero => simp only [scan, Nat.mul_zero]; exact Nat.le_refl _
  | succ fuel ih =>
      cases active : r.active with
      | nil => simp only [scan, active]; omega
      | cons bit rest =>
          have first := bodyFuel_bound r
          have tail := ih (bodyResult r)
          have mono := Nat.mul_le_mul_right fuel (Nat.add_le_add_right (stepBound_mono r) 1)
          simp only [scan, active, Nat.mul_succ]
          omega

theorem scan_stopped (fuel : Nat) (r : State) (enough : r.pending.length < fuel ∨ r.active = []) :
    (scan fuel r).state.active = [] := by
  induction fuel generalizing r with
  | zero => exact enough.resolve_left (Nat.not_lt_zero _)
  | succ fuel ih =>
      cases active : r.active with
      | nil => simp only [scan, active]
      | cons bit rest =>
          have nonempty : r.active ≠ [] := by rw [active]; intro h; cases h
          have size : r.pending.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have nextEnough : (bodyResult r).pending.length < fuel ∨ (bodyResult r).active = [] := by
            cases body_progress r with
            | inl stopped => exact Or.inr stopped
            | inr smaller => exact Or.inl (Nat.lt_of_lt_of_le smaller size)
          simpa only [scan, active] using ih (bodyResult r) nextEnough

theorem scan_preserves (fuel : Nat) (r : State) :
    (scan fuel r).state.parent.graph.core.formula = r.parent.graph.core.formula ∧
      (scan fuel r).state.parent.graph.core.matching = r.parent.graph.core.matching ∧
        (scan fuel r).state.trace = r.trace := by
  induction fuel generalizing r with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ fuel ih =>
      cases active : r.active with
      | nil => simp only [scan, active]; trivial
      | cons bit rest =>
          have first := body_preserves r
          have tail := ih (bodyResult r)
          simp only [scan, active]
          exact ⟨tail.1.trans first.1, tail.2.1.trans first.2.1, tail.2.2.trans first.2.2⟩

def whole (r : State) : ScanResult := scan (r.pending.length + 1) r
theorem whole_exec (r : State) : Exec loop r.store (whole r).fuel (whole r).state.store :=
  scan_exec _ r (Or.inl (Nat.lt_succ_self _))
theorem whole_fuel_bound (r : State) : (whole r).fuel ≤ (stepBound r + 1) * (r.pending.length + 1) + 1 :=
  scan_fuel_bound _ r
theorem whole_stopped (r : State) : (whole r).state.active = [] :=
  scan_stopped _ r (Or.inl (Nat.lt_succ_self _))

end PNP.Concrete.NormalizerBlocks.Extraction

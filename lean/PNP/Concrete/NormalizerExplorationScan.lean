/-
Copyright (c) 2026 PNP Labs.

Complete finite exploration loop. Its protected countdown is decreased
on discovery and cleared when no eligible vertex remains. The execution
theorem applies to arbitrary register contents without a supplied trace.
-/

import PNP.Concrete.NormalizerExplorationStep

namespace PNP.Concrete.NormalizerBlocks.Exploration
open BitRegister

theorem State.get_remaining (r : State) :
    r.store.get (Frame.frameIndex 27 (0 : Fin 1)) = r.remaining := by
  rw [State.store, Frame.get_frame]
  rfl

structure ScanResult where
  fuel : Nat
  state : State

def loop : Block 28 := .loop (Frame.frameIndex 27 (0 : Fin 1)) body
def scan : Nat → State → ScanResult
  | 0, r => ⟨1, r⟩
  | fuel + 1, r =>
      match r.remaining with
      | [] => ⟨1, r⟩
      | _ :: _ =>
          let tail := scan fuel (bodyResult r)
          ⟨1 + (bodyFuel r + tail.fuel), tail.state⟩

theorem scan_empty (fuel : Nat) (r : State) (empty : r.remaining = []) :
    scan fuel r = ⟨1, r⟩ := by
  cases fuel <;> simp only [scan, empty]

theorem scan_step (fuel : Nat) (r : State) (nonempty : r.remaining ≠ []) :
    scan (fuel + 1) r =
      ⟨1 + (bodyFuel r + (scan fuel (bodyResult r)).fuel), (scan fuel (bodyResult r)).state⟩ := by
  cases remaining : r.remaining with
  | nil => exact False.elim (nonempty remaining)
  | cons bit rest => simp only [scan, remaining]

theorem body_shorter (r : State) (nonempty : r.remaining ≠ []) :
    (bodyResult r).remaining.length < r.remaining.length := by
  cases body_progress r with
  | inl empty =>
      rw [empty]
      exact List.length_pos_iff.mpr nonempty
  | inr tail =>
      rw [tail, List.length_tail]
      have positive := List.length_pos_iff.mpr nonempty
      omega

theorem scan_exec (fuel : Nat) (r : State) (enough : r.remaining.length < fuel ∨ r.remaining = []) :
    Exec loop r.store (scan fuel r).fuel (scan fuel r).state.store := by
  induction fuel generalizing r with
  | zero =>
      have empty := enough.resolve_left (Nat.not_lt_zero _)
      exact Exec.loopStop ((State.get_remaining r).trans empty)
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil =>
          simpa only [loop, scan, remaining] using
            (Exec.loopStop (source := Frame.frameIndex 27 (0 : Fin 1)) (body := body)
              (store := r.store) ((State.get_remaining r).trans remaining))
      | cons bit rest =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro h; cases h
          have size : r.remaining.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have smaller := Nat.lt_of_lt_of_le (body_shorter r nonempty) size
          simpa only [loop, scan, remaining] using
            Exec.loopStep (source := Frame.frameIndex 27 (0 : Fin 1)) (body := body) (before := r.store)
              ((State.get_remaining r).trans remaining) (body_exec r) (ih (bodyResult r) (Or.inl smaller))

theorem scan_stopped (fuel : Nat) (r : State) (enough : r.remaining.length < fuel ∨ r.remaining = []) :
    (scan fuel r).state.remaining = [] := by
  induction fuel generalizing r with
  | zero => exact enough.resolve_left (Nat.not_lt_zero _)
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simp only [scan, remaining]
      | cons bit rest =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro h; cases h
          have size : r.remaining.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have smaller := Nat.lt_of_lt_of_le (body_shorter r nonempty) size
          simpa only [scan, remaining] using ih (bodyResult r) (Or.inl smaller)

theorem scan_preserves (fuel : Nat) (r : State) :
    (scan fuel r).state.core.parent.graph.core.formula = r.core.parent.graph.core.formula ∧
      (scan fuel r).state.core.parent.graph.core.matching = r.core.parent.graph.core.matching := by
  induction fuel generalizing r with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simp only [scan, remaining]; trivial
      | cons bit rest =>
          have first := body_preserves r
          have tail := ih (bodyResult r)
          simp only [scan, remaining]
          exact ⟨tail.1.trans first.1, tail.2.trans first.2⟩

def whole (r : State) : ScanResult := scan (r.remaining.length + 1) r
theorem whole_exec (r : State) : Exec loop r.store (whole r).fuel (whole r).state.store :=
  scan_exec _ r (Or.inl (Nat.lt_succ_self _))
theorem whole_stopped (r : State) : (whole r).state.remaining = [] :=
  scan_stopped _ r (Or.inl (Nat.lt_succ_self _))

end PNP.Concrete.NormalizerBlocks.Exploration

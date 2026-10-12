/-
Copyright (c) 2026 PNP Labs.

The complete range-selection loop consumes a finite input counter. Its trace
stays fixed, its index increases exactly once per iteration, and its runtime
bound covers every register state rather than only canonical trace packets.
-/
import PNP.Concrete.NormalizerCutSelectionStep

namespace PNP.Concrete.NormalizerBlocks.CutSelection
open BitRegister

structure LoopResult where
  fuel : Nat
  state : State

theorem State.remaining_update (r : State) (word : BitString) (same : r.remaining = word) :
    {r with remaining := word} = r := by
  cases same
  rfl

def loop (tag : Bool) : Block 24 := .loop 22 (step tag)
def run (tag : Bool) : BitString → State → LoopResult
  | [], r => ⟨1, {r with remaining := []}⟩
  | bit :: rest, r =>
    let before := {r with remaining := bit :: rest}
    let next := stepped tag before
    let tail := run tag rest next
    ⟨1 + (stepFuel before + tail.fuel), tail.state⟩

theorem run_exec (tag : Bool) (word : BitString) (r : State) :
    Exec (loop tag) ({r with remaining := word}).store (run tag word r).fuel
      (run tag word r).state.store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons bit rest ih =>
    let before : State := {r with remaining := bit :: rest}
    let next := stepped tag before
    have nextRemaining : next.remaining = rest := (stepped_frame tag before).2.1
    have restored := State.remaining_update next rest nextRemaining
    have tail := ih next
    rw [restored] at tail
    exact Exec.loopStep (source := (22 : Fin 24)) (body := step tag)
      (before := before.store) rfl (step_exec tag before) tail

theorem run_trace (tag : Bool) (word : BitString) (r : State) :
    (run tag word r).state.trace = r.trace := by
  induction word generalizing r with
  | nil => rfl
  | cons bit rest ih =>
    exact (ih (stepped tag {r with remaining := bit :: rest})).trans
      (stepped_frame tag {r with remaining := bit :: rest}).1

theorem run_tag (tag : Bool) (word : BitString) (r : State) :
    (run tag word r).state.core.targetTag = r.core.targetTag := by
  induction word generalizing r with
  | nil => rfl
  | cons bit rest ih =>
    exact (ih (stepped tag {r with remaining := bit :: rest})).trans
      (stepped_frame tag {r with remaining := bit :: rest}).2.2.2

theorem run_stopped (tag : Bool) (word : BitString) (r : State) :
    (run tag word r).state.remaining = [] := by
  induction word generalizing r with
  | nil => rfl
  | cons bit rest ih => exact ih (stepped tag {r with remaining := bit :: rest})

theorem run_index_length (tag : Bool) (word : BitString) (r : State) :
    (run tag word r).state.core.targetIndex.length = r.core.targetIndex.length + word.length := by
  induction word generalizing r with
  | nil => exact (Nat.add_zero _).symm
  | cons bit rest ih =>
    let before : State := {r with remaining := bit :: rest}
    let next := stepped tag before
    have tail := ih next
    rw [(stepped_frame tag before).2.2.1, List.length_cons] at tail
    change (run tag rest next).state.core.targetIndex.length = r.core.targetIndex.length + (rest.length + 1)
    change (run tag rest next).state.core.targetIndex.length =
      (r.core.targetIndex.length + 1) + rest.length at tail
    omega

theorem run_fuel_bound (tag : Bool) (word : BitString) (r : State) :
    (run tag word r).fuel ≤
      (stepBound r.trace.length (r.core.targetIndex.length + word.length) + 1) * word.length + 1 := by
  induction word generalizing r with
  | nil => simp only [run, List.length_nil, Nat.mul_zero]; exact Nat.le_refl _
  | cons bit rest ih =>
    let before : State := {r with remaining := bit :: rest}
    let next := stepped tag before
    have tail := ih next
    rw [(stepped_frame tag before).1, (stepped_frame tag before).2.2.1, List.length_cons] at tail
    change (run tag rest next).fuel ≤
      (stepBound r.trace.length (r.core.targetIndex.length + 1 + rest.length) + 1) * rest.length + 1 at tail
    have factor : stepBound r.trace.length (r.core.targetIndex.length + 1 + rest.length) + 1 =
        stepBound r.trace.length (r.core.targetIndex.length + (rest.length + 1)) + 1 := by
      unfold stepBound
      omega
    rw [factor] at tail
    have first := stepFuel_bound before
    have wider : stepBound r.trace.length r.core.targetIndex.length ≤
        stepBound r.trace.length (r.core.targetIndex.length + (rest.length + 1)) := by
      unfold stepBound
      omega
    change stepFuel before ≤ stepBound r.trace.length r.core.targetIndex.length at first
    change 1 + (stepFuel before + (run tag rest next).fuel) ≤
      (stepBound r.trace.length (r.core.targetIndex.length + (rest.length + 1)) + 1) * (rest.length + 1) + 1
    rw [Nat.mul_succ]
    omega

def whole (tag : Bool) (r : State) : LoopResult := run tag r.remaining r
theorem whole_exec (tag : Bool) (r : State) :
    Exec (loop tag) r.store (whole tag r).fuel (whole tag r).state.store := run_exec tag r.remaining r
theorem whole_fuel_bound (tag : Bool) (r : State) :
    (whole tag r).fuel ≤
      (stepBound r.trace.length (r.core.targetIndex.length + r.remaining.length) + 1) * r.remaining.length + 1 :=
  run_fuel_bound tag r.remaining r

end PNP.Concrete.NormalizerBlocks.CutSelection

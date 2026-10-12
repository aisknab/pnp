/-
Copyright (c) 2026 PNP Labs.

A fixed loop emits the entire increasing tagged range. Its counter is a
finite input word; its index grows by one at each iteration. The cost bound
accounts for every unary index bit and is uniform over all register states.
-/

import PNP.Concrete.NormalizerVertexEmission

namespace PNP.Concrete.NormalizerBlocks.SearchVertices

open BitRegister Occurrence

def loop (tag : Bool) : Block 9 := .loop 2 (step tag)

def run (tag : Bool) : BitString → Registers → Result
  | [], r => ⟨1, {r with remaining := []}⟩
  | bit :: rest, r =>
      let next := advanced tag {r with remaining := bit :: rest}
      let tail := run tag rest next
      ⟨1 + ((4 * r.target.length + 12) + tail.fuel), tail.state⟩

theorem run_exec (tag : Bool) (word : BitString) (r : Registers) :
    Exec (loop tag) ({r with remaining := word}).store (run tag word r).fuel
      (run tag word r).state.store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons bit rest ih =>
      exact Exec.loopStep (source := (2 : Fin 9)) (body := step tag)
        (before := ({r with remaining := bit :: rest}).store) rfl
        (step_exec tag {r with remaining := bit :: rest})
        (ih (advanced tag {r with remaining := bit :: rest}))

theorem run_input (tag : Bool) (word : BitString) (r : Registers) :
    (run tag word r).state.input = r.input := by
  induction word generalizing r with
  | nil => rfl
  | cons bit rest ih => exact ih (advanced tag {r with remaining := bit :: rest})

theorem run_stopped (tag : Bool) (word : BitString) (r : Registers) :
    (run tag word r).state.remaining = [] := by
  induction word generalizing r with
  | nil => rfl
  | cons bit rest ih => exact ih (advanced tag {r with remaining := bit :: rest})

theorem run_excess (tag : Bool) (word : BitString) (r : Registers) :
    (run tag word r).state.excess =
      (rangeBits tag word.length r.target.length).reverse ++ r.excess := by
  induction word generalizing r with
  | nil => rfl
  | cons bit rest ih =>
      simpa only [run, advanced, emitted, List.length_cons, rangeBits,
        List.reverse_append, List.append_assoc] using
        ih (advanced tag {r with remaining := bit :: rest})

theorem run_target_length (tag : Bool) (word : BitString) (r : Registers) :
    (run tag word r).state.target.length = r.target.length + word.length := by
  induction word generalizing r with
  | nil => simp only [run, List.length_nil, Nat.add_zero]
  | cons bit rest ih =>
      have tail := ih (advanced tag {r with remaining := bit :: rest})
      change (run tag rest (advanced tag {r with remaining := bit :: rest})).state.target.length =
        (r.target.length + 1) + rest.length at tail
      change (run tag rest (advanced tag {r with remaining := bit :: rest})).state.target.length =
        r.target.length + (rest.length + 1)
      omega

theorem run_fuel_bound (tag : Bool) (word : BitString) (r : Registers) :
    (run tag word r).fuel ≤ (4 * (r.target.length + word.length) + 13) * word.length + 1 := by
  induction word generalizing r with
  | nil => exact Nat.le_refl _
  | cons bit rest ih =>
      have tail := ih (advanced tag {r with remaining := bit :: rest})
      change (run tag rest (advanced tag {r with remaining := bit :: rest})).fuel ≤
        (4 * (r.target.length + 1 + rest.length) + 13) * rest.length + 1 at tail
      have factor : 4 * (r.target.length + 1 + rest.length) + 13 =
          4 * (r.target.length + (rest.length + 1)) + 13 := by omega
      rw [factor] at tail
      simp only [run, List.length_cons, Nat.mul_succ]
      omega

def whole (tag : Bool) (r : Registers) : Result := run tag r.remaining r

theorem whole_exec (tag : Bool) (r : Registers) :
    Exec (loop tag) r.store (whole tag r).fuel (whole tag r).state.store := run_exec tag r.remaining r

theorem whole_input (tag : Bool) (r : Registers) : (whole tag r).state.input = r.input :=
  run_input tag r.remaining r

theorem whole_excess (tag : Bool) (r : Registers) :
    (whole tag r).state.excess =
      (rangeBits tag r.remaining.length r.target.length).reverse ++ r.excess := run_excess tag r.remaining r

theorem whole_fuel_bound (tag : Bool) (r : Registers) :
    (whole tag r).fuel ≤ (4 * (r.target.length + r.remaining.length) + 13) * r.remaining.length + 1 :=
  run_fuel_bound tag r.remaining r

end PNP.Concrete.NormalizerBlocks.SearchVertices

/-
Copyright (c) 2026 PNP Labs.

Finite comparison of disposable unary-counter words. The existing
occurrence-unit operation subtracts one unit at a time; equality requires
both residual counters to be empty. The original words are not supplied
as equality answers, and the loop is bounded on every raw word.
-/

import PNP.Concrete.NormalizerParentPolynomial

namespace PNP.Concrete.NormalizerBlocks.TraceCount

open BitRegister Occurrence

def step : Block 9 := .seq (.action (.pop 1)) unit
def loop : Block 9 := .loop 1 step
def drained (word : BitString) (r : Registers) : Registers :=
  {r with target := [], remaining := r.remaining.drop word.length, excess := List.replicate (word.length - r.remaining.length) true ++ r.excess}

theorem drain_exec (word : BitString) (r : Registers) :
    Exec loop ({r with target := word}).store (4 * word.length + 1) (drained word r).store := by
  induction word generalizing r with
  | nil =>
      have same : drained [] r = {r with target := []} := by
        simp only [drained, List.length_nil, List.drop_zero, Nat.zero_sub, List.replicate_zero, List.nil_append]
      rw [same]
      exact Exec.loopStop (source := (1 : Fin 9)) rfl
  | cons bit rest ih =>
      have cost : 4 * (bit :: rest).length + 1 = 1 + (3 + (4 * rest.length + 1)) := by
        simp only [List.length_cons]
        omega
      rw [cost]
      cases r with
      | mk input target remaining excess sign mode active reserved output =>
          cases remaining with
          | nil =>
              have checked := Exec.loopStep (source := (1 : Fin 9)) (body := step)
                (before := Registers.store ⟨input, bit :: rest, [], excess, sign, mode, active, reserved, output⟩)
                rfl
                (Exec.seq (.action _ _) (unit_exec ⟨input, rest, [], excess, sign, mode, active, reserved, output⟩))
                (ih ⟨input, rest, [], true :: excess, sign, mode, active, reserved, output⟩)
              simpa only [loop, drained, List.length_cons, List.length_nil, Nat.sub_zero, List.drop_nil,
                List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append] using checked
          | cons other tail =>
              have checked := Exec.loopStep (source := (1 : Fin 9)) (body := step)
                (before := Registers.store ⟨input, bit :: rest, other :: tail, excess, sign, mode, active, reserved, output⟩)
                rfl
                (Exec.seq (.action _ _) (unit_exec ⟨input, rest, other :: tail, excess, sign, mode, active, reserved, output⟩))
                (ih ⟨input, rest, tail, excess, sign, mode, active, reserved, output⟩)
              simpa only [loop, drained, List.length_cons, List.drop_succ_cons, Nat.succ_sub_succ_eq_sub] using checked

def emit (value : Bool) : Block 9 := .seq (.action (.clear 8)) (.action (.push 8 value))
def emitted (value : Bool) (r : Registers) : Registers := {r with output := [value]}
theorem emit_exec (value : Bool) (r : Registers) : Exec (emit value) r.store 2 (emitted value r).store :=
  Exec.seq (.action _ _) (.action _ _)

def finish : Block 9 := .branch 3 (.branch 2 (emit true) (emit false) (emit false)) (emit false) (emit false)
def finished (r : Registers) : Registers := emitted (r.remaining.isEmpty && r.excess.isEmpty) r
def finishFuel (r : Registers) : Nat := if r.excess.isEmpty then 4 else 3

theorem finish_exec (r : Registers) : Exec finish r.store (finishFuel r) (finished r).store := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases excess with
      | nil =>
          cases remaining with
          | nil => exact Exec.empty (source := (3 : Fin 9)) rfl (Exec.empty (source := (2 : Fin 9)) rfl (emit_exec true _))
          | cons bit rest => exact Exec.empty (source := (3 : Fin 9)) rfl (Exec.nonempty (source := (2 : Fin 9)) rfl (emit_exec false _))
      | cons bit rest =>
          cases remaining <;> exact Exec.nonempty (source := (3 : Fin 9)) rfl (emit_exec false _)

theorem finishFuel_bound (r : Registers) : finishFuel r ≤ 4 := by
  unfold finishFuel
  cases r.excess.isEmpty <;> decide

def block : Block 9 := .seq loop finish
def result (r : Registers) : Registers := finished (drained r.target r)
def fuel (r : Registers) : Nat := 4 * r.target.length + 1 + finishFuel (drained r.target r)
theorem block_exec (r : Registers) : Exec block r.store (fuel r) (result r).store :=
  Exec.seq (drain_exec r.target r) (finish_exec (drained r.target r))
theorem fuel_bound (r : Registers) : fuel r ≤ 4 * r.target.length + 5 := by
  have bound := finishFuel_bound (drained r.target r)
  unfold fuel
  omega

theorem empty_length (word : BitString) : word.isEmpty = (word.length == 0) := by
  cases word <;> rfl

theorem residuals_equal (left right : Nat) :
    ((right - left == 0) && (left - right == 0)) = (left == right) := by
  by_cases same : left = right
  · subst right
    have self : (left == left) = true := beq_iff_eq.mpr rfl
    rw [self, Nat.sub_self]
    rfl
  · have different : (left == right) = false := beq_eq_false_iff_ne.mpr same
    rw [different]
    cases first : right - left == 0 <;> cases second : left - right == 0
    · rfl
    · rfl
    · rfl
    · have firstZero : right - left = 0 := beq_iff_eq.mp first
      have secondZero : left - right = 0 := beq_iff_eq.mp second
      exact False.elim (same (by omega))

theorem result_output (r : Registers) (empty : r.excess = []) :
    (result r).output = [r.target.length == r.remaining.length] := by
  change [(r.remaining.drop r.target.length).isEmpty &&
    (List.replicate (r.target.length - r.remaining.length) true ++ r.excess).isEmpty] = _
  rw [empty, List.append_nil, empty_length, empty_length, List.length_drop, List.length_replicate, residuals_equal]

end PNP.Concrete.NormalizerBlocks.TraceCount

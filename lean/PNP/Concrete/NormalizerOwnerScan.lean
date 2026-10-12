/-
Copyright (c) 2026 PNP Labs.

Whole raw-word inverse-table scanning. The finite loop consumes a token pair
or stops on every live iteration, including truncated and malformed input.
The linear register-step bound does not assume a valid matching table.
-/

import PNP.Concrete.NormalizerOwnerOperations

namespace PNP.Concrete.NormalizerBlocks.TableOwner

open BitRegister Occurrence

def second (first : Bool) : Block 9 :=
  if first then
    .branch 0 stop (.seq (.action (.pop 0)) (token .finish)) (.seq (.action (.pop 0)) (token .t))
  else
    .branch 0 stop (.seq (.action (.pop 0)) (token .f)) (.seq (.action (.pop 0)) (token .sep))

def pair : Block 9 :=
  .branch 0 stop (.seq (.action (.pop 0)) (second false)) (.seq (.action (.pop 0)) (second true))

def pairResult (r : Registers) : Result :=
  match r.input with
  | [] => ⟨2, {r with active := []}⟩
  | [_] => ⟨4, {r with input := [], active := []}⟩
  | first :: second :: rest =>
      let read := tokenResult (CNFToken.ofBits first second) {r with input := rest}
      {read with fuel := 4 + read.fuel}

private theorem four_add (fuel : Nat) : 4 + fuel = 1 + (1 + (1 + (1 + fuel))) := by omega

theorem pair_exec (r : Registers) :
    Exec pair r.store (pairResult r).fuel (pairResult r).state.store := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases input with
      | nil => exact Exec.empty (source := (0 : Fin 9)) rfl (.action _ _)
      | cons first tail =>
          cases tail with
          | nil =>
              cases first
              · exact Exec.zero (source := (0 : Fin 9)) rfl (Exec.seq (.action _ _) (Exec.empty (source := (0 : Fin 9)) rfl (.action _ _)))
              · exact Exec.one (source := (0 : Fin 9)) rfl (Exec.seq (.action _ _) (Exec.empty (source := (0 : Fin 9)) rfl (.action _ _)))
          | cons second rest =>
              cases first <;> cases second
              · simp only [pairResult, CNFToken.ofBits, four_add]
                exact Exec.zero (source := (0 : Fin 9)) rfl (Exec.seq (.action (.pop 0)
                  (Registers.store ⟨false :: false :: rest, target, remaining, excess, sign, mode, active, reserved, output⟩))
                  (Exec.zero (source := (0 : Fin 9)) rfl (Exec.seq (.action (.pop 0) _) (token_exec .f ⟨rest, target, remaining, excess, sign, mode, active, reserved, output⟩))))
              · simp only [pairResult, CNFToken.ofBits, four_add]
                exact Exec.zero (source := (0 : Fin 9)) rfl (Exec.seq (.action (.pop 0)
                  (Registers.store ⟨false :: true :: rest, target, remaining, excess, sign, mode, active, reserved, output⟩))
                  (Exec.one (source := (0 : Fin 9)) rfl (Exec.seq (.action (.pop 0) _) (token_exec .sep ⟨rest, target, remaining, excess, sign, mode, active, reserved, output⟩))))
              · simp only [pairResult, CNFToken.ofBits, four_add]
                exact Exec.one (source := (0 : Fin 9)) rfl (Exec.seq (.action (.pop 0)
                  (Registers.store ⟨true :: false :: rest, target, remaining, excess, sign, mode, active, reserved, output⟩))
                  (Exec.zero (source := (0 : Fin 9)) rfl (Exec.seq (.action (.pop 0) _) (token_exec .finish ⟨rest, target, remaining, excess, sign, mode, active, reserved, output⟩))))
              · simp only [pairResult, CNFToken.ofBits, four_add]
                exact Exec.one (source := (0 : Fin 9)) rfl (Exec.seq (.action (.pop 0)
                  (Registers.store ⟨true :: true :: rest, target, remaining, excess, sign, mode, active, reserved, output⟩))
                  (Exec.one (source := (0 : Fin 9)) rfl (Exec.seq (.action (.pop 0) _) (token_exec .t ⟨rest, target, remaining, excess, sign, mode, active, reserved, output⟩))))

theorem pair_fuel_bound (r : Registers) : (pairResult r).fuel ≤ 11 := by
  cases input : r.input with
  | nil => simp only [pairResult, input]; decide
  | cons first tail =>
      cases tail with
      | nil => simp only [pairResult, input]; decide
      | cons second rest =>
          have h := token_fuel_bound (CNFToken.ofBits first second) {r with input := rest}
          simp only [pairResult, input]
          omega

theorem pair_progress (r : Registers) :
    (pairResult r).state.active = [] ∨ (pairResult r).state.input.length < r.input.length := by
  cases input : r.input with
  | nil => exact Or.inl (by simp only [pairResult, input])
  | cons first tail =>
      cases tail with
      | nil => exact Or.inl (by simp only [pairResult, input])
      | cons second rest =>
          apply Or.inr
          simp only [pairResult, input, token_input, List.length_cons]
          omega

def loop : Block 9 := .loop 6 pair

def scan : Nat → Registers → Result
  | 0, r => ⟨1, r⟩
  | fuel + 1, r =>
      match r.active with
      | [] => ⟨1, r⟩
      | _ :: _ =>
          let first := pairResult r
          let tail := scan fuel first.state
          ⟨1 + (first.fuel + tail.fuel), tail.state⟩

theorem scan_exec (fuel : Nat) (r : Registers)
    (enough : r.input.length < fuel ∨ r.active = []) :
    Exec loop r.store (scan fuel r).fuel (scan fuel r).state.store := by
  induction fuel generalizing r with
  | zero =>
      have empty : r.active = [] := enough.resolve_left (Nat.not_lt_zero _)
      exact Exec.loopStop empty
  | succ fuel ih =>
      cases active : r.active with
      | nil => simpa only [loop, scan, active] using (Exec.loopStop (source := (6 : Fin 9)) (body := pair) (store := r.store) active)
      | cons bit rest =>
          have size : r.input.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => rw [active] at h; cases h
          have nextEnough : (pairResult r).state.input.length < fuel ∨ (pairResult r).state.active = [] := by
            cases pair_progress r with
            | inl stopped => exact Or.inr stopped
            | inr smaller => exact Or.inl (Nat.lt_of_lt_of_le smaller size)
          have tail := ih (pairResult r).state nextEnough
          simpa only [loop, scan, active] using Exec.loopStep (source := (6 : Fin 9)) (body := pair) (before := r.store) active (pair_exec r) tail

theorem scan_fuel_bound (fuel : Nat) (r : Registers) : (scan fuel r).fuel ≤ 12 * fuel + 1 := by
  induction fuel generalizing r with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      cases active : r.active with
      | nil => simp only [scan, active]; omega
      | cons bit rest =>
          have first := pair_fuel_bound r
          have tail := ih (pairResult r).state
          simp only [scan, active]
          omega

theorem scan_stopped (fuel : Nat) (r : Registers)
    (enough : r.input.length < fuel ∨ r.active = []) : (scan fuel r).state.active = [] := by
  induction fuel generalizing r with
  | zero => exact enough.resolve_left (Nat.not_lt_zero _)
  | succ fuel ih =>
      cases active : r.active with
      | nil => simp only [scan, active]
      | cons bit rest =>
          have size : r.input.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => rw [active] at h; cases h
          have nextEnough : (pairResult r).state.input.length < fuel ∨ (pairResult r).state.active = [] := by
            cases pair_progress r with
            | inl stopped => exact Or.inr stopped
            | inr smaller => exact Or.inl (Nat.lt_of_lt_of_le smaller size)
          simpa only [scan, active] using ih (pairResult r).state nextEnough

def queryResult (r : Registers) : Result := scan (r.input.length + 1) r

theorem query_exec (r : Registers) :
    Exec loop r.store (queryResult r).fuel (queryResult r).state.store :=
  scan_exec _ r (Or.inl (Nat.lt_succ_self _))

theorem query_fuel_bound (r : Registers) :
    (queryResult r).fuel ≤ 12 * (r.input.length + 1) + 1 := scan_fuel_bound _ r

theorem query_stopped (r : Registers) : (queryResult r).state.active = [] :=
  scan_stopped _ r (Or.inl (Nat.lt_succ_self _))

end PNP.Concrete.NormalizerBlocks.TableOwner

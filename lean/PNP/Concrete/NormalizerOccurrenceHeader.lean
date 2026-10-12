/-
Copyright (c) 2026 PNP Labs.

The occurrence query's unary input header is read by a finite loop. The
header is input data, not a supplied numeric parameter or a unit-cost oracle.
-/

import PNP.Concrete.NormalizerOccurrenceScan

namespace PNP.Concrete.NormalizerBlocks.Occurrence

open BitRegister

def headerBody : Block 9 :=
  .branch 0 stop (.seq (.action (.pop 0)) stop)
    (.seq (.action (.pop 0)) (.action (.push 1 true)))

def headerLoop : Block 9 := .loop 6 headerBody

theorem header_empty_exec (r : Registers) :
    Exec headerBody ({r with input := []}).store 2 ({r with input := [], active := []}).store :=
  Exec.empty (source := (0 : Fin 9)) rfl (.action _ _)

theorem header_false_exec (r : Registers) (rest : BitString) :
    Exec headerBody ({r with input := false :: rest}).store 3
      ({r with input := rest, active := []}).store :=
  Exec.zero (source := (0 : Fin 9)) rfl (Exec.seq (.action _ _) (.action _ _))

theorem header_true_exec (r : Registers) (rest : BitString) :
    Exec headerBody ({r with input := true :: rest}).store 3
      ({r with input := rest, target := true :: r.target}).store :=
  Exec.one (source := (0 : Fin 9)) rfl (Exec.seq (.action _ _) (.action _ _))

def headerResult (input : BitString) (r : Registers) : Result :=
  match r.active with
  | [] => ⟨1, {r with input := input}⟩
  | _ :: _ =>
      match input with
      | [] => ⟨1 + (2 + 1), {r with input := [], active := []}⟩
      | false :: rest => ⟨1 + (3 + 1), {r with input := rest, active := []}⟩
      | true :: rest =>
          let tail := headerResult rest {r with target := true :: r.target}
          ⟨1 + (3 + tail.fuel), tail.state⟩
termination_by structural input

theorem header_exec (input : BitString) (r : Registers) :
    Exec headerLoop ({r with input := input}).store (headerResult input r).fuel
      (headerResult input r).state.store := by
  cases r with
  | mk original target remaining excess sign mode active reserved output =>
      induction input generalizing target with
      | nil =>
          cases active with
          | nil => exact Exec.loopStop rfl
          | cons bit tail =>
              exact Exec.loopStep (source := (6 : Fin 9)) (body := headerBody)
                (before := Registers.store ⟨[], target, remaining, excess, sign, mode, bit :: tail, reserved, output⟩)
                rfl (header_empty_exec ⟨original, target, remaining, excess, sign, mode, bit :: tail, reserved, output⟩)
                (Exec.loopStop rfl)
      | cons first rest ih =>
          cases first
          · cases active with
            | nil => exact Exec.loopStop rfl
            | cons bit tail =>
                exact Exec.loopStep (source := (6 : Fin 9)) (body := headerBody)
                  (before := Registers.store ⟨false :: rest, target, remaining, excess, sign, mode, bit :: tail, reserved, output⟩)
                  rfl (header_false_exec ⟨original, target, remaining, excess, sign, mode, bit :: tail, reserved, output⟩ rest)
                  (Exec.loopStop rfl)
          · cases active with
            | nil => exact Exec.loopStop rfl
            | cons bit tail =>
                exact Exec.loopStep (source := (6 : Fin 9)) (body := headerBody)
                  (before := Registers.store ⟨true :: rest, target, remaining, excess, sign, mode, bit :: tail, reserved, output⟩)
                  rfl (header_true_exec ⟨original, target, remaining, excess, sign, mode, bit :: tail, reserved, output⟩ rest)
                  (ih (true :: target))

theorem header_fuel_bound (input : BitString) (r : Registers) :
    (headerResult input r).fuel ≤ 4 * input.length + 5 := by
  cases r with
  | mk original target remaining excess sign mode active reserved output =>
      induction input generalizing target with
      | nil => cases active <;> simp only [headerResult, List.length_nil] <;> omega
      | cons first rest ih =>
          cases first
          · cases active <;> simp only [headerResult, List.length_cons] <;> omega
          · cases active with
            | nil => simp only [headerResult, List.length_cons]; omega
            | cons bit tail =>
                have h := ih (true :: target)
                simp only [headerResult, List.length_cons]
                omega

theorem header_input_bound (input : BitString) (r : Registers) :
    (headerResult input r).state.input.length ≤ input.length := by
  cases r with
  | mk original target remaining excess sign mode active reserved output =>
      induction input generalizing target with
      | nil => cases active <;> exact Nat.le_refl _
      | cons first rest ih =>
          cases first
          · cases active <;> simp only [headerResult, List.length_cons] <;> omega
          · cases active with
            | nil => exact Nat.le_refl _
            | cons bit tail =>
                have h := ih (true :: target)
                simp only [headerResult, List.length_cons]
                omega

theorem header_stopped (input : BitString) (r : Registers) :
    (headerResult input r).state.active = [] := by
  cases r with
  | mk original target remaining excess sign mode active reserved output =>
      induction input generalizing target with
      | nil => cases active <;> rfl
      | cons first rest ih =>
          cases first
          · cases active <;> rfl
          · cases active with
            | nil => rfl
            | cons bit tail => exact ih (true :: target)

end PNP.Concrete.NormalizerBlocks.Occurrence

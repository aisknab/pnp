/-
Copyright (c) 2026 PNP Labs.

Proof-only token traces for the whole-table writer. Every trace is realized
by the fixed raw-input program; it is not a supplied execution oracle.
-/

import PNP.Concrete.NormalizerTablePolynomial

namespace PNP.Concrete.NormalizerBlocks.TableWrite

open BitRegister Occurrence

def tokenScan (values : List CNFToken) (r : Registers) : Registers :=
  match r.active with
  | [] => {r with input := encodeTokenPairs values}
  | _ :: _ =>
      match values with
      | [] => {r with input := [], active := []}
      | value :: rest => tokenScan rest (tokenResult value {r with input := []}).state
termination_by structural values

theorem pair_token_exec (value : CNFToken) (rest : List CNFToken) (r : Registers) :
    Exec pair ({r with input := encodeTokenPairs (value :: rest)}).store
      (4 + (tokenResult value {r with input := encodeTokenPairs rest}).fuel)
      ({(tokenResult value {r with input := []}).state with input := encodeTokenPairs rest}).store := by
  have checked := pair_exec {r with input := encodeTokenPairs (value :: rest)}
  have decoded : pairResult {r with input := encodeTokenPairs (value :: rest)} =
      ⟨4 + (tokenResult value {r with input := encodeTokenPairs rest}).fuel,
        (tokenResult value {r with input := encodeTokenPairs rest}).state⟩ := by
    cases value <;> rfl
  rw [decoded] at checked
  rw [token_result_input] at checked
  exact checked

theorem tokenScan_exec (values : List CNFToken) (r : Registers) :
    ∃ fuel, Exec loop ({r with input := encodeTokenPairs values}).store fuel (tokenScan values r).store := by
  induction values generalizing r with
  | nil =>
      cases r with
      | mk input target remaining excess sign mode active reserved output =>
          cases active with
          | nil => exact ⟨1, Exec.loopStop rfl⟩
          | cons bit tail =>
              exact ⟨1 + (2 + 1), Exec.loopStep (source := (6 : Fin 9)) (body := pair)
                (before := Registers.store ⟨[], target, remaining, excess, sign, mode, bit :: tail, reserved, output⟩)
                rfl (pair_exec ⟨[], target, remaining, excess, sign, mode, bit :: tail, reserved, output⟩)
                (Exec.loopStop rfl)⟩
  | cons value rest ih =>
      cases r with
      | mk input target remaining excess sign mode active reserved output =>
          cases active with
          | nil => exact ⟨1, Exec.loopStop rfl⟩
          | cons bit tail =>
              obtain ⟨fuel, checked⟩ := ih (tokenResult value
                ⟨[], target, remaining, excess, sign, mode, bit :: tail, reserved, output⟩).state
              exact ⟨1 + ((4 + (tokenResult value
                ⟨encodeTokenPairs rest, target, remaining, excess, sign, mode, bit :: tail, reserved, output⟩).fuel) + fuel),
                Exec.loopStep (source := (6 : Fin 9)) (body := pair)
                  (before := Registers.store
                    ⟨encodeTokenPairs (value :: rest), target, remaining, excess, sign, mode, bit :: tail, reserved, output⟩)
                  rfl (pair_token_exec value rest
                    ⟨input, target, remaining, excess, sign, mode, bit :: tail, reserved, output⟩) checked⟩

theorem tokenScan_inactive (values : List CNFToken) (r : Registers) (inactive : r.active = []) :
    tokenScan values r = {r with input := encodeTokenPairs values} := by
  cases values <;> simp only [tokenScan, inactive]

end PNP.Concrete.NormalizerBlocks.TableWrite

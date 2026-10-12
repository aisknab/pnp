/-
Copyright (c) 2026 PNP Labs.

A proof-only token trace of the concrete occurrence scanner. Every trace is
realized by the already bounded finite program; it is not an instruction,
an oracle, or a premise supplied to the compiled query.
-/

import PNP.Concrete.NormalizerOccurrencePolynomial

namespace PNP.Concrete.NormalizerBlocks.Occurrence

open BitRegister

def tokenScan (values : List CNFToken) (r : Registers) : Registers :=
  match r.active with
  | [] => {r with input := encodeTokenPairs values}
  | _ :: _ =>
      match values with
      | [] => {r with input := [], active := []}
      | value :: rest => tokenScan rest (tokenResult value {r with input := []}).state
termination_by structural values

theorem token_result_input (value : CNFToken) (r : Registers) (bits : BitString) :
    (tokenResult value {r with input := bits}).state =
      {(tokenResult value {r with input := []}).state with input := bits} := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases value with
      | sep => rfl
      | finish => rfl
      | t => cases mode <;> simp only [tokenResult, startState, unitState] <;> split <;> rfl
      | f =>
          cases mode with
          | nil => rfl
          | cons head tail => cases excess with
              | cons head tail => rfl
              | nil => cases remaining <;> rfl

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

def counting (target : BitString) (remaining excess : Nat) (sign reserved output : BitString) : Registers :=
  ⟨[], target, List.replicate remaining true, List.replicate excess true,
    sign, [true], [true], reserved, output⟩

theorem tokenScan_unary (index remaining excess : Nat) (target sign reserved output : BitString)
    (rest : List CNFToken) :
    tokenScan (encodeUnaryTokens index ++ rest) (counting target remaining excess sign reserved output) =
      tokenScan (.f :: rest) (counting target (remaining - index) (excess + (index - remaining)) sign reserved output) := by
  induction index generalizing remaining excess with
  | zero =>
      simp only [encodeUnaryTokens, List.cons_append, List.nil_append, Nat.sub_zero, Nat.zero_sub, Nat.add_zero]
  | succ index ih =>
      cases remaining with
      | zero =>
          have step := ih 0 (excess + 1)
          have equal : excess + 1 + (index - 0) = excess + (index + 1 - 0) := by omega
          simpa only [encodeUnaryTokens, List.cons_append, tokenScan, counting, tokenResult,
            unitState, List.replicate_zero, List.replicate_succ, Nat.zero_sub, equal] using step
      | succ remaining =>
          simpa only [encodeUnaryTokens, List.cons_append, tokenScan, counting, tokenResult,
            unitState, List.replicate_succ, Nat.succ_sub_succ_eq_sub] using ih remaining excess

end PNP.Concrete.NormalizerBlocks.Occurrence

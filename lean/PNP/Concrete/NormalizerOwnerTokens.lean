/-
Copyright (c) 2026 PNP Labs.

Token-level reasoning for the fixed owner scanner. These traces justify
executions of the finite program; they are not supplied runtime instructions.
Unary comparison and early stopping preserve the source's first-match order.
-/

import PNP.Concrete.NormalizerOwnerPolynomial

namespace PNP.Concrete.NormalizerBlocks.TableOwner

open BitRegister Occurrence

def tokenScan (values : List CNFToken) (r : Registers) : Registers :=
  match r.active with
  | [] => {r with input := encodeTokenPairs values}
  | _ :: _ =>
      match values with
      | [] => {r with input := [], active := []}
      | value :: rest => tokenScan rest (tokenResult value {r with input := []}).state
termination_by structural values

theorem tokenScan_inactive (values : List CNFToken) (r : Registers) (inactive : r.active = []) :
    tokenScan values r = {r with input := encodeTokenPairs values} := by
  cases values <;> simp only [tokenScan, inactive]

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

theorem tokenScan_literal (literal : CNFLiteral) (target : Nat) (rest : List CNFToken)
    (remaining excess sign reserved : BitString) :
    tokenScan (encodeLiteralTokens literal ++ rest) (waiting target remaining excess sign reserved) =
      tokenScan (.f :: rest)
        (counting (List.replicate target true) (target - literal.variableIndex)
          (literal.variableIndex - target) [literal.positive] reserved [false]) := by
  cases literal with
  | mk positive index =>
      cases positive
      · change tokenScan (encodeUnaryTokens index ++ rest)
          (counting (List.replicate target true) target 0 [false] reserved [false]) = _
        simpa only [Nat.zero_add] using
          tokenScan_unary index target 0 (List.replicate target true) [false] reserved [false] rest
      · change tokenScan (encodeUnaryTokens index ++ rest)
          (counting (List.replicate target true) target 0 [true] reserved [false]) = _
        simpa only [Nat.zero_add] using
          tokenScan_unary index target 0 (List.replicate target true) [true] reserved [false] rest

end PNP.Concrete.NormalizerBlocks.TableOwner

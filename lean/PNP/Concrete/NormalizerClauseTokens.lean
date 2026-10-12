/-
Copyright (c) 2026 PNP Labs.

A proof-only token trace of the concrete indexed-clause scanner. Every trace is
realized by the already bounded finite program; it is not an instruction,
an oracle, or a premise supplied to the compiled query builder.
-/

import PNP.Concrete.NormalizerClausePolynomial

namespace PNP.Concrete.NormalizerBlocks.ClauseQuery

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

/-- The literal grammar uses only the two data tokens. -/
inductive DataTokens : List CNFToken → Prop where
  | nil : DataTokens []
  | f {rest : List CNFToken} : DataTokens rest → DataTokens (.f :: rest)
  | t {rest : List CNFToken} : DataTokens rest → DataTokens (.t :: rest)

theorem DataTokens.append {first second : List CNFToken}
    (left : DataTokens first) (right : DataTokens second) : DataTokens (first ++ second) := by
  induction left with
  | nil => exact right
  | f _ ih => exact .f ih
  | t _ ih => exact .t ih

theorem unary_data (index : Nat) : DataTokens (encodeUnaryTokens index) := by
  induction index with
  | zero => exact .f .nil
  | succ index ih => exact .t ih

theorem literal_data (literal : CNFLiteral) : DataTokens (encodeLiteralTokens literal) := by
  cases literal with
  | mk positive index =>
      cases positive
      · exact .f (unary_data index)
      · exact .t (unary_data index)

theorem clause_data (clause : List CNFLiteral) : DataTokens (encodeLiteralListTokens clause) := by
  induction clause with
  | nil => exact .nil
  | cons literal rest ih => exact (literal_data literal).append ih

end PNP.Concrete.NormalizerBlocks.ClauseQuery

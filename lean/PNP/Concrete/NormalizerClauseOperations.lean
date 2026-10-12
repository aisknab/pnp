/-
Copyright (c) 2026 PNP Labs.

Finite indexed-clause selection operations. The selected clause is read from
the full encoded list, not supplied as a semantic lookup result. Register 2
is the encoded index countdown, 3 accumulates reversed output, 5 records
selection, and 6 controls the scan. The other finite words are preserved.
-/

import PNP.Concrete.NormalizerOccurrenceHeader

namespace PNP.Concrete.NormalizerBlocks.ClauseQuery

open BitRegister Occurrence

def stop : Block 9 := .action (.clear 6)

def emit (first second : Bool) : Block 9 :=
  .seq (.action (.push 3 first)) (.action (.push 3 second))

def emitted (first second : Bool) (r : Registers) : Registers :=
  {r with excess := second :: first :: r.excess}

theorem emit_exec (first second : Bool) (r : Registers) :
    Exec (emit first second) r.store 2 (emitted first second r).store :=
  Exec.seq (.action _ _) (.action _ _)

def separator : Block 9 :=
  .branch 2 (.action (.push 5 true)) (.action (.pop 2)) (.action (.pop 2))

def separated (r : Registers) : Registers :=
  match r.remaining with
  | [] => {r with mode := true :: r.mode}
  | _ :: rest => {r with remaining := rest}

theorem separator_exec (r : Registers) :
    Exec separator r.store 2 (separated r).store := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases remaining with
      | nil => exact Exec.empty rfl (.action _ _)
      | cons bit rest => exact Exec.nonempty rfl (.action _ _)

def token (value : CNFToken) : Block 9 :=
  match value with
  | .f => .branch 5 .skip (emit false false) (emit false false)
  | .t => .branch 5 .skip (emit true true) (emit true true)
  | .sep => .branch 5 separator stop stop
  | .finish => .branch 5 .skip stop stop

def tokenResult (value : CNFToken) (r : Registers) : Result :=
  match r.mode with
  | [] =>
      match value with
      | .sep => ⟨3, separated r⟩
      | .f | .t | .finish => ⟨2, r⟩
  | _ :: _ =>
      match value with
      | .f => ⟨3, emitted false false r⟩
      | .t => ⟨3, emitted true true r⟩
      | .sep | .finish => ⟨2, {r with active := []}⟩

theorem token_exec (value : CNFToken) (r : Registers) :
    Exec (token value) r.store (tokenResult value r).fuel (tokenResult value r).state.store := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases mode with
      | nil =>
          cases value with
          | f => exact Exec.empty rfl (Exec.skip _)
          | t => exact Exec.empty rfl (Exec.skip _)
          | sep => exact Exec.empty rfl (separator_exec _)
          | finish => exact Exec.empty rfl (Exec.skip _)
      | cons bit rest =>
          cases value with
          | f => exact Exec.nonempty rfl (emit_exec false false _)
          | t => exact Exec.nonempty rfl (emit_exec true true _)
          | sep => exact Exec.nonempty rfl (.action _ _)
          | finish => exact Exec.nonempty rfl (.action _ _)

theorem token_fuel_bound (value : CNFToken) (r : Registers) : (tokenResult value r).fuel ≤ 3 := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases mode with
      | nil =>
          cases value with
          | sep => exact Nat.le_refl 3
          | f => exact Nat.le_succ 2
          | t => exact Nat.le_succ 2
          | finish => exact Nat.le_succ 2
      | cons bit rest =>
          cases value with
          | f => exact Nat.le_refl 3
          | t => exact Nat.le_refl 3
          | sep => exact Nat.le_succ 2
          | finish => exact Nat.le_succ 2

theorem token_input (value : CNFToken) (r : Registers) : (tokenResult value r).state.input = r.input := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases mode with
      | nil =>
          cases value with
          | sep => cases remaining <;> rfl
          | f => rfl
          | t => rfl
          | finish => rfl
      | cons bit rest => cases value <;> rfl

theorem token_result_input (value : CNFToken) (r : Registers) (bits : BitString) :
    (tokenResult value {r with input := bits}).state =
      {(tokenResult value {r with input := []}).state with input := bits} := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases mode with
      | nil =>
          cases value with
          | sep => cases remaining <;> rfl
          | f => rfl
          | t => rfl
          | finish => rfl
      | cons bit rest => cases value <;> rfl

end PNP.Concrete.NormalizerBlocks.ClauseQuery

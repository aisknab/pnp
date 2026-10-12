/-
Copyright (c) 2026 PNP Labs.

Fixed finite control for a table write: copy preceding entries, replace the
selected entry, skip its old payload, then copy the suffix. Repeated separators
on malformed input remain finite and are covered by the raw-input cost bound.
-/

import PNP.Concrete.NormalizerTableEmission

namespace PNP.Concrete.NormalizerBlocks.TableWrite

open BitRegister Occurrence

def stop : Block 9 := .action (.clear 6)
def finished : Block 9 := .seq (.action (.clear 5)) (.action (.push 5 false))
def afterEntry (r : Registers) : Registers := {r with mode := [false]}

def separator : Block 9 :=
  .branch 2 replacement
    (.seq (.action (.pop 2)) (ClauseQuery.emit false true))
    (.seq (.action (.pop 2)) (ClauseQuery.emit false true))

def separatorResult (r : Registers) : Result :=
  match r.remaining with
  | [] => ⟨1 + replacementFuel r, replaced r⟩
  | _ :: rest => ⟨4, ClauseQuery.emitted false true {r with remaining := rest}⟩

theorem separator_exec (r : Registers) :
    Exec separator r.store (separatorResult r).fuel (separatorResult r).state.store := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases remaining with
      | nil => exact Exec.empty rfl (replacement_exec _)
      | cons bit rest =>
          exact Exec.nonempty rfl (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def token (value : CNFToken) : Block 9 :=
  match value with
  | .f => .branch 5 (ClauseQuery.emit false false) (ClauseQuery.emit false false) .skip
  | .t => .branch 5 (ClauseQuery.emit true true) (ClauseQuery.emit true true) .skip
  | .sep => .branch 5 separator (ClauseQuery.emit false true) .skip
  | .finish => .branch 5 (ClauseQuery.emit true false) (ClauseQuery.emit true false) finished

def tokenResult (value : CNFToken) (r : Registers) : Result :=
  match r.mode with
  | [] =>
      match value with
      | .sep => let result := separatorResult r; ⟨1 + result.fuel, result.state⟩
      | .f => ⟨3, ClauseQuery.emitted false false r⟩
      | .t => ⟨3, ClauseQuery.emitted true true r⟩
      | .finish => ⟨3, ClauseQuery.emitted true false r⟩
  | false :: _ =>
      match value with
      | .f => ⟨3, ClauseQuery.emitted false false r⟩
      | .t => ⟨3, ClauseQuery.emitted true true r⟩
      | .sep => ⟨3, ClauseQuery.emitted false true r⟩
      | .finish => ⟨3, ClauseQuery.emitted true false r⟩
  | true :: _ =>
      match value with
      | .finish => ⟨3, afterEntry r⟩
      | .f | .t | .sep => ⟨2, r⟩

theorem token_exec (value : CNFToken) (r : Registers) :
    Exec (token value) r.store (tokenResult value r).fuel (tokenResult value r).state.store := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases mode with
      | nil =>
          cases value with
          | f => exact Exec.empty rfl (ClauseQuery.emit_exec false false _)
          | t => exact Exec.empty rfl (ClauseQuery.emit_exec true true _)
          | sep => exact Exec.empty rfl (separator_exec _)
          | finish => exact Exec.empty rfl (ClauseQuery.emit_exec true false _)
      | cons bit rest =>
          cases bit
          · cases value with
            | f => exact Exec.zero rfl (ClauseQuery.emit_exec false false _)
            | t => exact Exec.zero rfl (ClauseQuery.emit_exec true true _)
            | sep => exact Exec.zero rfl (ClauseQuery.emit_exec false true _)
            | finish => exact Exec.zero rfl (ClauseQuery.emit_exec true false _)
          · cases value with
            | f => exact Exec.one rfl (.skip _)
            | t => exact Exec.one rfl (.skip _)
            | sep => exact Exec.one rfl (.skip _)
            | finish => exact Exec.one rfl (Exec.seq (.action _ _) (.action _ _))

theorem token_fuel_bound (value : CNFToken) (r : Registers) :
    (tokenResult value r).fuel ≤ 4 * r.target.length + 13 := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases mode with
      | nil =>
          cases value <;> cases remaining <;>
            simp only [tokenResult, separatorResult, replacementFuel] <;> omega
      | cons bit rest =>
          cases bit <;> cases value <;> simp only [tokenResult] <;> omega

theorem token_input (value : CNFToken) (r : Registers) :
    (tokenResult value r).state.input = r.input := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases mode with
      | nil => cases value <;> cases remaining <;> rfl
      | cons bit rest => cases bit <;> cases value <;> rfl

theorem token_target (value : CNFToken) (r : Registers) :
    (tokenResult value r).state.target = r.target := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases mode with
      | nil => cases value <;> cases remaining <;> rfl
      | cons bit rest => cases bit <;> cases value <;> rfl

theorem token_result_input (value : CNFToken) (r : Registers) (bits : BitString) :
    (tokenResult value {r with input := bits}).state =
      {(tokenResult value {r with input := []}).state with input := bits} := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases mode with
      | nil => cases value <;> cases remaining <;> rfl
      | cons bit rest => cases bit <;> cases value <;> rfl

end PNP.Concrete.NormalizerBlocks.TableWrite

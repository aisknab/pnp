/-
Copyright (c) 2026 PNP Labs.

Finite source-order inverse lookup in a matching table. The target value is
compared by the existing unary literal operations. The reserved register counts
completed entries, and the first matching entry stops the scan. No matching
function or externally supplied owner is an instruction.
-/

import PNP.Concrete.NormalizerBatchPacketCanonical

namespace PNP.Concrete.NormalizerBlocks.TableOwner

open BitRegister Occurrence

def found : Block 9 :=
  .seq (.action (.copy 8 7)) (.seq (.action (.push 8 true)) Occurrence.stop)
def foundState (r : Registers) : Registers := {r with output := true :: r.reserved, active := []}

def endIndex : Block 9 :=
  .branch 3 (.branch 2 found nextLiteral nextLiteral) nextLiteral nextLiteral

def nextEntry : Block 9 := .seq (.action (.clear 5)) (.action (.push 7 true))
def afterEntry (r : Registers) : Registers := {r with mode := [], reserved := true :: r.reserved}

def token (value : CNFToken) : Block 9 :=
  match value with
  | .f => .branch 5 (startLiteral false) endIndex endIndex
  | .t => .branch 5 (startLiteral true) unit unit
  | .sep => nextLiteral
  | .finish => nextEntry

def tokenResult (value : CNFToken) (r : Registers) : Result :=
  match value with
  | .sep => ⟨1, {r with mode := []}⟩
  | .finish => ⟨2, afterEntry r⟩
  | .t =>
      match r.mode with
      | [] => ⟨7, startState true r⟩
      | _ :: _ => ⟨3, unitState r⟩
  | .f =>
      match r.mode with
      | [] => ⟨7, startState false r⟩
      | _ :: _ =>
          match r.excess with
          | _ :: _ => ⟨3, {r with mode := []}⟩
          | [] =>
              match r.remaining with
              | [] => ⟨6, foundState r⟩
              | _ :: _ => ⟨4, {r with mode := []}⟩

theorem found_exec (r : Registers) : Exec found r.store 3 (foundState r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

theorem nextEntry_exec (r : Registers) : Exec nextEntry r.store 2 (afterEntry r).store :=
  Exec.seq (.action _ _) (.action _ _)

theorem token_exec (value : CNFToken) (r : Registers) :
    Exec (token value) r.store (tokenResult value r).fuel (tokenResult value r).state.store := by
  cases value with
  | sep => exact .action _ _
  | finish => exact nextEntry_exec r
  | t =>
      cases r with
      | mk input target remaining excess sign mode active reserved output =>
          cases mode with
          | nil => exact Exec.empty rfl (start_exec true _)
          | cons bit rest => exact Exec.nonempty rfl (unit_exec _)
  | f =>
      cases r with
      | mk input target remaining excess sign mode active reserved output =>
          cases mode with
          | nil => exact Exec.empty rfl (start_exec false _)
          | cons bit rest =>
              cases excess with
              | cons head tail => exact Exec.nonempty rfl (Exec.nonempty rfl (.action _ _))
              | nil =>
                  cases remaining with
                  | nil => exact Exec.nonempty rfl (Exec.empty rfl (Exec.empty rfl (found_exec _)))
                  | cons head tail => exact Exec.nonempty rfl (Exec.empty rfl (Exec.nonempty rfl (.action _ _)))

theorem token_fuel_bound (value : CNFToken) (r : Registers) : (tokenResult value r).fuel ≤ 7 := by
  cases value with
  | f =>
      simp only [tokenResult]
      split
      · change 7 ≤ 7; decide
      · split
        · change 3 ≤ 7; decide
        · split
          · change 6 ≤ 7; decide
          · change 4 ≤ 7; decide
  | t =>
      simp only [tokenResult]
      split
      · change 7 ≤ 7; decide
      · change 3 ≤ 7; decide
  | sep => change 1 ≤ 7; decide
  | finish => change 2 ≤ 7; decide

theorem token_input (value : CNFToken) (r : Registers) : (tokenResult value r).state.input = r.input := by
  cases value with
  | f =>
      simp only [tokenResult]
      split
      · rfl
      · split
        · rfl
        · split <;> rfl
  | t =>
      simp only [tokenResult]
      split
      · rfl
      · simp only [unitState]; split <;> rfl
  | sep => rfl
  | finish => rfl

theorem token_target (value : CNFToken) (r : Registers) : (tokenResult value r).state.target = r.target := by
  cases value with
  | f =>
      simp only [tokenResult]
      split
      · rfl
      · split
        · rfl
        · split <;> rfl
  | t =>
      simp only [tokenResult]
      split
      · rfl
      · simp only [unitState]; split <;> rfl
  | sep => rfl
  | finish => rfl

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

end PNP.Concrete.NormalizerBlocks.TableOwner

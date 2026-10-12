/-
Copyright (c) 2026 PNP Labs.

Finite literal-occurrence query operations for source-derived matching.
The query finds the first occurrence's sign, preserving duplicate literals and
the original clause order. Registers are concrete finite words; no incidence
predicate or matching data is supplied to an instruction.
-/

import PNP.Concrete.NormalizerBlockExecution

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

theorem Exec.nonempty {count : Nat} {source : Fin count} {empty body : Block count}
    {before after : Store count} {cost : Nat} {bit : Bool} {rest : BitString}
    (read : before.get source = bit :: rest) (checked : Exec body before cost after) :
    Exec (.branch source empty body body) before (1 + cost) after := by
  cases bit
  · exact Exec.zero read checked
  · exact Exec.one read checked

namespace Occurrence

structure Registers where
  input : BitString
  target : BitString
  remaining : BitString
  excess : BitString
  sign : BitString
  mode : BitString
  active : BitString
  reserved : BitString
  output : BitString
deriving Repr

def Registers.store (r : Registers) : Store 9 :=
  .cons r.input (.cons r.target (.cons r.remaining (.cons r.excess (.cons r.sign
    (.cons r.mode (.cons r.active (.cons r.reserved (.cons r.output .nil))))))))

structure Result where
  fuel : Nat
  state : Registers
deriving Repr

def stop : Block 9 := .action (.clear 6)
def nextLiteral : Block 9 := .action (.clear 5)

def startLiteral (positive : Bool) : Block 9 :=
  .seq (.action (.copy 2 1)) (.seq (.action (.clear 3)) (.seq (.action (.clear 4))
    (.seq (.action (.push 4 positive)) (.seq (.action (.clear 5)) (.action (.push 5 true))))))

def startState (positive : Bool) (r : Registers) : Registers :=
  {r with remaining := r.target, excess := [], sign := [positive], mode := [true]}

def found : Block 9 :=
  .seq (.action (.copy 8 4)) (.seq (.action (.push 8 true)) stop)

def foundState (r : Registers) : Registers := {r with output := true :: r.sign, active := []}

def unit : Block 9 :=
  .branch 2 (.action (.push 3 true)) (.action (.pop 2)) (.action (.pop 2))

def unitState (r : Registers) : Registers :=
  match r.remaining with
  | [] => {r with excess := true :: r.excess}
  | _ :: rest => {r with remaining := rest}

def endIndex : Block 9 :=
  .branch 3 (.branch 2 found nextLiteral nextLiteral) nextLiteral nextLiteral

def token (value : CNFToken) : Block 9 :=
  match value with
  | .f => .branch 5 (startLiteral false) endIndex endIndex
  | .t => .branch 5 (startLiteral true) unit unit
  | .sep => stop
  | .finish => stop

def tokenResult (value : CNFToken) (r : Registers) : Result :=
  match value with
  | .sep | .finish => ⟨1, {r with active := []}⟩
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

theorem start_exec (positive : Bool) (r : Registers) :
    Exec (startLiteral positive) r.store 6 (startState positive r).store := by
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))))

theorem found_exec (r : Registers) : Exec found r.store 3 (foundState r).store := by
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

theorem unit_exec (r : Registers) : Exec unit r.store 2 (unitState r).store := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases remaining with
      | nil => exact Exec.empty rfl (.action _ _)
      | cons bit rest => exact Exec.nonempty rfl (.action _ _)

theorem token_exec (value : CNFToken) (r : Registers) :
    Exec (token value) r.store (tokenResult value r).fuel (tokenResult value r).state.store := by
  cases value with
  | sep => exact .action _ _
  | finish => exact .action _ _
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
                  | cons head tail =>
                      exact Exec.nonempty rfl (Exec.empty rfl (Exec.nonempty rfl (.action _ _)))

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
  | finish => change 1 ≤ 7; decide

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

end Occurrence
end PNP.Concrete.NormalizerBlocks

/-
Copyright (c) 2026 PNP Labs.

Literal tape primitives for the finite bit-register compiler. Every transition
is an explicit finite WorkRule. The theorems charge real tape transitions and
reuse the existing six-transition raw compiler. These primitives alone are not
the complete register compiler or normalizer implementation.
-/

import PNP.Concrete.BitRegisterProgram

namespace PNP.Concrete.BitRegister.TapePrimitive

def focus (left right : List WorkSymbol) : WorkTape :=
  match right with
  | [] => ⟨left, WorkSymbol.blank, []⟩
  | head :: tail => ⟨left, head, tail⟩

def focusLeft (left right : List WorkSymbol) : WorkTape :=
  match left with
  | [] => ⟨[], WorkSymbol.blank, right⟩
  | head :: tail => ⟨tail, head, right⟩

/-- Reverse onto an existing suffix by constructor recursion. -/
def reverseOnto : List WorkSymbol → List WorkSymbol → List WorkSymbol
  | [], suffix => suffix
  | first :: rest, suffix => reverseOnto rest (first :: suffix)

private def keep (source target : Nat) (symbol : WorkSymbol)
    (movement : HeadMove) : WorkRule :=
  ⟨source, symbol, target, symbol, movement⟩

/-- Skip one complete register, including its delimiter. -/
def skip : WorkMachine :=
  { rules := [
      keep 0 0 (Store.bitSymbol false) .right,
      keep 0 0 (Store.bitSymbol true) .right,
      keep 0 1 Store.separator .right]
    startState := 0, acceptState := 1, rejectState := 2 }

theorem skip_bit_step (bit : Bool) (left right : List WorkSymbol) :
    workStep? skip ⟨0, focus left (Store.bitSymbol bit :: right)⟩ =
      some ⟨0, focus (Store.bitSymbol bit :: left) right⟩ := by
  cases bit <;> cases right <;> rfl

theorem skip_separator_step (left right : List WorkSymbol) :
    workStep? skip ⟨0, focus left (Store.separator :: right)⟩ =
      some ⟨1, focus (Store.separator :: left) right⟩ := by
  cases right <;> rfl

/-- Exact, all-string cost: one move per data bit and one per delimiter. -/
theorem skip_run (bits : BitString) (left right : List WorkSymbol) :
    workRunExact? skip (bits.length + 1)
      ⟨0, focus left (bits.map Store.bitSymbol ++ Store.separator :: right)⟩ =
    some ⟨1, focus
      (Store.separator :: reverseOnto (bits.map Store.bitSymbol) left) right⟩ := by
  induction bits generalizing left with
  | nil =>
      change (match workStep? skip ⟨0, focus left (Store.separator :: right)⟩ with
        | none => none
        | some next => some next) = _
      rw [skip_separator_step]
      rfl
  | cons bit rest ih =>
      change (match workStep? skip
          ⟨0, focus left (Store.bitSymbol bit ::
            (rest.map Store.bitSymbol ++ Store.separator :: right))⟩ with
        | none => none
        | some next => workRunExact? skip (rest.length + 1) next) = _
      rw [skip_bit_step]
      exact ih (Store.bitSymbol bit :: left)

theorem skip_raw_run (bits : BitString) (left right : List WorkSymbol) :
    PNP.Concrete.run (compileWorkMachine skip) (6 * (bits.length + 1))
      (encodeWorkConfiguration
        ⟨0, focus left (bits.map Store.bitSymbol ++ Store.separator :: right)⟩) =
    encodeWorkConfiguration
      ⟨1, focus (Store.separator :: reverseOnto (bits.map Store.bitSymbol) left)
        right⟩ :=
  run_compileWorkMachine_mul_of_workRunExact skip (bits.length + 1) _ _
    (skip_run bits left right)

/-- Only these three symbols may occur inside an encoded register bank. -/
inductive DataSymbol : WorkSymbol → Prop where
  | zero : DataSymbol (Store.bitSymbol false)
  | one : DataSymbol (Store.bitSymbol true)
  | separator : DataSymbol Store.separator

def DataWord : List WorkSymbol → Prop
  | [] => True
  | first :: rest => DataSymbol first ∧ DataWord rest

theorem bitWord_data (bits : BitString) (suffix : List WorkSymbol)
    (h : DataWord suffix) : DataWord (bits.map Store.bitSymbol ++ suffix) := by
  induction bits with
  | nil => exact h
  | cons bit rest ih =>
      cases bit with
      | false => exact ⟨.zero, ih⟩
      | true => exact ⟨.one, ih⟩

theorem store_data {count : Nat} (store : Store count) : DataWord store.encode := by
  induction store with
  | nil => exact True.intro
  | cons first rest ih => exact bitWord_data first _ ⟨.separator, ih⟩

/-- Restore the left boundary without changing any register symbol. -/
def rewind : WorkMachine :=
  { rules := [
      keep 0 0 (Store.bitSymbol false) .left,
      keep 0 0 (Store.bitSymbol true) .left,
      keep 0 0 Store.separator .left,
      keep 0 1 WorkSymbol.blankZero .stay]
    startState := 0, acceptState := 1, rejectState := 2 }

theorem rewind_symbol_step (symbol : WorkSymbol) (left right : List WorkSymbol)
    (h : DataSymbol symbol) :
    workStep? rewind ⟨0, { left := left, head := symbol, right := right }⟩ =
      some ⟨0, focusLeft left (symbol :: right)⟩ := by
  cases h <;> cases left <;> rfl

/-- The exterior is arbitrary and preserved; only the visited prefix is read. -/
theorem rewind_run (visited outside right : List WorkSymbol) (h : DataWord visited) :
    workRunExact? rewind (visited.length + 1)
      ⟨0, focusLeft (visited ++ WorkSymbol.blankZero :: outside) right⟩ =
    some ⟨1, { left := outside, head := WorkSymbol.blankZero, right := reverseOnto visited right }⟩ := by
  induction visited generalizing right with
  | nil => rfl
  | cons symbol rest ih =>
      change (match workStep? rewind
          ⟨0, { left := rest ++ WorkSymbol.blankZero :: outside, head := symbol, right := right }⟩ with
        | none => none
        | some next => workRunExact? rewind (rest.length + 1) next) = _
      rw [rewind_symbol_step symbol _ _ h.1]
      exact ih (symbol :: right) h.2

theorem rewind_raw_run (visited outside right : List WorkSymbol)
    (h : DataWord visited) :
    PNP.Concrete.run (compileWorkMachine rewind) (6 * (visited.length + 1))
      (encodeWorkConfiguration
        ⟨0, focusLeft (visited ++ WorkSymbol.blankZero :: outside) right⟩) =
    encodeWorkConfiguration
      ⟨1, { left := outside, head := WorkSymbol.blankZero, right := reverseOnto visited right }⟩ :=
  run_compileWorkMachine_mul_of_workRunExact rewind (visited.length + 1) _ _
    (rewind_run visited outside right h)

/-- Empty-register test at the register's first symbol; no tape mutation. -/
def isEmpty : WorkMachine :=
  { rules := [
      keep 0 1 Store.separator .stay,
      keep 0 2 (Store.bitSymbol false) .stay,
      keep 0 2 (Store.bitSymbol true) .stay]
    startState := 0, acceptState := 1, rejectState := 2 }

def emptyState : BitString → Nat
  | [] => 1
  | _ :: _ => 2

theorem isEmpty_run (bits : BitString) (left right : List WorkSymbol) :
    workRunExact? isEmpty 1
      ⟨0, focus left (bits.map Store.bitSymbol ++ Store.separator :: right)⟩ =
    some ⟨emptyState bits,
      focus left (bits.map Store.bitSymbol ++ Store.separator :: right)⟩ := by
  cases bits with
  | nil => rfl
  | cons bit rest => cases bit <;> rfl

/-- Called only on a nonempty register after the empty test. -/
def headBit : WorkMachine :=
  { rules := [
      keep 0 2 (Store.bitSymbol false) .stay,
      keep 0 1 (Store.bitSymbol true) .stay]
    startState := 0, acceptState := 1, rejectState := 2 }

theorem headBit_run (bit : Bool) (tail : BitString) (left right : List WorkSymbol) :
    workRunExact? headBit 1
      ⟨0, focus left ((bit :: tail).map Store.bitSymbol ++ Store.separator :: right)⟩ =
    some ⟨(if bit then 1 else 2),
      focus left ((bit :: tail).map Store.bitSymbol ++ Store.separator :: right)⟩ := by
  cases bit <;> rfl

end PNP.Concrete.BitRegister.TapePrimitive

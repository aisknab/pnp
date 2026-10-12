/-
Copyright (c) 2026 PNP Labs.

Literal, finite-state insertion and deletion inside the bit-register tape.
All intervening data, register delimiters and copy marks are moved explicitly.
Costs count actual work-machine transitions, not source-language operations.
Deletion may leave an extra represented blank beyond the right boundary;
insertion consumes one such blank when available. This slack is tracked
explicitly rather than silently equating different tape representations.
-/

import PNP.Concrete.BitRegisterTape
import PNP.Concrete.PipelineMachineSimulation

namespace PNP.Concrete.BitRegister.Mutation

open TapePrimitive

/-- Five movable symbols; copy marks have finite distinct representations. -/
inductive Cell where
  | zero
  | one
  | separator
  | markedZero
  | markedOne
deriving BEq, DecidableEq, Repr

namespace Cell

def symbol : Cell → WorkSymbol
  | .zero => Store.bitSymbol false
  | .one => Store.bitSymbol true
  | .separator => Store.separator
  | .markedZero => WorkSymbol.zeroOne
  | .markedOne => WorkSymbol.oneOne

def all : List Cell := [.zero, .one, .separator, .markedZero, .markedOne]

def carryState : Cell → Nat
  | .zero => 10
  | .one => 11
  | .separator => 12
  | .markedZero => 13
  | .markedOne => 14

end Cell

def rightBoundary : WorkSymbol := WorkSymbol.zeroZero
def anchor : WorkSymbol := WorkSymbol.oneZero
def tail (slack : Nat) : List WorkSymbol :=
  rightBoundary :: List.replicate slack WorkSymbol.blank

private def rule (source : Nat) (read : WorkSymbol) (target : Nat)
    (write : WorkSymbol) (movement : HeadMove) : WorkRule :=
  ⟨source, read, target, write, movement⟩

/-- An actual step yields one exact transition, not a timeout convention. -/
theorem exact_one {machine : WorkMachine} {start finish : WorkConfiguration}
    (h : workStep? machine start = some finish) :
    workRunExact? machine 1 start = some finish := by
  change (match workStep? machine start with
    | none => none
    | some next => some next) = some finish
  rw [h]

/-- Trace algebra only. Every use below supplies an explicit finite-table proof
of the one-cell step; this is not an assumed implementation certificate. -/
theorem traverse_left (machine : WorkMachine) (state : Nat)
    (hStep : ∀ (cell : Cell) (left right : List WorkSymbol),
      workStep? machine ⟨state, ⟨left, cell.symbol, right⟩⟩ =
        some ⟨state, focusLeft left (cell.symbol :: right)⟩)
    (cells : List Cell) (left right : List WorkSymbol) :
    workRunExact? machine cells.length
      ⟨state, focusLeft (reverseOnto (cells.map Cell.symbol) left) right⟩ =
    some ⟨state, focusLeft left (cells.map Cell.symbol ++ right)⟩ := by
  induction cells generalizing left right with
  | nil => rfl
  | cons cell rest ih =>
      have hFirst := ih (cell.symbol :: left) right
      have hLast := exact_one (hStep cell left (rest.map Cell.symbol ++ right))
      exact PipelineMachineSimulation.workRunExact?_compose machine rest.length 1
        _ _ _ hFirst hLast

/-- Insert one bit, remembering displaced symbols in a finite control state. -/
def insert (bit : Bool) : WorkMachine :=
  { rules :=
      Cell.all.map (fun cell =>
        rule 0 cell.symbol cell.carryState anchor .right) ++
      Cell.all.flatMap (fun carried =>
        Cell.all.map (fun next =>
          rule carried.carryState next.symbol next.carryState carried.symbol .right) ++
        [rule carried.carryState rightBoundary 4 carried.symbol .right]) ++
      [rule 4 WorkSymbol.blank 2 rightBoundary .left] ++
      Cell.all.map (fun cell => rule 2 cell.symbol 2 cell.symbol .left) ++
      [rule 2 anchor 1 (Store.bitSymbol bit) .stay]
    startState := 0
    acceptState := 1
    rejectState := 3 }

theorem insert_initial_step (bit : Bool) (cell : Cell) (left right : List WorkSymbol) :
    workStep? (insert bit) ⟨0, focus left (cell.symbol :: right)⟩ =
      some ⟨cell.carryState, focus (anchor :: left) right⟩ := by
  cases cell <;> cases right <;> rfl

theorem insert_carry_step (bit : Bool) (carried next : Cell)
    (left right : List WorkSymbol) :
    workStep? (insert bit) ⟨carried.carryState, focus left (next.symbol :: right)⟩ =
      some ⟨next.carryState, focus (carried.symbol :: left) right⟩ := by
  cases carried <;> cases next <;> cases right <;> rfl

theorem insert_finish_carry (bit : Bool) (carried : Cell)
    (left : List WorkSymbol) (slack : Nat) :
    workRunExact? (insert bit) 2 ⟨carried.carryState, focus left (tail slack)⟩ =
    some ⟨2, focusLeft (carried.symbol :: left) (tail (slack - 1))⟩ := by
  cases carried <;> cases slack <;> rfl

theorem insert_drain (bit : Bool) (carried : Cell) (remaining : List Cell)
    (left : List WorkSymbol) (slack : Nat) :
    workRunExact? (insert bit) (remaining.length + 2)
      ⟨carried.carryState, focus left (remaining.map Cell.symbol ++ tail slack)⟩ =
    some ⟨2, focusLeft
      (reverseOnto ((carried :: remaining).map Cell.symbol) left) (tail (slack - 1))⟩ := by
  induction remaining generalizing carried left with
  | nil => exact insert_finish_carry bit carried left slack
  | cons next rest ih =>
      change (match workStep? (insert bit)
          ⟨carried.carryState, focus left (next.symbol ::
            (rest.map Cell.symbol ++ tail slack))⟩ with
        | none => none
        | some nextConfiguration =>
            workRunExact? (insert bit) (rest.length + 2) nextConfiguration) = _
      rw [insert_carry_step]
      exact ih next (carried.symbol :: left)

theorem insert_return_step (bit : Bool) (cell : Cell) (left right : List WorkSymbol) :
    workStep? (insert bit) ⟨2, ⟨left, cell.symbol, right⟩⟩ =
      some ⟨2, focusLeft left (cell.symbol :: right)⟩ := by
  cases cell <;> cases left <;> rfl

theorem insert_return (bit : Bool) (cells : List Cell) (left right : List WorkSymbol) :
    workRunExact? (insert bit) cells.length
      ⟨2, focusLeft (reverseOnto (cells.map Cell.symbol) left) right⟩ =
    some ⟨2, focusLeft left (cells.map Cell.symbol ++ right)⟩ :=
  traverse_left (insert bit) 2 (insert_return_step bit) cells left right

theorem insert_stop (bit : Bool) (left right : List WorkSymbol) :
    workRunExact? (insert bit) 1 ⟨2, ⟨left, anchor, right⟩⟩ =
      some ⟨1, ⟨left, Store.bitSymbol bit, right⟩⟩ := by
  rfl

private theorem insertion_cost (n : Nat) :
    1 + (n + 2) + (n + 1) + 1 = 2 * (n + 1) + 3 := by
  have hFirst : 1 + (n + 2) = n + 3 := Nat.add_left_comm 1 n 2
  have hMiddle : (n + 3) + (n + 1) = (n + n) + 4 :=
    (Nat.add_assoc n 3 (n + 1)).trans
      ((congrArg (fun value => n + value) (Nat.add_left_comm 3 n 1)).trans
        (Nat.add_assoc n n (3 + 1)).symm)
  calc
    1 + (n + 2) + (n + 1) + 1 = (n + 3) + (n + 1) + 1 :=
      congrArg (fun value => value + (n + 1) + 1) hFirst
    _ = (n + n) + 4 + 1 := congrArg (fun value => value + 1) hMiddle
    _ = 2 * (n + 1) + 3 := by rw [Nat.mul_succ, Nat.two_mul]

/-- The whole suffix is shifted exactly once in each direction. No register
beyond the insertion point is discarded or treated as free host-language data. -/
theorem insert_run (bit : Bool) (first : Cell) (rest : List Cell)
    (left : List WorkSymbol) (slack : Nat) :
    workRunExact? (insert bit) (2 * (rest.length + 1) + 3)
      ⟨0, focus left ((first :: rest).map Cell.symbol ++ tail slack)⟩ =
    some ⟨1, focus left
      (Store.bitSymbol bit :: ((first :: rest).map Cell.symbol ++ tail (slack - 1)))⟩ := by
  have hStart := exact_one
    (insert_initial_step bit first left (rest.map Cell.symbol ++ tail slack))
  have hDrain := insert_drain bit first rest (anchor :: left) slack
  have hReturn := insert_return bit (first :: rest) (anchor :: left) (tail (slack - 1))
  have hStop := insert_stop bit left ((first :: rest).map Cell.symbol ++ tail (slack - 1))
  have hFirst := PipelineMachineSimulation.workRunExact?_compose (insert bit)
    1 (rest.length + 2) _ _ _ hStart hDrain
  have hSecond := PipelineMachineSimulation.workRunExact?_compose (insert bit)
    (1 + (rest.length + 2)) (rest.length + 1) _ _ _ hFirst hReturn
  have hAll := PipelineMachineSimulation.workRunExact?_compose (insert bit)
    (1 + (rest.length + 2) + (rest.length + 1)) 1 _ _ _ hSecond hStop
  have hSteps := insertion_cost rest.length
  rw [hSteps] at hAll
  exact hAll

theorem insert_raw_run (bit : Bool) (first : Cell) (rest : List Cell)
    (left : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (insert bit)) (6 * (2 * (rest.length + 1) + 3))
      (encodeWorkConfiguration
        ⟨0, focus left ((first :: rest).map Cell.symbol ++ tail slack)⟩) =
    encodeWorkConfiguration
      ⟨1, focus left
        (Store.bitSymbol bit :: ((first :: rest).map Cell.symbol ++ tail (slack - 1)))⟩ :=
  run_compileWorkMachine_mul_of_workRunExact (insert bit) _ _ _
    (insert_run bit first rest left slack)

/-- Delete a selected movable cell and restore the left boundary.
This primitive is not an empty-register pop: its caller must select the cell
to remove. The later register compiler must preserve register delimiters. -/
def eraseCell : WorkMachine :=
  { rules :=
      Cell.all.map (fun cell => rule 0 cell.symbol 2 anchor .right) ++
      Cell.all.map (fun cell => rule 2 cell.symbol cell.carryState anchor .left) ++
      Cell.all.map (fun cell => rule cell.carryState anchor 3 cell.symbol .right) ++
      [rule 3 anchor 2 anchor .right,
       rule 2 rightBoundary 5 WorkSymbol.blank .left,
       rule 5 anchor 4 rightBoundary .left] ++
      Cell.all.map (fun cell => rule 4 cell.symbol 4 cell.symbol .left) ++
      [rule 4 WorkSymbol.blankZero 1 WorkSymbol.blankZero .stay]
    startState := 0
    acceptState := 1
    rejectState := 6 }

theorem erase_initial_step (cell : Cell) (left right : List WorkSymbol) :
    workStep? eraseCell ⟨0, focus left (cell.symbol :: right)⟩ =
      some ⟨2, focus (anchor :: left) right⟩ := by
  cases cell <;> cases right <;> rfl

theorem erase_shift_three (cell : Cell) (left right : List WorkSymbol) :
    workRunExact? eraseCell 3 ⟨2, focus (anchor :: left) (cell.symbol :: right)⟩ =
      some ⟨2, focus (anchor :: cell.symbol :: left) right⟩ := by
  cases cell <;> cases right <;> rfl

theorem erase_finish_shift (left : List WorkSymbol) (slack : Nat) :
    workRunExact? eraseCell 2 ⟨2, focus (anchor :: left) (tail slack)⟩ =
      some ⟨4, focusLeft left (tail (slack + 1))⟩ := by
  cases left <;> rfl

theorem erase_drain (remaining : List Cell) (left : List WorkSymbol) (slack : Nat) :
    workRunExact? eraseCell (3 * remaining.length + 2)
      ⟨2, focus (anchor :: left) (remaining.map Cell.symbol ++ tail slack)⟩ =
    some ⟨4, focusLeft (reverseOnto (remaining.map Cell.symbol) left) (tail (slack + 1))⟩ := by
  induction remaining generalizing left with
  | nil => exact erase_finish_shift left slack
  | cons cell rest ih =>
      have hFirst := erase_shift_three cell left (rest.map Cell.symbol ++ tail slack)
      have hTail := ih (cell.symbol :: left)
      have hAll := PipelineMachineSimulation.workRunExact?_compose eraseCell
        3 (3 * rest.length + 2) _ _ _ hFirst hTail
      have hSteps : 3 + (3 * rest.length + 2) = 3 * (rest.length + 1) + 2 := by
        rw [Nat.mul_succ]
        exact (Nat.add_assoc 3 (3 * rest.length) 2).symm.trans
          (congrArg (fun value => value + 2) (Nat.add_comm 3 (3 * rest.length)))
      rw [hSteps] at hAll
      exact hAll

theorem erase_return_step (cell : Cell) (left right : List WorkSymbol) :
    workStep? eraseCell ⟨4, ⟨left, cell.symbol, right⟩⟩ =
      some ⟨4, focusLeft left (cell.symbol :: right)⟩ := by
  cases cell <;> cases left <;> rfl

theorem erase_return (cells : List Cell) (left right : List WorkSymbol) :
    workRunExact? eraseCell cells.length
      ⟨4, focusLeft (reverseOnto (cells.map Cell.symbol) left) right⟩ =
    some ⟨4, focusLeft left (cells.map Cell.symbol ++ right)⟩ :=
  traverse_left eraseCell 4 erase_return_step cells left right

theorem erase_stop (outside right : List WorkSymbol) :
    workRunExact? eraseCell 1 ⟨4, ⟨outside, WorkSymbol.blankZero, right⟩⟩ =
      some ⟨1, ⟨outside, WorkSymbol.blankZero, right⟩⟩ := by
  rfl

private theorem deletion_cost (n p : Nat) :
    1 + (3 * n + 2) + n + p + 1 = 4 * n + p + 4 := by
  have hFirst : 1 + (3 * n + 2) = 3 * n + 3 := Nat.add_left_comm 1 (3 * n) 2
  have hSwap (a b c : Nat) : (a + b) + c = (a + c) + b :=
    (Nat.add_assoc a b c).trans
      ((congrArg (fun value => a + value) (Nat.add_comm b c)).trans
        (Nat.add_assoc a c b).symm)
  have hMiddle : (3 * n + 3) + n + p = (3 * n + n + p) + 3 :=
    (congrArg (fun value => value + p) (hSwap (3 * n) 3 n)).trans
      (hSwap (3 * n + n) 3 p)
  calc
    1 + (3 * n + 2) + n + p + 1 = (3 * n + 3) + n + p + 1 :=
      congrArg (fun value => value + n + p + 1) hFirst
    _ = (3 * n + n + p) + 3 + 1 := congrArg (fun value => value + 1) hMiddle
    _ = 4 * n + p + 4 := by rw [Nat.succ_mul 3 n]

/-- Exact deletion with an arbitrary preserved prefix, suffix and exterior.
The extra represented blank is part of the result, not silently dropped. -/
theorem erase_run (first : Cell) (before after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? eraseCell (4 * after.length + before.length + 4)
      ⟨0, focus (reverseOnto (before.map Cell.symbol) (WorkSymbol.blankZero :: outside))
        ((first :: after).map Cell.symbol ++ tail slack)⟩ =
    some ⟨1, ⟨outside, WorkSymbol.blankZero,
      before.map Cell.symbol ++ (after.map Cell.symbol ++ tail (slack + 1))⟩⟩ := by
  let left := reverseOnto (before.map Cell.symbol) (WorkSymbol.blankZero :: outside)
  have hStart := exact_one
    (erase_initial_step first left (after.map Cell.symbol ++ tail slack))
  have hDrain := erase_drain after left slack
  have hReturnAfter := erase_return after left (tail (slack + 1))
  have hReturnBefore := erase_return before (WorkSymbol.blankZero :: outside)
    (after.map Cell.symbol ++ tail (slack + 1))
  have hStop := erase_stop outside
    (before.map Cell.symbol ++ (after.map Cell.symbol ++ tail (slack + 1)))
  have hFirst := PipelineMachineSimulation.workRunExact?_compose eraseCell
    1 (3 * after.length + 2) _ _ _ hStart hDrain
  have hSecond := PipelineMachineSimulation.workRunExact?_compose eraseCell
    (1 + (3 * after.length + 2)) after.length _ _ _ hFirst hReturnAfter
  have hThird := PipelineMachineSimulation.workRunExact?_compose eraseCell
    (1 + (3 * after.length + 2) + after.length) before.length _ _ _ hSecond hReturnBefore
  have hAll := PipelineMachineSimulation.workRunExact?_compose eraseCell
    (1 + (3 * after.length + 2) + after.length + before.length) 1 _ _ _ hThird hStop
  have hSteps := deletion_cost after.length before.length
  rw [hSteps] at hAll
  exact hAll

theorem erase_raw_run (first : Cell) (before after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine eraseCell)
      (6 * (4 * after.length + before.length + 4))
      (encodeWorkConfiguration
        ⟨0, focus (reverseOnto (before.map Cell.symbol) (WorkSymbol.blankZero :: outside))
          ((first :: after).map Cell.symbol ++ tail slack)⟩) =
    encodeWorkConfiguration
      ⟨1, ⟨outside, WorkSymbol.blankZero,
        before.map Cell.symbol ++ (after.map Cell.symbol ++ tail (slack + 1))⟩⟩ :=
  run_compileWorkMachine_mul_of_workRunExact eraseCell _ _ _
    (erase_run first before after outside slack)

end PNP.Concrete.BitRegister.Mutation

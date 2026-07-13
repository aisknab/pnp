/-
Copyright (c) 2026 PNP Labs.

Constructive equivalence for finite tape representations which differ only by
materialized exterior blanks.  The raw transition system observes an infinite
blank extension on both sides, so finite list boundaries are representation
details rather than machine-visible data.

This module proves only representation invariance and the ordinary-input to
work-input bridge.  It does not construct a pipeline stage, a RawRefinement,
or any complexity-class result.
-/

import PNP.Concrete.TapeHandoff
import PNP.Concrete.WorkInput

namespace PNP.Concrete

namespace Tape

/-- Read one cell from a finite side list, extending it with blanks forever. -/
def blankCellAt : List TapeSymbol → Nat → TapeSymbol
  | [], _ => .blank
  | symbol :: _, 0 => symbol
  | _ :: rest, index + 1 => blankCellAt rest index

@[simp] theorem blankCellAt_nil (index : Nat) :
    blankCellAt [] index = .blank := by
  cases index <;> rfl

@[simp] theorem blankCellAt_cons_zero (symbol : TapeSymbol)
    (rest : List TapeSymbol) :
    blankCellAt (symbol :: rest) 0 = symbol := rfl

@[simp] theorem blankCellAt_cons_succ (symbol : TapeSymbol)
    (rest : List TapeSymbol) (index : Nat) :
    blankCellAt (symbol :: rest) (index + 1) = blankCellAt rest index := rfl

/-- Two finite tape values denote the same infinite blank-extended tape. -/
def BlankEquivalent (first second : Tape) : Prop :=
  first.head = second.head ∧
    (∀ index, blankCellAt first.left index = blankCellAt second.left index) ∧
    (∀ index, blankCellAt first.right index = blankCellAt second.right index)

theorem blankEquivalent_refl (tape : Tape) : BlankEquivalent tape tape := by
  exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem blankEquivalent_symm {first second : Tape}
    (h : BlankEquivalent first second) : BlankEquivalent second first := by
  rcases h with ⟨hHead, hLeft, hRight⟩
  exact ⟨hHead.symm, fun index => (hLeft index).symm,
    fun index => (hRight index).symm⟩

theorem blankEquivalent_trans {first second third : Tape}
    (hFirst : BlankEquivalent first second)
    (hSecond : BlankEquivalent second third) : BlankEquivalent first third := by
  rcases hFirst with ⟨hFirstHead, hFirstLeft, hFirstRight⟩
  rcases hSecond with ⟨hSecondHead, hSecondLeft, hSecondRight⟩
  exact ⟨hFirstHead.trans hSecondHead,
    fun index => (hFirstLeft index).trans (hSecondLeft index),
    fun index => (hFirstRight index).trans (hSecondRight index)⟩

theorem blankEquivalent_write {first second : Tape}
    (h : BlankEquivalent first second) (symbol : TapeSymbol) :
    BlankEquivalent (first.write symbol) (second.write symbol) := by
  rcases h with ⟨_, hLeft, hRight⟩
  exact ⟨rfl, hLeft, hRight⟩

private theorem moveLeft_head (tape : Tape) :
    tape.moveLeft.head = blankCellAt tape.left 0 := by
  cases tape with
  | mk left head right =>
      cases left <;> rfl

private theorem moveLeft_left (tape : Tape) (index : Nat) :
    blankCellAt tape.moveLeft.left index =
      blankCellAt tape.left (index + 1) := by
  cases tape with
  | mk left head right =>
      cases left with
      | nil => cases index <;> rfl
      | cons first rest => rfl

private theorem moveLeft_right_zero (tape : Tape) :
    blankCellAt tape.moveLeft.right 0 = tape.head := by
  cases tape with
  | mk left head right =>
      cases left <;> rfl

private theorem moveLeft_right_succ (tape : Tape) (index : Nat) :
    blankCellAt tape.moveLeft.right (index + 1) =
      blankCellAt tape.right index := by
  cases tape with
  | mk left head right =>
      cases left <;> rfl

theorem blankEquivalent_moveLeft {first second : Tape}
    (h : BlankEquivalent first second) :
    BlankEquivalent first.moveLeft second.moveLeft := by
  rcases h with ⟨hHead, hLeft, hRight⟩
  constructor
  · rw [moveLeft_head, moveLeft_head]
    exact hLeft 0
  constructor
  · intro index
    rw [moveLeft_left, moveLeft_left]
    exact hLeft (index + 1)
  · intro index
    cases index with
    | zero =>
        rw [moveLeft_right_zero, moveLeft_right_zero]
        exact hHead
    | succ index =>
        rw [moveLeft_right_succ, moveLeft_right_succ]
        exact hRight index

private theorem moveRight_head (tape : Tape) :
    tape.moveRight.head = blankCellAt tape.right 0 := by
  cases tape with
  | mk left head right =>
      cases right <;> rfl

private theorem moveRight_right (tape : Tape) (index : Nat) :
    blankCellAt tape.moveRight.right index =
      blankCellAt tape.right (index + 1) := by
  cases tape with
  | mk left head right =>
      cases right with
      | nil => cases index <;> rfl
      | cons first rest => rfl

private theorem moveRight_left_zero (tape : Tape) :
    blankCellAt tape.moveRight.left 0 = tape.head := by
  cases tape with
  | mk left head right =>
      cases right <;> rfl

private theorem moveRight_left_succ (tape : Tape) (index : Nat) :
    blankCellAt tape.moveRight.left (index + 1) =
      blankCellAt tape.left index := by
  cases tape with
  | mk left head right =>
      cases right <;> rfl

theorem blankEquivalent_moveRight {first second : Tape}
    (h : BlankEquivalent first second) :
    BlankEquivalent first.moveRight second.moveRight := by
  rcases h with ⟨hHead, hLeft, hRight⟩
  constructor
  · rw [moveRight_head, moveRight_head]
    exact hRight 0
  constructor
  · intro index
    cases index with
    | zero =>
        rw [moveRight_left_zero, moveRight_left_zero]
        exact hHead
    | succ index =>
        rw [moveRight_left_succ, moveRight_left_succ]
        exact hLeft index
  · intro index
    rw [moveRight_right, moveRight_right]
    exact hRight (index + 1)

theorem blankEquivalent_move {first second : Tape}
    (h : BlankEquivalent first second) (move : HeadMove) :
    BlankEquivalent (first.move move) (second.move move) := by
  cases move with
  | left => exact blankEquivalent_moveLeft h
  | stay => exact h
  | right => exact blankEquivalent_moveRight h

private theorem decodeOutputCells_eq_of_blankCellAt
    (first second : List TapeSymbol)
    (h : ∀ index, blankCellAt first index = blankCellAt second index) :
    decodeOutputCells first = decodeOutputCells second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons symbol rest =>
          have hHead := h 0
          change TapeSymbol.blank = symbol at hHead
          cases symbol with
          | blank => rfl
          | zero => contradiction
          | one => contradiction
  | cons firstSymbol firstRest ih =>
      cases second with
      | nil =>
          have hHead := h 0
          change firstSymbol = TapeSymbol.blank at hHead
          cases firstSymbol with
          | blank => rfl
          | zero => contradiction
          | one => contradiction
      | cons secondSymbol secondRest =>
          have hHead := h 0
          change firstSymbol = secondSymbol at hHead
          subst secondSymbol
          cases firstSymbol with
          | blank => rfl
          | zero =>
              apply congrArg (List.cons false)
              apply ih
              intro index
              exact h (index + 1)
          | one =>
              apply congrArg (List.cons true)
              apply ih
              intro index
              exact h (index + 1)

theorem outputBits_eq_of_blankEquivalent {first second : Tape}
    (h : BlankEquivalent first second) :
    outputBits first = outputBits second := by
  rcases h with ⟨hHead, _, hRight⟩
  unfold outputBits
  cases first with
  | mk firstLeft firstHead firstRight =>
      cases second with
      | mk secondLeft secondHead secondRight =>
          change firstHead = secondHead at hHead
          subst secondHead
          cases firstHead with
          | blank => rfl
          | zero =>
              apply congrArg (List.cons false)
              exact decodeOutputCells_eq_of_blankCellAt
                firstRight secondRight hRight
          | one =>
              apply congrArg (List.cons true)
              exact decodeOutputCells_eq_of_blankCellAt
                firstRight secondRight hRight

end Tape

namespace Configuration

/-- Configurations agree when their control states and infinite tapes agree. -/
def BlankEquivalent (first second : Configuration) : Prop :=
  first.state = second.state ∧ Tape.BlankEquivalent first.tape second.tape

theorem blankEquivalent_refl (config : Configuration) :
    BlankEquivalent config config := by
  exact ⟨rfl, Tape.blankEquivalent_refl config.tape⟩

theorem blankEquivalent_symm {first second : Configuration}
    (h : BlankEquivalent first second) : BlankEquivalent second first := by
  exact ⟨h.1.symm, Tape.blankEquivalent_symm h.2⟩

theorem blankEquivalent_trans {first second third : Configuration}
    (hFirst : BlankEquivalent first second)
    (hSecond : BlankEquivalent second third) : BlankEquivalent first third := by
  exact ⟨hFirst.1.trans hSecond.1,
    Tape.blankEquivalent_trans hFirst.2 hSecond.2⟩

end Configuration

private theorem applyRule_blankEquivalent (rule : Rule)
    {first second : Configuration}
    (h : Configuration.BlankEquivalent first second) :
    Configuration.BlankEquivalent (applyRule rule first) (applyRule rule second) := by
  rcases h with ⟨hState, hTape⟩
  exact ⟨rfl, Tape.blankEquivalent_move
    (Tape.blankEquivalent_write hTape rule.writeSymbol) rule.move⟩

private theorem step?_blankEquivalent (machine : Machine)
    {first second : Configuration}
    (h : Configuration.BlankEquivalent first second) :
    (step? machine first = none ∧ step? machine second = none) ∨
      ∃ firstNext secondNext,
        step? machine first = some firstNext ∧
        step? machine second = some secondNext ∧
        Configuration.BlankEquivalent firstNext secondNext := by
  rcases h with ⟨hState, hTape⟩
  have hHead := hTape.1
  unfold step?
  have hHalted : machine.isHalted first = machine.isHalted second := by
    unfold Machine.isHalted
    rw [hState]
  rw [hHalted]
  cases hStop : machine.isHalted second with
  | true => exact Or.inl ⟨rfl, rfl⟩
  | false =>
      have hRule : findRule machine.rules first.state first.tape.head =
          findRule machine.rules second.state second.tape.head := by
        rw [hState, hHead]
      rw [hRule]
      cases hFound : findRule machine.rules second.state second.tape.head with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some rule =>
          exact Or.inr ⟨applyRule rule first, applyRule rule second,
            rfl, rfl, applyRule_blankEquivalent rule ⟨hState, hTape⟩⟩

/-- Raw execution cannot distinguish implicit from finitely materialized
exterior blanks. -/
theorem run_blankEquivalent (machine : Machine) (fuel : Nat)
    {first second : Configuration}
    (h : Configuration.BlankEquivalent first second) :
    Configuration.BlankEquivalent (run machine fuel first)
      (run machine fuel second) := by
  induction fuel generalizing first second with
  | zero => exact h
  | succ fuel ih =>
      rw [run_succ, run_succ]
      rcases step?_blankEquivalent machine h with
        hNone | ⟨firstNext, secondNext, hFirst, hSecond, hNext⟩
      · rw [hNone.1, hNone.2]
        exact h
      · rw [hFirst, hSecond]
        exact ih hNext

/-- Pack arbitrary raw input cells into two-cell work symbols.  An odd final
cell is paired with a materialized blank; empty input uses the blank work
focus. -/
def rawInputWorkTape (input : BitString) : WorkTape :=
  WorkTape.ofSymbols
    (packWorkSymbols (input.map TapeSymbol.ofBool))

private theorem encodePack_blankCellAt :
    ∀ (symbols : List TapeSymbol) (index : Nat),
      Tape.blankCellAt (encodeWorkRight (packWorkSymbols symbols)) index =
        Tape.blankCellAt symbols index
  | [], index => by cases index <;> rfl
  | first :: [], index => by
      cases index with
      | zero => rfl
      | succ index => cases index <;> rfl
  | first :: second :: rest, 0 => rfl
  | first :: second :: rest, 1 => rfl
  | first :: second :: rest, index + 2 =>
      encodePack_blankCellAt rest index

/-- The packed work view and ordinary raw input denote the same infinite
blank-extended tape for every input length. -/
theorem encodeWorkTape_rawInputWorkTape_blankEquivalent (input : BitString) :
    Tape.BlankEquivalent (Tape.ofInput input)
      (encodeWorkTape (rawInputWorkTape input)) := by
  cases input with
  | nil =>
      exact ⟨rfl, fun index => by cases index <;> rfl,
        fun index => by cases index <;> rfl⟩
  | cons first rest =>
      cases rest with
      | nil =>
          exact ⟨rfl, fun index => by cases index <;> rfl,
            fun index => by cases index <;> rfl⟩
      | cons second tail =>
          constructor
          · rfl
          constructor
          · intro index
            cases index <;> rfl
          · intro index
            cases index with
            | zero => rfl
            | succ index =>
                exact (encodePack_blankCellAt
                  (tail.map TapeSymbol.ofBool) index).symm

/-- Ordinary raw start configuration agrees with the macro-boundary work
start even for empty and odd inputs. -/
theorem startConfig_compileWorkMachine_blankEquivalent
    (machine : WorkMachine) (input : BitString) :
    Configuration.BlankEquivalent
      (startConfig (compileWorkMachine machine) input)
      (encodeWorkConfiguration
        (workStartConfiguration machine (rawInputWorkTape input))) := by
  constructor
  · rfl
  · exact encodeWorkTape_rawInputWorkTape_blankEquivalent input

end PNP.Concrete

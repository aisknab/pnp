/-
Copyright (c) 2026 PNP Labs.

Blank-tail invariance for work-machine executions.

`WorkTape` stores only a finite materialized window of an otherwise blank
two-track tape.  Controller primitives may materialize a different number of
exterior blank work cells while preserving the same logical tape.  This file
provides the representation-independent relation needed to compose those
literal machines without treating a particular finite blank suffix as data.
-/

import PNP.Concrete.WorkMachine

namespace PNP.Concrete

namespace WorkTape

/-- Read a nearest-first or ordinary work-cell list with an implicit blank
tail. -/
def blankCellAt : List WorkSymbol → Nat → WorkSymbol
  | [], _ => WorkSymbol.blank
  | symbol :: _, 0 => symbol
  | _ :: rest, index + 1 => blankCellAt rest index

@[simp] theorem blankCellAt_nil (index : Nat) :
    blankCellAt [] index = WorkSymbol.blank := by
  rfl

@[simp] theorem blankCellAt_cons_zero
    (symbol : WorkSymbol) (rest : List WorkSymbol) :
    blankCellAt (symbol :: rest) 0 = symbol := by
  rfl

@[simp] theorem blankCellAt_cons_succ
    (symbol : WorkSymbol) (rest : List WorkSymbol) (index : Nat) :
    blankCellAt (symbol :: rest) (index + 1) =
      blankCellAt rest index := by
  rfl

theorem blankCellAt_replicate_blank
    (count index : Nat) :
    blankCellAt
        (List.replicate count WorkSymbol.blank) index =
      WorkSymbol.blank := by
  induction count generalizing index with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      cases index with
      | zero =>
          rfl
      | succ index =>
          exact inductionHypothesis index

/-- Materializing finitely many cells from an implicit exterior blank tail
does not change the represented infinite work-cell list. -/
theorem blankCellAt_append_replicate_blank
    (word : List WorkSymbol) (count index : Nat) :
    blankCellAt
        (word ++ List.replicate count WorkSymbol.blank) index =
      blankCellAt word index := by
  induction word generalizing index with
  | nil =>
      simpa using blankCellAt_replicate_blank count index
  | cons head rest inductionHypothesis =>
      cases index with
      | zero =>
          rfl
      | succ index =>
          simpa using inductionHypothesis index

theorem blankCellAt_append_blank
    (word : List WorkSymbol) (index : Nat) :
    blankCellAt (word ++ [WorkSymbol.blank]) index =
      blankCellAt word index := by
  simpa using
    blankCellAt_append_replicate_blank word 1 index

/-- Two finite work-tape windows denote the same infinite blank tape. -/
structure BlankEquivalent (first second : WorkTape) : Prop where
  head : first.head = second.head
  left : ∀ index,
    blankCellAt first.left index =
      blankCellAt second.left index
  right : ∀ index,
    blankCellAt first.right index =
      blankCellAt second.right index

theorem blankEquivalent_of_padding
    (tape : WorkTape) (leftPadding rightPadding : Nat) :
    BlankEquivalent
      { tape with
        left :=
          tape.left ++
            List.replicate leftPadding WorkSymbol.blank
        right :=
          tape.right ++
            List.replicate rightPadding WorkSymbol.blank }
      tape := by
  refine ⟨rfl, ?_, ?_⟩
  · intro index
    exact blankCellAt_append_replicate_blank
      tape.left leftPadding index
  · intro index
    exact blankCellAt_append_replicate_blank
      tape.right rightPadding index

theorem blankEquivalent_refl (tape : WorkTape) :
    BlankEquivalent tape tape := by
  exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem blankEquivalent_symm {first second : WorkTape}
    (equivalent : BlankEquivalent first second) :
    BlankEquivalent second first := by
  exact
    ⟨equivalent.head.symm,
      fun index => (equivalent.left index).symm,
      fun index => (equivalent.right index).symm⟩

theorem blankEquivalent_trans {first second third : WorkTape}
    (firstEquivalent : BlankEquivalent first second)
    (secondEquivalent : BlankEquivalent second third) :
    BlankEquivalent first third := by
  exact
    ⟨firstEquivalent.head.trans secondEquivalent.head,
      fun index =>
        (firstEquivalent.left index).trans
          (secondEquivalent.left index),
      fun index =>
        (firstEquivalent.right index).trans
          (secondEquivalent.right index)⟩

theorem blankEquivalent_write {first second : WorkTape}
    (equivalent : BlankEquivalent first second)
    (symbol : WorkSymbol) :
    BlankEquivalent (first.write symbol) (second.write symbol) := by
  exact ⟨rfl, equivalent.left, equivalent.right⟩

@[simp] theorem moveLeft_head (tape : WorkTape) :
    tape.moveLeft.head = blankCellAt tape.left 0 := by
  cases tape with
  | mk left head right =>
      cases left <;> rfl

@[simp] theorem moveLeft_left (tape : WorkTape) (index : Nat) :
    blankCellAt tape.moveLeft.left index =
      blankCellAt tape.left (index + 1) := by
  cases tape with
  | mk left head right =>
      cases left <;> rfl

@[simp] theorem moveLeft_right_zero (tape : WorkTape) :
    blankCellAt tape.moveLeft.right 0 = tape.head := by
  cases tape with
  | mk left head right =>
      cases left <;> rfl

@[simp] theorem moveLeft_right_succ
    (tape : WorkTape) (index : Nat) :
    blankCellAt tape.moveLeft.right (index + 1) =
      blankCellAt tape.right index := by
  cases tape with
  | mk left head right =>
      cases left <;> rfl

theorem blankEquivalent_moveLeft {first second : WorkTape}
    (equivalent : BlankEquivalent first second) :
    BlankEquivalent first.moveLeft second.moveLeft := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [moveLeft_head]
    exact equivalent.left 0
  · intro index
    simp only [moveLeft_left]
    exact equivalent.left (index + 1)
  · intro index
    cases index with
    | zero =>
        simp only [moveLeft_right_zero]
        exact equivalent.head
    | succ index =>
        simp only [moveLeft_right_succ]
        exact equivalent.right index

@[simp] theorem moveRight_head (tape : WorkTape) :
    tape.moveRight.head = blankCellAt tape.right 0 := by
  cases tape with
  | mk left head right =>
      cases right <;> rfl

@[simp] theorem moveRight_right (tape : WorkTape) (index : Nat) :
    blankCellAt tape.moveRight.right index =
      blankCellAt tape.right (index + 1) := by
  cases tape with
  | mk left head right =>
      cases right <;> rfl

@[simp] theorem moveRight_left_zero (tape : WorkTape) :
    blankCellAt tape.moveRight.left 0 = tape.head := by
  cases tape with
  | mk left head right =>
      cases right <;> rfl

@[simp] theorem moveRight_left_succ
    (tape : WorkTape) (index : Nat) :
    blankCellAt tape.moveRight.left (index + 1) =
      blankCellAt tape.left index := by
  cases tape with
  | mk left head right =>
      cases right <;> rfl

theorem blankEquivalent_moveRight {first second : WorkTape}
    (equivalent : BlankEquivalent first second) :
    BlankEquivalent first.moveRight second.moveRight := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [moveRight_head]
    exact equivalent.right 0
  · intro index
    cases index with
    | zero =>
        simp only [moveRight_left_zero]
        exact equivalent.head
    | succ index =>
        simp only [moveRight_left_succ]
        exact equivalent.left index
  · intro index
    simp only [moveRight_right]
    exact equivalent.right (index + 1)

theorem blankEquivalent_move {first second : WorkTape}
    (equivalent : BlankEquivalent first second)
    (move : HeadMove) :
    BlankEquivalent (first.move move) (second.move move) := by
  cases move with
  | left => exact blankEquivalent_moveLeft equivalent
  | stay => exact equivalent
  | right => exact blankEquivalent_moveRight equivalent

end WorkTape

namespace WorkConfiguration

/-- Work configurations agree on control and denote the same infinite blank
work tape. -/
structure BlankEquivalent
    (first second : WorkConfiguration) : Prop where
  state : first.state = second.state
  tape : WorkTape.BlankEquivalent first.tape second.tape

theorem blankEquivalent_refl (configuration : WorkConfiguration) :
    BlankEquivalent configuration configuration := by
  exact ⟨rfl, WorkTape.blankEquivalent_refl _⟩

theorem blankEquivalent_symm
    {first second : WorkConfiguration}
    (equivalent : BlankEquivalent first second) :
    BlankEquivalent second first := by
  exact
    ⟨equivalent.state.symm,
      WorkTape.blankEquivalent_symm equivalent.tape⟩

theorem blankEquivalent_trans
    {first second third : WorkConfiguration}
    (firstEquivalent : BlankEquivalent first second)
    (secondEquivalent : BlankEquivalent second third) :
    BlankEquivalent first third := by
  exact
    ⟨firstEquivalent.state.trans secondEquivalent.state,
      WorkTape.blankEquivalent_trans
        firstEquivalent.tape secondEquivalent.tape⟩

end WorkConfiguration

private theorem applyWorkRule_blankEquivalent
    (rule : WorkRule)
    {first second : WorkConfiguration}
    (equivalent :
      WorkConfiguration.BlankEquivalent first second) :
    WorkConfiguration.BlankEquivalent
      (applyWorkRule rule first) (applyWorkRule rule second) := by
  refine ⟨rfl, ?_⟩
  exact WorkTape.blankEquivalent_move
    (WorkTape.blankEquivalent_write equivalent.tape rule.writeSymbol)
    rule.move

theorem workStep?_blankEquivalent
    (machine : WorkMachine)
    {first second : WorkConfiguration}
    (equivalent :
      WorkConfiguration.BlankEquivalent first second) :
    (workStep? machine first = none ∧
        workStep? machine second = none) ∨
      ∃ firstNext secondNext,
        workStep? machine first = some firstNext ∧
        workStep? machine second = some secondNext ∧
        WorkConfiguration.BlankEquivalent firstNext secondNext := by
  have halted :
      machine.isHalted first = machine.isHalted second := by
    unfold WorkMachine.isHalted
    rw [equivalent.state]
  have selected :
      findWorkRule machine.rules first.state first.tape.head =
        findWorkRule machine.rules second.state second.tape.head := by
    rw [equivalent.state, equivalent.tape.head]
  unfold workStep?
  rw [halted]
  cases haltedSecond : machine.isHalted second with
  | true =>
      exact Or.inl ⟨rfl, rfl⟩
  | false =>
      rw [selected]
      cases found :
          findWorkRule machine.rules second.state second.tape.head with
      | none =>
          exact Or.inl ⟨rfl, rfl⟩
      | some rule =>
          exact
            Or.inr
              ⟨applyWorkRule rule first,
                applyWorkRule rule second,
                rfl, rfl,
                applyWorkRule_blankEquivalent rule equivalent⟩

/-- Exact optional executions synchronize across finite representations of
the same infinite blank work tape. -/
theorem workRunExact?_blankEquivalent
    (machine : WorkMachine) (steps : Nat)
    {first second : WorkConfiguration}
    (equivalent :
      WorkConfiguration.BlankEquivalent first second) :
    (workRunExact? machine steps first = none ∧
        workRunExact? machine steps second = none) ∨
      ∃ firstFinal secondFinal,
        workRunExact? machine steps first = some firstFinal ∧
        workRunExact? machine steps second = some secondFinal ∧
        WorkConfiguration.BlankEquivalent
          firstFinal secondFinal := by
  induction steps generalizing first second with
  | zero =>
      exact
        Or.inr
          ⟨first, second, rfl, rfl, equivalent⟩
  | succ steps inductionHypothesis =>
      change
        ((match workStep? machine first with
          | none => none
          | some next => workRunExact? machine steps next) = none ∧
         (match workStep? machine second with
          | none => none
          | some next => workRunExact? machine steps next) = none) ∨
        ∃ firstFinal secondFinal,
          (match workStep? machine first with
            | none => none
            | some next =>
                workRunExact? machine steps next) =
              some firstFinal ∧
          (match workStep? machine second with
            | none => none
            | some next =>
                workRunExact? machine steps next) =
              some secondFinal ∧
          WorkConfiguration.BlankEquivalent
            firstFinal secondFinal
      rcases workStep?_blankEquivalent machine equivalent with
        stopped | ⟨firstNext, secondNext,
          firstStep, secondStep, nextEquivalent⟩
      · rw [stopped.1, stopped.2]
        exact Or.inl ⟨rfl, rfl⟩
      · rw [firstStep, secondStep]
        exact inductionHypothesis nextEquivalent

/-- Transport a known exact run to any blank-equivalent work configuration.
The transported endpoint is existential because its finite exterior blank
window may differ from the canonical endpoint. -/
theorem workRunExact?_transport
    (machine : WorkMachine) (steps : Nat)
    {actual canonical canonicalFinal : WorkConfiguration}
    (equivalent :
      WorkConfiguration.BlankEquivalent actual canonical)
    (canonicalRun :
      workRunExact? machine steps canonical =
        some canonicalFinal) :
    ∃ actualFinal,
      workRunExact? machine steps actual = some actualFinal ∧
      WorkConfiguration.BlankEquivalent
        actualFinal canonicalFinal := by
  rcases workRunExact?_blankEquivalent
      machine steps equivalent with
    stopped | ⟨actualFinal, comparedFinal,
      actualRun, comparedRun, finalEquivalent⟩
  · rw [canonicalRun] at stopped
    cases stopped.2
  · rw [canonicalRun] at comparedRun
    have finalEq :
        comparedFinal = canonicalFinal :=
      (Option.some.inj comparedRun).symm
    subst comparedFinal
    exact ⟨actualFinal, actualRun, finalEquivalent⟩

end PNP.Concrete

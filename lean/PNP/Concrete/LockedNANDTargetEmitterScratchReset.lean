/-
Copyright (c) 2026 PNP Labs.

Literal reset primitive for the locked-NAND target emitter's nearest unary
scratch record.  Starting at the focused source cell, the machine crosses the
source-left boundary, erases the unary count, validates one reserved blank,
moves the separator next to the boundary, and returns to the same source cell.
The retained source, target, reserve capacity, and outer workspace are
preserved.

The executable rule table is fixed and literal.  Unexpected symbols enter a
ruleless dead state; in particular, the machine never overwrites an occupied
reserve cell.
-/

import PNP.Concrete.LockedNANDTargetEmitterCursorAppender
import PNP.Concrete.PipelineMachineSimulation

namespace PNP.Concrete.LockedNAND.TargetEmitterScratchReset

open PNP.Concrete

def startState : Nat := 0
def boundaryState : Nat := 1
def eraseState : Nat := 2
def reserveState : Nat := 3
def returnState : Nat := 4
def placeSeparatorState : Nat := 5
def finishState : Nat := 6
def acceptState : Nat := 7
def rejectState : Nat := 8
def deadState : Nat := 9

def unaryUnit : WorkSymbol := TargetEmitter.unaryUnit
def unarySeparator : WorkSymbol := TargetEmitter.unarySeparator
def sourceLeftBoundary : WorkSymbol := TargetEmitter.sourceLeftBoundary
def cursorMarker : WorkSymbol :=
  TargetEmitterCursorAppender.cursorMarker

def allWorkSymbols : List WorkSymbol :=
  TargetEmitter.allWorkSymbols

structure StateProgram where
  state : Nat
  action : WorkSymbol → Nat × WorkSymbol × HeadMove

def deadAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  (deadState, symbol, .stay)

def sourceAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨
      symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨
      symbol = WorkSymbol.oneOne ∨
      symbol = cursorMarker then
    (boundaryState, symbol, .left)
  else
    deadAction symbol

def boundaryAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = sourceLeftBoundary then
    (eraseState, symbol, .left)
  else
    deadAction symbol

def eraseAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (eraseState, WorkSymbol.blank, .left)
  else if symbol = unarySeparator then
    (reserveState, WorkSymbol.blank, .left)
  else
    deadAction symbol

def reserveAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.blank then
    (returnState, symbol, .right)
  else
    deadAction symbol

def returnAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.blank then
    (returnState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (placeSeparatorState, symbol, .left)
  else
    deadAction symbol

def placeSeparatorAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.blank then
    (finishState, unarySeparator, .right)
  else
    deadAction symbol

def finishAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = sourceLeftBoundary then
    (acceptState, symbol, .right)
  else
    deadAction symbol

def statePrograms : List StateProgram :=
  [ { state := startState, action := sourceAction }
  , { state := boundaryState, action := boundaryAction }
  , { state := eraseState, action := eraseAction }
  , { state := reserveState, action := reserveAction }
  , { state := returnState, action := returnAction }
  , { state := placeSeparatorState, action := placeSeparatorAction }
  , { state := finishState, action := finishAction } ]

def rulesAt (program : StateProgram) : List WorkRule :=
  allWorkSymbols.map fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.1
      writeSymbol := action.2.1
      move := action.2.2 }

def rules : List WorkRule :=
  statePrograms.flatMap rulesAt

def machine : WorkMachine :=
  { rules := rules
    startState := startState
    acceptState := acceptState
    rejectState := rejectState }

def compiledMachine : Machine :=
  compileWorkMachine machine

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem rulesAt_length (program : StateProgram) :
    (rulesAt program).length = 9 := by
  rfl

theorem statePrograms_length :
    statePrograms.length = 7 := by
  rfl

theorem rules_length :
    rules.length = 63 := by
  rfl

private theorem rulesAt_pairwise (program : StateProgram) :
    (rulesAt program).Pairwise QueryDistinct := by
  unfold rulesAt allWorkSymbols TargetEmitter.allWorkSymbols
  simp [QueryDistinct,
    WorkSymbol.blank, WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem rulesAt_source
    {program : StateProgram} {rule : WorkRule}
    (member : rule ∈ rulesAt program) :
    rule.sourceState = program.state := by
  rcases List.mem_map.mp member with
    ⟨symbol, _symbolMember, equality⟩
  rw [← equality]

private theorem statePrograms_pairwise :
    statePrograms.Pairwise
      (fun left right => left.state ≠ right.state) := by
  decide

private theorem materialized_pairwise
    (programs : List StateProgram)
    (distinct :
      programs.Pairwise (fun left right => left.state ≠ right.state)) :
    (programs.flatMap rulesAt).Pairwise QueryDistinct := by
  induction programs with
  | nil =>
      simp
  | cons program rest ih =>
      rw [List.flatMap_cons, List.pairwise_append]
      refine
        ⟨rulesAt_pairwise program,
          ih (List.pairwise_cons.mp distinct).2,
          ?_⟩
      intro left leftMember right rightMember
      have leftSource := rulesAt_source leftMember
      rcases List.mem_flatMap.mp rightMember with
        ⟨rightProgram, rightProgramMember, rightRuleMember⟩
      have rightSource := rulesAt_source rightRuleMember
      have stateNe :
          program.state ≠ rightProgram.state :=
        (List.pairwise_cons.mp distinct).1 rightProgram
          rightProgramMember
      intro queryEqual
      exact stateNe
        (leftSource.symm.trans
          ((congrArg Prod.fst queryEqual).trans rightSource))

theorem rules_pairwise :
    rules.Pairwise QueryDistinct := by
  exact materialized_pairwise statePrograms statePrograms_pairwise

theorem start_ne_accept :
    machine.startState ≠ machine.acceptState := by
  decide

theorem start_ne_reject :
    machine.startState ≠ machine.rejectState := by
  decide

theorem accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  decide

set_option maxRecDepth 100000 in
theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules acceptState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules rejectState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule rules deadState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

def configAtWord (state : Nat)
    (left word : List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtWord state left word

def configAtLeftWord (state : Nat)
    (leftWord right : List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtLeftWord state leftWord right

private theorem exactRun_add (first second : Nat)
    (initial middle final : WorkConfiguration)
    (hFirst :
      workRunExact? machine first initial = some middle)
    (hSecond :
      workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial = some final :=
  PipelineMachineSimulation.workRunExact?_compose
    machine first second initial middle final hFirst hSecond

private theorem exactRun_one
    (initial final : WorkConfiguration)
    (step : workStep? machine initial = some final) :
    workRunExact? machine 1 initial = some final := by
  change
    (match workStep? machine initial with
     | none => none
     | some next => workRunExact? machine 0 next) =
      some final
  rw [step]
  rfl

private def literalRule (source : Nat) (read : WorkSymbol)
    (target : Nat) (write : WorkSymbol) (move : HeadMove) :
    WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

private theorem replicate_succ_append {α : Type}
    (count : Nat) (item : α) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change
        item :: List.replicate (count + 1) item =
          item :: (List.replicate count item ++ [item])
      rw [ih]

set_option maxRecDepth 100000 in
private theorem find_start_source
    (symbol : WorkSymbol)
    (allowed :
      TargetEmitter.PackedSymbol symbol ∨ symbol = cursorMarker) :
    findWorkRule rules startState symbol =
      some
        (literalRule startState symbol boundaryState symbol .left) := by
  rcases allowed with packed | cursor
  · cases packed <;> decide
  · subst symbol
    decide

set_option maxRecDepth 100000 in
private theorem find_boundary :
    findWorkRule rules boundaryState sourceLeftBoundary =
      some
        (literalRule boundaryState sourceLeftBoundary
          eraseState sourceLeftBoundary .left) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_erase_unit :
    findWorkRule rules eraseState unaryUnit =
      some
        (literalRule eraseState unaryUnit
          eraseState WorkSymbol.blank .left) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_erase_separator :
    findWorkRule rules eraseState unarySeparator =
      some
        (literalRule eraseState unarySeparator
          reserveState WorkSymbol.blank .left) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_reserve_blank :
    findWorkRule rules reserveState WorkSymbol.blank =
      some
        (literalRule reserveState WorkSymbol.blank
          returnState WorkSymbol.blank .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_return_blank :
    findWorkRule rules returnState WorkSymbol.blank =
      some
        (literalRule returnState WorkSymbol.blank
          returnState WorkSymbol.blank .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_return_boundary :
    findWorkRule rules returnState sourceLeftBoundary =
      some
        (literalRule returnState sourceLeftBoundary
          placeSeparatorState sourceLeftBoundary .left) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_place_blank :
    findWorkRule rules placeSeparatorState WorkSymbol.blank =
      some
        (literalRule placeSeparatorState WorkSymbol.blank
          finishState unarySeparator .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_finish_boundary :
    findWorkRule rules finishState sourceLeftBoundary =
      some
        (literalRule finishState sourceLeftBoundary
          acceptState sourceLeftBoundary .right) := by
  decide

private theorem source_step (symbol : WorkSymbol)
    (allowed :
      TargetEmitter.PackedSymbol symbol ∨ symbol = cursorMarker)
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord startState left (symbol :: right)) =
      some
        (configAtLeftWord boundaryState left (symbol :: right)) := by
  apply exactRun_one
  have notHalted :
      machine.isHalted
        (configAtWord startState left (symbol :: right)) = false := by
    rfl
  calc
    workStep? machine
        (configAtWord startState left (symbol :: right)) =
      some
        (applyWorkRule
          (literalRule startState symbol
            boundaryState symbol .left)
          (configAtWord startState left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_start_source symbol allowed)
    _ = some
        (configAtLeftWord boundaryState left
          (symbol :: right)) := by
      cases left <;> rfl

private theorem boundary_step
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord boundaryState
          (sourceLeftBoundary :: left) right) =
      some
        (configAtLeftWord eraseState left
          (sourceLeftBoundary :: right)) := by
  apply exactRun_one
  have notHalted :
      machine.isHalted
        (configAtLeftWord boundaryState
          (sourceLeftBoundary :: left) right) = false := by
    rfl
  calc
    workStep? machine
        (configAtLeftWord boundaryState
          (sourceLeftBoundary :: left) right) =
      some
        (applyWorkRule
          (literalRule boundaryState sourceLeftBoundary
            eraseState sourceLeftBoundary .left)
          (configAtLeftWord boundaryState
            (sourceLeftBoundary :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted find_boundary
    _ = some
        (configAtLeftWord eraseState left
          (sourceLeftBoundary :: right)) := by
      cases left <;> rfl

private theorem erase_unit_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord eraseState
          (unaryUnit :: leftTail) rightSide) =
      some
        (configAtLeftWord eraseState
          leftTail (WorkSymbol.blank :: rightSide)) := by
  have notHalted :
      machine.isHalted
        (configAtLeftWord eraseState
          (unaryUnit :: leftTail) rightSide) = false := by
    rfl
  calc
    workStep? machine
        (configAtLeftWord eraseState
          (unaryUnit :: leftTail) rightSide) =
      some
        (applyWorkRule
          (literalRule eraseState unaryUnit
            eraseState WorkSymbol.blank .left)
          (configAtLeftWord eraseState
            (unaryUnit :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted find_erase_unit
    _ = some
        (configAtLeftWord eraseState
          leftTail (WorkSymbol.blank :: rightSide)) := by
      cases leftTail <;> rfl

private theorem erase_units_exact
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? machine count
        (configAtLeftWord eraseState
          (List.replicate count unaryUnit ++ left) right) =
      some
        (configAtLeftWord eraseState left
          (List.replicate count WorkSymbol.blank ++ right)) := by
  induction count generalizing right with
  | zero =>
      rfl
  | succ count ih =>
      change
        (match
          workStep? machine
            (configAtLeftWord eraseState
              (unaryUnit ::
                (List.replicate count unaryUnit ++ left)) right)
        with
        | none => none
        | some next =>
            workRunExact? machine count next) = _
      rw [erase_unit_step]
      simpa [replicate_succ_append, List.append_assoc] using
        ih (WorkSymbol.blank :: right)

private theorem erase_separator_step
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord eraseState
          (unarySeparator :: left) right) =
      some
        (configAtLeftWord reserveState left
          (WorkSymbol.blank :: right)) := by
  apply exactRun_one
  have notHalted :
      machine.isHalted
        (configAtLeftWord eraseState
          (unarySeparator :: left) right) = false := by
    rfl
  calc
    workStep? machine
        (configAtLeftWord eraseState
          (unarySeparator :: left) right) =
      some
        (applyWorkRule
          (literalRule eraseState unarySeparator
            reserveState WorkSymbol.blank .left)
          (configAtLeftWord eraseState
            (unarySeparator :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        find_erase_separator
    _ = some
        (configAtLeftWord reserveState left
          (WorkSymbol.blank :: right)) := by
      cases left <;> rfl

private theorem reserve_blank_step
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord reserveState
          (WorkSymbol.blank :: left) right) =
      some
        (configAtWord returnState
          (WorkSymbol.blank :: left) right) := by
  apply exactRun_one
  have notHalted :
      machine.isHalted
        (configAtLeftWord reserveState
          (WorkSymbol.blank :: left) right) = false := by
    rfl
  calc
    workStep? machine
        (configAtLeftWord reserveState
          (WorkSymbol.blank :: left) right) =
      some
        (applyWorkRule
          (literalRule reserveState WorkSymbol.blank
            returnState WorkSymbol.blank .right)
          (configAtLeftWord reserveState
            (WorkSymbol.blank :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        find_reserve_blank
    _ = some
        (configAtWord returnState
          (WorkSymbol.blank :: left) right) := by
      cases right <;> rfl

private theorem return_blank_step
    (leftSide rightTail : List WorkSymbol) :
    workStep? machine
        (configAtWord returnState leftSide
          (WorkSymbol.blank :: rightTail)) =
      some
        (configAtWord returnState
          (WorkSymbol.blank :: leftSide) rightTail) := by
  have notHalted :
      machine.isHalted
        (configAtWord returnState leftSide
          (WorkSymbol.blank :: rightTail)) = false := by
    rfl
  calc
    workStep? machine
        (configAtWord returnState leftSide
          (WorkSymbol.blank :: rightTail)) =
      some
        (applyWorkRule
          (literalRule returnState WorkSymbol.blank
            returnState WorkSymbol.blank .right)
          (configAtWord returnState leftSide
            (WorkSymbol.blank :: rightTail))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted find_return_blank
    _ = some
        (configAtWord returnState
          (WorkSymbol.blank :: leftSide) rightTail) := by
      cases rightTail <;> rfl

private theorem return_word_exact
    (blanks left right : List WorkSymbol)
    (allBlank :
      ∀ symbol, symbol ∈ blanks → symbol = WorkSymbol.blank) :
    workRunExact? machine blanks.length
        (configAtWord returnState left (blanks ++ right)) =
      some
        (configAtWord returnState
          (blanks.reverse ++ left) right) := by
  induction blanks generalizing left with
  | nil =>
      rfl
  | cons head rest ih =>
      have headEq :
          head = WorkSymbol.blank :=
        allBlank head (List.Mem.head rest)
      subst head
      have restBlank :
          ∀ symbol, symbol ∈ rest →
            symbol = WorkSymbol.blank := by
        intro symbol member
        exact allBlank symbol
          (List.Mem.tail WorkSymbol.blank member)
      change
        (match
          workStep? machine
            (configAtWord returnState left
              (WorkSymbol.blank :: (rest ++ right)))
        with
        | none => none
        | some next =>
            workRunExact? machine rest.length next) = _
      rw [return_blank_step]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (WorkSymbol.blank :: left) restBlank

private theorem return_blanks_exact
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? machine count
        (configAtWord returnState left
          (List.replicate count WorkSymbol.blank ++ right)) =
      some
        (configAtWord returnState
          (List.replicate count WorkSymbol.blank ++ left) right) := by
  simpa using
    return_word_exact (List.replicate count WorkSymbol.blank)
      left right (by simp)

private theorem return_boundary_step
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord returnState left
          (sourceLeftBoundary :: right)) =
      some
        (configAtLeftWord placeSeparatorState left
          (sourceLeftBoundary :: right)) := by
  apply exactRun_one
  have notHalted :
      machine.isHalted
        (configAtWord returnState left
          (sourceLeftBoundary :: right)) = false := by
    rfl
  calc
    workStep? machine
        (configAtWord returnState left
          (sourceLeftBoundary :: right)) =
      some
        (applyWorkRule
          (literalRule returnState sourceLeftBoundary
            placeSeparatorState sourceLeftBoundary .left)
          (configAtWord returnState left
            (sourceLeftBoundary :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        find_return_boundary
    _ = some
        (configAtLeftWord placeSeparatorState left
          (sourceLeftBoundary :: right)) := by
      cases left <;> rfl

private theorem place_separator_step
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord placeSeparatorState
          (WorkSymbol.blank :: left) right) =
      some
        (configAtWord finishState
          (unarySeparator :: left) right) := by
  apply exactRun_one
  have notHalted :
      machine.isHalted
        (configAtLeftWord placeSeparatorState
          (WorkSymbol.blank :: left) right) = false := by
    rfl
  calc
    workStep? machine
        (configAtLeftWord placeSeparatorState
          (WorkSymbol.blank :: left) right) =
      some
        (applyWorkRule
          (literalRule placeSeparatorState WorkSymbol.blank
            finishState unarySeparator .right)
          (configAtLeftWord placeSeparatorState
            (WorkSymbol.blank :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted find_place_blank
    _ = some
        (configAtWord finishState
          (unarySeparator :: left) right) := by
      cases right <;> rfl

private theorem finish_boundary_step
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord finishState left
          (sourceLeftBoundary :: right)) =
      some
        (configAtWord acceptState
          (sourceLeftBoundary :: left) right) := by
  apply exactRun_one
  have notHalted :
      machine.isHalted
        (configAtWord finishState left
          (sourceLeftBoundary :: right)) = false := by
    rfl
  calc
    workStep? machine
        (configAtWord finishState left
          (sourceLeftBoundary :: right)) =
      some
        (applyWorkRule
          (literalRule finishState sourceLeftBoundary
            acceptState sourceLeftBoundary .right)
          (configAtWord finishState left
            (sourceLeftBoundary :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        find_finish_boundary
    _ = some
        (configAtWord acceptState
          (sourceLeftBoundary :: left) right) := by
      cases right <;> rfl

def entryConfiguration (count : Nat)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight reserve outsideLeft :
      List WorkSymbol) : WorkConfiguration :=
  configAtWord startState
    (sourceLeftBoundary ::
      (List.replicate count unaryUnit ++
        unarySeparator :: WorkSymbol.blank :: reserve ++ outsideLeft))
    (sourceHead :: sourceTail ++ targetAndRight)

def finalConfiguration (count : Nat)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight reserve outsideLeft :
      List WorkSymbol) : WorkConfiguration :=
  configAtWord acceptState
    (sourceLeftBoundary ::
      unarySeparator ::
        (List.replicate (count + 1) WorkSymbol.blank ++
          reserve ++ outsideLeft))
    (sourceHead :: sourceTail ++ targetAndRight)

def workSteps (count : Nat) : Nat :=
  2 * count + 8

theorem workSteps_evaluated (count : Nat) :
    workSteps count = 2 * count + 8 := by
  rfl

theorem exact (count : Nat)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight reserve outsideLeft :
      List WorkSymbol)
    (sourceAllowed :
      TargetEmitter.PackedSymbol sourceHead ∨
        sourceHead = cursorMarker) :
    workRunExact? machine (workSteps count)
        (entryConfiguration count sourceHead sourceTail
          targetAndRight reserve outsideLeft) =
      some
        (finalConfiguration count sourceHead sourceTail
          targetAndRight reserve outsideLeft) := by
  let sourceWord := sourceHead :: sourceTail ++ targetAndRight
  let scratchTail :=
    List.replicate count unaryUnit ++
      unarySeparator :: WorkSymbol.blank :: reserve ++ outsideLeft
  let afterSource :=
    configAtLeftWord boundaryState
      (sourceLeftBoundary :: scratchTail) sourceWord
  let afterBoundary :=
    configAtLeftWord eraseState scratchTail
      (sourceLeftBoundary :: sourceWord)
  let atSeparator :=
    configAtLeftWord eraseState
      (unarySeparator :: WorkSymbol.blank :: reserve ++ outsideLeft)
      (List.replicate count WorkSymbol.blank ++
        sourceLeftBoundary :: sourceWord)
  let atReserve :=
    configAtLeftWord reserveState
      (WorkSymbol.blank :: reserve ++ outsideLeft)
      (WorkSymbol.blank ::
        List.replicate count WorkSymbol.blank ++
          sourceLeftBoundary :: sourceWord)
  let returning :=
    configAtWord returnState
      (WorkSymbol.blank :: reserve ++ outsideLeft)
      (List.replicate (count + 1) WorkSymbol.blank ++
        sourceLeftBoundary :: sourceWord)
  let atBoundary :=
    configAtWord returnState
      (List.replicate (count + 1) WorkSymbol.blank ++
        WorkSymbol.blank :: reserve ++ outsideLeft)
      (sourceLeftBoundary :: sourceWord)
  let atPlace :=
    configAtLeftWord placeSeparatorState
      (List.replicate (count + 1) WorkSymbol.blank ++
        WorkSymbol.blank :: reserve ++ outsideLeft)
      (sourceLeftBoundary :: sourceWord)
  let atFinish :=
    configAtWord finishState
      (unarySeparator ::
        (List.replicate count WorkSymbol.blank ++
          WorkSymbol.blank :: reserve ++ outsideLeft))
      (sourceLeftBoundary :: sourceWord)
  have hSource :=
    source_step sourceHead sourceAllowed
      (sourceLeftBoundary :: scratchTail)
      (sourceTail ++ targetAndRight)
  have hSourceCanonical :
      workRunExact? machine 1
          (entryConfiguration count sourceHead sourceTail
            targetAndRight reserve outsideLeft) =
        some afterSource := by
    simpa [entryConfiguration, afterSource, scratchTail,
      sourceWord, List.append_assoc] using hSource
  have hBoundary :=
    boundary_step scratchTail sourceWord
  have hBoundaryCanonical :
      workRunExact? machine 1 afterSource =
        some afterBoundary := by
    simpa [afterSource, afterBoundary] using hBoundary
  have hErase :=
    erase_units_exact count
      (unarySeparator :: WorkSymbol.blank :: reserve ++ outsideLeft)
      (sourceLeftBoundary :: sourceWord)
  have hEraseCanonical :
      workRunExact? machine count afterBoundary =
        some atSeparator := by
    simpa [afterBoundary, atSeparator, scratchTail,
      List.append_assoc] using hErase
  have hSeparator :=
    erase_separator_step
      (WorkSymbol.blank :: reserve ++ outsideLeft)
      (List.replicate count WorkSymbol.blank ++
        sourceLeftBoundary :: sourceWord)
  have hSeparatorCanonical :
      workRunExact? machine 1 atSeparator =
        some atReserve := by
    simpa [atSeparator, atReserve] using hSeparator
  have hReserve :=
    reserve_blank_step
      (reserve ++ outsideLeft)
      (WorkSymbol.blank ::
        List.replicate count WorkSymbol.blank ++
          sourceLeftBoundary :: sourceWord)
  have hReserveCanonical :
      workRunExact? machine 1 atReserve =
        some returning := by
    simpa [atReserve, returning, List.replicate_succ,
      List.append_assoc] using hReserve
  have hReturn :=
    return_blanks_exact (count + 1)
      (WorkSymbol.blank :: reserve ++ outsideLeft)
      (sourceLeftBoundary :: sourceWord)
  have hReturnCanonical :
      workRunExact? machine (count + 1) returning =
        some atBoundary := by
    simpa [returning, atBoundary] using hReturn
  have hBoundaryReturn :=
    return_boundary_step
      (List.replicate (count + 1) WorkSymbol.blank ++
        WorkSymbol.blank :: reserve ++ outsideLeft)
      sourceWord
  have hBoundaryReturnCanonical :
      workRunExact? machine 1 atBoundary =
        some atPlace := by
    simpa [atBoundary, atPlace] using hBoundaryReturn
  have hPlace :=
    place_separator_step
      (List.replicate count WorkSymbol.blank ++
        WorkSymbol.blank :: reserve ++ outsideLeft)
      (sourceLeftBoundary :: sourceWord)
  have hPlaceCanonical :
      workRunExact? machine 1 atPlace =
        some atFinish := by
    simpa [atPlace, atFinish, List.replicate_succ,
      List.append_assoc] using hPlace
  have hFinish :=
    finish_boundary_step
      (unarySeparator ::
        (List.replicate count WorkSymbol.blank ++
          WorkSymbol.blank :: reserve ++ outsideLeft))
      sourceWord
  have hFinishCanonical :
      workRunExact? machine 1 atFinish =
        some
          (finalConfiguration count sourceHead sourceTail
            targetAndRight reserve outsideLeft) := by
    simpa [atFinish, finalConfiguration, sourceWord,
      replicate_succ_append, List.append_assoc] using hFinish
  have h01 := exactRun_add 1 1 _ _ _
    hSourceCanonical hBoundaryCanonical
  have h02 := exactRun_add 2 count _ _ _ h01 hEraseCanonical
  have h03 := exactRun_add (2 + count) 1 _ _ _
    h02 hSeparatorCanonical
  have h04 := exactRun_add (2 + count + 1) 1 _ _ _
    h03 hReserveCanonical
  have h05 := exactRun_add (2 + count + 1 + 1) (count + 1)
    _ _ _ h04 hReturnCanonical
  have h06 := exactRun_add
    (2 + count + 1 + 1 + (count + 1)) 1
    _ _ _ h05 hBoundaryReturnCanonical
  have h07 := exactRun_add
    (2 + count + 1 + 1 + (count + 1) + 1) 1
    _ _ _ h06 hPlaceCanonical
  have all := exactRun_add
    (2 + count + 1 + 1 + (count + 1) + 1 + 1) 1
    _ _ _ h07 hFinishCanonical
  have steps :
      2 + count + 1 + 1 + (count + 1) + 1 + 1 + 1 =
        workSteps count := by
    unfold workSteps
    omega
  rw [steps] at all
  exact all

theorem final_halted (count : Nat)
    (sourceHead : WorkSymbol)
    (sourceTail targetAndRight reserve outsideLeft :
      List WorkSymbol) :
    machine.isHalted
      (finalConfiguration count sourceHead sourceTail
        targetAndRight reserve outsideLeft) = true := by
  rfl

set_option maxRecDepth 100000 in
private theorem find_source_malformed
    (symbol : WorkSymbol)
    (notPacked : ¬ TargetEmitter.PackedSymbol symbol)
    (notCursor : symbol ≠ cursorMarker) :
    findWorkRule rules startState symbol =
      some
        (literalRule startState symbol
          deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · decide
  · decide
  · decide
  · decide
  · exact
      (notPacked TargetEmitter.PackedSymbol.zeroZero).elim
  · exact
      (notPacked TargetEmitter.PackedSymbol.zeroOne).elim
  · exact (notCursor rfl).elim
  · exact
      (notPacked TargetEmitter.PackedSymbol.oneZero).elim
  · exact
      (notPacked TargetEmitter.PackedSymbol.oneOne).elim

set_option maxRecDepth 100000 in
private theorem find_boundary_malformed
    (symbol : WorkSymbol)
    (malformed : symbol ≠ sourceLeftBoundary) :
    findWorkRule rules boundaryState symbol =
      some
        (literalRule boundaryState symbol
          deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · decide
  · exact (malformed rfl).elim
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_counter_malformed
    (symbol : WorkSymbol)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    findWorkRule rules eraseState symbol =
      some
        (literalRule eraseState symbol
          deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · decide
  · decide
  · decide
  · exact (notUnit rfl).elim
  · decide
  · decide
  · exact (notSeparator rfl).elim
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_reserve_occupied
    (symbol : WorkSymbol)
    (occupied : symbol ≠ WorkSymbol.blank) :
    findWorkRule rules reserveState symbol =
      some
        (literalRule reserveState symbol
          deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · exact (occupied rfl).elim
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_return_malformed
    (symbol : WorkSymbol)
    (notBlank : symbol ≠ WorkSymbol.blank)
    (notBoundary : symbol ≠ sourceLeftBoundary) :
    findWorkRule rules returnState symbol =
      some
        (literalRule returnState symbol
          deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · exact (notBlank rfl).elim
  · exact (notBoundary rfl).elim
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_place_occupied
    (symbol : WorkSymbol)
    (occupied : symbol ≠ WorkSymbol.blank) :
    findWorkRule rules placeSeparatorState symbol =
      some
        (literalRule placeSeparatorState symbol
          deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · exact (occupied rfl).elim
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_finish_malformed
    (symbol : WorkSymbol)
    (malformed : symbol ≠ sourceLeftBoundary) :
    findWorkRule rules finishState symbol =
      some
        (literalRule finishState symbol
          deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · decide
  · exact (malformed rfl).elim
  all_goals decide

private theorem left_dead_step
    (state : Nat) (symbol : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      machine.isHalted
        (configAtLeftWord state (symbol :: left) right) = false)
    (found :
      findWorkRule rules state symbol =
        some
          (literalRule state symbol
            deadState symbol .stay)) :
    workStep? machine
        (configAtLeftWord state (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  calc
    workStep? machine
        (configAtLeftWord state (symbol :: left) right) =
      some
        (applyWorkRule
          (literalRule state symbol deadState symbol .stay)
          (configAtLeftWord state (symbol :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
      rfl

/-- A non-source symbol at entry fails closed without changing the tape. -/
theorem malformed_source_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notPacked : ¬ TargetEmitter.PackedSymbol symbol)
    (notCursor : symbol ≠ cursorMarker) :
    workStep? machine
        (configAtWord startState left (symbol :: right)) =
      some
        (configAtWord deadState left (symbol :: right)) := by
  have notHalted :
      machine.isHalted
        (configAtWord startState left (symbol :: right)) = false := by
    rfl
  calc
    workStep? machine
        (configAtWord startState left (symbol :: right)) =
      some
        (applyWorkRule
          (literalRule startState symbol deadState symbol .stay)
          (configAtWord startState left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_source_malformed symbol notPacked notCursor)
    _ = some
        (configAtWord deadState left
          (symbol :: right)) := by
      rfl

/-- A missing source-left boundary fails closed without changing the tape. -/
theorem malformed_boundary_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (malformed : symbol ≠ sourceLeftBoundary) :
    workStep? machine
        (configAtLeftWord boundaryState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  exact left_dead_step boundaryState symbol left right
    (by rfl) (find_boundary_malformed symbol malformed)

/-- A symbol other than a unary unit or separator in the counter scan fails
closed without changing the tape. -/
theorem malformed_counter_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    workStep? machine
        (configAtLeftWord eraseState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  exact left_dead_step eraseState symbol left right
    (by rfl)
    (find_counter_malformed symbol notUnit notSeparator)

/-- Scratch capacity is fail-closed: an occupied cell beyond the old
separator is observed but never overwritten. -/
theorem occupied_reserve_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (occupied : symbol ≠ WorkSymbol.blank) :
    workStep? machine
        (configAtLeftWord reserveState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  exact left_dead_step reserveState symbol left right
    (by rfl) (find_reserve_occupied symbol occupied)

/-- The return scan accepts only reclaimed blanks and the source boundary. -/
theorem malformed_return_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notBlank : symbol ≠ WorkSymbol.blank)
    (notBoundary : symbol ≠ sourceLeftBoundary) :
    workStep? machine
        (configAtWord returnState left (symbol :: right)) =
      some
        (configAtWord deadState left (symbol :: right)) := by
  have notHalted :
      machine.isHalted
        (configAtWord returnState left (symbol :: right)) = false := by
    rfl
  calc
    workStep? machine
        (configAtWord returnState left (symbol :: right)) =
      some
        (applyWorkRule
          (literalRule returnState symbol deadState symbol .stay)
          (configAtWord returnState left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_return_malformed symbol notBlank notBoundary)
    _ = some
        (configAtWord deadState left
          (symbol :: right)) := by
      rfl

/-- The new separator is written only into a reclaimed blank. -/
theorem occupied_separator_slot_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (occupied : symbol ≠ WorkSymbol.blank) :
    workStep? machine
        (configAtLeftWord placeSeparatorState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  exact left_dead_step placeSeparatorState symbol left right
    (by rfl) (find_place_occupied symbol occupied)

/-- The final crossing accepts only the retained source-left boundary. -/
theorem malformed_finish_boundary_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (malformed : symbol ≠ sourceLeftBoundary) :
    workStep? machine
        (configAtWord finishState left (symbol :: right)) =
      some
        (configAtWord deadState left (symbol :: right)) := by
  have notHalted :
      machine.isHalted
        (configAtWord finishState left (symbol :: right)) = false := by
    rfl
  calc
    workStep? machine
        (configAtWord finishState left (symbol :: right)) =
      some
        (applyWorkRule
          (literalRule finishState symbol deadState symbol .stay)
          (configAtWord finishState left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_finish_malformed symbol malformed)
    _ = some
        (configAtWord deadState left
          (symbol :: right)) := by
      rfl

theorem dead_stuck (tape : WorkTape) :
    workStep? machine { state := deadState, tape := tape } = none := by
  have notHalted :
      machine.isHalted { state := deadState, tape := tape } = false := by
    rfl
  unfold workStep?
  rw [notHalted]
  change
    (match findWorkRule rules deadState tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           { state := deadState, tape := tape })) = none
  rw [no_rule_at_dead]

end PNP.Concrete.LockedNAND.TargetEmitterScratchReset

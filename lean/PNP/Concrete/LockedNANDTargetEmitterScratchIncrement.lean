/-
Copyright (c) 2026 PNP Labs.

Literal increment primitive for the locked-NAND target emitter's nearest unary
scratch record.  Starting at the focused source cell, the machine crosses the
source-left boundary, replaces the scratch separator by one unary unit, moves
the separator into the next reserved blank, and returns to the same source
cell.  The retained source, target, and all outer workspace are untouched.
-/

import PNP.Concrete.LockedNANDTargetEmitterCursorAppender
import PNP.Concrete.PipelineMachineSimulation

namespace PNP.Concrete.LockedNAND.TargetEmitterScratchIncrement

open PNP.Concrete

def startState : Nat := 0
def boundaryState : Nat := 1
def seekSeparatorState : Nat := 2
def writeSeparatorState : Nat := 3
def returnState : Nat := 4
def acceptState : Nat := 5
def rejectState : Nat := 6
def deadState : Nat := 7

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
    (seekSeparatorState, symbol, .left)
  else
    deadAction symbol

def seekSeparatorAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (seekSeparatorState, symbol, .left)
  else if symbol = unarySeparator then
    (writeSeparatorState, unaryUnit, .left)
  else
    deadAction symbol

def writeSeparatorAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.blank then
    (returnState, unarySeparator, .right)
  else
    deadAction symbol

def returnAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (returnState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (acceptState, symbol, .right)
  else
    deadAction symbol

def statePrograms : List StateProgram :=
  [ { state := startState, action := sourceAction }
  , { state := boundaryState, action := boundaryAction }
  , { state := seekSeparatorState, action := seekSeparatorAction }
  , { state := writeSeparatorState, action := writeSeparatorAction }
  , { state := returnState, action := returnAction } ]

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
    statePrograms.length = 5 := by
  rfl

theorem rules_length :
    rules.length = 45 := by
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
          seekSeparatorState sourceLeftBoundary .left) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_seek_unit :
    findWorkRule rules seekSeparatorState unaryUnit =
      some
        (literalRule seekSeparatorState unaryUnit
          seekSeparatorState unaryUnit .left) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_seek_separator :
    findWorkRule rules seekSeparatorState unarySeparator =
      some
        (literalRule seekSeparatorState unarySeparator
          writeSeparatorState unaryUnit .left) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_write_blank :
    findWorkRule rules writeSeparatorState WorkSymbol.blank =
      some
        (literalRule writeSeparatorState WorkSymbol.blank
          returnState unarySeparator .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_return_unit :
    findWorkRule rules returnState unaryUnit =
      some
        (literalRule returnState unaryUnit
          returnState unaryUnit .right) := by
  decide

set_option maxRecDepth 100000 in
private theorem find_return_boundary :
    findWorkRule rules returnState sourceLeftBoundary =
      some
        (literalRule returnState sourceLeftBoundary
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
        (configAtLeftWord seekSeparatorState left
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
            seekSeparatorState sourceLeftBoundary .left)
          (configAtLeftWord boundaryState
            (sourceLeftBoundary :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted find_boundary
    _ = some
        (configAtLeftWord seekSeparatorState left
          (sourceLeftBoundary :: right)) := by
      cases left <;> rfl

private theorem seek_unit_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? machine
        (configAtLeftWord seekSeparatorState
          (unaryUnit :: leftTail) rightSide) =
      some
        (configAtLeftWord seekSeparatorState
          leftTail (unaryUnit :: rightSide)) := by
  have notHalted :
      machine.isHalted
        (configAtLeftWord seekSeparatorState
          (unaryUnit :: leftTail) rightSide) =
        false := by
    rfl
  calc
    workStep? machine
        (configAtLeftWord seekSeparatorState
          (unaryUnit :: leftTail) rightSide) =
      some
        (applyWorkRule
          (literalRule seekSeparatorState unaryUnit
            seekSeparatorState unaryUnit .left)
          (configAtLeftWord seekSeparatorState
            (unaryUnit :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted find_seek_unit
    _ = some
        (configAtLeftWord seekSeparatorState
          leftTail (unaryUnit :: rightSide)) := by
      cases leftTail <;> rfl

private theorem seek_word_exact
    (units left right : List WorkSymbol)
    (allUnits :
      ∀ symbol, symbol ∈ units → symbol = unaryUnit) :
    workRunExact? machine units.length
        (configAtLeftWord seekSeparatorState
          (units ++ left) right) =
      some
        (configAtLeftWord seekSeparatorState left
          (units.reverse ++ right)) := by
  induction units generalizing right with
  | nil =>
      rfl
  | cons head rest ih =>
      have headEq :
          head = unaryUnit :=
        allUnits head (List.Mem.head rest)
      subst head
      have restUnits :
          ∀ symbol, symbol ∈ rest → symbol = unaryUnit := by
        intro symbol member
        exact allUnits symbol (List.Mem.tail unaryUnit member)
      change
        (match
          workStep? machine
            (configAtLeftWord seekSeparatorState
              (unaryUnit :: (rest ++ left)) right)
        with
        | none => none
        | some next =>
            workRunExact? machine rest.length next) = _
      rw [seek_unit_step]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (unaryUnit :: right) restUnits

private theorem seek_units_exact
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? machine count
        (configAtLeftWord seekSeparatorState
          (List.replicate count unaryUnit ++ left) right) =
      some
        (configAtLeftWord seekSeparatorState left
          (List.replicate count unaryUnit ++ right)) := by
  simpa using
    seek_word_exact (List.replicate count unaryUnit)
      left right (by simp)

private theorem separator_step
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord seekSeparatorState
          (unarySeparator :: left) right) =
      some
        (configAtLeftWord writeSeparatorState left
          (unaryUnit :: right)) := by
  apply exactRun_one
  have notHalted :
      machine.isHalted
        (configAtLeftWord seekSeparatorState
          (unarySeparator :: left) right) = false := by
    rfl
  calc
    workStep? machine
        (configAtLeftWord seekSeparatorState
          (unarySeparator :: left) right) =
      some
        (applyWorkRule
          (literalRule seekSeparatorState unarySeparator
            writeSeparatorState unaryUnit .left)
          (configAtLeftWord seekSeparatorState
            (unarySeparator :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        find_seek_separator
    _ = some
        (configAtLeftWord writeSeparatorState left
          (unaryUnit :: right)) := by
      cases left <;> rfl

private theorem write_separator_step
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord writeSeparatorState
          (WorkSymbol.blank :: left) right) =
      some
        (configAtWord returnState
          (unarySeparator :: left) right) := by
  apply exactRun_one
  have notHalted :
      machine.isHalted
        (configAtLeftWord writeSeparatorState
          (WorkSymbol.blank :: left) right) = false := by
    rfl
  calc
    workStep? machine
        (configAtLeftWord writeSeparatorState
          (WorkSymbol.blank :: left) right) =
      some
        (applyWorkRule
          (literalRule writeSeparatorState WorkSymbol.blank
            returnState unarySeparator .right)
          (configAtLeftWord writeSeparatorState
            (WorkSymbol.blank :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted find_write_blank
    _ = some
        (configAtWord returnState
          (unarySeparator :: left) right) := by
      cases right <;> rfl

private theorem return_unit_step
    (leftSide rightTail : List WorkSymbol) :
    workStep? machine
        (configAtWord returnState leftSide
          (unaryUnit :: rightTail)) =
      some
        (configAtWord returnState
          (unaryUnit :: leftSide) rightTail) := by
  have notHalted :
      machine.isHalted
        (configAtWord returnState leftSide
          (unaryUnit :: rightTail)) =
        false := by
    rfl
  calc
    workStep? machine
        (configAtWord returnState leftSide
          (unaryUnit :: rightTail)) =
      some
        (applyWorkRule
          (literalRule returnState unaryUnit
            returnState unaryUnit .right)
          (configAtWord returnState leftSide
            (unaryUnit :: rightTail))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted find_return_unit
    _ = some
        (configAtWord returnState
          (unaryUnit :: leftSide) rightTail) := by
      cases rightTail <;> rfl

private theorem return_word_exact
    (units left right : List WorkSymbol)
    (allUnits :
      ∀ symbol, symbol ∈ units → symbol = unaryUnit) :
    workRunExact? machine units.length
        (configAtWord returnState left (units ++ right)) =
      some
        (configAtWord returnState
          (units.reverse ++ left) right) := by
  induction units generalizing left with
  | nil =>
      rfl
  | cons head rest ih =>
      have headEq :
          head = unaryUnit :=
        allUnits head (List.Mem.head rest)
      subst head
      have restUnits :
          ∀ symbol, symbol ∈ rest → symbol = unaryUnit := by
        intro symbol member
        exact allUnits symbol (List.Mem.tail unaryUnit member)
      change
        (match
          workStep? machine
            (configAtWord returnState left
              (unaryUnit :: (rest ++ right)))
        with
        | none => none
        | some next =>
            workRunExact? machine rest.length next) = _
      rw [return_unit_step]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (unaryUnit :: left) restUnits

private theorem return_units_exact
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? machine count
        (configAtWord returnState left
          (List.replicate count unaryUnit ++ right)) =
      some
        (configAtWord returnState
          (List.replicate count unaryUnit ++ left) right) := by
  simpa using
    return_word_exact (List.replicate count unaryUnit)
      left right (by simp)

private theorem return_boundary_step
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord returnState left
          (sourceLeftBoundary :: right)) =
      some
        (configAtWord acceptState
          (sourceLeftBoundary :: left) right) := by
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
            acceptState sourceLeftBoundary .right)
          (configAtWord returnState left
            (sourceLeftBoundary :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        find_return_boundary
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
      (List.replicate (count + 1) unaryUnit ++
        unarySeparator :: reserve ++ outsideLeft))
    (sourceHead :: sourceTail ++ targetAndRight)

def workSteps (count : Nat) : Nat :=
  2 * count + 6

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
    configAtLeftWord seekSeparatorState scratchTail
      (sourceLeftBoundary :: sourceWord)
  let atSeparator :=
    configAtLeftWord seekSeparatorState
      (unarySeparator :: WorkSymbol.blank :: reserve ++ outsideLeft)
      (List.replicate count unaryUnit ++
        sourceLeftBoundary :: sourceWord)
  let atBlank :=
    configAtLeftWord writeSeparatorState
      (WorkSymbol.blank :: reserve ++ outsideLeft)
      (unaryUnit :: List.replicate count unaryUnit ++
        sourceLeftBoundary :: sourceWord)
  let returning :=
    configAtWord returnState
      (unarySeparator :: reserve ++ outsideLeft)
      (List.replicate (count + 1) unaryUnit ++
        sourceLeftBoundary :: sourceWord)
  let atBoundary :=
    configAtWord returnState
      (List.replicate (count + 1) unaryUnit ++
        unarySeparator :: reserve ++ outsideLeft)
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
  have hSeek :=
    seek_units_exact count
      (unarySeparator :: WorkSymbol.blank :: reserve ++ outsideLeft)
      (sourceLeftBoundary :: sourceWord)
  have hSeekCanonical :
      workRunExact? machine count afterBoundary =
        some atSeparator := by
    simpa [afterBoundary, atSeparator, scratchTail,
      List.append_assoc] using hSeek
  have hSeparator :=
    separator_step
      (WorkSymbol.blank :: reserve ++ outsideLeft)
      (List.replicate count unaryUnit ++
        sourceLeftBoundary :: sourceWord)
  have hSeparatorCanonical :
      workRunExact? machine 1 atSeparator =
        some atBlank := by
    simpa [atSeparator, atBlank] using hSeparator
  have hWrite :=
    write_separator_step
      (reserve ++ outsideLeft)
      (unaryUnit :: List.replicate count unaryUnit ++
        sourceLeftBoundary :: sourceWord)
  have hWriteCanonical :
      workRunExact? machine 1 atBlank =
        some returning := by
    simpa [atBlank, returning, List.replicate_succ,
      List.append_assoc, Nat.add_comm] using hWrite
  have hReturn :=
    return_units_exact (count + 1)
      (unarySeparator :: reserve ++ outsideLeft)
      (sourceLeftBoundary :: sourceWord)
  have hReturnCanonical :
      workRunExact? machine (count + 1) returning =
        some atBoundary := by
    simpa [returning, atBoundary] using hReturn
  have hLast :=
    return_boundary_step
      (List.replicate (count + 1) unaryUnit ++
        unarySeparator :: reserve ++ outsideLeft)
      sourceWord
  have hLastCanonical :
      workRunExact? machine 1 atBoundary =
        some
          (finalConfiguration count sourceHead sourceTail
            targetAndRight reserve outsideLeft) := by
    simpa [atBoundary, finalConfiguration, sourceWord,
      List.append_assoc] using hLast
  have h01 := exactRun_add 1 1 _ _ _ hSourceCanonical hBoundaryCanonical
  have h02 := exactRun_add 2 count _ _ _ h01 hSeekCanonical
  have h03 := exactRun_add (2 + count) 1 _ _ _ h02 hSeparatorCanonical
  have h04 := exactRun_add (2 + count + 1) 1 _ _ _ h03 hWriteCanonical
  have h05 := exactRun_add (2 + count + 1 + 1) (count + 1)
    _ _ _ h04 hReturnCanonical
  have all := exactRun_add
    (2 + count + 1 + 1 + (count + 1)) 1
    _ _ _ h05 hLastCanonical
  have steps :
      2 + count + 1 + 1 + (count + 1) + 1 =
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
private theorem find_write_occupied
    (symbol : WorkSymbol) (occupied : symbol ≠ WorkSymbol.blank) :
    findWorkRule rules writeSeparatorState symbol =
      some
        (literalRule writeSeparatorState symbol
          deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · exact (occupied rfl).elim
  all_goals decide

/-- Scratch capacity is fail-closed: an occupied cell beyond the current
separator enters the ruleless dead state instead of overwriting a ledger. -/
theorem occupied_reserve_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (occupied : symbol ≠ WorkSymbol.blank) :
    workStep? machine
        (configAtLeftWord writeSeparatorState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  have notHalted :
      machine.isHalted
        (configAtLeftWord writeSeparatorState
          (symbol :: left) right) = false := by
    rfl
  calc
    workStep? machine
        (configAtLeftWord writeSeparatorState
          (symbol :: left) right) =
      some
        (applyWorkRule
          (literalRule writeSeparatorState symbol
            deadState symbol .stay)
          (configAtLeftWord writeSeparatorState
            (symbol :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_write_occupied symbol occupied)
    _ = some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
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

end PNP.Concrete.LockedNAND.TargetEmitterScratchIncrement

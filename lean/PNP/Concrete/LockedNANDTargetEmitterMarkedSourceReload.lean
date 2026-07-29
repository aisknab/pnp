/-
Copyright (c) 2026 PNP Labs.

Literal reload of one cursor-marked input or gate source.

The machine starts on the first retained source cell, seeks the unique
contextual cursor, validates the marked source backwards, and reconstructs
its unary natural in the nearest zero scratch record.  One source `01` cell
is marked only while a physical scratch increment is in progress.  The
cursor and every retained source, target, ledger, and outside cell are
preserved.
-/

import PNP.Concrete.LockedNANDTargetEmitterSourceCapture
import PNP.Concrete.TapeBlankEquivalence

namespace PNP.Concrete.LockedNAND.TargetEmitterMarkedSourceReload

open PNP.Concrete

abbrev NatKind := TargetEmitterSourceCapture.NatKind

def cell00 : WorkSymbol := TargetEmitterSourceCapture.cell00
def cell01 : WorkSymbol := TargetEmitterSourceCapture.cell01
def cell10 : WorkSymbol := TargetEmitterSourceCapture.cell10
def cell11 : WorkSymbol := TargetEmitterSourceCapture.cell11

def sourceLeftBoundary : WorkSymbol :=
  TargetEmitterSourceCapture.sourceLeftBoundary
def cursorMarker : WorkSymbol :=
  TargetEmitterSourceCapture.cursorMarker
def temporaryMark : WorkSymbol :=
  TargetEmitter.sourceTargetBoundary
def unaryUnit : WorkSymbol := TargetEmitter.unaryUnit
def unarySeparator : WorkSymbol := TargetEmitter.unarySeparator

def firstCell : NatKind → WorkSymbol
  | .input => cell00
  | .gate => cell01

def secondCell : NatKind → WorkSymbol
  | .input => cell11
  | .gate => cell10

def allWorkSymbols : List WorkSymbol :=
  TargetEmitter.allWorkSymbols

theorem temporaryMark_ne_cursor :
    temporaryMark ≠ cursorMarker := by
  decide

theorem temporaryMark_not_packed :
    ¬ TargetEmitter.PackedSymbol temporaryMark := by
  intro packed
  cases packed <;> contradiction

inductive PackedCell where
  | cell00
  | cell01
  | cell10
  | cell11
deriving BEq, DecidableEq, Repr

def PackedCell.symbol : PackedCell → WorkSymbol
  | .cell00 => WorkSymbol.zeroZero
  | .cell01 => WorkSymbol.zeroOne
  | .cell10 => WorkSymbol.oneZero
  | .cell11 => WorkSymbol.oneOne

def packedWord (cells : List PackedCell) : List WorkSymbol :=
  cells.map PackedCell.symbol

theorem packedWord_all_packed (cells : List PackedCell) :
    ∀ symbol, symbol ∈ packedWord cells →
      TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  rcases List.mem_map.mp member with
    ⟨cell, _cellMember, equality⟩
  rw [← equality]
  cases cell <;> constructor

def startState : Nat := 0
def terminalState : Nat := 1
def inspectState : Nat := 2
def pairFirstState : Nat := 3
def rewindBoundaryState : Nat := 4
def incrementSeekState : Nat := 5
def incrementWriteState : Nat := 6
def incrementReturnState : Nat := 7
def resumeSeekState : Nat := 8
def restorePairFirstState : Nat := 9
def inputTagFirstState : Nat := 10
def gateTagFirstState : Nat := 11
def rewindFinalState : Nat := 12
def acceptState : Nat := 13
def rejectState : Nat := 14
def deadState : Nat := 15

def tagFirstState : NatKind → Nat
  | .input => inputTagFirstState
  | .gate => gateTagFirstState

structure StateProgram where
  state : Nat
  action : WorkSymbol → Nat × WorkSymbol × HeadMove

def deadAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  (deadState, symbol, .stay)

def seekAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell00 ∨ symbol = cell01 ∨
      symbol = cell10 ∨ symbol = cell11 then
    (startState, symbol, .right)
  else if symbol = cursorMarker then
    (terminalState, symbol, .left)
  else
    deadAction symbol

def terminalAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell00 then
    (inspectState, symbol, .left)
  else
    deadAction symbol

def inspectAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell01 then
    (pairFirstState, temporaryMark, .left)
  else if symbol = cell11 then
    (inputTagFirstState, symbol, .left)
  else if symbol = cell10 then
    (gateTagFirstState, symbol, .left)
  else
    deadAction symbol

def pairFirstAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell00 then
    (rewindBoundaryState, symbol, .left)
  else
    deadAction symbol

def rewindBoundaryAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell00 ∨ symbol = cell01 ∨
      symbol = cell10 ∨ symbol = cell11 then
    (rewindBoundaryState, symbol, .left)
  else if symbol = sourceLeftBoundary then
    (incrementSeekState, symbol, .left)
  else
    deadAction symbol

def incrementSeekAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (incrementSeekState, symbol, .left)
  else if symbol = unarySeparator then
    (incrementWriteState, unaryUnit, .left)
  else
    deadAction symbol

def incrementWriteAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.blank then
    (incrementReturnState, unarySeparator, .right)
  else
    deadAction symbol

def incrementReturnAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (incrementReturnState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (resumeSeekState, symbol, .right)
  else
    deadAction symbol

def resumeSeekAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell00 ∨ symbol = cell01 ∨
      symbol = cell10 ∨ symbol = cell11 then
    (resumeSeekState, symbol, .right)
  else if symbol = temporaryMark then
    (restorePairFirstState, cell01, .left)
  else
    deadAction symbol

def restorePairFirstAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell00 then
    (inspectState, symbol, .left)
  else
    deadAction symbol

def inputTagFirstAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell00 then
    (rewindFinalState, symbol, .left)
  else
    deadAction symbol

def gateTagFirstAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell01 then
    (rewindFinalState, symbol, .left)
  else
    deadAction symbol

def rewindFinalAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell00 ∨ symbol = cell01 ∨
      symbol = cell10 ∨ symbol = cell11 then
    (rewindFinalState, symbol, .left)
  else if symbol = sourceLeftBoundary then
    (acceptState, symbol, .right)
  else
    deadAction symbol

def statePrograms : List StateProgram :=
  [ { state := startState, action := seekAction }
  , { state := terminalState, action := terminalAction }
  , { state := inspectState, action := inspectAction }
  , { state := pairFirstState, action := pairFirstAction }
  , { state := rewindBoundaryState,
      action := rewindBoundaryAction }
  , { state := incrementSeekState,
      action := incrementSeekAction }
  , { state := incrementWriteState,
      action := incrementWriteAction }
  , { state := incrementReturnState,
      action := incrementReturnAction }
  , { state := resumeSeekState, action := resumeSeekAction }
  , { state := restorePairFirstState,
      action := restorePairFirstAction }
  , { state := inputTagFirstState,
      action := inputTagFirstAction }
  , { state := gateTagFirstState,
      action := gateTagFirstAction }
  , { state := rewindFinalState,
      action := rewindFinalAction } ]

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

/-- Specification-indexed aliases; both reduce to the same literal machine. -/
def rulesFor (_kind : NatKind) : List WorkRule := rules
def machineFor (_kind : NatKind) : WorkMachine := machine
def compiledMachineFor (_kind : NatKind) : Machine := compiledMachine

theorem rules_kind_independent :
    rulesFor .input = rulesFor .gate := by
  rfl

theorem machine_kind_independent :
    machineFor .input = machineFor .gate := by
  rfl

theorem compiledMachine_kind_independent :
    compiledMachineFor .input = compiledMachineFor .gate := by
  rfl

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem rulesAt_length (program : StateProgram) :
    (rulesAt program).length = 9 := by
  rfl

theorem statePrograms_length :
    statePrograms.length = 13 := by
  rfl

theorem rules_length :
    rules.length = 117 := by
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
      programs.Pairwise
        (fun left right => left.state ≠ right.state)) :
    (programs.flatMap rulesAt).Pairwise QueryDistinct := by
  induction programs with
  | nil =>
      simp
  | cons program rest inductionHypothesis =>
      rw [List.flatMap_cons, List.pairwise_append]
      refine
        ⟨rulesAt_pairwise program,
          inductionHypothesis
            (List.pairwise_cons.mp distinct).2,
          ?_⟩
      intro left leftMember right rightMember
      have leftSource := rulesAt_source leftMember
      rcases List.mem_flatMap.mp rightMember with
        ⟨rightProgram, rightProgramMember,
          rightRuleMember⟩
      have rightSource := rulesAt_source rightRuleMember
      have stateNe :
          program.state ≠ rightProgram.state :=
        (List.pairwise_cons.mp distinct).1
          rightProgram rightProgramMember
      intro queryEquality
      exact stateNe
        (leftSource.symm.trans
          ((congrArg Prod.fst queryEquality).trans
            rightSource))

theorem rules_pairwise :
    rules.Pairwise QueryDistinct :=
  materialized_pairwise statePrograms statePrograms_pairwise

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
theorem no_rule_at_accept
    (symbol : WorkSymbol) :
    findWorkRule rules acceptState symbol = none := by
  rcases symbol with ⟨left, right⟩
  cases left <;> cases right <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_reject
    (symbol : WorkSymbol) :
    findWorkRule rules rejectState symbol = none := by
  rcases symbol with ⟨left, right⟩
  cases left <;> cases right <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_dead
    (symbol : WorkSymbol) :
    findWorkRule rules deadState symbol = none := by
  rcases symbol with ⟨left, right⟩
  cases left <;> cases right <;> decide

def configAtWord (state : Nat)
    (left word : List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtWord state left word

def configAtLeftWord (state : Nat)
    (leftWord right : List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtLeftWord state leftWord right

def scratchWord (count blankCount : Nat)
    (reserve ledger outsideLeft : List WorkSymbol) :
    List WorkSymbol :=
  List.replicate count unaryUnit ++
    unarySeparator ::
      (List.replicate blankCount WorkSymbol.blank ++
        reserve ++ ledger ++ outsideLeft)

def unitPrefix (value : Nat) : List WorkSymbol :=
  TargetEmitterSourceCapture.unitPrefix value

def markedSourceCells
    (kind : NatKind) (value : Nat) : List WorkSymbol :=
  TargetEmitterSourceCapture.markedSourceCells
    kind.sourceKind value

theorem markedSourceCells_shape
    (kind : NatKind) (value : Nat) :
    markedSourceCells kind value =
      [firstCell kind, secondCell kind] ++
        unitPrefix value ++ [cell00, cursorMarker] := by
  cases kind <;>
    simp [markedSourceCells, firstCell, secondCell, unitPrefix,
      cell00, cell01, cell10, cell11, cursorMarker,
      TargetEmitterSourceCapture.NatKind.sourceKind,
      TargetEmitterSourceCapture.markedSourceCells]

def entryConfiguration (kind : NatKind)
    (value : Nat) (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) : WorkConfiguration :=
  configAtWord startState
    (sourceLeftBoundary ::
      scratchWord 0 (value + 1)
        reserve ledger outsideLeft)
    (packedWord before ++ markedSourceCells kind value ++
      afterSource ++ targetAndRight)

def finalConfiguration (kind : NatKind)
    (value : Nat) (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) : WorkConfiguration :=
  configAtWord acceptState
    (sourceLeftBoundary ::
      scratchWord value 1 reserve ledger outsideLeft)
    (packedWord before ++ markedSourceCells kind value ++
      afterSource ++ targetAndRight)

/-! ### Exact-run calculus -/

private theorem exactRun_add (kind : NatKind)
    (first second : Nat)
    (initial middle final : WorkConfiguration)
    (firstRun :
      workRunExact? (machineFor kind) first initial = some middle)
    (secondRun :
      workRunExact? (machineFor kind) second middle = some final) :
    workRunExact? (machineFor kind) (first + second) initial =
      some final :=
  PipelineMachineSimulation.workRunExact?_compose
    (machineFor kind) first second initial middle final
    firstRun secondRun

private theorem exactRun_one (kind : NatKind)
    (initial final : WorkConfiguration)
    (step :
      workStep? (machineFor kind) initial = some final) :
    workRunExact? (machineFor kind) 1 initial = some final := by
  change
    (match workStep? (machineFor kind) initial with
     | none => none
     | some next => workRunExact? (machineFor kind) 0 next) =
      some final
  rw [step]
  rfl

private theorem scanLeftExact (kind : NatKind) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (step : ∀ head leftTail rightSide,
      Allowed head →
      workStep? (machineFor kind)
          (configAtLeftWord state
            (head :: leftTail) rightSide) =
        some (configAtLeftWord state
          leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? (machineFor kind) word.length
        (configAtLeftWord state
          (word ++ leftSuffix) rightSide) =
      some (configAtLeftWord state leftSuffix
        (word.reverse ++ rightSide)) := by
  induction word generalizing rightSide with
  | nil =>
      rfl
  | cons head rest inductionHypothesis =>
      have headAllowed :
          Allowed head :=
        allowed head (List.Mem.head rest)
      have restAllowed :
          ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol member
        exact allowed symbol (List.Mem.tail head member)
      change
        (match workStep? (machineFor kind)
            (configAtLeftWord state
              (head :: (rest ++ leftSuffix)) rightSide) with
         | none => none
         | some next =>
             workRunExact? (machineFor kind) rest.length next) = _
      rw [step head (rest ++ leftSuffix) rightSide headAllowed]
      simpa [List.reverse_cons, List.append_assoc] using
        inductionHypothesis (head :: rightSide) restAllowed

private theorem scanRightExact (kind : NatKind) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (step : ∀ leftSide head suffix,
      Allowed head →
      workStep? (machineFor kind)
          (configAtWord state leftSide (head :: suffix)) =
        some (configAtWord state
          (head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? (machineFor kind) word.length
        (configAtWord state leftSide (word ++ suffix)) =
      some (configAtWord state
        (word.reverse ++ leftSide) suffix) := by
  induction word generalizing leftSide with
  | nil =>
      rfl
  | cons head rest inductionHypothesis =>
      have headAllowed :
          Allowed head :=
        allowed head (List.Mem.head rest)
      have restAllowed :
          ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol member
        exact allowed symbol (List.Mem.tail head member)
      change
        (match workStep? (machineFor kind)
            (configAtWord state leftSide
              (head :: (rest ++ suffix))) with
         | none => none
         | some next =>
             workRunExact? (machineFor kind) rest.length next) = _
      rw [step leftSide head (rest ++ suffix) headAllowed]
      simpa [List.reverse_cons, List.append_assoc] using
        inductionHypothesis (head :: leftSide) restAllowed

private def literalRule (source : Nat)
    (read : WorkSymbol) (target : Nat)
    (write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

private theorem moveLeftFromWord_of_find (kind : NatKind)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      (machineFor kind).isHalted
        (configAtWord state left (symbol :: right)) = false)
    (found :
      findWorkRule (rulesFor kind) state symbol =
        some (literalRule state symbol target write .left)) :
    workStep? (machineFor kind)
        (configAtWord state left (symbol :: right)) =
      some (configAtLeftWord target left (write :: right)) := by
  calc
    workStep? (machineFor kind)
        (configAtWord state left (symbol :: right)) =
      some (applyWorkRule
        (literalRule state symbol target write .left)
        (configAtWord state left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (configAtLeftWord target left
        (write :: right)) := by
      cases left <;> rfl

private theorem moveLeftFromLeftWord_of_find
    (kind : NatKind)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      (machineFor kind).isHalted
        (configAtLeftWord state (symbol :: left) right) = false)
    (found :
      findWorkRule (rulesFor kind) state symbol =
        some (literalRule state symbol target write .left)) :
    workStep? (machineFor kind)
        (configAtLeftWord state (symbol :: left) right) =
      some (configAtLeftWord target left (write :: right)) := by
  calc
    workStep? (machineFor kind)
        (configAtLeftWord state (symbol :: left) right) =
      some (applyWorkRule
        (literalRule state symbol target write .left)
        (configAtLeftWord state (symbol :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (configAtLeftWord target left
        (write :: right)) := by
      cases left <;> rfl

private theorem moveRightFromWord_of_find (kind : NatKind)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      (machineFor kind).isHalted
        (configAtWord state left (symbol :: right)) = false)
    (found :
      findWorkRule (rulesFor kind) state symbol =
        some (literalRule state symbol target write .right)) :
    workStep? (machineFor kind)
        (configAtWord state left (symbol :: right)) =
      some (configAtWord target (write :: left) right) := by
  calc
    workStep? (machineFor kind)
        (configAtWord state left (symbol :: right)) =
      some (applyWorkRule
        (literalRule state symbol target write .right)
        (configAtWord state left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (configAtWord target
        (write :: left) right) := by
      cases right <;> rfl

private theorem moveRightFromLeftWord_of_find
    (kind : NatKind)
    (state target : Nat) (symbol write : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      (machineFor kind).isHalted
        (configAtLeftWord state (symbol :: left) right) = false)
    (found :
      findWorkRule (rulesFor kind) state symbol =
        some (literalRule state symbol target write .right)) :
    workStep? (machineFor kind)
        (configAtLeftWord state (symbol :: left) right) =
      some (configAtWord target (write :: left) right) := by
  calc
    workStep? (machineFor kind)
        (configAtLeftWord state (symbol :: left) right) =
      some (applyWorkRule
        (literalRule state symbol target write .right)
        (configAtLeftWord state (symbol :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some (configAtWord target
        (write :: left) right) := by
      cases right <;> rfl

set_option maxRecDepth 100000 in
private theorem find_seek_packed (kind : NatKind)
    (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol) :
    findWorkRule (rulesFor kind) startState symbol =
      some (literalRule startState symbol
        startState symbol .right) := by
  cases kind <;> cases packed <;> decide

set_option maxRecDepth 100000 in
private theorem find_seek_cursor (kind : NatKind) :
    findWorkRule (rulesFor kind) startState cursorMarker =
      some (literalRule startState cursorMarker
        terminalState cursorMarker .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_terminal (kind : NatKind) :
    findWorkRule (rulesFor kind) terminalState cell00 =
      some (literalRule terminalState cell00
        inspectState cell00 .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_inspect_unit (kind : NatKind) :
    findWorkRule (rulesFor kind) inspectState cell01 =
      some (literalRule inspectState cell01
        pairFirstState temporaryMark .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_inspect_tag (kind : NatKind) :
    findWorkRule (rulesFor kind) inspectState (secondCell kind) =
      some (literalRule inspectState (secondCell kind)
        (tagFirstState kind) (secondCell kind) .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_pair_first (kind : NatKind) :
    findWorkRule (rulesFor kind) pairFirstState cell00 =
      some (literalRule pairFirstState cell00
        rewindBoundaryState cell00 .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_rewind_packed (kind : NatKind)
    (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol) :
    findWorkRule (rulesFor kind) rewindBoundaryState symbol =
      some (literalRule rewindBoundaryState symbol
        rewindBoundaryState symbol .left) := by
  cases kind <;> cases packed <;> decide

set_option maxRecDepth 100000 in
private theorem find_rewind_boundary (kind : NatKind) :
    findWorkRule (rulesFor kind) rewindBoundaryState
        sourceLeftBoundary =
      some (literalRule rewindBoundaryState
        sourceLeftBoundary incrementSeekState
        sourceLeftBoundary .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_increment_unit (kind : NatKind) :
    findWorkRule (rulesFor kind) incrementSeekState unaryUnit =
      some (literalRule incrementSeekState unaryUnit
        incrementSeekState unaryUnit .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_increment_separator (kind : NatKind) :
    findWorkRule (rulesFor kind) incrementSeekState unarySeparator =
      some (literalRule incrementSeekState unarySeparator
        incrementWriteState unaryUnit .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_increment_blank (kind : NatKind) :
    findWorkRule (rulesFor kind) incrementWriteState WorkSymbol.blank =
      some (literalRule incrementWriteState WorkSymbol.blank
        incrementReturnState unarySeparator .right) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_return_unit (kind : NatKind) :
    findWorkRule (rulesFor kind) incrementReturnState unaryUnit =
      some (literalRule incrementReturnState unaryUnit
        incrementReturnState unaryUnit .right) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_return_boundary (kind : NatKind) :
    findWorkRule (rulesFor kind) incrementReturnState
        sourceLeftBoundary =
      some (literalRule incrementReturnState
        sourceLeftBoundary resumeSeekState
        sourceLeftBoundary .right) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_resume_packed (kind : NatKind)
    (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol) :
    findWorkRule (rulesFor kind) resumeSeekState symbol =
      some (literalRule resumeSeekState symbol
        resumeSeekState symbol .right) := by
  cases kind <;> cases packed <;> decide

set_option maxRecDepth 100000 in
private theorem find_resume_mark (kind : NatKind) :
    findWorkRule (rulesFor kind) resumeSeekState temporaryMark =
      some (literalRule resumeSeekState temporaryMark
        restorePairFirstState cell01 .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_restore_pair_first (kind : NatKind) :
    findWorkRule (rulesFor kind) restorePairFirstState cell00 =
      some (literalRule restorePairFirstState cell00
        inspectState cell00 .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_tag_first (kind : NatKind) :
    findWorkRule (rulesFor kind) (tagFirstState kind)
        (firstCell kind) =
      some (literalRule (tagFirstState kind) (firstCell kind)
        rewindFinalState (firstCell kind) .left) := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_final_packed (kind : NatKind)
    (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol) :
    findWorkRule (rulesFor kind) rewindFinalState symbol =
      some (literalRule rewindFinalState symbol
        rewindFinalState symbol .left) := by
  cases kind <;> cases packed <;> decide

set_option maxRecDepth 100000 in
private theorem find_final_boundary (kind : NatKind) :
    findWorkRule (rulesFor kind) rewindFinalState
        sourceLeftBoundary =
      some (literalRule rewindFinalState
        sourceLeftBoundary acceptState
        sourceLeftBoundary .right) := by
  cases kind <;> decide

private theorem seek_packed_step (kind : NatKind)
    (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtWord startState left (symbol :: right)) =
      some (configAtWord startState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find kind
  · cases kind <;> rfl
  · exact find_seek_packed kind symbol packed

private theorem seek_cursor_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtWord startState left
          (cursorMarker :: right)) =
      some (configAtLeftWord terminalState left
        (cursorMarker :: right)) := by
  apply moveLeftFromWord_of_find kind
  · cases kind <;> rfl
  · exact find_seek_cursor kind

private theorem terminal_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord terminalState
          (cell00 :: left) right) =
      some (configAtLeftWord inspectState left
        (cell00 :: right)) := by
  apply moveLeftFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_terminal kind

private theorem inspect_unit_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord inspectState
          (cell01 :: left) right) =
      some (configAtLeftWord pairFirstState left
        (temporaryMark :: right)) := by
  apply moveLeftFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_inspect_unit kind

private theorem inspect_tag_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord inspectState
          (secondCell kind :: left) right) =
      some (configAtLeftWord (tagFirstState kind) left
        (secondCell kind :: right)) := by
  apply moveLeftFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_inspect_tag kind

private theorem pair_first_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord pairFirstState
          (cell00 :: left) right) =
      some (configAtLeftWord rewindBoundaryState left
        (cell00 :: right)) := by
  apply moveLeftFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_pair_first kind

private theorem rewind_packed_step (kind : NatKind)
    (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord rewindBoundaryState
          (symbol :: left) right) =
      some (configAtLeftWord rewindBoundaryState left
        (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_rewind_packed kind symbol packed

private theorem rewind_boundary_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord rewindBoundaryState
          (sourceLeftBoundary :: left) right) =
      some (configAtLeftWord incrementSeekState left
        (sourceLeftBoundary :: right)) := by
  apply moveLeftFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_rewind_boundary kind

private theorem increment_unit_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord incrementSeekState
          (unaryUnit :: left) right) =
      some (configAtLeftWord incrementSeekState left
        (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_increment_unit kind

private theorem increment_separator_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord incrementSeekState
          (unarySeparator :: left) right) =
      some (configAtLeftWord incrementWriteState left
        (unaryUnit :: right)) := by
  apply moveLeftFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_increment_separator kind

private theorem increment_blank_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord incrementWriteState
          (WorkSymbol.blank :: left) right) =
      some (configAtWord incrementReturnState
        (unarySeparator :: left) right) := by
  apply moveRightFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_increment_blank kind

private theorem return_unit_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtWord incrementReturnState left
          (unaryUnit :: right)) =
      some (configAtWord incrementReturnState
        (unaryUnit :: left) right) := by
  apply moveRightFromWord_of_find kind
  · cases kind <;> rfl
  · exact find_return_unit kind

private theorem return_boundary_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtWord incrementReturnState left
          (sourceLeftBoundary :: right)) =
      some (configAtWord resumeSeekState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromWord_of_find kind
  · cases kind <;> rfl
  · exact find_return_boundary kind

private theorem resume_packed_step (kind : NatKind)
    (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtWord resumeSeekState left
          (symbol :: right)) =
      some (configAtWord resumeSeekState
        (symbol :: left) right) := by
  apply moveRightFromWord_of_find kind
  · cases kind <;> rfl
  · exact find_resume_packed kind symbol packed

private theorem resume_mark_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtWord resumeSeekState left
          (temporaryMark :: right)) =
      some (configAtLeftWord restorePairFirstState left
        (cell01 :: right)) := by
  apply moveLeftFromWord_of_find kind
  · cases kind <;> rfl
  · exact find_resume_mark kind

private theorem restore_pair_first_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord restorePairFirstState
          (cell00 :: left) right) =
      some (configAtLeftWord inspectState left
        (cell00 :: right)) := by
  apply moveLeftFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_restore_pair_first kind

private theorem tag_first_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord (tagFirstState kind)
          (firstCell kind :: left) right) =
      some (configAtLeftWord rewindFinalState left
        (firstCell kind :: right)) := by
  apply moveLeftFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_tag_first kind

private theorem final_packed_step (kind : NatKind)
    (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord rewindFinalState
          (symbol :: left) right) =
      some (configAtLeftWord rewindFinalState left
        (symbol :: right)) := by
  apply moveLeftFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_final_packed kind symbol packed

private theorem final_boundary_step (kind : NatKind)
    (left right : List WorkSymbol) :
    workStep? (machineFor kind)
        (configAtLeftWord rewindFinalState
          (sourceLeftBoundary :: left) right) =
      some (configAtWord acceptState
        (sourceLeftBoundary :: left) right) := by
  apply moveRightFromLeftWord_of_find kind
  · cases kind <;> rfl
  · exact find_final_boundary kind

private theorem seek_word_exact (kind : NatKind)
    (word suffix left : List WorkSymbol)
    (packed :
      ∀ symbol, symbol ∈ word →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machineFor kind) word.length
        (configAtWord startState left (word ++ suffix)) =
      some (configAtWord startState
        (word.reverse ++ left) suffix) := by
  exact scanRightExact kind startState
    TargetEmitter.PackedSymbol
    (fun leftSide head rightSide allowed =>
      seek_packed_step kind head allowed leftSide rightSide)
    word suffix left packed

private theorem rewind_word_exact (kind : NatKind)
    (word left right : List WorkSymbol)
    (packed :
      ∀ symbol, symbol ∈ word →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machineFor kind) word.length
        (configAtLeftWord rewindBoundaryState
          (word ++ left) right) =
      some (configAtLeftWord rewindBoundaryState left
        (word.reverse ++ right)) := by
  exact scanLeftExact kind rewindBoundaryState
    TargetEmitter.PackedSymbol
    (fun head leftSide rightSide allowed =>
      rewind_packed_step kind head allowed leftSide rightSide)
    word left right packed

private theorem increment_units_exact (kind : NatKind)
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor kind) count
        (configAtLeftWord incrementSeekState
          (List.replicate count unaryUnit ++ left) right) =
      some (configAtLeftWord incrementSeekState left
        (List.replicate count unaryUnit ++ right)) := by
  have scanned := scanLeftExact kind incrementSeekState
    (fun symbol => symbol = unaryUnit)
    (fun head leftSide rightSide equality => by
      subst head
      exact increment_unit_step kind leftSide rightSide)
    (List.replicate count unaryUnit) left right (by simp)
  simpa using scanned

private theorem return_units_exact (kind : NatKind)
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? (machineFor kind) count
        (configAtWord incrementReturnState left
          (List.replicate count unaryUnit ++ right)) =
      some (configAtWord incrementReturnState
        (List.replicate count unaryUnit ++ left) right) := by
  have scanned := scanRightExact kind incrementReturnState
    (fun symbol => symbol = unaryUnit)
    (fun leftSide head rightSide equality => by
      subst head
      exact return_unit_step kind leftSide rightSide)
    (List.replicate count unaryUnit) right left (by simp)
  simpa using scanned

private theorem resume_word_exact (kind : NatKind)
    (word suffix left : List WorkSymbol)
    (packed :
      ∀ symbol, symbol ∈ word →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machineFor kind) word.length
        (configAtWord resumeSeekState left (word ++ suffix)) =
      some (configAtWord resumeSeekState
        (word.reverse ++ left) suffix) := by
  exact scanRightExact kind resumeSeekState
    TargetEmitter.PackedSymbol
    (fun leftSide head rightSide allowed =>
      resume_packed_step kind head allowed leftSide rightSide)
    word suffix left packed

private theorem final_rewind_exact (kind : NatKind)
    (word left right : List WorkSymbol)
    (packed :
      ∀ symbol, symbol ∈ word →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machineFor kind) word.length
        (configAtLeftWord rewindFinalState
          (word ++ left) right) =
      some (configAtLeftWord rewindFinalState left
        (word.reverse ++ right)) := by
  exact scanLeftExact kind rewindFinalState
    TargetEmitter.PackedSymbol
    (fun head leftSide rightSide allowed =>
      final_packed_step kind head allowed leftSide rightSide)
    word left right packed

theorem unitPrefix_length (value : Nat) :
    (unitPrefix value).length = 2 * value := by
  exact TargetEmitterSourceCapture.unitPrefix_length value

private theorem unitPrefix_append_succ (value : Nat) :
    unitPrefix (value + 1) =
      unitPrefix value ++ [cell00, cell01] := by
  induction value with
  | zero =>
      rfl
  | succ value inductionHypothesis =>
      change
        cell00 :: cell01 :: unitPrefix (value + 1) =
          (cell00 :: cell01 :: unitPrefix value) ++
            [cell00, cell01]
      rw [inductionHypothesis]
      rfl

theorem unitPrefix_all_packed (value : Nat) :
    ∀ symbol, symbol ∈ unitPrefix value →
      TargetEmitter.PackedSymbol symbol := by
  induction value with
  | zero =>
      simp [unitPrefix, TargetEmitterSourceCapture.unitPrefix]
  | succ value inductionHypothesis =>
      intro symbol member
      change
        symbol ∈ cell00 :: cell01 :: unitPrefix value at member
      simp only [List.mem_cons] at member
      rcases member with rfl | rfl | tailMember
      · constructor
      · constructor
      · exact inductionHypothesis symbol tailMember

def basePrefix (kind : NatKind)
    (before : List PackedCell) : List WorkSymbol :=
  packedWord before ++ [firstCell kind, secondCell kind]

theorem basePrefix_length (kind : NatKind)
    (before : List PackedCell) :
    (basePrefix kind before).length = before.length + 2 := by
  simp [basePrefix, packedWord]

theorem basePrefix_all_packed (kind : NatKind)
    (before : List PackedCell) :
    ∀ symbol, symbol ∈ basePrefix kind before →
      TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  rw [basePrefix, List.mem_append] at member
  rcases member with beforeMember | tagMember
  · exact packedWord_all_packed before symbol beforeMember
  · cases kind <;>
      simp [firstCell, secondCell, cell00, cell01,
        cell10, cell11] at tagMember
    all_goals
      rcases tagMember with rfl | rfl <;> constructor

def unitReloadSteps (prefixLength count : Nat) : Nat :=
  2 * prefixLength + 2 * count + 10

private theorem unit_reload_exact
    (kind : NatKind) (sourcePrefix : List WorkSymbol)
    (count : Nat)
    (suffix reserve ledger outsideLeft : List WorkSymbol)
    (prefixPacked :
      ∀ symbol, symbol ∈ sourcePrefix →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machineFor kind)
        (unitReloadSteps sourcePrefix.length count)
        (configAtLeftWord inspectState
          (cell01 :: cell00 :: sourcePrefix.reverse ++
            sourceLeftBoundary ::
              scratchWord count 2
                reserve ledger outsideLeft)
          suffix) =
      some
        (configAtLeftWord inspectState
          (sourcePrefix.reverse ++
            sourceLeftBoundary ::
              scratchWord (count + 1) 1
                reserve ledger outsideLeft)
          (cell00 :: cell01 :: suffix)) := by
  let scratchTail :=
    List.replicate count unaryUnit ++
      unarySeparator :: WorkSymbol.blank ::
        WorkSymbol.blank :: reserve ++ ledger ++ outsideLeft
  let markedRight := cell00 :: temporaryMark :: suffix
  have hInspect :=
    exactRun_one kind _ _
      (inspect_unit_step kind
        (cell00 :: sourcePrefix.reverse ++
          sourceLeftBoundary :: scratchTail)
        suffix)
  have hPair :=
    exactRun_one kind _ _
      (pair_first_step kind
        (sourcePrefix.reverse ++
          sourceLeftBoundary :: scratchTail)
        (temporaryMark :: suffix))
  have reversePacked :
      ∀ symbol, symbol ∈ sourcePrefix.reverse →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    exact prefixPacked symbol (List.mem_reverse.mp member)
  have hRewind :
      workRunExact? (machineFor kind) sourcePrefix.length
          (configAtLeftWord rewindBoundaryState
            (sourcePrefix.reverse ++
              sourceLeftBoundary :: scratchTail)
            markedRight) =
        some
          (configAtLeftWord rewindBoundaryState
            (sourceLeftBoundary :: scratchTail)
            (sourcePrefix ++ markedRight)) := by
    have scanned := rewind_word_exact kind sourcePrefix.reverse
      (sourceLeftBoundary :: scratchTail) markedRight reversePacked
    simpa using scanned
  have hBoundary :=
    exactRun_one kind _ _
      (rewind_boundary_step kind scratchTail
        (sourcePrefix ++ markedRight))
  have hSeek := increment_units_exact kind count
    (unarySeparator :: WorkSymbol.blank ::
      WorkSymbol.blank :: reserve ++ ledger ++ outsideLeft)
    (sourceLeftBoundary :: sourcePrefix ++ markedRight)
  have hSeparator :=
    exactRun_one kind _ _
      (increment_separator_step kind
        (WorkSymbol.blank :: WorkSymbol.blank ::
          reserve ++ ledger ++ outsideLeft)
        (List.replicate count unaryUnit ++
          sourceLeftBoundary :: sourcePrefix ++ markedRight))
  have hWrite :=
    exactRun_one kind _ _
      (increment_blank_step kind
        (WorkSymbol.blank :: reserve ++ ledger ++ outsideLeft)
        (unaryUnit :: List.replicate count unaryUnit ++
          sourceLeftBoundary :: sourcePrefix ++ markedRight))
  have hReturn := return_units_exact kind (count + 1)
    (unarySeparator :: WorkSymbol.blank ::
      reserve ++ ledger ++ outsideLeft)
    (sourceLeftBoundary :: sourcePrefix ++ markedRight)
  have hReturnBoundary :=
    exactRun_one kind _ _
      (return_boundary_step kind
        (List.replicate (count + 1) unaryUnit ++
          unarySeparator :: WorkSymbol.blank ::
            reserve ++ ledger ++ outsideLeft)
        (sourcePrefix ++ markedRight))
  have resumePrefixPacked :
      ∀ symbol, symbol ∈ sourcePrefix ++ [cell00] →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    rcases List.mem_append.mp member with fromPrefix | fromTerminal
    · exact prefixPacked symbol fromPrefix
    · simp only [List.mem_singleton] at fromTerminal
      subst symbol
      constructor
  have hResume := resume_word_exact kind
    (sourcePrefix ++ [cell00])
    (temporaryMark :: suffix)
    (sourceLeftBoundary ::
      List.replicate (count + 1) unaryUnit ++
        unarySeparator :: WorkSymbol.blank ::
          reserve ++ ledger ++ outsideLeft)
    resumePrefixPacked
  have hMark :=
    exactRun_one kind _ _
      (resume_mark_step kind
        ((sourcePrefix ++ [cell00]).reverse ++
          sourceLeftBoundary ::
            List.replicate (count + 1) unaryUnit ++
              unarySeparator :: WorkSymbol.blank ::
                reserve ++ ledger ++ outsideLeft)
        suffix)
  have hRestore :=
    exactRun_one kind _ _
      (restore_pair_first_step kind
        (sourcePrefix.reverse ++
          sourceLeftBoundary ::
            List.replicate (count + 1) unaryUnit ++
              unarySeparator :: WorkSymbol.blank ::
                reserve ++ ledger ++ outsideLeft)
        (cell01 :: suffix))
  have hSeekCanonical :
      workRunExact? (machineFor kind) count
          (configAtLeftWord incrementSeekState scratchTail
            (sourceLeftBoundary :: sourcePrefix ++ markedRight)) =
        some
          (configAtLeftWord incrementSeekState
            (unarySeparator :: WorkSymbol.blank ::
              WorkSymbol.blank :: reserve ++ ledger ++ outsideLeft)
            (List.replicate count unaryUnit ++
              sourceLeftBoundary :: sourcePrefix ++ markedRight)) := by
    simpa [scratchTail, List.append_assoc] using hSeek
  have hReturnCanonical :
      workRunExact? (machineFor kind) (count + 1)
          (configAtWord incrementReturnState
            (unarySeparator :: WorkSymbol.blank ::
              reserve ++ ledger ++ outsideLeft)
            (List.replicate (count + 1) unaryUnit ++
              sourceLeftBoundary :: sourcePrefix ++ markedRight)) =
        some
          (configAtWord incrementReturnState
            (List.replicate (count + 1) unaryUnit ++
              unarySeparator :: WorkSymbol.blank ::
                reserve ++ ledger ++ outsideLeft)
            (sourceLeftBoundary :: sourcePrefix ++ markedRight)) := by
    simpa [List.append_assoc] using hReturn
  have hResumeCanonical :
      workRunExact? (machineFor kind) (sourcePrefix.length + 1)
          (configAtWord resumeSeekState
            (sourceLeftBoundary ::
              List.replicate (count + 1) unaryUnit ++
                unarySeparator :: WorkSymbol.blank ::
                  reserve ++ ledger ++ outsideLeft)
            (sourcePrefix ++ markedRight)) =
        some
          (configAtWord resumeSeekState
            ((sourcePrefix ++ [cell00]).reverse ++
              sourceLeftBoundary ::
                List.replicate (count + 1) unaryUnit ++
                  unarySeparator :: WorkSymbol.blank ::
                    reserve ++ ledger ++ outsideLeft)
            (temporaryMark :: suffix)) := by
    simpa [markedRight, List.append_assoc] using hResume
  have hRestoreCanonical :
      workRunExact? (machineFor kind) 1
          (configAtLeftWord restorePairFirstState
            ((sourcePrefix ++ [cell00]).reverse ++
              sourceLeftBoundary ::
                List.replicate (count + 1) unaryUnit ++
                  unarySeparator :: WorkSymbol.blank ::
                    reserve ++ ledger ++ outsideLeft)
            (cell01 :: suffix)) =
        some
          (configAtLeftWord inspectState
            (sourcePrefix.reverse ++
              sourceLeftBoundary ::
                List.replicate (count + 1) unaryUnit ++
                  unarySeparator :: WorkSymbol.blank ::
                    reserve ++ ledger ++ outsideLeft)
            (cell00 :: cell01 :: suffix)) := by
    simpa [List.reverse_append] using hRestore
  have h01 := exactRun_add kind 1 1 _ _ _ hInspect hPair
  have h02 := exactRun_add kind 2 sourcePrefix.length
    _ _ _ h01 hRewind
  have h03 := exactRun_add kind (2 + sourcePrefix.length) 1
    _ _ _ h02 hBoundary
  have h04 := exactRun_add kind
    (2 + sourcePrefix.length + 1) count
    _ _ _ h03 hSeekCanonical
  have h05 := exactRun_add kind
    (2 + sourcePrefix.length + 1 + count) 1
    _ _ _ h04 hSeparator
  have h06 := exactRun_add kind
    (2 + sourcePrefix.length + 1 + count + 1) 1
    _ _ _ h05 hWrite
  have h07 := exactRun_add kind
    (2 + sourcePrefix.length + 1 + count + 1 + 1)
    (count + 1) _ _ _ h06 hReturnCanonical
  have h08 := exactRun_add kind
    (2 + sourcePrefix.length + 1 + count + 1 + 1 +
      (count + 1)) 1 _ _ _ h07 hReturnBoundary
  have h09 := exactRun_add kind
    (2 + sourcePrefix.length + 1 + count + 1 + 1 +
      (count + 1) + 1) (sourcePrefix.length + 1)
    _ _ _ h08 hResumeCanonical
  have h10 := exactRun_add kind
    (2 + sourcePrefix.length + 1 + count + 1 + 1 +
      (count + 1) + 1 + (sourcePrefix.length + 1)) 1
    _ _ _ h09 hMark
  have all := exactRun_add kind
    (2 + sourcePrefix.length + 1 + count + 1 + 1 +
      (count + 1) + 1 + (sourcePrefix.length + 1) + 1) 1
    _ _ _ h10 hRestoreCanonical
  have steps :
      2 + sourcePrefix.length + 1 + count + 1 + 1 +
          (count + 1) + 1 + (sourcePrefix.length + 1) + 1 + 1 =
        unitReloadSteps sourcePrefix.length count := by
    unfold unitReloadSteps
    omega
  rw [steps] at all
  simpa [scratchWord, scratchTail, markedRight,
    List.replicate_succ, List.append_assoc] using all

def reloadFinishSteps (beforeLength : Nat) : Nat :=
  beforeLength + 3

private theorem reload_finish_exact
    (kind : NatKind) (before : List PackedCell)
    (count : Nat)
    (suffix reserve ledger outsideLeft : List WorkSymbol) :
    workRunExact? (machineFor kind)
        (reloadFinishSteps before.length)
        (configAtLeftWord inspectState
          ((basePrefix kind before).reverse ++
            sourceLeftBoundary ::
              scratchWord count 1
                reserve ledger outsideLeft)
          (unitPrefix count ++
            [cell00, cursorMarker] ++ suffix)) =
      some
        (configAtWord acceptState
          (sourceLeftBoundary ::
            scratchWord count 1
              reserve ledger outsideLeft)
          (basePrefix kind before ++ unitPrefix count ++
            [cell00, cursorMarker] ++ suffix)) := by
  let scratch :=
    scratchWord count 1 reserve ledger outsideLeft
  let processed :=
    unitPrefix count ++ [cell00, cursorMarker] ++ suffix
  have hInspect :=
    exactRun_one kind _ _
      (inspect_tag_step kind
        (firstCell kind :: (packedWord before).reverse ++
          sourceLeftBoundary :: scratch)
        processed)
  have hTag :=
    exactRun_one kind _ _
      (tag_first_step kind
        ((packedWord before).reverse ++
          sourceLeftBoundary :: scratch)
        (secondCell kind :: processed))
  have reversePacked :
      ∀ symbol, symbol ∈ (packedWord before).reverse →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    exact packedWord_all_packed before symbol
      (List.mem_reverse.mp member)
  have hRewind :
      workRunExact? (machineFor kind) before.length
          (configAtLeftWord rewindFinalState
            ((packedWord before).reverse ++
              sourceLeftBoundary :: scratch)
            (firstCell kind :: secondCell kind :: processed)) =
        some
          (configAtLeftWord rewindFinalState
            (sourceLeftBoundary :: scratch)
            (packedWord before ++
              firstCell kind :: secondCell kind :: processed)) := by
    have scanned := final_rewind_exact kind
      (packedWord before).reverse
      (sourceLeftBoundary :: scratch)
      (firstCell kind :: secondCell kind :: processed)
      reversePacked
    simpa [packedWord] using scanned
  have hBoundary :=
    exactRun_one kind _ _
      (final_boundary_step kind scratch
        (packedWord before ++
          firstCell kind :: secondCell kind :: processed))
  have h01 := exactRun_add kind 1 1 _ _ _ hInspect hTag
  have h02 := exactRun_add kind 2 before.length
    _ _ _ h01 hRewind
  have all := exactRun_add kind (2 + before.length) 1
    _ _ _ h02 hBoundary
  have steps :
      2 + before.length + 1 =
        reloadFinishSteps before.length := by
    unfold reloadFinishSteps
    omega
  rw [steps] at all
  simpa [basePrefix, scratch, processed,
    List.reverse_append, List.append_assoc] using all

def reloadLoopSteps : Nat → Nat → Nat → Nat
  | beforeLength, _, 0 =>
      reloadFinishSteps beforeLength
  | beforeLength, count, remaining + 1 =>
      unitReloadSteps (beforeLength + 2 + 2 * remaining) count +
        reloadLoopSteps beforeLength (count + 1) remaining

private theorem replicate_add
    (first second : Nat) (symbol : WorkSymbol) :
    List.replicate (first + second) symbol =
      List.replicate first symbol ++
        List.replicate second symbol := by
  induction first with
  | zero =>
      simp
  | succ first inductionHypothesis =>
      simp only [Nat.succ_add, List.replicate_succ,
        inductionHypothesis, List.cons_append]

private theorem reload_loop_exact
    (kind : NatKind) (before : List PackedCell)
    (count remaining : Nat)
    (suffix reserve ledger outsideLeft : List WorkSymbol) :
    workRunExact? (machineFor kind)
        (reloadLoopSteps before.length count remaining)
        (configAtLeftWord inspectState
          ((basePrefix kind before ++
              unitPrefix remaining).reverse ++
            sourceLeftBoundary ::
              scratchWord count (remaining + 1)
                reserve ledger outsideLeft)
          (unitPrefix count ++
            [cell00, cursorMarker] ++ suffix)) =
      some
        (configAtWord acceptState
          (sourceLeftBoundary ::
            scratchWord (count + remaining) 1
              reserve ledger outsideLeft)
          (basePrefix kind before ++
            unitPrefix (count + remaining) ++
              [cell00, cursorMarker] ++ suffix)) := by
  induction remaining generalizing count with
  | zero =>
      simpa [reloadLoopSteps, unitPrefix,
        TargetEmitterSourceCapture.unitPrefix] using
        reload_finish_exact kind before count suffix
          reserve ledger outsideLeft
  | succ remaining inductionHypothesis =>
      let sourcePrefix :=
        basePrefix kind before ++ unitPrefix remaining
      let processed :=
        unitPrefix count ++
          [cell00, cursorMarker] ++ suffix
      have sourcePrefixPacked :
          ∀ symbol, symbol ∈ sourcePrefix →
            TargetEmitter.PackedSymbol symbol := by
        intro symbol member
        rcases List.mem_append.mp member with
          fromBase | fromUnits
        · exact basePrefix_all_packed kind before symbol fromBase
        · exact unitPrefix_all_packed remaining symbol fromUnits
      have hIteration := unit_reload_exact kind sourcePrefix count
        processed
        (List.replicate remaining WorkSymbol.blank ++ reserve)
        ledger outsideLeft sourcePrefixPacked
      have hTail :=
        inductionHypothesis (count + 1)
      have sourceShape :
          (basePrefix kind before ++
              unitPrefix (remaining + 1)).reverse =
            cell01 :: cell00 :: sourcePrefix.reverse := by
        rw [unitPrefix_append_succ]
        simp [sourcePrefix, List.reverse_append]
      have scratchShape :
          scratchWord count (remaining + 1 + 1)
              reserve ledger outsideLeft =
            scratchWord count 2
              (List.replicate remaining WorkSymbol.blank ++
                reserve)
              ledger outsideLeft := by
        have blanks :
            List.replicate (remaining + 1 + 1)
                WorkSymbol.blank =
              List.replicate 2 WorkSymbol.blank ++
                List.replicate remaining WorkSymbol.blank := by
          rw [show remaining + 1 + 1 = 2 + remaining by omega]
          exact replicate_add 2 remaining WorkSymbol.blank
        simp only [scratchWord, blanks, List.append_assoc]
      have nextScratchShape :
          scratchWord (count + 1) 1
              (List.replicate remaining WorkSymbol.blank ++ reserve)
              ledger outsideLeft =
            scratchWord (count + 1) (remaining + 1)
              reserve ledger outsideLeft := by
        have blanks :
            List.replicate (remaining + 1)
                WorkSymbol.blank =
              List.replicate 1 WorkSymbol.blank ++
                List.replicate remaining WorkSymbol.blank := by
          rw [show remaining + 1 = 1 + remaining by omega]
          exact replicate_add 1 remaining WorkSymbol.blank
        simp only [scratchWord, blanks, List.append_assoc]
      have processedShape :
          cell00 :: cell01 :: processed =
            unitPrefix (count + 1) ++
              [cell00, cursorMarker] ++ suffix := by
        rfl
      have prefixLength :
          sourcePrefix.length =
            before.length + 2 + 2 * remaining := by
        simp [sourcePrefix, basePrefix_length, unitPrefix_length]
      have hIterationCanonical :
          workRunExact? (machineFor kind)
              (unitReloadSteps
                (before.length + 2 + 2 * remaining) count)
              (configAtLeftWord inspectState
                ((basePrefix kind before ++
                    unitPrefix (remaining + 1)).reverse ++
                  sourceLeftBoundary ::
                    scratchWord count (remaining + 1 + 1)
                      reserve ledger outsideLeft)
                (unitPrefix count ++
                  [cell00, cursorMarker] ++ suffix)) =
            some
              (configAtLeftWord inspectState
                ((basePrefix kind before ++
                    unitPrefix remaining).reverse ++
                  sourceLeftBoundary ::
                    scratchWord (count + 1) (remaining + 1)
                      reserve ledger outsideLeft)
                (unitPrefix (count + 1) ++
                  [cell00, cursorMarker] ++ suffix)) := by
        simpa only [sourcePrefix, processed, sourceShape,
          scratchShape, nextScratchShape, processedShape,
          prefixLength] using hIteration
      have hTailCanonical :
          workRunExact? (machineFor kind)
              (reloadLoopSteps before.length
                (count + 1) remaining)
              (configAtLeftWord inspectState
                ((basePrefix kind before ++
                    unitPrefix remaining).reverse ++
                  sourceLeftBoundary ::
                    scratchWord (count + 1) (remaining + 1)
                      reserve ledger outsideLeft)
                (unitPrefix (count + 1) ++
                  [cell00, cursorMarker] ++ suffix)) =
            some
              (configAtWord acceptState
                (sourceLeftBoundary ::
                  scratchWord (count + 1 + remaining) 1
                    reserve ledger outsideLeft)
                (basePrefix kind before ++
                  unitPrefix (count + 1 + remaining) ++
                    [cell00, cursorMarker] ++ suffix)) := by
        exact hTail
      have all := exactRun_add kind
        (unitReloadSteps
          (before.length + 2 + 2 * remaining) count)
        (reloadLoopSteps before.length
          (count + 1) remaining)
        _ _ _ hIterationCanonical hTailCanonical
      have finalCount :
          count + 1 + remaining =
            count + (remaining + 1) := by
        omega
      rw [finalCount] at all
      simpa [reloadLoopSteps] using all

def seekPrefix (kind : NatKind) (value : Nat)
    (before : List PackedCell) : List WorkSymbol :=
  basePrefix kind before ++ unitPrefix value ++ [cell00]

theorem seekPrefix_length (kind : NatKind) (value : Nat)
    (before : List PackedCell) :
    (seekPrefix kind value before).length =
      before.length + 2 * value + 3 := by
  simp [seekPrefix, basePrefix_length, unitPrefix_length]
  omega

theorem seekPrefix_all_packed (kind : NatKind) (value : Nat)
    (before : List PackedCell) :
    ∀ symbol, symbol ∈ seekPrefix kind value before →
      TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  rw [seekPrefix, List.mem_append] at member
  rcases member with fromPrefix | fromTerminal
  · rw [List.mem_append] at fromPrefix
    rcases fromPrefix with fromBase | fromUnits
    · exact basePrefix_all_packed kind before symbol fromBase
    · exact unitPrefix_all_packed value symbol fromUnits
  · simp only [List.mem_singleton] at fromTerminal
    subst symbol
    constructor

def initialSeekSteps (beforeLength value : Nat) : Nat :=
  beforeLength + 2 * value + 5

def workSteps (beforeLength value : Nat) : Nat :=
  initialSeekSteps beforeLength value +
    reloadLoopSteps beforeLength 0 value

theorem reloadLoopSteps_evaluated
    (beforeLength count remaining : Nat) :
    reloadLoopSteps beforeLength count remaining =
      3 * remaining * remaining +
        2 * beforeLength * remaining +
        2 * count * remaining +
        11 * remaining + beforeLength + 3 := by
  induction remaining generalizing count with
  | zero =>
      simp [reloadLoopSteps, reloadFinishSteps]
  | succ remaining inductionHypothesis =>
      rw [reloadLoopSteps, inductionHypothesis]
      unfold unitReloadSteps
      simp only [Nat.mul_succ, Nat.mul_add,
        Nat.add_mul]
      omega

theorem workSteps_evaluated (beforeLength value : Nat) :
    workSteps beforeLength value =
      3 * value * value +
        2 * beforeLength * value +
        13 * value + 2 * beforeLength + 8 := by
  rw [workSteps, reloadLoopSteps_evaluated]
  unfold initialSeekSteps
  omega

def workPolynomial : NatPolynomial :=
  .add (NatPolynomial.quadratic 5 8)
    (NatPolynomial.linear 15 0)

theorem workPolynomial_eval (size : Nat) :
    workPolynomial.eval size =
      5 * size * size + 15 * size + 8 := by
  simp [workPolynomial, NatPolynomial.quadratic,
    NatPolynomial.linear]
  omega

def polynomialWorkBound
    (beforeLength value : Nat) : Nat :=
  workPolynomial.eval (beforeLength + value)

theorem workSteps_le_polynomialWorkBound
    (beforeLength value : Nat) :
    workSteps beforeLength value ≤
      polynomialWorkBound beforeLength value := by
  rw [workSteps_evaluated]
  unfold polynomialWorkBound
  rw [workPolynomial_eval]
  have valueLe : value ≤ beforeLength + value := by omega
  have beforeLe : beforeLength ≤ beforeLength + value := by omega
  have squareLe :
      value * value ≤
        (beforeLength + value) * (beforeLength + value) :=
    Nat.mul_le_mul valueLe valueLe
  have crossLe :
      beforeLength * value ≤
        (beforeLength + value) * (beforeLength + value) :=
    Nat.mul_le_mul beforeLe valueLe
  have squareScaled :=
    Nat.mul_le_mul_left 3 squareLe
  have crossScaled :=
    Nat.mul_le_mul_left 2 crossLe
  have valueScaled :=
    Nat.mul_le_mul_left 13 valueLe
  have beforeScaled :=
    Nat.mul_le_mul_left 2 beforeLe
  have quadraticLe :
      3 * (value * value) +
          2 * (beforeLength * value) ≤
        5 * ((beforeLength + value) *
          (beforeLength + value)) := by
    have combined :=
      Nat.add_le_add squareScaled crossScaled
    omega
  have linearLe :
      13 * value + 2 * beforeLength ≤
        15 * (beforeLength + value) := by
    omega
  simp only [Nat.mul_assoc]
  omega

theorem workRunExact (kind : NatKind) (value : Nat)
    (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) :
    workRunExact? machine
        (workSteps before.length value)
        (entryConfiguration kind value before
          afterSource targetAndRight reserve ledger outsideLeft) =
      some
        (finalConfiguration kind value before
          afterSource targetAndRight reserve ledger outsideLeft) := by
  let seekWord := seekPrefix kind value before
  let rightSuffix := afterSource ++ targetAndRight
  let leftSide :=
    sourceLeftBoundary ::
      scratchWord 0 (value + 1) reserve ledger outsideLeft
  have hSeek := seek_word_exact kind seekWord
    (cursorMarker :: rightSuffix) leftSide
    (seekPrefix_all_packed kind value before)
  have seekWordLength :
      seekWord.length =
        before.length + 2 * value + 3 := by
    exact seekPrefix_length kind value before
  rw [seekWordLength] at hSeek
  have hCursor :=
    exactRun_one kind _ _
      (seek_cursor_step kind
        (seekWord.reverse ++ leftSide) rightSuffix)
  have hTerminal :=
    exactRun_one kind _ _
      (terminal_step kind
        ((basePrefix kind before ++
          unitPrefix value).reverse ++ leftSide)
        (cursorMarker :: rightSuffix))
  have hLoop := reload_loop_exact kind before 0 value
    rightSuffix reserve ledger outsideLeft
  have hSeekCanonical :
      workRunExact? machine
          (before.length + 2 * value + 3)
          (entryConfiguration kind value before
            afterSource targetAndRight reserve ledger outsideLeft) =
        some
          (configAtWord startState
            (seekWord.reverse ++ leftSide)
            (cursorMarker :: rightSuffix)) := by
    cases kind <;>
      simpa [machineFor, seekWord, rightSuffix, leftSide,
        entryConfiguration, markedSourceCells_shape,
        seekPrefix, basePrefix, List.append_assoc] using hSeek
  have hTerminalCanonical :
      workRunExact? machine 1
          (configAtLeftWord terminalState
            (seekWord.reverse ++ leftSide)
            (cursorMarker :: rightSuffix)) =
        some
          (configAtLeftWord inspectState
            ((basePrefix kind before ++
                unitPrefix value).reverse ++ leftSide)
            (cell00 :: cursorMarker :: rightSuffix)) := by
    cases kind <;>
      simpa [machineFor, seekWord, seekPrefix,
        List.reverse_append, List.append_assoc] using hTerminal
  have hLoopCanonical :
      workRunExact? machine
          (reloadLoopSteps before.length 0 value)
          (configAtLeftWord inspectState
            ((basePrefix kind before ++
                unitPrefix value).reverse ++ leftSide)
            (cell00 :: cursorMarker :: rightSuffix)) =
        some
          (finalConfiguration kind value before
            afterSource targetAndRight
            reserve ledger outsideLeft) := by
    cases kind <;>
      simpa [machineFor, leftSide, rightSuffix,
        finalConfiguration, markedSourceCells_shape,
        basePrefix,
        unitPrefix, TargetEmitterSourceCapture.unitPrefix,
        List.append_assoc] using hLoop
  have h01 := exactRun_add kind
    (before.length + 2 * value + 3) 1
    _ _ _ hSeekCanonical hCursor
  have h02 := exactRun_add kind
    (before.length + 2 * value + 3 + 1) 1
    _ _ _ h01 hTerminalCanonical
  have all := exactRun_add kind
    (before.length + 2 * value + 3 + 1 + 1)
    (reloadLoopSteps before.length 0 value)
    _ _ _ h02 hLoopCanonical
  have steps :
      before.length + 2 * value + 3 + 1 + 1 +
          reloadLoopSteps before.length 0 value =
        workSteps before.length value := by
    unfold workSteps initialSeekSteps
    omega
  rw [steps] at all
  exact all

theorem input_exact (value : Nat)
    (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) :
    workRunExact? machine
        (workSteps before.length value)
        (entryConfiguration .input value before
          afterSource targetAndRight reserve ledger outsideLeft) =
      some
        (finalConfiguration .input value before
          afterSource targetAndRight reserve ledger outsideLeft) :=
  workRunExact .input value before
    afterSource targetAndRight reserve ledger outsideLeft

theorem gate_exact (value : Nat)
    (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) :
    workRunExact? machine
        (workSteps before.length value)
        (entryConfiguration .gate value before
          afterSource targetAndRight reserve ledger outsideLeft) =
      some
        (finalConfiguration .gate value before
          afterSource targetAndRight reserve ledger outsideLeft) :=
  workRunExact .gate value before
    afterSource targetAndRight reserve ledger outsideLeft

theorem final_halted (kind : NatKind) (value : Nat)
    (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) :
    machine.isHalted
      (finalConfiguration kind value before
        afterSource targetAndRight reserve ledger outsideLeft) = true := by
  unfold finalConfiguration configAtWord
  rw [markedSourceCells_shape]
  cases before with
  | nil =>
      cases kind <;> rfl
  | cons packed rest =>
      cases packed <;> rfl

theorem final_state_eq_accept (kind : NatKind) (value : Nat)
    (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) :
    (finalConfiguration kind value before
      afterSource targetAndRight reserve ledger outsideLeft).state =
        machine.acceptState := by
  unfold finalConfiguration configAtWord
  rw [markedSourceCells_shape]
  cases before with
  | nil =>
      cases kind <;> rfl
  | cons packed rest =>
      cases packed <;> rfl

theorem final_source_and_right_preserved
    (kind : NatKind) (value : Nat)
    (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) :
    (finalConfiguration kind value before
      afterSource targetAndRight reserve ledger outsideLeft).tape.head ::
        (finalConfiguration kind value before
          afterSource targetAndRight reserve ledger outsideLeft).tape.right =
      packedWord before ++ markedSourceCells kind value ++
        afterSource ++ targetAndRight := by
  unfold finalConfiguration configAtWord
  rw [markedSourceCells_shape]
  cases before with
  | nil =>
      cases kind <;> rfl
  | cons packed rest =>
      cases packed <;> rfl

theorem final_scratch_loaded (kind : NatKind) (value : Nat)
    (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) :
    (finalConfiguration kind value before
      afterSource targetAndRight reserve ledger outsideLeft).tape.left =
        sourceLeftBoundary ::
          scratchWord value 1 reserve ledger outsideLeft := by
  unfold finalConfiguration configAtWord
  rw [markedSourceCells_shape]
  cases before with
  | nil =>
      cases kind <;> rfl
  | cons packed rest =>
      cases packed <;> rfl

theorem workRun_bounded (kind : NatKind) (value : Nat)
    (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) :
    workRun machine
        (polynomialWorkBound before.length value)
        (entryConfiguration kind value before
          afterSource targetAndRight reserve ledger outsideLeft) =
      finalConfiguration kind value before
        afterSource targetAndRight reserve ledger outsideLeft := by
  exact workRun_of_workRunExact_halted_le
    machine (workSteps before.length value)
    (polynomialWorkBound before.length value)
    (entryConfiguration kind value before
      afterSource targetAndRight reserve ledger outsideLeft)
    (finalConfiguration kind value before
      afterSource targetAndRight reserve ledger outsideLeft)
    (workRunExact kind value before
      afterSource targetAndRight reserve ledger outsideLeft)
    (final_halted kind value before
      afterSource targetAndRight reserve ledger outsideLeft)
    (workSteps_le_polynomialWorkBound before.length value)

theorem workRun_bounded_accepts
    (kind : NatKind) (value : Nat)
    (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) :
    (workRun machine
      (polynomialWorkBound before.length value)
      (entryConfiguration kind value before
        afterSource targetAndRight reserve ledger outsideLeft)).state =
      machine.acceptState := by
  rw [workRun_bounded kind value before
    afterSource targetAndRight reserve ledger outsideLeft]
  exact final_state_eq_accept kind value before
    afterSource targetAndRight reserve ledger outsideLeft

def rawTimeBound (beforeLength value : Nat) : Nat :=
  6 * polynomialWorkBound beforeLength value

theorem six_workSteps_le_rawTimeBound
    (beforeLength value : Nat) :
    6 * workSteps beforeLength value ≤
      rawTimeBound beforeLength value := by
  unfold rawTimeBound
  exact Nat.mul_le_mul_left 6
    (workSteps_le_polynomialWorkBound beforeLength value)

theorem run_compiled_exact (kind : NatKind) (value : Nat)
    (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) :
    run compiledMachine
        (6 * workSteps before.length value)
        (encodeWorkConfiguration
          (entryConfiguration kind value before
            afterSource targetAndRight reserve ledger outsideLeft)) =
      encodeWorkConfiguration
        (finalConfiguration kind value before
          afterSource targetAndRight reserve ledger outsideLeft) := by
  exact run_compileWorkMachine_mul_of_workRunExact
    machine (workSteps before.length value)
    (entryConfiguration kind value before
      afterSource targetAndRight reserve ledger outsideLeft)
    (finalConfiguration kind value before
      afterSource targetAndRight reserve ledger outsideLeft)
    (workRunExact kind value before
      afterSource targetAndRight reserve ledger outsideLeft)

theorem run_compiled_bounded (kind : NatKind) (value : Nat)
    (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol) :
    run compiledMachine
        (rawTimeBound before.length value)
        (encodeWorkConfiguration
          (entryConfiguration kind value before
            afterSource targetAndRight reserve ledger outsideLeft)) =
      encodeWorkConfiguration
        (finalConfiguration kind value before
          afterSource targetAndRight reserve ledger outsideLeft) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    machine (workSteps before.length value)
    (rawTimeBound before.length value)
    (entryConfiguration kind value before
      afterSource targetAndRight reserve ledger outsideLeft)
    (finalConfiguration kind value before
      afterSource targetAndRight reserve ledger outsideLeft)
    (workRunExact kind value before
      afterSource targetAndRight reserve ledger outsideLeft)
    (final_halted kind value before
      afterSource targetAndRight reserve ledger outsideLeft)
    (six_workSteps_le_rawTimeBound before.length value)

theorem run_compiled_blankEquivalent
    (kind : NatKind) (value : Nat)
    (before : List PackedCell)
    (afterSource targetAndRight reserve ledger outsideLeft :
      List WorkSymbol)
    (initial : Configuration)
    (equivalent :
      Configuration.BlankEquivalent initial
        (encodeWorkConfiguration
          (entryConfiguration kind value before
            afterSource targetAndRight reserve ledger outsideLeft))) :
    Configuration.BlankEquivalent
      (run compiledMachine
        (rawTimeBound before.length value) initial)
      (encodeWorkConfiguration
        (finalConfiguration kind value before
          afterSource targetAndRight reserve ledger outsideLeft)) := by
  have transported :=
    run_blankEquivalent compiledMachine
      (rawTimeBound before.length value) equivalent
  rw [run_compiled_bounded kind value before
    afterSource targetAndRight reserve ledger outsideLeft] at transported
  exact transported

/-! ### Fail-closed malformed-workspace behavior -/

private theorem stayFromWord_of_find
    (state : Nat) (symbol : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      machine.isHalted
        (configAtWord state left (symbol :: right)) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol deadState symbol .stay)) :
    workStep? machine
        (configAtWord state left (symbol :: right)) =
      some
        (configAtWord deadState left (symbol :: right)) := by
  calc
    workStep? machine
        (configAtWord state left (symbol :: right)) =
      some
        (applyWorkRule
          (literalRule state symbol deadState symbol .stay)
          (configAtWord state left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some
        (configAtWord deadState left (symbol :: right)) := by
      rfl

private theorem stayFromLeftWord_of_find
    (state : Nat) (symbol : WorkSymbol)
    (left right : List WorkSymbol)
    (notHalted :
      machine.isHalted
        (configAtLeftWord state (symbol :: left) right) = false)
    (found :
      findWorkRule rules state symbol =
        some (literalRule state symbol deadState symbol .stay)) :
    workStep? machine
        (configAtLeftWord state (symbol :: left) right) =
      some
        (configAtLeftWord deadState (symbol :: left) right) := by
  calc
    workStep? machine
        (configAtLeftWord state (symbol :: left) right) =
      some
        (applyWorkRule
          (literalRule state symbol deadState symbol .stay)
          (configAtLeftWord state (symbol :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted found
    _ = some
        (configAtLeftWord deadState (symbol :: left) right) := by
      rfl

set_option maxRecDepth 100000 in
private theorem find_seek_dead (symbol : WorkSymbol)
    (not00 : symbol ≠ cell00)
    (not01 : symbol ≠ cell01)
    (not10 : symbol ≠ cell10)
    (not11 : symbol ≠ cell11)
    (notCursor : symbol ≠ cursorMarker) :
    findWorkRule rules startState symbol =
      some (literalRule startState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [cell00, cell01, cell10, cell11,
      TargetEmitterSourceCapture.cell00,
      TargetEmitterSourceCapture.cell01,
      TargetEmitterSourceCapture.cell10,
      TargetEmitterSourceCapture.cell11,
      cursorMarker, TargetEmitterSourceCapture.cursorMarker,
      TargetEmitterCursorAppender.cursorMarker,
      WorkSymbol.zeroZero, WorkSymbol.zeroOne,
      WorkSymbol.oneZero, WorkSymbol.oneOne,
      WorkSymbol.oneBlank]
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_terminal_dead (symbol : WorkSymbol)
    (malformed : symbol ≠ cell00) :
    findWorkRule rules terminalState symbol =
      some (literalRule terminalState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [cell00, TargetEmitterSourceCapture.cell00,
      WorkSymbol.zeroZero]
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_inspect_dead (symbol : WorkSymbol)
    (notUnit : symbol ≠ cell01)
    (notInputTag : symbol ≠ cell11)
    (notGateTag : symbol ≠ cell10) :
    findWorkRule rules inspectState symbol =
      some (literalRule inspectState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [cell01, cell10, cell11,
      TargetEmitterSourceCapture.cell01,
      TargetEmitterSourceCapture.cell10,
      TargetEmitterSourceCapture.cell11,
      WorkSymbol.zeroOne, WorkSymbol.oneZero,
      WorkSymbol.oneOne]
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_pair_first_dead (symbol : WorkSymbol)
    (malformed : symbol ≠ cell00) :
    findWorkRule rules pairFirstState symbol =
      some (literalRule pairFirstState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [cell00, TargetEmitterSourceCapture.cell00,
      WorkSymbol.zeroZero]
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_rewind_dead (symbol : WorkSymbol)
    (not00 : symbol ≠ cell00)
    (not01 : symbol ≠ cell01)
    (not10 : symbol ≠ cell10)
    (not11 : symbol ≠ cell11)
    (notBoundary : symbol ≠ sourceLeftBoundary) :
    findWorkRule rules rewindBoundaryState symbol =
      some (literalRule rewindBoundaryState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [cell00, cell01, cell10, cell11,
      TargetEmitterSourceCapture.cell00,
      TargetEmitterSourceCapture.cell01,
      TargetEmitterSourceCapture.cell10,
      TargetEmitterSourceCapture.cell11,
      sourceLeftBoundary,
      TargetEmitterSourceCapture.sourceLeftBoundary,
      TargetEmitter.sourceLeftBoundary,
      WorkSymbol.zeroZero, WorkSymbol.zeroOne,
      WorkSymbol.oneZero, WorkSymbol.oneOne,
      WorkSymbol.blankZero]
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_increment_seek_dead (symbol : WorkSymbol)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    findWorkRule rules incrementSeekState symbol =
      some (literalRule incrementSeekState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [unaryUnit, unarySeparator,
      TargetEmitter.unaryUnit, TargetEmitter.unarySeparator,
      WorkSymbol.zeroBlank, WorkSymbol.oneBlank]
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_increment_write_dead (symbol : WorkSymbol)
    (malformed : symbol ≠ WorkSymbol.blank) :
    findWorkRule rules incrementWriteState symbol =
      some (literalRule incrementWriteState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [WorkSymbol.blank]
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_increment_return_dead (symbol : WorkSymbol)
    (notUnit : symbol ≠ unaryUnit)
    (notBoundary : symbol ≠ sourceLeftBoundary) :
    findWorkRule rules incrementReturnState symbol =
      some (literalRule incrementReturnState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [unaryUnit, TargetEmitter.unaryUnit,
      sourceLeftBoundary,
      TargetEmitterSourceCapture.sourceLeftBoundary,
      TargetEmitter.sourceLeftBoundary,
      WorkSymbol.zeroBlank, WorkSymbol.blankZero]
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_resume_dead (symbol : WorkSymbol)
    (not00 : symbol ≠ cell00)
    (not01 : symbol ≠ cell01)
    (not10 : symbol ≠ cell10)
    (not11 : symbol ≠ cell11)
    (notMark : symbol ≠ temporaryMark) :
    findWorkRule rules resumeSeekState symbol =
      some (literalRule resumeSeekState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [cell00, cell01, cell10, cell11,
      TargetEmitterSourceCapture.cell00,
      TargetEmitterSourceCapture.cell01,
      TargetEmitterSourceCapture.cell10,
      TargetEmitterSourceCapture.cell11,
      temporaryMark, TargetEmitter.sourceTargetBoundary,
      WorkSymbol.zeroZero, WorkSymbol.zeroOne,
      WorkSymbol.oneZero, WorkSymbol.oneOne,
      WorkSymbol.blankOne]
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_restore_dead (symbol : WorkSymbol)
    (malformed : symbol ≠ cell00) :
    findWorkRule rules restorePairFirstState symbol =
      some (literalRule restorePairFirstState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [cell00, TargetEmitterSourceCapture.cell00,
      WorkSymbol.zeroZero]
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_input_tag_dead (symbol : WorkSymbol)
    (malformed : symbol ≠ cell00) :
    findWorkRule rules inputTagFirstState symbol =
      some (literalRule inputTagFirstState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [cell00, TargetEmitterSourceCapture.cell00,
      WorkSymbol.zeroZero]
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_gate_tag_dead (symbol : WorkSymbol)
    (malformed : symbol ≠ cell01) :
    findWorkRule rules gateTagFirstState symbol =
      some (literalRule gateTagFirstState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [cell01, TargetEmitterSourceCapture.cell01,
      WorkSymbol.zeroOne]
  all_goals decide

set_option maxRecDepth 100000 in
private theorem find_final_rewind_dead (symbol : WorkSymbol)
    (not00 : symbol ≠ cell00)
    (not01 : symbol ≠ cell01)
    (not10 : symbol ≠ cell10)
    (not11 : symbol ≠ cell11)
    (notBoundary : symbol ≠ sourceLeftBoundary) :
    findWorkRule rules rewindFinalState symbol =
      some (literalRule rewindFinalState symbol
        deadState symbol .stay) := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    simp_all [cell00, cell01, cell10, cell11,
      TargetEmitterSourceCapture.cell00,
      TargetEmitterSourceCapture.cell01,
      TargetEmitterSourceCapture.cell10,
      TargetEmitterSourceCapture.cell11,
      sourceLeftBoundary,
      TargetEmitterSourceCapture.sourceLeftBoundary,
      TargetEmitter.sourceLeftBoundary,
      WorkSymbol.zeroZero, WorkSymbol.zeroOne,
      WorkSymbol.oneZero, WorkSymbol.oneOne,
      WorkSymbol.blankZero]
  all_goals decide

theorem malformed_seek_enters_dead (symbol : WorkSymbol)
    (left right : List WorkSymbol)
    (not00 : symbol ≠ cell00)
    (not01 : symbol ≠ cell01)
    (not10 : symbol ≠ cell10)
    (not11 : symbol ≠ cell11)
    (notCursor : symbol ≠ cursorMarker) :
    workStep? machine
        (configAtWord startState left (symbol :: right)) =
      some
        (configAtWord deadState left (symbol :: right)) := by
  apply stayFromWord_of_find
  · rfl
  · exact find_seek_dead symbol
      not00 not01 not10 not11 notCursor

theorem malformed_cursor_predecessor_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (malformed : symbol ≠ cell00) :
    workStep? machine
        (configAtLeftWord terminalState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  apply stayFromLeftWord_of_find
  · rfl
  · exact find_terminal_dead symbol malformed

theorem malformed_source_cell_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notUnit : symbol ≠ cell01)
    (notInputTag : symbol ≠ cell11)
    (notGateTag : symbol ≠ cell10) :
    workStep? machine
        (configAtLeftWord inspectState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  apply stayFromLeftWord_of_find
  · rfl
  · exact find_inspect_dead symbol
      notUnit notInputTag notGateTag

theorem malformed_unit_pair_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (malformed : symbol ≠ cell00) :
    workStep? machine
        (configAtLeftWord pairFirstState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  apply stayFromLeftWord_of_find
  · rfl
  · exact find_pair_first_dead symbol malformed

theorem malformed_source_rewind_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (not00 : symbol ≠ cell00)
    (not01 : symbol ≠ cell01)
    (not10 : symbol ≠ cell10)
    (not11 : symbol ≠ cell11)
    (notBoundary : symbol ≠ sourceLeftBoundary) :
    workStep? machine
        (configAtLeftWord rewindBoundaryState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  apply stayFromLeftWord_of_find
  · rfl
  · exact find_rewind_dead symbol
      not00 not01 not10 not11 notBoundary

theorem malformed_scratch_tally_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notUnit : symbol ≠ unaryUnit)
    (notSeparator : symbol ≠ unarySeparator) :
    workStep? machine
        (configAtLeftWord incrementSeekState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  apply stayFromLeftWord_of_find
  · rfl
  · exact find_increment_seek_dead symbol
      notUnit notSeparator

theorem occupied_scratch_slot_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (occupied : symbol ≠ WorkSymbol.blank) :
    workStep? machine
        (configAtLeftWord incrementWriteState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  apply stayFromLeftWord_of_find
  · rfl
  · exact find_increment_write_dead symbol occupied

theorem malformed_scratch_return_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (notUnit : symbol ≠ unaryUnit)
    (notBoundary : symbol ≠ sourceLeftBoundary) :
    workStep? machine
        (configAtWord incrementReturnState
          left (symbol :: right)) =
      some
        (configAtWord deadState
          left (symbol :: right)) := by
  apply stayFromWord_of_find
  · rfl
  · exact find_increment_return_dead symbol
      notUnit notBoundary

theorem malformed_resume_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (not00 : symbol ≠ cell00)
    (not01 : symbol ≠ cell01)
    (not10 : symbol ≠ cell10)
    (not11 : symbol ≠ cell11)
    (notMark : symbol ≠ temporaryMark) :
    workStep? machine
        (configAtWord resumeSeekState
          left (symbol :: right)) =
      some
        (configAtWord deadState
          left (symbol :: right)) := by
  apply stayFromWord_of_find
  · rfl
  · exact find_resume_dead symbol
      not00 not01 not10 not11 notMark

theorem malformed_restored_pair_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (malformed : symbol ≠ cell00) :
    workStep? machine
        (configAtLeftWord restorePairFirstState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  apply stayFromLeftWord_of_find
  · rfl
  · exact find_restore_dead symbol malformed

theorem malformed_input_tag_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (malformed : symbol ≠ cell00) :
    workStep? machine
        (configAtLeftWord inputTagFirstState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  apply stayFromLeftWord_of_find
  · rfl
  · exact find_input_tag_dead symbol malformed

theorem malformed_gate_tag_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (malformed : symbol ≠ cell01) :
    workStep? machine
        (configAtLeftWord gateTagFirstState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  apply stayFromLeftWord_of_find
  · rfl
  · exact find_gate_tag_dead symbol malformed

theorem malformed_final_rewind_enters_dead
    (symbol : WorkSymbol) (left right : List WorkSymbol)
    (not00 : symbol ≠ cell00)
    (not01 : symbol ≠ cell01)
    (not10 : symbol ≠ cell10)
    (not11 : symbol ≠ cell11)
    (notBoundary : symbol ≠ sourceLeftBoundary) :
    workStep? machine
        (configAtLeftWord rewindFinalState
          (symbol :: left) right) =
      some
        (configAtLeftWord deadState
          (symbol :: left) right) := by
  apply stayFromLeftWord_of_find
  · rfl
  · exact find_final_rewind_dead symbol
      not00 not01 not10 not11 notBoundary

theorem dead_not_halted (tape : WorkTape) :
    machine.isHalted
      { state := deadState, tape := tape } = false := by
  rfl

theorem dead_stuck (tape : WorkTape) :
    workStep? machine
      { state := deadState, tape := tape } = none := by
  unfold workStep?
  rw [dead_not_halted]
  change
    (match findWorkRule rules deadState tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           { state := deadState, tape := tape })) = none
  rw [no_rule_at_dead]

end PNP.Concrete.LockedNAND.TargetEmitterMarkedSourceReload

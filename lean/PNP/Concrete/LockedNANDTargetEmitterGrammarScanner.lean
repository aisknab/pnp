/-
Copyright (c) 2026 PNP Labs.

A literal finite work machine for the grammar-only strict-v0 circuit boundary.

This scanner is deliberately weaker than `LockedNANDSourceParser`: it checks
the exact external token grammar and the declared number of gate records, but
does not compare source indices with either the input count or the completed
gate prefix.  Consequently every `encodeCircuit raw` word is accepted,
including encodings whose raw references fail intrinsic elaboration.

The executable table below does not call `decodeCircuit`, `RawCircuit.elaborate`,
the raw target builder, or any semantic source/target function.  Successful
execution restores every packed source cell and returns the head to the first
cell.  Any unexpected symbol enters a cleanup path which erases the guarded
source region before rejecting.
-/

import PNP.Concrete.LockedNANDSourceParserFailureShapes
import PNP.Concrete.LockedNANDSourceParserTotalTrace
import PNP.Concrete.LockedNANDSourceParserValidTrace
import PNP.Concrete.PipelineRefinement

namespace PNP.Concrete.LockedNAND.TargetEmitterGrammarScanner

/-! ### Fixed nine-symbol alphabet -/

def cellBlank : WorkSymbol := WorkSymbol.blank
def leftGuard : WorkSymbol := WorkSymbol.blankZero
def cursorMark : WorkSymbol := WorkSymbol.blankOne
def countMark : WorkSymbol := WorkSymbol.zeroBlank
def cell00 : WorkSymbol := WorkSymbol.zeroZero
def cell01 : WorkSymbol := WorkSymbol.zeroOne
def gateMark : WorkSymbol := WorkSymbol.oneBlank
def cell10 : WorkSymbol := WorkSymbol.oneZero
def cell11 : WorkSymbol := WorkSymbol.oneOne

def workAlphabet : List WorkSymbol :=
  [cellBlank, leftGuard, cursorMark, countMark,
    cell00, cell01, gateMark, cell10, cell11]

inductive SourceContinuation where
  | gateLeft
  | gateRight
  | output
deriving BEq, DecidableEq, Repr

namespace SourceContinuation

def code : SourceContinuation → Nat
  | .gateLeft => 0
  | .gateRight => 1
  | .output => 2

def all : List SourceContinuation :=
  [.gateLeft, .gateRight, .output]

end SourceContinuation

/-! ### Disjoint finite control -/

namespace State

def accept : Nat := 0
def reject : Nat := 1
def boot : Nat := 2
def installGuard : Nat := 3
def versionFirst : Nat := 4
def versionSecond : Nat := 5
def inputCountFirst : Nat := 6
def inputCountSecond : Nat := 7
def gateCountFirst : Nat := 8
def gateCountSecond : Nat := 9
def gateStart : Nat := 10
def gateEndFirst : Nat := 11
def gateEndSecond : Nat := 12
def programEndSecond : Nat := 13
def programCountSeekGuard : Nat := 14
def programSkipVersionFirst : Nat := 15
def programSkipVersionSecond : Nat := 16
def programSkipInputFirst : Nat := 17
def programSkipInputSecond : Nat := 18
def programCountFirst : Nat := 19
def programCountSecond : Nat := 20
def programSeekCursor : Nat := 21
def programSkipSecond : Nat := 22
def outputsEndFirst : Nat := 23
def outputsEndSecond : Nat := 24
def instanceEndFirst : Nat := 25
def instanceEndSecond : Nat := 26
def finalEOF : Nat := 27
def successRestoreLeft : Nat := 28
def cleanupSeekGuard : Nat := 29
def cleanupRight : Nat := 30

private def boolCode : Bool → Nat
  | false => 0
  | true => 1

private def gateDecrementBase (firstWas01 : Bool) : Nat :=
  40 + 8 * boolCode firstWas01

def gateDecrementSeekGuard (firstWas01 : Bool) : Nat :=
  gateDecrementBase firstWas01

def gateDecrementVersionFirst (firstWas01 : Bool) : Nat :=
  gateDecrementBase firstWas01 + 1

def gateDecrementVersionSecond (firstWas01 : Bool) : Nat :=
  gateDecrementBase firstWas01 + 2

def gateDecrementInputFirst (firstWas01 : Bool) : Nat :=
  gateDecrementBase firstWas01 + 3

def gateDecrementInputSecond (firstWas01 : Bool) : Nat :=
  gateDecrementBase firstWas01 + 4

def gateDecrementCountFirst (firstWas01 : Bool) : Nat :=
  gateDecrementBase firstWas01 + 5

def gateDecrementCountSecond (firstWas01 : Bool) : Nat :=
  gateDecrementBase firstWas01 + 6

def gateDecrementSeekCursor (firstWas01 : Bool) : Nat :=
  gateDecrementBase firstWas01 + 7

private def sourceBase (continuation : SourceContinuation) : Nat :=
  60 + 5 * continuation.code

def sourceStart (continuation : SourceContinuation) : Nat :=
  sourceBase continuation

def sourceAfter00 (continuation : SourceContinuation) : Nat :=
  sourceBase continuation + 1

def sourceAfter01 (continuation : SourceContinuation) : Nat :=
  sourceBase continuation + 2

def sourceNatFirst (continuation : SourceContinuation) : Nat :=
  sourceBase continuation + 3

def sourceNatSecond (continuation : SourceContinuation) : Nat :=
  sourceBase continuation + 4

end State

/-! ### Total nine-way state rows -/

structure Action where
  targetState : Nat
  writeSymbol : WorkSymbol
  move : HeadMove

structure StateProgram where
  state : Nat
  action : WorkSymbol → Action

def keepAction (target : Nat) (move : HeadMove)
    (symbol : WorkSymbol) : Action :=
  { targetState := target, writeSymbol := symbol, move := move }

def writeAction (target : Nat) (write : WorkSymbol)
    (move : HeadMove) : Action :=
  { targetState := target, writeSymbol := write, move := move }

def cleanupAction (symbol : WorkSymbol) : Action :=
  keepAction State.cleanupSeekGuard .stay symbol

def expectOne (expected : WorkSymbol) (action : Action)
    (symbol : WorkSymbol) : Action :=
  if symbol == expected then action else cleanupAction symbol

def expectTwo (first second : WorkSymbol)
    (firstAction secondAction : Action)
    (symbol : WorkSymbol) : Action :=
  if symbol == first then firstAction
  else if symbol == second then secondAction
  else cleanupAction symbol

def expectThree (first second third : WorkSymbol)
    (firstAction secondAction thirdAction : Action)
    (symbol : WorkSymbol) : Action :=
  if symbol == first then firstAction
  else if symbol == second then secondAction
  else if symbol == third then thirdAction
  else cleanupAction symbol

def stateRules (program : StateProgram) : List WorkRule :=
  workAlphabet.map (fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.targetState
      writeSymbol := action.writeSymbol
      move := action.move })

def afterSourceState : SourceContinuation → Nat
  | .gateLeft => State.sourceStart .gateRight
  | .gateRight => State.gateEndFirst
  | .output => State.outputsEndFirst

private def corePrograms : List StateProgram :=
  [ { state := State.boot
      action := fun symbol =>
        keepAction State.installGuard .left symbol }
  , { state := State.installGuard
      action := fun _ =>
        writeAction State.versionFirst leftGuard .right }
  , { state := State.versionFirst
      action := expectOne cell00
        (keepAction State.versionSecond .right cell00) }
  , { state := State.versionSecond
      action := expectOne cell00
        (keepAction State.inputCountFirst .right cell00) }
  , { state := State.inputCountFirst
      action := expectOne cell00
        (keepAction State.inputCountSecond .right cell00) }
  , { state := State.inputCountSecond
      action := expectTwo cell01 cell10
        (keepAction State.inputCountFirst .right cell01)
        (keepAction State.gateCountFirst .right cell10) }
  , { state := State.gateCountFirst
      action := expectOne cell00
        (keepAction State.gateCountSecond .right cell00) }
  , { state := State.gateCountSecond
      action := expectTwo cell01 cell10
        (keepAction State.gateCountFirst .right cell01)
        (keepAction State.gateStart .right cell10) }
  , { state := State.gateStart
      action := fun symbol =>
        if symbol == cell00 then
          writeAction (State.gateDecrementSeekGuard false)
            cursorMark .left
        else if symbol == cell01 then
          writeAction (State.gateDecrementSeekGuard true)
            cursorMark .left
        else if symbol == cell10 then
          writeAction State.programEndSecond cursorMark .right
        else
          cleanupAction symbol }
  , { state := State.gateEndFirst
      action := expectOne cell01
        (writeAction State.gateEndSecond gateMark .right) }
  , { state := State.gateEndSecond
      action := expectOne cell11
        (keepAction State.gateStart .right cell11) }
  , { state := State.programEndSecond
      action := expectOne cell00
        (keepAction State.programCountSeekGuard .left cell00) }
  , { state := State.programCountSeekGuard
      action := fun symbol =>
        if symbol == leftGuard then
          keepAction State.programSkipVersionFirst .right symbol
        else
          keepAction State.programCountSeekGuard .left symbol }
  , { state := State.programSkipVersionFirst
      action := expectOne cell00
        (keepAction State.programSkipVersionSecond .right cell00) }
  , { state := State.programSkipVersionSecond
      action := expectOne cell00
        (keepAction State.programSkipInputFirst .right cell00) }
  , { state := State.programSkipInputFirst
      action := expectOne cell00
        (keepAction State.programSkipInputSecond .right cell00) }
  , { state := State.programSkipInputSecond
      action := expectTwo cell01 cell10
        (keepAction State.programSkipInputFirst .right cell01)
        (keepAction State.programCountFirst .right cell10) }
  , { state := State.programCountFirst
      action := expectOne cell00
        (keepAction State.programCountSecond .right cell00) }
  , { state := State.programCountSecond
      action := fun symbol =>
        if symbol == countMark then
          writeAction State.programCountFirst cell01 .right
        else if symbol == cell10 then
          keepAction State.programSeekCursor .right symbol
        else
          cleanupAction symbol }
  , { state := State.programSeekCursor
      action := fun symbol =>
        if symbol == cursorMark then
          writeAction State.programSkipSecond cell10 .right
        else if symbol == cellBlank then
          cleanupAction symbol
        else
          keepAction State.programSeekCursor .right symbol }
  , { state := State.programSkipSecond
      action := expectOne cell00
        (keepAction (State.sourceStart .output) .right cell00) }
  , { state := State.outputsEndFirst
      action := expectOne cell10
        (keepAction State.outputsEndSecond .right cell10) }
  , { state := State.outputsEndSecond
      action := expectOne cell01
        (keepAction State.instanceEndFirst .right cell01) }
  , { state := State.instanceEndFirst
      action := expectOne cell10
        (keepAction State.instanceEndSecond .right cell10) }
  , { state := State.instanceEndSecond
      action := expectOne cell11
        (keepAction State.finalEOF .right cell11) }
  , { state := State.finalEOF
      action := expectOne cellBlank
        (keepAction State.successRestoreLeft .left cellBlank) }
  , { state := State.successRestoreLeft
      action := fun symbol =>
        if symbol == gateMark then
          writeAction State.successRestoreLeft cell01 .left
        else if symbol == leftGuard then
          writeAction State.accept cellBlank .right
        else if symbol == cell00 then
          keepAction State.successRestoreLeft .left symbol
        else if symbol == cell01 then
          keepAction State.successRestoreLeft .left symbol
        else if symbol == cell10 then
          keepAction State.successRestoreLeft .left symbol
        else if symbol == cell11 then
          keepAction State.successRestoreLeft .left symbol
        else
          cleanupAction symbol }
  , { state := State.cleanupSeekGuard
      action := fun symbol =>
        if symbol == leftGuard then
          writeAction State.cleanupRight cellBlank .right
        else
          keepAction State.cleanupSeekGuard .left symbol }
  , { state := State.cleanupRight
      action := fun symbol =>
        if symbol == cellBlank then
          keepAction State.reject .stay symbol
        else
          writeAction State.cleanupRight cellBlank .right }
  ]

private def gateDecrementPrograms (firstWas01 : Bool) :
    List StateProgram :=
  [ { state := State.gateDecrementSeekGuard firstWas01
      action := fun symbol =>
        if symbol == leftGuard then
          keepAction (State.gateDecrementVersionFirst firstWas01)
            .right symbol
        else
          keepAction (State.gateDecrementSeekGuard firstWas01)
            .left symbol }
  , { state := State.gateDecrementVersionFirst firstWas01
      action := expectOne cell00
        (keepAction (State.gateDecrementVersionSecond firstWas01)
          .right cell00) }
  , { state := State.gateDecrementVersionSecond firstWas01
      action := expectOne cell00
        (keepAction (State.gateDecrementInputFirst firstWas01)
          .right cell00) }
  , { state := State.gateDecrementInputFirst firstWas01
      action := expectOne cell00
        (keepAction (State.gateDecrementInputSecond firstWas01)
          .right cell00) }
  , { state := State.gateDecrementInputSecond firstWas01
      action := expectTwo cell01 cell10
        (keepAction (State.gateDecrementInputFirst firstWas01)
          .right cell01)
        (keepAction (State.gateDecrementCountFirst firstWas01)
          .right cell10) }
  , { state := State.gateDecrementCountFirst firstWas01
      action := expectOne cell00
        (keepAction (State.gateDecrementCountSecond firstWas01)
          .right cell00) }
  , { state := State.gateDecrementCountSecond firstWas01
      action := fun symbol =>
        if symbol == countMark then
          keepAction (State.gateDecrementCountFirst firstWas01)
            .right symbol
        else if symbol == cell01 then
          writeAction (State.gateDecrementSeekCursor firstWas01)
            countMark .right
        else
          cleanupAction symbol }
  , { state := State.gateDecrementSeekCursor firstWas01
      action := fun symbol =>
        if symbol == cursorMark then
          if firstWas01 then
            writeAction (State.sourceAfter01 .gateLeft) cell01 .right
          else
            writeAction (State.sourceAfter00 .gateLeft) cell00 .right
        else if symbol == cellBlank then
          cleanupAction symbol
        else
          keepAction (State.gateDecrementSeekCursor firstWas01)
            .right symbol }
  ]

private def allGateDecrementPrograms : List StateProgram :=
  gateDecrementPrograms false ++ gateDecrementPrograms true

private def sourcePrograms (continuation : SourceContinuation) :
    List StateProgram :=
  [ { state := State.sourceStart continuation
      action := expectTwo cell00 cell01
        (keepAction (State.sourceAfter00 continuation) .right cell00)
        (keepAction (State.sourceAfter01 continuation) .right cell01) }
  , { state := State.sourceAfter00 continuation
      action := expectOne cell11
        (keepAction (State.sourceNatFirst continuation) .right cell11) }
  , { state := State.sourceAfter01 continuation
      action := expectThree cell00 cell01 cell10
        (keepAction (afterSourceState continuation) .right cell00)
        (keepAction (afterSourceState continuation) .right cell01)
        (keepAction (State.sourceNatFirst continuation) .right cell10) }
  , { state := State.sourceNatFirst continuation
      action := expectOne cell00
        (keepAction (State.sourceNatSecond continuation) .right cell00) }
  , { state := State.sourceNatSecond continuation
      action := expectTwo cell01 cell10
        (keepAction (State.sourceNatFirst continuation) .right cell01)
        (keepAction (afterSourceState continuation) .right cell10) }
  ]

private def allSourcePrograms : List StateProgram :=
  SourceContinuation.all.flatMap sourcePrograms

/-- Complete fixed state program.  The functions above are evaluated while
materializing this finite list; no decoder participates in the rule table. -/
def statePrograms : List StateProgram :=
  corePrograms ++ allGateDecrementPrograms ++ allSourcePrograms

/-- Sixty active control states, with exactly one row for each work symbol. -/
theorem statePrograms_length : statePrograms.length = 60 := by
  rfl

def rules : List WorkRule :=
  statePrograms.flatMap stateRules

def machine : WorkMachine :=
  { rules := rules
    startState := State.boot
    acceptState := State.accept
    rejectState := State.reject }

def compiledMachine : Machine :=
  compileWorkMachine machine

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

private theorem stateRules_source_eq {program : StateProgram}
    {rule : WorkRule} (member : rule ∈ stateRules program) :
    rule.sourceState = program.state := by
  rcases List.mem_map.mp member with ⟨symbol, _symbolMember, ruleEq⟩
  rw [← ruleEq]

private theorem stateRules_pairwise_query_distinct
    (program : StateProgram) :
    (stateRules program).Pairwise QueryDistinct := by
  unfold stateRules workAlphabet QueryDistinct
  simp [cellBlank, leftGuard, cursorMark, countMark,
    cell00, cell01, gateMark, cell10, cell11,
    WorkSymbol.blank, WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem materializedPrograms_pairwise_query_distinct
    (programs : List StateProgram)
    (stateDistinct : programs.Pairwise (fun left right =>
      left.state ≠ right.state)) :
    (programs.flatMap stateRules).Pairwise QueryDistinct := by
  induction programs with
  | nil => exact List.Pairwise.nil
  | cons first rest ih =>
      cases stateDistinct with
      | cons firstDistinct restDistinct =>
          change
            (stateRules first ++ rest.flatMap stateRules).Pairwise
              QueryDistinct
          rw [List.pairwise_append]
          refine
            ⟨stateRules_pairwise_query_distinct first,
             ih restDistinct, ?_⟩
          intro left leftMember right rightMember queryEq
          rcases List.mem_flatMap.mp rightMember with
            ⟨rightProgram, rightProgramMember, rightRuleMember⟩
          have sourceNe :=
            firstDistinct rightProgram rightProgramMember
          have leftSource := stateRules_source_eq leftMember
          have rightSource := stateRules_source_eq rightRuleMember
          have sourceEq := congrArg Prod.fst queryEq
          exact sourceNe
            (leftSource.symm.trans (sourceEq.trans rightSource))

set_option maxRecDepth 100000 in
private theorem statePrograms_pairwise_state_distinct :
    statePrograms.Pairwise (fun left right =>
      left.state ≠ right.state) := by
  decide

theorem rules_pairwise_query_distinct :
    rules.Pairwise QueryDistinct := by
  exact materializedPrograms_pairwise_query_distinct statePrograms
    statePrograms_pairwise_state_distinct

private theorem materializedPrograms_length
    (programs : List StateProgram) :
    (programs.flatMap stateRules).length = 9 * programs.length := by
  induction programs with
  | nil => rfl
  | cons first rest ih =>
      change
        (stateRules first ++ rest.flatMap stateRules).length =
          9 * Nat.succ rest.length
      rw [List.length_append, ih, Nat.mul_succ]
      have firstLength : (stateRules first).length = 9 := by
        rfl
      rw [firstLength, Nat.add_comm]

def ruleCount : Nat := 540

theorem rules_length : rules.length = ruleCount := by
  change (statePrograms.flatMap stateRules).length = 540
  rw [materializedPrograms_length, statePrograms_length]

theorem machine_startState_ne_acceptState :
    machine.startState ≠ machine.acceptState := by
  intro impossible
  contradiction

theorem machine_startState_ne_rejectState :
    machine.startState ≠ machine.rejectState := by
  intro impossible
  contradiction

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  intro impossible
  contradiction

set_option maxRecDepth 300000 in
theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules State.accept symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 300000 in
theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules State.reject symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

/-! ### Exact grammar-local traces -/

private theorem exactRun_add (first second : Nat)
    (initial middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first initial = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial = some final := by
  induction first generalizing initial with
  | zero =>
      have initialEq : initial = middle := Option.some.inj hFirst
      cases initialEq
      simpa using hSecond
  | succ first ih =>
      cases stepEq : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => workRunExact? machine first next) =
              some middle at hFirst
          rw [stepEq] at hFirst
          contradiction
      | some next =>
          have tail :
              workRunExact? machine first next = some middle := by
            change
              (match workStep? machine initial with
               | none => none
               | some next => workRunExact? machine first next) =
                some middle at hFirst
            rw [stepEq] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? machine initial with
             | none => none
             | some next =>
                 workRunExact? machine (first + second) next) =
              some final
          rw [stepEq]
          exact ih next tail

def tapeAtWord (left : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := left, head := cellBlank, right := [] }
  | first :: rest => { left := left, head := first, right := rest }

def configAtWord (state : Nat) (left word : List WorkSymbol) :
    WorkConfiguration :=
  { state := state, tape := tapeAtWord left word }

def pushCrossed : List WorkSymbol → List WorkSymbol → List WorkSymbol
  | [], left => left
  | first :: rest, left => pushCrossed rest (first :: left)

private theorem pushCrossed_append
    (first second left : List WorkSymbol) :
    pushCrossed (first ++ second) left =
      pushCrossed second (pushCrossed first left) := by
  induction first generalizing left with
  | nil => rfl
  | cons symbol rest ih =>
      exact ih (symbol :: left)

private theorem pushCrossed_eq_reverse_append
    (word left : List WorkSymbol) :
    pushCrossed word left = word.reverse ++ left := by
  induction word generalizing left with
  | nil =>
      rfl
  | cons symbol rest ih =>
      rw [pushCrossed, ih]
      simp

private theorem pushCrossed_reverse
    (word right : List WorkSymbol) :
    pushCrossed word.reverse right = word ++ right := by
  rw [pushCrossed_eq_reverse_append, List.reverse_reverse]

/-- Focus a nearest-first word on the left of a tape. -/
def tapeAtLeftWord (right : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := [], head := cellBlank, right := right }
  | first :: rest => { left := rest, head := first, right := right }

def configAtLeftWord (state : Nat) (leftWord right : List WorkSymbol) :
    WorkConfiguration :=
  { state := state, tape := tapeAtLeftWord right leftWord }

/-- A configuration whose logical prefix lies between the unique left guard and
the focused word. -/
def guardedConfig (state : Nat)
    (guardedPrefix word : List WorkSymbol) : WorkConfiguration :=
  configAtWord state (pushCrossed guardedPrefix [leftGuard]) word

private theorem guardedMoveLeft_after_write
    (guardedPrefix : List WorkSymbol)
    (head write : WorkSymbol) (suffix : List WorkSymbol) :
    ((tapeAtWord (pushCrossed guardedPrefix [leftGuard])
        (head :: suffix)).write write).moveLeft =
      tapeAtLeftWord (write :: suffix)
        (guardedPrefix.reverse ++ [leftGuard]) := by
  rw [pushCrossed_eq_reverse_append]
  cases guardedPrefix.reverse <;> rfl

/- Short aliases keep the operational proof legible while retaining the
published source-cell layout definitionally. -/
abbrev natCells (value : Nat) : List WorkSymbol :=
  SourceParser.natCells value

abbrev natCellsTail (value : Nat) : List WorkSymbol :=
  SourceParser.natCellsTail value

abbrev sourceCells (source : RawSource) : List WorkSymbol :=
  SourceParser.sourceCells source

abbrev gateCells (gate : RawGate) : List WorkSymbol :=
  SourceParser.gateCells gate

abbrev gateListCells (gates : List RawGate) : List WorkSymbol :=
  SourceParser.gateListCells gates

abbrev countCells (used remaining : Nat) : List WorkSymbol :=
  SourceParser.countCells used remaining

abbrev borrowedCountCells (used : Nat) : List WorkSymbol :=
  SourceParser.borrowedCountCells used

abbrev markedGateCells (gate : RawGate) : List WorkSymbol :=
  SourceParser.markedGateCells gate

abbrev markedGateListCells (gates : List RawGate) : List WorkSymbol :=
  SourceParser.markedGateListCells gates

abbrev gatePrefix (inputs : Nat) (done todo : List RawGate) :
    List WorkSymbol :=
  SourceParser.gatePrefix inputs done todo

abbrev gateParsingPrefix
    (inputs : Nat) (done todo : List RawGate) : List WorkSymbol :=
  SourceParser.gateParsingPrefix inputs done todo

abbrev circuitCells (raw : RawCircuit) : List WorkSymbol :=
  SourceParser.circuitCells raw

private theorem countCells_eq_borrowed_append
    (used remaining : Nat) :
    countCells used remaining =
      borrowedCountCells used ++ natCells remaining := by
  induction used with
  | zero =>
      rfl
  | succ used ih =>
      change
        cell00 :: countMark :: countCells used remaining =
          cell00 :: countMark ::
            (borrowedCountCells used ++ natCells remaining)
      rw [ih]

private theorem countCells_succ_remaining
    (used remaining : Nat) :
    countCells used (remaining + 1) =
      borrowedCountCells used ++
        cell00 :: cell01 :: natCells remaining := by
  rw [countCells_eq_borrowed_append]
  cases remaining <;> rfl

private theorem markedGateListCells_append
    (first second : List RawGate) :
    SourceParser.markedGateListCells (first ++ second) =
      SourceParser.markedGateListCells first ++
        SourceParser.markedGateListCells second := by
  induction first with
  | nil =>
      rfl
  | cons gate rest ih =>
      change
        SourceParser.markedGateCells gate ++
            SourceParser.markedGateListCells (rest ++ second) =
          (SourceParser.markedGateCells gate ++
              SourceParser.markedGateListCells rest) ++
            SourceParser.markedGateListCells second
      rw [ih, List.append_assoc]

private theorem gatePrefix_snoc
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (todo : List RawGate) :
    gatePrefix inputs (done ++ [gate]) todo =
      gateParsingPrefix inputs done todo ++ markedGateCells gate := by
  simp only [gatePrefix, gateParsingPrefix,
    SourceParser.gatePrefix, SourceParser.gateParsingPrefix]
  rw [markedGateListCells_append]
  simp [markedGateCells, SourceParser.markedGateListCells,
    List.append_assoc]

/-- Symbols which may occur in a successfully guarded canonical prefix. -/
def ordinaryCell (symbol : WorkSymbol) : Prop :=
  symbol = cell00 ∨ symbol = cell01 ∨ symbol = countMark ∨
    symbol = gateMark ∨ symbol = cell10 ∨ symbol = cell11

private theorem cell00_ordinary : ordinaryCell cell00 :=
  Or.inl rfl

private theorem cell01_ordinary : ordinaryCell cell01 :=
  Or.inr (Or.inl rfl)

private theorem countMark_ordinary : ordinaryCell countMark :=
  Or.inr (Or.inr (Or.inl rfl))

private theorem gateMark_ordinary : ordinaryCell gateMark :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))

private theorem cell10_ordinary : ordinaryCell cell10 :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

private theorem cell11_ordinary : ordinaryCell cell11 :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

private theorem ordinary_append
    {first second : List WorkSymbol}
    (firstOrdinary :
      ∀ symbol, symbol ∈ first → ordinaryCell symbol)
    (secondOrdinary :
      ∀ symbol, symbol ∈ second → ordinaryCell symbol) :
    ∀ symbol, symbol ∈ first ++ second → ordinaryCell symbol := by
  intro symbol member
  rcases List.mem_append.mp member with member | member
  · exact firstOrdinary symbol member
  · exact secondOrdinary symbol member

private theorem natCells_ordinary (value : Nat) :
    ∀ symbol, symbol ∈ natCells value → ordinaryCell symbol := by
  induction value with
  | zero =>
      intro symbol member
      simp only [natCells, SourceParser.natCells,
        List.mem_cons, List.not_mem_nil] at member
      rcases member with h | h
      · subst symbol
        exact cell00_ordinary
      · rcases h with h | impossible
        · subst symbol
          exact cell10_ordinary
        · contradiction
  | succ value ih =>
      intro symbol member
      simp only [natCells, SourceParser.natCells,
        List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        exact cell00_ordinary
      · subst symbol
        exact cell01_ordinary
      · exact ih symbol member

private theorem countCells_ordinary (used remaining : Nat) :
    ∀ symbol, symbol ∈ countCells used remaining →
      ordinaryCell symbol := by
  induction used with
  | zero =>
      exact natCells_ordinary remaining
  | succ used ih =>
      intro symbol member
      simp only [countCells, SourceParser.countCells,
        List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        exact cell00_ordinary
      · subst symbol
        exact countMark_ordinary
      · exact ih symbol member

private theorem sourceCells_ordinary (source : RawSource) :
    ∀ symbol, symbol ∈ sourceCells source → ordinaryCell symbol := by
  cases source with
  | input index =>
      intro symbol member
      simp only [sourceCells, SourceParser.sourceCells,
        List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        exact cell00_ordinary
      · subst symbol
        exact cell11_ordinary
      · exact natCells_ordinary index symbol member
  | constant value =>
      cases value <;>
        intro symbol member <;>
        simp only [sourceCells, SourceParser.sourceCells,
          List.mem_cons, List.not_mem_nil] at member <;>
        rcases member with h | h | impossible
      · subst symbol
        exact cell01_ordinary
      · subst symbol
        exact cell00_ordinary
      · contradiction
      · subst symbol
        exact cell01_ordinary
      · subst symbol
        exact cell01_ordinary
      · contradiction
  | gate index =>
      intro symbol member
      simp only [sourceCells, SourceParser.sourceCells,
        List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        exact cell01_ordinary
      · subst symbol
        exact cell10_ordinary
      · exact natCells_ordinary index symbol member

private theorem markedGateCells_ordinary (gate : RawGate) :
    ∀ symbol, symbol ∈ markedGateCells gate →
      ordinaryCell symbol := by
  cases gate with
  | mk left right =>
      unfold markedGateCells
      change
        ∀ symbol,
          symbol ∈
              (sourceCells left ++ sourceCells right) ++
                [gateMark, cell11] →
            ordinaryCell symbol
      apply ordinary_append
        (first := sourceCells left ++ sourceCells right)
        (second := [gateMark, cell11])
      · exact ordinary_append
          (sourceCells_ordinary left) (sourceCells_ordinary right)
      · intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | h | impossible
        · subst symbol
          exact gateMark_ordinary
        · subst symbol
          exact cell11_ordinary
        · contradiction

private theorem markedGateListCells_ordinary (gates : List RawGate) :
    ∀ symbol, symbol ∈ markedGateListCells gates →
      ordinaryCell symbol := by
  induction gates with
  | nil =>
      intro symbol member
      contradiction
  | cons gate rest ih =>
      unfold markedGateListCells
      exact ordinary_append
        (first := markedGateCells gate)
        (second := markedGateListCells rest)
        (markedGateCells_ordinary gate) ih

private theorem gatePrefix_ordinary
    (inputs : Nat) (done todo : List RawGate) :
    ∀ symbol, symbol ∈ gatePrefix inputs done todo →
      ordinaryCell symbol := by
  intro symbol member
  unfold gatePrefix at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | h | impossible
        · subst symbol
          exact cell00_ordinary
        · subst symbol
          exact cell00_ordinary
        · contradiction
      · exact natCells_ordinary inputs symbol member
    · exact countCells_ordinary done.length todo.length symbol member
  · exact markedGateListCells_ordinary done symbol member

private theorem scanRight_exact (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (step : ∀ left head suffix,
      Allowed head →
      workStep? machine
          (configAtWord state left (head :: suffix)) =
        some
          (configAtWord state (head :: left) suffix))
    (word suffix left : List WorkSymbol)
    (allowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtWord state left (word ++ suffix)) =
      some
        (configAtWord state (pushCrossed word left) suffix) := by
  induction word generalizing left with
  | nil =>
      rfl
  | cons head rest ih =>
      have headAllowed :=
        allowed head (List.Mem.head rest)
      have restAllowed :
          ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol member
        exact allowed symbol (List.Mem.tail head member)
      change
        (match workStep? machine
            (configAtWord state left
              (head :: (rest ++ suffix))) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (configAtWord state
              (pushCrossed (head :: rest) left) suffix)
      rw [step left head (rest ++ suffix) headAllowed]
      exact ih (head :: left) restAllowed

private theorem scanLeft_exact (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (step : ∀ head leftTail right,
      Allowed head →
      workStep? machine
          (configAtLeftWord state (head :: leftTail) right) =
        some
          (configAtLeftWord state leftTail (head :: right)))
    (word leftSuffix right : List WorkSymbol)
    (allowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtLeftWord state (word ++ leftSuffix) right) =
      some
        (configAtLeftWord state leftSuffix
          (pushCrossed word right)) := by
  induction word generalizing right with
  | nil =>
      rfl
  | cons head rest ih =>
      have headAllowed :=
        allowed head (List.Mem.head rest)
      have restAllowed :
          ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol member
        exact allowed symbol (List.Mem.tail head member)
      change
        (match workStep? machine
            (configAtLeftWord state
              (head :: (rest ++ leftSuffix)) right) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (configAtLeftWord state leftSuffix
              (pushCrossed (head :: rest) right))
      rw [step head (rest ++ leftSuffix) right headAllowed]
      exact ih (head :: right) restAllowed

/-! ### General canonical header trace -/

set_option maxRecDepth 100000 in
private theorem bootVersion_exact
    (current : WorkSymbol) (rest : List WorkSymbol) :
    workRunExact? machine 4
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            (cell00 :: cell00 :: current :: rest))) =
      some
        (configAtWord State.inputCountFirst
          [cell00, cell00, leftGuard] (current :: rest)) := by
  rfl

set_option maxRecDepth 100000 in
private theorem inputCountUnit_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.inputCountFirst left
          (cell00 :: cell01 :: rest)) =
      some
        (configAtWord State.inputCountFirst
          (cell01 :: cell00 :: left) rest) := by
  rfl

set_option maxRecDepth 100000 in
private theorem inputCountEnd_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.inputCountFirst left
          (cell00 :: cell10 :: rest)) =
      some
        (configAtWord State.gateCountFirst
          (cell10 :: cell00 :: left) rest) := by
  rfl

private theorem inputCount_exact (value : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (value + 1))
        (configAtWord State.inputCountFirst left
          (natCells value ++ suffix)) =
      some
        (configAtWord State.gateCountFirst
          (pushCrossed (natCells value) left) suffix) := by
  induction value generalizing left with
  | zero =>
      exact inputCountEnd_exact left suffix
  | succ value ih =>
      have first :=
        inputCountUnit_exact left (natCells value ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * (value + 1)) _ _ _ first tail
      have costEq :
          2 + 2 * (value + 1) =
            2 * ((value + 1) + 1) := by
        omega
      rw [costEq] at all
      simpa [natCells, SourceParser.natCells, pushCrossed,
        cell00, cell01, SourceParser.cell00,
        SourceParser.cell01] using all

set_option maxRecDepth 100000 in
private theorem gateCountUnit_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.gateCountFirst left
          (cell00 :: cell01 :: rest)) =
      some
        (configAtWord State.gateCountFirst
          (cell01 :: cell00 :: left) rest) := by
  rfl

set_option maxRecDepth 100000 in
private theorem gateCountEnd_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.gateCountFirst left
          (cell00 :: cell10 :: rest)) =
      some
        (configAtWord State.gateStart
          (cell10 :: cell00 :: left) rest) := by
  rfl

private theorem gateCount_exact (value : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (value + 1))
        (configAtWord State.gateCountFirst left
          (natCells value ++ suffix)) =
      some
        (configAtWord State.gateStart
          (pushCrossed (natCells value) left) suffix) := by
  induction value generalizing left with
  | zero =>
      exact gateCountEnd_exact left suffix
  | succ value ih =>
      have first :=
        gateCountUnit_exact left (natCells value ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * (value + 1)) _ _ _ first tail
      have costEq :
          2 + 2 * (value + 1) =
            2 * ((value + 1) + 1) := by
        omega
      rw [costEq] at all
      simpa [natCells, SourceParser.natCells, pushCrossed,
        cell00, cell01, SourceParser.cell00,
        SourceParser.cell01] using all

/-- Exact boot, version, input-count, and declared-gate-count execution for
arbitrary natural fields. -/
theorem canonicalHeader_exact
    (inputs gateCount : Nat) (current : WorkSymbol)
    (rest : List WorkSymbol) :
    workRunExact? machine (2 * inputs + 2 * gateCount + 8)
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            (cell00 :: cell00 ::
              (natCells inputs ++ natCells gateCount ++
                current :: rest)))) =
      some
        (configAtWord State.gateStart
          (pushCrossed (natCells gateCount)
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard]))
          (current :: rest)) := by
  have boot :=
    bootVersion_exact cell00
      (natCellsTail inputs ++ natCells gateCount ++ current :: rest)
  have bootCanonical :
      workRunExact? machine 4
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (cell00 :: cell00 ::
                (natCells inputs ++ natCells gateCount ++
                  current :: rest)))) =
        some
          (configAtWord State.inputCountFirst
            [cell00, cell00, leftGuard]
            (natCells inputs ++ natCells gateCount ++
              current :: rest)) := by
    simpa [natCells, natCellsTail,
      SourceParser.natCells_eq_cons,
      cell00, SourceParser.cell00] using boot
  have inputsRun :=
    inputCount_exact inputs [cell00, cell00, leftGuard]
      (natCells gateCount ++ current :: rest)
  have inputsRunCanonical :
      workRunExact? machine (2 * (inputs + 1))
          (configAtWord State.inputCountFirst
            [cell00, cell00, leftGuard]
            (natCells inputs ++ natCells gateCount ++
              current :: rest)) =
        some
          (configAtWord State.gateCountFirst
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])
            (natCells gateCount ++ current :: rest)) := by
    simpa [List.append_assoc] using inputsRun
  have gatesRun :=
    gateCount_exact gateCount
      (pushCrossed (natCells inputs)
        [cell00, cell00, leftGuard])
      (current :: rest)
  have throughInputs :=
    exactRun_add 4 (2 * (inputs + 1))
      _ _ _ bootCanonical inputsRunCanonical
  have all :=
    exactRun_add (4 + 2 * (inputs + 1))
      (2 * (gateCount + 1))
      _ _ _ throughInputs gatesRun
  have costEq :
      (4 + 2 * (inputs + 1)) + 2 * (gateCount + 1) =
        2 * inputs + 2 * gateCount + 8 := by
    omega
  rw [← costEq]
  exact all

/-! ### Gate-count decrement and source launch -/

def firstSourceCell (firstWas01 : Bool) : WorkSymbol :=
  if firstWas01 then cell01 else cell00

def afterFirstSourceState (firstWas01 : Bool)
    (continuation : SourceContinuation) : Nat :=
  if firstWas01 then State.sourceAfter01 continuation
  else State.sourceAfter00 continuation

set_option maxRecDepth 100000 in
private theorem gateDecrementSeekGuard_step
    (firstWas01 : Bool) (head : WorkSymbol)
    (leftTail right : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          (head :: leftTail) right) =
      some
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          leftTail (head :: right)) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> cases firstWas01 <;> rfl

private theorem gateDecrementSeekGuard_scan_exact
    (firstWas01 : Bool) (scannedPrefix right : List WorkSymbol)
    (ordinary :
      ∀ symbol, symbol ∈ scannedPrefix → ordinaryCell symbol) :
    workRunExact? machine scannedPrefix.length
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          (scannedPrefix.reverse ++ [leftGuard]) right) =
      some
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          [leftGuard] (scannedPrefix ++ right)) := by
  have scan :=
    scanLeft_exact
      (State.gateDecrementSeekGuard firstWas01)
      ordinaryCell
      (gateDecrementSeekGuard_step firstWas01)
      scannedPrefix.reverse [leftGuard] right
      (by
        intro symbol member
        exact ordinary symbol (by simpa using member))
  simpa [pushCrossed_reverse] using scan

set_option maxRecDepth 100000 in
private theorem gateDecrementGuard_exact
    (firstWas01 : Bool) (suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          [leftGuard] suffix) =
      some
        (configAtWord
          (State.gateDecrementVersionFirst firstWas01)
          [leftGuard] suffix) := by
  cases firstWas01 <;> rfl

set_option maxRecDepth 100000 in
private theorem gateDecrementVersion_exact
    (firstWas01 : Bool) (left : List WorkSymbol)
    (suffix : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.gateDecrementVersionFirst firstWas01) left
          (cell00 :: cell00 :: suffix)) =
      some
        (configAtWord
          (State.gateDecrementInputFirst firstWas01)
          (cell00 :: cell00 :: left) suffix) := by
  cases firstWas01 <;> rfl

set_option maxRecDepth 100000 in
private theorem gateDecrementInputUnit_exact
    (firstWas01 : Bool) (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.gateDecrementInputFirst firstWas01) left
          (cell00 :: cell01 :: rest)) =
      some
        (configAtWord
          (State.gateDecrementInputFirst firstWas01)
          (cell01 :: cell00 :: left) rest) := by
  cases firstWas01 <;> rfl

set_option maxRecDepth 100000 in
private theorem gateDecrementInputEnd_exact
    (firstWas01 : Bool) (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.gateDecrementInputFirst firstWas01) left
          (cell00 :: cell10 :: rest)) =
      some
        (configAtWord
          (State.gateDecrementCountFirst firstWas01)
          (cell10 :: cell00 :: left) rest) := by
  cases firstWas01 <;> rfl

private theorem gateDecrementInput_exact
    (firstWas01 : Bool) (value : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (value + 1))
        (configAtWord
          (State.gateDecrementInputFirst firstWas01) left
          (natCells value ++ suffix)) =
      some
        (configAtWord
          (State.gateDecrementCountFirst firstWas01)
          (pushCrossed (natCells value) left)
          suffix) := by
  induction value generalizing left with
  | zero =>
      exact gateDecrementInputEnd_exact firstWas01 left suffix
  | succ value ih =>
      have first :=
        gateDecrementInputUnit_exact firstWas01 left
          (natCells value ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * (value + 1))
          _ _ _ first tail
      have costEq :
          2 + 2 * (value + 1) =
            2 * ((value + 1) + 1) := by
        omega
      rw [costEq] at all
      simpa [natCells, SourceParser.natCells, pushCrossed,
        cell00, cell01, SourceParser.cell00,
        SourceParser.cell01] using all

set_option maxRecDepth 100000 in
private theorem gateDecrementCountBorrowed_exact
    (firstWas01 : Bool) (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.gateDecrementCountFirst firstWas01) left
          (cell00 :: countMark :: rest)) =
      some
        (configAtWord
          (State.gateDecrementCountFirst firstWas01)
          (countMark :: cell00 :: left) rest) := by
  cases firstWas01 <;> rfl

set_option maxRecDepth 100000 in
private theorem gateDecrementCountSelect_exact
    (firstWas01 : Bool) (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.gateDecrementCountFirst firstWas01) left
          (cell00 :: cell01 :: rest)) =
      some
        (configAtWord
          (State.gateDecrementSeekCursor firstWas01)
          (countMark :: cell00 :: left) rest) := by
  cases firstWas01 <;> rfl

private theorem gateDecrementCount_exact
    (firstWas01 : Bool) (used : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (used + 1))
        (configAtWord
          (State.gateDecrementCountFirst firstWas01) left
          (borrowedCountCells used ++
            cell00 :: cell01 :: suffix)) =
      some
        (configAtWord
          (State.gateDecrementSeekCursor firstWas01)
          (pushCrossed (borrowedCountCells (used + 1)) left)
          suffix) := by
  induction used generalizing left with
  | zero =>
      exact gateDecrementCountSelect_exact firstWas01 left suffix
  | succ used ih =>
      have first :=
        gateDecrementCountBorrowed_exact firstWas01 left
          (borrowedCountCells used ++ cell00 :: cell01 :: suffix)
      have tail := ih (countMark :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * (used + 1))
          _ _ _ first tail
      have costEq :
          2 + 2 * (used + 1) =
            2 * ((used + 1) + 1) := by
        omega
      rw [costEq] at all
      simpa [borrowedCountCells,
        SourceParser.borrowedCountCells, pushCrossed,
        cell00, countMark, SourceParser.cell00,
        SourceParser.countMark] using all

private theorem gateDecrementBorrowed_exact
    (firstWas01 : Bool) (used : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * used)
        (configAtWord
          (State.gateDecrementCountFirst firstWas01) left
          (borrowedCountCells used ++ suffix)) =
      some
        (configAtWord
          (State.gateDecrementCountFirst firstWas01)
          (pushCrossed (borrowedCountCells used) left)
          suffix) := by
  induction used generalizing left with
  | zero =>
      rfl
  | succ used ih =>
      have first :=
        gateDecrementCountBorrowed_exact firstWas01 left
          (borrowedCountCells used ++ suffix)
      have tail := ih (countMark :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * used) _ _ _ first tail
      have stepsEq : 2 + 2 * used = 2 * (used + 1) := by
        omega
      rw [stepsEq] at all
      simpa [borrowedCountCells,
        SourceParser.borrowedCountCells, pushCrossed,
        cell00, countMark, SourceParser.cell00,
        SourceParser.countMark] using all

set_option maxRecDepth 100000 in
private theorem gateDecrementSeekCursor_step
    (firstWas01 : Bool) (left : List WorkSymbol)
    (head : WorkSymbol) (suffix : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtWord
          (State.gateDecrementSeekCursor firstWas01) left
          (head :: suffix)) =
      some
        (configAtWord
          (State.gateDecrementSeekCursor firstWas01)
          (head :: left) suffix) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> cases firstWas01 <;> rfl

set_option maxRecDepth 100000 in
private theorem gateDecrementCursor_exact
    (firstWas01 : Bool) (left : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord
          (State.gateDecrementSeekCursor firstWas01) left
          (cursorMark :: current :: rest)) =
      some
        (configAtWord
          (afterFirstSourceState firstWas01 .gateLeft)
          (firstSourceCell firstWas01 :: left)
          (current :: rest)) := by
  cases firstWas01 <;> rfl

private theorem gateDecrementForward_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (gate : RawGate) (todo : List RawGate)
    (current : WorkSymbol) (rest : List WorkSymbol) :
    ∃ steps,
      steps = (gatePrefix inputs done (gate :: todo)).length + 1 ∧
      workRunExact? machine steps
          (configAtWord
            (State.gateDecrementVersionFirst firstWas01)
            [leftGuard]
            (gatePrefix inputs done (gate :: todo) ++
              cursorMark :: current :: rest)) =
        some
          (guardedConfig
            (afterFirstSourceState firstWas01 .gateLeft)
            (gateParsingPrefix inputs done todo ++
              [firstSourceCell firstWas01])
            (current :: rest)) := by
  let afterCount : List WorkSymbol :=
    natCells todo.length ++ markedGateListCells done
  let afterHeader : List WorkSymbol :=
    countCells done.length (todo.length + 1) ++
      markedGateListCells done ++ cursorMark :: current :: rest
  have version :=
    gateDecrementVersion_exact firstWas01 [leftGuard]
      (natCells inputs ++ afterHeader)
  have input :=
    gateDecrementInput_exact firstWas01 inputs
      (cell00 :: cell00 :: [leftGuard]) afterHeader
  have count :=
    gateDecrementCount_exact firstWas01 done.length
      (pushCrossed (natCells inputs)
        (cell00 :: cell00 :: [leftGuard]))
      (afterCount ++ cursorMark :: current :: rest)
  have countCanonical :
      workRunExact? machine (2 * (done.length + 1))
          (configAtWord
            (State.gateDecrementCountFirst firstWas01)
            (pushCrossed (natCells inputs)
              (cell00 :: cell00 :: [leftGuard]))
            afterHeader) =
        some
          (configAtWord
            (State.gateDecrementSeekCursor firstWas01)
            (pushCrossed (borrowedCountCells (done.length + 1))
              (pushCrossed (natCells inputs)
                (cell00 :: cell00 :: [leftGuard])))
            (afterCount ++ cursorMark :: current :: rest)) := by
    simpa [afterHeader, afterCount, countCells_succ_remaining,
      List.append_assoc] using count
  have scan :=
    scanRight_exact
      (State.gateDecrementSeekCursor firstWas01)
      ordinaryCell
      (gateDecrementSeekCursor_step firstWas01)
      afterCount (cursorMark :: current :: rest)
      (pushCrossed (borrowedCountCells (done.length + 1))
        (pushCrossed (natCells inputs)
          (cell00 :: cell00 :: [leftGuard])))
      (ordinary_append
        (natCells_ordinary todo.length)
        (markedGateListCells_ordinary done))
  have cursor :=
    gateDecrementCursor_exact firstWas01
      (pushCrossed afterCount
        (pushCrossed (borrowedCountCells (done.length + 1))
          (pushCrossed (natCells inputs)
            (cell00 :: cell00 :: [leftGuard]))))
      current rest
  have throughInput :=
    exactRun_add 2 (2 * (inputs + 1))
      _ _ _ version input
  have throughCount :=
    exactRun_add (2 + 2 * (inputs + 1))
      (2 * (done.length + 1))
      _ _ _ throughInput countCanonical
  have throughScan :=
    exactRun_add
      ((2 + 2 * (inputs + 1)) +
        2 * (done.length + 1))
      afterCount.length
      _ _ _ throughCount scan
  have all :=
    exactRun_add
      (((2 + 2 * (inputs + 1)) +
        2 * (done.length + 1)) + afterCount.length)
      1 _ _ _ throughScan cursor
  let steps :=
    (((2 + 2 * (inputs + 1)) +
      2 * (done.length + 1)) + afterCount.length) + 1
  have costEq :
      steps =
        (gatePrefix inputs done (gate :: todo)).length + 1 := by
    simp only [steps, gatePrefix, SourceParser.gatePrefix,
      afterCount, List.length_append, List.length_cons,
      List.length_nil, SourceParser.natCells_length,
      countCells_succ_remaining,
      SourceParser.borrowedCountCells_length,
      markedGateListCells]
    omega
  have endpointEq :
      firstSourceCell firstWas01 ::
          pushCrossed (markedGateListCells done)
            (pushCrossed (natCells todo.length)
              (pushCrossed
                (borrowedCountCells (done.length + 1))
                (pushCrossed (natCells inputs)
                  [cell00, cell00, leftGuard]))) =
        pushCrossed
          (gateParsingPrefix inputs done todo ++
            [firstSourceCell firstWas01])
          [leftGuard] := by
    simp only [gateParsingPrefix,
      SourceParser.gateParsingPrefix,
      countCells_eq_borrowed_append]
    repeat rw [pushCrossed_append]
    rfl
  refine ⟨steps, costEq, ?_⟩
  unfold guardedConfig
  rw [← endpointEq]
  simpa [steps, afterHeader, afterCount, gatePrefix,
    SourceParser.gatePrefix, countCells_eq_borrowed_append,
    pushCrossed_append, List.append_assoc,
    markedGateListCells, cell00, SourceParser.cell00] using all

set_option maxRecDepth 100000 in
private theorem gateDecrementCursorWord_exact
    (firstWas01 : Bool) (left word : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord
          (State.gateDecrementSeekCursor firstWas01) left
          (cursorMark :: word)) =
      some
        (configAtWord
          (afterFirstSourceState firstWas01 .gateLeft)
          (firstSourceCell firstWas01 :: left)
          word) := by
  cases firstWas01 <;> cases word <;> rfl

private theorem gateDecrementForwardWord_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (gate : RawGate)
    (todo : List RawGate) (word : List WorkSymbol) :
    ∃ steps,
      steps =
          (gatePrefix inputs done (gate :: todo)).length + 1 ∧
      workRunExact? machine steps
          (configAtWord
            (State.gateDecrementVersionFirst firstWas01)
            [leftGuard]
            (gatePrefix inputs done (gate :: todo) ++
              cursorMark :: word)) =
        some
          (guardedConfig
            (afterFirstSourceState firstWas01 .gateLeft)
            (gateParsingPrefix inputs done todo ++
              [firstSourceCell firstWas01])
            word) := by
  let afterCount : List WorkSymbol :=
    natCells todo.length ++ markedGateListCells done
  let afterHeader : List WorkSymbol :=
    countCells done.length (todo.length + 1) ++
      markedGateListCells done ++ cursorMark :: word
  have version :=
    gateDecrementVersion_exact firstWas01 [leftGuard]
      (natCells inputs ++ afterHeader)
  have input :=
    gateDecrementInput_exact firstWas01 inputs
      (cell00 :: cell00 :: [leftGuard]) afterHeader
  have count :=
    gateDecrementCount_exact firstWas01 done.length
      (pushCrossed (natCells inputs)
        (cell00 :: cell00 :: [leftGuard]))
      (afterCount ++ cursorMark :: word)
  have countCanonical :
      workRunExact? machine (2 * (done.length + 1))
          (configAtWord
            (State.gateDecrementCountFirst firstWas01)
            (pushCrossed (natCells inputs)
              (cell00 :: cell00 :: [leftGuard]))
            afterHeader) =
        some
          (configAtWord
            (State.gateDecrementSeekCursor firstWas01)
            (pushCrossed (borrowedCountCells (done.length + 1))
              (pushCrossed (natCells inputs)
                (cell00 :: cell00 :: [leftGuard])))
            (afterCount ++ cursorMark :: word)) := by
    simpa [afterHeader, afterCount, countCells_succ_remaining,
      List.append_assoc] using count
  have scan :=
    scanRight_exact
      (State.gateDecrementSeekCursor firstWas01)
      ordinaryCell
      (gateDecrementSeekCursor_step firstWas01)
      afterCount (cursorMark :: word)
      (pushCrossed (borrowedCountCells (done.length + 1))
        (pushCrossed (natCells inputs)
          (cell00 :: cell00 :: [leftGuard])))
      (ordinary_append
        (natCells_ordinary todo.length)
        (markedGateListCells_ordinary done))
  let cursorLeft :=
    pushCrossed afterCount
      (pushCrossed (borrowedCountCells (done.length + 1))
        (pushCrossed (natCells inputs)
          (cell00 :: cell00 :: [leftGuard])))
  have cursor :=
    gateDecrementCursorWord_exact
      firstWas01 cursorLeft word
  have throughInput :=
    exactRun_add 2 (2 * (inputs + 1))
      _ _ _ version input
  have throughCount :=
    exactRun_add (2 + 2 * (inputs + 1))
      (2 * (done.length + 1))
      _ _ _ throughInput countCanonical
  have throughScan :=
    exactRun_add
      ((2 + 2 * (inputs + 1)) +
        2 * (done.length + 1))
      afterCount.length
      _ _ _ throughCount scan
  have all :=
    exactRun_add
      (((2 + 2 * (inputs + 1)) +
        2 * (done.length + 1)) + afterCount.length)
      1 _ _ _ throughScan cursor
  let steps :=
    (((2 + 2 * (inputs + 1)) +
      2 * (done.length + 1)) + afterCount.length) + 1
  have costEq :
      steps =
        (gatePrefix inputs done (gate :: todo)).length + 1 := by
    simp only [steps, gatePrefix, SourceParser.gatePrefix,
      afterCount, List.length_append, List.length_cons,
      List.length_nil, SourceParser.natCells_length,
      countCells_succ_remaining,
      SourceParser.borrowedCountCells_length,
      markedGateListCells]
    omega
  have endpointEq :
      firstSourceCell firstWas01 :: cursorLeft =
        pushCrossed
          (gateParsingPrefix inputs done todo ++
            [firstSourceCell firstWas01])
          [leftGuard] := by
    dsimp [cursorLeft, afterCount]
    simp only [gateParsingPrefix,
      SourceParser.gateParsingPrefix,
      countCells_eq_borrowed_append]
    repeat rw [pushCrossed_append]
    rfl
  refine ⟨steps, costEq, ?_⟩
  unfold guardedConfig
  rw [← endpointEq]
  simpa [steps, afterHeader, afterCount, gatePrefix,
    SourceParser.gatePrefix, countCells_eq_borrowed_append,
    pushCrossed_append, List.append_assoc,
    markedGateListCells, cell00, SourceParser.cell00]
    using all

set_option maxRecDepth 100000 in
private theorem gateStartLaunchWord_exact
    (firstWas01 : Bool) (guardedPrefix word : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig State.gateStart guardedPrefix
          (firstSourceCell firstWas01 :: word)) =
      some
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          (guardedPrefix.reverse ++ [leftGuard])
          (cursorMark :: word)) := by
  unfold guardedConfig
  rw [pushCrossed_eq_reverse_append]
  cases firstWas01 <;> cases guardedPrefix.reverse <;> rfl

private theorem gateDecrementWord_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (gate : RawGate)
    (todo : List RawGate) (word : List WorkSymbol) :
    workRunExact? machine
        (2 * (gatePrefix inputs done (gate :: todo)).length + 3)
        (guardedConfig State.gateStart
          (gatePrefix inputs done (gate :: todo))
          (firstSourceCell firstWas01 :: word)) =
      some
        (guardedConfig
          (afterFirstSourceState firstWas01 .gateLeft)
          (gateParsingPrefix inputs done todo ++
            [firstSourceCell firstWas01])
          word) := by
  let logicalPrefix := gatePrefix inputs done (gate :: todo)
  have launch :=
    gateStartLaunchWord_exact
      firstWas01 logicalPrefix word
  have backward :=
    gateDecrementSeekGuard_scan_exact firstWas01 logicalPrefix
      (cursorMark :: word)
      (gatePrefix_ordinary inputs done (gate :: todo))
  have guard :=
    gateDecrementGuard_exact firstWas01
      (logicalPrefix ++ cursorMark :: word)
  rcases
      gateDecrementForwardWord_exact firstWas01
        inputs done gate todo word with
    ⟨forwardSteps, forwardStepsEq, forward⟩
  have throughBackward :=
    exactRun_add 1 logicalPrefix.length _ _ _
      launch backward
  have throughGuard :=
    exactRun_add (1 + logicalPrefix.length) 1
      _ _ _ throughBackward guard
  have all :=
    exactRun_add
      ((1 + logicalPrefix.length) + 1)
      forwardSteps _ _ _ throughGuard forward
  rw [forwardStepsEq] at all
  have costEq :
      ((1 + logicalPrefix.length) + 1) +
          (logicalPrefix.length + 1) =
        2 * logicalPrefix.length + 3 := by
    omega
  rw [costEq] at all
  simpa [logicalPrefix] using all

set_option maxRecDepth 100000 in
private theorem gateStartLaunch_exact
    (firstWas01 : Bool) (guardedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig State.gateStart guardedPrefix
          (firstSourceCell firstWas01 :: current :: rest)) =
      some
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          (guardedPrefix.reverse ++ [leftGuard])
          (cursorMark :: current :: rest)) := by
  have raw :
      workStep? machine
          (guardedConfig State.gateStart guardedPrefix
            (firstSourceCell firstWas01 :: current :: rest)) =
        some
          { state := State.gateDecrementSeekGuard firstWas01
            tape :=
              ((tapeAtWord
                  (pushCrossed guardedPrefix [leftGuard])
                  (firstSourceCell firstWas01 ::
                    current :: rest)).write cursorMark).moveLeft } := by
    cases firstWas01 <;> rfl
  change
    (match workStep? machine
        (guardedConfig State.gateStart guardedPrefix
          (firstSourceCell firstWas01 :: current :: rest)) with
     | none => none
     | some next => some next) =
      some
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          (guardedPrefix.reverse ++ [leftGuard])
          (cursorMark :: current :: rest))
  rw [raw]
  rw [guardedMoveLeft_after_write]
  rfl

private theorem gateDecrement_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (gate : RawGate) (todo : List RawGate)
    (current : WorkSymbol) (rest : List WorkSymbol) :
    workRunExact? machine
        (2 * (gatePrefix inputs done (gate :: todo)).length + 3)
        (guardedConfig State.gateStart
          (gatePrefix inputs done (gate :: todo))
          (firstSourceCell firstWas01 :: current :: rest)) =
      some
        (guardedConfig
          (afterFirstSourceState firstWas01 .gateLeft)
          (gateParsingPrefix inputs done todo ++
            [firstSourceCell firstWas01])
          (current :: rest)) := by
  let logicalPrefix := gatePrefix inputs done (gate :: todo)
  have launch :=
    gateStartLaunch_exact firstWas01 logicalPrefix current rest
  have backward :=
    gateDecrementSeekGuard_scan_exact firstWas01 logicalPrefix
      (cursorMark :: current :: rest)
      (gatePrefix_ordinary inputs done (gate :: todo))
  have guard :=
    gateDecrementGuard_exact firstWas01
      (logicalPrefix ++ cursorMark :: current :: rest)
  rcases gateDecrementForward_exact firstWas01 inputs done gate todo
      current rest with
    ⟨forwardSteps, forwardStepsEq, forward⟩
  have throughBackward :=
    exactRun_add 1 logicalPrefix.length _ _ _ launch backward
  have throughGuard :=
    exactRun_add (1 + logicalPrefix.length) 1
      _ _ _ throughBackward guard
  have all :=
    exactRun_add ((1 + logicalPrefix.length) + 1)
      forwardSteps _ _ _ throughGuard forward
  rw [forwardStepsEq] at all
  have costEq :
      ((1 + logicalPrefix.length) + 1) +
          (logicalPrefix.length + 1) =
        2 * logicalPrefix.length + 3 := by
    omega
  rw [costEq] at all
  simpa [logicalPrefix] using all

set_option maxRecDepth 100000 in
private theorem gateEnd_exact
    (left suffix : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.gateEndFirst left
          (cell01 :: cell11 :: suffix)) =
      some
        (configAtWord State.gateStart
          (cell11 :: gateMark :: left) suffix) := by
  rfl

private theorem gateEndGuarded_exact
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (todo : List RawGate)
    (suffix : List WorkSymbol) :
    workRunExact? machine 2
        (guardedConfig State.gateEndFirst
          (gateParsingPrefix inputs done todo ++
            sourceCells gate.left ++ sourceCells gate.right)
          (cell01 :: cell11 :: suffix)) =
      some
        (guardedConfig State.gateStart
          (gatePrefix inputs (done ++ [gate]) todo)
          suffix) := by
  have base :=
    gateEnd_exact
      (pushCrossed
        (gateParsingPrefix inputs done todo ++
          sourceCells gate.left ++ sourceCells gate.right)
        [leftGuard])
      suffix
  have endpointEq :
      cell11 :: gateMark ::
          pushCrossed
            (gateParsingPrefix inputs done todo ++
              sourceCells gate.left ++ sourceCells gate.right)
            [leftGuard] =
        pushCrossed
          (gateParsingPrefix inputs done todo ++
            ((sourceCells gate.left ++ sourceCells gate.right) ++
              [gateMark, cell11]))
          [leftGuard] := by
    simp only [pushCrossed_append, pushCrossed]
  have endpointEqQualified :
      cell11 :: gateMark ::
          pushCrossed
            (gateParsingPrefix inputs done todo ++
              sourceCells gate.left ++ sourceCells gate.right)
            [leftGuard] =
        pushCrossed
          (gateParsingPrefix inputs done todo ++
            (SourceParser.sourceCells gate.left ++
              SourceParser.sourceCells gate.right ++
                [SourceParser.gateMark, SourceParser.cell11]))
          [leftGuard] := by
    simpa [sourceCells, cell11, gateMark,
      SourceParser.cell11, SourceParser.gateMark] using endpointEq
  rw [gatePrefix_snoc]
  unfold guardedConfig
  simp only [markedGateCells, SourceParser.markedGateCells]
  rw [← endpointEqQualified]
  exact base

/-- The grammar scanner consumes an arbitrary unary natural without consulting
the input-count or prior-gate fields.  This is the operational distinction from
the stricter source parser. -/
theorem sourceNat_exact
    (continuation : SourceContinuation) (value : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (SourceParser.natCells value).length
        (configAtWord (State.sourceNatFirst continuation) left
          (SourceParser.natCells value ++ suffix)) =
      some
        (configAtWord (afterSourceState continuation)
          (pushCrossed (SourceParser.natCells value) left) suffix) := by
  set_option maxRecDepth 100000 in
    induction value generalizing left with
    | zero =>
        cases continuation <;> rfl
    | succ value ih =>
        let middle :=
          configAtWord (State.sourceNatFirst continuation)
            (cell01 :: cell00 :: left)
            (SourceParser.natCells value ++ suffix)
        have first :
            workRunExact? machine 2
                (configAtWord (State.sourceNatFirst continuation) left
                  (cell00 :: cell01 ::
                    (SourceParser.natCells value ++ suffix))) =
              some middle := by
          cases continuation <;> rfl
        have tail :
            workRunExact? machine (SourceParser.natCells value).length
                middle =
              some
                (configAtWord (afterSourceState continuation)
                  (pushCrossed (SourceParser.natCells value)
                    (cell01 :: cell00 :: left))
                  suffix) := by
          exact ih (cell01 :: cell00 :: left)
        have combined :=
          exactRun_add 2 (SourceParser.natCells value).length
            _ middle _ first tail
        have stepsEq :
            2 + (SourceParser.natCells value).length =
              (SourceParser.natCells (value + 1)).length := by
          simp [SourceParser.natCells]
          omega
        rw [stepsEq] at combined
        simpa [SourceParser.natCells, pushCrossed,
          cell00, cell01, SourceParser.cell00,
          SourceParser.cell01] using combined

/-- Every raw source token has an exact non-destructive local trace.  Input
and gate indices are treated identically as unary grammar fields. -/
theorem source_exact
    (continuation : SourceContinuation) (source : RawSource)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (SourceParser.sourceCells source).length
        (configAtWord (State.sourceStart continuation) left
          (SourceParser.sourceCells source ++ suffix)) =
      some
        (configAtWord (afterSourceState continuation)
          (pushCrossed (SourceParser.sourceCells source) left) suffix) := by
  set_option maxRecDepth 100000 in
    cases source with
    | input index =>
        let middle :=
          configAtWord (State.sourceNatFirst continuation)
            (cell11 :: cell00 :: left)
            (SourceParser.natCells index ++ suffix)
        have first :
            workRunExact? machine 2
                (configAtWord (State.sourceStart continuation) left
                  (cell00 :: cell11 ::
                    (SourceParser.natCells index ++ suffix))) =
              some middle := by
          cases continuation <;> rfl
        have tail :
            workRunExact? machine (SourceParser.natCells index).length
                middle =
              some
                (configAtWord (afterSourceState continuation)
                  (pushCrossed (SourceParser.natCells index)
                    (cell11 :: cell00 :: left))
                  suffix) :=
          sourceNat_exact continuation index
            (cell11 :: cell00 :: left) suffix
        have combined :=
          exactRun_add 2 (SourceParser.natCells index).length
            _ middle _ first tail
        have stepsEq :
            2 + (SourceParser.natCells index).length =
              (SourceParser.sourceCells (.input index)).length := by
          simp [SourceParser.sourceCells]
          omega
        rw [stepsEq] at combined
        simpa [SourceParser.sourceCells, pushCrossed,
          cell00, cell11, SourceParser.cell00,
          SourceParser.cell11] using combined
    | constant value =>
        cases value <;> cases continuation <;> rfl
    | gate index =>
        let middle :=
          configAtWord (State.sourceNatFirst continuation)
            (cell10 :: cell01 :: left)
            (SourceParser.natCells index ++ suffix)
        have first :
            workRunExact? machine 2
                (configAtWord (State.sourceStart continuation) left
                  (cell01 :: cell10 ::
                    (SourceParser.natCells index ++ suffix))) =
              some middle := by
          cases continuation <;> rfl
        have tail :
            workRunExact? machine (SourceParser.natCells index).length
                middle =
              some
                (configAtWord (afterSourceState continuation)
                  (pushCrossed (SourceParser.natCells index)
                    (cell10 :: cell01 :: left))
                  suffix) :=
          sourceNat_exact continuation index
            (cell10 :: cell01 :: left) suffix
        have combined :=
          exactRun_add 2 (SourceParser.natCells index).length
            _ middle _ first tail
        have stepsEq :
            2 + (SourceParser.natCells index).length =
              (SourceParser.sourceCells (.gate index)).length := by
          simp [SourceParser.sourceCells]
          omega
        rw [stepsEq] at combined
        simpa [SourceParser.sourceCells, pushCrossed,
          cell01, cell10, SourceParser.cell01,
          SourceParser.cell10] using combined

/-! ### Complete grammar-only source and gate traces -/

def sourceFirstWas01 : RawSource → Bool
  | .input _ => false
  | .constant _ => true
  | .gate _ => true

def sourceRemainderCells : RawSource → List WorkSymbol
  | .input index => cell11 :: natCells index
  | .constant false => [cell00]
  | .constant true => [cell01]
  | .gate index => cell10 :: natCells index

def sourceSecondCell : RawSource → WorkSymbol
  | .input _ => cell11
  | .constant false => cell00
  | .constant true => cell01
  | .gate _ => cell10

def sourceAfterSecondCells : RawSource → List WorkSymbol
  | .input index => natCells index
  | .constant _ => []
  | .gate index => natCells index

private theorem sourceCells_eq_first_remainder (source : RawSource) :
    sourceCells source =
      firstSourceCell (sourceFirstWas01 source) ::
        sourceRemainderCells source := by
  cases source with
  | input index => rfl
  | constant value =>
      cases value <;> rfl
  | gate index => rfl

private theorem sourceRemainderCells_eq_second (source : RawSource) :
    sourceRemainderCells source =
      sourceSecondCell source :: sourceAfterSecondCells source := by
  cases source with
  | input index => rfl
  | constant value =>
      cases value <;> rfl
  | gate index => rfl

private theorem sourceRemainderLocal_exact
    (continuation : SourceContinuation) (source : RawSource)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (sourceRemainderCells source).length
        (configAtWord
          (afterFirstSourceState (sourceFirstWas01 source)
            continuation)
          left (sourceRemainderCells source ++ suffix)) =
      some
        (configAtWord (afterSourceState continuation)
          (pushCrossed (sourceRemainderCells source) left)
          suffix) := by
  set_option maxRecDepth 100000 in
    cases source with
    | input index =>
        let middle :=
          configAtWord (State.sourceNatFirst continuation)
            (cell11 :: left) (natCells index ++ suffix)
        have first :
            workRunExact? machine 1
                (configAtWord (State.sourceAfter00 continuation) left
                  (cell11 :: natCells index ++ suffix)) =
              some middle := by
          cases continuation <;> rfl
        have tail :
            workRunExact? machine (natCells index).length middle =
              some
                (configAtWord (afterSourceState continuation)
                  (pushCrossed (natCells index) (cell11 :: left))
                  suffix) := by
          exact sourceNat_exact continuation index
            (cell11 :: left) suffix
        have all :=
          exactRun_add 1 (natCells index).length
            _ middle _ first tail
        simpa [sourceRemainderCells, sourceFirstWas01,
          afterFirstSourceState, pushCrossed,
          Nat.add_comm] using all
    | constant value =>
        cases value <;> cases continuation <;> rfl
    | gate index =>
        let middle :=
          configAtWord (State.sourceNatFirst continuation)
            (cell10 :: left) (natCells index ++ suffix)
        have first :
            workRunExact? machine 1
                (configAtWord (State.sourceAfter01 continuation) left
                  (cell10 :: natCells index ++ suffix)) =
              some middle := by
          cases continuation <;> rfl
        have tail :
            workRunExact? machine (natCells index).length middle =
              some
                (configAtWord (afterSourceState continuation)
                  (pushCrossed (natCells index) (cell10 :: left))
                  suffix) := by
          exact sourceNat_exact continuation index
            (cell10 :: left) suffix
        have all :=
          exactRun_add 1 (natCells index).length
            _ middle _ first tail
        simpa [sourceRemainderCells, sourceFirstWas01,
          afterFirstSourceState, pushCrossed,
          Nat.add_comm] using all

/-- The remainder of every raw source is consumed in place after its first
cell has been used as the gate-decrement cursor.  No reference bound is
consulted. -/
theorem sourceRemainder_exact
    (continuation : SourceContinuation) (source : RawSource)
    (guardedPrefix suffix : List WorkSymbol) :
    workRunExact? machine (sourceRemainderCells source).length
        (guardedConfig
          (afterFirstSourceState (sourceFirstWas01 source)
            continuation)
          (guardedPrefix ++
            [firstSourceCell (sourceFirstWas01 source)])
          (sourceRemainderCells source ++ suffix)) =
      some
        (guardedConfig (afterSourceState continuation)
          (guardedPrefix ++ sourceCells source) suffix) := by
  have base :=
    sourceRemainderLocal_exact continuation source
      (pushCrossed
        (guardedPrefix ++
          [firstSourceCell (sourceFirstWas01 source)])
        [leftGuard])
      suffix
  unfold guardedConfig
  rw [sourceCells_eq_first_remainder]
  simpa [pushCrossed_append, List.append_assoc,
    pushCrossed] using base

/-- Guarded companion to the local raw-source trace. -/
theorem sourceGuarded_exact
    (continuation : SourceContinuation) (source : RawSource)
    (guardedPrefix suffix : List WorkSymbol) :
    workRunExact? machine (sourceCells source).length
        (guardedConfig (State.sourceStart continuation)
          guardedPrefix (sourceCells source ++ suffix)) =
      some
        (guardedConfig (afterSourceState continuation)
          (guardedPrefix ++ sourceCells source) suffix) := by
  have base :=
    source_exact continuation source
      (pushCrossed guardedPrefix [leftGuard]) suffix
  unfold guardedConfig
  simpa [pushCrossed_append] using base

def gateSteps
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (todo : List RawGate) : Nat :=
  2 * (gatePrefix inputs done (gate :: todo)).length + 3 +
    (sourceRemainderCells gate.left).length +
    (sourceCells gate.right).length + 2

/-- Exact gate-record trace for arbitrary raw sources.  In particular,
out-of-range input and gate indices follow this accepting trace. -/
theorem gate_exact
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (todo : List RawGate)
    (after : List WorkSymbol) :
    workRunExact? machine (gateSteps inputs done gate todo)
        (guardedConfig State.gateStart
          (gatePrefix inputs done (gate :: todo))
          (gateCells gate ++ gateListCells todo ++ after)) =
      some
        (guardedConfig State.gateStart
          (gatePrefix inputs (done ++ [gate]) todo)
          (gateListCells todo ++ after)) := by
  have decrement :=
    gateDecrement_exact (sourceFirstWas01 gate.left)
      inputs done gate todo
      (sourceSecondCell gate.left)
      (sourceAfterSecondCells gate.left ++
        sourceCells gate.right ++ [cell01, cell11] ++
        gateListCells todo ++ after)
  have decrementCanonical :
      workRunExact? machine
          (2 * (gatePrefix inputs done (gate :: todo)).length + 3)
          (guardedConfig State.gateStart
            (gatePrefix inputs done (gate :: todo))
            (gateCells gate ++ gateListCells todo ++ after)) =
        some
          (guardedConfig
            (afterFirstSourceState
              (sourceFirstWas01 gate.left) .gateLeft)
            (gateParsingPrefix inputs done todo ++
              [firstSourceCell (sourceFirstWas01 gate.left)])
            (sourceRemainderCells gate.left ++
              sourceCells gate.right ++ [cell01, cell11] ++
              gateListCells todo ++ after)) := by
    simpa [gateCells, SourceParser.gateCells,
      sourceCells_eq_first_remainder,
      sourceRemainderCells_eq_second,
      List.append_assoc, cell01, cell11,
      SourceParser.cell01, SourceParser.cell11] using decrement
  have leftSource :=
    sourceRemainder_exact .gateLeft gate.left
      (gateParsingPrefix inputs done todo)
      (sourceCells gate.right ++ [cell01, cell11] ++
        gateListCells todo ++ after)
  have leftSourceCanonical :
      workRunExact? machine
          (sourceRemainderCells gate.left).length
          (guardedConfig
            (afterFirstSourceState
              (sourceFirstWas01 gate.left) .gateLeft)
            (gateParsingPrefix inputs done todo ++
              [firstSourceCell (sourceFirstWas01 gate.left)])
            (sourceRemainderCells gate.left ++
              sourceCells gate.right ++ [cell01, cell11] ++
              gateListCells todo ++ after)) =
        some
          (guardedConfig (State.sourceStart .gateRight)
            (gateParsingPrefix inputs done todo ++
              sourceCells gate.left)
            (sourceCells gate.right ++ [cell01, cell11] ++
              gateListCells todo ++ after)) := by
    simpa [afterSourceState, List.append_assoc] using leftSource
  have rightSource :=
    sourceGuarded_exact .gateRight gate.right
      (gateParsingPrefix inputs done todo ++
        sourceCells gate.left)
      ([cell01, cell11] ++ gateListCells todo ++ after)
  have rightSourceCanonical :
      workRunExact? machine (sourceCells gate.right).length
          (guardedConfig (State.sourceStart .gateRight)
            (gateParsingPrefix inputs done todo ++
              sourceCells gate.left)
            (sourceCells gate.right ++ [cell01, cell11] ++
              gateListCells todo ++ after)) =
        some
          (guardedConfig State.gateEndFirst
            (gateParsingPrefix inputs done todo ++
              sourceCells gate.left ++ sourceCells gate.right)
            (cell01 :: cell11 ::
              gateListCells todo ++ after)) := by
    simpa [afterSourceState, List.append_assoc] using rightSource
  have ending :=
    gateEndGuarded_exact inputs done gate todo
      (gateListCells todo ++ after)
  have throughLeft :=
    exactRun_add
      (2 * (gatePrefix inputs done (gate :: todo)).length + 3)
      (sourceRemainderCells gate.left).length
      _ _ _ decrementCanonical leftSourceCanonical
  have throughRight :=
    exactRun_add
      ((2 * (gatePrefix inputs done (gate :: todo)).length + 3) +
        (sourceRemainderCells gate.left).length)
      (sourceCells gate.right).length
      _ _ _ throughLeft rightSourceCanonical
  have all :=
    exactRun_add
      (((2 * (gatePrefix inputs done (gate :: todo)).length + 3) +
        (sourceRemainderCells gate.left).length) +
        (sourceCells gate.right).length)
      2 _ _ _ throughRight ending
  simpa [gateSteps, List.append_assoc] using all

def gatesSteps
    (inputs : Nat) (done : List RawGate) :
    List RawGate → Nat
  | [] => 0
  | gate :: rest =>
      gateSteps inputs done gate rest +
        gatesSteps inputs (done ++ [gate]) rest

/-- Exact grammar trace for every declared canonical gate list, with no
well-formedness premise. -/
theorem gates_exact
    (inputs : Nat) (done gates : List RawGate)
    (after : List WorkSymbol) :
    workRunExact? machine (gatesSteps inputs done gates)
        (guardedConfig State.gateStart
          (gatePrefix inputs done gates)
          (gateListCells gates ++ after)) =
      some
        (guardedConfig State.gateStart
          (gatePrefix inputs (done ++ gates) [])
          after) := by
  induction gates generalizing done with
  | nil =>
      simp only [gatesSteps, gateListCells,
        SourceParser.gateListCells, List.nil_append,
        List.append_nil, workRunExact?]
  | cons gate rest ih =>
      have first := gate_exact inputs done gate rest after
      have tail := ih (done ++ [gate])
      have tailCanonical :
          workRunExact? machine
              (gatesSteps inputs (done ++ [gate]) rest)
              (guardedConfig State.gateStart
                (gatePrefix inputs (done ++ [gate]) rest)
                (gateListCells rest ++ after)) =
            some
              (guardedConfig State.gateStart
                (gatePrefix inputs (done ++ gate :: rest) [])
                after) := by
        simpa [List.append_assoc] using tail
      have all :=
        exactRun_add
          (gateSteps inputs done gate rest)
          (gatesSteps inputs (done ++ [gate]) rest)
          _ _ _ first tailCanonical
      simpa [gatesSteps, gateListCells,
        SourceParser.gateListCells, List.append_assoc] using all

/-! ### Program terminator and output launch -/

set_option maxRecDepth 100000 in
private theorem programEndLaunch_exact
    (guardedPrefix rest : List WorkSymbol) :
    workRunExact? machine 2
        (guardedConfig State.gateStart guardedPrefix
          (cell10 :: cell00 :: rest)) =
      some
        (configAtLeftWord State.programCountSeekGuard
          (cursorMark :: guardedPrefix.reverse ++ [leftGuard])
          (cell00 :: rest)) := by
  unfold guardedConfig
  rw [pushCrossed_eq_reverse_append]
  rfl

set_option maxRecDepth 100000 in
private theorem programSeekGuardCursor_exact
    (leftTail right : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord State.programCountSeekGuard
          (cursorMark :: leftTail) right) =
      some
        (configAtLeftWord State.programCountSeekGuard
          leftTail (cursorMark :: right)) := by
  rfl

set_option maxRecDepth 100000 in
private theorem programSeekGuard_step
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtLeftWord State.programCountSeekGuard
          (head :: leftTail) right) =
      some
        (configAtLeftWord State.programCountSeekGuard
          leftTail (head :: right)) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> rfl

private theorem programSeekGuard_scan_exact
    (guardedPrefix right : List WorkSymbol)
    (ordinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol) :
    workRunExact? machine guardedPrefix.length
        (configAtLeftWord State.programCountSeekGuard
          (guardedPrefix.reverse ++ [leftGuard]) right) =
      some
        (configAtLeftWord State.programCountSeekGuard
          [leftGuard] (guardedPrefix ++ right)) := by
  have scan :=
    scanLeft_exact State.programCountSeekGuard ordinaryCell
      programSeekGuard_step
      guardedPrefix.reverse [leftGuard] right
      (by
        intro symbol member
        exact ordinary symbol (by simpa using member))
  simpa [pushCrossed_reverse] using scan

set_option maxRecDepth 100000 in
private theorem programSeekGuard_exact
    (suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord State.programCountSeekGuard
          [leftGuard] suffix) =
      some
        (configAtWord State.programSkipVersionFirst
          [leftGuard] suffix) := by
  rfl

set_option maxRecDepth 100000 in
private theorem programSkipVersion_exact
    (left suffix : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.programSkipVersionFirst left
          (cell00 :: cell00 :: suffix)) =
      some
        (configAtWord State.programSkipInputFirst
          (cell00 :: cell00 :: left) suffix) := by
  rfl

set_option maxRecDepth 100000 in
private theorem programSkipInputUnit_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.programSkipInputFirst left
          (cell00 :: cell01 :: rest)) =
      some
        (configAtWord State.programSkipInputFirst
          (cell01 :: cell00 :: left) rest) := by
  rfl

set_option maxRecDepth 100000 in
private theorem programSkipInputEnd_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.programSkipInputFirst left
          (cell00 :: cell10 :: rest)) =
      some
        (configAtWord State.programCountFirst
          (cell10 :: cell00 :: left) rest) := by
  rfl

private theorem programSkipInput_exact
    (inputs : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (inputs + 1))
        (configAtWord State.programSkipInputFirst left
          (natCells inputs ++ suffix)) =
      some
        (configAtWord State.programCountFirst
          (pushCrossed (natCells inputs) left) suffix) := by
  induction inputs generalizing left with
  | zero =>
      exact programSkipInputEnd_exact left suffix
  | succ inputs ih =>
      have first :=
        programSkipInputUnit_exact left
          (natCells inputs ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * (inputs + 1))
          _ _ _ first tail
      have costEq :
          2 + 2 * (inputs + 1) =
            2 * ((inputs + 1) + 1) := by
        omega
      rw [costEq] at all
      simpa [natCells, SourceParser.natCells, pushCrossed,
        cell00, cell01, SourceParser.cell00,
        SourceParser.cell01] using all

set_option maxRecDepth 100000 in
private theorem programCountMarker_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.programCountFirst left
          (cell00 :: countMark :: rest)) =
      some
        (configAtWord State.programCountFirst
          (cell01 :: cell00 :: left) rest) := by
  rfl

private def programCountUnitCells : Nat → List WorkSymbol
  | 0 => []
  | used + 1 =>
      cell00 :: cell01 :: programCountUnitCells used

private theorem programCountUnitCells_ordinary (used : Nat) :
    ∀ symbol, symbol ∈ programCountUnitCells used →
      ordinaryCell symbol := by
  induction used with
  | zero =>
      intro symbol member
      contradiction
  | succ used ih =>
      intro symbol member
      simp only [programCountUnitCells,
        List.mem_cons] at member
      rcases member with rfl | rfl | member
      · exact cell00_ordinary
      · exact cell01_ordinary
      · exact ih symbol member

private theorem programCountMarkers_exact
    (used : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * used)
        (configAtWord State.programCountFirst left
          (borrowedCountCells used ++ suffix)) =
      some
        (configAtWord State.programCountFirst
          (pushCrossed (programCountUnitCells used) left)
          suffix) := by
  induction used generalizing left with
  | zero =>
      rfl
  | succ used ih =>
      have first :=
        programCountMarker_exact left
          (borrowedCountCells used ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * used) _ _ _ first tail
      have stepsEq : 2 + 2 * used = 2 * (used + 1) := by
        omega
      rw [stepsEq] at all
      simpa [borrowedCountCells,
        SourceParser.borrowedCountCells,
        programCountUnitCells, pushCrossed,
        cell00, cell01, countMark,
        SourceParser.cell00, SourceParser.cell01,
        SourceParser.countMark] using all

set_option maxRecDepth 100000 in
private theorem programCountEnd_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.programCountFirst left
          (cell00 :: cell10 :: rest)) =
      some
        (configAtWord State.programSeekCursor
          (cell10 :: cell00 :: left) rest) := by
  rfl

private theorem programCountRestore_exact
    (gateCount : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (gateCount + 1))
        (configAtWord State.programCountFirst left
          (countCells gateCount 0 ++ suffix)) =
      some
        (configAtWord State.programSeekCursor
          (pushCrossed (natCells gateCount) left) suffix) := by
  induction gateCount generalizing left with
  | zero =>
      exact programCountEnd_exact left suffix
  | succ gateCount ih =>
      have first :=
        programCountMarker_exact left
          (countCells gateCount 0 ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * (gateCount + 1))
          _ _ _ first tail
      have costEq :
          2 + 2 * (gateCount + 1) =
            2 * ((gateCount + 1) + 1) := by
        omega
      rw [costEq] at all
      simpa [countCells, SourceParser.countCells,
        natCells, SourceParser.natCells, pushCrossed,
        cell00, cell01, countMark,
        SourceParser.cell00, SourceParser.cell01,
        SourceParser.countMark] using all

set_option maxRecDepth 100000 in
private theorem programSeekCursor_step
    (left : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtWord State.programSeekCursor
          left (head :: suffix)) =
      some
        (configAtWord State.programSeekCursor
          (head :: left) suffix) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> rfl

set_option maxRecDepth 100000 in
private theorem programCursor_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord State.programSeekCursor left
          (cursorMark :: cell00 :: rest)) =
      some
        (configAtWord State.programSkipSecond
          (cell10 :: left) (cell00 :: rest)) := by
  rfl

set_option maxRecDepth 100000 in
private theorem programSkipSecond_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord State.programSkipSecond left
          (cell00 :: rest)) =
      some
        (configAtWord (State.sourceStart .output)
          (cell00 :: left) rest) := by
  rfl

/-- Marked canonical prefix immediately before the output source. -/
def outputPrefix (inputs : Nat) (gates : List RawGate) :
    List WorkSymbol :=
  [cell00, cell00] ++ natCells inputs ++
    natCells gates.length ++ markedGateListCells gates ++
    [cell10, cell00]

def programEndSteps (inputs : Nat) (gates : List RawGate) : Nat :=
  let logicalPrefix := gatePrefix inputs gates []
  2 + 1 + logicalPrefix.length + 1 +
    2 + 2 * (inputs + 1) + 2 * (gates.length + 1) +
    (markedGateListCells gates).length + 1 + 1

/-- The program terminator restores the declared gate-count field, retains
the gate anchors, restores its cursor, and launches the output source. -/
theorem programEnd_exact
    (inputs : Nat) (gates : List RawGate)
    (rest : List WorkSymbol) :
    workRunExact? machine (programEndSteps inputs gates)
        (guardedConfig State.gateStart
          (gatePrefix inputs gates [])
          (cell10 :: cell00 :: rest)) =
      some
        (guardedConfig (State.sourceStart .output)
          (outputPrefix inputs gates) rest) := by
  let logicalPrefix := gatePrefix inputs gates []
  let afterCount :=
    markedGateListCells gates ++
      cursorMark :: cell00 :: rest
  have launch :=
    programEndLaunch_exact logicalPrefix rest
  have cursorLeft :=
    programSeekGuardCursor_exact
      (logicalPrefix.reverse ++ [leftGuard])
      (cell00 :: rest)
  have backward :=
    programSeekGuard_scan_exact logicalPrefix
      (cursorMark :: cell00 :: rest)
      (gatePrefix_ordinary inputs gates [])
  have guard :=
    programSeekGuard_exact
      (logicalPrefix ++ cursorMark :: cell00 :: rest)
  have version :=
    programSkipVersion_exact [leftGuard]
      (natCells inputs ++ countCells gates.length 0 ++ afterCount)
  have versionCanonical :
      workRunExact? machine 2
          (configAtWord State.programSkipVersionFirst
            [leftGuard]
            (logicalPrefix ++ cursorMark :: cell00 :: rest)) =
        some
          (configAtWord State.programSkipInputFirst
            [cell00, cell00, leftGuard]
            (natCells inputs ++
              countCells gates.length 0 ++ afterCount)) := by
    simpa [logicalPrefix, gatePrefix,
      SourceParser.gatePrefix, afterCount,
      List.append_assoc, natCells, countCells,
      markedGateListCells, cell00,
      SourceParser.cell00] using version
  have input :=
    programSkipInput_exact inputs
      [cell00, cell00, leftGuard]
      (countCells gates.length 0 ++ afterCount)
  have inputCanonical :
      workRunExact? machine (2 * (inputs + 1))
          (configAtWord State.programSkipInputFirst
            [cell00, cell00, leftGuard]
            (natCells inputs ++
              countCells gates.length 0 ++ afterCount)) =
        some
          (configAtWord State.programCountFirst
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])
            (countCells gates.length 0 ++ afterCount)) := by
    simpa [List.append_assoc] using input
  have count :=
    programCountRestore_exact gates.length
      (pushCrossed (natCells inputs)
        [cell00, cell00, leftGuard])
      afterCount
  have scan :=
    scanRight_exact State.programSeekCursor ordinaryCell
      programSeekCursor_step
      (markedGateListCells gates)
      (cursorMark :: cell00 :: rest)
      (pushCrossed (natCells gates.length)
        (pushCrossed (natCells inputs)
          [cell00, cell00, leftGuard]))
      (markedGateListCells_ordinary gates)
  have cursor :=
    programCursor_exact
      (pushCrossed (markedGateListCells gates)
        (pushCrossed (natCells gates.length)
          (pushCrossed (natCells inputs)
            [cell00, cell00, leftGuard])))
      rest
  have skip :=
    programSkipSecond_exact
      (cell10 ::
        pushCrossed (markedGateListCells gates)
          (pushCrossed (natCells gates.length)
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])))
      rest
  have throughCursorLeft :=
    exactRun_add 2 1 _ _ _ launch cursorLeft
  have throughBackward :=
    exactRun_add (2 + 1) logicalPrefix.length
      _ _ _ throughCursorLeft backward
  have throughGuard :=
    exactRun_add ((2 + 1) + logicalPrefix.length) 1
      _ _ _ throughBackward guard
  have throughVersion :=
    exactRun_add
      (((2 + 1) + logicalPrefix.length) + 1)
      2 _ _ _ throughGuard versionCanonical
  have throughInput :=
    exactRun_add
      ((((2 + 1) + logicalPrefix.length) + 1) + 2)
      (2 * (inputs + 1))
      _ _ _ throughVersion inputCanonical
  have throughCount :=
    exactRun_add
      (((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1))
      (2 * (gates.length + 1))
      _ _ _ throughInput count
  have throughScan :=
    exactRun_add
      ((((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1)) + 2 * (gates.length + 1))
      (markedGateListCells gates).length
      _ _ _ throughCount scan
  have throughCursor :=
    exactRun_add
      (((((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1)) + 2 * (gates.length + 1)) +
        (markedGateListCells gates).length)
      1 _ _ _ throughScan cursor
  have all :=
    exactRun_add
      ((((((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1)) + 2 * (gates.length + 1)) +
        (markedGateListCells gates).length) + 1)
      1 _ _ _ throughCursor skip
  have endpointEq :
      cell00 :: cell10 ::
          pushCrossed (markedGateListCells gates)
            (pushCrossed (natCells gates.length)
              (pushCrossed (natCells inputs)
                [cell00, cell00, leftGuard])) =
        pushCrossed (outputPrefix inputs gates) [leftGuard] := by
    unfold outputPrefix
    repeat rw [pushCrossed_append]
    rfl
  unfold programEndSteps guardedConfig
  rw [← endpointEq]
  simpa [logicalPrefix, afterCount,
    guardedConfig, List.append_assoc] using all

/-! ### Final delimiters and accepting restoration -/

def markedCircuitCells (raw : RawCircuit) : List WorkSymbol :=
  outputPrefix raw.inputCount raw.gates ++
    sourceCells raw.output ++
    [cell10, cell01, cell10, cell11]

theorem markedCircuitCells_length (raw : RawCircuit) :
    (markedCircuitCells raw).length =
      (circuitCells raw).length := by
  simp [markedCircuitCells, outputPrefix, circuitCells,
    SourceParser.circuitCells,
    SourceParser.markedGateListCells_length]

private theorem natCells_no_gateMark (value : Nat) :
    ∀ symbol, symbol ∈ natCells value → symbol ≠ gateMark := by
  induction value with
  | zero =>
      intro symbol member
      simp only [natCells, SourceParser.natCells,
        List.mem_cons, List.not_mem_nil] at member
      rcases member with h | h | impossible
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
  | succ value ih =>
      intro symbol member
      simp only [natCells, SourceParser.natCells,
        List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact ih symbol member

private theorem natCells_no_countMark (value : Nat) :
    ∀ symbol, symbol ∈ natCells value → symbol ≠ countMark := by
  induction value with
  | zero =>
      intro symbol member
      simp only [natCells, SourceParser.natCells,
        List.mem_cons, List.not_mem_nil] at member
      rcases member with h | h | impossible
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
  | succ value ih =>
      intro symbol member
      simp only [natCells, SourceParser.natCells,
        List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact ih symbol member

private theorem sourceCells_no_gateMark (source : RawSource) :
    ∀ symbol, symbol ∈ sourceCells source → symbol ≠ gateMark := by
  cases source with
  | input index =>
      intro symbol member
      simp only [sourceCells, SourceParser.sourceCells,
        List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact natCells_no_gateMark index symbol member
  | constant value =>
      cases value <;>
        intro symbol member <;>
        simp only [sourceCells, SourceParser.sourceCells,
          List.mem_cons, List.not_mem_nil] at member <;>
        rcases member with h | h | impossible
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
  | gate index =>
      intro symbol member
      simp only [sourceCells, SourceParser.sourceCells,
        List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact natCells_no_gateMark index symbol member

private theorem sourceCells_no_countMark (source : RawSource) :
    ∀ symbol, symbol ∈ sourceCells source → symbol ≠ countMark := by
  cases source with
  | input index =>
      intro symbol member
      simp only [sourceCells, SourceParser.sourceCells,
        List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact natCells_no_countMark index symbol member
  | constant value =>
      cases value <;>
        intro symbol member <;>
        simp only [sourceCells, SourceParser.sourceCells,
          List.mem_cons, List.not_mem_nil] at member <;>
        rcases member with h | h | impossible
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
  | gate index =>
      intro symbol member
      simp only [sourceCells, SourceParser.sourceCells,
        List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact natCells_no_countMark index symbol member

private theorem markedGateCells_no_countMark (gate : RawGate) :
    ∀ symbol, symbol ∈ markedGateCells gate →
      symbol ≠ countMark := by
  cases gate with
  | mk left right =>
      intro symbol member
      simp only [markedGateCells,
        SourceParser.markedGateCells] at member
      rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · exact sourceCells_no_countMark left symbol member
        · exact sourceCells_no_countMark right symbol member
      · simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | h | impossible
        · subst symbol
          decide
        · subst symbol
          decide
        · contradiction

private theorem markedGateListCells_no_countMark
    (gates : List RawGate) :
    ∀ symbol, symbol ∈ markedGateListCells gates →
      symbol ≠ countMark := by
  induction gates with
  | nil =>
      intro symbol member
      contradiction
  | cons gate rest ih =>
      intro symbol member
      unfold markedGateListCells at member
      rcases List.mem_append.mp member with member | member
      · exact markedGateCells_no_countMark gate symbol member
      · exact ih symbol member

set_option maxRecDepth 100000 in
private theorem finalDelimiters_exact
    (guardedPrefix : List WorkSymbol) :
    workRunExact? machine 5
        (guardedConfig State.outputsEndFirst guardedPrefix
          [cell10, cell01, cell10, cell11]) =
      some
        (configAtLeftWord State.successRestoreLeft
          ((guardedPrefix ++
            [cell10, cell01, cell10, cell11]).reverse ++
            [leftGuard])
          [cellBlank]) := by
  unfold guardedConfig
  rw [pushCrossed_eq_reverse_append]
  simp [List.reverse_append]
  rfl

def restorePersistentSymbol (symbol : WorkSymbol) : WorkSymbol :=
  if symbol == gateMark then cell01 else symbol

set_option maxRecDepth 100000 in
private theorem successRestore_step
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (ordinary : ordinaryCell head)
    (noCountMark : head ≠ countMark) :
    workStep? machine
        (configAtLeftWord State.successRestoreLeft
          (head :: leftTail) right) =
      some
        (configAtLeftWord State.successRestoreLeft
          leftTail (restorePersistentSymbol head :: right)) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head
  · rfl
  · rfl
  · exact False.elim (noCountMark rfl)
  · rfl
  · rfl
  · rfl

private theorem successRestoreNearest_exact
    (word leftSuffix right : List WorkSymbol)
    (ordinary : ∀ symbol, symbol ∈ word → ordinaryCell symbol)
    (noCountMark :
      ∀ symbol, symbol ∈ word → symbol ≠ countMark) :
    workRunExact? machine word.length
        (configAtLeftWord State.successRestoreLeft
          (word ++ leftSuffix) right) =
      some
        (configAtLeftWord State.successRestoreLeft
          leftSuffix
          (pushCrossed (word.map restorePersistentSymbol) right)) := by
  induction word generalizing right with
  | nil =>
      rfl
  | cons head rest ih =>
      have headOrdinary :=
        ordinary head (List.Mem.head rest)
      have headNoCountMark :=
        noCountMark head (List.Mem.head rest)
      have restOrdinary :
          ∀ symbol, symbol ∈ rest → ordinaryCell symbol := by
        intro symbol member
        exact ordinary symbol (List.Mem.tail head member)
      have restNoCountMark :
          ∀ symbol, symbol ∈ rest → symbol ≠ countMark := by
        intro symbol member
        exact noCountMark symbol (List.Mem.tail head member)
      change
        (match workStep? machine
            (configAtLeftWord State.successRestoreLeft
              (head :: (rest ++ leftSuffix)) right) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (configAtLeftWord State.successRestoreLeft
              leftSuffix
              (pushCrossed
                ((head :: rest).map restorePersistentSymbol)
                right))
      rw [successRestore_step head (rest ++ leftSuffix) right
        headOrdinary headNoCountMark]
      exact ih (restorePersistentSymbol head :: right)
        restOrdinary restNoCountMark

private theorem successRestoreWord_exact
    (word right : List WorkSymbol)
    (ordinary : ∀ symbol, symbol ∈ word → ordinaryCell symbol)
    (noCountMark :
      ∀ symbol, symbol ∈ word → symbol ≠ countMark) :
    workRunExact? machine word.length
        (configAtLeftWord State.successRestoreLeft
          (word.reverse ++ [leftGuard]) right) =
      some
        (configAtLeftWord State.successRestoreLeft
          [leftGuard]
          (word.map restorePersistentSymbol ++ right)) := by
  have scan :=
    successRestoreNearest_exact word.reverse [leftGuard] right
      (by
        intro symbol member
        exact ordinary symbol (by simpa using member))
      (by
        intro symbol member
        exact noCountMark symbol (by simpa using member))
  simpa [List.map_reverse, pushCrossed_reverse] using scan

private theorem restorePersistentSymbol_eq_self
    {symbol : WorkSymbol} (notGateMark : symbol ≠ gateMark) :
    restorePersistentSymbol symbol = symbol := by
  simp [restorePersistentSymbol, notGateMark]

private theorem map_restore_eq_self
    (word : List WorkSymbol)
    (noGateMark :
      ∀ symbol, symbol ∈ word → symbol ≠ gateMark) :
    word.map restorePersistentSymbol = word := by
  induction word with
  | nil =>
      rfl
  | cons head rest ih =>
      have headNe := noGateMark head (List.Mem.head rest)
      have restNe :
          ∀ symbol, symbol ∈ rest → symbol ≠ gateMark := by
        intro symbol member
        exact noGateMark symbol (List.Mem.tail head member)
      simp [restorePersistentSymbol_eq_self headNe, ih restNe]

private theorem map_restore_natCells (value : Nat) :
    (natCells value).map restorePersistentSymbol =
      natCells value :=
  map_restore_eq_self (natCells value) (natCells_no_gateMark value)

private theorem map_restore_sourceCells (source : RawSource) :
    (sourceCells source).map restorePersistentSymbol =
      sourceCells source :=
  map_restore_eq_self (sourceCells source)
    (sourceCells_no_gateMark source)

private theorem map_restore_markedGateCells (gate : RawGate) :
    (markedGateCells gate).map restorePersistentSymbol =
      gateCells gate := by
  unfold markedGateCells gateCells
  simp only [SourceParser.markedGateCells,
    SourceParser.gateCells, List.map_append,
    map_restore_sourceCells]
  rfl

private theorem map_restore_markedGateListCells
    (gates : List RawGate) :
    (markedGateListCells gates).map restorePersistentSymbol =
      gateListCells gates := by
  induction gates with
  | nil =>
      rfl
  | cons gate rest ih =>
      unfold markedGateListCells gateListCells
      simp only [SourceParser.markedGateListCells,
        SourceParser.gateListCells, List.map_append,
        map_restore_markedGateCells, ih]

private theorem map_restore_markedCircuitCells (raw : RawCircuit) :
    (markedCircuitCells raw).map restorePersistentSymbol =
      circuitCells raw := by
  unfold markedCircuitCells outputPrefix circuitCells
  simp only [SourceParser.circuitCells,
    List.map_append, List.map_cons, List.map_nil,
    map_restore_natCells, map_restore_markedGateListCells,
    map_restore_sourceCells]
  rfl

private theorem outputPrefix_ordinary
    (inputs : Nat) (gates : List RawGate) :
    ∀ symbol, symbol ∈ outputPrefix inputs gates →
      ordinaryCell symbol := by
  intro symbol member
  unfold outputPrefix at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · simp only [List.mem_cons, List.not_mem_nil] at member
          rcases member with h | h | impossible
          · subst symbol
            exact cell00_ordinary
          · subst symbol
            exact cell00_ordinary
          · contradiction
        · exact natCells_ordinary inputs symbol member
      · exact natCells_ordinary gates.length symbol member
    · exact markedGateListCells_ordinary gates symbol member
  · simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with h | h | impossible
    · subst symbol
      exact cell10_ordinary
    · subst symbol
      exact cell00_ordinary
    · contradiction

private theorem outputPrefix_no_countMark
    (inputs : Nat) (gates : List RawGate) :
    ∀ symbol, symbol ∈ outputPrefix inputs gates →
      symbol ≠ countMark := by
  intro symbol member
  unfold outputPrefix at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · simp only [List.mem_cons, List.not_mem_nil] at member
          rcases member with h | h | impossible
          · subst symbol
            decide
          · subst symbol
            decide
          · contradiction
        · exact natCells_no_countMark inputs symbol member
      · exact natCells_no_countMark gates.length symbol member
    · exact markedGateListCells_no_countMark gates symbol member
  · simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with h | h | impossible
    · subst symbol
      decide
    · subst symbol
      decide
    · contradiction

private theorem markedCircuitCells_ordinary (raw : RawCircuit) :
    ∀ symbol, symbol ∈ markedCircuitCells raw →
      ordinaryCell symbol := by
  intro symbol member
  unfold markedCircuitCells at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact
        outputPrefix_ordinary raw.inputCount raw.gates symbol member
    · exact sourceCells_ordinary raw.output symbol member
  · simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with h | h | h | h | impossible
    · subst symbol
      exact cell10_ordinary
    · subst symbol
      exact cell01_ordinary
    · subst symbol
      exact cell10_ordinary
    · subst symbol
      exact cell11_ordinary
    · contradiction

private theorem markedCircuitCells_no_countMark (raw : RawCircuit) :
    ∀ symbol, symbol ∈ markedCircuitCells raw →
      symbol ≠ countMark := by
  intro symbol member
  unfold markedCircuitCells at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact
        outputPrefix_no_countMark raw.inputCount raw.gates symbol member
    · exact sourceCells_no_countMark raw.output symbol member
  · simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with h | h | h | h | impossible
    · subst symbol
      decide
    · subst symbol
      decide
    · subst symbol
      decide
    · subst symbol
      decide
    · contradiction

set_option maxRecDepth 100000 in
private theorem successRestoreGuard_exact (raw : RawCircuit) :
    workRunExact? machine 1
        (configAtLeftWord State.successRestoreLeft
          [leftGuard] (circuitCells raw ++ [cellBlank])) =
      some
        { state := State.accept
          tape := SourceParser.acceptedTape raw } := by
  cases raw <;> rfl

def finalRestoreSteps (raw : RawCircuit) : Nat :=
  5 + (markedCircuitCells raw).length + 1

/-- Exact final delimiters, leftward anchor restoration, and accepting return to
the first canonical source cell. -/
theorem finalRestore_exact (raw : RawCircuit) :
    workRunExact? machine (finalRestoreSteps raw)
        (guardedConfig State.outputsEndFirst
          (outputPrefix raw.inputCount raw.gates ++
            sourceCells raw.output)
          [cell10, cell01, cell10, cell11]) =
      some
        { state := State.accept
          tape := SourceParser.acceptedTape raw } := by
  let guardedPrefix :=
    outputPrefix raw.inputCount raw.gates ++ sourceCells raw.output
  have delimiters :=
    finalDelimiters_exact guardedPrefix
  have delimitersCanonical :
      workRunExact? machine 5
          (guardedConfig State.outputsEndFirst guardedPrefix
            [cell10, cell01, cell10, cell11]) =
        some
          (configAtLeftWord State.successRestoreLeft
            ((markedCircuitCells raw).reverse ++ [leftGuard])
            [cellBlank]) := by
    simpa [guardedPrefix, markedCircuitCells,
      List.append_assoc] using delimiters
  have restore :=
    successRestoreWord_exact (markedCircuitCells raw)
      [cellBlank] (markedCircuitCells_ordinary raw)
      (markedCircuitCells_no_countMark raw)
  have restoreCanonical :
      workRunExact? machine (markedCircuitCells raw).length
          (configAtLeftWord State.successRestoreLeft
            ((markedCircuitCells raw).reverse ++ [leftGuard])
            [cellBlank]) =
        some
          (configAtLeftWord State.successRestoreLeft
            [leftGuard] (circuitCells raw ++ [cellBlank])) := by
    rw [map_restore_markedCircuitCells] at restore
    exact restore
  have guard := successRestoreGuard_exact raw
  have throughRestore :=
    exactRun_add 5 (markedCircuitCells raw).length
      _ _ _ delimitersCanonical restoreCanonical
  have all :=
    exactRun_add (5 + (markedCircuitCells raw).length) 1
      _ _ _ throughRestore guard
  simpa [finalRestoreSteps, guardedPrefix] using all

/-! ### Canonical endpoint and conservative polynomial envelope -/

def acceptedConfiguration (raw : RawCircuit) : WorkConfiguration :=
  { state := machine.acceptState
    tape := SourceParser.acceptedTape raw }

def circuitAfterHeaderCells (raw : RawCircuit) : List WorkSymbol :=
  gateListCells raw.gates ++
    [cell10, cell00] ++ sourceCells raw.output ++
    [cell10, cell01, cell10, cell11]

private theorem circuitAfterHeaderCells_ne_empty (raw : RawCircuit) :
    circuitAfterHeaderCells raw ≠ [] := by
  simp [circuitAfterHeaderCells]

/-- Literal schedule for the complete grammar-only accepting trace. -/
def canonicalSteps (raw : RawCircuit) : Nat :=
  2 * raw.inputCount + 2 * raw.gates.length + 8 +
    gatesSteps raw.inputCount [] raw.gates +
    programEndSteps raw.inputCount raw.gates +
    (sourceCells raw.output).length +
    finalRestoreSteps raw

/-- Every canonical strict-v0 raw circuit encoding has an exact accepting,
source-preserving execution.  This theorem intentionally has no elaboration or
reference-well-formedness premise. -/
theorem canonical_exact (raw : RawCircuit) :
    workRunExact? machine (canonicalSteps raw)
        (workStartConfiguration machine
          (rawInputWorkTape (encodeCircuit raw))) =
      some (acceptedConfiguration raw) := by
  let afterGates :=
    [cell10, cell00] ++ sourceCells raw.output ++
      [cell10, cell01, cell10, cell11]
  cases cellsEq : circuitAfterHeaderCells raw with
  | nil =>
      exact False.elim (circuitAfterHeaderCells_ne_empty raw cellsEq)
  | cons current rest =>
      have header :=
        canonicalHeader_exact raw.inputCount raw.gates.length
          current rest
      have headerLeftEq :
          pushCrossed
              (gatePrefix raw.inputCount [] raw.gates)
              [leftGuard] =
            pushCrossed (natCells raw.gates.length)
              (pushCrossed (natCells raw.inputCount)
                [cell00, cell00, leftGuard]) := by
        simp only [gatePrefix, SourceParser.gatePrefix,
          SourceParser.markedGateListCells,
          List.append_nil]
        repeat rw [pushCrossed_append]
        rfl
      have headerCanonical :
          workRunExact? machine
              (2 * raw.inputCount + 2 * raw.gates.length + 8)
              (workStartConfiguration machine
                (rawInputWorkTape (encodeCircuit raw))) =
            some
              (guardedConfig State.gateStart
                (gatePrefix raw.inputCount [] raw.gates)
                (gateListCells raw.gates ++ afterGates)) := by
        rw [← cellsEq] at header
        rw [SourceParser.rawInputWorkTape_encodeCircuit]
        unfold guardedConfig
        rw [headerLeftEq]
        simpa [circuitCells, SourceParser.circuitCells,
          circuitAfterHeaderCells, afterGates,
          gatePrefix, SourceParser.gatePrefix,
          countCells, SourceParser.countCells,
          markedGateListCells, SourceParser.markedGateListCells,
          gateListCells, sourceCells,
          pushCrossed_append, List.append_assoc,
          cell00, cell01, cell10, cell11,
          SourceParser.cell00, SourceParser.cell01,
          SourceParser.cell10, SourceParser.cell11] using header
      have gates :=
        gates_exact raw.inputCount [] raw.gates afterGates
      have gatesCanonical :
          workRunExact? machine
              (gatesSteps raw.inputCount [] raw.gates)
              (guardedConfig State.gateStart
                (gatePrefix raw.inputCount [] raw.gates)
                (gateListCells raw.gates ++ afterGates)) =
            some
              (guardedConfig State.gateStart
                (gatePrefix raw.inputCount raw.gates [])
                afterGates) := by
        simpa using gates
      have program :=
        programEnd_exact raw.inputCount raw.gates
          (sourceCells raw.output ++
            [cell10, cell01, cell10, cell11])
      have programCanonical :
          workRunExact? machine
              (programEndSteps raw.inputCount raw.gates)
              (guardedConfig State.gateStart
                (gatePrefix raw.inputCount raw.gates [])
                afterGates) =
            some
              (guardedConfig (State.sourceStart .output)
                (outputPrefix raw.inputCount raw.gates)
                (sourceCells raw.output ++
                  [cell10, cell01, cell10, cell11])) := by
        simpa [afterGates, List.append_assoc] using program
      have output :=
        sourceGuarded_exact .output raw.output
          (outputPrefix raw.inputCount raw.gates)
          [cell10, cell01, cell10, cell11]
      have restore := finalRestore_exact raw
      have throughGates :=
        exactRun_add
          (2 * raw.inputCount + 2 * raw.gates.length + 8)
          (gatesSteps raw.inputCount [] raw.gates)
          _ _ _ headerCanonical gatesCanonical
      have throughProgram :=
        exactRun_add
          ((2 * raw.inputCount + 2 * raw.gates.length + 8) +
            gatesSteps raw.inputCount [] raw.gates)
          (programEndSteps raw.inputCount raw.gates)
          _ _ _ throughGates programCanonical
      have throughOutput :=
        exactRun_add
          (((2 * raw.inputCount + 2 * raw.gates.length + 8) +
            gatesSteps raw.inputCount [] raw.gates) +
            programEndSteps raw.inputCount raw.gates)
          (sourceCells raw.output).length
          _ _ _ throughProgram output
      have all :=
        exactRun_add
          ((((2 * raw.inputCount + 2 * raw.gates.length + 8) +
            gatesSteps raw.inputCount [] raw.gates) +
            programEndSteps raw.inputCount raw.gates) +
            (sourceCells raw.output).length)
          (finalRestoreSteps raw)
          _ _ _ throughOutput restore
      simpa [canonicalSteps, acceptedConfiguration,
        machine] using all

/-- Successful strict-v0 decoding is sufficient to launch the same exact
grammar-only execution from the caller's original bitstring. -/
theorem decoded_exact
    (bits : BitString) (raw : RawCircuit)
    (decoded : decodeCircuit bits = some raw) :
    workRunExact? machine (canonicalSteps raw)
        (workStartConfiguration machine (rawInputWorkTape bits)) =
      some (acceptedConfiguration raw) := by
  have encoded :=
    PNP.Concrete.LockedNAND.encodeCircuit_eq_of_decodeCircuit_eq_some
      bits raw decoded
  rw [← encoded]
  exact canonical_exact raw

theorem acceptedConfiguration_state (raw : RawCircuit) :
    (acceptedConfiguration raw).state = machine.acceptState := by
  rfl

theorem acceptedConfiguration_isHalted (raw : RawCircuit) :
    machine.isHalted (acceptedConfiguration raw) = true := by
  rfl

theorem acceptedConfiguration_outputBits (raw : RawCircuit) :
    (encodeWorkTape (acceptedConfiguration raw).tape).outputBits =
      encodeCircuit raw := by
  exact SourceParser.acceptedTape_outputBits raw

/-- Small canonical regression with no gate records and a constant output. -/
def zeroGateConstantFalse : RawCircuit :=
  { inputCount := 0
    gates := []
    output := .constant false }

/-- A grammar-canonical circuit deliberately containing out-of-range input,
prior-gate, and output references.  It must be accepted by this scanner even
though intrinsic elaboration fails. -/
def decodedInvalidReferenceCircuit : RawCircuit :=
  { inputCount := 0
    gates :=
      [{ left := .input 7
         right := .gate 5 }]
    output := .gate 9 }

theorem decodedInvalidReferenceCircuit_unelaboratable :
    decodedInvalidReferenceCircuit.elaborate = none := by
  rfl

theorem zeroGateConstantFalse_exact :
    workRunExact? machine 48
        (workStartConfiguration machine
          (rawInputWorkTape
            (encodeCircuit zeroGateConstantFalse))) =
      some (acceptedConfiguration zeroGateConstantFalse) := by
  set_option maxRecDepth 100000 in
    rfl

/-- Concrete operational witness that the scanner recognizes grammar rather
than intrinsic reference validity.  The source word is restored exactly. -/
theorem decodedInvalidReferenceCircuit_exact :
    workRunExact? machine 250
        (workStartConfiguration machine
          (rawInputWorkTape
            (encodeCircuit decodedInvalidReferenceCircuit))) =
      some
        (acceptedConfiguration decodedInvalidReferenceCircuit) := by
  set_option maxRecDepth 100000 in
    rfl

/-! ### Total cleanup for malformed grammar words

The scanner deliberately shares the parser's cleanup-state numbers and tape
layout, but the execution below is proved for this scanner's literal
`machine`.  No trace is transported from the stricter source parser. -/

private def cleanupSeekConfiguration
    (outsideLeft scan right : List WorkSymbol) :
    WorkConfiguration :=
  match scan with
  | [] =>
      { state := State.cleanupSeekGuard
        tape :=
          { left := outsideLeft
            head := leftGuard
            right := right } }
  | symbol :: rest =>
      { state := State.cleanupSeekGuard
        tape :=
          { left := rest ++ leftGuard :: outsideLeft
            head := symbol
            right := right } }

private def cleanupRightConfiguration
    (left word suffix : List WorkSymbol) :
    WorkConfiguration :=
  match word with
  | [] =>
      { state := State.cleanupRight
        tape :=
          { left := left
            head := cellBlank
            right := suffix } }
  | symbol :: rest =>
      { state := State.cleanupRight
        tape :=
          { left := left
            head := symbol
            right := rest ++ cellBlank :: suffix } }

private def cleanupRightFiniteConfiguration
    (left word : List WorkSymbol) : WorkConfiguration :=
  match word with
  | [] =>
      { state := State.cleanupRight
        tape :=
          { left := left
            head := cellBlank
            right := [] } }
  | symbol :: rest =>
      { state := State.cleanupRight
        tape :=
          { left := left
            head := symbol
            right := rest } }

private abbrev pushCleanupScan :=
  SourceParser.pushCleanupScan

private abbrev pushCleanupBlanks :=
  SourceParser.pushCleanupBlanks

private abbrev guardedCleanupSteps :=
  SourceParser.guardedCleanupSteps

private abbrev guardedCleanupExplicitSteps :=
  SourceParser.guardedCleanupExplicitSteps

private def cleanupRejectConfiguration
    (outsideLeft leftScan rightWord suffix : List WorkSymbol) :
    WorkConfiguration :=
  { state := State.reject
    tape :=
      { left :=
          pushCleanupBlanks
            (pushCleanupScan leftScan rightWord)
            (cellBlank :: outsideLeft)
        head := cellBlank
        right := suffix } }

private def cleanupExplicitRejectConfiguration
    (outsideLeft eraseWord suffix : List WorkSymbol) :
    WorkConfiguration :=
  { state := State.reject
    tape :=
      { left :=
          pushCleanupBlanks eraseWord
            (cellBlank :: outsideLeft)
        head := cellBlank
        right := suffix } }

private theorem workSymbol_beq_false_of_ne
    (first second : WorkSymbol) (different : first ≠ second) :
    (first == second) = false := by
  rcases first with ⟨firstLeft, firstRight⟩
  rcases second with ⟨secondLeft, secondRight⟩
  cases firstLeft <;> cases firstRight <;>
    cases secondLeft <;> cases secondRight <;>
    first | rfl | exact False.elim (different rfl)

private theorem cleanupSeekGuard_workStep (tape : WorkTape) :
    workStep? machine
        ({ state := State.cleanupSeekGuard, tape := tape } :
          WorkConfiguration) =
      if tape.head == leftGuard then
        some
          { state := State.cleanupRight
            tape := (tape.write cellBlank).move .right }
      else
        some
          { state := State.cleanupSeekGuard
            tape := tape.move .left } := by
  set_option maxRecDepth 100000 in
    rcases tape with ⟨left, ⟨first, second⟩, right⟩
    cases first <;> cases second <;> rfl

private theorem cleanupRight_workStep (tape : WorkTape) :
    workStep? machine
        ({ state := State.cleanupRight, tape := tape } :
          WorkConfiguration) =
      if tape.head == cellBlank then
        some
          { state := State.reject
            tape := tape }
      else
        some
          { state := State.cleanupRight
            tape := (tape.write cellBlank).move .right } := by
  set_option maxRecDepth 100000 in
    rcases tape with ⟨left, ⟨first, second⟩, right⟩
    cases first <;> cases second <;> rfl

private theorem cleanupSeekConfiguration_step
    (outsideLeft : List WorkSymbol) (symbol : WorkSymbol)
    (rest right : List WorkSymbol)
    (notGuard : symbol ≠ leftGuard) :
    workStep? machine
        (cleanupSeekConfiguration outsideLeft
          (symbol :: rest) right) =
      some
        (cleanupSeekConfiguration outsideLeft rest
          (symbol :: right)) := by
  unfold cleanupSeekConfiguration
  have compared :
      (symbol == leftGuard) = false :=
    workSymbol_beq_false_of_ne symbol leftGuard notGuard
  have transition :=
    cleanupSeekGuard_workStep
      ({ left := rest ++ leftGuard :: outsideLeft
         head := symbol
         right := right } : WorkTape)
  rw [transition, compared]
  cases rest <;> rfl

private theorem cleanupSeekGuard_exact
    (outsideLeft scan right : List WorkSymbol)
    (noInnerGuard :
      ∀ symbol, symbol ∈ scan → symbol ≠ leftGuard) :
    workRunExact? machine scan.length
        (cleanupSeekConfiguration outsideLeft scan right) =
      some
        (cleanupSeekConfiguration outsideLeft []
          (pushCleanupScan scan right)) := by
  induction scan generalizing right with
  | nil =>
      rfl
  | cons symbol rest ih =>
      have headNotGuard :
          symbol ≠ leftGuard :=
        noInnerGuard symbol (List.Mem.head rest)
      have restNoGuard :
          ∀ found, found ∈ rest → found ≠ leftGuard := by
        intro found member
        exact noInnerGuard found (List.Mem.tail symbol member)
      change
        (match workStep? machine
            (cleanupSeekConfiguration outsideLeft
              (symbol :: rest) right) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (cleanupSeekConfiguration outsideLeft []
              (pushCleanupScan (symbol :: rest) right))
      rw [cleanupSeekConfiguration_step outsideLeft symbol rest right
        headNotGuard]
      exact ih (symbol :: right) restNoGuard

private theorem cleanupRightConfiguration_step
    (left : List WorkSymbol) (symbol : WorkSymbol)
    (rest suffix : List WorkSymbol)
    (notBlank : symbol ≠ cellBlank) :
    workStep? machine
        (cleanupRightConfiguration left
          (symbol :: rest) suffix) =
      some
        (cleanupRightConfiguration (cellBlank :: left)
          rest suffix) := by
  unfold cleanupRightConfiguration
  have compared :
      (symbol == cellBlank) = false :=
    workSymbol_beq_false_of_ne symbol cellBlank notBlank
  have transition :=
    cleanupRight_workStep
      ({ left := left
         head := symbol
         right := rest ++ cellBlank :: suffix } : WorkTape)
  rw [transition, compared]
  cases rest <;> rfl

private theorem cleanupRight_erase_exact
    (left word suffix : List WorkSymbol)
    (nonblank :
      ∀ symbol, symbol ∈ word → symbol ≠ cellBlank) :
    workRunExact? machine word.length
        (cleanupRightConfiguration left word suffix) =
      some
        (cleanupRightConfiguration
          (pushCleanupBlanks word left) [] suffix) := by
  induction word generalizing left with
  | nil =>
      rfl
  | cons symbol rest ih =>
      have headNotBlank :
          symbol ≠ cellBlank :=
        nonblank symbol (List.Mem.head rest)
      have restNonblank :
          ∀ found, found ∈ rest → found ≠ cellBlank := by
        intro found member
        exact nonblank found (List.Mem.tail symbol member)
      change
        (match workStep? machine
            (cleanupRightConfiguration left
              (symbol :: rest) suffix) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (cleanupRightConfiguration
              (pushCleanupBlanks (symbol :: rest) left)
              [] suffix)
      rw [cleanupRightConfiguration_step left symbol rest suffix
        headNotBlank]
      exact ih (cellBlank :: left) restNonblank

private theorem cleanupRight_reject_exact
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (cleanupRightConfiguration left [] suffix) =
      some
        { state := State.reject
          tape :=
            { left := left
              head := cellBlank
              right := suffix } } := by
  unfold cleanupRightConfiguration
  change
    (match workStep? machine
        ({ state := State.cleanupRight
           tape :=
             { left := left
               head := cellBlank
               right := suffix } } : WorkConfiguration) with
     | none => none
     | some next => some next) =
      some
        { state := State.reject
          tape :=
            { left := left
              head := cellBlank
              right := suffix } }
  rw [cleanupRight_workStep]
  rfl

private theorem cleanupRight_exact
    (left word suffix : List WorkSymbol)
    (nonblank :
      ∀ symbol, symbol ∈ word → symbol ≠ cellBlank) :
    workRunExact? machine (word.length + 1)
        (cleanupRightConfiguration left word suffix) =
      some
        { state := State.reject
          tape :=
            { left := pushCleanupBlanks word left
              head := cellBlank
              right := suffix } } := by
  exact exactRun_add word.length 1
    (cleanupRightConfiguration left word suffix)
    (cleanupRightConfiguration
      (pushCleanupBlanks word left) [] suffix)
    { state := State.reject
      tape :=
        { left := pushCleanupBlanks word left
          head := cellBlank
          right := suffix } }
    (cleanupRight_erase_exact left word suffix nonblank)
    (cleanupRight_reject_exact
      (pushCleanupBlanks word left) suffix)

private theorem cleanupRightFiniteConfiguration_step
    (left : List WorkSymbol) (symbol : WorkSymbol)
    (rest : List WorkSymbol)
    (notBlank : symbol ≠ cellBlank) :
    workStep? machine
        (cleanupRightFiniteConfiguration left
          (symbol :: rest)) =
      some
        (cleanupRightFiniteConfiguration
          (cellBlank :: left) rest) := by
  unfold cleanupRightFiniteConfiguration
  have compared :
      (symbol == cellBlank) = false :=
    workSymbol_beq_false_of_ne symbol cellBlank notBlank
  have transition :=
    cleanupRight_workStep
      ({ left := left
         head := symbol
         right := rest } : WorkTape)
  rw [transition, compared]
  cases rest <;> rfl

private theorem cleanupRightFinite_erase_exact
    (left word : List WorkSymbol)
    (nonblank :
      ∀ symbol, symbol ∈ word → symbol ≠ cellBlank) :
    workRunExact? machine word.length
        (cleanupRightFiniteConfiguration left word) =
      some
        (cleanupRightFiniteConfiguration
          (pushCleanupBlanks word left) []) := by
  induction word generalizing left with
  | nil =>
      rfl
  | cons symbol rest ih =>
      have headNotBlank :
          symbol ≠ cellBlank :=
        nonblank symbol (List.Mem.head rest)
      have restNonblank :
          ∀ found, found ∈ rest → found ≠ cellBlank := by
        intro found member
        exact nonblank found (List.Mem.tail symbol member)
      change
        (match workStep? machine
            (cleanupRightFiniteConfiguration left
              (symbol :: rest)) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (cleanupRightFiniteConfiguration
              (pushCleanupBlanks (symbol :: rest) left) [])
      rw [cleanupRightFiniteConfiguration_step
        left symbol rest headNotBlank]
      exact ih (cellBlank :: left) restNonblank

private theorem cleanupRightFinite_exact
    (left word : List WorkSymbol)
    (nonblank :
      ∀ symbol, symbol ∈ word → symbol ≠ cellBlank) :
    workRunExact? machine (word.length + 1)
        (cleanupRightFiniteConfiguration left word) =
      some
        { state := State.reject
          tape :=
            { left := pushCleanupBlanks word left
              head := cellBlank
              right := [] } } := by
  exact exactRun_add word.length 1
    (cleanupRightFiniteConfiguration left word)
    (cleanupRightFiniteConfiguration
      (pushCleanupBlanks word left) [])
    { state := State.reject
      tape :=
        { left := pushCleanupBlanks word left
          head := cellBlank
          right := [] } }
    (cleanupRightFinite_erase_exact left word nonblank)
    (by
      change
        workRunExact? machine 1
            (cleanupRightConfiguration
              (pushCleanupBlanks word left) [] []) =
          some
            { state := State.reject
              tape :=
                { left := pushCleanupBlanks word left
                  head := cellBlank
                  right := [] } }
      exact cleanupRight_reject_exact
        (pushCleanupBlanks word left) [])

private theorem guardedCleanupFinite_exact
    (outsideLeft leftScan rightWord : List WorkSymbol)
    (noInnerGuard :
      ∀ symbol, symbol ∈ leftScan → symbol ≠ leftGuard)
    (nonblank :
      ∀ symbol,
        symbol ∈ pushCleanupScan leftScan rightWord →
          symbol ≠ cellBlank) :
    workRunExact? machine
        (guardedCleanupSteps leftScan rightWord)
        (cleanupSeekConfiguration
          outsideLeft leftScan rightWord) =
      some
        (cleanupRejectConfiguration
          outsideLeft leftScan rightWord []) := by
  let forwardWord := pushCleanupScan leftScan rightWord
  let atGuard :=
    cleanupSeekConfiguration outsideLeft [] forwardWord
  let atErase :=
    cleanupRightFiniteConfiguration
      (cellBlank :: outsideLeft) forwardWord
  have seek :
      workRunExact? machine leftScan.length
          (cleanupSeekConfiguration
            outsideLeft leftScan rightWord) =
        some atGuard := by
    exact cleanupSeekGuard_exact
      outsideLeft leftScan rightWord noInnerGuard
  have crossGuard :
      workRunExact? machine 1 atGuard = some atErase := by
    dsimp [atGuard, atErase, forwardWord]
    change
      (match workStep? machine
          ({ state := State.cleanupSeekGuard
             tape :=
               { left := outsideLeft
                 head := leftGuard
                 right :=
                   pushCleanupScan leftScan rightWord } } :
            WorkConfiguration) with
       | none => none
       | some next => some next) =
        some
          (cleanupRightFiniteConfiguration
            (cellBlank :: outsideLeft)
            (pushCleanupScan leftScan rightWord))
    rw [cleanupSeekGuard_workStep]
    cases wordEq : pushCleanupScan leftScan rightWord <;> rfl
  have erase :
      workRunExact? machine (forwardWord.length + 1)
          atErase =
        some
          (cleanupRejectConfiguration
            outsideLeft leftScan rightWord []) := by
    dsimp [atErase, forwardWord]
    exact cleanupRightFinite_exact
      (cellBlank :: outsideLeft)
      (pushCleanupScan leftScan rightWord) nonblank
  have throughGuard := exactRun_add leftScan.length 1
    (cleanupSeekConfiguration outsideLeft leftScan rightWord)
    atGuard atErase seek crossGuard
  have complete := exactRun_add (leftScan.length + 1)
    (forwardWord.length + 1)
    (cleanupSeekConfiguration outsideLeft leftScan rightWord)
    atErase
    (cleanupRejectConfiguration
      outsideLeft leftScan rightWord [])
    throughGuard erase
  simpa [guardedCleanupSteps,
    SourceParser.guardedCleanupSteps, forwardWord,
    Nat.add_assoc] using complete

private theorem guardedCleanupExplicit_exact
    (outsideLeft leftScan right eraseWord suffix :
      List WorkSymbol)
    (noInnerGuard :
      ∀ symbol, symbol ∈ leftScan → symbol ≠ leftGuard)
    (forwardShape :
      pushCleanupScan leftScan right =
        eraseWord ++ cellBlank :: suffix)
    (nonblank :
      ∀ symbol, symbol ∈ eraseWord →
        symbol ≠ cellBlank) :
    workRunExact? machine
        (guardedCleanupExplicitSteps leftScan eraseWord)
        (cleanupSeekConfiguration
          outsideLeft leftScan right) =
      some
        (cleanupExplicitRejectConfiguration
          outsideLeft eraseWord suffix) := by
  let atGuard :=
    cleanupSeekConfiguration outsideLeft []
      (eraseWord ++ cellBlank :: suffix)
  let atErase :=
    cleanupRightConfiguration
      (cellBlank :: outsideLeft) eraseWord suffix
  have seek :
      workRunExact? machine leftScan.length
          (cleanupSeekConfiguration
            outsideLeft leftScan right) =
        some atGuard := by
    have run := cleanupSeekGuard_exact
      outsideLeft leftScan right noInnerGuard
    rw [forwardShape] at run
    exact run
  have crossGuard :
      workRunExact? machine 1 atGuard = some atErase := by
    dsimp [atGuard, atErase]
    change
      (match workStep? machine
          ({ state := State.cleanupSeekGuard
             tape :=
               { left := outsideLeft
                 head := leftGuard
                 right :=
                   eraseWord ++ cellBlank :: suffix } } :
            WorkConfiguration) with
       | none => none
       | some next => some next) =
        some
          (cleanupRightConfiguration
            (cellBlank :: outsideLeft) eraseWord suffix)
    rw [cleanupSeekGuard_workStep]
    cases eraseWord <;> rfl
  have erase :
      workRunExact? machine (eraseWord.length + 1)
          atErase =
        some
          (cleanupExplicitRejectConfiguration
            outsideLeft eraseWord suffix) := by
    dsimp [atErase]
    exact cleanupRight_exact
      (cellBlank :: outsideLeft)
      eraseWord suffix nonblank
  have throughGuard := exactRun_add leftScan.length 1
    (cleanupSeekConfiguration outsideLeft leftScan right)
    atGuard atErase seek crossGuard
  have complete := exactRun_add (leftScan.length + 1)
    (eraseWord.length + 1)
    (cleanupSeekConfiguration outsideLeft leftScan right)
    atErase
    (cleanupExplicitRejectConfiguration
      outsideLeft eraseWord suffix)
    throughGuard erase
  simpa [guardedCleanupExplicitSteps,
    SourceParser.guardedCleanupExplicitSteps,
    Nat.add_assoc] using complete

private theorem cleanupReject_output_empty
    (outsideLeft leftScan rightWord : List WorkSymbol) :
    (encodeWorkTape
      (cleanupRejectConfiguration
        outsideLeft leftScan rightWord []).tape).outputBits = [] := by
  rfl

private theorem cleanupExplicitReject_output_empty
    (outsideLeft eraseWord : List WorkSymbol) :
    (encodeWorkTape
      (cleanupExplicitRejectConfiguration
        outsideLeft eraseWord []).tape).outputBits = [] := by
  rfl

private theorem cleanupReject_isHalted
    (outsideLeft leftScan rightWord suffix : List WorkSymbol) :
    machine.isHalted
      (cleanupRejectConfiguration
        outsideLeft leftScan rightWord suffix) = true := by
  rfl

private theorem cleanupExplicitReject_isHalted
    (outsideLeft eraseWord suffix : List WorkSymbol) :
    machine.isHalted
      (cleanupExplicitRejectConfiguration
        outsideLeft eraseWord suffix) = true := by
  rfl

private def SafeSourceWord (word : List WorkSymbol) : Prop :=
  ∀ symbol, symbol ∈ word →
    symbol ≠ leftGuard ∧ symbol ≠ cellBlank

private theorem sourcePackedCell_safe
    {symbol : WorkSymbol}
    (packed : SourceParser.SourcePackedCell symbol) :
    symbol ≠ leftGuard ∧ symbol ≠ cellBlank := by
  rcases packed with h | h | h | h | h | h <;>
    subst symbol <;> decide

private theorem packedTokenCells_safe (tokens : List Token) :
    SafeSourceWord (SourceParser.packedTokenCells tokens) := by
  intro symbol member
  apply sourcePackedCell_safe
  apply SourceParser.packedRawBits_allSourcePacked
    (encodeTokens tokens) symbol
  change
    symbol ∈
      packWorkSymbols
        ((encodeTokens tokens).map TapeSymbol.ofBool)
  rw [SourceParser.pack_encodeTokens]
  exact member

private theorem malformedWorkTail_safe
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed : SourceParser.MalformedWorkTail rawTail workTail) :
    SafeSourceWord workTail := by
  intro symbol member
  exact sourcePackedCell_safe
    (malformed.allSourcePacked symbol member)

private theorem safe_append
    {first second : List WorkSymbol}
    (firstSafe : SafeSourceWord first)
    (secondSafe : SafeSourceWord second) :
    SafeSourceWord (first ++ second) := by
  intro symbol member
  rcases List.mem_append.mp member with member | member
  · exact firstSafe symbol member
  · exact secondSafe symbol member

private theorem pushCleanupScan_pushCrossed
    (word accumulator right : List WorkSymbol) :
    pushCleanupScan (pushCrossed word accumulator) right =
      pushCleanupScan accumulator (word ++ right) := by
  induction word generalizing accumulator with
  | nil =>
      rfl
  | cons symbol rest ih =>
      change
        pushCleanupScan
            (pushCrossed rest (symbol :: accumulator)) right =
          pushCleanupScan accumulator
            (symbol :: (rest ++ right))
      simpa [pushCleanupScan, SourceParser.pushCleanupScan] using
        ih (symbol :: accumulator)

private theorem pushCleanupScan_mem_iff
    (scan right : List WorkSymbol) (symbol : WorkSymbol) :
    symbol ∈ pushCleanupScan scan right ↔
      symbol ∈ scan ∨ symbol ∈ right := by
  induction scan generalizing right with
  | nil =>
      simp [pushCleanupScan, SourceParser.pushCleanupScan]
  | cons head rest ih =>
      change
        symbol ∈ pushCleanupScan rest (head :: right) ↔
          symbol ∈ head :: rest ∨ symbol ∈ right
      rw [ih]
      simp [or_assoc, or_left_comm]

private theorem explicitFailureForward_eq
    (parsedPrefix : List WorkSymbol) (current : WorkSymbol)
    (rest : List WorkSymbol) :
    pushCleanupScan
        (current :: pushCrossed parsedPrefix []) rest =
      parsedPrefix ++ current :: rest := by
  rw [pushCleanupScan, SourceParser.pushCleanupScan]
  exact pushCleanupScan_pushCrossed
    parsedPrefix [] (current :: rest)

private theorem safeExplicitFailure_exact
    (word parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (initial : WorkConfiguration) (launchSteps : Nat)
    (shape : word = parsedPrefix ++ current :: rest)
    (safe : SafeSourceWord word)
    (launch :
      workRunExact? machine launchSteps initial =
        some
          (cleanupSeekConfiguration
            [] (current :: pushCrossed parsedPrefix []) rest)) :
    ∃ steps final,
      workRunExact? machine steps initial = some final ∧
      machine.isHalted final = true ∧
      final.state = State.reject ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  let scan := current :: pushCrossed parsedPrefix []
  have forwardEq :
      pushCleanupScan scan rest = word := by
    dsimp [scan]
    rw [explicitFailureForward_eq, ← shape]
  have noGuard :
      ∀ symbol, symbol ∈ scan →
        symbol ≠ leftGuard := by
    intro symbol member
    exact
      (safe symbol
        (by
          rw [← forwardEq]
          exact
            (pushCleanupScan_mem_iff
              scan rest symbol).mpr (Or.inl member))).1
  have nonblank :
      ∀ symbol,
        symbol ∈ pushCleanupScan scan rest →
          symbol ≠ cellBlank := by
    intro symbol member
    exact (safe symbol (by rwa [forwardEq] at member)).2
  have cleanup :=
    guardedCleanupFinite_exact
      [] scan rest noGuard nonblank
  let steps :=
    launchSteps + guardedCleanupSteps scan rest
  let final :=
    cleanupRejectConfiguration [] scan rest []
  refine ⟨steps, final, ?_, ?_, rfl, ?_⟩
  · exact exactRun_add launchSteps
      (guardedCleanupSteps scan rest)
      _ _ _ launch cleanup
  · exact cleanupReject_isHalted [] scan rest []
  · exact cleanupReject_output_empty [] scan rest

private def missingEndScan
    (crossed : List WorkSymbol) : List WorkSymbol :=
  cellBlank :: crossed

private def missingEndEraseWord
    (crossed : List WorkSymbol) : List WorkSymbol :=
  pushCleanupScan crossed []

private def missingEndTailSteps
    (crossed : List WorkSymbol) : Nat :=
  1 + guardedCleanupExplicitSteps
    (missingEndScan crossed)
    (missingEndEraseWord crossed)

private theorem missingEndTail_exact
    (state : Nat) (prefixCells crossed : List WorkSymbol)
    (crossedEq : crossed = pushCrossed prefixCells [])
    (safe : SafeSourceWord prefixCells)
    (failure :
      workRunExact? machine 1
          (configAtWord state
            (crossed ++ [leftGuard]) []) =
        some
          (cleanupSeekConfiguration
            [] (missingEndScan crossed) [])) :
    workRunExact? machine
        (missingEndTailSteps crossed)
        (configAtWord state
          (crossed ++ [leftGuard]) []) =
      some
        (cleanupExplicitRejectConfiguration
          [] (missingEndEraseWord crossed) []) := by
  have scanNoGuard :
      ∀ symbol, symbol ∈ missingEndScan crossed →
        symbol ≠ leftGuard := by
    intro symbol member
    simp only [missingEndScan, List.mem_cons] at member
    rcases member with blankEq | crossedMember
    · subst symbol
      decide
    · rw [crossedEq] at crossedMember
      rw [pushCrossed_eq_reverse_append] at crossedMember
      have member' :
          symbol ∈ prefixCells.reverse := by
        simpa using crossedMember
      exact
        (safe symbol (by simpa using member')).1
  have eraseNonblank :
      ∀ symbol,
        symbol ∈ missingEndEraseWord crossed →
          symbol ≠ cellBlank := by
    intro symbol member
    unfold missingEndEraseWord at member
    have materialized :
        pushCleanupScan (pushCrossed prefixCells []) [] =
          prefixCells := by
      simpa [pushCleanupScan, SourceParser.pushCleanupScan] using
        (pushCleanupScan_pushCrossed prefixCells [] [])
    rw [crossedEq, materialized] at member
    exact (safe symbol member).2
  have forwardShape :
      pushCleanupScan (missingEndScan crossed) [] =
        missingEndEraseWord crossed ++ cellBlank :: [] := by
    unfold missingEndScan missingEndEraseWord
    rw [pushCleanupScan, SourceParser.pushCleanupScan]
    simpa using
      (SourceParser.pushCleanupScan_append crossed []
        [cellBlank])
  have cleanup :=
    guardedCleanupExplicit_exact
      [] (missingEndScan crossed) []
      (missingEndEraseWord crossed) []
      scanNoGuard forwardShape eraseNonblank
  unfold missingEndTailSteps
  exact exactRun_add 1
    (guardedCleanupExplicitSteps
      (missingEndScan crossed)
      (missingEndEraseWord crossed))
    _ _ _ failure cleanup

private theorem packedTokenCells_append
    (first second : List Token) :
    SourceParser.packedTokenCells (first ++ second) =
      SourceParser.packedTokenCells first ++
        SourceParser.packedTokenCells second := by
  induction first with
  | nil =>
      rfl
  | cons token rest ih =>
      change
        SourceParser.tokenCells token ++
            SourceParser.packedTokenCells (rest ++ second) =
          (SourceParser.tokenCells token ++
              SourceParser.packedTokenCells rest) ++
            SourceParser.packedTokenCells second
      rw [ih, List.append_assoc]

private def unaryUnitCells : Nat → List WorkSymbol
  | 0 => []
  | units + 1 => cell00 :: cell01 :: unaryUnitCells units

private theorem packedTokenCells_replicate_unit (units : Nat) :
    SourceParser.packedTokenCells
        (List.replicate units Token.unit) =
      unaryUnitCells units := by
  induction units with
  | zero =>
      rfl
  | succ units ih =>
      rw [List.replicate_succ]
      change
        cell00 :: cell01 ::
            SourceParser.packedTokenCells
              (List.replicate units Token.unit) =
          cell00 :: cell01 :: unaryUnitCells units
      rw [ih]

private theorem unaryUnitCells_safe (units : Nat) :
    SafeSourceWord (unaryUnitCells units) := by
  intro symbol member
  induction units with
  | zero =>
      contradiction
  | succ units ih =>
      simp only [unaryUnitCells, List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact ih member

private inductive NatReader where
  | inputCount
  | gateCount
  | source (continuation : SourceContinuation)

private def NatReader.state : NatReader → Nat
  | .inputCount => State.inputCountFirst
  | .gateCount => State.gateCountFirst
  | .source continuation => State.sourceNatFirst continuation

set_option maxRecDepth 100000 in
private theorem natReaderUnit_exact
    (reader : NatReader) (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord reader.state left
          (cell00 :: cell01 :: rest)) =
      some
        (configAtWord reader.state
          (cell01 :: cell00 :: left) rest) := by
  cases reader with
  | inputCount => rfl
  | gateCount => rfl
  | source continuation =>
      cases continuation <;> rfl

private theorem natReaderUnits_exact
    (reader : NatReader) (units : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * units)
        (configAtWord reader.state left
          (unaryUnitCells units ++ suffix)) =
      some
        (configAtWord reader.state
          (pushCrossed (unaryUnitCells units) left)
          suffix) := by
  induction units generalizing left with
  | zero =>
      rfl
  | succ units ih =>
      have first :=
        natReaderUnit_exact reader left
          (unaryUnitCells units ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * units) _ _ _ first tail
      have stepsEq : 2 + 2 * units = 2 * (units + 1) := by
        omega
      rw [stepsEq] at all
      simpa [unaryUnitCells, pushCrossed] using all

private theorem natReaderFirstFailure_exact
    (reader : NatReader) (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (wrong : current ≠ cell00) :
    workRunExact? machine 1
        (guardedConfig reader.state parsedPrefix
          (current :: rest)) =
      some
        (cleanupSeekConfiguration
          [] (current :: pushCrossed parsedPrefix []) rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  rw [pushCrossed_eq_reverse_append,
    pushCrossed_eq_reverse_append]
  simp only [List.append_nil]
  set_option maxRecDepth 100000 in
    cases reader with
    | inputCount =>
        simp only [NatReader.state]
        simp only [cell00, WorkSymbol.zeroZero] at wrong
        rcases current with ⟨first, second⟩
        cases first <;> cases second <;> try rfl
        exact False.elim (wrong rfl)
    | gateCount =>
        simp only [NatReader.state]
        simp only [cell00, WorkSymbol.zeroZero] at wrong
        rcases current with ⟨first, second⟩
        cases first <;> cases second <;>
          first | rfl | exact False.elim (wrong rfl)
    | source continuation =>
        simp only [NatReader.state]
        simp only [cell00, WorkSymbol.zeroZero] at wrong
        cases continuation <;>
          rcases current with ⟨first, second⟩ <;>
          cases first <;> cases second <;>
          first | rfl | exact False.elim (wrong rfl)

private theorem natReaderSecondFailure_exact
    (reader : NatReader) (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (notUnit : current ≠ cell01)
    (notEnd : current ≠ cell10) :
    workRunExact? machine 2
        (guardedConfig reader.state parsedPrefix
          (cell00 :: current :: rest)) =
      some
        (cleanupSeekConfiguration
          []
          (current ::
            pushCrossed (parsedPrefix ++ [cell00]) [])
          rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_nil,
    List.cons_append]
  set_option maxRecDepth 100000 in
    cases reader with
    | inputCount =>
        simp only [NatReader.state]
        simp only [cell01, cell10, WorkSymbol.zeroOne,
          WorkSymbol.oneZero] at notUnit notEnd
        rcases current with ⟨first, second⟩
        cases first <;> cases second <;>
          first
          | rfl
          | exact False.elim (notUnit rfl)
          | exact False.elim (notEnd rfl)
    | gateCount =>
        simp only [NatReader.state]
        simp only [cell01, cell10, WorkSymbol.zeroOne,
          WorkSymbol.oneZero] at notUnit notEnd
        rcases current with ⟨first, second⟩
        cases first <;> cases second <;>
          first
          | rfl
          | exact False.elim (notUnit rfl)
          | exact False.elim (notEnd rfl)
    | source continuation =>
        simp only [NatReader.state]
        simp only [cell01, cell10, WorkSymbol.zeroOne,
          WorkSymbol.oneZero] at notUnit notEnd
        cases continuation <;>
          rcases current with ⟨first, second⟩ <;>
          cases first <;> cases second <;>
          first
          | rfl
          | exact False.elim (notUnit rfl)
          | exact False.elim (notEnd rfl)

private theorem natReaderMissingFailure_exact
    (reader : NatReader) (parsedPrefix : List WorkSymbol) :
    let crossed := pushCrossed parsedPrefix []
    workRunExact? machine 1
        (guardedConfig reader.state parsedPrefix []) =
      some
        (cleanupSeekConfiguration
          [] (missingEndScan crossed) []) := by
  dsimp only
  unfold guardedConfig cleanupSeekConfiguration missingEndScan
  rw [pushCrossed_eq_reverse_append,
    pushCrossed_eq_reverse_append]
  simp only [List.append_nil, NatReader.state]
  set_option maxRecDepth 100000 in
    cases reader with
    | inputCount => rfl
    | gateCount => rfl
    | source continuation =>
        cases continuation <;> rfl

private theorem natTokenFailure_exact
    (reader : NatReader) (parsedPrefix : List WorkSymbol)
    {tokens : List Token}
    (failure : SourceParser.NatTokenFailure tokens)
    (prefixSafe : SafeSourceWord parsedPrefix) :
    ∃ steps final,
      workRunExact? machine steps
          (guardedConfig reader.state parsedPrefix
            (SourceParser.packedTokenCells tokens)) =
        some final ∧
      machine.isHalted final = true ∧
      final.state = State.reject ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  cases failure with
  | missingEnd units =>
      let parsed := parsedPrefix ++ unaryUnitCells units
      let crossed := pushCrossed parsed []
      have unitsRun :=
        natReaderUnits_exact reader units
          (pushCrossed parsedPrefix [leftGuard]) []
      have unitsCanonical :
          workRunExact? machine (2 * units)
              (guardedConfig reader.state parsedPrefix
                (unaryUnitCells units)) =
            some
              (guardedConfig reader.state parsed []) := by
        unfold guardedConfig
        simpa [parsed, pushCrossed_append] using unitsRun
      have failed :=
        natReaderMissingFailure_exact reader parsed
      have parsedSafe :
          SafeSourceWord parsed :=
        safe_append prefixSafe (unaryUnitCells_safe units)
      have tail :
          workRunExact? machine
              (missingEndTailSteps crossed)
              (guardedConfig reader.state parsed []) =
            some
              (cleanupExplicitRejectConfiguration
                [] (missingEndEraseWord crossed) []) := by
        have base :=
          missingEndTail_exact reader.state parsed crossed rfl
            parsedSafe
            (by
              unfold guardedConfig at failed
              rw [pushCrossed_eq_reverse_append] at failed
              simpa [crossed, pushCrossed_eq_reverse_append]
                using failed)
        unfold guardedConfig
        rw [pushCrossed_eq_reverse_append]
        simpa [crossed, pushCrossed_eq_reverse_append] using base
      have all :=
        exactRun_add (2 * units)
          (missingEndTailSteps crossed)
          _ _ _ unitsCanonical tail
      refine
        ⟨2 * units + missingEndTailSteps crossed,
          cleanupExplicitRejectConfiguration
            [] (missingEndEraseWord crossed) [],
          ?_, ?_, rfl, ?_⟩
      · simpa [packedTokenCells_replicate_unit] using all
      · exact cleanupExplicitReject_isHalted
          [] (missingEndEraseWord crossed) []
      · exact cleanupExplicitReject_output_empty
          [] (missingEndEraseWord crossed)
  | wrongToken units token suffix notUnit notNatEnd =>
      let tokens :=
        List.replicate units Token.unit ++ token :: suffix
      let parsed := parsedPrefix ++ unaryUnitCells units
      let suffixCells := SourceParser.packedTokenCells suffix
      let initial :=
        guardedConfig reader.state parsedPrefix
          (SourceParser.packedTokenCells tokens)
      have wordShape :
          SourceParser.packedTokenCells tokens =
            unaryUnitCells units ++
              SourceParser.tokenCells token ++ suffixCells := by
        dsimp [tokens, suffixCells]
        rw [packedTokenCells_append,
          packedTokenCells_replicate_unit]
        simp [SourceParser.packedTokenCells, List.append_assoc]
      have unitsRun :=
        natReaderUnits_exact reader units
          (pushCrossed parsedPrefix [leftGuard])
          (SourceParser.tokenCells token ++ suffixCells)
      have prefixRun :
          workRunExact? machine (2 * units) initial =
            some
              (guardedConfig reader.state parsed
                (SourceParser.tokenCells token ++ suffixCells)) := by
        unfold initial guardedConfig
        rw [wordShape]
        simpa [parsed, pushCrossed_append] using unitsRun
      have allWordSafe :
          SafeSourceWord
            (parsedPrefix ++
              SourceParser.packedTokenCells tokens) :=
        safe_append prefixSafe (packedTokenCells_safe tokens)
      have rejectFirst
          (current next : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [current, next])
          (wrong : current ≠ cell00) :
          ∃ steps final,
            workRunExact? machine steps initial = some final ∧
            machine.isHalted final = true ∧
            final.state = State.reject ∧
            (encodeWorkTape final.tape).outputBits = [] := by
        have failed :=
          natReaderFirstFailure_exact reader parsed
            current (next :: suffixCells) wrong
        have launch :=
          exactRun_add (2 * units) 1
            _ _ _ prefixRun
            (by simpa [cellsEq] using failed)
        have shape :
            parsedPrefix ++
                SourceParser.packedTokenCells tokens =
              parsed ++ current :: next :: suffixCells := by
          rw [wordShape, cellsEq]
          simp [parsed, List.append_assoc]
        exact safeExplicitFailure_exact
          (parsedPrefix ++
            SourceParser.packedTokenCells tokens)
          parsed current (next :: suffixCells)
          initial (2 * units + 1)
          shape allWordSafe launch
      have rejectSecond
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell00, current])
          (notUnitCell : current ≠ cell01)
          (notEndCell : current ≠ cell10) :
          ∃ steps final,
            workRunExact? machine steps initial = some final ∧
            machine.isHalted final = true ∧
            final.state = State.reject ∧
            (encodeWorkTape final.tape).outputBits = [] := by
        have failed :=
          natReaderSecondFailure_exact reader parsed current
            suffixCells notUnitCell notEndCell
        have launch :=
          exactRun_add (2 * units) 2
            _ _ _ prefixRun
            (by simpa [cellsEq] using failed)
        have shape :
            parsedPrefix ++
                SourceParser.packedTokenCells tokens =
              (parsed ++ [cell00]) ++ current :: suffixCells := by
          rw [wordShape, cellsEq]
          simp [parsed, List.append_assoc]
        exact safeExplicitFailure_exact
          (parsedPrefix ++
            SourceParser.packedTokenCells tokens)
          (parsed ++ [cell00]) current suffixCells
          initial (2 * units + 2)
          shape allWordSafe launch
      cases token with
      | version0 =>
          exact rejectSecond cell00 rfl (by decide) (by decide)
      | unit =>
          exact False.elim (notUnit rfl)
      | natEnd =>
          exact False.elim (notNatEnd rfl)
      | input =>
          exact rejectSecond cell11 rfl (by decide) (by decide)
      | constantFalse =>
          exact rejectFirst cell01 cell00 rfl (by decide)
      | constantTrue =>
          exact rejectFirst cell01 cell01 rfl (by decide)
      | gate =>
          exact rejectFirst cell01 cell10 rfl (by decide)
      | gateEnd =>
          exact rejectFirst cell01 cell11 rfl (by decide)
      | programEnd =>
          exact rejectFirst cell10 cell00 rfl (by decide)
      | outputsEnd =>
          exact rejectFirst cell10 cell01 rfl (by decide)
      | threshold =>
          exact rejectFirst cell10 cell10 rfl (by decide)
      | instanceEnd =>
          exact rejectFirst cell10 cell11 rfl (by decide)

set_option maxRecDepth 100000 in
private theorem sourceStartFirstFailure_exact
    (continuation : SourceContinuation)
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not00 : current ≠ cell00)
    (not01 : current ≠ cell01) :
    workRunExact? machine 1
        (guardedConfig (State.sourceStart continuation)
          parsedPrefix (current :: rest)) =
      some
        (cleanupSeekConfiguration
          [] (current :: pushCrossed parsedPrefix []) rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  rw [pushCrossed_eq_reverse_append,
    pushCrossed_eq_reverse_append]
  simp only [List.append_nil]
  simp only [cell00, cell01, WorkSymbol.zeroZero,
    WorkSymbol.zeroOne] at not00 not01
  cases continuation <;>
    rcases current with ⟨first, second⟩ <;>
    cases first <;> cases second <;>
    first
    | exact False.elim (not00 rfl)
    | exact False.elim (not01 rfl)
    | rfl

set_option maxRecDepth 100000 in
private theorem sourceAfter00Failure_exact
    (continuation : SourceContinuation)
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not11 : current ≠ cell11) :
    workRunExact? machine 2
        (guardedConfig (State.sourceStart continuation)
          parsedPrefix (cell00 :: current :: rest)) =
      some
        (cleanupSeekConfiguration
          []
          (current ::
            pushCrossed (parsedPrefix ++ [cell00]) [])
          rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_nil,
    List.cons_append]
  simp only [cell11, WorkSymbol.oneOne] at not11
  cases continuation <;>
    rcases current with ⟨first, second⟩ <;>
    cases first <;> cases second <;>
    first
    | rfl
    | rfl
    | rfl
    | exact False.elim (not11 rfl)

set_option maxRecDepth 100000 in
private theorem sourceAfter01Failure_exact
    (continuation : SourceContinuation)
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not00 : current ≠ cell00)
    (not01 : current ≠ cell01)
    (not10 : current ≠ cell10) :
    workRunExact? machine 2
        (guardedConfig (State.sourceStart continuation)
          parsedPrefix (cell01 :: current :: rest)) =
      some
        (cleanupSeekConfiguration
          []
          (current ::
            pushCrossed (parsedPrefix ++ [cell01]) [])
          rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_nil,
    List.cons_append]
  simp only [cell00, cell01, cell10,
    WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneZero] at not00 not01 not10
  cases continuation <;>
    rcases current with ⟨first, second⟩ <;>
    cases first <;> cases second <;>
    first
    | exact False.elim (not00 rfl)
    | exact False.elim (not01 rfl)
    | exact False.elim (not10 rfl)
    | rfl

private theorem sourceMissingFailure_exact
    (continuation : SourceContinuation)
    (parsedPrefix : List WorkSymbol) :
    let crossed := pushCrossed parsedPrefix []
    workRunExact? machine 1
        (guardedConfig (State.sourceStart continuation)
          parsedPrefix []) =
      some
        (cleanupSeekConfiguration
          [] (missingEndScan crossed) []) := by
  dsimp only
  unfold guardedConfig cleanupSeekConfiguration missingEndScan
  rw [pushCrossed_eq_reverse_append,
    pushCrossed_eq_reverse_append]
  simp only [List.append_nil]
  set_option maxRecDepth 100000 in
    cases continuation <;> rfl

private theorem sourceTokenFailure_exact
    (continuation : SourceContinuation)
    (parsedPrefix : List WorkSymbol)
    {tokens : List Token}
    (failure : SourceParser.SourceTokenFailure tokens)
    (prefixSafe : SafeSourceWord parsedPrefix) :
    ∃ steps final,
      workRunExact? machine steps
          (guardedConfig (State.sourceStart continuation)
            parsedPrefix
            (SourceParser.packedTokenCells tokens)) =
        some final ∧
      machine.isHalted final = true ∧
      final.state = State.reject ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  cases failure with
  | missing =>
      let crossed := pushCrossed parsedPrefix []
      have failed :=
        sourceMissingFailure_exact continuation parsedPrefix
      have tail :
          workRunExact? machine
              (missingEndTailSteps crossed)
              (guardedConfig (State.sourceStart continuation)
                parsedPrefix []) =
            some
              (cleanupExplicitRejectConfiguration
                [] (missingEndEraseWord crossed) []) := by
        have base :=
          missingEndTail_exact
            (State.sourceStart continuation)
            parsedPrefix crossed rfl prefixSafe
            (by
              unfold guardedConfig at failed
              rw [pushCrossed_eq_reverse_append] at failed
              simpa [crossed, pushCrossed_eq_reverse_append]
                using failed)
        unfold guardedConfig
        rw [pushCrossed_eq_reverse_append]
        simpa [crossed, pushCrossed_eq_reverse_append] using base
      refine
        ⟨missingEndTailSteps crossed,
          cleanupExplicitRejectConfiguration
            [] (missingEndEraseWord crossed) [],
          ?_, ?_, rfl, ?_⟩
      · simpa [SourceParser.packedTokenCells] using tail
      · exact cleanupExplicitReject_isHalted
          [] (missingEndEraseWord crossed) []
      · exact cleanupExplicitReject_output_empty
          [] (missingEndEraseWord crossed)
  | wrongHead token suffix notInput notFalse notTrue notGate =>
      let suffixCells := SourceParser.packedTokenCells suffix
      let initial :=
        guardedConfig (State.sourceStart continuation)
          parsedPrefix
          (SourceParser.packedTokenCells (token :: suffix))
      have allWordSafe :
          SafeSourceWord
            (parsedPrefix ++
              SourceParser.packedTokenCells (token :: suffix)) :=
        safe_append prefixSafe
          (packedTokenCells_safe (token :: suffix))
      have rejectFirst
          (current next : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [current, next])
          (not00 : current ≠ cell00)
          (not01 : current ≠ cell01) :
          ∃ steps final,
            workRunExact? machine steps initial = some final ∧
            machine.isHalted final = true ∧
            final.state = State.reject ∧
            (encodeWorkTape final.tape).outputBits = [] := by
        have failed :=
          sourceStartFirstFailure_exact continuation parsedPrefix
            current (next :: suffixCells) not00 not01
        have shape :
            parsedPrefix ++
                SourceParser.packedTokenCells (token :: suffix) =
              parsedPrefix ++ current :: next :: suffixCells := by
          simp [SourceParser.packedTokenCells, cellsEq, suffixCells]
        apply safeExplicitFailure_exact
          (parsedPrefix ++
            SourceParser.packedTokenCells (token :: suffix))
          parsedPrefix current (next :: suffixCells)
          initial 1 shape allWordSafe
        simpa [initial, SourceParser.packedTokenCells,
          cellsEq, suffixCells] using failed
      have rejectAfter00
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell00, current])
          (not11 : current ≠ cell11) :
          ∃ steps final,
            workRunExact? machine steps initial = some final ∧
            machine.isHalted final = true ∧
            final.state = State.reject ∧
            (encodeWorkTape final.tape).outputBits = [] := by
        have failed :=
          sourceAfter00Failure_exact continuation parsedPrefix
            current suffixCells not11
        have shape :
            parsedPrefix ++
                SourceParser.packedTokenCells (token :: suffix) =
              (parsedPrefix ++ [cell00]) ++
                current :: suffixCells := by
          simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells]
        apply safeExplicitFailure_exact
          (parsedPrefix ++
            SourceParser.packedTokenCells (token :: suffix))
          (parsedPrefix ++ [cell00]) current suffixCells
          initial 2 shape allWordSafe
        simpa [initial, SourceParser.packedTokenCells,
          cellsEq, suffixCells] using failed
      have rejectAfter01
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell01, current])
          (not00 : current ≠ cell00)
          (not01 : current ≠ cell01)
          (not10 : current ≠ cell10) :
          ∃ steps final,
            workRunExact? machine steps initial = some final ∧
            machine.isHalted final = true ∧
            final.state = State.reject ∧
            (encodeWorkTape final.tape).outputBits = [] := by
        have failed :=
          sourceAfter01Failure_exact continuation parsedPrefix
            current suffixCells not00 not01 not10
        have shape :
            parsedPrefix ++
                SourceParser.packedTokenCells (token :: suffix) =
              (parsedPrefix ++ [cell01]) ++
                current :: suffixCells := by
          simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells]
        apply safeExplicitFailure_exact
          (parsedPrefix ++
            SourceParser.packedTokenCells (token :: suffix))
          (parsedPrefix ++ [cell01]) current suffixCells
          initial 2 shape allWordSafe
        simpa [initial, SourceParser.packedTokenCells,
          cellsEq, suffixCells] using failed
      cases token with
      | version0 =>
          exact rejectAfter00 cell00 rfl (by decide)
      | unit =>
          exact rejectAfter00 cell01 rfl (by decide)
      | natEnd =>
          exact rejectAfter00 cell10 rfl (by decide)
      | input =>
          exact False.elim (notInput rfl)
      | constantFalse =>
          exact False.elim (notFalse rfl)
      | constantTrue =>
          exact False.elim (notTrue rfl)
      | gate =>
          exact False.elim (notGate rfl)
      | gateEnd =>
          exact rejectAfter01 cell11 rfl
            (by decide) (by decide) (by decide)
      | programEnd =>
          exact rejectFirst cell10 cell00 rfl
            (by decide) (by decide)
      | outputsEnd =>
          exact rejectFirst cell10 cell01 rfl
            (by decide) (by decide)
      | threshold =>
          exact rejectFirst cell10 cell10 rfl
            (by decide) (by decide)
      | instanceEnd =>
          exact rejectFirst cell10 cell11 rfl
            (by decide) (by decide)
  | @inputIndex indexTokens failure =>
      let nextPrefix := parsedPrefix ++ [cell00, cell11]
      have launch :
          workRunExact? machine 2
              (guardedConfig (State.sourceStart continuation)
                parsedPrefix
                (cell00 :: cell11 ::
                  SourceParser.packedTokenCells indexTokens)) =
            some
              (guardedConfig
                (State.sourceNatFirst continuation)
                nextPrefix
                (SourceParser.packedTokenCells indexTokens)) := by
        unfold guardedConfig
        simp [nextPrefix, pushCrossed_append, pushCrossed]
        set_option maxRecDepth 100000 in
          cases continuation <;> rfl
      have nextSafe :
          SafeSourceWord nextPrefix := by
        apply safe_append prefixSafe
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · decide
        · decide
        · contradiction
      rcases
          natTokenFailure_exact (.source continuation)
            nextPrefix failure nextSafe with
        ⟨tailSteps, final, tail, halted,
          finalState, output⟩
      refine
        ⟨2 + tailSteps, final, ?_,
          halted, finalState, output⟩
      apply exactRun_add 2 tailSteps _ _ _ ?_ tail
      simpa [SourceParser.packedTokenCells,
        SourceParser.tokenCells, NatReader.state,
        cell00, cell11, SourceParser.cell00,
        SourceParser.cell11] using launch
  | @gateIndex indexTokens failure =>
      let nextPrefix := parsedPrefix ++ [cell01, cell10]
      have launch :
          workRunExact? machine 2
              (guardedConfig (State.sourceStart continuation)
                parsedPrefix
                (cell01 :: cell10 ::
                  SourceParser.packedTokenCells indexTokens)) =
            some
              (guardedConfig
                (State.sourceNatFirst continuation)
                nextPrefix
                (SourceParser.packedTokenCells indexTokens)) := by
        unfold guardedConfig
        simp [nextPrefix, pushCrossed_append, pushCrossed]
        set_option maxRecDepth 100000 in
          cases continuation <;> rfl
      have nextSafe :
          SafeSourceWord nextPrefix := by
        apply safe_append prefixSafe
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · decide
        · decide
        · contradiction
      rcases
          natTokenFailure_exact (.source continuation)
            nextPrefix failure nextSafe with
        ⟨tailSteps, final, tail, halted,
          finalState, output⟩
      refine
        ⟨2 + tailSteps, final, ?_,
          halted, finalState, output⟩
      apply exactRun_add 2 tailSteps _ _ _ ?_ tail
      simpa [SourceParser.packedTokenCells,
        SourceParser.tokenCells, NatReader.state,
        cell01, cell10, SourceParser.cell01,
        SourceParser.cell10] using launch

/-! ### Constructive circuit-prefix composition -/

def RejectingExecution
    (initial : WorkConfiguration) : Prop :=
  ∃ steps final,
    workRunExact? machine steps initial = some final ∧
    machine.isHalted final = true ∧
    final.state = State.reject ∧
    (encodeWorkTape final.tape).outputBits = []

private theorem RejectingExecution.prepend
    (prefixSteps : Nat)
    (initial middle : WorkConfiguration)
    (prefixRun :
      workRunExact? machine prefixSteps initial = some middle)
    (tail : RejectingExecution middle) :
    RejectingExecution initial := by
  rcases tail with
    ⟨tailSteps, final, tailRun, halted,
      finalState, outputEmpty⟩
  exact
    ⟨prefixSteps + tailSteps, final,
      exactRun_add prefixSteps tailSteps
        initial middle final prefixRun tailRun,
      halted, finalState, outputEmpty⟩

/-! ### Constructive launches from malformed four-bit framing tails -/

private theorem guardedConfig_eq_crossed
    (state : Nat) (parsedPrefix word : List WorkSymbol) :
    guardedConfig state parsedPrefix word =
      configAtWord state
        (pushCrossed parsedPrefix [] ++ [leftGuard])
        word := by
  unfold guardedConfig
  rw [pushCrossed_eq_reverse_append,
    pushCrossed_eq_reverse_append]
  simp

private inductive BoundaryCleanupLaunch
    (state : Nat) (parsedPrefix word : List WorkSymbol) : Prop where
  | intro
      (steps : Nat)
      (consumedCells : List WorkSymbol)
      (storedCells : List WorkSymbol)
      (currentCell : WorkSymbol)
      (restCells : List WorkSymbol)
      (storedSafe : SafeSourceWord storedCells)
      (launchBound : steps ≤ 2)
      (storedLength :
        storedCells.length ≤ consumedCells.length)
      (wordShape :
        (word =
          consumedCells ++ currentCell :: restCells) ∨
          (word = consumedCells ∧
            currentCell = cellBlank ∧
              restCells = []))
      (run :
        workRunExact? machine steps
            (guardedConfig state parsedPrefix word) =
          some
            (cleanupSeekConfiguration
              []
              (currentCell ::
                pushCrossed
                  (parsedPrefix ++ storedCells) [])
              restCells)) :
      BoundaryCleanupLaunch state parsedPrefix word

private theorem boundaryCleanupLaunch_immediate
    (state : Nat) (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (run :
      workRunExact? machine 1
          (guardedConfig state parsedPrefix
            (current :: rest)) =
        some
          (cleanupSeekConfiguration
            [] (current ::
              pushCrossed parsedPrefix []) rest)) :
    BoundaryCleanupLaunch
      state parsedPrefix (current :: rest) := by
  refine
    ⟨1, [], [], current, rest, ?_, by omega, by simp,
      Or.inl rfl, ?_⟩
  · intro symbol member
    contradiction
  · simpa using run

private theorem boundaryCleanupLaunch_afterOne_retained
    (state : Nat) (parsedPrefix : List WorkSymbol)
    (consumed current : WorkSymbol)
    (rest : List WorkSymbol)
    (consumedSafe : SafeSourceWord [consumed])
    (run :
      workRunExact? machine 2
          (guardedConfig state parsedPrefix
            (consumed :: current :: rest)) =
        some
          (cleanupSeekConfiguration
            [] (current ::
              pushCrossed
                (parsedPrefix ++ [consumed]) [])
              rest)) :
    BoundaryCleanupLaunch state parsedPrefix
      (consumed :: current :: rest) := by
  exact
    ⟨2, [consumed], [consumed], current, rest,
      consumedSafe, by omega, by simp, Or.inl rfl, run⟩

private theorem boundaryCleanupLaunch_afterOne_rewritten
    (state : Nat) (parsedPrefix : List WorkSymbol)
    (consumed stored current : WorkSymbol)
    (rest : List WorkSymbol)
    (storedSafe : SafeSourceWord [stored])
    (run :
      workRunExact? machine 2
          (guardedConfig state parsedPrefix
            (consumed :: current :: rest)) =
        some
          (cleanupSeekConfiguration
            [] (current ::
              pushCrossed
                (parsedPrefix ++ [stored]) [])
              rest)) :
    BoundaryCleanupLaunch state parsedPrefix
      (consumed :: current :: rest) := by
  exact
    ⟨2, [consumed], [stored], current, rest,
      storedSafe, by omega, by simp, Or.inl rfl, run⟩

private theorem boundaryCleanupLaunch_eof_retained
    (state : Nat) (parsedPrefix : List WorkSymbol)
    (consumed : WorkSymbol)
    (consumedSafe : SafeSourceWord [consumed])
    (run :
      workRunExact? machine 2
          (guardedConfig state parsedPrefix [consumed]) =
        some
          (cleanupSeekConfiguration
            [] (cellBlank ::
              pushCrossed
                (parsedPrefix ++ [consumed]) [])
              [])) :
    BoundaryCleanupLaunch state parsedPrefix [consumed] := by
  exact
    ⟨2, [consumed], [consumed], cellBlank, [],
      consumedSafe, by omega, by simp,
      Or.inr ⟨rfl, rfl, rfl⟩, run⟩

private theorem boundaryCleanupLaunch_eof_rewritten
    (state : Nat) (parsedPrefix : List WorkSymbol)
    (consumed stored : WorkSymbol)
    (storedSafe : SafeSourceWord [stored])
    (run :
      workRunExact? machine 2
          (guardedConfig state parsedPrefix [consumed]) =
        some
          (cleanupSeekConfiguration
            [] (cellBlank ::
              pushCrossed
                (parsedPrefix ++ [stored]) [])
              [])) :
    BoundaryCleanupLaunch state parsedPrefix [consumed] := by
  exact
    ⟨2, [consumed], [stored], cellBlank, [],
      storedSafe, by omega, by simp,
      Or.inr ⟨rfl, rfl, rfl⟩, run⟩

private inductive SimpleMalformedBoundary where
  | versionFirst
  | versionSecond
  | nat (reader : NatReader)
  | source (continuation : SourceContinuation)
  | gateEnd
  | outputsEnd
  | instanceEnd
  | finalEOF

private def SimpleMalformedBoundary.state :
    SimpleMalformedBoundary → Nat
  | .versionFirst => State.versionFirst
  | .versionSecond => State.versionSecond
  | .nat reader => reader.state
  | .source continuation => State.sourceStart continuation
  | .gateEnd => State.gateEndFirst
  | .outputsEnd => State.outputsEndFirst
  | .instanceEnd => State.instanceEndFirst
  | .finalEOF => State.finalEOF

private theorem safe_singleton_of_sourcePacked
    (symbol : WorkSymbol)
    (packed : SourceParser.SourcePackedCell symbol) :
    SafeSourceWord [symbol] := by
  intro current member
  simp only [List.mem_cons, List.not_mem_nil,
    or_false] at member
  subst current
  exact sourcePackedCell_safe packed

private theorem safe_singleton_boolPair
    (first second : Bool) :
    SafeSourceWord
      [SourceParser.boolPairWorkCell first second] := by
  intro symbol member
  simp only [List.mem_cons, List.not_mem_nil,
    or_false] at member
  subst symbol
  cases first <;> cases second <;> decide

private theorem safe_singleton_gateMark :
    SafeSourceWord [gateMark] := by
  intro symbol member
  simp only [List.mem_cons, List.not_mem_nil,
    or_false] at member
  subst symbol
  decide

set_option maxRecDepth 100000 in
private theorem simpleMalformedBoundary_cell11_failure
    (boundary : SimpleMalformedBoundary)
    (parsedPrefix rest : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig boundary.state parsedPrefix
          (cell11 :: rest)) =
      some
        (cleanupSeekConfiguration
          [] (cell11 :: pushCrossed parsedPrefix [])
          rest) := by
  cases boundary with
  | versionFirst =>
      rw [guardedConfig_eq_crossed]
      rfl
  | versionSecond =>
      rw [guardedConfig_eq_crossed]
      rfl
  | nat reader =>
      cases reader with
      | inputCount =>
          rw [guardedConfig_eq_crossed]
          rfl
      | gateCount =>
          rw [guardedConfig_eq_crossed]
          rfl
      | source continuation =>
          cases continuation <;>
            rw [guardedConfig_eq_crossed] <;> rfl
  | source continuation =>
      cases continuation <;>
        rw [guardedConfig_eq_crossed] <;> rfl
  | gateEnd =>
      rw [guardedConfig_eq_crossed]
      rfl
  | outputsEnd =>
      rw [guardedConfig_eq_crossed]
      rfl
  | instanceEnd =>
      rw [guardedConfig_eq_crossed]
      rfl
  | finalEOF =>
      rw [guardedConfig_eq_crossed]
      rfl

set_option maxRecDepth 100000 in
private theorem simpleMalformedBoundary_dangling_failure
    (boundary : SimpleMalformedBoundary)
    (parsedPrefix : List WorkSymbol) (bit : Bool) :
    workRunExact? machine 1
        (guardedConfig boundary.state parsedPrefix
          [SourceParser.danglingWorkCell bit]) =
      some
        (cleanupSeekConfiguration
          [] (SourceParser.danglingWorkCell bit ::
            pushCrossed parsedPrefix [])
          []) := by
  cases boundary with
  | versionFirst =>
      cases bit <;>
        rw [guardedConfig_eq_crossed] <;> rfl
  | versionSecond =>
      cases bit <;>
        rw [guardedConfig_eq_crossed] <;> rfl
  | nat reader =>
      cases reader with
      | inputCount =>
          cases bit <;>
            rw [guardedConfig_eq_crossed] <;> rfl
      | gateCount =>
          cases bit <;>
            rw [guardedConfig_eq_crossed] <;> rfl
      | source continuation =>
          cases continuation <;> cases bit <;>
            rw [guardedConfig_eq_crossed] <;> rfl
  | source continuation =>
      cases continuation <;> cases bit <;>
        rw [guardedConfig_eq_crossed] <;> rfl
  | gateEnd =>
      cases bit <;>
        rw [guardedConfig_eq_crossed] <;> rfl
  | outputsEnd =>
      cases bit <;>
        rw [guardedConfig_eq_crossed] <;> rfl
  | instanceEnd =>
      cases bit <;>
        rw [guardedConfig_eq_crossed] <;> rfl
  | finalEOF =>
      cases bit <;>
        rw [guardedConfig_eq_crossed] <;> rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
private theorem simpleMalformedBoundary_trailingTwo
    (boundary : SimpleMalformedBoundary)
    (parsedPrefix : List WorkSymbol)
    (first second : Bool) :
    BoundaryCleanupLaunch boundary.state parsedPrefix
      [SourceParser.boolPairWorkCell first second] := by
  cases boundary with
  | versionFirst =>
      cases first <;> cases second <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl
        | apply boundaryCleanupLaunch_eof_retained
          · exact safe_singleton_boolPair _ _
          · rw [guardedConfig_eq_crossed]
            simp [pushCrossed_append, pushCrossed]
            rfl
  | versionSecond =>
      cases first <;> cases second <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl
        | apply boundaryCleanupLaunch_eof_retained
          · exact safe_singleton_boolPair _ _
          · rw [guardedConfig_eq_crossed]
            simp [pushCrossed_append, pushCrossed]
            rfl
  | nat reader =>
      cases reader with
      | inputCount =>
          cases first <;> cases second <;>
            first
            | apply boundaryCleanupLaunch_immediate
              rw [guardedConfig_eq_crossed]
              rfl
            | apply boundaryCleanupLaunch_eof_retained
              · exact safe_singleton_boolPair _ _
              · rw [guardedConfig_eq_crossed]
                simp [pushCrossed_append, pushCrossed]
                rfl
      | gateCount =>
          cases first <;> cases second <;>
            first
            | apply boundaryCleanupLaunch_immediate
              rw [guardedConfig_eq_crossed]
              rfl
            | apply boundaryCleanupLaunch_eof_retained
              · exact safe_singleton_boolPair _ _
              · rw [guardedConfig_eq_crossed]
                simp [pushCrossed_append, pushCrossed]
                rfl
      | source continuation =>
          cases continuation <;>
            cases first <;> cases second <;>
            first
            | apply boundaryCleanupLaunch_immediate
              rw [guardedConfig_eq_crossed]
              rfl
            | apply boundaryCleanupLaunch_eof_retained
              · exact safe_singleton_boolPair _ _
              · rw [guardedConfig_eq_crossed]
                simp [pushCrossed_append, pushCrossed]
                rfl
  | source continuation =>
      cases continuation <;>
        cases first <;> cases second <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl
        | apply boundaryCleanupLaunch_eof_retained
          · exact safe_singleton_boolPair _ _
          · rw [guardedConfig_eq_crossed]
            simp [pushCrossed_append, pushCrossed]
            rfl
  | gateEnd =>
      cases first <;> cases second <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl
        | apply boundaryCleanupLaunch_eof_rewritten
            (stored := gateMark)
          · exact safe_singleton_gateMark
          · rw [guardedConfig_eq_crossed]
            simp [pushCrossed_append, pushCrossed]
            rfl
  | outputsEnd =>
      cases first <;> cases second <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl
        | apply boundaryCleanupLaunch_eof_retained
          · exact safe_singleton_boolPair _ _
          · rw [guardedConfig_eq_crossed]
            simp [pushCrossed_append, pushCrossed]
            rfl
  | instanceEnd =>
      cases first <;> cases second <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl
        | apply boundaryCleanupLaunch_eof_retained
          · exact safe_singleton_boolPair _ _
          · rw [guardedConfig_eq_crossed]
            simp [pushCrossed_append, pushCrossed]
            rfl
  | finalEOF =>
      cases first <;> cases second <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 100000 in
private theorem simpleMalformedBoundary_trailingThree
    (boundary : SimpleMalformedBoundary)
    (parsedPrefix : List WorkSymbol)
    (first second third : Bool) :
    BoundaryCleanupLaunch boundary.state parsedPrefix
      [SourceParser.boolPairWorkCell first second,
        SourceParser.danglingWorkCell third] := by
  cases boundary with
  | versionFirst =>
      cases first <;> cases second <;> cases third <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl
        | apply boundaryCleanupLaunch_afterOne_retained
          · exact safe_singleton_boolPair _ _
          · rw [guardedConfig_eq_crossed]
            simp [pushCrossed_append, pushCrossed]
            rfl
  | versionSecond =>
      cases first <;> cases second <;> cases third <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl
        | apply boundaryCleanupLaunch_afterOne_retained
          · exact safe_singleton_boolPair _ _
          · rw [guardedConfig_eq_crossed]
            simp [pushCrossed_append, pushCrossed]
            rfl
  | nat reader =>
      cases reader with
      | inputCount =>
          cases first <;> cases second <;> cases third <;>
            first
            | apply boundaryCleanupLaunch_immediate
              rw [guardedConfig_eq_crossed]
              rfl
            | apply boundaryCleanupLaunch_afterOne_retained
              · exact safe_singleton_boolPair _ _
              · rw [guardedConfig_eq_crossed]
                simp [pushCrossed_append, pushCrossed]
                rfl
      | gateCount =>
          cases first <;> cases second <;> cases third <;>
            first
            | apply boundaryCleanupLaunch_immediate
              rw [guardedConfig_eq_crossed]
              rfl
            | apply boundaryCleanupLaunch_afterOne_retained
              · exact safe_singleton_boolPair _ _
              · rw [guardedConfig_eq_crossed]
                simp [pushCrossed_append, pushCrossed]
                rfl
      | source continuation =>
          cases continuation <;>
            cases first <;> cases second <;>
              cases third <;>
            first
            | apply boundaryCleanupLaunch_immediate
              rw [guardedConfig_eq_crossed]
              rfl
            | apply boundaryCleanupLaunch_afterOne_retained
              · exact safe_singleton_boolPair _ _
              · rw [guardedConfig_eq_crossed]
                simp [pushCrossed_append, pushCrossed]
                rfl
  | source continuation =>
      cases continuation <;>
        cases first <;> cases second <;> cases third <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl
        | apply boundaryCleanupLaunch_afterOne_retained
          · exact safe_singleton_boolPair _ _
          · rw [guardedConfig_eq_crossed]
            simp [pushCrossed_append, pushCrossed]
            rfl
  | gateEnd =>
      cases first <;> cases second <;> cases third <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl
        | apply boundaryCleanupLaunch_afterOne_rewritten
            (stored := gateMark)
          · exact safe_singleton_gateMark
          · rw [guardedConfig_eq_crossed]
            simp [pushCrossed_append, pushCrossed]
            rfl
  | outputsEnd =>
      cases first <;> cases second <;> cases third <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl
        | apply boundaryCleanupLaunch_afterOne_retained
          · exact safe_singleton_boolPair _ _
          · rw [guardedConfig_eq_crossed]
            simp [pushCrossed_append, pushCrossed]
            rfl
  | instanceEnd =>
      cases first <;> cases second <;> cases third <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl
        | apply boundaryCleanupLaunch_afterOne_retained
          · exact safe_singleton_boolPair _ _
          · rw [guardedConfig_eq_crossed]
            simp [pushCrossed_append, pushCrossed]
            rfl
  | finalEOF =>
      cases first <;> cases second <;> cases third <;>
        first
        | apply boundaryCleanupLaunch_immediate
          rw [guardedConfig_eq_crossed]
          rfl

private theorem simpleMalformedBoundary_launch
    (boundary : SimpleMalformedBoundary)
    (parsedPrefix : List WorkSymbol)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundaryCleanupLaunch boundary.state
      parsedPrefix workTail := by
  cases malformed with
  | reserved third fourth suffix =>
      apply boundaryCleanupLaunch_immediate
      exact simpleMalformedBoundary_cell11_failure
        boundary parsedPrefix
          (SourceParser.boolPairWorkCell third fourth ::
            SourceParser.packedRawBits suffix)
  | trailingOne first =>
      apply boundaryCleanupLaunch_immediate
      simpa [pushCrossed] using
        (simpleMalformedBoundary_dangling_failure
          boundary parsedPrefix first)
  | trailingTwo first second =>
      exact simpleMalformedBoundary_trailingTwo
        boundary parsedPrefix first second
  | trailingThree first second third =>
      exact simpleMalformedBoundary_trailingThree
        boundary parsedPrefix first second third

private theorem cleanupMissingSeek_rejecting_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix) :
    RejectingExecution
      (cleanupSeekConfiguration
        []
        (missingEndScan
          (pushCrossed parsedPrefix []))
        []) := by
  let crossed := pushCrossed parsedPrefix []
  let scan := missingEndScan crossed
  let eraseWord := missingEndEraseWord crossed
  have scanNoGuard :
      ∀ symbol, symbol ∈ scan →
        symbol ≠ leftGuard := by
    intro symbol member
    simp only [scan, missingEndScan,
      List.mem_cons] at member
    rcases member with blankEq | crossedMember
    · subst symbol
      decide
    · dsimp [crossed] at crossedMember
      rw [pushCrossed_eq_reverse_append] at crossedMember
      have member' :
          symbol ∈ parsedPrefix.reverse := by
        simpa using crossedMember
      exact
        (prefixSafe symbol (by simpa using member')).1
  have eraseNonblank :
      ∀ symbol, symbol ∈ eraseWord →
        symbol ≠ cellBlank := by
    intro symbol member
    dsimp [eraseWord, missingEndEraseWord] at member
    have materialized :
        pushCleanupScan
            (pushCrossed parsedPrefix []) [] =
          parsedPrefix := by
      simpa [pushCleanupScan, SourceParser.pushCleanupScan] using
        (pushCleanupScan_pushCrossed parsedPrefix [] [])
    rw [materialized] at member
    exact (prefixSafe symbol member).2
  have forwardShape :
      pushCleanupScan scan [] =
        eraseWord ++ cellBlank :: [] := by
    dsimp [scan, eraseWord]
    unfold missingEndScan missingEndEraseWord
    rw [pushCleanupScan, SourceParser.pushCleanupScan]
    simpa using
      (SourceParser.pushCleanupScan_append crossed []
        [cellBlank])
  have cleanup :=
    guardedCleanupExplicit_exact
      [] scan [] eraseWord []
      scanNoGuard forwardShape eraseNonblank
  refine
    ⟨guardedCleanupExplicitSteps scan eraseWord,
      cleanupExplicitRejectConfiguration
        [] eraseWord [],
      ?_, ?_, rfl, ?_⟩
  · simpa [scan] using cleanup
  · exact cleanupExplicitReject_isHalted
      [] eraseWord []
  · exact cleanupExplicitReject_output_empty
      [] eraseWord

private theorem boundaryCleanupLaunch_rejecting_exact
    (state : Nat) (parsedPrefix word : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (wordSafe : SafeSourceWord word)
    (launch :
      BoundaryCleanupLaunch state parsedPrefix word) :
    RejectingExecution
      (guardedConfig state parsedPrefix word) := by
  rcases launch with
    ⟨launchSteps, consumedCells, storedCells,
      currentCell, restCells, storedSafe, _launchBound,
      _storedLength,
      wordShape, launchRun⟩
  rcases wordShape with explicitShape | implicitShape
  · let cleanupPrefix := parsedPrefix ++ storedCells
    have cleanupPrefixSafe :
        SafeSourceWord cleanupPrefix :=
      safe_append prefixSafe storedSafe
    have tailSafe :
        SafeSourceWord (currentCell :: restCells) := by
      intro symbol member
      apply wordSafe symbol
      rw [explicitShape]
      exact List.mem_append.mpr (Or.inr member)
    have cleanupWordSafe :
        SafeSourceWord
          (cleanupPrefix ++ currentCell :: restCells) :=
      safe_append cleanupPrefixSafe tailSafe
    exact
      safeExplicitFailure_exact
        (cleanupPrefix ++ currentCell :: restCells)
        cleanupPrefix currentCell restCells
        (guardedConfig state parsedPrefix word)
        launchSteps rfl cleanupWordSafe launchRun
  · rcases implicitShape with
      ⟨wordEq, currentEq, restEq⟩
    subst currentCell
    subst restCells
    let cleanupPrefix := parsedPrefix ++ storedCells
    have cleanupPrefixSafe :
        SafeSourceWord cleanupPrefix :=
      safe_append prefixSafe storedSafe
    have tail :=
      cleanupMissingSeek_rejecting_exact
        cleanupPrefix cleanupPrefixSafe
    apply RejectingExecution.prepend launchSteps _ _ launchRun
    simpa [cleanupPrefix, missingEndScan] using tail

private theorem simpleMalformedBoundary_rejecting_exact
    (boundary : SimpleMalformedBoundary)
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (guardedConfig boundary.state
        parsedPrefix workTail) := by
  exact
    boundaryCleanupLaunch_rejecting_exact
      boundary.state parsedPrefix workTail
      prefixSafe (malformedWorkTail_safe malformed)
      (simpleMalformedBoundary_launch
        boundary parsedPrefix malformed)

private theorem natTokenFailureWithMalformedTail_exact
    (reader : NatReader) (parsedPrefix : List WorkSymbol)
    {tokens : List Token}
    (failure : SourceParser.NatTokenFailure tokens)
    (prefixSafe : SafeSourceWord parsedPrefix)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (guardedConfig reader.state parsedPrefix
        (SourceParser.packedTokenCells tokens ++ workTail)) := by
  cases failure with
  | missingEnd units =>
      let parsed := parsedPrefix ++ unaryUnitCells units
      have unitsRun :=
        natReaderUnits_exact reader units
          (pushCrossed parsedPrefix [leftGuard]) workTail
      have prefixRun :
          workRunExact? machine (2 * units)
              (guardedConfig reader.state parsedPrefix
                (unaryUnitCells units ++ workTail)) =
            some
              (guardedConfig reader.state parsed workTail) := by
        unfold guardedConfig
        simpa [parsed, pushCrossed_append] using unitsRun
      have parsedSafe :
          SafeSourceWord parsed :=
        safe_append prefixSafe (unaryUnitCells_safe units)
      have tail :=
        simpleMalformedBoundary_rejecting_exact
          (.nat reader) parsed parsedSafe malformed
      apply RejectingExecution.prepend
        (2 * units)
        (guardedConfig reader.state parsedPrefix
          (SourceParser.packedTokenCells
              (List.replicate units .unit) ++
            workTail))
        (guardedConfig reader.state parsed workTail)
      · simpa [packedTokenCells_replicate_unit] using prefixRun
      · simpa [SimpleMalformedBoundary.state] using tail
  | wrongToken units token suffix notUnit notNatEnd =>
      let tokens :=
        List.replicate units Token.unit ++ token :: suffix
      let parsed := parsedPrefix ++ unaryUnitCells units
      let suffixCells :=
        SourceParser.packedTokenCells suffix ++ workTail
      let initial :=
        guardedConfig reader.state parsedPrefix
          (SourceParser.packedTokenCells tokens ++ workTail)
      have wordShape :
          SourceParser.packedTokenCells tokens ++ workTail =
            unaryUnitCells units ++
              SourceParser.tokenCells token ++ suffixCells := by
        dsimp [tokens, suffixCells]
        rw [packedTokenCells_append,
          packedTokenCells_replicate_unit]
        simp [SourceParser.packedTokenCells, List.append_assoc]
      have unitsRun :=
        natReaderUnits_exact reader units
          (pushCrossed parsedPrefix [leftGuard])
          (SourceParser.tokenCells token ++ suffixCells)
      have prefixRun :
          workRunExact? machine (2 * units) initial =
            some
              (guardedConfig reader.state parsed
                (SourceParser.tokenCells token ++
                  suffixCells)) := by
        unfold initial guardedConfig
        rw [wordShape]
        simpa [parsed, pushCrossed_append] using unitsRun
      have allWordSafe :
          SafeSourceWord
            (parsedPrefix ++
              (SourceParser.packedTokenCells tokens ++
                workTail)) := by
        apply safe_append prefixSafe
        exact
          safe_append
            (packedTokenCells_safe tokens)
            (malformedWorkTail_safe malformed)
      have rejectFirst
          (current next : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [current, next])
          (wrong : current ≠ cell00) :
          RejectingExecution initial := by
        have failed :=
          natReaderFirstFailure_exact reader parsed
            current (next :: suffixCells) wrong
        have launch :=
          exactRun_add (2 * units) 1
            _ _ _ prefixRun
            (by simpa [cellsEq] using failed)
        have shape :
            parsedPrefix ++
                (SourceParser.packedTokenCells tokens ++
                  workTail) =
              parsed ++ current :: next :: suffixCells := by
          rw [wordShape, cellsEq]
          simp [parsed, List.append_assoc]
        exact
          safeExplicitFailure_exact
            (parsedPrefix ++
              (SourceParser.packedTokenCells tokens ++
                workTail))
            parsed current (next :: suffixCells)
            initial (2 * units + 1)
            shape allWordSafe launch
      have rejectSecond
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell00, current])
          (notUnitCell : current ≠ cell01)
          (notEndCell : current ≠ cell10) :
          RejectingExecution initial := by
        have failed :=
          natReaderSecondFailure_exact reader parsed current
            suffixCells notUnitCell notEndCell
        have launch :=
          exactRun_add (2 * units) 2
            _ _ _ prefixRun
            (by simpa [cellsEq] using failed)
        have shape :
            parsedPrefix ++
                (SourceParser.packedTokenCells tokens ++
                  workTail) =
              (parsed ++ [cell00]) ++
                current :: suffixCells := by
          rw [wordShape, cellsEq]
          simp [parsed, List.append_assoc]
        exact
          safeExplicitFailure_exact
            (parsedPrefix ++
              (SourceParser.packedTokenCells tokens ++
                workTail))
            (parsed ++ [cell00]) current suffixCells
            initial (2 * units + 2)
            shape allWordSafe launch
      cases token with
      | version0 =>
          exact rejectSecond cell00 rfl (by decide) (by decide)
      | unit =>
          exact False.elim (notUnit rfl)
      | natEnd =>
          exact False.elim (notNatEnd rfl)
      | input =>
          exact rejectSecond cell11 rfl (by decide) (by decide)
      | constantFalse =>
          exact rejectFirst cell01 cell00 rfl (by decide)
      | constantTrue =>
          exact rejectFirst cell01 cell01 rfl (by decide)
      | gate =>
          exact rejectFirst cell01 cell10 rfl (by decide)
      | gateEnd =>
          exact rejectFirst cell01 cell11 rfl (by decide)
      | programEnd =>
          exact rejectFirst cell10 cell00 rfl (by decide)
      | outputsEnd =>
          exact rejectFirst cell10 cell01 rfl (by decide)
      | threshold =>
          exact rejectFirst cell10 cell10 rfl (by decide)
      | instanceEnd =>
          exact rejectFirst cell10 cell11 rfl (by decide)

private theorem sourceTokenFailureWithMalformedTail_exact
    (continuation : SourceContinuation)
    (parsedPrefix : List WorkSymbol)
    {tokens : List Token}
    (failure : SourceParser.SourceTokenFailure tokens)
    (prefixSafe : SafeSourceWord parsedPrefix)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (guardedConfig (State.sourceStart continuation)
        parsedPrefix
        (SourceParser.packedTokenCells tokens ++ workTail)) := by
  cases failure with
  | missing =>
      exact
        simpleMalformedBoundary_rejecting_exact
          (.source continuation) parsedPrefix
          prefixSafe malformed
  | wrongHead token suffix notInput notFalse notTrue notGate =>
      let suffixCells :=
        SourceParser.packedTokenCells suffix ++ workTail
      let initial :=
        guardedConfig (State.sourceStart continuation)
          parsedPrefix
          (SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail)
      have allWordSafe :
          SafeSourceWord
            (parsedPrefix ++
              (SourceParser.packedTokenCells
                  (token :: suffix) ++
                workTail)) := by
        apply safe_append prefixSafe
        exact
          safe_append
            (packedTokenCells_safe (token :: suffix))
            (malformedWorkTail_safe malformed)
      have rejectFirst
          (current next : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [current, next])
          (not00 : current ≠ cell00)
          (not01 : current ≠ cell01) :
          RejectingExecution initial := by
        have failed :=
          sourceStartFirstFailure_exact continuation parsedPrefix
            current (next :: suffixCells) not00 not01
        have shape :
            parsedPrefix ++
                (SourceParser.packedTokenCells
                    (token :: suffix) ++
                  workTail) =
              parsedPrefix ++ current :: next :: suffixCells := by
          simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells]
        exact
          safeExplicitFailure_exact
            (parsedPrefix ++
              (SourceParser.packedTokenCells
                  (token :: suffix) ++
                workTail))
            parsedPrefix current (next :: suffixCells)
            initial 1 shape allWordSafe
            (by
              simpa [initial,
                SourceParser.packedTokenCells,
                cellsEq, suffixCells,
                List.append_assoc] using failed)
      have rejectAfter00
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell00, current])
          (not11 : current ≠ cell11) :
          RejectingExecution initial := by
        have failed :=
          sourceAfter00Failure_exact continuation parsedPrefix
            current suffixCells not11
        have shape :
            parsedPrefix ++
                (SourceParser.packedTokenCells
                    (token :: suffix) ++
                  workTail) =
              (parsedPrefix ++ [cell00]) ++
                current :: suffixCells := by
          simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells, List.append_assoc]
        exact
          safeExplicitFailure_exact
            (parsedPrefix ++
              (SourceParser.packedTokenCells
                  (token :: suffix) ++
                workTail))
            (parsedPrefix ++ [cell00])
            current suffixCells initial 2
            shape allWordSafe
            (by
              simpa [initial,
                SourceParser.packedTokenCells,
                cellsEq, suffixCells,
                List.append_assoc] using failed)
      have rejectAfter01
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell01, current])
          (not00 : current ≠ cell00)
          (not01 : current ≠ cell01)
          (not10 : current ≠ cell10) :
          RejectingExecution initial := by
        have failed :=
          sourceAfter01Failure_exact continuation parsedPrefix
            current suffixCells not00 not01 not10
        have shape :
            parsedPrefix ++
                (SourceParser.packedTokenCells
                    (token :: suffix) ++
                  workTail) =
              (parsedPrefix ++ [cell01]) ++
                current :: suffixCells := by
          simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells, List.append_assoc]
        exact
          safeExplicitFailure_exact
            (parsedPrefix ++
              (SourceParser.packedTokenCells
                  (token :: suffix) ++
                workTail))
            (parsedPrefix ++ [cell01])
            current suffixCells initial 2
            shape allWordSafe
            (by
              simpa [initial,
                SourceParser.packedTokenCells,
                cellsEq, suffixCells,
                List.append_assoc] using failed)
      cases token with
      | version0 =>
          exact rejectAfter00 cell00 rfl (by decide)
      | unit =>
          exact rejectAfter00 cell01 rfl (by decide)
      | natEnd =>
          exact rejectAfter00 cell10 rfl (by decide)
      | input =>
          exact False.elim (notInput rfl)
      | constantFalse =>
          exact False.elim (notFalse rfl)
      | constantTrue =>
          exact False.elim (notTrue rfl)
      | gate =>
          exact False.elim (notGate rfl)
      | gateEnd =>
          exact rejectAfter01 cell11 rfl
            (by decide) (by decide) (by decide)
      | programEnd =>
          exact rejectFirst cell10 cell00 rfl
            (by decide) (by decide)
      | outputsEnd =>
          exact rejectFirst cell10 cell01 rfl
            (by decide) (by decide)
      | threshold =>
          exact rejectFirst cell10 cell10 rfl
            (by decide) (by decide)
      | instanceEnd =>
          exact rejectFirst cell10 cell11 rfl
            (by decide) (by decide)
  | @inputIndex indexTokens indexFailure =>
      let nextPrefix := parsedPrefix ++ [cell00, cell11]
      have launch :
          workRunExact? machine 2
              (guardedConfig (State.sourceStart continuation)
                parsedPrefix
                (cell00 :: cell11 ::
                  (SourceParser.packedTokenCells indexTokens ++
                    workTail))) =
            some
              (guardedConfig
                (State.sourceNatFirst continuation)
                nextPrefix
                (SourceParser.packedTokenCells indexTokens ++
                  workTail)) := by
        unfold guardedConfig
        simp [nextPrefix, pushCrossed_append, pushCrossed]
        set_option maxRecDepth 100000 in
          cases continuation <;> rfl
      have nextSafe :
          SafeSourceWord nextPrefix := by
        apply safe_append prefixSafe
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · decide
        · decide
        · contradiction
      have tail :=
        natTokenFailureWithMalformedTail_exact
          (.source continuation) nextPrefix
          indexFailure nextSafe malformed
      apply RejectingExecution.prepend 2 _ _ ?_ tail
      simpa [SourceParser.packedTokenCells,
        SourceParser.tokenCells, NatReader.state,
        cell00, cell11, SourceParser.cell00,
        SourceParser.cell11, List.append_assoc] using launch
  | @gateIndex indexTokens indexFailure =>
      let nextPrefix := parsedPrefix ++ [cell01, cell10]
      have launch :
          workRunExact? machine 2
              (guardedConfig (State.sourceStart continuation)
                parsedPrefix
                (cell01 :: cell10 ::
                  (SourceParser.packedTokenCells indexTokens ++
                    workTail))) =
            some
              (guardedConfig
                (State.sourceNatFirst continuation)
                nextPrefix
                (SourceParser.packedTokenCells indexTokens ++
                  workTail)) := by
        unfold guardedConfig
        simp [nextPrefix, pushCrossed_append, pushCrossed]
        set_option maxRecDepth 100000 in
          cases continuation <;> rfl
      have nextSafe :
          SafeSourceWord nextPrefix := by
        apply safe_append prefixSafe
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · decide
        · decide
        · contradiction
      have tail :=
        natTokenFailureWithMalformedTail_exact
          (.source continuation) nextPrefix
          indexFailure nextSafe malformed
      apply RejectingExecution.prepend 2 _ _ ?_ tail
      simpa [SourceParser.packedTokenCells,
        SourceParser.tokenCells, NatReader.state,
        cell01, cell10, SourceParser.cell01,
        SourceParser.cell10, List.append_assoc] using launch

private theorem versionPrefixWord_exact
    (suffix : List WorkSymbol) :
    workRunExact? machine 4
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            ([cell00, cell00] ++ suffix))) =
      some
        (guardedConfig State.inputCountFirst
          [cell00, cell00] suffix) := by
  cases suffix <;> rfl

private def inputPrefixWordSteps (inputs : Nat) : Nat :=
  4 + 2 * (inputs + 1)

private theorem inputPrefixWord_exact
    (inputs : Nat) (suffix : List WorkSymbol) :
    workRunExact? machine (inputPrefixWordSteps inputs)
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            ([cell00, cell00] ++
              natCells inputs ++ suffix))) =
      some
        (guardedConfig State.gateCountFirst
          ([cell00, cell00] ++ natCells inputs)
          suffix) := by
  have version :=
    versionPrefixWord_exact (natCells inputs ++ suffix)
  have count :=
    inputCount_exact inputs [cell00, cell00, leftGuard] suffix
  have all :=
    exactRun_add 4 (2 * (inputs + 1))
      _ _ _ version (by
        simpa [guardedConfig, pushCrossed_append,
          pushCrossed] using count)
  simpa [inputPrefixWordSteps, guardedConfig,
    pushCrossed_append, pushCrossed,
    List.append_assoc] using all

private def headerPrefixCells
    (inputs gateCount : Nat) : List WorkSymbol :=
  [cell00, cell00] ++
    natCells inputs ++ natCells gateCount

private def headerPrefixWordSteps
    (inputs gateCount : Nat) : Nat :=
  inputPrefixWordSteps inputs + 2 * (gateCount + 1)

private theorem headerPrefixWord_exact
    (inputs gateCount : Nat) (suffix : List WorkSymbol) :
    workRunExact? machine
        (headerPrefixWordSteps inputs gateCount)
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            (headerPrefixCells inputs gateCount ++ suffix))) =
      some
        (guardedConfig State.gateStart
          (headerPrefixCells inputs gateCount) suffix) := by
  have input :=
    inputPrefixWord_exact inputs (natCells gateCount ++ suffix)
  have count :=
    gateCount_exact gateCount
      (pushCrossed
        ([cell00, cell00] ++ natCells inputs)
        [leftGuard])
      suffix
  have all :=
    exactRun_add (inputPrefixWordSteps inputs)
      (2 * (gateCount + 1))
      _ _ _ input (by
        simpa [guardedConfig, pushCrossed_append] using count)
  have endpointEq :
      pushCrossed (natCells gateCount)
          (pushCrossed
            ([cell00, cell00] ++ natCells inputs)
            [leftGuard]) =
        pushCrossed (headerPrefixCells inputs gateCount)
          [leftGuard] := by
    rw [← pushCrossed_append]
    simp [headerPrefixCells]
  unfold guardedConfig
  rw [← endpointEq]
  simpa [headerPrefixWordSteps, headerPrefixCells,
    List.append_assoc] using all

private theorem packedCircuitHeaderTokens_eq
    (inputs gateCount : Nat) :
    SourceParser.packedTokenCells
        (SourceParser.circuitHeaderTokens
          inputs gateCount) =
      headerPrefixCells inputs gateCount := by
  unfold SourceParser.circuitHeaderTokens
  change
    [cell00, cell00] ++
        SourceParser.packedTokenCells
          (encodeNatTokens inputs ++
            encodeNatTokens gateCount) =
      headerPrefixCells inputs gateCount
  rw [packedTokenCells_append,
    SourceParser.packedTokenCells_encodeNatTokens,
    SourceParser.packedTokenCells_encodeNatTokens]
  rfl

private theorem packedCircuitGatesPrefixTokens_eq
    (inputs : Nat) (gates : List RawGate) :
    SourceParser.packedTokenCells
        (SourceParser.circuitGatesPrefixTokens inputs gates) =
      headerPrefixCells inputs gates.length ++
        gateListCells gates := by
  unfold SourceParser.circuitGatesPrefixTokens
  rw [packedTokenCells_append,
    SourceParser.packedTokenCells_encodeGateListTokens]
  unfold SourceParser.circuitHeaderTokens
  change
    ([cell00, cell00] ++
      SourceParser.packedTokenCells
        (encodeNatTokens inputs ++
          encodeNatTokens gates.length)) ++
        gateListCells gates =
      headerPrefixCells inputs gates.length
        ++ gateListCells gates
  rw [packedTokenCells_append,
    SourceParser.packedTokenCells_encodeNatTokens,
    SourceParser.packedTokenCells_encodeNatTokens]
  rfl

private def circuitGatesPrefixWordSteps
    (inputs : Nat) (gates : List RawGate) : Nat :=
  headerPrefixWordSteps inputs gates.length +
    gatesSteps inputs [] gates

private theorem circuitGatesPrefixWord_exact
    (inputs : Nat) (gates : List RawGate)
    (suffix : List WorkSymbol) :
    workRunExact? machine
        (circuitGatesPrefixWordSteps inputs gates)
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            (SourceParser.packedTokenCells
                (SourceParser.circuitGatesPrefixTokens inputs gates) ++
              suffix))) =
      some
        (guardedConfig State.gateStart
          (gatePrefix inputs gates []) suffix) := by
  have header :=
    headerPrefixWord_exact inputs gates.length
      (gateListCells gates ++ suffix)
  have headerCanonical :
      workRunExact? machine
          (headerPrefixWordSteps inputs gates.length)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (SourceParser.circuitGatesPrefixTokens
                    inputs gates) ++
                suffix))) =
        some
          (guardedConfig State.gateStart
            (gatePrefix inputs [] gates)
            (gateListCells gates ++ suffix)) := by
    have prefixEq :
        gatePrefix inputs [] gates =
          headerPrefixCells inputs gates.length := by
      simp [gatePrefix, SourceParser.gatePrefix,
        headerPrefixCells, SourceParser.countCells,
        SourceParser.markedGateListCells,
        cell00, SourceParser.cell00]
    rw [packedCircuitGatesPrefixTokens_eq, prefixEq]
    simpa only [List.append_assoc] using header
  have gatesRun :=
    gates_exact inputs [] gates suffix
  have all :=
    exactRun_add
      (headerPrefixWordSteps inputs gates.length)
      (gatesSteps inputs [] gates)
      _ _ _ headerCanonical gatesRun
  simpa [circuitGatesPrefixWordSteps] using all

private def circuitProgramPrefixWordSteps
    (inputs : Nat) (gates : List RawGate) : Nat :=
  circuitGatesPrefixWordSteps inputs gates +
    programEndSteps inputs gates

private theorem circuitProgramPrefixWord_exact
    (inputs : Nat) (gates : List RawGate)
    (suffix : List WorkSymbol) :
    workRunExact? machine
        (circuitProgramPrefixWordSteps inputs gates)
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            (SourceParser.packedTokenCells
                (SourceParser.circuitGatesPrefixTokens inputs gates ++
                  [.programEnd]) ++ suffix))) =
      some
        (guardedConfig (State.sourceStart .output)
          (outputPrefix inputs gates) suffix) := by
  have gatesRun :=
    circuitGatesPrefixWord_exact inputs gates
      ([cell10, cell00] ++ suffix)
  have gatesCanonical :
      workRunExact? machine
          (circuitGatesPrefixWordSteps inputs gates)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (SourceParser.circuitGatesPrefixTokens inputs gates ++
                    [.programEnd]) ++ suffix))) =
        some
          (guardedConfig State.gateStart
            (gatePrefix inputs gates [])
            (cell10 :: cell00 :: suffix)) := by
    rw [packedTokenCells_append]
    simpa [SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      cell00, cell10,
      SourceParser.cell00, SourceParser.cell10,
      List.append_assoc] using gatesRun
  have ending :=
    programEnd_exact inputs gates suffix
  exact
    exactRun_add
      (circuitGatesPrefixWordSteps inputs gates)
      (programEndSteps inputs gates)
      _ _ _ gatesCanonical ending

private def circuitOutputPrefixWordSteps
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) : Nat :=
  circuitProgramPrefixWordSteps inputs gates +
    (sourceCells output).length

private theorem circuitOutputPrefixWord_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) (suffix : List WorkSymbol) :
    workRunExact? machine
        (circuitOutputPrefixWordSteps inputs gates output)
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            (SourceParser.packedTokenCells
                (SourceParser.circuitOutputPrefixTokens
                  inputs gates output) ++ suffix))) =
      some
        (guardedConfig State.outputsEndFirst
          (outputPrefix inputs gates ++ sourceCells output)
          suffix) := by
  have program :=
    circuitProgramPrefixWord_exact inputs gates
      (sourceCells output ++ suffix)
  have programCanonical :
      workRunExact? machine
          (circuitProgramPrefixWordSteps inputs gates)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (SourceParser.circuitOutputPrefixTokens
                    inputs gates output) ++ suffix))) =
        some
          (guardedConfig (State.sourceStart .output)
            (outputPrefix inputs gates)
            (sourceCells output ++ suffix)) := by
    unfold SourceParser.circuitOutputPrefixTokens
    rw [packedTokenCells_append,
      SourceParser.packedTokenCells_encodeSourceTokens]
    simpa only [List.append_assoc] using program
  have outputRun :=
    sourceGuarded_exact .output output
      (outputPrefix inputs gates) suffix
  have all :=
    exactRun_add
      (circuitProgramPrefixWordSteps inputs gates)
      (sourceCells output).length
      _ _ _ programCanonical outputRun
  simpa [circuitOutputPrefixWordSteps,
    afterSourceState] using all

private theorem ordinaryCell_safe
    {symbol : WorkSymbol}
    (ordinary : ordinaryCell symbol) :
    symbol ≠ leftGuard ∧ symbol ≠ cellBlank := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst symbol <;> decide

private theorem safe_of_ordinary
    {word : List WorkSymbol}
    (ordinary :
      ∀ symbol, symbol ∈ word → ordinaryCell symbol) :
    SafeSourceWord word := by
  intro symbol member
  exact ordinaryCell_safe (ordinary symbol member)

private theorem borrowedCountCells_ordinary (used : Nat) :
    ∀ symbol, symbol ∈ borrowedCountCells used →
      ordinaryCell symbol := by
  intro symbol member
  apply countCells_ordinary used 0 symbol
  rw [countCells_eq_borrowed_append]
  exact List.mem_append_left (natCells 0) member

private def placeholderGate : RawGate :=
  { left := .constant false
    right := .constant false }

private def placeholderGates (count : Nat) :
    List RawGate :=
  List.replicate count placeholderGate

private def failureGatePrefix
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) : List WorkSymbol :=
  gatePrefix inputs done (placeholderGates remaining)

private theorem failureGatePrefix_succ
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (gate : RawGate) :
    failureGatePrefix inputs done (remaining + 1) =
      gatePrefix inputs done
        (gate :: placeholderGates remaining) := by
  simp [failureGatePrefix, placeholderGates,
    gatePrefix, SourceParser.gatePrefix]

private theorem gateParsingPrefix_ordinary
    (inputs : Nat) (done todo : List RawGate) :
    ∀ symbol,
      symbol ∈ gateParsingPrefix inputs done todo →
        ordinaryCell symbol := by
  intro symbol member
  unfold gateParsingPrefix at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · simp only [List.mem_cons,
          List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · exact cell00_ordinary
        · exact cell00_ordinary
        · contradiction
      · exact natCells_ordinary inputs symbol member
    · exact countCells_ordinary
        (done.length + 1) todo.length symbol member
  · exact markedGateListCells_ordinary done symbol member

private def gateFirstSteps
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) : Nat :=
  2 * (failureGatePrefix inputs done (remaining + 1)).length + 3

private theorem gateFirst_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (remaining : Nat)
    (current : WorkSymbol) (rest : List WorkSymbol) :
    workRunExact? machine
        (gateFirstSteps inputs done remaining)
        (guardedConfig State.gateStart
          (failureGatePrefix inputs done (remaining + 1))
          (firstSourceCell firstWas01 :: current :: rest)) =
      some
        (guardedConfig
          (afterFirstSourceState firstWas01 .gateLeft)
          (gateParsingPrefix inputs done
              (placeholderGates remaining) ++
            [firstSourceCell firstWas01])
          (current :: rest)) := by
  have base :=
    gateDecrement_exact firstWas01 inputs done
      placeholderGate (placeholderGates remaining)
      current rest
  simpa [gateFirstSteps,
    failureGatePrefix_succ inputs done remaining
      placeholderGate] using base

private def gateLeftSteps
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (left : RawSource) : Nat :=
  gateFirstSteps inputs done remaining +
    (sourceRemainderCells left).length

private theorem gateLeft_exact
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (left : RawSource)
    (suffix : List WorkSymbol) :
    workRunExact? machine
        (gateLeftSteps inputs done remaining left)
        (guardedConfig State.gateStart
          (failureGatePrefix inputs done (remaining + 1))
          (sourceCells left ++ suffix)) =
      some
        (guardedConfig (State.sourceStart .gateRight)
          (gateParsingPrefix inputs done
              (placeholderGates remaining) ++
            sourceCells left)
          suffix) := by
  have firstRun :=
    gateFirst_exact
      (sourceFirstWas01 left) inputs done remaining
      (sourceSecondCell left)
      (sourceAfterSecondCells left ++ suffix)
  have firstCanonical :
      workRunExact? machine
          (gateFirstSteps inputs done remaining)
          (guardedConfig State.gateStart
            (failureGatePrefix inputs done (remaining + 1))
            (sourceCells left ++ suffix)) =
        some
          (guardedConfig
            (afterFirstSourceState
              (sourceFirstWas01 left) .gateLeft)
            (gateParsingPrefix inputs done
                (placeholderGates remaining) ++
              [firstSourceCell
                (sourceFirstWas01 left)])
            (sourceRemainderCells left ++ suffix)) := by
    simpa [sourceCells_eq_first_remainder,
      sourceRemainderCells_eq_second,
      List.append_assoc] using firstRun
  have remainder :=
    sourceRemainder_exact .gateLeft left
      (gateParsingPrefix inputs done
        (placeholderGates remaining))
      suffix
  have all :=
    exactRun_add
      (gateFirstSteps inputs done remaining)
      (sourceRemainderCells left).length
      _ _ _ firstCanonical remainder
  simpa [gateLeftSteps, afterSourceState] using all

private def gateSourcesSteps
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (gate : RawGate) : Nat :=
  gateLeftSteps inputs done remaining gate.left +
    (sourceCells gate.right).length

private theorem gateSources_exact
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (gate : RawGate)
    (suffix : List WorkSymbol) :
    workRunExact? machine
        (gateSourcesSteps inputs done remaining gate)
        (guardedConfig State.gateStart
          (failureGatePrefix inputs done (remaining + 1))
          (sourceCells gate.left ++
            sourceCells gate.right ++ suffix)) =
      some
        (guardedConfig State.gateEndFirst
          (gateParsingPrefix inputs done
              (placeholderGates remaining) ++
            sourceCells gate.left ++
              sourceCells gate.right)
          suffix) := by
  have leftRun :=
    gateLeft_exact inputs done remaining gate.left
      (sourceCells gate.right ++ suffix)
  have rightRun :=
    sourceGuarded_exact .gateRight gate.right
      (gateParsingPrefix inputs done
          (placeholderGates remaining) ++
        sourceCells gate.left)
      suffix
  have all :=
    exactRun_add
      (gateLeftSteps inputs done remaining gate.left)
      (sourceCells gate.right).length
      _ _ _ (by
        simpa [List.append_assoc] using leftRun)
      rightRun
  simpa [gateSourcesSteps, afterSourceState,
    List.append_assoc] using all

private def gateRecordSteps
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (gate : RawGate) : Nat :=
  gateSourcesSteps inputs done remaining gate + 2

private theorem gateRecord_exact
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (gate : RawGate)
    (suffix : List WorkSymbol) :
    workRunExact? machine
        (gateRecordSteps inputs done remaining gate)
        (guardedConfig State.gateStart
          (failureGatePrefix inputs done (remaining + 1))
          (gateCells gate ++ suffix)) =
      some
        (guardedConfig State.gateStart
          (failureGatePrefix inputs (done ++ [gate])
            remaining)
          suffix) := by
  have sources :=
    gateSources_exact inputs done remaining gate
      ([cell01, cell11] ++ suffix)
  have ending :=
    gateEndGuarded_exact inputs done gate
      (placeholderGates remaining) suffix
  have all :=
    exactRun_add
      (gateSourcesSteps inputs done remaining gate)
      2 _ _ _ (by
        simpa [gateCells, SourceParser.gateCells,
          List.append_assoc, cell01, cell11,
          SourceParser.cell01, SourceParser.cell11]
          using sources)
      ending
  change
    workRunExact? machine
        (gateRecordSteps inputs done remaining gate)
        (guardedConfig State.gateStart
          (failureGatePrefix inputs done (remaining + 1))
          ((sourceCells gate.left ++
              sourceCells gate.right ++ [cell01, cell11]) ++
            suffix)) =
      some
        (guardedConfig State.gateStart
          (failureGatePrefix inputs (done ++ [gate])
            remaining)
          suffix)
  simpa [gateRecordSteps, failureGatePrefix,
    cell01, cell11, SourceParser.cell01,
    SourceParser.cell11, List.append_assoc] using all

set_option maxRecDepth 100000 in
private theorem gateDecrementCountEndFailure_exact
    (firstWas01 : Bool) (parsedPrefix : List WorkSymbol)
    (rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.gateDecrementCountFirst firstWas01)
          (pushCrossed parsedPrefix [leftGuard])
          (cell00 :: cell10 :: rest)) =
      some
        (cleanupSeekConfiguration
          []
          (cell10 ::
            pushCrossed (parsedPrefix ++ [cell00]) [])
          rest) := by
  unfold cleanupSeekConfiguration
  rw [pushCrossed_eq_reverse_append,
    pushCrossed_eq_reverse_append]
  simp only [List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_nil,
    List.cons_append]
  cases firstWas01 <;> rfl

set_option maxRecDepth 100000 in
private theorem programCountRemainingFailure_exact
    (parsedPrefix rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.programCountFirst
          (pushCrossed parsedPrefix [leftGuard])
          (cell00 :: cell01 :: rest)) =
      some
        (cleanupSeekConfiguration
          []
          (cell01 ::
            pushCrossed (parsedPrefix ++ [cell00]) [])
          rest) := by
  unfold cleanupSeekConfiguration
  rw [pushCrossed_eq_reverse_append,
    pushCrossed_eq_reverse_append]
  simp only [List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_nil,
    List.cons_append]
  rfl

set_option maxRecDepth 100000 in
private theorem sourceAfter00ImmediateFailure_exact
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not11 : current ≠ cell11) :
    workRunExact? machine 1
        (guardedConfig (State.sourceAfter00 .gateLeft)
          parsedPrefix (current :: rest)) =
      some
        (cleanupSeekConfiguration
          [] (current :: pushCrossed parsedPrefix []) rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.append_nil]
  simp only [cell11, WorkSymbol.oneOne] at not11
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | rfl
    | rfl
    | rfl
    | exact False.elim (not11 rfl)

set_option maxRecDepth 100000 in
private theorem sourceAfter01ImmediateFailure_exact
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not00 : current ≠ cell00)
    (not01 : current ≠ cell01)
    (not10 : current ≠ cell10) :
    workRunExact? machine 1
        (guardedConfig (State.sourceAfter01 .gateLeft)
          parsedPrefix (current :: rest)) =
      some
        (cleanupSeekConfiguration
          [] (current :: pushCrossed parsedPrefix []) rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.append_nil]
  simp only [cell00, cell01, cell10,
    WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneZero] at not00 not01 not10
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | exact False.elim (not00 rfl)
    | exact False.elim (not01 rfl)
    | exact False.elim (not10 rfl)
    | rfl

set_option maxRecDepth 100000 in
private theorem sourceAfter00NatLaunch_exact
    (parsedPrefix rest : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig (State.sourceAfter00 .gateLeft)
          parsedPrefix (cell11 :: rest)) =
      some
        (guardedConfig (State.sourceNatFirst .gateLeft)
          (parsedPrefix ++ [cell11]) rest) := by
  unfold guardedConfig
  rw [pushCrossed_append]
  rfl

set_option maxRecDepth 100000 in
private theorem sourceAfter01NatLaunch_exact
    (parsedPrefix rest : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig (State.sourceAfter01 .gateLeft)
          parsedPrefix (cell10 :: rest)) =
      some
        (guardedConfig (State.sourceNatFirst .gateLeft)
          (parsedPrefix ++ [cell10]) rest) := by
  unfold guardedConfig
  rw [pushCrossed_append]
  rfl

private theorem gateDecrementExhaustedForwardWord_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate)
    (word : List WorkSymbol)
    (wordSafe : SafeSourceWord word) :
    RejectingExecution
      (configAtWord
        (State.gateDecrementVersionFirst firstWas01)
        [leftGuard]
        (gatePrefix inputs done [] ++
          cursorMark :: word)) := by
  let initial :=
    configAtWord
      (State.gateDecrementVersionFirst firstWas01)
      [leftGuard]
      (gatePrefix inputs done [] ++
        cursorMark :: word)
  let afterHeader :=
    countCells done.length 0 ++
      markedGateListCells done ++
        cursorMark :: word
  let countPrefix :=
    [cell00, cell00] ++ natCells inputs ++
      borrowedCountCells done.length
  let failureRest :=
    markedGateListCells done ++
      cursorMark :: word
  have version :=
    gateDecrementVersion_exact firstWas01 [leftGuard]
      (natCells inputs ++ afterHeader)
  have versionCanonical :
      workRunExact? machine 2 initial =
        some
          (configAtWord
            (State.gateDecrementInputFirst firstWas01)
            [cell00, cell00, leftGuard]
            (natCells inputs ++ afterHeader)) := by
    simpa [initial, afterHeader, gatePrefix,
      SourceParser.gatePrefix, natCells, countCells,
      markedGateListCells, cell00,
      SourceParser.cell00, List.append_assoc] using version
  have input :=
    gateDecrementInput_exact firstWas01 inputs
      [cell00, cell00, leftGuard] afterHeader
  have borrowed :=
    gateDecrementBorrowed_exact firstWas01 done.length
      (pushCrossed (natCells inputs)
        [cell00, cell00, leftGuard])
      (cell00 :: cell10 :: failureRest)
  have borrowedCanonical :
      workRunExact? machine (2 * done.length)
          (configAtWord
            (State.gateDecrementCountFirst firstWas01)
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])
            afterHeader) =
        some
          (configAtWord
            (State.gateDecrementCountFirst firstWas01)
            (pushCrossed (borrowedCountCells done.length)
              (pushCrossed (natCells inputs)
                [cell00, cell00, leftGuard]))
            (cell00 :: cell10 :: failureRest)) := by
    simpa [afterHeader, failureRest,
      countCells_eq_borrowed_append,
      natCells, SourceParser.natCells,
      cell00, cell10, SourceParser.cell00,
      SourceParser.cell10, List.append_assoc] using borrowed
  have leftEq :
      pushCrossed (borrowedCountCells done.length)
          (pushCrossed (natCells inputs)
            [cell00, cell00, leftGuard]) =
        pushCrossed countPrefix [leftGuard] := by
    repeat rw [pushCrossed_eq_reverse_append]
    simp [countPrefix, List.reverse_append,
      List.append_assoc]
  have failed :=
    gateDecrementCountEndFailure_exact firstWas01
      countPrefix failureRest
  have failedCanonical :
      workRunExact? machine 2
          (configAtWord
            (State.gateDecrementCountFirst firstWas01)
            (pushCrossed (borrowedCountCells done.length)
              (pushCrossed (natCells inputs)
                [cell00, cell00, leftGuard]))
            (cell00 :: cell10 :: failureRest)) =
        some
          (cleanupSeekConfiguration
            []
            (cell10 ::
              pushCrossed (countPrefix ++ [cell00]) [])
            failureRest) := by
    rw [leftEq]
    exact failed
  have throughInput :=
    exactRun_add 2 (2 * (inputs + 1))
      _ _ _ versionCanonical input
  have throughBorrowed :=
    exactRun_add (2 + 2 * (inputs + 1))
      (2 * done.length) _ _ _
      throughInput borrowedCanonical
  have launch :=
    exactRun_add
      ((2 + 2 * (inputs + 1)) +
        2 * done.length)
      2 _ _ _ throughBorrowed failedCanonical
  have countPrefixOrdinary :
      ∀ symbol, symbol ∈ countPrefix →
        ordinaryCell symbol := by
    dsimp [countPrefix]
    change
      ∀ symbol,
        symbol ∈
            (([cell00, cell00] ++ natCells inputs) ++
              borrowedCountCells done.length) →
          ordinaryCell symbol
    apply ordinary_append
    · apply ordinary_append
      · intro symbol member
        simp only [List.mem_cons,
          List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · exact cell00_ordinary
        · exact cell00_ordinary
        · contradiction
      · exact natCells_ordinary inputs
    · exact borrowedCountCells_ordinary done.length
  have parsedSafe :
      SafeSourceWord (countPrefix ++ [cell00]) :=
    safe_of_ordinary
      (ordinary_append countPrefixOrdinary
        (by
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell00_ordinary
          · contradiction))
  have markedAndCursorSafe :
      SafeSourceWord
        (markedGateListCells done ++ [cursorMark]) := by
    apply safe_append
    · exact safe_of_ordinary
        (markedGateListCells_ordinary done)
    · intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | impossible
      · decide
      · contradiction
  have restSafe : SafeSourceWord failureRest := by
    dsimp [failureRest]
    simpa [List.append_assoc] using
      safe_append markedAndCursorSafe wordSafe
  have internalSafe :
      SafeSourceWord
        ((countPrefix ++ [cell00]) ++
          cell10 :: failureRest) := by
    apply safe_append parsedSafe
    change SafeSourceWord ([cell10] ++ failureRest)
    apply safe_append
    · intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | impossible
      · decide
      · contradiction
    · exact restSafe
  exact
    safeExplicitFailure_exact
      ((countPrefix ++ [cell00]) ++
        cell10 :: failureRest)
      (countPrefix ++ [cell00])
      cell10 failureRest initial
      (((2 + 2 * (inputs + 1)) +
        2 * done.length) + 2)
      rfl internalSafe launch

private theorem gateDecrementExhaustedWord_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate)
    (word : List WorkSymbol)
    (wordSafe : SafeSourceWord word) :
    RejectingExecution
      (guardedConfig State.gateStart
        (gatePrefix inputs done [])
        (firstSourceCell firstWas01 :: word)) := by
  let logicalPrefix := gatePrefix inputs done []
  have launch :=
    gateStartLaunchWord_exact firstWas01 logicalPrefix word
  have backward :=
    gateDecrementSeekGuard_scan_exact firstWas01 logicalPrefix
      (cursorMark :: word)
      (gatePrefix_ordinary inputs done [])
  have guard :=
    gateDecrementGuard_exact firstWas01
      (logicalPrefix ++ cursorMark :: word)
  have throughBackward :=
    exactRun_add 1 logicalPrefix.length
      _ _ _ launch backward
  have throughGuard :=
    exactRun_add (1 + logicalPrefix.length) 1
      _ _ _ throughBackward guard
  exact
    RejectingExecution.prepend
      ((1 + logicalPrefix.length) + 1)
      _ _
      (by simpa [logicalPrefix] using throughGuard)
      (gateDecrementExhaustedForwardWord_exact
        firstWas01 inputs done word wordSafe)

private theorem gateDecrementExhausted_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (tailSafe : SafeSourceWord (current :: rest)) :
    RejectingExecution
      (guardedConfig State.gateStart
        (gatePrefix inputs done [])
        (firstSourceCell firstWas01 :: current :: rest)) := by
  exact
    gateDecrementExhaustedWord_exact
      firstWas01 inputs done (current :: rest) tailSafe

private theorem gateFirstWord_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (remaining : Nat)
    (word : List WorkSymbol) :
    workRunExact? machine
        (gateFirstSteps inputs done remaining)
        (guardedConfig State.gateStart
          (failureGatePrefix inputs done (remaining + 1))
          (firstSourceCell firstWas01 :: word)) =
      some
        (guardedConfig
          (afterFirstSourceState firstWas01 .gateLeft)
          (gateParsingPrefix inputs done
              (placeholderGates remaining) ++
            [firstSourceCell firstWas01])
          word) := by
  have base :=
    gateDecrementWord_exact firstWas01 inputs done
      placeholderGate (placeholderGates remaining) word
  simpa [gateFirstSteps,
    failureGatePrefix_succ inputs done remaining
      placeholderGate] using base

private theorem sourceAfterFirstMissingFailure_exact
    (firstWas01 : Bool)
    (parsedPrefix : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig
          (afterFirstSourceState firstWas01 .gateLeft)
          parsedPrefix []) =
      some
        (cleanupSeekConfiguration
          [] (missingEndScan
            (pushCrossed parsedPrefix [])) []) := by
  unfold guardedConfig cleanupSeekConfiguration missingEndScan
  rw [pushCrossed_eq_reverse_append,
    pushCrossed_eq_reverse_append]
  simp only [List.append_nil]
  cases firstWas01 <;> rfl

private theorem gateFirstParsedPrefix_safe
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (remaining : Nat) :
    SafeSourceWord
      (gateParsingPrefix inputs done
          (placeholderGates remaining) ++
        [firstSourceCell firstWas01]) := by
  apply safe_of_ordinary
  apply ordinary_append
    (gateParsingPrefix_ordinary inputs done
      (placeholderGates remaining))
  intro symbol member
  simp only [List.mem_cons,
    List.not_mem_nil] at member
  rcases member with rfl | impossible
  · cases firstWas01
    · exact cell00_ordinary
    · exact cell01_ordinary
  · contradiction

private theorem gateMalformedFirstEOF_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (count : Nat) :
    RejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done count)
        [firstSourceCell firstWas01]) := by
  cases count with
  | zero =>
      exact
        gateDecrementExhaustedWord_exact
          firstWas01 inputs done []
          (by
            intro symbol member
            contradiction)
  | succ remaining =>
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates remaining) ++
          [firstSourceCell firstWas01]
      have prefixRun :=
        gateFirstWord_exact
          firstWas01 inputs done remaining []
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        exact gateFirstParsedPrefix_safe
          firstWas01 inputs done remaining
      have failed :=
        sourceAfterFirstMissingFailure_exact
          firstWas01 parsedPrefix
      have cleanup :=
        cleanupMissingSeek_rejecting_exact
          parsedPrefix parsedSafe
      have tail :
          RejectingExecution
            (guardedConfig
              (afterFirstSourceState firstWas01 .gateLeft)
              parsedPrefix []) := by
        exact
          RejectingExecution.prepend 1 _ _ failed cleanup
      exact
        RejectingExecution.prepend
          (gateFirstSteps inputs done remaining)
          _ _ (by simpa [parsedPrefix] using prefixRun) tail

private theorem gateMalformedFirstDangling_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (count : Nat)
    (bit : Bool) :
    RejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done count)
        [firstSourceCell firstWas01,
          SourceParser.danglingWorkCell bit]) := by
  have danglingSafe :
      SafeSourceWord
        [SourceParser.danglingWorkCell bit] := by
    intro symbol member
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at member
    subst symbol
    cases bit <;> decide
  cases count with
  | zero =>
      exact
        gateDecrementExhaustedWord_exact
          firstWas01 inputs done
          [SourceParser.danglingWorkCell bit]
          danglingSafe
  | succ remaining =>
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates remaining) ++
          [firstSourceCell firstWas01]
      have prefixRun :=
        gateFirstWord_exact
          firstWas01 inputs done remaining
          [SourceParser.danglingWorkCell bit]
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        exact gateFirstParsedPrefix_safe
          firstWas01 inputs done remaining
      have tail :
          RejectingExecution
            (guardedConfig
              (afterFirstSourceState firstWas01 .gateLeft)
              parsedPrefix
              [SourceParser.danglingWorkCell bit]) := by
        cases firstWas01
        · exact
            safeExplicitFailure_exact
              (parsedPrefix ++
                [SourceParser.danglingWorkCell bit])
              parsedPrefix
              (SourceParser.danglingWorkCell bit) []
              (guardedConfig
                (State.sourceAfter00 .gateLeft)
                parsedPrefix
                [SourceParser.danglingWorkCell bit])
              1 rfl
              (safe_append parsedSafe danglingSafe)
              (sourceAfter00ImmediateFailure_exact
                parsedPrefix
                (SourceParser.danglingWorkCell bit) []
                (by cases bit <;> decide))
        · exact
            safeExplicitFailure_exact
              (parsedPrefix ++
                [SourceParser.danglingWorkCell bit])
              parsedPrefix
              (SourceParser.danglingWorkCell bit) []
              (guardedConfig
                (State.sourceAfter01 .gateLeft)
                parsedPrefix
                [SourceParser.danglingWorkCell bit])
              1 rfl
              (safe_append parsedSafe danglingSafe)
              (sourceAfter01ImmediateFailure_exact
                parsedPrefix
                (SourceParser.danglingWorkCell bit) []
                (by cases bit <;> decide)
                (by cases bit <;> decide)
                (by cases bit <;> decide))
      exact
        RejectingExecution.prepend
          (gateFirstSteps inputs done remaining)
          _ _ (by simpa [parsedPrefix] using prefixRun) tail

set_option maxRecDepth 100000 in
private theorem gateStartCell11Failure_exact
    (parsedPrefix rest : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig State.gateStart parsedPrefix
          (cell11 :: rest)) =
      some
        (cleanupSeekConfiguration
          [] (cell11 :: pushCrossed parsedPrefix [])
          rest) := by
  rw [guardedConfig_eq_crossed]
  rfl

set_option maxRecDepth 100000 in
private theorem gateStartDanglingFailure_exact
    (parsedPrefix : List WorkSymbol) (bit : Bool) :
    workRunExact? machine 1
        (guardedConfig State.gateStart parsedPrefix
          [SourceParser.danglingWorkCell bit]) =
      some
        (cleanupSeekConfiguration
          [] (SourceParser.danglingWorkCell bit ::
            pushCrossed parsedPrefix [])
          []) := by
  rw [guardedConfig_eq_crossed]
  cases bit <;> rfl

set_option maxRecDepth 100000 in
private theorem gateStartProgramEOFFailure_exact
    (parsedPrefix : List WorkSymbol) :
    workRunExact? machine 2
        (guardedConfig State.gateStart parsedPrefix [cell10]) =
      some
        (cleanupSeekConfiguration
          [] (cellBlank ::
            pushCrossed (parsedPrefix ++ [cursorMark]) [])
          []) := by
  rw [guardedConfig_eq_crossed]
  simp [pushCrossed_append, pushCrossed]
  cases pushCrossed parsedPrefix [] <;> rfl

set_option maxRecDepth 100000 in
private theorem gateStartProgramSecondFramingFailure_exact
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not00 : current ≠ cell00) :
    workRunExact? machine 2
        (guardedConfig State.gateStart parsedPrefix
          (cell10 :: current :: rest)) =
      some
        (cleanupSeekConfiguration
          []
          (current ::
            pushCrossed (parsedPrefix ++ [cursorMark]) [])
          rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_nil,
    List.cons_append]
  simp only [cell00, WorkSymbol.zeroZero] at not00
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | exact False.elim (not00 rfl)
    | rfl

private theorem gateStartProgramSecondFramingRejecting_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (tailSafe : SafeSourceWord (current :: rest))
    (not00 : current ≠ cell00) :
    RejectingExecution
      (guardedConfig State.gateStart parsedPrefix
        (cell10 :: current :: rest)) := by
  let parsedAfterCursor := parsedPrefix ++ [cursorMark]
  have cursorSafe : SafeSourceWord [cursorMark] := by
    intro symbol member
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at member
    subst symbol
    decide
  exact
    safeExplicitFailure_exact
      (parsedAfterCursor ++ current :: rest)
      parsedAfterCursor current rest
      (guardedConfig State.gateStart parsedPrefix
        (cell10 :: current :: rest))
      2 rfl
      (safe_append
        (safe_append prefixSafe cursorSafe)
        tailSafe)
      (gateStartProgramSecondFramingFailure_exact
        parsedPrefix current rest not00)

private theorem failureGatePrefix_safe
    (inputs : Nat) (done : List RawGate)
    (count : Nat) :
    SafeSourceWord
      (failureGatePrefix inputs done count) := by
  apply safe_of_ordinary
  dsimp [failureGatePrefix]
  exact gatePrefix_ordinary inputs done
    (placeholderGates count)

private theorem gateMalformedTail_exact
    (inputs : Nat) (done : List RawGate)
    (count : Nat)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done count)
        workTail) := by
  let parsedPrefix := failureGatePrefix inputs done count
  have parsedSafe : SafeSourceWord parsedPrefix :=
    failureGatePrefix_safe inputs done count
  cases malformed with
  | reserved third fourth suffix =>
      let rest :=
        SourceParser.boolPairWorkCell third fourth ::
          SourceParser.packedRawBits suffix
      let word := cell11 :: rest
      have launch :
          BoundaryCleanupLaunch State.gateStart
            parsedPrefix word := by
        apply boundaryCleanupLaunch_immediate
        exact gateStartCell11Failure_exact
          parsedPrefix rest
      exact
        boundaryCleanupLaunch_rejecting_exact
          State.gateStart parsedPrefix word
          parsedSafe
          (malformedWorkTail_safe
            (SourceParser.MalformedWorkTail.reserved
              third fourth suffix))
          launch
  | trailingOne bit =>
      let word := [SourceParser.danglingWorkCell bit]
      have launch :
          BoundaryCleanupLaunch State.gateStart
            parsedPrefix word := by
        apply boundaryCleanupLaunch_immediate
        exact gateStartDanglingFailure_exact
          parsedPrefix bit
      exact
        boundaryCleanupLaunch_rejecting_exact
          State.gateStart parsedPrefix word
          parsedSafe
          (malformedWorkTail_safe
            (SourceParser.MalformedWorkTail.trailingOne bit))
          launch
  | trailingTwo first second =>
      cases first <;> cases second
      · exact gateMalformedFirstEOF_exact
          false inputs done count
      · exact gateMalformedFirstEOF_exact
          true inputs done count
      · let word := [cell10]
        have launch :
            BoundaryCleanupLaunch State.gateStart
              parsedPrefix word := by
          apply boundaryCleanupLaunch_eof_rewritten
            (stored := cursorMark)
          · intro symbol member
            simp only [List.mem_cons,
              List.not_mem_nil, or_false] at member
            subst symbol
            decide
          · exact gateStartProgramEOFFailure_exact
              parsedPrefix
        exact
          boundaryCleanupLaunch_rejecting_exact
            State.gateStart parsedPrefix word
            parsedSafe
            (malformedWorkTail_safe
              (SourceParser.MalformedWorkTail.trailingTwo
                true false))
            launch
      · let word := [cell11]
        have launch :
            BoundaryCleanupLaunch State.gateStart
              parsedPrefix word := by
          apply boundaryCleanupLaunch_immediate
          exact gateStartCell11Failure_exact
            parsedPrefix []
        exact
          boundaryCleanupLaunch_rejecting_exact
            State.gateStart parsedPrefix word
            parsedSafe
            (malformedWorkTail_safe
              (SourceParser.MalformedWorkTail.trailingTwo
                true true))
            launch
  | trailingThree first second third =>
      cases first <;> cases second
      · exact gateMalformedFirstDangling_exact
          false inputs done count third
      · exact gateMalformedFirstDangling_exact
          true inputs done count third
      · have danglingSafe :
            SafeSourceWord
              [SourceParser.danglingWorkCell third] := by
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil, or_false] at member
          subst symbol
          cases third <;> decide
        exact
          gateStartProgramSecondFramingRejecting_exact
            parsedPrefix parsedSafe
            (SourceParser.danglingWorkCell third) []
            danglingSafe
            (by cases third <;> decide)
      · let word :=
          [cell11, SourceParser.danglingWorkCell third]
        have launch :
            BoundaryCleanupLaunch State.gateStart
              parsedPrefix word := by
          apply boundaryCleanupLaunch_immediate
          exact gateStartCell11Failure_exact
            parsedPrefix
              [SourceParser.danglingWorkCell third]
        exact
          boundaryCleanupLaunch_rejecting_exact
            State.gateStart parsedPrefix word
            parsedSafe
            (malformedWorkTail_safe
              (SourceParser.MalformedWorkTail.trailingThree
                true true third))
            launch

set_option maxRecDepth 100000 in
private theorem programEndSecondFailure_exact
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not00 : current ≠ cell00) :
    workRunExact? machine 2
        (guardedConfig State.gateStart
          parsedPrefix (cell10 :: current :: rest)) =
      some
        (cleanupSeekConfiguration
          []
          (current ::
            pushCrossed (parsedPrefix ++ [cursorMark]) [])
          rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_nil,
    List.cons_append]
  simp only [cell00, WorkSymbol.zeroZero] at not00
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | exact False.elim (not00 rfl)
    | rfl

set_option maxRecDepth 100000 in
private theorem gateEndFirstFailure_exact
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not01 : current ≠ cell01) :
    workRunExact? machine 1
        (guardedConfig State.gateEndFirst
          parsedPrefix (current :: rest)) =
      some
        (cleanupSeekConfiguration
          [] (current :: pushCrossed parsedPrefix []) rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.append_nil]
  simp only [cell01, WorkSymbol.zeroOne] at not01
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | rfl
    | exact False.elim (not01 rfl)

set_option maxRecDepth 100000 in
private theorem gateEndSecondFailure_exact
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not11 : current ≠ cell11) :
    workRunExact? machine 2
        (guardedConfig State.gateEndFirst
          parsedPrefix (cell01 :: current :: rest)) =
      some
        (cleanupSeekConfiguration
          []
          (current ::
            pushCrossed (parsedPrefix ++ [gateMark]) [])
          rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_nil,
    List.cons_append]
  simp only [cell11, WorkSymbol.oneOne] at not11
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | rfl
    | rfl
    | rfl
    | exact False.elim (not11 rfl)

private theorem programEndSecondRejecting_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (tailSafe : SafeSourceWord (current :: rest))
    (not00 : current ≠ cell00) :
    RejectingExecution
      (guardedConfig State.gateStart parsedPrefix
        (cell10 :: current :: rest)) := by
  let initial :=
    guardedConfig State.gateStart parsedPrefix
      (cell10 :: current :: rest)
  let parsedAfterCursor :=
    parsedPrefix ++ [cursorMark]
  have launch :=
    programEndSecondFailure_exact parsedPrefix
      current rest not00
  have cursorSafe : SafeSourceWord [cursorMark] := by
    intro symbol member
    simp only [List.mem_cons,
      List.not_mem_nil] at member
    rcases member with rfl | impossible
    · decide
    · contradiction
  have internalSafe :
      SafeSourceWord
        (parsedAfterCursor ++ current :: rest) := by
    exact safe_append
      (safe_append prefixSafe cursorSafe) tailSafe
  exact
    safeExplicitFailure_exact
      (parsedAfterCursor ++ current :: rest)
      parsedAfterCursor current rest initial 2 rfl
      internalSafe
      (by
        simpa [initial, parsedAfterCursor] using launch)

private theorem sourceAfter00Rejecting_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (tailSafe : SafeSourceWord (current :: rest))
    (not11 : current ≠ cell11) :
    RejectingExecution
      (guardedConfig (State.sourceAfter00 .gateLeft)
        parsedPrefix (current :: rest)) := by
  let initial :=
    guardedConfig (State.sourceAfter00 .gateLeft)
      parsedPrefix (current :: rest)
  have launch :=
    sourceAfter00ImmediateFailure_exact
      parsedPrefix current rest not11
  exact
    safeExplicitFailure_exact
      (parsedPrefix ++ current :: rest)
      parsedPrefix current rest initial 1 rfl
      (safe_append prefixSafe tailSafe)
      (by simpa [initial] using launch)

private theorem sourceAfter01Rejecting_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (tailSafe : SafeSourceWord (current :: rest))
    (not00 : current ≠ cell00)
    (not01 : current ≠ cell01)
    (not10 : current ≠ cell10) :
    RejectingExecution
      (guardedConfig (State.sourceAfter01 .gateLeft)
        parsedPrefix (current :: rest)) := by
  let initial :=
    guardedConfig (State.sourceAfter01 .gateLeft)
      parsedPrefix (current :: rest)
  have launch :=
    sourceAfter01ImmediateFailure_exact
      parsedPrefix current rest not00 not01 not10
  exact
    safeExplicitFailure_exact
      (parsedPrefix ++ current :: rest)
      parsedPrefix current rest initial 1 rfl
      (safe_append prefixSafe tailSafe)
      (by simpa [initial] using launch)

private theorem programCountRemainingRejecting_exact
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat)
    (tail : List WorkSymbol)
    (tailSafe : SafeSourceWord tail) :
    RejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done (remaining + 1))
        (cell10 :: cell00 :: tail)) := by
  let logicalPrefix :=
    failureGatePrefix inputs done (remaining + 1)
  let initial :=
    guardedConfig State.gateStart logicalPrefix
      (cell10 :: cell00 :: tail)
  let afterCount :=
    markedGateListCells done ++
      cursorMark :: cell00 :: tail
  let afterHeader :=
    countCells done.length (remaining + 1) ++ afterCount
  let countPrefix :=
    [cell00, cell00] ++ natCells inputs ++
      programCountUnitCells done.length
  let failureRest :=
    natCells remaining ++ afterCount
  have launch :=
    programEndLaunch_exact logicalPrefix tail
  have cursorLeft :=
    programSeekGuardCursor_exact
      (logicalPrefix.reverse ++ [leftGuard])
      (cell00 :: tail)
  have backward :=
    programSeekGuard_scan_exact logicalPrefix
      (cursorMark :: cell00 :: tail)
      (by
        dsimp [logicalPrefix, failureGatePrefix]
        exact gatePrefix_ordinary inputs done
          (placeholderGates (remaining + 1)))
  have guard :=
    programSeekGuard_exact
      (logicalPrefix ++
        cursorMark :: cell00 :: tail)
  have version :=
    programSkipVersion_exact [leftGuard]
      (natCells inputs ++ afterHeader)
  have versionCanonical :
      workRunExact? machine 2
          (configAtWord State.programSkipVersionFirst
            [leftGuard]
            (logicalPrefix ++
              cursorMark :: cell00 :: tail)) =
        some
          (configAtWord State.programSkipInputFirst
            [cell00, cell00, leftGuard]
            (natCells inputs ++ afterHeader)) := by
    simpa [logicalPrefix, failureGatePrefix,
      placeholderGates, gatePrefix,
      SourceParser.gatePrefix, afterHeader,
      afterCount, natCells, countCells,
      markedGateListCells, cell00,
      SourceParser.cell00, List.append_assoc]
      using version
  have input :=
    programSkipInput_exact inputs
      [cell00, cell00, leftGuard] afterHeader
  have markers :=
    programCountMarkers_exact done.length
      (pushCrossed (natCells inputs)
        [cell00, cell00, leftGuard])
      (cell00 :: cell01 :: failureRest)
  have markersCanonical :
      workRunExact? machine (2 * done.length)
          (configAtWord State.programCountFirst
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])
            afterHeader) =
        some
          (configAtWord State.programCountFirst
            (pushCrossed (programCountUnitCells done.length)
              (pushCrossed (natCells inputs)
                [cell00, cell00, leftGuard]))
            (cell00 :: cell01 :: failureRest)) := by
    simpa [afterHeader, afterCount, failureRest,
      countCells_succ_remaining,
      List.append_assoc] using markers
  have leftEq :
      pushCrossed (programCountUnitCells done.length)
          (pushCrossed (natCells inputs)
            [cell00, cell00, leftGuard]) =
        pushCrossed countPrefix [leftGuard] := by
    repeat rw [pushCrossed_eq_reverse_append]
    simp [countPrefix, List.reverse_append,
      List.append_assoc]
  have failed :=
    programCountRemainingFailure_exact
      countPrefix failureRest
  have failedCanonical :
      workRunExact? machine 2
          (configAtWord State.programCountFirst
            (pushCrossed (programCountUnitCells done.length)
              (pushCrossed (natCells inputs)
                [cell00, cell00, leftGuard]))
            (cell00 :: cell01 :: failureRest)) =
        some
          (cleanupSeekConfiguration
            []
            (cell01 ::
              pushCrossed (countPrefix ++ [cell00]) [])
            failureRest) := by
    rw [leftEq]
    exact failed
  have throughCursorLeft :=
    exactRun_add 2 1 _ _ _ launch cursorLeft
  have throughBackward :=
    exactRun_add (2 + 1) logicalPrefix.length
      _ _ _ throughCursorLeft backward
  have throughGuard :=
    exactRun_add ((2 + 1) + logicalPrefix.length) 1
      _ _ _ throughBackward guard
  have throughVersion :=
    exactRun_add
      (((2 + 1) + logicalPrefix.length) + 1)
      2 _ _ _ throughGuard versionCanonical
  have throughInput :=
    exactRun_add
      ((((2 + 1) + logicalPrefix.length) + 1) + 2)
      (2 * (inputs + 1))
      _ _ _ throughVersion input
  have throughMarkers :=
    exactRun_add
      (((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1))
      (2 * done.length)
      _ _ _ throughInput markersCanonical
  have failedRun :=
    exactRun_add
      ((((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1)) + 2 * done.length)
      2 _ _ _ throughMarkers failedCanonical
  have countPrefixOrdinary :
      ∀ symbol, symbol ∈ countPrefix →
        ordinaryCell symbol := by
    dsimp [countPrefix]
    change
      ∀ symbol,
        symbol ∈
            (([cell00, cell00] ++ natCells inputs) ++
              programCountUnitCells done.length) →
          ordinaryCell symbol
    apply ordinary_append
    · apply ordinary_append
      · intro symbol member
        simp only [List.mem_cons,
          List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · exact cell00_ordinary
        · exact cell00_ordinary
        · contradiction
      · exact natCells_ordinary inputs
    · exact programCountUnitCells_ordinary done.length
  have parsedSafe :
      SafeSourceWord (countPrefix ++ [cell00]) :=
    safe_of_ordinary
      (ordinary_append countPrefixOrdinary
        (by
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell00_ordinary
          · contradiction))
  have afterCountSafe : SafeSourceWord afterCount := by
    have markedSafe :=
      safe_of_ordinary
        (markedGateListCells_ordinary done)
    have cursorAndSecondSafe :
        SafeSourceWord [cursorMark, cell00] := by
      intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | rfl | impossible
      · decide
      · decide
      · contradiction
    dsimp [afterCount]
    simpa [List.append_assoc] using
      safe_append
        (safe_append markedSafe cursorAndSecondSafe)
        tailSafe
  have failureRestSafe : SafeSourceWord failureRest := by
    dsimp [failureRest]
    exact safe_append
      (safe_of_ordinary
        (natCells_ordinary remaining))
      afterCountSafe
  have internalSafe :
      SafeSourceWord
        ((countPrefix ++ [cell00]) ++
          cell01 :: failureRest) := by
    apply safe_append parsedSafe
    change SafeSourceWord ([cell01] ++ failureRest)
    apply safe_append
    · intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | impossible
      · decide
      · contradiction
    · exact failureRestSafe
  exact
    safeExplicitFailure_exact
      ((countPrefix ++ [cell00]) ++
        cell01 :: failureRest)
      (countPrefix ++ [cell00])
      cell01 failureRest initial
      (((((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1)) + 2 * done.length) + 2)
      rfl internalSafe
      (by simpa [initial] using failedRun)

private theorem missingExpected_exact
    (state : Nat) (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (failure :
      workRunExact? machine 1
          (guardedConfig state parsedPrefix []) =
        some
          (cleanupSeekConfiguration
            [] (missingEndScan
              (pushCrossed parsedPrefix [])) [])) :
    RejectingExecution
      (guardedConfig state parsedPrefix []) := by
  let crossed := pushCrossed parsedPrefix []
  have tail :=
    missingEndTail_exact state parsedPrefix crossed
      rfl prefixSafe (by
        unfold guardedConfig at failure
        rw [pushCrossed_eq_reverse_append] at failure
        simpa [crossed, pushCrossed_eq_reverse_append] using failure)
  refine
    ⟨missingEndTailSteps crossed,
      cleanupExplicitRejectConfiguration
        [] (missingEndEraseWord crossed) [],
      ?_, ?_, rfl, ?_⟩
  · unfold guardedConfig
    rw [pushCrossed_eq_reverse_append]
    simpa [crossed, pushCrossed_eq_reverse_append] using tail
  · exact cleanupExplicitReject_isHalted
      [] (missingEndEraseWord crossed) []
  · exact cleanupExplicitReject_output_empty
      [] (missingEndEraseWord crossed)

private theorem tokenExplicitFailure_exact
    (basePrefix parsedPrefix : List WorkSymbol)
    (token : Token) (suffix : List Token)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (initial : WorkConfiguration) (launchSteps : Nat)
    (prefixSafe : SafeSourceWord basePrefix)
    (shape :
      basePrefix ++
          SourceParser.packedTokenCells (token :: suffix) =
        parsedPrefix ++ current :: rest)
    (launch :
      workRunExact? machine launchSteps initial =
        some
          (cleanupSeekConfiguration
            [] (current :: pushCrossed parsedPrefix []) rest)) :
    RejectingExecution initial := by
  exact
    safeExplicitFailure_exact
      (basePrefix ++
        SourceParser.packedTokenCells (token :: suffix))
      parsedPrefix current rest initial launchSteps shape
      (safe_append prefixSafe
        (packedTokenCells_safe (token :: suffix)))
      launch

set_option maxRecDepth 100000 in
private theorem versionFirstFailure_exact
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not00 : current ≠ cell00) :
    workRunExact? machine 1
        (guardedConfig State.versionFirst []
          (current :: rest)) =
      some
        (cleanupSeekConfiguration [] [current] rest) := by
  simp only [cell00, WorkSymbol.zeroZero] at not00
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | exact False.elim (not00 rfl)
    | rfl

set_option maxRecDepth 100000 in
private theorem versionSecondFailure_exact
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not00 : current ≠ cell00) :
    workRunExact? machine 1
        (guardedConfig State.versionSecond [cell00]
          (current :: rest)) =
      some
        (cleanupSeekConfiguration
          [] (current :: pushCrossed [cell00] []) rest) := by
  simp only [cell00, WorkSymbol.zeroZero] at not00
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | exact False.elim (not00 rfl)
    | rfl

set_option maxRecDepth 100000 in
private theorem versionSecondFromFirstFailure_exact
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not00 : current ≠ cell00) :
    workRunExact? machine 2
        (guardedConfig State.versionFirst []
          (cell00 :: current :: rest)) =
      some
        (cleanupSeekConfiguration
          [] (current :: pushCrossed [cell00] []) rest) := by
  simp only [cell00, WorkSymbol.zeroZero] at not00
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | exact False.elim (not00 rfl)
    | rfl

set_option maxRecDepth 100000 in
private theorem outputsEndFirstFailure_exact
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not10 : current ≠ cell10) :
    workRunExact? machine 1
        (guardedConfig State.outputsEndFirst
          parsedPrefix (current :: rest)) =
      some
        (cleanupSeekConfiguration
          [] (current :: pushCrossed parsedPrefix []) rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.append_nil]
  simp only [cell10, WorkSymbol.oneZero] at not10
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | exact False.elim (not10 rfl)
    | rfl

set_option maxRecDepth 100000 in
private theorem outputsEndSecondFailure_exact
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not01 : current ≠ cell01) :
    workRunExact? machine 2
        (guardedConfig State.outputsEndFirst
          parsedPrefix (cell10 :: current :: rest)) =
      some
        (cleanupSeekConfiguration
          []
          (current ::
            pushCrossed (parsedPrefix ++ [cell10]) [])
          rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_nil,
    List.cons_append]
  simp only [cell01, WorkSymbol.zeroOne] at not01
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | rfl
    | exact False.elim (not01 rfl)

set_option maxRecDepth 100000 in
private theorem instanceEndFirstFailure_exact
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not10 : current ≠ cell10) :
    workRunExact? machine 1
        (guardedConfig State.instanceEndFirst
          parsedPrefix (current :: rest)) =
      some
        (cleanupSeekConfiguration
          [] (current :: pushCrossed parsedPrefix []) rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.append_nil]
  simp only [cell10, WorkSymbol.oneZero] at not10
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | exact False.elim (not10 rfl)
    | rfl

set_option maxRecDepth 100000 in
private theorem instanceEndSecondFailure_exact
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (not11 : current ≠ cell11) :
    workRunExact? machine 2
        (guardedConfig State.instanceEndFirst
          parsedPrefix (cell10 :: current :: rest)) =
      some
        (cleanupSeekConfiguration
          []
          (current ::
            pushCrossed (parsedPrefix ++ [cell10]) [])
          rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_nil,
    List.cons_append]
  simp only [cell11, WorkSymbol.oneOne] at not11
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | rfl
    | rfl
    | rfl
    | exact False.elim (not11 rfl)

set_option maxRecDepth 100000 in
private theorem finalEOFFailure_exact
    (parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (notBlank : current ≠ cellBlank) :
    workRunExact? machine 1
        (guardedConfig State.finalEOF
          parsedPrefix (current :: rest)) =
      some
        (cleanupSeekConfiguration
          [] (current :: pushCrossed parsedPrefix []) rest) := by
  unfold guardedConfig cleanupSeekConfiguration
  simp only [pushCrossed_eq_reverse_append,
    List.append_nil]
  simp only [cellBlank, WorkSymbol.blank] at notBlank
  rcases current with ⟨first, second⟩
  cases first <;> cases second <;>
    first
    | exact False.elim (notBlank rfl)
    | rfl

private theorem outputsEndMissingFailure_exact
    (parsedPrefix : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig State.outputsEndFirst parsedPrefix []) =
      some
        (cleanupSeekConfiguration
          [] (missingEndScan
            (pushCrossed parsedPrefix [])) []) := by
  unfold guardedConfig cleanupSeekConfiguration missingEndScan
  rw [pushCrossed_eq_reverse_append,
    pushCrossed_eq_reverse_append]
  simp only [List.append_nil]
  rfl

private theorem instanceEndMissingFailure_exact
    (parsedPrefix : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig State.instanceEndFirst parsedPrefix []) =
      some
        (cleanupSeekConfiguration
          [] (missingEndScan
            (pushCrossed parsedPrefix [])) []) := by
  unfold guardedConfig cleanupSeekConfiguration missingEndScan
  rw [pushCrossed_eq_reverse_append,
    pushCrossed_eq_reverse_append]
  simp only [List.append_nil]
  rfl

private theorem gateStartMissingFailure_exact
    (parsedPrefix : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig State.gateStart parsedPrefix []) =
      some
        (cleanupSeekConfiguration
          [] (missingEndScan
            (pushCrossed parsedPrefix [])) []) := by
  unfold guardedConfig cleanupSeekConfiguration missingEndScan
  rw [pushCrossed_eq_reverse_append,
    pushCrossed_eq_reverse_append]
  simp only [List.append_nil]
  rfl

private theorem gateEndMissingFailure_exact
    (parsedPrefix : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig State.gateEndFirst parsedPrefix []) =
      some
        (cleanupSeekConfiguration
          [] (missingEndScan
            (pushCrossed parsedPrefix [])) []) := by
  unfold guardedConfig cleanupSeekConfiguration missingEndScan
  rw [pushCrossed_eq_reverse_append,
    pushCrossed_eq_reverse_append]
  simp only [List.append_nil]
  rfl

set_option maxRecDepth 100000 in
private theorem outputsEnd_exact
    (parsedPrefix suffix : List WorkSymbol) :
    workRunExact? machine 2
        (guardedConfig State.outputsEndFirst parsedPrefix
          (cell10 :: cell01 :: suffix)) =
      some
        (guardedConfig State.instanceEndFirst
          (parsedPrefix ++ [cell10, cell01]) suffix) := by
  unfold guardedConfig
  rw [pushCrossed_append]
  rfl

set_option maxRecDepth 100000 in
private theorem instanceEnd_exact
    (parsedPrefix suffix : List WorkSymbol) :
    workRunExact? machine 2
        (guardedConfig State.instanceEndFirst parsedPrefix
          (cell10 :: cell11 :: suffix)) =
      some
        (guardedConfig State.finalEOF
          (parsedPrefix ++ [cell10, cell11]) suffix) := by
  unfold guardedConfig
  rw [pushCrossed_append]
  rfl

private theorem gateEndWrongToken_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token)
    (notGateEnd : token ≠ .gateEnd) :
    RejectingExecution
      (guardedConfig State.gateEndFirst parsedPrefix
        (SourceParser.packedTokenCells (token :: suffix))) := by
  let suffixCells := SourceParser.packedTokenCells suffix
  let initial :=
    guardedConfig State.gateEndFirst parsedPrefix
      (SourceParser.packedTokenCells (token :: suffix))
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not01 : current ≠ cell01) :
      RejectingExecution initial := by
    have launch :=
      gateEndFirstFailure_exact parsedPrefix current
        (next :: suffixCells) not01
    apply tokenExplicitFailure_exact
      parsedPrefix parsedPrefix token suffix current
        (next :: suffixCells) initial 1 prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells] using launch
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell01, current])
      (not11 : current ≠ cell11) :
      RejectingExecution initial := by
    let parsedAfterMark :=
      parsedPrefix ++ [gateMark]
    have launch :=
      gateEndSecondFailure_exact parsedPrefix current
        suffixCells not11
    have markerSafe : SafeSourceWord [gateMark] := by
      intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | impossible
      · decide
      · contradiction
    have tailSafe :
        SafeSourceWord (current :: suffixCells) := by
      have packedSafe :=
        packedTokenCells_safe (token :: suffix)
      intro symbol member
      apply packedSafe symbol
      change
        symbol ∈
          SourceParser.tokenCells token ++ suffixCells
      rw [cellsEq]
      simp only [List.mem_cons] at member
      rcases member with currentEq | member
      · subst symbol
        exact List.mem_append_left suffixCells
          (by simp)
      · exact List.mem_append_right
          [cell01, current] member
    have internalSafe :
        SafeSourceWord
          (parsedAfterMark ++ current :: suffixCells) :=
      safe_append
        (safe_append prefixSafe markerSafe) tailSafe
    exact
      safeExplicitFailure_exact
        (parsedAfterMark ++ current :: suffixCells)
        parsedAfterMark current suffixCells initial 2
        rfl internalSafe
        (by
          simpa [initial, parsedAfterMark,
            SourceParser.packedTokenCells, cellsEq,
            suffixCells] using launch)
  cases token with
  | version0 =>
      exact rejectFirst cell00 cell00 rfl (by decide)
  | unit =>
      exact rejectFirst cell00 cell01 rfl (by decide)
  | natEnd =>
      exact rejectFirst cell00 cell10 rfl (by decide)
  | input =>
      exact rejectFirst cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact rejectSecond cell00 rfl (by decide)
  | constantTrue =>
      exact rejectSecond cell01 rfl (by decide)
  | gate =>
      exact rejectSecond cell10 rfl (by decide)
  | gateEnd =>
      exact False.elim (notGateEnd rfl)
  | programEnd =>
      exact rejectFirst cell10 cell00 rfl (by decide)
  | outputsEnd =>
      exact rejectFirst cell10 cell01 rfl (by decide)
  | threshold =>
      exact rejectFirst cell10 cell10 rfl (by decide)
  | instanceEnd =>
      exact rejectFirst cell10 cell11 rfl (by decide)

private theorem outputsEndWrongToken_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token)
    (notOutputsEnd : token ≠ .outputsEnd) :
    RejectingExecution
      (guardedConfig State.outputsEndFirst parsedPrefix
        (SourceParser.packedTokenCells (token :: suffix))) := by
  let suffixCells := SourceParser.packedTokenCells suffix
  let initial :=
    guardedConfig State.outputsEndFirst parsedPrefix
      (SourceParser.packedTokenCells (token :: suffix))
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not10 : current ≠ cell10) :
      RejectingExecution initial := by
    have launch :=
      outputsEndFirstFailure_exact parsedPrefix current
        (next :: suffixCells) not10
    apply tokenExplicitFailure_exact
      parsedPrefix parsedPrefix token suffix current
        (next :: suffixCells) initial 1 prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells] using launch
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell10, current])
      (not01 : current ≠ cell01) :
      RejectingExecution initial := by
    have launch :=
      outputsEndSecondFailure_exact parsedPrefix current
        suffixCells not01
    apply tokenExplicitFailure_exact
      parsedPrefix (parsedPrefix ++ [cell10])
        token suffix current suffixCells initial 2 prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells] using launch
  cases token with
  | version0 =>
      exact rejectFirst cell00 cell00 rfl (by decide)
  | unit =>
      exact rejectFirst cell00 cell01 rfl (by decide)
  | natEnd =>
      exact rejectFirst cell00 cell10 rfl (by decide)
  | input =>
      exact rejectFirst cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact rejectFirst cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact rejectFirst cell01 cell01 rfl (by decide)
  | gate =>
      exact rejectFirst cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact rejectFirst cell01 cell11 rfl (by decide)
  | programEnd =>
      exact rejectSecond cell00 rfl (by decide)
  | outputsEnd =>
      exact False.elim (notOutputsEnd rfl)
  | threshold =>
      exact rejectSecond cell10 rfl (by decide)
  | instanceEnd =>
      exact rejectSecond cell11 rfl (by decide)

private theorem instanceEndWrongToken_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token)
    (notInstanceEnd : token ≠ .instanceEnd) :
    RejectingExecution
      (guardedConfig State.instanceEndFirst parsedPrefix
        (SourceParser.packedTokenCells (token :: suffix))) := by
  let suffixCells := SourceParser.packedTokenCells suffix
  let initial :=
    guardedConfig State.instanceEndFirst parsedPrefix
      (SourceParser.packedTokenCells (token :: suffix))
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not10 : current ≠ cell10) :
      RejectingExecution initial := by
    have launch :=
      instanceEndFirstFailure_exact parsedPrefix current
        (next :: suffixCells) not10
    apply tokenExplicitFailure_exact
      parsedPrefix parsedPrefix token suffix current
        (next :: suffixCells) initial 1 prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells] using launch
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell10, current])
      (not11 : current ≠ cell11) :
      RejectingExecution initial := by
    have launch :=
      instanceEndSecondFailure_exact parsedPrefix current
        suffixCells not11
    apply tokenExplicitFailure_exact
      parsedPrefix (parsedPrefix ++ [cell10])
        token suffix current suffixCells initial 2 prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells, List.append_assoc]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells] using launch
  cases token with
  | version0 =>
      exact rejectFirst cell00 cell00 rfl (by decide)
  | unit =>
      exact rejectFirst cell00 cell01 rfl (by decide)
  | natEnd =>
      exact rejectFirst cell00 cell10 rfl (by decide)
  | input =>
      exact rejectFirst cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact rejectFirst cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact rejectFirst cell01 cell01 rfl (by decide)
  | gate =>
      exact rejectFirst cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact rejectFirst cell01 cell11 rfl (by decide)
  | programEnd =>
      exact rejectSecond cell00 rfl (by decide)
  | outputsEnd =>
      exact rejectSecond cell01 rfl (by decide)
  | threshold =>
      exact rejectSecond cell10 rfl (by decide)
  | instanceEnd =>
      exact False.elim (notInstanceEnd rfl)

private theorem finalEOFToken_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token) :
    RejectingExecution
      (guardedConfig State.finalEOF parsedPrefix
        (SourceParser.packedTokenCells (token :: suffix))) := by
  let suffixCells := SourceParser.packedTokenCells suffix
  let initial :=
    guardedConfig State.finalEOF parsedPrefix
      (SourceParser.packedTokenCells (token :: suffix))
  have reject
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (notBlank : current ≠ cellBlank) :
      RejectingExecution initial := by
    have launch :=
      finalEOFFailure_exact parsedPrefix current
        (next :: suffixCells) notBlank
    apply tokenExplicitFailure_exact
      parsedPrefix parsedPrefix token suffix current
        (next :: suffixCells) initial 1 prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells, pushCrossed] using launch
  cases token with
  | version0 =>
      exact reject cell00 cell00 rfl (by decide)
  | unit =>
      exact reject cell00 cell01 rfl (by decide)
  | natEnd =>
      exact reject cell00 cell10 rfl (by decide)
  | input =>
      exact reject cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact reject cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact reject cell01 cell01 rfl (by decide)
  | gate =>
      exact reject cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact reject cell01 cell11 rfl (by decide)
  | programEnd =>
      exact reject cell10 cell00 rfl (by decide)
  | outputsEnd =>
      exact reject cell10 cell01 rfl (by decide)
  | threshold =>
      exact reject cell10 cell10 rfl (by decide)
  | instanceEnd =>
      exact reject cell10 cell11 rfl (by decide)

private theorem outputParsedPrefix_safe
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) :
    SafeSourceWord
      (outputPrefix inputs gates ++ sourceCells output) := by
  apply safe_of_ordinary
  exact ordinary_append
    (outputPrefix_ordinary inputs gates)
    (sourceCells_ordinary output)

private theorem scannerBootToken_exact
    (token : Token) (suffix : List Token) :
    workRunExact? machine 2
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            (SourceParser.packedTokenCells
              (token :: suffix)))) =
      some
        (guardedConfig State.versionFirst []
          (SourceParser.packedTokenCells
            (token :: suffix))) := by
  cases token <;> rfl

private theorem versionWrongToken_exact
    (token : Token) (suffix : List Token)
    (notVersion : token ≠ .version0) :
    RejectingExecution
      (guardedConfig State.versionFirst []
        (SourceParser.packedTokenCells (token :: suffix))) := by
  let suffixCells := SourceParser.packedTokenCells suffix
  let initial :=
    guardedConfig State.versionFirst []
      (SourceParser.packedTokenCells (token :: suffix))
  have emptySafe : SafeSourceWord [] := by
    intro symbol member
    contradiction
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not00 : current ≠ cell00) :
      RejectingExecution initial := by
    have launch :=
      versionFirstFailure_exact current
        (next :: suffixCells) not00
    apply tokenExplicitFailure_exact
      [] [] token suffix current (next :: suffixCells)
        initial 1 emptySafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells, pushCrossed] using launch
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell00, current])
      (not00 : current ≠ cell00) :
      RejectingExecution initial := by
    have launch :=
      versionSecondFromFirstFailure_exact
        current suffixCells not00
    apply tokenExplicitFailure_exact
      [] [cell00] token suffix current suffixCells
        initial 2 emptySafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells] using launch
  cases token with
  | version0 =>
      exact False.elim (notVersion rfl)
  | unit =>
      exact rejectSecond cell01 rfl (by decide)
  | natEnd =>
      exact rejectSecond cell10 rfl (by decide)
  | input =>
      exact rejectSecond cell11 rfl (by decide)
  | constantFalse =>
      exact rejectFirst cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact rejectFirst cell01 cell01 rfl (by decide)
  | gate =>
      exact rejectFirst cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact rejectFirst cell01 cell11 rfl (by decide)
  | programEnd =>
      exact rejectFirst cell10 cell00 rfl (by decide)
  | outputsEnd =>
      exact rejectFirst cell10 cell01 rfl (by decide)
  | threshold =>
      exact rejectFirst cell10 cell10 rfl (by decide)
  | instanceEnd =>
      exact rejectFirst cell10 cell11 rfl (by decide)

private theorem wrongProgramEndToken_exact
    (inputs : Nat) (gates : List RawGate)
    (token : Token) (suffix : List Token)
    (notProgramEnd : token ≠ .programEnd) :
    RejectingExecution
      (guardedConfig State.gateStart
        (gatePrefix inputs gates [])
        (SourceParser.packedTokenCells
          (token :: suffix))) := by
  let suffixCells := SourceParser.packedTokenCells suffix
  let initial :=
    guardedConfig State.gateStart
      (gatePrefix inputs gates [])
      (SourceParser.packedTokenCells (token :: suffix))
  have prefixSafe :
      SafeSourceWord (gatePrefix inputs gates []) :=
    safe_of_ordinary
      (gatePrefix_ordinary inputs gates [])
  have packedSafe :=
    packedTokenCells_safe (token :: suffix)
  have tailSafe
      (first current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [first, current]) :
      SafeSourceWord (current :: suffixCells) := by
    intro symbol member
    apply packedSafe symbol
    change
      symbol ∈
        SourceParser.tokenCells token ++ suffixCells
    rw [cellsEq]
    simp only [List.mem_cons] at member
    rcases member with currentEq | member
    · subst symbol
      exact List.mem_append_left suffixCells
        (by simp)
    · exact List.mem_append_right [first, current] member
  have exhausted
      (firstWas01 : Bool)
      (first current : WorkSymbol)
      (firstEq : firstSourceCell firstWas01 = first)
      (cellsEq :
        SourceParser.tokenCells token = [first, current]) :
      RejectingExecution initial := by
    have run :=
      gateDecrementExhausted_exact
        firstWas01 inputs gates current suffixCells
        (tailSafe first current cellsEq)
    simpa [initial, SourceParser.packedTokenCells,
      cellsEq, suffixCells, firstEq] using run
  have badSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell10, current])
      (not00 : current ≠ cell00) :
      RejectingExecution initial := by
    have run :=
      programEndSecondRejecting_exact
        (gatePrefix inputs gates []) prefixSafe
        current suffixCells
        (tailSafe cell10 current cellsEq) not00
    simpa [initial, SourceParser.packedTokenCells,
      cellsEq, suffixCells] using run
  cases token with
  | version0 =>
      exact exhausted false cell00 cell00 rfl rfl
  | unit =>
      exact exhausted false cell00 cell01 rfl rfl
  | natEnd =>
      exact exhausted false cell00 cell10 rfl rfl
  | input =>
      exact exhausted false cell00 cell11 rfl rfl
  | constantFalse =>
      exact exhausted true cell01 cell00 rfl rfl
  | constantTrue =>
      exact exhausted true cell01 cell01 rfl rfl
  | gate =>
      exact exhausted true cell01 cell10 rfl rfl
  | gateEnd =>
      exact exhausted true cell01 cell11 rfl rfl
  | programEnd =>
      exact False.elim (notProgramEnd rfl)
  | outputsEnd =>
      exact badSecond cell01 rfl (by decide)
  | threshold =>
      exact badSecond cell10 rfl (by decide)
  | instanceEnd =>
      exact badSecond cell11 rfl (by decide)

private theorem gateLeftTokenFailure_exact
    (inputs : Nat) (done : List RawGate)
    {remaining : Nat} {tokens : List Token}
    (failure : SourceParser.SourceTokenFailure tokens) :
    RejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done (remaining + 1))
        (SourceParser.packedTokenCells tokens)) := by
  let parsingPrefix :=
    gateParsingPrefix inputs done
      (placeholderGates remaining)
  have startPrefixSafe :
      SafeSourceWord
        (failureGatePrefix inputs done (remaining + 1)) := by
    apply safe_of_ordinary
    dsimp [failureGatePrefix]
    exact gatePrefix_ordinary inputs done
      (placeholderGates (remaining + 1))
  have parsingPrefixSafe :
      SafeSourceWord parsingPrefix := by
    exact safe_of_ordinary
      (gateParsingPrefix_ordinary inputs done
        (placeholderGates remaining))
  have firstPrefixSafe
      (first : WorkSymbol)
      (firstOrdinary : ordinaryCell first) :
      SafeSourceWord (parsingPrefix ++ [first]) := by
    apply safe_of_ordinary
    apply ordinary_append
      (gateParsingPrefix_ordinary inputs done
        (placeholderGates remaining))
    intro symbol member
    simp only [List.mem_cons,
      List.not_mem_nil] at member
    rcases member with rfl | impossible
    · exact firstOrdinary
    · contradiction
  cases failure with
  | missing =>
      exact
        missingExpected_exact State.gateStart
          (failureGatePrefix inputs done
            (remaining + 1))
          startPrefixSafe
          (gateStartMissingFailure_exact
            (failureGatePrefix inputs done
              (remaining + 1)))
  | wrongHead token suffix notInput notFalse notTrue notGate =>
      let suffixCells :=
        SourceParser.packedTokenCells suffix
      let initial :=
        guardedConfig State.gateStart
          (failureGatePrefix inputs done
            (remaining + 1))
          (SourceParser.packedTokenCells
            (token :: suffix))
      have packedSafe :=
        packedTokenCells_safe (token :: suffix)
      have tailSafe
          (first current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token =
              [first, current]) :
          SafeSourceWord (current :: suffixCells) := by
        intro symbol member
        apply packedSafe symbol
        have targetMember :
            symbol ∈
              SourceParser.tokenCells token ++ suffixCells := by
          rw [cellsEq]
          simp only [List.mem_cons] at member
          rcases member with currentEq | member
          · subst symbol
            exact List.mem_append_left suffixCells
              (by simp)
          · exact List.mem_append_right
              [first, current] member
        simpa [SourceParser.packedTokenCells,
          suffixCells, List.append_assoc] using targetMember
      have after00
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token =
              [cell00, current])
          (not11 : current ≠ cell11) :
          RejectingExecution initial := by
        have firstRun :=
          gateFirst_exact false inputs done remaining
            current suffixCells
        have firstCanonical :
            workRunExact? machine
                (gateFirstSteps inputs done remaining)
                initial =
              some
                (guardedConfig
                  (State.sourceAfter00 .gateLeft)
                  (parsingPrefix ++ [cell00])
                  (current :: suffixCells)) := by
          simpa [initial, parsingPrefix,
            SourceParser.packedTokenCells, cellsEq,
            suffixCells, firstSourceCell,
            afterFirstSourceState] using firstRun
        exact
          RejectingExecution.prepend
            (gateFirstSteps inputs done remaining)
            _ _ firstCanonical
            (sourceAfter00Rejecting_exact
              (parsingPrefix ++ [cell00])
              (firstPrefixSafe cell00
                cell00_ordinary)
              current suffixCells
              (tailSafe cell00 current cellsEq)
              not11)
      have after01
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token =
              [cell01, current])
          (not00 : current ≠ cell00)
          (not01 : current ≠ cell01)
          (not10 : current ≠ cell10) :
          RejectingExecution initial := by
        have firstRun :=
          gateFirst_exact true inputs done remaining
            current suffixCells
        have firstCanonical :
            workRunExact? machine
                (gateFirstSteps inputs done remaining)
                initial =
              some
                (guardedConfig
                  (State.sourceAfter01 .gateLeft)
                  (parsingPrefix ++ [cell01])
                  (current :: suffixCells)) := by
          simpa [initial, parsingPrefix,
            SourceParser.packedTokenCells, cellsEq,
            suffixCells, firstSourceCell,
            afterFirstSourceState] using firstRun
        exact
          RejectingExecution.prepend
            (gateFirstSteps inputs done remaining)
            _ _ firstCanonical
            (sourceAfter01Rejecting_exact
              (parsingPrefix ++ [cell01])
              (firstPrefixSafe cell01
                cell01_ordinary)
              current suffixCells
              (tailSafe cell01 current cellsEq)
              not00 not01 not10)
      have badProgramSecond
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token =
              [cell10, current])
          (not00 : current ≠ cell00) :
          RejectingExecution initial := by
        have run :=
          programEndSecondRejecting_exact
            (failureGatePrefix inputs done
              (remaining + 1))
            startPrefixSafe current suffixCells
            (tailSafe cell10 current cellsEq) not00
        simpa [initial, SourceParser.packedTokenCells,
          cellsEq, suffixCells] using run
      have prematureProgramEnd
          (cellsEq :
            SourceParser.tokenCells token =
              [cell10, cell00]) :
          RejectingExecution initial := by
        have run :=
          programCountRemainingRejecting_exact
            inputs done remaining suffixCells
            (packedTokenCells_safe suffix)
        simpa [initial, SourceParser.packedTokenCells,
          cellsEq, suffixCells] using run
      cases token with
      | version0 =>
          exact after00 cell00 rfl (by decide)
      | unit =>
          exact after00 cell01 rfl (by decide)
      | natEnd =>
          exact after00 cell10 rfl (by decide)
      | input =>
          exact False.elim (notInput rfl)
      | constantFalse =>
          exact False.elim (notFalse rfl)
      | constantTrue =>
          exact False.elim (notTrue rfl)
      | gate =>
          exact False.elim (notGate rfl)
      | gateEnd =>
          exact after01 cell11 rfl
            (by decide) (by decide) (by decide)
      | programEnd =>
          exact prematureProgramEnd rfl
      | outputsEnd =>
          exact badProgramSecond cell01 rfl
            (by decide)
      | threshold =>
          exact badProgramSecond cell10 rfl
            (by decide)
      | instanceEnd =>
          exact badProgramSecond cell11 rfl
            (by decide)
  | @inputIndex indexTokens indexFailure =>
      let afterFirst :=
        parsingPrefix ++ [cell00]
      let afterHead :=
        afterFirst ++ [cell11]
      have firstRun :=
        gateFirst_exact false inputs done remaining
          cell11
          (SourceParser.packedTokenCells indexTokens)
      have firstCanonical :
          workRunExact? machine
              (gateFirstSteps inputs done remaining)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (remaining + 1))
                (SourceParser.packedTokenCells
                  (.input :: indexTokens))) =
            some
              (guardedConfig
                (State.sourceAfter00 .gateLeft)
                afterFirst
                (cell11 ::
                  SourceParser.packedTokenCells
                    indexTokens)) := by
        simpa [afterFirst, parsingPrefix,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          firstSourceCell,
          afterFirstSourceState,
          cell00, cell11,
          SourceParser.cell00,
          SourceParser.cell11] using firstRun
      have headRun :=
        sourceAfter00NatLaunch_exact afterFirst
          (SourceParser.packedTokenCells indexTokens)
      have afterHeadSafe :
          SafeSourceWord afterHead := by
        apply safe_of_ordinary
        dsimp [afterHead, afterFirst, parsingPrefix]
        apply ordinary_append
        · apply ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates remaining))
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell00_ordinary
          · contradiction
        · intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell11_ordinary
          · contradiction
      exact
        RejectingExecution.prepend
          (gateFirstSteps inputs done remaining)
          _ _ firstCanonical
          (RejectingExecution.prepend 1 _ _
            (by
              simpa [afterHead, NatReader.state]
                using headRun)
            (natTokenFailure_exact
              (.source .gateLeft) afterHead
              indexFailure afterHeadSafe))
  | @gateIndex indexTokens indexFailure =>
      let afterFirst :=
        parsingPrefix ++ [cell01]
      let afterHead :=
        afterFirst ++ [cell10]
      have firstRun :=
        gateFirst_exact true inputs done remaining
          cell10
          (SourceParser.packedTokenCells indexTokens)
      have firstCanonical :
          workRunExact? machine
              (gateFirstSteps inputs done remaining)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (remaining + 1))
                (SourceParser.packedTokenCells
                  (.gate :: indexTokens))) =
            some
              (guardedConfig
                (State.sourceAfter01 .gateLeft)
                afterFirst
                (cell10 ::
                  SourceParser.packedTokenCells
                    indexTokens)) := by
        simpa [afterFirst, parsingPrefix,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          firstSourceCell,
          afterFirstSourceState,
          cell01, cell10,
          SourceParser.cell01,
          SourceParser.cell10] using firstRun
      have headRun :=
        sourceAfter01NatLaunch_exact afterFirst
          (SourceParser.packedTokenCells indexTokens)
      have afterHeadSafe :
          SafeSourceWord afterHead := by
        apply safe_of_ordinary
        dsimp [afterHead, afterFirst, parsingPrefix]
        apply ordinary_append
        · apply ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates remaining))
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell01_ordinary
          · contradiction
        · intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell10_ordinary
          · contradiction
      exact
        RejectingExecution.prepend
          (gateFirstSteps inputs done remaining)
          _ _ firstCanonical
          (RejectingExecution.prepend 1 _ _
            (by
              simpa [afterHead, NatReader.state]
                using headRun)
            (natTokenFailure_exact
              (.source .gateLeft) afterHead
              indexFailure afterHeadSafe))

private theorem gateLeftTokenFailureWithMalformedTail_exact
    (inputs : Nat) (done : List RawGate)
    {remaining : Nat} {tokens : List Token}
    (failure : SourceParser.SourceTokenFailure tokens)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done (remaining + 1))
        (SourceParser.packedTokenCells tokens ++ workTail)) := by
  let parsingPrefix :=
    gateParsingPrefix inputs done
      (placeholderGates remaining)
  have startPrefixSafe :
      SafeSourceWord
        (failureGatePrefix inputs done (remaining + 1)) :=
    failureGatePrefix_safe inputs done (remaining + 1)
  have parsingPrefixSafe :
      SafeSourceWord parsingPrefix := by
    exact safe_of_ordinary
      (gateParsingPrefix_ordinary inputs done
        (placeholderGates remaining))
  have firstPrefixSafe
      (first : WorkSymbol)
      (firstOrdinary : ordinaryCell first) :
      SafeSourceWord (parsingPrefix ++ [first]) := by
    apply safe_of_ordinary
    apply ordinary_append
      (gateParsingPrefix_ordinary inputs done
        (placeholderGates remaining))
    intro symbol member
    simp only [List.mem_cons,
      List.not_mem_nil] at member
    rcases member with rfl | impossible
    · exact firstOrdinary
    · contradiction
  cases failure with
  | missing =>
      exact gateMalformedTail_exact
        inputs done (remaining + 1) malformed
  | wrongHead token suffix notInput notFalse notTrue notGate =>
      let suffixCells :=
        SourceParser.packedTokenCells suffix ++ workTail
      let initial :=
        guardedConfig State.gateStart
          (failureGatePrefix inputs done (remaining + 1))
          (SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail)
      have packedSafe :
          SafeSourceWord
            (SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail) :=
        safe_append
          (packedTokenCells_safe (token :: suffix))
          (malformedWorkTail_safe malformed)
      have tailSafe
          (first current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token =
              [first, current]) :
          SafeSourceWord (current :: suffixCells) := by
        intro symbol member
        apply packedSafe symbol
        have targetMember :
            symbol ∈
              SourceParser.tokenCells token ++ suffixCells := by
          rw [cellsEq]
          simp only [List.mem_cons] at member
          rcases member with currentEq | member
          · subst symbol
            exact List.mem_append_left suffixCells
              (by simp)
          · exact List.mem_append_right
              [first, current] member
        simpa [SourceParser.packedTokenCells,
          suffixCells, List.append_assoc] using targetMember
      have after00
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token =
              [cell00, current])
          (not11 : current ≠ cell11) :
          RejectingExecution initial := by
        have firstRun :=
          gateFirst_exact false inputs done remaining
            current suffixCells
        have firstCanonical :
            workRunExact? machine
                (gateFirstSteps inputs done remaining)
                initial =
              some
                (guardedConfig
                  (State.sourceAfter00 .gateLeft)
                  (parsingPrefix ++ [cell00])
                  (current :: suffixCells)) := by
          simpa [initial, parsingPrefix,
            SourceParser.packedTokenCells, cellsEq,
            suffixCells, firstSourceCell,
            afterFirstSourceState,
            List.append_assoc] using firstRun
        exact
          RejectingExecution.prepend
            (gateFirstSteps inputs done remaining)
            _ _ firstCanonical
            (sourceAfter00Rejecting_exact
              (parsingPrefix ++ [cell00])
              (firstPrefixSafe cell00 cell00_ordinary)
              current suffixCells
              (tailSafe cell00 current cellsEq)
              not11)
      have after01
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token =
              [cell01, current])
          (not00 : current ≠ cell00)
          (not01 : current ≠ cell01)
          (not10 : current ≠ cell10) :
          RejectingExecution initial := by
        have firstRun :=
          gateFirst_exact true inputs done remaining
            current suffixCells
        have firstCanonical :
            workRunExact? machine
                (gateFirstSteps inputs done remaining)
                initial =
              some
                (guardedConfig
                  (State.sourceAfter01 .gateLeft)
                  (parsingPrefix ++ [cell01])
                  (current :: suffixCells)) := by
          simpa [initial, parsingPrefix,
            SourceParser.packedTokenCells, cellsEq,
            suffixCells, firstSourceCell,
            afterFirstSourceState,
            List.append_assoc] using firstRun
        exact
          RejectingExecution.prepend
            (gateFirstSteps inputs done remaining)
            _ _ firstCanonical
            (sourceAfter01Rejecting_exact
              (parsingPrefix ++ [cell01])
              (firstPrefixSafe cell01 cell01_ordinary)
              current suffixCells
              (tailSafe cell01 current cellsEq)
              not00 not01 not10)
      have badProgramSecond
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token =
              [cell10, current])
          (not00 : current ≠ cell00) :
          RejectingExecution initial := by
        have run :=
          programEndSecondRejecting_exact
            (failureGatePrefix inputs done
              (remaining + 1))
            startPrefixSafe current suffixCells
            (tailSafe cell10 current cellsEq) not00
        simpa [initial, SourceParser.packedTokenCells,
          cellsEq, suffixCells, List.append_assoc] using run
      have prematureProgramEnd
          (cellsEq :
            SourceParser.tokenCells token =
              [cell10, cell00]) :
          RejectingExecution initial := by
        have run :=
          programCountRemainingRejecting_exact
            inputs done remaining suffixCells
            (safe_append
              (packedTokenCells_safe suffix)
              (malformedWorkTail_safe malformed))
        simpa [initial, SourceParser.packedTokenCells,
          cellsEq, suffixCells, List.append_assoc] using run
      cases token with
      | version0 =>
          exact after00 cell00 rfl (by decide)
      | unit =>
          exact after00 cell01 rfl (by decide)
      | natEnd =>
          exact after00 cell10 rfl (by decide)
      | input =>
          exact False.elim (notInput rfl)
      | constantFalse =>
          exact False.elim (notFalse rfl)
      | constantTrue =>
          exact False.elim (notTrue rfl)
      | gate =>
          exact False.elim (notGate rfl)
      | gateEnd =>
          exact after01 cell11 rfl
            (by decide) (by decide) (by decide)
      | programEnd =>
          exact prematureProgramEnd rfl
      | outputsEnd =>
          exact badProgramSecond cell01 rfl (by decide)
      | threshold =>
          exact badProgramSecond cell10 rfl (by decide)
      | instanceEnd =>
          exact badProgramSecond cell11 rfl (by decide)
  | @inputIndex indexTokens indexFailure =>
      let afterFirst := parsingPrefix ++ [cell00]
      let afterHead := afterFirst ++ [cell11]
      let indexWord :=
        SourceParser.packedTokenCells indexTokens ++ workTail
      have firstRun :=
        gateFirst_exact false inputs done remaining
          cell11 indexWord
      have firstCanonical :
          workRunExact? machine
              (gateFirstSteps inputs done remaining)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done (remaining + 1))
                (SourceParser.packedTokenCells
                    (.input :: indexTokens) ++
                  workTail)) =
            some
              (guardedConfig
                (State.sourceAfter00 .gateLeft)
                afterFirst (cell11 :: indexWord)) := by
        simpa [afterFirst, parsingPrefix, indexWord,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          firstSourceCell, afterFirstSourceState,
          cell00, cell11, SourceParser.cell00,
          SourceParser.cell11, List.append_assoc] using firstRun
      have headRun :=
        sourceAfter00NatLaunch_exact afterFirst indexWord
      have afterHeadSafe :
          SafeSourceWord afterHead := by
        apply safe_of_ordinary
        dsimp [afterHead, afterFirst, parsingPrefix]
        apply ordinary_append
        · apply ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates remaining))
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell00_ordinary
          · contradiction
        · intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell11_ordinary
          · contradiction
      exact
        RejectingExecution.prepend
          (gateFirstSteps inputs done remaining)
          _ _ firstCanonical
          (RejectingExecution.prepend 1 _ _
            (by
              simpa [afterHead, NatReader.state]
                using headRun)
            (natTokenFailureWithMalformedTail_exact
              (.source .gateLeft) afterHead
              indexFailure afterHeadSafe malformed))
  | @gateIndex indexTokens indexFailure =>
      let afterFirst := parsingPrefix ++ [cell01]
      let afterHead := afterFirst ++ [cell10]
      let indexWord :=
        SourceParser.packedTokenCells indexTokens ++ workTail
      have firstRun :=
        gateFirst_exact true inputs done remaining
          cell10 indexWord
      have firstCanonical :
          workRunExact? machine
              (gateFirstSteps inputs done remaining)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done (remaining + 1))
                (SourceParser.packedTokenCells
                    (.gate :: indexTokens) ++
                  workTail)) =
            some
              (guardedConfig
                (State.sourceAfter01 .gateLeft)
                afterFirst (cell10 :: indexWord)) := by
        simpa [afterFirst, parsingPrefix, indexWord,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          firstSourceCell, afterFirstSourceState,
          cell01, cell10, SourceParser.cell01,
          SourceParser.cell10, List.append_assoc] using firstRun
      have headRun :=
        sourceAfter01NatLaunch_exact afterFirst indexWord
      have afterHeadSafe :
          SafeSourceWord afterHead := by
        apply safe_of_ordinary
        dsimp [afterHead, afterFirst, parsingPrefix]
        apply ordinary_append
        · apply ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates remaining))
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell01_ordinary
          · contradiction
        · intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell10_ordinary
          · contradiction
      exact
        RejectingExecution.prepend
          (gateFirstSteps inputs done remaining)
          _ _ firstCanonical
          (RejectingExecution.prepend 1 _ _
            (by
              simpa [afterHead, NatReader.state]
                using headRun)
            (natTokenFailureWithMalformedTail_exact
              (.source .gateLeft) afterHead
              indexFailure afterHeadSafe malformed))

private theorem gateEndWrongTokenWithMalformedTail_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token)
    (notGateEnd : token ≠ .gateEnd)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (guardedConfig State.gateEndFirst parsedPrefix
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail)) := by
  let suffixCells :=
    SourceParser.packedTokenCells suffix ++ workTail
  let initial :=
    guardedConfig State.gateEndFirst parsedPrefix
      (SourceParser.packedTokenCells
          (token :: suffix) ++
        workTail)
  have packedSafe :
      SafeSourceWord
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail) :=
    safe_append
      (packedTokenCells_safe (token :: suffix))
      (malformedWorkTail_safe malformed)
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not01 : current ≠ cell01) :
      RejectingExecution initial := by
    have launch :=
      gateEndFirstFailure_exact parsedPrefix current
        (next :: suffixCells) not01
    have shape :
        parsedPrefix ++
            (SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail) =
          parsedPrefix ++ current :: next :: suffixCells := by
      simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    exact
      safeExplicitFailure_exact
        (parsedPrefix ++
          (SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail))
        parsedPrefix current (next :: suffixCells)
        initial 1 shape
        (safe_append prefixSafe packedSafe)
        (by
          simpa [initial,
            SourceParser.packedTokenCells,
            cellsEq, suffixCells,
            List.append_assoc] using launch)
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell01, current])
      (not11 : current ≠ cell11) :
      RejectingExecution initial := by
    let parsedAfterMark := parsedPrefix ++ [gateMark]
    have launch :=
      gateEndSecondFailure_exact parsedPrefix current
        suffixCells not11
    have markerSafe : SafeSourceWord [gateMark] := by
      exact safe_singleton_gateMark
    have tailSafe :
        SafeSourceWord (current :: suffixCells) := by
      intro symbol member
      apply packedSafe symbol
      have targetMember :
          symbol ∈
            SourceParser.tokenCells token ++ suffixCells := by
        rw [cellsEq]
        simp only [List.mem_cons] at member
        rcases member with currentEq | member
        · subst symbol
          exact List.mem_append_left suffixCells (by simp)
        · exact List.mem_append_right
            [cell01, current] member
      simpa [SourceParser.packedTokenCells,
        suffixCells, List.append_assoc] using targetMember
    have internalSafe :
        SafeSourceWord
          (parsedAfterMark ++ current :: suffixCells) :=
      safe_append
        (safe_append prefixSafe markerSafe) tailSafe
    exact
      safeExplicitFailure_exact
        (parsedAfterMark ++ current :: suffixCells)
        parsedAfterMark current suffixCells initial 2
        rfl internalSafe
        (by
          simpa [initial, parsedAfterMark,
            SourceParser.packedTokenCells, cellsEq,
            suffixCells, List.append_assoc] using launch)
  cases token with
  | version0 =>
      exact rejectFirst cell00 cell00 rfl (by decide)
  | unit =>
      exact rejectFirst cell00 cell01 rfl (by decide)
  | natEnd =>
      exact rejectFirst cell00 cell10 rfl (by decide)
  | input =>
      exact rejectFirst cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact rejectSecond cell00 rfl (by decide)
  | constantTrue =>
      exact rejectSecond cell01 rfl (by decide)
  | gate =>
      exact rejectSecond cell10 rfl (by decide)
  | gateEnd =>
      exact False.elim (notGateEnd rfl)
  | programEnd =>
      exact rejectFirst cell10 cell00 rfl (by decide)
  | outputsEnd =>
      exact rejectFirst cell10 cell01 rfl (by decide)
  | threshold =>
      exact rejectFirst cell10 cell10 rfl (by decide)
  | instanceEnd =>
      exact rejectFirst cell10 cell11 rfl (by decide)

private theorem nGatesTokenFailureWithMalformedTail_exact
    (inputs : Nat) (done : List RawGate)
    {count : Nat} {tokens : List Token}
    (failure :
      SourceParser.NGatesTokenFailure count tokens)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done count)
        (SourceParser.packedTokenCells tokens ++ workTail)) := by
  induction failure generalizing done with
  | left failure =>
      exact gateLeftTokenFailureWithMalformedTail_exact
        inputs done failure malformed
  | @right count left failedTokens failure =>
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates count) ++
          sourceCells left
      let failedWord :=
        SourceParser.packedTokenCells failedTokens ++ workTail
      have leftRun :=
        gateLeft_exact inputs done count left failedWord
      have leftCanonical :
          workRunExact? machine
              (gateLeftSteps inputs done count left)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done (count + 1))
                (SourceParser.packedTokenCells
                    (encodeSourceTokens left ++ failedTokens) ++
                  workTail)) =
            some
              (guardedConfig
                (State.sourceStart .gateRight)
                parsedPrefix failedWord) := by
        rw [packedTokenCells_append,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [parsedPrefix, failedWord,
          List.append_assoc] using leftRun
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        apply safe_of_ordinary
        dsimp [parsedPrefix]
        exact ordinary_append
          (gateParsingPrefix_ordinary inputs done
            (placeholderGates count))
          (sourceCells_ordinary left)
      exact
        RejectingExecution.prepend
          (gateLeftSteps inputs done count left)
          _ _ leftCanonical
          (sourceTokenFailureWithMalformedTail_exact
            .gateRight parsedPrefix failure
            parsedSafe malformed)
  | missingGateEnd count left right =>
      let gate : RawGate :=
        { left := left, right := right }
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates count) ++
          sourceCells left ++ sourceCells right
      have sources :=
        gateSources_exact inputs done count gate workTail
      have sourcesCanonical :
          workRunExact? machine
              (gateSourcesSteps inputs done count gate)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done (count + 1))
                (SourceParser.packedTokenCells
                    (encodeSourceTokens left ++
                      encodeSourceTokens right) ++
                  workTail)) =
            some
              (guardedConfig State.gateEndFirst
                parsedPrefix workTail) := by
        rw [packedTokenCells_append,
          SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [gate, parsedPrefix,
          List.append_assoc] using sources
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        apply safe_of_ordinary
        dsimp [parsedPrefix]
        exact ordinary_append
          (ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates count))
            (sourceCells_ordinary left))
          (sourceCells_ordinary right)
      exact
        RejectingExecution.prepend
          (gateSourcesSteps inputs done count gate)
          _ _ sourcesCanonical
          (simpleMalformedBoundary_rejecting_exact
            .gateEnd parsedPrefix parsedSafe malformed)
  | wrongGateEnd count left right token suffix notGateEnd =>
      let gate : RawGate :=
        { left := left, right := right }
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates count) ++
          sourceCells left ++ sourceCells right
      let failedWord :=
        SourceParser.packedTokenCells (token :: suffix) ++
          workTail
      have sources :=
        gateSources_exact inputs done count gate failedWord
      have sourcesCanonical :
          workRunExact? machine
              (gateSourcesSteps inputs done count gate)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done (count + 1))
                (SourceParser.packedTokenCells
                    (encodeSourceTokens left ++
                      encodeSourceTokens right ++
                        token :: suffix) ++
                  workTail)) =
            some
              (guardedConfig State.gateEndFirst
                parsedPrefix failedWord) := by
        repeat rw [packedTokenCells_append]
        rw [SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [gate, parsedPrefix, failedWord,
          List.append_assoc] using sources
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        apply safe_of_ordinary
        dsimp [parsedPrefix]
        exact ordinary_append
          (ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates count))
            (sourceCells_ordinary left))
          (sourceCells_ordinary right)
      exact
        RejectingExecution.prepend
          (gateSourcesSteps inputs done count gate)
          _ _ sourcesCanonical
          (gateEndWrongTokenWithMalformedTail_exact
            parsedPrefix parsedSafe token suffix
            notGateEnd malformed)
  | @rest count left right failedTokens failure ih =>
      let gate : RawGate :=
        { left := left, right := right }
      let failedWord :=
        SourceParser.packedTokenCells failedTokens ++ workTail
      have record :=
        gateRecord_exact inputs done count gate failedWord
      have recordCanonical :
          workRunExact? machine
              (gateRecordSteps inputs done count gate)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done (count + 1))
                (SourceParser.packedTokenCells
                    (encodeSourceTokens left ++
                      encodeSourceTokens right ++
                        .gateEnd :: failedTokens) ++
                  workTail)) =
            some
              (guardedConfig State.gateStart
                (failureGatePrefix inputs
                  (done ++ [gate]) count)
                failedWord) := by
        repeat rw [packedTokenCells_append]
        rw [SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [gate, gateCells,
          SourceParser.gateCells,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          cell01, cell11,
          SourceParser.cell01,
          SourceParser.cell11,
          failedWord, List.append_assoc] using record
      exact
        RejectingExecution.prepend
          (gateRecordSteps inputs done count gate)
          _ _ recordCanonical
          (ih (done ++ [gate]))

private theorem tokenMalformedExplicitFailure_exact
    (basePrefix parsedPrefix : List WorkSymbol)
    (token : Token) (suffix : List Token)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (initial : WorkConfiguration) (launchSteps : Nat)
    (prefixSafe : SafeSourceWord basePrefix)
    (shape :
      basePrefix ++
          (SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail) =
        parsedPrefix ++ current :: rest)
    (launch :
      workRunExact? machine launchSteps initial =
        some
          (cleanupSeekConfiguration
            [] (current :: pushCrossed parsedPrefix []) rest)) :
    RejectingExecution initial := by
  exact
    safeExplicitFailure_exact
      (basePrefix ++
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail))
      parsedPrefix current rest initial launchSteps shape
      (safe_append prefixSafe
        (safe_append
          (packedTokenCells_safe (token :: suffix))
          (malformedWorkTail_safe malformed)))
      launch

private theorem versionWrongTokenWithMalformedTail_exact
    (token : Token) (suffix : List Token)
    (notVersion : token ≠ .version0)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (guardedConfig State.versionFirst []
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail)) := by
  let suffixCells :=
    SourceParser.packedTokenCells suffix ++ workTail
  let initial :=
    guardedConfig State.versionFirst []
      (SourceParser.packedTokenCells
          (token :: suffix) ++
        workTail)
  have emptySafe : SafeSourceWord [] := by
    intro symbol member
    contradiction
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not00 : current ≠ cell00) :
      RejectingExecution initial := by
    have launch :=
      versionFirstFailure_exact current
        (next :: suffixCells) not00
    apply tokenMalformedExplicitFailure_exact
      [] [] token suffix malformed current
        (next :: suffixCells) initial 1 emptySafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells, pushCrossed,
        List.append_assoc] using launch
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell00, current])
      (not00 : current ≠ cell00) :
      RejectingExecution initial := by
    have launch :=
      versionSecondFromFirstFailure_exact
        current suffixCells not00
    apply tokenMalformedExplicitFailure_exact
      [] [cell00] token suffix malformed current
        suffixCells initial 2 emptySafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells, List.append_assoc] using launch
  cases token with
  | version0 =>
      exact False.elim (notVersion rfl)
  | unit =>
      exact rejectSecond cell01 rfl (by decide)
  | natEnd =>
      exact rejectSecond cell10 rfl (by decide)
  | input =>
      exact rejectSecond cell11 rfl (by decide)
  | constantFalse =>
      exact rejectFirst cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact rejectFirst cell01 cell01 rfl (by decide)
  | gate =>
      exact rejectFirst cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact rejectFirst cell01 cell11 rfl (by decide)
  | programEnd =>
      exact rejectFirst cell10 cell00 rfl (by decide)
  | outputsEnd =>
      exact rejectFirst cell10 cell01 rfl (by decide)
  | threshold =>
      exact rejectFirst cell10 cell10 rfl (by decide)
  | instanceEnd =>
      exact rejectFirst cell10 cell11 rfl (by decide)

private theorem wrongProgramEndTokenWithMalformedTail_exact
    (inputs : Nat) (gates : List RawGate)
    (token : Token) (suffix : List Token)
    (notProgramEnd : token ≠ .programEnd)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (guardedConfig State.gateStart
        (gatePrefix inputs gates [])
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail)) := by
  let suffixCells :=
    SourceParser.packedTokenCells suffix ++ workTail
  let initial :=
    guardedConfig State.gateStart
      (gatePrefix inputs gates [])
      (SourceParser.packedTokenCells
          (token :: suffix) ++
        workTail)
  have prefixSafe :
      SafeSourceWord (gatePrefix inputs gates []) :=
    safe_of_ordinary
      (gatePrefix_ordinary inputs gates [])
  have packedSafe :
      SafeSourceWord
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail) :=
    safe_append
      (packedTokenCells_safe (token :: suffix))
      (malformedWorkTail_safe malformed)
  have tailSafe
      (first current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [first, current]) :
      SafeSourceWord (current :: suffixCells) := by
    intro symbol member
    apply packedSafe symbol
    have targetMember :
        symbol ∈
          SourceParser.tokenCells token ++ suffixCells := by
      rw [cellsEq]
      simp only [List.mem_cons] at member
      rcases member with currentEq | member
      · subst symbol
        exact List.mem_append_left suffixCells (by simp)
      · exact List.mem_append_right [first, current] member
    simpa [SourceParser.packedTokenCells,
      suffixCells, List.append_assoc] using targetMember
  have exhausted
      (firstWas01 : Bool)
      (first current : WorkSymbol)
      (firstEq : firstSourceCell firstWas01 = first)
      (cellsEq :
        SourceParser.tokenCells token = [first, current]) :
      RejectingExecution initial := by
    have run :=
      gateDecrementExhausted_exact
        firstWas01 inputs gates current suffixCells
        (tailSafe first current cellsEq)
    simpa [initial, SourceParser.packedTokenCells,
      cellsEq, suffixCells, firstEq,
      List.append_assoc] using run
  have badSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell10, current])
      (not00 : current ≠ cell00) :
      RejectingExecution initial := by
    have run :=
      programEndSecondRejecting_exact
        (gatePrefix inputs gates []) prefixSafe
        current suffixCells
        (tailSafe cell10 current cellsEq) not00
    simpa [initial, SourceParser.packedTokenCells,
      cellsEq, suffixCells, List.append_assoc] using run
  cases token with
  | version0 =>
      exact exhausted false cell00 cell00 rfl rfl
  | unit =>
      exact exhausted false cell00 cell01 rfl rfl
  | natEnd =>
      exact exhausted false cell00 cell10 rfl rfl
  | input =>
      exact exhausted false cell00 cell11 rfl rfl
  | constantFalse =>
      exact exhausted true cell01 cell00 rfl rfl
  | constantTrue =>
      exact exhausted true cell01 cell01 rfl rfl
  | gate =>
      exact exhausted true cell01 cell10 rfl rfl
  | gateEnd =>
      exact exhausted true cell01 cell11 rfl rfl
  | programEnd =>
      exact False.elim (notProgramEnd rfl)
  | outputsEnd =>
      exact badSecond cell01 rfl (by decide)
  | threshold =>
      exact badSecond cell10 rfl (by decide)
  | instanceEnd =>
      exact badSecond cell11 rfl (by decide)

private theorem outputsEndWrongTokenWithMalformedTail_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token)
    (notOutputsEnd : token ≠ .outputsEnd)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (guardedConfig State.outputsEndFirst parsedPrefix
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail)) := by
  let suffixCells :=
    SourceParser.packedTokenCells suffix ++ workTail
  let initial :=
    guardedConfig State.outputsEndFirst parsedPrefix
      (SourceParser.packedTokenCells
          (token :: suffix) ++
        workTail)
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not10 : current ≠ cell10) :
      RejectingExecution initial := by
    have launch :=
      outputsEndFirstFailure_exact parsedPrefix current
        (next :: suffixCells) not10
    apply tokenMalformedExplicitFailure_exact
      parsedPrefix parsedPrefix token suffix malformed
      current (next :: suffixCells) initial 1 prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells,
        List.append_assoc] using launch
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell10, current])
      (not01 : current ≠ cell01) :
      RejectingExecution initial := by
    have launch :=
      outputsEndSecondFailure_exact parsedPrefix current
        suffixCells not01
    apply tokenMalformedExplicitFailure_exact
      parsedPrefix (parsedPrefix ++ [cell10])
      token suffix malformed current suffixCells
      initial 2 prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells,
        List.append_assoc] using launch
  cases token with
  | version0 =>
      exact rejectFirst cell00 cell00 rfl (by decide)
  | unit =>
      exact rejectFirst cell00 cell01 rfl (by decide)
  | natEnd =>
      exact rejectFirst cell00 cell10 rfl (by decide)
  | input =>
      exact rejectFirst cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact rejectFirst cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact rejectFirst cell01 cell01 rfl (by decide)
  | gate =>
      exact rejectFirst cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact rejectFirst cell01 cell11 rfl (by decide)
  | programEnd =>
      exact rejectSecond cell00 rfl (by decide)
  | outputsEnd =>
      exact False.elim (notOutputsEnd rfl)
  | threshold =>
      exact rejectSecond cell10 rfl (by decide)
  | instanceEnd =>
      exact rejectSecond cell11 rfl (by decide)

private theorem instanceEndWrongTokenWithMalformedTail_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token)
    (notInstanceEnd : token ≠ .instanceEnd)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (guardedConfig State.instanceEndFirst parsedPrefix
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail)) := by
  let suffixCells :=
    SourceParser.packedTokenCells suffix ++ workTail
  let initial :=
    guardedConfig State.instanceEndFirst parsedPrefix
      (SourceParser.packedTokenCells
          (token :: suffix) ++
        workTail)
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not10 : current ≠ cell10) :
      RejectingExecution initial := by
    have launch :=
      instanceEndFirstFailure_exact parsedPrefix current
        (next :: suffixCells) not10
    apply tokenMalformedExplicitFailure_exact
      parsedPrefix parsedPrefix token suffix malformed
      current (next :: suffixCells) initial 1 prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells,
        List.append_assoc] using launch
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell10, current])
      (not11 : current ≠ cell11) :
      RejectingExecution initial := by
    have launch :=
      instanceEndSecondFailure_exact parsedPrefix current
        suffixCells not11
    apply tokenMalformedExplicitFailure_exact
      parsedPrefix (parsedPrefix ++ [cell10])
      token suffix malformed current suffixCells
      initial 2 prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells, List.append_assoc]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells,
        List.append_assoc] using launch
  cases token with
  | version0 =>
      exact rejectFirst cell00 cell00 rfl (by decide)
  | unit =>
      exact rejectFirst cell00 cell01 rfl (by decide)
  | natEnd =>
      exact rejectFirst cell00 cell10 rfl (by decide)
  | input =>
      exact rejectFirst cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact rejectFirst cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact rejectFirst cell01 cell01 rfl (by decide)
  | gate =>
      exact rejectFirst cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact rejectFirst cell01 cell11 rfl (by decide)
  | programEnd =>
      exact rejectSecond cell00 rfl (by decide)
  | outputsEnd =>
      exact rejectSecond cell01 rfl (by decide)
  | threshold =>
      exact rejectSecond cell10 rfl (by decide)
  | instanceEnd =>
      exact False.elim (notInstanceEnd rfl)

private theorem finalEOFWordRejecting_exact
    (parsedPrefix word : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (wordSafe : SafeSourceWord word)
    (wordNonempty : word ≠ []) :
    RejectingExecution
      (guardedConfig State.finalEOF parsedPrefix word) := by
  cases word with
  | nil =>
      exact False.elim (wordNonempty rfl)
  | cons current rest =>
      have notBlank : current ≠ cellBlank :=
        (wordSafe current (by simp)).2
      have launch :=
        finalEOFFailure_exact parsedPrefix current
          rest notBlank
      exact
        safeExplicitFailure_exact
          (parsedPrefix ++ current :: rest)
          parsedPrefix current rest
          (guardedConfig State.finalEOF
            parsedPrefix (current :: rest))
          1 rfl
          (safe_append prefixSafe wordSafe)
          launch

private theorem nGatesTokenFailure_exact
    (inputs : Nat) (done : List RawGate)
    {count : Nat} {tokens : List Token}
    (failure :
      SourceParser.NGatesTokenFailure count tokens) :
    RejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done count)
        (SourceParser.packedTokenCells tokens)) := by
  induction failure generalizing done with
  | left failure =>
      exact gateLeftTokenFailure_exact
        inputs done failure
  | @right count left failedTokens failure =>
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates count) ++
          sourceCells left
      have leftRun :=
        gateLeft_exact inputs done count left
          (SourceParser.packedTokenCells failedTokens)
      have leftCanonical :
          workRunExact? machine
              (gateLeftSteps inputs done count left)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (count + 1))
                (SourceParser.packedTokenCells
                  (encodeSourceTokens left ++
                    failedTokens))) =
            some
              (guardedConfig
                (State.sourceStart .gateRight)
                parsedPrefix
                (SourceParser.packedTokenCells
                  failedTokens)) := by
        rw [packedTokenCells_append,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [parsedPrefix] using leftRun
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        apply safe_of_ordinary
        dsimp [parsedPrefix]
        exact ordinary_append
          (gateParsingPrefix_ordinary inputs done
            (placeholderGates count))
          (sourceCells_ordinary left)
      exact
        RejectingExecution.prepend
          (gateLeftSteps inputs done count left)
          _ _ leftCanonical
          (sourceTokenFailure_exact .gateRight
            parsedPrefix failure parsedSafe)
  | missingGateEnd count left right =>
      let gate : RawGate :=
        { left := left, right := right }
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates count) ++
          sourceCells left ++ sourceCells right
      have sources :=
        gateSources_exact inputs done count gate []
      have sourcesCanonical :
          workRunExact? machine
              (gateSourcesSteps inputs done count gate)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (count + 1))
                (SourceParser.packedTokenCells
                  (encodeSourceTokens left ++
                    encodeSourceTokens right))) =
            some
              (guardedConfig State.gateEndFirst
                parsedPrefix []) := by
        rw [packedTokenCells_append,
          SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [gate, parsedPrefix,
          List.append_assoc] using sources
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        apply safe_of_ordinary
        dsimp [parsedPrefix]
        exact ordinary_append
          (ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates count))
            (sourceCells_ordinary left))
          (sourceCells_ordinary right)
      exact
        RejectingExecution.prepend
          (gateSourcesSteps inputs done count gate)
          _ _ sourcesCanonical
          (missingExpected_exact State.gateEndFirst
            parsedPrefix parsedSafe
            (gateEndMissingFailure_exact parsedPrefix))
  | wrongGateEnd count left right token suffix notGateEnd =>
      let gate : RawGate :=
        { left := left, right := right }
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates count) ++
          sourceCells left ++ sourceCells right
      have sources :=
        gateSources_exact inputs done count gate
          (SourceParser.packedTokenCells
            (token :: suffix))
      have sourcesCanonical :
          workRunExact? machine
              (gateSourcesSteps inputs done count gate)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (count + 1))
                (SourceParser.packedTokenCells
                  (encodeSourceTokens left ++
                    encodeSourceTokens right ++
                      token :: suffix))) =
            some
              (guardedConfig State.gateEndFirst
                parsedPrefix
                (SourceParser.packedTokenCells
                  (token :: suffix))) := by
        repeat rw [packedTokenCells_append]
        rw [SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [gate, parsedPrefix,
          List.append_assoc] using sources
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        apply safe_of_ordinary
        dsimp [parsedPrefix]
        exact ordinary_append
          (ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates count))
            (sourceCells_ordinary left))
          (sourceCells_ordinary right)
      exact
        RejectingExecution.prepend
          (gateSourcesSteps inputs done count gate)
          _ _ sourcesCanonical
          (gateEndWrongToken_exact parsedPrefix
            parsedSafe token suffix notGateEnd)
  | @rest count left right failedTokens failure ih =>
      let gate : RawGate :=
        { left := left, right := right }
      have record :=
        gateRecord_exact inputs done count gate
          (SourceParser.packedTokenCells failedTokens)
      have recordCanonical :
          workRunExact? machine
              (gateRecordSteps inputs done count gate)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (count + 1))
                (SourceParser.packedTokenCells
                  (encodeSourceTokens left ++
                    encodeSourceTokens right ++
                      .gateEnd :: failedTokens))) =
            some
              (guardedConfig State.gateStart
                (failureGatePrefix inputs
                  (done ++ [gate]) count)
                (SourceParser.packedTokenCells
                  failedTokens)) := by
        repeat rw [packedTokenCells_append]
        rw [SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [gate, gateCells,
          SourceParser.gateCells,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          cell01, cell11,
          SourceParser.cell01,
          SourceParser.cell11,
          List.append_assoc] using record
      exact
        RejectingExecution.prepend
          (gateRecordSteps inputs done count gate)
          _ _ recordCanonical
          (ih (done ++ [gate]))

def emptyRejectConfiguration : WorkConfiguration :=
  { state := State.reject
    tape :=
      { left := [cellBlank]
        head := cellBlank
        right := [] } }

def oneBitRejectConfiguration : WorkConfiguration :=
  { state := State.reject
    tape :=
      { left := [cellBlank, cellBlank]
        head := cellBlank
        right := [] } }

theorem malformedEmpty_exact :
    workRunExact? machine 6
        (workStartConfiguration machine (rawInputWorkTape [])) =
      some emptyRejectConfiguration := by
  set_option maxRecDepth 100000 in
    rfl

theorem malformedOneBit_exact :
    workRunExact? machine 7
        (workStartConfiguration machine (rawInputWorkTape [false])) =
      some oneBitRejectConfiguration := by
  set_option maxRecDepth 100000 in
    rfl

theorem emptyRejectConfiguration_outputBits :
    (encodeWorkTape emptyRejectConfiguration.tape).outputBits = [] := by
  rfl

theorem oneBitRejectConfiguration_outputBits :
    (encodeWorkTape oneBitRejectConfiguration.tape).outputBits = [] := by
  rfl

/-! ### Exact aligned circuit-token failures -/

theorem circuitMissingVersionFailure_exact :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells []))) := by
  exact
    ⟨6, emptyRejectConfiguration,
      by
        simpa [rawInputWorkTape, packWorkSymbols,
          SourceParser.packedTokenCells] using malformedEmpty_exact,
      rfl, rfl, emptyRejectConfiguration_outputBits⟩

theorem circuitWrongVersionFailure_exact
    (token : Token) (suffix : List Token)
    (notVersion : token ≠ .version0) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (token :: suffix)))) := by
  have prefixRun :=
    scannerBootToken_exact token suffix
  exact
    RejectingExecution.prepend 2 _ _ prefixRun
      (versionWrongToken_exact token suffix notVersion)

theorem circuitInputCountFailure_exact
    {tokens : List Token}
    (failure : SourceParser.NatTokenFailure tokens) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (.version0 :: tokens)))) := by
  have prefixRun :=
    versionPrefixWord_exact
      (SourceParser.packedTokenCells tokens)
  have prefixCanonical :
      workRunExact? machine 4
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (.version0 :: tokens)))) =
        some
          (guardedConfig State.inputCountFirst
            [cell00, cell00]
            (SourceParser.packedTokenCells tokens)) := by
    simpa [SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      cell00, SourceParser.cell00] using prefixRun
  have prefixSafe : SafeSourceWord [cell00, cell00] := by
    intro symbol member
    simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with rfl | rfl | impossible
    · decide
    · decide
    · contradiction
  exact
    RejectingExecution.prepend 4 _ _ prefixCanonical
      (natTokenFailure_exact .inputCount
        [cell00, cell00] failure prefixSafe)

theorem circuitGateCountFailure_exact
    (inputs : Nat) {tokens : List Token}
    (failure : SourceParser.NatTokenFailure tokens) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (.version0 ::
              (encodeNatTokens inputs ++ tokens))))) := by
  let parsedPrefix :=
    [cell00, cell00] ++ natCells inputs
  have prefixRun :=
    inputPrefixWord_exact inputs
      (SourceParser.packedTokenCells tokens)
  have prefixCanonical :
      workRunExact? machine (inputPrefixWordSteps inputs)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (.version0 ::
                  (encodeNatTokens inputs ++ tokens))))) =
        some
          (guardedConfig State.gateCountFirst
            parsedPrefix
            (SourceParser.packedTokenCells tokens)) := by
    dsimp [parsedPrefix]
    simpa [SourceParser.packedTokenCells,
      SourceParser.tokenCells, packedTokenCells_append,
      SourceParser.packedTokenCells_encodeNatTokens,
      cell00, SourceParser.cell00,
      List.append_assoc] using prefixRun
  have prefixSafe : SafeSourceWord parsedPrefix := by
    have safe :=
      packedTokenCells_safe
        (.version0 :: encodeNatTokens inputs)
    dsimp [parsedPrefix]
    simpa [SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      SourceParser.packedTokenCells_encodeNatTokens,
      cell00, SourceParser.cell00] using safe
  exact
    RejectingExecution.prepend
      (inputPrefixWordSteps inputs) _ _ prefixCanonical
      (natTokenFailure_exact .gateCount
        parsedPrefix failure prefixSafe)

theorem circuitGatesFailure_exact
    (inputs gateCount : Nat) {tokens : List Token}
    (failure :
      SourceParser.NGatesTokenFailure gateCount tokens) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitHeaderTokens
                inputs gateCount ++
              tokens)))) := by
  have headerRun :=
    headerPrefixWord_exact inputs gateCount
      (SourceParser.packedTokenCells tokens)
  have prefixEq :
      failureGatePrefix inputs [] gateCount =
        headerPrefixCells inputs gateCount := by
    simp [failureGatePrefix, placeholderGates,
      gatePrefix, SourceParser.gatePrefix,
      headerPrefixCells,
      SourceParser.markedGateListCells,
      SourceParser.countCells,
      natCells, cell00,
      SourceParser.cell00]
  have headerCanonical :
      workRunExact? machine
          (headerPrefixWordSteps inputs gateCount)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitHeaderTokens
                    inputs gateCount ++
                  tokens)))) =
        some
          (guardedConfig State.gateStart
            (failureGatePrefix inputs [] gateCount)
            (SourceParser.packedTokenCells tokens)) := by
    rw [packedTokenCells_append,
      packedCircuitHeaderTokens_eq, prefixEq]
    exact headerRun
  exact
    RejectingExecution.prepend
      (headerPrefixWordSteps inputs gateCount)
      _ _ headerCanonical
      (nGatesTokenFailure_exact
        inputs [] failure)

theorem circuitMissingProgramEndFailure_exact
    (inputs : Nat) (gates : List RawGate) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitGatesPrefixTokens
              inputs gates)))) := by
  have prefixRun :=
    circuitGatesPrefixWord_exact inputs gates []
  have prefixSafe :
      SafeSourceWord (gatePrefix inputs gates []) :=
    safe_of_ordinary
      (gatePrefix_ordinary inputs gates [])
  exact
    RejectingExecution.prepend
      (circuitGatesPrefixWordSteps inputs gates)
      _ _ (by simpa using prefixRun)
      (missingExpected_exact State.gateStart
        (gatePrefix inputs gates []) prefixSafe
        (gateStartMissingFailure_exact
          (gatePrefix inputs gates [])))

theorem circuitWrongProgramEndFailure_exact
    (inputs : Nat) (gates : List RawGate)
    (token : Token) (suffix : List Token)
    (notProgramEnd : token ≠ .programEnd) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitGatesPrefixTokens
                inputs gates ++
              token :: suffix)))) := by
  have prefixRun :=
    circuitGatesPrefixWord_exact inputs gates
      (SourceParser.packedTokenCells
        (token :: suffix))
  have prefixCanonical :
      workRunExact? machine
          (circuitGatesPrefixWordSteps inputs gates)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitGatesPrefixTokens
                    inputs gates ++
                  token :: suffix)))) =
        some
          (guardedConfig State.gateStart
            (gatePrefix inputs gates [])
            (SourceParser.packedTokenCells
              (token :: suffix))) := by
    rw [packedTokenCells_append]
    exact prefixRun
  exact
    RejectingExecution.prepend
      (circuitGatesPrefixWordSteps inputs gates)
      _ _ prefixCanonical
      (wrongProgramEndToken_exact
        inputs gates token suffix notProgramEnd)

theorem circuitOutputFailure_exact
    (inputs : Nat) (gates : List RawGate)
    {tokens : List Token}
    (failure : SourceParser.SourceTokenFailure tokens) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitGatesPrefixTokens inputs gates ++
              .programEnd :: tokens)))) := by
  have prefixRun :=
    circuitProgramPrefixWord_exact inputs gates
      (SourceParser.packedTokenCells tokens)
  have prefixCanonical :
      workRunExact? machine
          (circuitProgramPrefixWordSteps inputs gates)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitGatesPrefixTokens inputs gates ++
                  .programEnd :: tokens)))) =
        some
          (guardedConfig (State.sourceStart .output)
            (outputPrefix inputs gates)
            (SourceParser.packedTokenCells tokens)) := by
    rw [packedTokenCells_append] at prefixRun
    rw [packedTokenCells_append]
    simpa [SourceParser.packedTokenCells,
      SourceParser.tokenCells, List.append_assoc] using prefixRun
  exact
    RejectingExecution.prepend
      (circuitProgramPrefixWordSteps inputs gates)
      _ _ prefixCanonical
      (sourceTokenFailure_exact .output
        (outputPrefix inputs gates) failure
        (safe_of_ordinary
          (outputPrefix_ordinary inputs gates)))

theorem circuitMissingOutputsEndFailure_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
              inputs gates output)))) := by
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  have prefixRun :=
    circuitOutputPrefixWord_exact
      inputs gates output []
  have prefixCanonical :
      workRunExact? machine
          (circuitOutputPrefixWordSteps inputs gates output)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitOutputPrefixTokens
                  inputs gates output)))) =
        some
          (guardedConfig State.outputsEndFirst
            parsedPrefix []) := by
    simpa [parsedPrefix] using prefixRun
  exact
    RejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output)
      _ _ prefixCanonical
      (missingExpected_exact State.outputsEndFirst
        parsedPrefix
        (outputParsedPrefix_safe inputs gates output)
        (outputsEndMissingFailure_exact parsedPrefix))

theorem circuitWrongOutputsEndFailure_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) (token : Token)
    (suffix : List Token)
    (notOutputsEnd : token ≠ .outputsEnd) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
                inputs gates output ++
              token :: suffix)))) := by
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  have prefixRun :=
    circuitOutputPrefixWord_exact inputs gates output
      (SourceParser.packedTokenCells (token :: suffix))
  have prefixCanonical :
      workRunExact? machine
          (circuitOutputPrefixWordSteps inputs gates output)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitOutputPrefixTokens
                    inputs gates output ++
                  token :: suffix)))) =
        some
          (guardedConfig State.outputsEndFirst parsedPrefix
            (SourceParser.packedTokenCells
              (token :: suffix))) := by
    rw [packedTokenCells_append]
    simpa [parsedPrefix] using prefixRun
  exact
    RejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output)
      _ _ prefixCanonical
      (outputsEndWrongToken_exact parsedPrefix
        (outputParsedPrefix_safe inputs gates output)
        token suffix notOutputsEnd)

theorem circuitMissingInstanceEndFailure_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (SourceParser.circuitOutputPrefixTokens
                inputs gates output) ++
            [cell10, cell01]))) := by
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  let afterOutputs :=
    parsedPrefix ++ [cell10, cell01]
  have prefixRun :=
    circuitOutputPrefixWord_exact inputs gates output
      [cell10, cell01]
  have delimiter :=
    outputsEnd_exact parsedPrefix []
  have through :=
    exactRun_add
      (circuitOutputPrefixWordSteps inputs gates output)
      2 _ _ _ (by simpa [parsedPrefix] using prefixRun)
      delimiter
  have afterSafe : SafeSourceWord afterOutputs := by
    apply safe_append
      (outputParsedPrefix_safe inputs gates output)
    intro symbol member
    simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with rfl | rfl | impossible
    · decide
    · decide
    · contradiction
  exact
    RejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output + 2)
      _ _ (by simpa [parsedPrefix, afterOutputs] using through)
      (missingExpected_exact State.instanceEndFirst
        afterOutputs afterSafe
        (instanceEndMissingFailure_exact afterOutputs))

theorem circuitWrongInstanceEndFailure_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) (token : Token)
    (suffix : List Token)
    (notInstanceEnd : token ≠ .instanceEnd) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (SourceParser.circuitOutputPrefixTokens
                inputs gates output) ++
            [cell10, cell01] ++
              SourceParser.packedTokenCells
                (token :: suffix)))) := by
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  let afterOutputs :=
    parsedPrefix ++ [cell10, cell01]
  let tokenCells :=
    SourceParser.packedTokenCells (token :: suffix)
  have prefixRun :=
    circuitOutputPrefixWord_exact inputs gates output
      ([cell10, cell01] ++ tokenCells)
  have delimiter :=
    outputsEnd_exact parsedPrefix tokenCells
  have through :=
    exactRun_add
      (circuitOutputPrefixWordSteps inputs gates output)
      2 _ _ _ (by simpa [parsedPrefix, tokenCells] using prefixRun)
      delimiter
  have afterSafe : SafeSourceWord afterOutputs := by
    apply safe_append
      (outputParsedPrefix_safe inputs gates output)
    intro symbol member
    simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with rfl | rfl | impossible
    · decide
    · decide
    · contradiction
  exact
    RejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output + 2)
      _ _ (by
        simpa [parsedPrefix, afterOutputs, tokenCells,
          List.append_assoc] using through)
      (instanceEndWrongToken_exact afterOutputs afterSafe
        token suffix notInstanceEnd)

theorem circuitTrailingTokenFailure_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) (token : Token)
    (suffix : List Token) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (SourceParser.circuitOutputPrefixTokens
                inputs gates output) ++
            [cell10, cell01, cell10, cell11] ++
              SourceParser.packedTokenCells
                (token :: suffix)))) := by
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  let afterOutputs :=
    parsedPrefix ++ [cell10, cell01]
  let afterInstance :=
    afterOutputs ++ [cell10, cell11]
  let tokenCells :=
    SourceParser.packedTokenCells (token :: suffix)
  have prefixRun :=
    circuitOutputPrefixWord_exact inputs gates output
      ([cell10, cell01, cell10, cell11] ++ tokenCells)
  have outputsRun :=
    outputsEnd_exact parsedPrefix
      ([cell10, cell11] ++ tokenCells)
  have instanceRun :=
    instanceEnd_exact afterOutputs tokenCells
  have throughOutputs :=
    exactRun_add
      (circuitOutputPrefixWordSteps inputs gates output)
      2 _ _ _ (by simpa [parsedPrefix, tokenCells] using prefixRun)
      outputsRun
  have throughInstance :=
    exactRun_add
      (circuitOutputPrefixWordSteps inputs gates output + 2)
      2 _ _ _ (by
        simpa [afterOutputs, List.append_assoc] using
          throughOutputs)
      instanceRun
  have afterSafe : SafeSourceWord afterInstance := by
    apply safe_append
    · apply safe_append
        (outputParsedPrefix_safe inputs gates output)
      intro symbol member
      simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with rfl | rfl | impossible
      · decide
      · decide
      · contradiction
    · intro symbol member
      simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with rfl | rfl | impossible
      · decide
      · decide
      · contradiction
  exact
    RejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output + 2 + 2)
      _ _ (by
        simpa [parsedPrefix, afterOutputs, afterInstance,
          tokenCells, List.append_assoc] using throughInstance)
      (finalEOFToken_exact afterInstance afterSafe token suffix)

theorem circuitTokenFailure_exact
    {tokens : List Token}
    (failure : SourceParser.CircuitTokenFailure tokens) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells tokens))) := by
  cases failure with
  | missingVersion =>
      exact circuitMissingVersionFailure_exact
  | wrongVersion token suffix notVersion =>
      exact circuitWrongVersionFailure_exact
        token suffix notVersion
  | inputCount failure =>
      exact circuitInputCountFailure_exact failure
  | gateCount inputs failure =>
      exact circuitGateCountFailure_exact
        inputs failure
  | gates inputs gateCount failure =>
      exact circuitGatesFailure_exact
        inputs gateCount failure
  | missingProgramEnd inputs gates =>
      exact circuitMissingProgramEndFailure_exact
        inputs gates
  | wrongProgramEnd inputs gates token suffix notProgramEnd =>
      exact circuitWrongProgramEndFailure_exact
        inputs gates token suffix notProgramEnd
  | output inputs gates failure =>
      exact circuitOutputFailure_exact
        inputs gates failure
  | missingOutputsEnd inputs gates output =>
      exact circuitMissingOutputsEndFailure_exact
        inputs gates output
  | wrongOutputsEnd inputs gates output token suffix
      notOutputsEnd =>
      exact circuitWrongOutputsEndFailure_exact
        inputs gates output token suffix notOutputsEnd
  | missingInstanceEnd inputs gates output =>
      simpa [packedTokenCells_append,
        SourceParser.packedTokenCells,
        SourceParser.tokenCells,
        cell10, cell01,
        SourceParser.cell10,
        SourceParser.cell01] using
        (circuitMissingInstanceEndFailure_exact
          inputs gates output)
  | wrongInstanceEnd inputs gates output token suffix
      notInstanceEnd =>
      simpa [packedTokenCells_append,
        SourceParser.packedTokenCells,
        SourceParser.tokenCells,
        cell10, cell01,
        SourceParser.cell10,
        SourceParser.cell01,
        List.append_assoc] using
        (circuitWrongInstanceEndFailure_exact
          inputs gates output token suffix notInstanceEnd)
  | trailingToken inputs gates output token suffix =>
      simpa [packedTokenCells_append,
        SourceParser.packedTokenCells,
        SourceParser.tokenCells,
        cell10, cell01, cell11,
        SourceParser.cell10,
        SourceParser.cell01,
        SourceParser.cell11,
        List.append_assoc] using
        (circuitTrailingTokenFailure_exact
          inputs gates output token suffix)

set_option maxRecDepth 100000 in
private theorem scannerBootWord_exact
    (word : List WorkSymbol) :
    workRunExact? machine 2
        (workStartConfiguration machine
          (WorkTape.ofSymbols word)) =
      some
        (guardedConfig State.versionFirst [] word) := by
  cases word with
  | nil =>
      rfl
  | cons head rest =>
      rcases head with ⟨first, second⟩
      cases first <;> cases second <;> rfl

theorem circuitTokenFailureWithMalformedTail_exact
    {tokens : List Token}
    (failure : SourceParser.CircuitTokenFailure tokens)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells tokens ++ workTail))) := by
  cases failure with
  | missingVersion =>
      have prefixRun := scannerBootWord_exact workTail
      have tail :=
        simpleMalformedBoundary_rejecting_exact
          .versionFirst [] (by
            intro symbol member
            contradiction) malformed
      exact
        RejectingExecution.prepend 2 _ _
          (by
            simpa [SourceParser.packedTokenCells,
              SimpleMalformedBoundary.state]
              using prefixRun)
          tail
  | wrongVersion token suffix notVersion =>
      let word :=
        SourceParser.packedTokenCells (token :: suffix) ++
          workTail
      have prefixRun := scannerBootWord_exact word
      exact
        RejectingExecution.prepend 2 _ _
          (by simpa [word] using prefixRun)
          (versionWrongTokenWithMalformedTail_exact
            token suffix notVersion malformed)
  | @inputCount tokens failure =>
      let suffixWord :=
        SourceParser.packedTokenCells tokens ++ workTail
      have prefixRun := versionPrefixWord_exact suffixWord
      have prefixSafe :
          SafeSourceWord [cell00, cell00] := by
        intro symbol member
        simp only [List.mem_cons,
          List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · decide
        · decide
        · contradiction
      apply RejectingExecution.prepend 4 _ _ ?_
        (natTokenFailureWithMalformedTail_exact
          .inputCount [cell00, cell00]
          failure prefixSafe malformed)
      simpa [suffixWord, SourceParser.packedTokenCells,
        SourceParser.tokenCells,
        NatReader.state,
        cell00, SourceParser.cell00,
        List.append_assoc] using prefixRun
  | @gateCount inputs tokens failure =>
      let parsedPrefix :=
        [cell00, cell00] ++ natCells inputs
      let suffixWord :=
        SourceParser.packedTokenCells tokens ++ workTail
      have prefixRun :=
        inputPrefixWord_exact inputs suffixWord
      have prefixSafe : SafeSourceWord parsedPrefix := by
        have safe :=
          packedTokenCells_safe
            (.version0 :: encodeNatTokens inputs)
        dsimp [parsedPrefix]
        simpa [SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          SourceParser.packedTokenCells_encodeNatTokens,
          cell00, SourceParser.cell00] using safe
      apply RejectingExecution.prepend
        (inputPrefixWordSteps inputs) _ _ ?_
        (natTokenFailureWithMalformedTail_exact
          .gateCount parsedPrefix failure
          prefixSafe malformed)
      dsimp [suffixWord, parsedPrefix] at prefixRun ⊢
      simpa [SourceParser.packedTokenCells,
        SourceParser.tokenCells, packedTokenCells_append,
        SourceParser.packedTokenCells_encodeNatTokens,
        NatReader.state,
        cell00, SourceParser.cell00,
        List.append_assoc] using prefixRun
  | @gates inputs gateCount tokens failure =>
      let suffixWord :=
        SourceParser.packedTokenCells tokens ++ workTail
      have headerRun :=
        headerPrefixWord_exact inputs gateCount suffixWord
      have prefixEq :
          failureGatePrefix inputs [] gateCount =
            headerPrefixCells inputs gateCount := by
        simp [failureGatePrefix, placeholderGates,
          gatePrefix, SourceParser.gatePrefix,
          headerPrefixCells,
          SourceParser.markedGateListCells,
          SourceParser.countCells,
          natCells, cell00, SourceParser.cell00]
      apply RejectingExecution.prepend
        (headerPrefixWordSteps inputs gateCount)
        _ _ ?_
        (nGatesTokenFailureWithMalformedTail_exact
          inputs [] failure malformed)
      rw [packedTokenCells_append,
        packedCircuitHeaderTokens_eq, prefixEq]
      simpa [suffixWord, List.append_assoc] using headerRun
  | missingProgramEnd inputs gates =>
      have prefixRun :=
        circuitGatesPrefixWord_exact
          inputs gates workTail
      have tail :=
        gateMalformedTail_exact inputs gates 0 malformed
      exact
        RejectingExecution.prepend
          (circuitGatesPrefixWordSteps inputs gates)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (SourceParser.circuitGatesPrefixTokens
                    inputs gates) ++
                workTail)))
          (guardedConfig State.gateStart
            (gatePrefix inputs gates []) workTail)
          (by simpa [List.append_assoc] using prefixRun)
          (by
            simpa [failureGatePrefix,
              placeholderGates] using tail)
  | wrongProgramEnd inputs gates token suffix notProgramEnd =>
      let suffixWord :=
        SourceParser.packedTokenCells (token :: suffix) ++
          workTail
      have prefixRun :=
        circuitGatesPrefixWord_exact
          inputs gates suffixWord
      apply RejectingExecution.prepend
        (circuitGatesPrefixWordSteps inputs gates)
        _ _ ?_
        (wrongProgramEndTokenWithMalformedTail_exact
          inputs gates token suffix notProgramEnd malformed)
      rw [packedTokenCells_append]
      simpa [suffixWord, List.append_assoc] using prefixRun
  | @output inputs gates tokens failure =>
      let suffixWord :=
        SourceParser.packedTokenCells tokens ++ workTail
      have prefixRun :=
        circuitProgramPrefixWord_exact
          inputs gates suffixWord
      apply RejectingExecution.prepend
        (circuitProgramPrefixWordSteps inputs gates)
        _ _ ?_
        (sourceTokenFailureWithMalformedTail_exact
          .output (outputPrefix inputs gates)
          failure
          (safe_of_ordinary
            (outputPrefix_ordinary inputs gates))
          malformed)
      rw [packedTokenCells_append] at prefixRun
      repeat rw [packedTokenCells_append]
      simpa [suffixWord, SourceParser.packedTokenCells,
        SourceParser.tokenCells,
        List.append_assoc] using prefixRun
  | missingOutputsEnd inputs gates output =>
      let parsedPrefix :=
        outputPrefix inputs gates ++ sourceCells output
      have prefixRun :=
        circuitOutputPrefixWord_exact
          inputs gates output workTail
      apply RejectingExecution.prepend
        (circuitOutputPrefixWordSteps inputs gates output)
        _ _ ?_
        (simpleMalformedBoundary_rejecting_exact
          .outputsEnd parsedPrefix
          (outputParsedPrefix_safe inputs gates output)
          malformed)
      simpa [parsedPrefix, List.append_assoc,
        SimpleMalformedBoundary.state] using prefixRun
  | wrongOutputsEnd inputs gates output token suffix
      notOutputsEnd =>
      let parsedPrefix :=
        outputPrefix inputs gates ++ sourceCells output
      let suffixWord :=
        SourceParser.packedTokenCells (token :: suffix) ++
          workTail
      have prefixRun :=
        circuitOutputPrefixWord_exact
          inputs gates output suffixWord
      apply RejectingExecution.prepend
        (circuitOutputPrefixWordSteps inputs gates output)
        _ _ ?_
        (outputsEndWrongTokenWithMalformedTail_exact
          parsedPrefix
          (outputParsedPrefix_safe inputs gates output)
          token suffix notOutputsEnd malformed)
      rw [packedTokenCells_append]
      simpa [parsedPrefix, suffixWord,
        List.append_assoc] using prefixRun
  | missingInstanceEnd inputs gates output =>
      let parsedPrefix :=
        outputPrefix inputs gates ++ sourceCells output
      let afterOutputs :=
        parsedPrefix ++ [cell10, cell01]
      have prefixRun :=
        circuitOutputPrefixWord_exact inputs gates output
          ([cell10, cell01] ++ workTail)
      have delimiter :=
        outputsEnd_exact parsedPrefix workTail
      have through :=
        exactRun_add
          (circuitOutputPrefixWordSteps inputs gates output)
          2 _ _ _
          (by simpa [parsedPrefix] using prefixRun)
          delimiter
      have afterSafe : SafeSourceWord afterOutputs := by
        apply safe_append
          (outputParsedPrefix_safe inputs gates output)
        intro symbol member
        simp only [List.mem_cons,
          List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · decide
        · decide
        · contradiction
      apply RejectingExecution.prepend
        (circuitOutputPrefixWordSteps inputs gates output + 2)
        _ _ ?_
        (simpleMalformedBoundary_rejecting_exact
          .instanceEnd afterOutputs afterSafe malformed)
      rw [packedTokenCells_append]
      simpa [parsedPrefix, afterOutputs,
        SourceParser.packedTokenCells,
        SourceParser.tokenCells,
        cell10, cell01,
        SourceParser.cell10, SourceParser.cell01,
        List.append_assoc,
        SimpleMalformedBoundary.state] using through
  | wrongInstanceEnd inputs gates output token suffix
      notInstanceEnd =>
      let parsedPrefix :=
        outputPrefix inputs gates ++ sourceCells output
      let afterOutputs :=
        parsedPrefix ++ [cell10, cell01]
      let tokenWord :=
        SourceParser.packedTokenCells (token :: suffix) ++
          workTail
      have prefixRun :=
        circuitOutputPrefixWord_exact inputs gates output
          ([cell10, cell01] ++ tokenWord)
      have delimiter :=
        outputsEnd_exact parsedPrefix tokenWord
      have through :=
        exactRun_add
          (circuitOutputPrefixWordSteps inputs gates output)
          2 _ _ _
          (by simpa [parsedPrefix] using prefixRun)
          delimiter
      have afterSafe : SafeSourceWord afterOutputs := by
        apply safe_append
          (outputParsedPrefix_safe inputs gates output)
        intro symbol member
        simp only [List.mem_cons,
          List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · decide
        · decide
        · contradiction
      apply RejectingExecution.prepend
        (circuitOutputPrefixWordSteps inputs gates output + 2)
        _ _ ?_
        (instanceEndWrongTokenWithMalformedTail_exact
          afterOutputs afterSafe token suffix
          notInstanceEnd malformed)
      repeat rw [packedTokenCells_append]
      simpa [parsedPrefix, afterOutputs, tokenWord,
        SourceParser.packedTokenCells,
        SourceParser.tokenCells,
        cell10, cell01,
        SourceParser.cell10, SourceParser.cell01,
        List.append_assoc] using through
  | trailingToken inputs gates output token suffix =>
      let parsedPrefix :=
        outputPrefix inputs gates ++ sourceCells output
      let afterOutputs :=
        parsedPrefix ++ [cell10, cell01]
      let afterInstance :=
        afterOutputs ++ [cell10, cell11]
      let tokenWord :=
        SourceParser.packedTokenCells (token :: suffix) ++
          workTail
      have prefixRun :=
        circuitOutputPrefixWord_exact inputs gates output
          ([cell10, cell01, cell10, cell11] ++ tokenWord)
      have outputsRun :=
        outputsEnd_exact parsedPrefix
          ([cell10, cell11] ++ tokenWord)
      have instanceRun :=
        instanceEnd_exact afterOutputs tokenWord
      have throughOutputs :=
        exactRun_add
          (circuitOutputPrefixWordSteps inputs gates output)
          2 _ _ _
          (by simpa [parsedPrefix] using prefixRun)
          outputsRun
      have throughInstance :=
        exactRun_add
          (circuitOutputPrefixWordSteps inputs gates output + 2)
          2 _ _ _
          (by
            simpa [afterOutputs,
              List.append_assoc] using throughOutputs)
          instanceRun
      have afterSafe : SafeSourceWord afterInstance := by
        apply safe_append
        · apply safe_append
            (outputParsedPrefix_safe inputs gates output)
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | rfl | impossible
          · decide
          · decide
          · contradiction
        · intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | rfl | impossible
          · decide
          · decide
          · contradiction
      have tokenWordSafe : SafeSourceWord tokenWord :=
        safe_append
          (packedTokenCells_safe (token :: suffix))
          (malformedWorkTail_safe malformed)
      have tokenWordNonempty : tokenWord ≠ [] := by
        intro empty
        have lengthEq := congrArg List.length empty
        dsimp [tokenWord] at lengthEq
        simp only [List.length_append,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells_length] at lengthEq
        omega
      apply RejectingExecution.prepend
        (circuitOutputPrefixWordSteps inputs gates output + 2 + 2)
        _ _ ?_
        (finalEOFWordRejecting_exact
          afterInstance tokenWord afterSafe
          tokenWordSafe tokenWordNonempty)
      repeat rw [packedTokenCells_append]
      simpa [parsedPrefix, afterOutputs, afterInstance,
        tokenWord, SourceParser.packedTokenCells,
        SourceParser.tokenCells,
        cell10, cell01, cell11,
        SourceParser.cell10, SourceParser.cell01,
        SourceParser.cell11,
        List.append_assoc] using throughInstance

/-! ### Total strict decoder boundary -/

private theorem canonicalCircuitWithMalformedTail_exact
    (raw : RawCircuit)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    RejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (encodeCircuitTokens raw) ++ workTail))) := by
  let parsedPrefix :=
    outputPrefix raw.inputCount raw.gates ++
      sourceCells raw.output
  let afterOutputs :=
    parsedPrefix ++ [cell10, cell01]
  let afterInstance :=
    afterOutputs ++ [cell10, cell11]
  have prefixRun :=
    circuitOutputPrefixWord_exact
      raw.inputCount raw.gates raw.output
      ([cell10, cell01, cell10, cell11] ++ workTail)
  have outputsRun :=
    outputsEnd_exact parsedPrefix
      ([cell10, cell11] ++ workTail)
  have instanceRun :=
    instanceEnd_exact afterOutputs workTail
  have throughOutputs :=
    exactRun_add
      (circuitOutputPrefixWordSteps
        raw.inputCount raw.gates raw.output)
      2 _ _ _
      (by simpa [parsedPrefix] using prefixRun)
      outputsRun
  have throughInstance :=
    exactRun_add
      (circuitOutputPrefixWordSteps
          raw.inputCount raw.gates raw.output + 2)
      2 _ _ _
      (by
        simpa [afterOutputs, List.append_assoc] using
          throughOutputs)
      instanceRun
  have afterSafe : SafeSourceWord afterInstance := by
    apply safe_append
    · apply safe_append
        (outputParsedPrefix_safe
          raw.inputCount raw.gates raw.output)
      intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | rfl | impossible
      · decide
      · decide
      · contradiction
    · intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | rfl | impossible
      · decide
      · decide
      · contradiction
  apply RejectingExecution.prepend
    (circuitOutputPrefixWordSteps
      raw.inputCount raw.gates raw.output + 2 + 2)
    _ _ ?_
    (simpleMalformedBoundary_rejecting_exact
      .finalEOF afterInstance afterSafe malformed)
  rw [show
    encodeCircuitTokens raw =
      SourceParser.circuitOutputPrefixTokens
          raw.inputCount raw.gates raw.output ++
        [.outputsEnd, .instanceEnd] by
      simp [encodeCircuitTokens,
        SourceParser.circuitOutputPrefixTokens,
        SourceParser.circuitGatesPrefixTokens,
        SourceParser.circuitHeaderTokens,
        List.append_assoc]]
  repeat rw [packedTokenCells_append]
  simpa [parsedPrefix, afterOutputs, afterInstance,
    SourceParser.packedTokenCells,
    SourceParser.tokenCells,
    cell10, cell01, cell11,
    SourceParser.cell10, SourceParser.cell01,
    SourceParser.cell11,
    SimpleMalformedBoundary.state,
    List.append_assoc] using throughInstance

private theorem encodeCircuitTokens_eq_of_decodeCircuitTokens_eq_some
    (tokens : List Token) (raw : RawCircuit)
    (decoded : decodeCircuitTokens tokens = some raw) :
    encodeCircuitTokens raw = tokens := by
  cases tokens with
  | nil =>
      contradiction
  | cons first afterVersion =>
      cases first <;>
        simp only [decodeCircuitTokens] at decoded
      case version0 =>
        cases inputsEq : decodeNatTokens afterVersion with
        | none =>
            rw [inputsEq] at decoded
            contradiction
        | some decodedInputs =>
            rcases decodedInputs with
              ⟨inputs, afterInputs⟩
            rw [inputsEq] at decoded
            simp only at decoded
            cases gateCountEq :
                decodeNatTokens afterInputs with
            | none =>
                rw [gateCountEq] at decoded
                contradiction
            | some decodedGateCount =>
                rcases decodedGateCount with
                  ⟨gateCount, afterGateCount⟩
                rw [gateCountEq] at decoded
                simp only at decoded
                cases gatesEq :
                    decodeNGatesTokens gateCount
                      afterGateCount with
                | none =>
                    rw [gatesEq] at decoded
                    contradiction
                | some decodedGates =>
                    rcases decodedGates with
                      ⟨gates, afterGates⟩
                    rw [gatesEq] at decoded
                    cases afterGates with
                    | nil =>
                        contradiction
                    | cons programTerminator afterProgram =>
                        cases programTerminator <;>
                          simp only at decoded
                        case programEnd =>
                          cases outputEq :
                              decodeSourceTokens afterProgram with
                          | none =>
                              rw [outputEq] at decoded
                              contradiction
                          | some decodedOutput =>
                              rcases decodedOutput with
                                ⟨output, afterOutput⟩
                              rw [outputEq] at decoded
                              cases afterOutput with
                              | nil =>
                                  contradiction
                              | cons outputsTerminator afterOutputs =>
                                  cases outputsTerminator
                                  case outputsEnd =>
                                    cases afterOutputs with
                                    | nil =>
                                        contradiction
                                    | cons instanceTerminator trailing =>
                                        cases instanceTerminator
                                        case instanceEnd =>
                                          cases trailing with
                                          | cons extra more =>
                                              contradiction
                                          | nil =>
                                              have rawEq :
                                                  { inputCount := inputs
                                                    gates := gates
                                                    output := output } =
                                                    raw :=
                                                Option.some.inj decoded
                                              rw [← rawEq]
                                              have inputsShape :=
                                                (SourceParser.decodeNatTokens_eq_some_iff
                                                  afterVersion inputs
                                                    afterInputs).mp
                                                  inputsEq
                                              have gateCountShape :=
                                                (SourceParser.decodeNatTokens_eq_some_iff
                                                  afterInputs gateCount
                                                    afterGateCount).mp
                                                  gateCountEq
                                              have gatesShape :=
                                                (SourceParser.decodeNGatesTokens_eq_some_iff
                                                  gateCount afterGateCount
                                                    gates
                                                    (.programEnd ::
                                                      afterProgram)).mp
                                                  gatesEq
                                              have outputShape :=
                                                (SourceParser.decodeSourceTokens_eq_some_iff
                                                  afterProgram output
                                                    [.outputsEnd,
                                                      .instanceEnd]).mp
                                                  outputEq
                                              rw [inputsShape,
                                                gateCountShape,
                                                gatesShape.2,
                                                outputShape]
                                              simp [encodeCircuitTokens,
                                                gatesShape.1,
                                                List.append_assoc]
                                        all_goals contradiction
                                  all_goals contradiction
                        all_goals contradiction
      all_goals contradiction

private theorem token_bits_eq_of_ofBits_eq_some
    (first second third fourth : Bool) (token : Token)
    (decoded :
      Token.ofBits first second third fourth = some token) :
    token.bits = [first, second, third, fourth] := by
  cases first <;> cases second <;>
    cases third <;> cases fourth <;>
    cases token <;> first | rfl | contradiction

private theorem encodeTokens_eq_of_decodeTokens_eq_some
    (bits : BitString) (tokens : List Token)
    (decoded : decodeTokens bits = some tokens) :
    encodeTokens tokens = bits := by
  induction tokens generalizing bits with
  | nil =>
      cases bits with
      | nil =>
          rfl
      | cons first afterFirst =>
          cases afterFirst with
          | nil =>
              simp [decodeTokens] at decoded
          | cons second afterSecond =>
              cases afterSecond with
              | nil =>
                  simp [decodeTokens] at decoded
              | cons third afterThird =>
                  cases afterThird with
                  | nil =>
                      simp [decodeTokens] at decoded
                  | cons fourth rest =>
                      simp only [decodeTokens] at decoded
                      cases tokenEq :
                          Token.ofBits first second
                            third fourth with
                      | none =>
                          rw [tokenEq] at decoded
                          contradiction
                      | some token =>
                          cases restEq : decodeTokens rest with
                          | none =>
                              rw [tokenEq, restEq] at decoded
                              contradiction
                          | some decodedRest =>
                              rw [tokenEq, restEq] at decoded
                              have impossible :
                                  token :: decodedRest = [] :=
                                Option.some.inj decoded
                              contradiction
  | cons token rest ih =>
      cases bits with
      | nil =>
          simp [decodeTokens] at decoded
      | cons first afterFirst =>
          cases afterFirst with
          | nil =>
              contradiction
          | cons second afterSecond =>
              cases afterSecond with
              | nil =>
                  contradiction
              | cons third afterThird =>
                  cases afterThird with
                  | nil =>
                      contradiction
                  | cons fourth suffix =>
                      simp only [decodeTokens] at decoded
                      cases tokenEq :
                          Token.ofBits first second
                            third fourth with
                      | none =>
                          rw [tokenEq] at decoded
                          contradiction
                      | some decodedToken =>
                          cases suffixEq :
                              decodeTokens suffix with
                          | none =>
                              rw [tokenEq, suffixEq] at decoded
                              contradiction
                          | some decodedRest =>
                              rw [tokenEq, suffixEq] at decoded
                              have decodedEq :
                                  decodedToken :: decodedRest =
                                    token :: rest :=
                                Option.some.inj decoded
                              have headEq :
                                  decodedToken = token :=
                                (List.cons.inj decodedEq).1
                              have tailEq :
                                  decodedRest = rest :=
                                (List.cons.inj decodedEq).2
                              subst decodedToken
                              subst decodedRest
                              have tokenBits :=
                                token_bits_eq_of_ofBits_eq_some
                                  first second third fourth
                                  token tokenEq
                              have suffixBits :=
                                ih suffix suffixEq
                              simp only [encodeTokens]
                              rw [tokenBits, suffixBits]
                              rfl

/-- A four-bit framing failure has one exact rejecting execution.  The proof
uses the constructive packed-tail witness and never asks the executable
scanner to call the host decoder. -/
theorem framingFailure_exact
    (bits : BitString)
    (failure : SourceParser.TokenDecodeFailure bits) :
    RejectingExecution
      (workStartConfiguration machine
        (rawInputWorkTape bits)) := by
  rcases failure.packedShape with
    ⟨tokens, rawTail, workTail, malformed,
      _bitsEq, packedEq⟩
  have packedTokensEq :
      SourceParser.packedRawBits (encodeTokens tokens) =
        SourceParser.packedTokenCells tokens := by
    simpa [SourceParser.packedRawBits] using
      SourceParser.pack_encodeTokens tokens
  have inputEq :
      rawInputWorkTape bits =
        WorkTape.ofSymbols
          (SourceParser.packedTokenCells tokens ++
            workTail) := by
    unfold rawInputWorkTape
    change
      WorkTape.ofSymbols
          (SourceParser.packedRawBits bits) =
        WorkTape.ofSymbols
          (SourceParser.packedTokenCells tokens ++
            workTail)
    rw [packedEq, packedTokensEq]
  cases circuitEq : decodeCircuitTokens tokens with
  | none =>
      have grammarFailure :=
        (SourceParser.decodeCircuitTokens_eq_none_iff_failure
          tokens).mp circuitEq
      rw [inputEq]
      exact
        circuitTokenFailureWithMalformedTail_exact
          grammarFailure malformed
  | some raw =>
      have tokensEq :=
        encodeCircuitTokens_eq_of_decodeCircuitTokens_eq_some
          tokens raw circuitEq
      rw [inputEq]
      simpa [tokensEq] using
        (canonicalCircuitWithMalformedTail_exact
          raw malformed)

/-- Every raw bitstring rejected by the strict-v0 grammar decoder has one
exact cleanup execution ending in the reject state with empty output. -/
theorem malformed_exact
    (bits : BitString)
    (malformed : decodeCircuit bits = none) :
    RejectingExecution
      (workStartConfiguration machine
        (rawInputWorkTape bits)) := by
  cases tokenEq : decodeTokens bits with
  | none =>
      have framingFailure :=
        (SourceParser.decodeTokens_eq_none_iff_failure
          bits).mp tokenEq
      exact framingFailure_exact bits framingFailure
  | some tokens =>
      have grammarMalformed :
          decodeCircuitTokens tokens = none := by
        unfold decodeCircuit at malformed
        rw [tokenEq] at malformed
        exact malformed
      have grammarFailure :=
        (SourceParser.decodeCircuitTokens_eq_none_iff_failure
          tokens).mp grammarMalformed
      have rejection :=
        circuitTokenFailure_exact grammarFailure
      have bitsEq :=
        encodeTokens_eq_of_decodeTokens_eq_some
          bits tokens tokenEq
      have inputEq :
          rawInputWorkTape bits =
            WorkTape.ofSymbols
              (SourceParser.packedTokenCells tokens) := by
        rw [← bitsEq]
        unfold rawInputWorkTape
        rw [SourceParser.pack_encodeTokens]
      rw [inputEq]
      exact rejection

/-- The grammar-only scanner has one exact outcome on every raw bitstring:
canonical strict-v0 words accept with the source restored exactly, while every
decoder failure rejects after clearing the exposed output. -/
theorem allInput_exact
    (bits : BitString) :
    match decodeCircuit bits with
    | some raw =>
        workRunExact? machine (canonicalSteps raw)
            (workStartConfiguration machine
              (rawInputWorkTape bits)) =
          some (acceptedConfiguration raw)
    | none =>
        RejectingExecution
          (workStartConfiguration machine
            (rawInputWorkTape bits)) := by
  cases decoded : decodeCircuit bits with
  | none =>
      simpa [decoded] using
        malformed_exact bits decoded
  | some raw =>
      simpa [decoded] using
        decoded_exact bits raw decoded

/-- Cubic envelope reserved for the exact canonical and malformed traces.
The grammar-only controller uses no reference-bound round trips, so this is
deliberately no smaller than the already published parser envelope. -/
def grammarWorkBound (bitLength : Nat) : Nat :=
  SourceParser.validWorkBound bitLength

theorem grammarWorkBound_polynomial (bitLength : Nat) :
    grammarWorkBound bitLength =
      4096 * (bitLength + 1) * (bitLength + 1) *
        (bitLength + 1) := by
  rfl

private def grammarCellCube (cells : Nat) : Nat :=
  (cells + 1) * (cells + 1) * (cells + 1)

private theorem one_le_grammarCellCube (cells : Nat) :
    1 ≤ grammarCellCube cells := by
  have positive : 1 ≤ cells + 1 := by omega
  have square :
      1 ≤ (cells + 1) * (cells + 1) := by
    have product := Nat.mul_le_mul positive positive
    simpa using product
  exact Nat.le_trans square
    (by
      simpa [grammarCellCube] using
        Nat.mul_le_mul_left ((cells + 1) * (cells + 1))
          positive)

private theorem cell_le_grammarCellCube (cells : Nat) :
    cells ≤ grammarCellCube cells := by
  have successor : cells ≤ cells + 1 := by omega
  have positive : 1 ≤ cells + 1 := by omega
  have square :
      cells + 1 ≤ (cells + 1) * (cells + 1) := by
    simpa using Nat.mul_le_mul_left (cells + 1) positive
  have cube :
      (cells + 1) * (cells + 1) ≤
        grammarCellCube cells := by
    simpa [grammarCellCube] using
      Nat.mul_le_mul_left ((cells + 1) * (cells + 1))
        positive
  exact Nat.le_trans successor (Nat.le_trans square cube)

private theorem succSquare_le_grammarCellCube (cells : Nat) :
    (cells + 1) * (cells + 1) ≤
      grammarCellCube cells := by
  have positive : 1 ≤ cells + 1 := by omega
  simpa [grammarCellCube] using
    Nat.mul_le_mul_left ((cells + 1) * (cells + 1))
      positive

private theorem grammarCellCube_mono
    {left right : Nat} (bound : left ≤ right) :
    grammarCellCube left ≤ grammarCellCube right := by
  have successorBound : left + 1 ≤ right + 1 := by omega
  unfold grammarCellCube
  exact Nat.mul_le_mul
    (Nat.mul_le_mul successorBound successorBound)
    successorBound

private abbrev gateWorkspace :=
  SourceParser.gateWorkspace

private theorem gateStep_le_linearWorkspace
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (rest : List RawGate) :
    gateSteps inputs done gate rest ≤
      9 * (gateWorkspace inputs done (gate :: rest) + 1) := by
  let workspace :=
    gateWorkspace inputs done (gate :: rest)
  have prefixBound :
      (gatePrefix inputs done (gate :: rest)).length ≤
        workspace := by
    simp [workspace,
      SourceParser.gateWorkspace]
  have remainderSource :
      (sourceRemainderCells gate.left).length ≤
        (sourceCells gate.left).length := by
    rw [sourceCells_eq_first_remainder]
    simp
  have leftGate :
      (sourceCells gate.left).length ≤
        (gateCells gate).length := by
    simp [gateCells, SourceParser.gateCells]
  have gateList :
      (gateCells gate).length ≤
        (gateListCells (gate :: rest)).length := by
    simp [gateListCells, SourceParser.gateListCells]
  have listWorkspace :
      (gateListCells (gate :: rest)).length ≤
        workspace := by
    simp [workspace,
      SourceParser.gateWorkspace]
  have leftBound :
      (sourceRemainderCells gate.left).length ≤
        workspace :=
    Nat.le_trans remainderSource
      (Nat.le_trans leftGate
        (Nat.le_trans gateList listWorkspace))
  have rightGate :
      (sourceCells gate.right).length ≤
        (gateCells gate).length := by
    change
      (SourceParser.sourceCells gate.right).length ≤
        (SourceParser.gateCells gate).length
    simp [SourceParser.gateCells]
    omega
  have rightBound :
      (sourceCells gate.right).length ≤ workspace :=
    Nat.le_trans rightGate
      (Nat.le_trans gateList listWorkspace)
  unfold gateSteps
  change
    2 *
          (SourceParser.gatePrefix
            inputs done (gate :: rest)).length +
        3 +
      (sourceRemainderCells gate.left).length +
      (SourceParser.sourceCells gate.right).length +
      2 ≤
    9 * (workspace + 1)
  change
    (sourceRemainderCells gate.left).length ≤
      workspace at leftBound
  change
    (SourceParser.sourceCells gate.right).length ≤
      workspace at rightBound
  change
    (SourceParser.gatePrefix
      inputs done (gate :: rest)).length ≤
      workspace at prefixBound
  omega

private theorem gatesSteps_le_linearWorkspace
    (inputs : Nat) (done gates : List RawGate) :
    gatesSteps inputs done gates ≤
      gates.length *
        (9 * (gateWorkspace inputs done gates + 1)) := by
  induction gates generalizing done with
  | nil =>
      simp [gatesSteps]
  | cons gate rest ih =>
      have head :=
        gateStep_le_linearWorkspace inputs done gate rest
      have tail := ih (done ++ [gate])
      change
        gatesSteps inputs (done ++ [gate]) rest ≤
          rest.length *
            (9 *
              (SourceParser.gateWorkspace
                inputs (done ++ [gate]) rest + 1)) at tail
      rw [← SourceParser.gateWorkspace_step
        inputs done gate rest] at tail
      simp only [gatesSteps, List.length_cons]
      calc
        gateSteps inputs done gate rest +
              gatesSteps inputs (done ++ [gate]) rest ≤
            9 *
                (gateWorkspace inputs done (gate :: rest) + 1) +
              rest.length *
                (9 *
                  (gateWorkspace inputs done (gate :: rest) + 1)) :=
          Nat.add_le_add head tail
        _ = Nat.succ rest.length *
              (9 *
                (gateWorkspace inputs done (gate :: rest) + 1)) := by
          simp [Nat.succ_mul, Nat.add_comm]

private theorem initialGateWorkspace_le (raw : RawCircuit) :
    gateWorkspace raw.inputCount [] raw.gates ≤
      (SourceParser.circuitCells raw).length := by
  change
    SourceParser.gateWorkspace
        raw.inputCount [] raw.gates ≤
      (SourceParser.circuitCells raw).length
  simp [SourceParser.gateWorkspace,
    SourceParser.gatePrefix,
    SourceParser.circuitCells,
    SourceParser.gateListCells,
    SourceParser.countCells_length,
    SourceParser.natCells_length,
    SourceParser.markedGateListCells_length]
  omega

private theorem canonicalGateCount_le (raw : RawCircuit) :
    raw.gates.length ≤
      (SourceParser.circuitCells raw).length := by
  change
    raw.gates.length ≤
      (SourceParser.circuitCells raw).length
  simp [SourceParser.circuitCells,
    SourceParser.natCells_length]
  omega

private theorem canonicalHeaderSteps_le (raw : RawCircuit) :
    2 * raw.inputCount + 2 * raw.gates.length + 8 ≤
      (SourceParser.circuitCells raw).length := by
  change
    2 * raw.inputCount + 2 * raw.gates.length + 8 ≤
      (SourceParser.circuitCells raw).length
  simp [SourceParser.circuitCells,
    SourceParser.natCells_length]
  omega

private theorem programEndSteps_eq
    (inputs : Nat) (gates : List RawGate) :
    programEndSteps inputs gates =
      2 * (gatePrefix inputs gates []).length + 6 := by
  unfold programEndSteps
  change
    2 + 1 +
          (SourceParser.gatePrefix inputs gates []).length +
        1 +
      2 +
      2 * (inputs + 1) +
      2 * (gates.length + 1) +
      (SourceParser.markedGateListCells gates).length +
      1 + 1 =
    2 * (SourceParser.gatePrefix inputs gates []).length + 6
  simp [SourceParser.gatePrefix,
    SourceParser.countCells_length,
    SourceParser.natCells_length,
    SourceParser.markedGateListCells_length]
  omega

private theorem canonicalProgramPrefix_le (raw : RawCircuit) :
    (gatePrefix raw.inputCount raw.gates []).length ≤
      (SourceParser.circuitCells raw).length := by
  change
    (SourceParser.gatePrefix
        raw.inputCount raw.gates []).length ≤
      (SourceParser.circuitCells raw).length
  simp [SourceParser.gatePrefix,
    SourceParser.circuitCells,
    SourceParser.countCells_length,
    SourceParser.natCells_length,
    SourceParser.markedGateListCells_length]

private theorem finalRestoreSteps_eq (raw : RawCircuit) :
    finalRestoreSteps raw =
      (SourceParser.circuitCells raw).length + 6 := by
  unfold finalRestoreSteps
  rw [markedCircuitCells_length]
  change
    5 + (SourceParser.circuitCells raw).length + 1 =
      (SourceParser.circuitCells raw).length + 6
  omega

private theorem canonicalGatesSteps_le_cube (raw : RawCircuit) :
    gatesSteps raw.inputCount [] raw.gates ≤
      9 *
        grammarCellCube
          (SourceParser.circuitCells raw).length := by
  let cells := (SourceParser.circuitCells raw).length
  let workspace :=
    gateWorkspace raw.inputCount [] raw.gates
  have run :=
    gatesSteps_le_linearWorkspace
      raw.inputCount [] raw.gates
  have countBound : raw.gates.length ≤ cells + 1 := by
    have base := canonicalGateCount_le raw
    omega
  have workspaceBound : workspace + 1 ≤ cells + 1 := by
    have base := initialGateWorkspace_le raw
    omega
  have productBound :=
    Nat.mul_le_mul countBound workspaceBound
  calc
    gatesSteps raw.inputCount [] raw.gates ≤
        raw.gates.length * (9 * (workspace + 1)) := by
      simpa [workspace] using run
    _ = 9 * (raw.gates.length * (workspace + 1)) := by
      ac_rfl
    _ ≤ 9 * ((cells + 1) * (cells + 1)) :=
      Nat.mul_le_mul_left 9 productBound
    _ ≤ 9 * grammarCellCube cells :=
      Nat.mul_le_mul_left 9
        (succSquare_le_grammarCellCube cells)
    _ = 9 *
          grammarCellCube
            (SourceParser.circuitCells raw).length := by
      rfl

private theorem canonicalProgramSteps_le_cube (raw : RawCircuit) :
    programEndSteps raw.inputCount raw.gates ≤
      8 *
        grammarCellCube
          (SourceParser.circuitCells raw).length := by
  have costEq :=
    programEndSteps_eq raw.inputCount raw.gates
  have prefixBound := canonicalProgramPrefix_le raw
  have cellsBound :=
    cell_le_grammarCellCube
      (SourceParser.circuitCells raw).length
  have one :=
    one_le_grammarCellCube
      (SourceParser.circuitCells raw).length
  rw [costEq]
  omega

private theorem canonicalOutputSteps_le_cube (raw : RawCircuit) :
    (SourceParser.sourceCells raw.output).length ≤
      grammarCellCube
        (SourceParser.circuitCells raw).length := by
  have outputBound :
      (SourceParser.sourceCells raw.output).length ≤
        (SourceParser.circuitCells raw).length := by
    simp [SourceParser.circuitCells]
    omega
  exact Nat.le_trans outputBound
    (cell_le_grammarCellCube
      (SourceParser.circuitCells raw).length)

private theorem canonicalRestoreSteps_le_cube (raw : RawCircuit) :
    finalRestoreSteps raw ≤
      7 *
        grammarCellCube
          (SourceParser.circuitCells raw).length := by
  rw [finalRestoreSteps_eq]
  have cellsBound :=
    cell_le_grammarCellCube
      (SourceParser.circuitCells raw).length
  have one :=
    one_le_grammarCellCube
      (SourceParser.circuitCells raw).length
  omega

private theorem canonicalSteps_le_cellCube (raw : RawCircuit) :
    canonicalSteps raw ≤
      26 *
        grammarCellCube
          (SourceParser.circuitCells raw).length := by
  have headerBase := canonicalHeaderSteps_le raw
  have cellsBound :=
    cell_le_grammarCellCube
      (SourceParser.circuitCells raw).length
  have headerBound :
      2 * raw.inputCount + 2 * raw.gates.length + 8 ≤
        grammarCellCube
          (SourceParser.circuitCells raw).length :=
    Nat.le_trans headerBase cellsBound
  have gatesBound := canonicalGatesSteps_le_cube raw
  have programBound := canonicalProgramSteps_le_cube raw
  have outputBound := canonicalOutputSteps_le_cube raw
  have restoreBound := canonicalRestoreSteps_le_cube raw
  unfold canonicalSteps
  change
    2 * raw.inputCount + 2 * raw.gates.length + 8 +
          gatesSteps raw.inputCount [] raw.gates +
        programEndSteps raw.inputCount raw.gates +
      (SourceParser.sourceCells raw.output).length +
      finalRestoreSteps raw ≤
    26 *
      grammarCellCube
        (SourceParser.circuitCells raw).length
  omega

/-- The exact source-preserving accepting schedule fits the advertised cubic
bit-length envelope even for raw circuits with intrinsically invalid source
references. -/
theorem canonicalSteps_le_grammarWorkBound (raw : RawCircuit) :
    canonicalSteps raw ≤
      grammarWorkBound (encodeCircuit raw).length := by
  let cells := (SourceParser.circuitCells raw).length
  let bits := (encodeCircuit raw).length
  have run := canonicalSteps_le_cellCube raw
  have lengthEq := SourceParser.encodeCircuit_length_eq raw
  have cellsLeBits : cells ≤ bits := by omega
  have cubeBound :
      grammarCellCube cells ≤ grammarCellCube bits :=
    grammarCellCube_mono cellsLeBits
  have scaled := Nat.mul_le_mul_left 26 cubeBound
  have coefficient :=
    Nat.mul_le_mul_right (grammarCellCube bits)
      (show 26 ≤ 4096 by omega)
  calc
    canonicalSteps raw ≤ 26 * grammarCellCube cells := by
      simpa [cells] using run
    _ ≤ 26 * grammarCellCube bits := scaled
    _ ≤ 4096 * grammarCellCube bits := coefficient
    _ = grammarWorkBound (encodeCircuit raw).length := by
      simp [bits, grammarCellCube, grammarWorkBound,
        SourceParser.validWorkBound, Nat.mul_assoc]

/-! ### Constructive malformed-input accounting

The exact rejection theorems above intentionally expose only a proposition.
The bounded companions below therefore rebuild the same literal cleanup
traces while carrying their arithmetic charge.  They never select a witness
from an existential proof and never appeal to the strict parser's different
machine.
-/

private def BoundedRejectingExecution
    (initial : WorkConfiguration) (bound : Nat) : Prop :=
  ∃ steps final,
    steps ≤ bound ∧
    workRunExact? machine steps initial = some final ∧
    machine.isHalted final = true ∧
    final.state = State.reject ∧
    (encodeWorkTape final.tape).outputBits = []

private theorem BoundedRejectingExecution.prepend
    (prefixSteps tailBound : Nat)
    (initial middle : WorkConfiguration)
    (prefixRun :
      workRunExact? machine prefixSteps initial = some middle)
    (tail :
      BoundedRejectingExecution middle tailBound) :
    BoundedRejectingExecution initial
      (prefixSteps + tailBound) := by
  rcases tail with
    ⟨tailSteps, final, bounded, tailRun, halted,
      finalState, outputEmpty⟩
  exact
    ⟨prefixSteps + tailSteps, final,
      Nat.add_le_add_left bounded prefixSteps,
      exactRun_add prefixSteps tailSteps
        initial middle final prefixRun tailRun,
      halted, finalState, outputEmpty⟩

private theorem safeExplicitFailure_bounded_exact
    (word parsedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (initial : WorkConfiguration) (launchSteps : Nat)
    (shape : word = parsedPrefix ++ current :: rest)
    (safe : SafeSourceWord word)
    (launch :
      workRunExact? machine launchSteps initial =
        some
          (cleanupSeekConfiguration
            [] (current :: pushCrossed parsedPrefix []) rest)) :
    BoundedRejectingExecution initial
      (launchSteps + 2 * word.length + 2) := by
  let scan := current :: pushCrossed parsedPrefix []
  have forwardEq :
      pushCleanupScan scan rest = word := by
    dsimp [scan]
    rw [explicitFailureForward_eq, ← shape]
  have noGuard :
      ∀ symbol, symbol ∈ scan →
        symbol ≠ leftGuard := by
    intro symbol member
    exact
      (safe symbol
        (by
          rw [← forwardEq]
          exact
            (pushCleanupScan_mem_iff
              scan rest symbol).mpr (Or.inl member))).1
  have nonblank :
      ∀ symbol,
        symbol ∈ pushCleanupScan scan rest →
          symbol ≠ cellBlank := by
    intro symbol member
    exact (safe symbol (by rwa [forwardEq] at member)).2
  have cleanup :=
    guardedCleanupFinite_exact
      [] scan rest noGuard nonblank
  let cleanupSteps := guardedCleanupSteps scan rest
  let final := cleanupRejectConfiguration [] scan rest []
  have cleanupBound :
      cleanupSteps ≤ 2 * word.length + 2 := by
    have closed :=
      SourceParser.guardedCleanupSteps_eq scan rest
    dsimp [cleanupSteps]
    change
      SourceParser.guardedCleanupSteps scan rest ≤
        2 * word.length + 2
    rw [closed]
    have shapeLength := congrArg List.length shape
    have crossedLength :
        (pushCrossed parsedPrefix []).length =
          parsedPrefix.length := by
      rw [pushCrossed_eq_reverse_append]
      simp
    dsimp [scan]
    simp only [List.length_cons, List.length_append] at shapeLength ⊢
    rw [crossedLength]
    omega
  refine
    ⟨launchSteps + cleanupSteps, final,
      Nat.add_le_add_left cleanupBound launchSteps,
      ?_, ?_, rfl, ?_⟩
  · exact
      exactRun_add launchSteps cleanupSteps
        initial
        (cleanupSeekConfiguration
          [] (current :: pushCrossed parsedPrefix []) rest)
        final launch (by simpa [cleanupSteps, final] using cleanup)
  · exact cleanupReject_isHalted [] scan rest []
  · exact cleanupReject_output_empty [] scan rest

private theorem missingEndTailSteps_le
    (parsedPrefix : List WorkSymbol) :
    let crossed := pushCrossed parsedPrefix []
    missingEndTailSteps crossed ≤
      2 * parsedPrefix.length + 4 := by
  dsimp only
  unfold missingEndTailSteps
  have closed :=
    SourceParser.guardedCleanupExplicitSteps_eq
      (missingEndScan (pushCrossed parsedPrefix []))
      (missingEndEraseWord (pushCrossed parsedPrefix []))
  change
    1 +
        SourceParser.guardedCleanupExplicitSteps
          (missingEndScan (pushCrossed parsedPrefix []))
          (missingEndEraseWord (pushCrossed parsedPrefix [])) ≤
      2 * parsedPrefix.length + 4
  rw [closed]
  have crossedLength :
      (pushCrossed parsedPrefix []).length =
        parsedPrefix.length := by
    rw [pushCrossed_eq_reverse_append]
    simp
  simp [missingEndScan, missingEndEraseWord,
    pushCleanupScan, SourceParser.pushCleanupScan_length,
    crossedLength]
  omega

private theorem unaryUnitCells_length_bounded
    (units : Nat) :
    (unaryUnitCells units).length = 2 * units := by
  induction units with
  | zero =>
      rfl
  | succ units ih =>
      simp only [unaryUnitCells, List.length_cons, ih]
      omega

private theorem natTokenFailure_bounded_exact
    (reader : NatReader) (parsedPrefix : List WorkSymbol)
    {tokens : List Token}
    (failure : SourceParser.NatTokenFailure tokens)
    (prefixSafe : SafeSourceWord parsedPrefix) :
    BoundedRejectingExecution
      (guardedConfig reader.state parsedPrefix
        (SourceParser.packedTokenCells tokens))
      (8 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells tokens).length + 1)) := by
  cases failure with
  | missingEnd units =>
      let parsed := parsedPrefix ++ unaryUnitCells units
      let crossed := pushCrossed parsed []
      have unitsRun :=
        natReaderUnits_exact reader units
          (pushCrossed parsedPrefix [leftGuard]) []
      have unitsCanonical :
          workRunExact? machine (2 * units)
              (guardedConfig reader.state parsedPrefix
                (unaryUnitCells units)) =
            some
              (guardedConfig reader.state parsed []) := by
        unfold guardedConfig
        simpa [parsed, pushCrossed_append] using unitsRun
      have failed :=
        natReaderMissingFailure_exact reader parsed
      have parsedSafe :
          SafeSourceWord parsed :=
        safe_append prefixSafe (unaryUnitCells_safe units)
      have tailRun :
          workRunExact? machine
              (missingEndTailSteps crossed)
              (guardedConfig reader.state parsed []) =
            some
              (cleanupExplicitRejectConfiguration
                [] (missingEndEraseWord crossed) []) := by
        have base :=
          missingEndTail_exact reader.state parsed crossed rfl
            parsedSafe
            (by
              unfold guardedConfig at failed
              rw [pushCrossed_eq_reverse_append] at failed
              simpa [crossed, pushCrossed_eq_reverse_append]
                using failed)
        unfold guardedConfig
        rw [pushCrossed_eq_reverse_append]
        simpa [crossed, pushCrossed_eq_reverse_append] using base
      have tailBound :
          missingEndTailSteps crossed ≤
            2 * parsed.length + 4 := by
        simpa [crossed] using missingEndTailSteps_le parsed
      have totalBound :
          2 * units + missingEndTailSteps crossed ≤
            8 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells
                  (List.replicate units .unit)).length + 1) := by
        rw [packedTokenCells_replicate_unit]
        dsimp [parsed] at tailBound
        simp only [List.length_append] at tailBound
        rw [unaryUnitCells_length_bounded] at tailBound ⊢
        omega
      refine
        ⟨2 * units + missingEndTailSteps crossed,
          cleanupExplicitRejectConfiguration
            [] (missingEndEraseWord crossed) [],
          totalBound, ?_, ?_, rfl, ?_⟩
      · have complete :=
          exactRun_add (2 * units)
            (missingEndTailSteps crossed)
            _ _ _ unitsCanonical tailRun
        simpa [packedTokenCells_replicate_unit] using complete
      · exact cleanupExplicitReject_isHalted
          [] (missingEndEraseWord crossed) []
      · exact cleanupExplicitReject_output_empty
          [] (missingEndEraseWord crossed)
  | wrongToken units token suffix notUnit notNatEnd =>
      let tokens :=
        List.replicate units Token.unit ++ token :: suffix
      let parsed := parsedPrefix ++ unaryUnitCells units
      let suffixCells := SourceParser.packedTokenCells suffix
      let initial :=
        guardedConfig reader.state parsedPrefix
          (SourceParser.packedTokenCells tokens)
      have wordShape :
          SourceParser.packedTokenCells tokens =
            unaryUnitCells units ++
              SourceParser.tokenCells token ++ suffixCells := by
        dsimp [tokens, suffixCells]
        rw [packedTokenCells_append,
          packedTokenCells_replicate_unit]
        simp [SourceParser.packedTokenCells, List.append_assoc]
      have unitsRun :=
        natReaderUnits_exact reader units
          (pushCrossed parsedPrefix [leftGuard])
          (SourceParser.tokenCells token ++ suffixCells)
      have prefixRun :
          workRunExact? machine (2 * units) initial =
            some
              (guardedConfig reader.state parsed
                (SourceParser.tokenCells token ++ suffixCells)) := by
        unfold initial guardedConfig
        rw [wordShape]
        simpa [parsed, pushCrossed_append] using unitsRun
      have allWordSafe :
          SafeSourceWord
            (parsedPrefix ++
              SourceParser.packedTokenCells tokens) :=
        safe_append prefixSafe (packedTokenCells_safe tokens)
      have widen
          (launchSteps : Nat)
          (result :
            BoundedRejectingExecution initial
              (launchSteps +
                2 *
                  (parsedPrefix ++
                    SourceParser.packedTokenCells tokens).length +
                2))
          (launchBound : launchSteps ≤ 2 * units + 2) :
          BoundedRejectingExecution initial
            (8 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells tokens).length + 1)) := by
        rcases result with
          ⟨steps, final, bounded, run, halted,
            finalState, outputEmpty⟩
        refine
          ⟨steps, final, Nat.le_trans bounded ?_,
            run, halted, finalState, outputEmpty⟩
        have tokenLength :
            (SourceParser.tokenCells token).length = 2 :=
          SourceParser.tokenCells_length token
        have shapeLength := congrArg List.length wordShape
        simp only [List.length_append, tokenLength] at shapeLength
        rw [unaryUnitCells_length_bounded] at shapeLength
        simp only [List.length_append] at bounded ⊢
        omega
      have rejectFirst
          (current next : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [current, next])
          (wrong : current ≠ cell00) :
          BoundedRejectingExecution initial
            (8 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells tokens).length + 1)) := by
        have failed :=
          natReaderFirstFailure_exact reader parsed
            current (next :: suffixCells) wrong
        have launch :=
          exactRun_add (2 * units) 1
            _ _ _ prefixRun
            (by simpa [cellsEq] using failed)
        have shape :
            parsedPrefix ++
                SourceParser.packedTokenCells tokens =
              parsed ++ current :: next :: suffixCells := by
          rw [wordShape, cellsEq]
          simp [parsed, List.append_assoc]
        apply widen (2 * units + 1)
        · exact
            safeExplicitFailure_bounded_exact
              (parsedPrefix ++
                SourceParser.packedTokenCells tokens)
              parsed current (next :: suffixCells)
              initial (2 * units + 1)
              shape allWordSafe launch
        · omega
      have rejectSecond
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell00, current])
          (notUnitCell : current ≠ cell01)
          (notEndCell : current ≠ cell10) :
          BoundedRejectingExecution initial
            (8 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells tokens).length + 1)) := by
        have failed :=
          natReaderSecondFailure_exact reader parsed current
            suffixCells notUnitCell notEndCell
        have launch :=
          exactRun_add (2 * units) 2
            _ _ _ prefixRun
            (by simpa [cellsEq] using failed)
        have shape :
            parsedPrefix ++
                SourceParser.packedTokenCells tokens =
              (parsed ++ [cell00]) ++ current :: suffixCells := by
          rw [wordShape, cellsEq]
          simp [parsed, List.append_assoc]
        apply widen (2 * units + 2)
        · exact
            safeExplicitFailure_bounded_exact
              (parsedPrefix ++
                SourceParser.packedTokenCells tokens)
              (parsed ++ [cell00]) current suffixCells
              initial (2 * units + 2)
              shape allWordSafe launch
        · omega
      cases token with
      | version0 =>
          exact rejectSecond cell00 rfl (by decide) (by decide)
      | unit =>
          exact False.elim (notUnit rfl)
      | natEnd =>
          exact False.elim (notNatEnd rfl)
      | input =>
          exact rejectSecond cell11 rfl (by decide) (by decide)
      | constantFalse =>
          exact rejectFirst cell01 cell00 rfl (by decide)
      | constantTrue =>
          exact rejectFirst cell01 cell01 rfl (by decide)
      | gate =>
          exact rejectFirst cell01 cell10 rfl (by decide)
      | gateEnd =>
          exact rejectFirst cell01 cell11 rfl (by decide)
      | programEnd =>
          exact rejectFirst cell10 cell00 rfl (by decide)
      | outputsEnd =>
          exact rejectFirst cell10 cell01 rfl (by decide)
      | threshold =>
          exact rejectFirst cell10 cell10 rfl (by decide)
      | instanceEnd =>
          exact rejectFirst cell10 cell11 rfl (by decide)

private theorem sourceTokenFailure_bounded_exact
    (continuation : SourceContinuation)
    (parsedPrefix : List WorkSymbol)
    {tokens : List Token}
    (failure : SourceParser.SourceTokenFailure tokens)
    (prefixSafe : SafeSourceWord parsedPrefix) :
    BoundedRejectingExecution
      (guardedConfig (State.sourceStart continuation)
        parsedPrefix
        (SourceParser.packedTokenCells tokens))
      (16 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells tokens).length + 1)) := by
  cases failure with
  | missing =>
      let crossed := pushCrossed parsedPrefix []
      have failed :=
        sourceMissingFailure_exact continuation parsedPrefix
      have tailRun :
          workRunExact? machine
              (missingEndTailSteps crossed)
              (guardedConfig (State.sourceStart continuation)
                parsedPrefix []) =
            some
              (cleanupExplicitRejectConfiguration
                [] (missingEndEraseWord crossed) []) := by
        have base :=
          missingEndTail_exact
            (State.sourceStart continuation)
            parsedPrefix crossed rfl prefixSafe
            (by
              unfold guardedConfig at failed
              rw [pushCrossed_eq_reverse_append] at failed
              simpa [crossed, pushCrossed_eq_reverse_append]
                using failed)
        unfold guardedConfig
        rw [pushCrossed_eq_reverse_append]
        simpa [crossed, pushCrossed_eq_reverse_append] using base
      have bound :
          missingEndTailSteps crossed ≤
            16 * (parsedPrefix.length + 0 + 1) := by
        have linear :
            missingEndTailSteps crossed ≤
              2 * parsedPrefix.length + 4 := by
          simpa [crossed] using
            missingEndTailSteps_le parsedPrefix
        omega
      refine
        ⟨missingEndTailSteps crossed,
          cleanupExplicitRejectConfiguration
            [] (missingEndEraseWord crossed) [],
          ?_, ?_, ?_, rfl, ?_⟩
      · simpa [SourceParser.packedTokenCells] using bound
      · simpa [SourceParser.packedTokenCells] using tailRun
      · exact cleanupExplicitReject_isHalted
          [] (missingEndEraseWord crossed) []
      · exact cleanupExplicitReject_output_empty
          [] (missingEndEraseWord crossed)
  | wrongHead token suffix notInput notFalse notTrue notGate =>
      let suffixCells := SourceParser.packedTokenCells suffix
      let initial :=
        guardedConfig (State.sourceStart continuation)
          parsedPrefix
          (SourceParser.packedTokenCells (token :: suffix))
      have allWordSafe :
          SafeSourceWord
            (parsedPrefix ++
              SourceParser.packedTokenCells (token :: suffix)) :=
        safe_append prefixSafe
          (packedTokenCells_safe (token :: suffix))
      have widen
          (launchSteps : Nat)
          (result :
            BoundedRejectingExecution initial
              (launchSteps +
                2 *
                  (parsedPrefix ++
                    SourceParser.packedTokenCells
                      (token :: suffix)).length +
                2))
          (launchBound : launchSteps ≤ 2) :
          BoundedRejectingExecution initial
            (16 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells
                  (token :: suffix)).length + 1)) := by
        rcases result with
          ⟨steps, final, bounded, run, halted,
            finalState, outputEmpty⟩
        refine
          ⟨steps, final, Nat.le_trans bounded ?_,
            run, halted, finalState, outputEmpty⟩
        simp only [List.length_append] at bounded ⊢
        omega
      have rejectFirst
          (current next : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [current, next])
          (not00 : current ≠ cell00)
          (not01 : current ≠ cell01) :
          BoundedRejectingExecution initial
            (16 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells
                  (token :: suffix)).length + 1)) := by
        have failed :=
          sourceStartFirstFailure_exact continuation parsedPrefix
            current (next :: suffixCells) not00 not01
        have shape :
            parsedPrefix ++
                SourceParser.packedTokenCells (token :: suffix) =
              parsedPrefix ++ current :: next :: suffixCells := by
          simp [SourceParser.packedTokenCells, cellsEq, suffixCells]
        apply widen 1
        · apply
            safeExplicitFailure_bounded_exact
              (parsedPrefix ++
                SourceParser.packedTokenCells (token :: suffix))
              parsedPrefix current (next :: suffixCells)
              initial 1 shape allWordSafe
          simpa [initial, SourceParser.packedTokenCells,
            cellsEq, suffixCells] using failed
        · omega
      have rejectAfter00
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell00, current])
          (not11 : current ≠ cell11) :
          BoundedRejectingExecution initial
            (16 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells
                  (token :: suffix)).length + 1)) := by
        have failed :=
          sourceAfter00Failure_exact continuation parsedPrefix
            current suffixCells not11
        have shape :
            parsedPrefix ++
                SourceParser.packedTokenCells (token :: suffix) =
              (parsedPrefix ++ [cell00]) ++
                current :: suffixCells := by
          simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells]
        apply widen 2
        · apply
            safeExplicitFailure_bounded_exact
              (parsedPrefix ++
                SourceParser.packedTokenCells (token :: suffix))
              (parsedPrefix ++ [cell00]) current suffixCells
              initial 2 shape allWordSafe
          simpa [initial, SourceParser.packedTokenCells,
            cellsEq, suffixCells] using failed
        · omega
      have rejectAfter01
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell01, current])
          (not00 : current ≠ cell00)
          (not01 : current ≠ cell01)
          (not10 : current ≠ cell10) :
          BoundedRejectingExecution initial
            (16 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells
                  (token :: suffix)).length + 1)) := by
        have failed :=
          sourceAfter01Failure_exact continuation parsedPrefix
            current suffixCells not00 not01 not10
        have shape :
            parsedPrefix ++
                SourceParser.packedTokenCells (token :: suffix) =
              (parsedPrefix ++ [cell01]) ++
                current :: suffixCells := by
          simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells]
        apply widen 2
        · apply
            safeExplicitFailure_bounded_exact
              (parsedPrefix ++
                SourceParser.packedTokenCells (token :: suffix))
              (parsedPrefix ++ [cell01]) current suffixCells
              initial 2 shape allWordSafe
          simpa [initial, SourceParser.packedTokenCells,
            cellsEq, suffixCells] using failed
        · omega
      cases token with
      | version0 =>
          exact rejectAfter00 cell00 rfl (by decide)
      | unit =>
          exact rejectAfter00 cell01 rfl (by decide)
      | natEnd =>
          exact rejectAfter00 cell10 rfl (by decide)
      | input =>
          exact False.elim (notInput rfl)
      | constantFalse =>
          exact False.elim (notFalse rfl)
      | constantTrue =>
          exact False.elim (notTrue rfl)
      | gate =>
          exact False.elim (notGate rfl)
      | gateEnd =>
          exact rejectAfter01 cell11 rfl
            (by decide) (by decide) (by decide)
      | programEnd =>
          exact rejectFirst cell10 cell00 rfl
            (by decide) (by decide)
      | outputsEnd =>
          exact rejectFirst cell10 cell01 rfl
            (by decide) (by decide)
      | threshold =>
          exact rejectFirst cell10 cell10 rfl
            (by decide) (by decide)
      | instanceEnd =>
          exact rejectFirst cell10 cell11 rfl
            (by decide) (by decide)
  | @inputIndex indexTokens failure =>
      let nextPrefix := parsedPrefix ++ [cell00, cell11]
      have launch :
          workRunExact? machine 2
              (guardedConfig (State.sourceStart continuation)
                parsedPrefix
                (cell00 :: cell11 ::
                  SourceParser.packedTokenCells indexTokens)) =
            some
              (guardedConfig
                (State.sourceNatFirst continuation)
                nextPrefix
                (SourceParser.packedTokenCells indexTokens)) := by
        unfold guardedConfig
        simp [nextPrefix, pushCrossed_append, pushCrossed]
        set_option maxRecDepth 100000 in
          cases continuation <;> rfl
      have nextSafe :
          SafeSourceWord nextPrefix := by
        apply safe_append prefixSafe
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · decide
        · decide
        · contradiction
      have tail :=
        natTokenFailure_bounded_exact
          (.source continuation) nextPrefix failure nextSafe
      have joined :=
        BoundedRejectingExecution.prepend
          2
          (8 *
            (nextPrefix.length +
              (SourceParser.packedTokenCells indexTokens).length + 1))
          _ _ (by
            simpa [SourceParser.packedTokenCells,
              SourceParser.tokenCells, NatReader.state,
              cell00, cell11, SourceParser.cell00,
              SourceParser.cell11] using launch)
          tail
      rcases joined with
        ⟨steps, final, bounded, run, halted,
          finalState, outputEmpty⟩
      refine
        ⟨steps, final, Nat.le_trans bounded ?_,
          run, halted, finalState, outputEmpty⟩
      simp only [nextPrefix, List.length_append,
        List.length_cons, List.length_nil,
        SourceParser.packedTokenCells,
        SourceParser.tokenCells_length]
      omega
  | @gateIndex indexTokens failure =>
      let nextPrefix := parsedPrefix ++ [cell01, cell10]
      have launch :
          workRunExact? machine 2
              (guardedConfig (State.sourceStart continuation)
                parsedPrefix
                (cell01 :: cell10 ::
                  SourceParser.packedTokenCells indexTokens)) =
            some
              (guardedConfig
                (State.sourceNatFirst continuation)
                nextPrefix
                (SourceParser.packedTokenCells indexTokens)) := by
        unfold guardedConfig
        simp [nextPrefix, pushCrossed_append, pushCrossed]
        set_option maxRecDepth 100000 in
          cases continuation <;> rfl
      have nextSafe :
          SafeSourceWord nextPrefix := by
        apply safe_append prefixSafe
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · decide
        · decide
        · contradiction
      have tail :=
        natTokenFailure_bounded_exact
          (.source continuation) nextPrefix failure nextSafe
      have joined :=
        BoundedRejectingExecution.prepend
          2
          (8 *
            (nextPrefix.length +
              (SourceParser.packedTokenCells indexTokens).length + 1))
          _ _ (by
            simpa [SourceParser.packedTokenCells,
              SourceParser.tokenCells, NatReader.state,
              cell01, cell10, SourceParser.cell01,
              SourceParser.cell10] using launch)
          tail
      rcases joined with
        ⟨steps, final, bounded, run, halted,
          finalState, outputEmpty⟩
      refine
        ⟨steps, final, Nat.le_trans bounded ?_,
          run, halted, finalState, outputEmpty⟩
      simp only [nextPrefix, List.length_append,
        List.length_cons, List.length_nil,
        SourceParser.packedTokenCells,
        SourceParser.tokenCells_length]
      omega

private theorem missingExpected_bounded_exact
    (state : Nat) (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (failure :
      workRunExact? machine 1
          (guardedConfig state parsedPrefix []) =
        some
          (cleanupSeekConfiguration
            [] (missingEndScan
              (pushCrossed parsedPrefix [])) [])) :
    BoundedRejectingExecution
      (guardedConfig state parsedPrefix [])
      (8 * (parsedPrefix.length + 1)) := by
  let crossed := pushCrossed parsedPrefix []
  have tailRun :=
    missingEndTail_exact state parsedPrefix crossed
      rfl prefixSafe (by
        unfold guardedConfig at failure
        rw [pushCrossed_eq_reverse_append] at failure
        simpa [crossed, pushCrossed_eq_reverse_append]
          using failure)
  have bounded :
      missingEndTailSteps crossed ≤
        8 * (parsedPrefix.length + 1) := by
    have linear :
        missingEndTailSteps crossed ≤
          2 * parsedPrefix.length + 4 := by
      simpa [crossed] using
        missingEndTailSteps_le parsedPrefix
    omega
  refine
    ⟨missingEndTailSteps crossed,
      cleanupExplicitRejectConfiguration
        [] (missingEndEraseWord crossed) [],
      bounded, ?_, ?_, rfl, ?_⟩
  · unfold guardedConfig
    rw [pushCrossed_eq_reverse_append]
    simpa [crossed, pushCrossed_eq_reverse_append]
      using tailRun
  · exact cleanupExplicitReject_isHalted
      [] (missingEndEraseWord crossed) []
  · exact cleanupExplicitReject_output_empty
      [] (missingEndEraseWord crossed)

private theorem sourceAfter00_bounded_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (tailSafe : SafeSourceWord (current :: rest))
    (not11 : current ≠ cell11) :
    BoundedRejectingExecution
      (guardedConfig (State.sourceAfter00 .gateLeft)
        parsedPrefix (current :: rest))
      (8 *
        (parsedPrefix.length + (current :: rest).length + 1)) := by
  let initial :=
    guardedConfig (State.sourceAfter00 .gateLeft)
      parsedPrefix (current :: rest)
  have launch :=
    sourceAfter00ImmediateFailure_exact
      parsedPrefix current rest not11
  have boundedRun :=
    safeExplicitFailure_bounded_exact
      (parsedPrefix ++ current :: rest)
      parsedPrefix current rest initial 1 rfl
      (safe_append prefixSafe tailSafe)
      (by simpa [initial] using launch)
  rcases boundedRun with
    ⟨steps, final, bounded, run, halted,
      finalState, outputEmpty⟩
  refine
    ⟨steps, final, Nat.le_trans bounded ?_,
      run, halted, finalState, outputEmpty⟩
  simp only [List.length_append, List.length_cons]
  omega

private theorem sourceAfter01_bounded_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (tailSafe : SafeSourceWord (current :: rest))
    (not00 : current ≠ cell00)
    (not01 : current ≠ cell01)
    (not10 : current ≠ cell10) :
    BoundedRejectingExecution
      (guardedConfig (State.sourceAfter01 .gateLeft)
        parsedPrefix (current :: rest))
      (8 *
        (parsedPrefix.length + (current :: rest).length + 1)) := by
  let initial :=
    guardedConfig (State.sourceAfter01 .gateLeft)
      parsedPrefix (current :: rest)
  have launch :=
    sourceAfter01ImmediateFailure_exact
      parsedPrefix current rest not00 not01 not10
  have boundedRun :=
    safeExplicitFailure_bounded_exact
      (parsedPrefix ++ current :: rest)
      parsedPrefix current rest initial 1 rfl
      (safe_append prefixSafe tailSafe)
      (by simpa [initial] using launch)
  rcases boundedRun with
    ⟨steps, final, bounded, run, halted,
      finalState, outputEmpty⟩
  refine
    ⟨steps, final, Nat.le_trans bounded ?_,
      run, halted, finalState, outputEmpty⟩
  simp only [List.length_append, List.length_cons]
  omega

private theorem programEndSecond_bounded_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (tailSafe : SafeSourceWord (current :: rest))
    (not00 : current ≠ cell00) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart parsedPrefix
        (cell10 :: current :: rest))
      (8 *
        (parsedPrefix.length +
          (cell10 :: current :: rest).length + 1)) := by
  let initial :=
    guardedConfig State.gateStart parsedPrefix
      (cell10 :: current :: rest)
  let parsedAfterCursor :=
    parsedPrefix ++ [cursorMark]
  have launch :=
    programEndSecondFailure_exact parsedPrefix
      current rest not00
  have cursorSafe : SafeSourceWord [cursorMark] := by
    intro symbol member
    simp only [List.mem_cons,
      List.not_mem_nil] at member
    rcases member with rfl | impossible
    · decide
    · contradiction
  have internalSafe :
      SafeSourceWord
        (parsedAfterCursor ++ current :: rest) :=
    safe_append
      (safe_append prefixSafe cursorSafe) tailSafe
  have boundedRun :=
    safeExplicitFailure_bounded_exact
      (parsedAfterCursor ++ current :: rest)
      parsedAfterCursor current rest initial 2 rfl
      internalSafe
      (by simpa [initial, parsedAfterCursor] using launch)
  rcases boundedRun with
    ⟨steps, final, bounded, run, halted,
      finalState, outputEmpty⟩
  refine
    ⟨steps, final, Nat.le_trans bounded ?_,
      run, halted, finalState, outputEmpty⟩
  simp only [parsedAfterCursor, List.length_append,
    List.length_cons, List.length_nil]
  omega

private theorem cleanupMissingSeek_bounded_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix) :
    BoundedRejectingExecution
      (cleanupSeekConfiguration
        []
        (missingEndScan
          (pushCrossed parsedPrefix []))
        [])
      (8 * (parsedPrefix.length + 1)) := by
  let crossed := pushCrossed parsedPrefix []
  let scan := missingEndScan crossed
  let eraseWord := missingEndEraseWord crossed
  have scanNoGuard :
      ∀ symbol, symbol ∈ scan →
        symbol ≠ leftGuard := by
    intro symbol member
    simp only [scan, missingEndScan,
      List.mem_cons] at member
    rcases member with blankEq | crossedMember
    · subst symbol
      decide
    · dsimp [crossed] at crossedMember
      rw [pushCrossed_eq_reverse_append] at crossedMember
      have member' :
          symbol ∈ parsedPrefix.reverse := by
        simpa using crossedMember
      exact
        (prefixSafe symbol (by simpa using member')).1
  have eraseNonblank :
      ∀ symbol, symbol ∈ eraseWord →
        symbol ≠ cellBlank := by
    intro symbol member
    dsimp [eraseWord, missingEndEraseWord] at member
    have materialized :
        pushCleanupScan
            (pushCrossed parsedPrefix []) [] =
          parsedPrefix := by
      simpa [pushCleanupScan, SourceParser.pushCleanupScan] using
        (pushCleanupScan_pushCrossed parsedPrefix [] [])
    rw [materialized] at member
    exact (prefixSafe symbol member).2
  have forwardShape :
      pushCleanupScan scan [] =
        eraseWord ++ cellBlank :: [] := by
    dsimp [scan, eraseWord]
    unfold missingEndScan missingEndEraseWord
    rw [pushCleanupScan, SourceParser.pushCleanupScan]
    simpa using
      (SourceParser.pushCleanupScan_append crossed []
        [cellBlank])
  have cleanup :=
    guardedCleanupExplicit_exact
      [] scan [] eraseWord []
      scanNoGuard forwardShape eraseNonblank
  have stepBound :
      guardedCleanupExplicitSteps scan eraseWord ≤
        8 * (parsedPrefix.length + 1) := by
    have closed :=
      SourceParser.guardedCleanupExplicitSteps_eq scan eraseWord
    change
      SourceParser.guardedCleanupExplicitSteps scan eraseWord ≤
        8 * (parsedPrefix.length + 1)
    rw [closed]
    dsimp [scan, eraseWord, crossed]
    rw [pushCrossed_eq_reverse_append]
    simp [missingEndScan, missingEndEraseWord,
      pushCleanupScan, SourceParser.pushCleanupScan_length]
    omega
  refine
    ⟨guardedCleanupExplicitSteps scan eraseWord,
      cleanupExplicitRejectConfiguration
        [] eraseWord [],
      stepBound, ?_, ?_, rfl, ?_⟩
  · simpa [scan] using cleanup
  · exact cleanupExplicitReject_isHalted
      [] eraseWord []
  · exact cleanupExplicitReject_output_empty
      [] eraseWord

private theorem boundaryCleanupLaunch_bounded_exact
    (state : Nat) (parsedPrefix word : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (wordSafe : SafeSourceWord word)
    (launch :
      BoundaryCleanupLaunch state parsedPrefix word) :
    BoundedRejectingExecution
      (guardedConfig state parsedPrefix word)
      (16 * (parsedPrefix.length + word.length + 1)) := by
  rcases launch with
    ⟨launchSteps, consumedCells, storedCells,
      currentCell, restCells, storedSafe, launchBound,
      storedLength, wordShape, launchRun⟩
  rcases wordShape with explicitShape | implicitShape
  · let cleanupPrefix := parsedPrefix ++ storedCells
    have cleanupPrefixSafe :
        SafeSourceWord cleanupPrefix :=
      safe_append prefixSafe storedSafe
    have tailSafe :
        SafeSourceWord (currentCell :: restCells) := by
      intro symbol member
      apply wordSafe symbol
      rw [explicitShape]
      exact List.mem_append.mpr (Or.inr member)
    have cleanupWordSafe :
        SafeSourceWord
          (cleanupPrefix ++ currentCell :: restCells) :=
      safe_append cleanupPrefixSafe tailSafe
    have boundedRun :=
      safeExplicitFailure_bounded_exact
        (cleanupPrefix ++ currentCell :: restCells)
        cleanupPrefix currentCell restCells
        (guardedConfig state parsedPrefix word)
        launchSteps rfl cleanupWordSafe launchRun
    rcases boundedRun with
      ⟨steps, final, bounded, run, halted,
        finalState, outputEmpty⟩
    refine
      ⟨steps, final, Nat.le_trans bounded ?_,
        run, halted, finalState, outputEmpty⟩
    have explicitLength := congrArg List.length explicitShape
    simp only [List.length_append, List.length_cons] at explicitLength
    simp only [cleanupPrefix, List.length_append,
      List.length_cons]
    omega
  · rcases implicitShape with
      ⟨wordEq, currentEq, restEq⟩
    subst currentCell
    subst restCells
    let cleanupPrefix := parsedPrefix ++ storedCells
    have cleanupPrefixSafe :
        SafeSourceWord cleanupPrefix :=
      safe_append prefixSafe storedSafe
    have tail :=
      cleanupMissingSeek_bounded_exact
        cleanupPrefix cleanupPrefixSafe
    have joined :=
      BoundedRejectingExecution.prepend
        launchSteps
        (8 * (cleanupPrefix.length + 1))
        (guardedConfig state parsedPrefix word)
        (cleanupSeekConfiguration
          []
          (missingEndScan
            (pushCrossed cleanupPrefix []))
          [])
        (by simpa [cleanupPrefix, missingEndScan] using launchRun)
        tail
    rcases joined with
      ⟨steps, final, bounded, run, halted,
        finalState, outputEmpty⟩
    refine
      ⟨steps, final, Nat.le_trans bounded ?_,
        run, halted, finalState, outputEmpty⟩
    have wordLength := congrArg List.length wordEq
    simp only [cleanupPrefix, List.length_append]
    omega

private theorem simpleMalformedBoundary_bounded_exact
    (boundary : SimpleMalformedBoundary)
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (guardedConfig boundary.state
        parsedPrefix workTail)
      (16 * (parsedPrefix.length + workTail.length + 1)) := by
  exact
    boundaryCleanupLaunch_bounded_exact
      boundary.state parsedPrefix workTail
      prefixSafe (malformedWorkTail_safe malformed)
      (simpleMalformedBoundary_launch
        boundary parsedPrefix malformed)

private theorem gateParsingPrefix_failurePrefix_length
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) :
    (gateParsingPrefix inputs done
        (placeholderGates remaining)).length =
      (failureGatePrefix inputs done
        (remaining + 1)).length := by
  change
    (SourceParser.gateParsingPrefix inputs done
        (placeholderGates remaining)).length =
      (SourceParser.gatePrefix inputs done
        (placeholderGates (remaining + 1))).length
  simp [placeholderGates,
    SourceParser.gateParsingPrefix, SourceParser.gatePrefix,
    SourceParser.countCells_length,
    SourceParser.natCells_length,
    SourceParser.markedGateListCells_length,
    List.length_replicate]
  omega

private theorem gateFirstSteps_le_span
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (word : List WorkSymbol) :
    gateFirstSteps inputs done remaining ≤
      8 *
        ((failureGatePrefix inputs done
            (remaining + 1)).length +
          (firstSourceCell false :: word).length + 1) := by
  unfold gateFirstSteps
  simp only [List.length_cons]
  omega

private theorem gateLeftSteps_le_span
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (left : RawSource)
    (suffix : List WorkSymbol) :
    gateLeftSteps inputs done remaining left ≤
      8 *
        ((failureGatePrefix inputs done
            (remaining + 1)).length +
          (sourceCells left ++ suffix).length + 1) := by
  unfold gateLeftSteps gateFirstSteps
  have remainderLength :
      (sourceRemainderCells left).length + 1 =
        (sourceCells left).length := by
    rw [sourceCells_eq_first_remainder]
    simp
  simp only [List.length_append]
  omega

private theorem gateSourcesSteps_le_span
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (gate : RawGate)
    (suffix : List WorkSymbol) :
    gateSourcesSteps inputs done remaining gate ≤
      16 *
        ((failureGatePrefix inputs done
            (remaining + 1)).length +
          (sourceCells gate.left ++
            sourceCells gate.right ++ suffix).length + 1) := by
  unfold gateSourcesSteps
  have leftBound :=
    gateLeftSteps_le_span inputs done remaining
      gate.left (sourceCells gate.right ++ suffix)
  change
    gateLeftSteps inputs done remaining gate.left ≤
      8 *
        ((failureGatePrefix inputs done
            (remaining + 1)).length +
          (sourceCells gate.left ++
            (sourceCells gate.right ++ suffix)).length + 1)
      at leftBound
  simp only [List.length_append] at leftBound ⊢
  omega

private theorem gateRecordSteps_le_span
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (gate : RawGate)
    (suffix : List WorkSymbol) :
    gateRecordSteps inputs done remaining gate ≤
      32 *
        ((failureGatePrefix inputs done
            (remaining + 1)).length +
          (gateCells gate ++ suffix).length + 1) := by
  unfold gateRecordSteps
  have sourcesBound :=
    gateSourcesSteps_le_span inputs done remaining
      gate ([cell01, cell11] ++ suffix)
  change
    gateSourcesSteps inputs done remaining gate ≤
      16 *
        ((failureGatePrefix inputs done
            (remaining + 1)).length +
          (sourceCells gate.left ++
            sourceCells gate.right ++
              ([cell01, cell11] ++ suffix)).length + 1)
      at sourcesBound
  simp only [gateCells, sourceCells, SourceParser.gateCells,
    List.length_append, List.length_cons,
    List.length_nil] at sourcesBound ⊢
  omega

private theorem gateLeft_span_preserved
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (left : RawSource)
    (suffix : List WorkSymbol) :
    (gateParsingPrefix inputs done
          (placeholderGates remaining) ++
        sourceCells left).length +
        suffix.length =
      (failureGatePrefix inputs done
          (remaining + 1)).length +
        (sourceCells left ++ suffix).length := by
  rw [List.length_append, List.length_append,
    gateParsingPrefix_failurePrefix_length]
  omega

private theorem gateSources_span_preserved
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (gate : RawGate)
    (suffix : List WorkSymbol) :
    (gateParsingPrefix inputs done
            (placeholderGates remaining) ++
          sourceCells gate.left ++
        sourceCells gate.right).length +
        suffix.length =
      (failureGatePrefix inputs done
          (remaining + 1)).length +
        (sourceCells gate.left ++
          sourceCells gate.right ++ suffix).length := by
  rw [List.length_append, List.length_append,
    List.length_append, List.length_append,
    gateParsingPrefix_failurePrefix_length]
  omega

private theorem gateRecord_span_preserved
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat) (gate : RawGate)
    (suffix : List WorkSymbol) :
    (failureGatePrefix inputs (done ++ [gate])
        remaining).length + suffix.length =
      (failureGatePrefix inputs done
          (remaining + 1)).length +
        (gateCells gate ++ suffix).length := by
  have gateListAppend :
      (SourceParser.gateListCells (done ++ [gate])).length =
        (SourceParser.gateListCells done).length +
          (SourceParser.gateCells gate).length := by
    induction done with
    | nil =>
        simp [SourceParser.gateListCells]
    | cons head rest ih =>
        simp [SourceParser.gateListCells, ih,
          Nat.add_assoc]
  simp [failureGatePrefix, placeholderGates,
    gatePrefix, SourceParser.gatePrefix,
    SourceParser.countCells_length,
    SourceParser.natCells_length,
    SourceParser.markedGateListCells_length,
    gateCells, SourceParser.gateCells,
    gateListAppend]
  omega

private theorem programCountUnitCells_length_bounded
    (used : Nat) :
    (programCountUnitCells used).length = 2 * used := by
  induction used with
  | zero =>
      rfl
  | succ used ih =>
      simp only [programCountUnitCells,
        List.length_cons, ih]
      omega

private theorem programCountRemaining_bounded_exact
    (inputs : Nat) (done : List RawGate)
    (remaining : Nat)
    (tail : List WorkSymbol)
    (tailSafe : SafeSourceWord tail) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done (remaining + 1))
        (cell10 :: cell00 :: tail))
      (64 *
        ((failureGatePrefix inputs done
            (remaining + 1)).length +
          (cell10 :: cell00 :: tail).length + 1)) := by
  let logicalPrefix :=
    failureGatePrefix inputs done (remaining + 1)
  let initial :=
    guardedConfig State.gateStart logicalPrefix
      (cell10 :: cell00 :: tail)
  let afterCount :=
    markedGateListCells done ++
      cursorMark :: cell00 :: tail
  let afterHeader :=
    countCells done.length (remaining + 1) ++ afterCount
  let countPrefix :=
    [cell00, cell00] ++ natCells inputs ++
      programCountUnitCells done.length
  let failureRest :=
    natCells remaining ++ afterCount
  have launch :=
    programEndLaunch_exact logicalPrefix tail
  have cursorLeft :=
    programSeekGuardCursor_exact
      (logicalPrefix.reverse ++ [leftGuard])
      (cell00 :: tail)
  have backward :=
    programSeekGuard_scan_exact logicalPrefix
      (cursorMark :: cell00 :: tail)
      (by
        dsimp [logicalPrefix, failureGatePrefix]
        exact gatePrefix_ordinary inputs done
          (placeholderGates (remaining + 1)))
  have guard :=
    programSeekGuard_exact
      (logicalPrefix ++
        cursorMark :: cell00 :: tail)
  have version :=
    programSkipVersion_exact [leftGuard]
      (natCells inputs ++ afterHeader)
  have versionCanonical :
      workRunExact? machine 2
          (configAtWord State.programSkipVersionFirst
            [leftGuard]
            (logicalPrefix ++
              cursorMark :: cell00 :: tail)) =
        some
          (configAtWord State.programSkipInputFirst
            [cell00, cell00, leftGuard]
            (natCells inputs ++ afterHeader)) := by
    simpa [logicalPrefix, failureGatePrefix,
      placeholderGates, gatePrefix,
      SourceParser.gatePrefix, afterHeader,
      afterCount, natCells, countCells,
      markedGateListCells, cell00,
      SourceParser.cell00, List.append_assoc]
      using version
  have input :=
    programSkipInput_exact inputs
      [cell00, cell00, leftGuard] afterHeader
  have markers :=
    programCountMarkers_exact done.length
      (pushCrossed (natCells inputs)
        [cell00, cell00, leftGuard])
      (cell00 :: cell01 :: failureRest)
  have markersCanonical :
      workRunExact? machine (2 * done.length)
          (configAtWord State.programCountFirst
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])
            afterHeader) =
        some
          (configAtWord State.programCountFirst
            (pushCrossed (programCountUnitCells done.length)
              (pushCrossed (natCells inputs)
                [cell00, cell00, leftGuard]))
            (cell00 :: cell01 :: failureRest)) := by
    simpa [afterHeader, afterCount, failureRest,
      countCells_succ_remaining,
      List.append_assoc] using markers
  have leftEq :
      pushCrossed (programCountUnitCells done.length)
          (pushCrossed (natCells inputs)
            [cell00, cell00, leftGuard]) =
        pushCrossed countPrefix [leftGuard] := by
    repeat rw [pushCrossed_eq_reverse_append]
    simp [countPrefix, List.reverse_append,
      List.append_assoc]
  have failed :=
    programCountRemainingFailure_exact
      countPrefix failureRest
  have failedCanonical :
      workRunExact? machine 2
          (configAtWord State.programCountFirst
            (pushCrossed (programCountUnitCells done.length)
              (pushCrossed (natCells inputs)
                [cell00, cell00, leftGuard]))
            (cell00 :: cell01 :: failureRest)) =
        some
          (cleanupSeekConfiguration
            []
            (cell01 ::
              pushCrossed (countPrefix ++ [cell00]) [])
            failureRest) := by
    rw [leftEq]
    exact failed
  have throughCursorLeft :=
    exactRun_add 2 1 _ _ _ launch cursorLeft
  have throughBackward :=
    exactRun_add (2 + 1) logicalPrefix.length
      _ _ _ throughCursorLeft backward
  have throughGuard :=
    exactRun_add ((2 + 1) + logicalPrefix.length) 1
      _ _ _ throughBackward guard
  have throughVersion :=
    exactRun_add
      (((2 + 1) + logicalPrefix.length) + 1)
      2 _ _ _ throughGuard versionCanonical
  have throughInput :=
    exactRun_add
      ((((2 + 1) + logicalPrefix.length) + 1) + 2)
      (2 * (inputs + 1))
      _ _ _ throughVersion input
  have throughMarkers :=
    exactRun_add
      (((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1))
      (2 * done.length)
      _ _ _ throughInput markersCanonical
  have failedRun :=
    exactRun_add
      ((((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1)) + 2 * done.length)
      2 _ _ _ throughMarkers failedCanonical
  have countPrefixOrdinary :
      ∀ symbol, symbol ∈ countPrefix →
        ordinaryCell symbol := by
    dsimp [countPrefix]
    change
      ∀ symbol,
        symbol ∈
            (([cell00, cell00] ++ natCells inputs) ++
              programCountUnitCells done.length) →
          ordinaryCell symbol
    apply ordinary_append
    · apply ordinary_append
      · intro symbol member
        simp only [List.mem_cons,
          List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · exact cell00_ordinary
        · exact cell00_ordinary
        · contradiction
      · exact natCells_ordinary inputs
    · exact programCountUnitCells_ordinary done.length
  have parsedSafe :
      SafeSourceWord (countPrefix ++ [cell00]) :=
    safe_of_ordinary
      (ordinary_append countPrefixOrdinary
        (by
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell00_ordinary
          · contradiction))
  have afterCountSafe : SafeSourceWord afterCount := by
    have markedSafe :=
      safe_of_ordinary
        (markedGateListCells_ordinary done)
    have cursorAndSecondSafe :
        SafeSourceWord [cursorMark, cell00] := by
      intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | rfl | impossible
      · decide
      · decide
      · contradiction
    dsimp [afterCount]
    simpa [List.append_assoc] using
      safe_append
        (safe_append markedSafe cursorAndSecondSafe)
        tailSafe
  have failureRestSafe : SafeSourceWord failureRest := by
    dsimp [failureRest]
    exact safe_append
      (safe_of_ordinary
        (natCells_ordinary remaining))
      afterCountSafe
  have internalSafe :
      SafeSourceWord
        ((countPrefix ++ [cell00]) ++
          cell01 :: failureRest) := by
    apply safe_append parsedSafe
    change SafeSourceWord ([cell01] ++ failureRest)
    apply safe_append
    · intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | impossible
      · decide
      · contradiction
    · exact failureRestSafe
  let launchSteps :=
    (((((((2 + 1) + logicalPrefix.length) + 1) + 2) +
      2 * (inputs + 1)) + 2 * done.length) + 2)
  have boundedRun :=
    safeExplicitFailure_bounded_exact
      ((countPrefix ++ [cell00]) ++
        cell01 :: failureRest)
      (countPrefix ++ [cell00])
      cell01 failureRest initial launchSteps
      rfl internalSafe
      (by simpa [initial, launchSteps] using failedRun)
  rcases boundedRun with
    ⟨steps, final, bounded, run, halted,
      finalState, outputEmpty⟩
  refine
    ⟨steps, final, Nat.le_trans bounded ?_,
      (by simpa [initial, logicalPrefix] using run),
      halted, finalState, outputEmpty⟩
  have inputCells :
      (natCells inputs).length = 2 * (inputs + 1) := by
    exact SourceParser.natCells_length inputs
  have remainingCells :
      (natCells remaining).length = 2 * (remaining + 1) := by
    exact SourceParser.natCells_length remaining
  have unitCells :=
    programCountUnitCells_length_bounded done.length
  dsimp [launchSteps, countPrefix, failureRest,
    afterCount, logicalPrefix]
  simp only [List.length_append, List.length_cons,
    List.length_nil, inputCells, remainingCells,
    unitCells]
  unfold failureGatePrefix
  simp [placeholderGates, gatePrefix,
    SourceParser.gatePrefix,
    SourceParser.countCells_length,
    SourceParser.natCells_length,
    SourceParser.markedGateListCells_length]
  omega

private theorem gateLeftTokenFailure_bounded_exact
    (inputs : Nat) (done : List RawGate)
    {remaining : Nat} {tokens : List Token}
    (failure : SourceParser.SourceTokenFailure tokens) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done (remaining + 1))
        (SourceParser.packedTokenCells tokens))
      (128 *
        ((failureGatePrefix inputs done
            (remaining + 1)).length +
          (SourceParser.packedTokenCells tokens).length + 1)) := by
  let parsingPrefix :=
    gateParsingPrefix inputs done
      (placeholderGates remaining)
  have startPrefixSafe :
      SafeSourceWord
        (failureGatePrefix inputs done (remaining + 1)) := by
    apply safe_of_ordinary
    dsimp [failureGatePrefix]
    exact gatePrefix_ordinary inputs done
      (placeholderGates (remaining + 1))
  have parsingPrefixSafe :
      SafeSourceWord parsingPrefix := by
    exact safe_of_ordinary
      (gateParsingPrefix_ordinary inputs done
        (placeholderGates remaining))
  have firstPrefixSafe
      (first : WorkSymbol)
      (firstOrdinary : ordinaryCell first) :
      SafeSourceWord (parsingPrefix ++ [first]) := by
    apply safe_of_ordinary
    apply ordinary_append
      (gateParsingPrefix_ordinary inputs done
        (placeholderGates remaining))
    intro symbol member
    simp only [List.mem_cons,
      List.not_mem_nil] at member
    rcases member with rfl | impossible
    · exact firstOrdinary
    · contradiction
  cases failure with
  | missing =>
      have result :=
        missingExpected_bounded_exact State.gateStart
          (failureGatePrefix inputs done (remaining + 1))
          startPrefixSafe
          (gateStartMissingFailure_exact
            (failureGatePrefix inputs done (remaining + 1)))
      rcases result with
        ⟨steps, final, bounded, run, halted,
          finalState, outputEmpty⟩
      refine
        ⟨steps, final, Nat.le_trans bounded ?_,
          (by simpa [SourceParser.packedTokenCells] using run),
          halted, finalState, outputEmpty⟩
      simp [SourceParser.packedTokenCells]
      omega
  | wrongHead token suffix notInput notFalse notTrue notGate =>
      let suffixCells := SourceParser.packedTokenCells suffix
      let initial :=
        guardedConfig State.gateStart
          (failureGatePrefix inputs done (remaining + 1))
          (SourceParser.packedTokenCells (token :: suffix))
      have packedSafe :=
        packedTokenCells_safe (token :: suffix)
      have tailSafe
          (first current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [first, current]) :
          SafeSourceWord (current :: suffixCells) := by
        intro symbol member
        apply packedSafe symbol
        have targetMember :
            symbol ∈
              SourceParser.tokenCells token ++ suffixCells := by
          rw [cellsEq]
          simp only [List.mem_cons] at member
          rcases member with currentEq | member
          · subst symbol
            exact List.mem_append_left suffixCells
              (by simp)
          · exact List.mem_append_right
              [first, current] member
        simpa [SourceParser.packedTokenCells,
          suffixCells, List.append_assoc] using targetMember
      have widen
          (bound : Nat)
          (result : BoundedRejectingExecution initial bound)
          (linear :
            bound ≤
              128 *
                ((failureGatePrefix inputs done
                    (remaining + 1)).length +
                  (SourceParser.packedTokenCells
                    (token :: suffix)).length + 1)) :
          BoundedRejectingExecution initial
            (128 *
              ((failureGatePrefix inputs done
                  (remaining + 1)).length +
                (SourceParser.packedTokenCells
                  (token :: suffix)).length + 1)) := by
        rcases result with
          ⟨steps, final, bounded, run, halted,
            finalState, outputEmpty⟩
        exact
          ⟨steps, final, Nat.le_trans bounded linear,
            run, halted, finalState, outputEmpty⟩
      have after00
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell00, current])
          (not11 : current ≠ cell11) :
          BoundedRejectingExecution initial
            (128 *
              ((failureGatePrefix inputs done
                  (remaining + 1)).length +
                (SourceParser.packedTokenCells
                  (token :: suffix)).length + 1)) := by
        have firstRun :=
          gateFirst_exact false inputs done remaining
            current suffixCells
        have firstCanonical :
            workRunExact? machine
                (gateFirstSteps inputs done remaining)
                initial =
              some
                (guardedConfig
                  (State.sourceAfter00 .gateLeft)
                  (parsingPrefix ++ [cell00])
                  (current :: suffixCells)) := by
          simpa [initial, parsingPrefix,
            SourceParser.packedTokenCells, cellsEq,
            suffixCells, firstSourceCell,
            afterFirstSourceState] using firstRun
        have tail :=
          sourceAfter00_bounded_exact
            (parsingPrefix ++ [cell00])
            (firstPrefixSafe cell00 cell00_ordinary)
            current suffixCells
            (tailSafe cell00 current cellsEq) not11
        have joined :=
          BoundedRejectingExecution.prepend
            (gateFirstSteps inputs done remaining)
            (8 *
              ((parsingPrefix ++ [cell00]).length +
                (current :: suffixCells).length + 1))
            initial _ firstCanonical tail
        apply widen _ joined
        have firstBound :=
          gateFirstSteps_le_span
            inputs done remaining
            (current :: suffixCells)
        have prefixLength :=
          gateParsingPrefix_failurePrefix_length
            inputs done remaining
        have tokenLength :=
          SourceParser.tokenCells_length token
        simp only [parsingPrefix, List.length_append,
          List.length_cons, List.length_nil,
          SourceParser.packedTokenCells,
          List.length_append, tokenLength] at firstBound prefixLength ⊢
        dsimp [suffixCells] at firstBound ⊢
        omega
      have after01
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell01, current])
          (not00 : current ≠ cell00)
          (not01 : current ≠ cell01)
          (not10 : current ≠ cell10) :
          BoundedRejectingExecution initial
            (128 *
              ((failureGatePrefix inputs done
                  (remaining + 1)).length +
                (SourceParser.packedTokenCells
                  (token :: suffix)).length + 1)) := by
        have firstRun :=
          gateFirst_exact true inputs done remaining
            current suffixCells
        have firstCanonical :
            workRunExact? machine
                (gateFirstSteps inputs done remaining)
                initial =
              some
                (guardedConfig
                  (State.sourceAfter01 .gateLeft)
                  (parsingPrefix ++ [cell01])
                  (current :: suffixCells)) := by
          simpa [initial, parsingPrefix,
            SourceParser.packedTokenCells, cellsEq,
            suffixCells, firstSourceCell,
            afterFirstSourceState] using firstRun
        have tail :=
          sourceAfter01_bounded_exact
            (parsingPrefix ++ [cell01])
            (firstPrefixSafe cell01 cell01_ordinary)
            current suffixCells
            (tailSafe cell01 current cellsEq)
            not00 not01 not10
        have joined :=
          BoundedRejectingExecution.prepend
            (gateFirstSteps inputs done remaining)
            (8 *
              ((parsingPrefix ++ [cell01]).length +
                (current :: suffixCells).length + 1))
            initial _ firstCanonical tail
        apply widen _ joined
        have firstBound :=
          gateFirstSteps_le_span
            inputs done remaining
            (current :: suffixCells)
        have prefixLength :=
          gateParsingPrefix_failurePrefix_length
            inputs done remaining
        have tokenLength :=
          SourceParser.tokenCells_length token
        simp only [parsingPrefix, List.length_append,
          List.length_cons, List.length_nil,
          SourceParser.packedTokenCells,
          List.length_append, tokenLength] at firstBound prefixLength ⊢
        dsimp [suffixCells] at firstBound ⊢
        omega
      have badProgramSecond
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell10, current])
          (not00 : current ≠ cell00) :
          BoundedRejectingExecution initial
            (128 *
              ((failureGatePrefix inputs done
                  (remaining + 1)).length +
                (SourceParser.packedTokenCells
                  (token :: suffix)).length + 1)) := by
        have result :=
          programEndSecond_bounded_exact
            (failureGatePrefix inputs done (remaining + 1))
            startPrefixSafe current suffixCells
            (tailSafe cell10 current cellsEq) not00
        apply widen _ (by
          simpa [initial, SourceParser.packedTokenCells,
            cellsEq, suffixCells] using result)
        have tokenLength :=
          SourceParser.tokenCells_length token
        simp only [SourceParser.packedTokenCells,
          List.length_append, tokenLength]
        omega
      have prematureProgramEnd
          (cellsEq :
            SourceParser.tokenCells token = [cell10, cell00]) :
          BoundedRejectingExecution initial
            (128 *
              ((failureGatePrefix inputs done
                  (remaining + 1)).length +
                (SourceParser.packedTokenCells
                  (token :: suffix)).length + 1)) := by
        have result :=
          programCountRemaining_bounded_exact
            inputs done remaining suffixCells
            (packedTokenCells_safe suffix)
        apply widen _ (by
          simpa [initial, SourceParser.packedTokenCells,
            cellsEq, suffixCells] using result)
        have tokenLength :=
          SourceParser.tokenCells_length token
        simp only [SourceParser.packedTokenCells,
          List.length_append, tokenLength]
        omega
      cases token with
      | version0 =>
          exact after00 cell00 rfl (by decide)
      | unit =>
          exact after00 cell01 rfl (by decide)
      | natEnd =>
          exact after00 cell10 rfl (by decide)
      | input =>
          exact False.elim (notInput rfl)
      | constantFalse =>
          exact False.elim (notFalse rfl)
      | constantTrue =>
          exact False.elim (notTrue rfl)
      | gate =>
          exact False.elim (notGate rfl)
      | gateEnd =>
          exact after01 cell11 rfl
            (by decide) (by decide) (by decide)
      | programEnd =>
          exact prematureProgramEnd rfl
      | outputsEnd =>
          exact badProgramSecond cell01 rfl (by decide)
      | threshold =>
          exact badProgramSecond cell10 rfl (by decide)
      | instanceEnd =>
          exact badProgramSecond cell11 rfl (by decide)
  | @inputIndex indexTokens indexFailure =>
      let afterFirst := parsingPrefix ++ [cell00]
      let afterHead := afterFirst ++ [cell11]
      have firstRun :=
        gateFirst_exact false inputs done remaining
          cell11 (SourceParser.packedTokenCells indexTokens)
      have firstCanonical :
          workRunExact? machine
              (gateFirstSteps inputs done remaining)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done (remaining + 1))
                (SourceParser.packedTokenCells
                  (.input :: indexTokens))) =
            some
              (guardedConfig
                (State.sourceAfter00 .gateLeft)
                afterFirst
                (cell11 ::
                  SourceParser.packedTokenCells indexTokens)) := by
        simpa [afterFirst, parsingPrefix,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          firstSourceCell, afterFirstSourceState,
          cell00, cell11,
          SourceParser.cell00,
          SourceParser.cell11] using firstRun
      have headRun :=
        sourceAfter00NatLaunch_exact afterFirst
          (SourceParser.packedTokenCells indexTokens)
      have afterHeadSafe :
          SafeSourceWord afterHead := by
        apply safe_of_ordinary
        dsimp [afterHead, afterFirst, parsingPrefix]
        apply ordinary_append
        · apply ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates remaining))
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell00_ordinary
          · contradiction
        · intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell11_ordinary
          · contradiction
      have tail :=
        natTokenFailure_bounded_exact
          (.source .gateLeft) afterHead
          indexFailure afterHeadSafe
      have throughHead :=
        BoundedRejectingExecution.prepend
          1
          (8 *
            (afterHead.length +
              (SourceParser.packedTokenCells indexTokens).length + 1))
          _ _ (by
            simpa [afterHead, NatReader.state] using headRun)
          tail
      have joined :=
        BoundedRejectingExecution.prepend
          (gateFirstSteps inputs done remaining)
          (1 +
            8 *
              (afterHead.length +
                (SourceParser.packedTokenCells indexTokens).length + 1))
          _ _ firstCanonical throughHead
      rcases joined with
        ⟨steps, final, bounded, run, halted,
          finalState, outputEmpty⟩
      refine
        ⟨steps, final, Nat.le_trans bounded ?_,
          run, halted, finalState, outputEmpty⟩
      have firstBound :=
        gateFirstSteps_le_span inputs done remaining
          (cell11 :: SourceParser.packedTokenCells indexTokens)
      have prefixLength :=
        gateParsingPrefix_failurePrefix_length
          inputs done remaining
      simp only [afterHead, afterFirst, parsingPrefix,
        List.length_append, List.length_cons, List.length_nil,
        SourceParser.packedTokenCells,
        SourceParser.tokenCells_length] at firstBound prefixLength ⊢
      omega
  | @gateIndex indexTokens indexFailure =>
      let afterFirst := parsingPrefix ++ [cell01]
      let afterHead := afterFirst ++ [cell10]
      have firstRun :=
        gateFirst_exact true inputs done remaining
          cell10 (SourceParser.packedTokenCells indexTokens)
      have firstCanonical :
          workRunExact? machine
              (gateFirstSteps inputs done remaining)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done (remaining + 1))
                (SourceParser.packedTokenCells
                  (.gate :: indexTokens))) =
            some
              (guardedConfig
                (State.sourceAfter01 .gateLeft)
                afterFirst
                (cell10 ::
                  SourceParser.packedTokenCells indexTokens)) := by
        simpa [afterFirst, parsingPrefix,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          firstSourceCell, afterFirstSourceState,
          cell01, cell10,
          SourceParser.cell01,
          SourceParser.cell10] using firstRun
      have headRun :=
        sourceAfter01NatLaunch_exact afterFirst
          (SourceParser.packedTokenCells indexTokens)
      have afterHeadSafe :
          SafeSourceWord afterHead := by
        apply safe_of_ordinary
        dsimp [afterHead, afterFirst, parsingPrefix]
        apply ordinary_append
        · apply ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates remaining))
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell01_ordinary
          · contradiction
        · intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell10_ordinary
          · contradiction
      have tail :=
        natTokenFailure_bounded_exact
          (.source .gateLeft) afterHead
          indexFailure afterHeadSafe
      have throughHead :=
        BoundedRejectingExecution.prepend
          1
          (8 *
            (afterHead.length +
              (SourceParser.packedTokenCells indexTokens).length + 1))
          _ _ (by
            simpa [afterHead, NatReader.state] using headRun)
          tail
      have joined :=
        BoundedRejectingExecution.prepend
          (gateFirstSteps inputs done remaining)
          (1 +
            8 *
              (afterHead.length +
                (SourceParser.packedTokenCells indexTokens).length + 1))
          _ _ firstCanonical throughHead
      rcases joined with
        ⟨steps, final, bounded, run, halted,
          finalState, outputEmpty⟩
      refine
        ⟨steps, final, Nat.le_trans bounded ?_,
          run, halted, finalState, outputEmpty⟩
      have firstBound :=
        gateFirstSteps_le_span inputs done remaining
          (cell10 :: SourceParser.packedTokenCells indexTokens)
      have prefixLength :=
        gateParsingPrefix_failurePrefix_length
          inputs done remaining
      simp only [afterHead, afterFirst, parsingPrefix,
        List.length_append, List.length_cons, List.length_nil,
        SourceParser.packedTokenCells,
        SourceParser.tokenCells_length] at firstBound prefixLength ⊢
      omega

private theorem gateEndWrongToken_bounded_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token)
    (notGateEnd : token ≠ .gateEnd) :
    BoundedRejectingExecution
      (guardedConfig State.gateEndFirst parsedPrefix
        (SourceParser.packedTokenCells (token :: suffix)))
      (16 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells
            (token :: suffix)).length + 1)) := by
  let suffixCells := SourceParser.packedTokenCells suffix
  let initial :=
    guardedConfig State.gateEndFirst parsedPrefix
      (SourceParser.packedTokenCells (token :: suffix))
  have widen
      (launchSteps : Nat)
      (result :
        BoundedRejectingExecution initial
          (launchSteps +
            2 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells
                  (token :: suffix)).length + 1) +
            2))
      (launchBound : launchSteps ≤ 2) :
      BoundedRejectingExecution initial
        (16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1)) := by
    rcases result with
      ⟨steps, final, bounded, run, halted,
        finalState, outputEmpty⟩
    refine
      ⟨steps, final, Nat.le_trans bounded ?_,
        run, halted, finalState, outputEmpty⟩
    omega
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not01 : current ≠ cell01) :
      BoundedRejectingExecution initial
        (16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1)) := by
    have launch :=
      gateEndFirstFailure_exact parsedPrefix current
        (next :: suffixCells) not01
    have safe :=
      safe_append prefixSafe
        (packedTokenCells_safe (token :: suffix))
    have shape :
        parsedPrefix ++
            SourceParser.packedTokenCells (token :: suffix) =
          parsedPrefix ++ current :: next :: suffixCells := by
      simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    have boundedRun :=
      safeExplicitFailure_bounded_exact
        (parsedPrefix ++
          SourceParser.packedTokenCells (token :: suffix))
        parsedPrefix current (next :: suffixCells)
        initial 1 shape safe
        (by
          simpa [initial, SourceParser.packedTokenCells,
            cellsEq, suffixCells] using launch)
    apply widen 1
    · rcases boundedRun with
        ⟨steps, final, bounded, run, halted,
          finalState, outputEmpty⟩
      have linear :
          1 +
              2 *
                (parsedPrefix ++
                  SourceParser.packedTokenCells
                    (token :: suffix)).length +
              2 ≤
            1 +
              2 *
                (parsedPrefix.length +
                  (SourceParser.packedTokenCells
                    (token :: suffix)).length + 1) +
              2 := by
        simp only [List.length_append]
        omega
      exact
        ⟨steps, final, Nat.le_trans bounded linear,
          run, halted, finalState, outputEmpty⟩
    · omega
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell01, current])
      (not11 : current ≠ cell11) :
      BoundedRejectingExecution initial
        (16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1)) := by
    let parsedAfterMark := parsedPrefix ++ [gateMark]
    have launch :=
      gateEndSecondFailure_exact parsedPrefix current
        suffixCells not11
    have markerSafe : SafeSourceWord [gateMark] := by
      intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | impossible
      · decide
      · contradiction
    have tailSafe :
        SafeSourceWord (current :: suffixCells) := by
      have packedSafe :=
        packedTokenCells_safe (token :: suffix)
      intro symbol member
      apply packedSafe symbol
      change
        symbol ∈ SourceParser.tokenCells token ++ suffixCells
      rw [cellsEq]
      simp only [List.mem_cons] at member
      rcases member with currentEq | member
      · subst symbol
        exact List.mem_append_left suffixCells (by simp)
      · exact List.mem_append_right
          [cell01, current] member
    have internalSafe :
        SafeSourceWord
          (parsedAfterMark ++ current :: suffixCells) :=
      safe_append
        (safe_append prefixSafe markerSafe) tailSafe
    have boundedRun :=
      safeExplicitFailure_bounded_exact
        (parsedAfterMark ++ current :: suffixCells)
        parsedAfterMark current suffixCells initial 2
        rfl internalSafe
        (by
          simpa [initial, parsedAfterMark,
            SourceParser.packedTokenCells, cellsEq,
            suffixCells] using launch)
    have tokenLength :=
      SourceParser.tokenCells_length token
    apply widen 2
    · rcases boundedRun with
        ⟨steps, final, bounded, run, halted,
          finalState, outputEmpty⟩
      have linear :
          2 +
              2 *
                (parsedAfterMark ++
                  current :: suffixCells).length +
              2 ≤
            2 +
              2 *
                (parsedPrefix.length +
                  (SourceParser.packedTokenCells
                    (token :: suffix)).length + 1) +
              2 := by
        simp only [parsedAfterMark, suffixCells,
          List.length_append, List.length_cons,
          List.length_nil,
          SourceParser.packedTokenCells,
          tokenLength]
        omega
      exact
        ⟨steps, final, Nat.le_trans bounded linear,
          run, halted, finalState, outputEmpty⟩
    · omega
  cases token with
  | version0 =>
      exact rejectFirst cell00 cell00 rfl (by decide)
  | unit =>
      exact rejectFirst cell00 cell01 rfl (by decide)
  | natEnd =>
      exact rejectFirst cell00 cell10 rfl (by decide)
  | input =>
      exact rejectFirst cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact rejectSecond cell00 rfl (by decide)
  | constantTrue =>
      exact rejectSecond cell01 rfl (by decide)
  | gate =>
      exact rejectSecond cell10 rfl (by decide)
  | gateEnd =>
      exact False.elim (notGateEnd rfl)
  | programEnd =>
      exact rejectFirst cell10 cell00 rfl (by decide)
  | outputsEnd =>
      exact rejectFirst cell10 cell01 rfl (by decide)
  | threshold =>
      exact rejectFirst cell10 cell10 rfl (by decide)
  | instanceEnd =>
      exact rejectFirst cell10 cell11 rfl (by decide)

private theorem versionWrongToken_bounded_exact
    (token : Token) (suffix : List Token)
    (notVersion : token ≠ .version0) :
    BoundedRejectingExecution
      (guardedConfig State.versionFirst []
        (SourceParser.packedTokenCells (token :: suffix)))
      (16 *
        ((SourceParser.packedTokenCells
          (token :: suffix)).length + 1)) := by
  let suffixCells := SourceParser.packedTokenCells suffix
  have emptySafe : SafeSourceWord [] := by
    intro symbol member
    contradiction
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not00 : current ≠ cell00) :
      BoundedRejectingExecution
        (guardedConfig State.versionFirst []
          (SourceParser.packedTokenCells (token :: suffix)))
        (16 *
          ((SourceParser.packedTokenCells
            (token :: suffix)).length + 1)) := by
    have launch :
        BoundaryCleanupLaunch State.versionFirst []
          (current :: next :: suffixCells) :=
      boundaryCleanupLaunch_immediate
        State.versionFirst [] current
          (next :: suffixCells)
        (versionFirstFailure_exact current
          (next :: suffixCells) not00)
    have wordSafe :
        SafeSourceWord (current :: next :: suffixCells) := by
      simpa [SourceParser.packedTokenCells,
        cellsEq, suffixCells] using
          packedTokenCells_safe (token :: suffix)
    simpa [SourceParser.packedTokenCells,
      cellsEq, suffixCells] using
      boundaryCleanupLaunch_bounded_exact
        State.versionFirst [] (current :: next :: suffixCells)
        emptySafe wordSafe launch
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell00, current])
      (not00 : current ≠ cell00) :
      BoundedRejectingExecution
        (guardedConfig State.versionFirst []
          (SourceParser.packedTokenCells (token :: suffix)))
        (16 *
          ((SourceParser.packedTokenCells
            (token :: suffix)).length + 1)) := by
    have firstSafe : SafeSourceWord [cell00] := by
      intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | impossible
      · decide
      · contradiction
    have launch :
        BoundaryCleanupLaunch State.versionFirst []
          (cell00 :: current :: suffixCells) :=
      boundaryCleanupLaunch_afterOne_retained
        State.versionFirst [] cell00 current suffixCells
        firstSafe
        (versionSecondFromFirstFailure_exact
          current suffixCells not00)
    have wordSafe :
        SafeSourceWord (cell00 :: current :: suffixCells) := by
      simpa [SourceParser.packedTokenCells,
        cellsEq, suffixCells] using
          packedTokenCells_safe (token :: suffix)
    simpa [SourceParser.packedTokenCells,
      cellsEq, suffixCells] using
      boundaryCleanupLaunch_bounded_exact
        State.versionFirst []
        (cell00 :: current :: suffixCells)
        emptySafe wordSafe launch
  cases token with
  | version0 =>
      exact False.elim (notVersion rfl)
  | unit =>
      exact rejectSecond cell01 rfl (by decide)
  | natEnd =>
      exact rejectSecond cell10 rfl (by decide)
  | input =>
      exact rejectSecond cell11 rfl (by decide)
  | constantFalse =>
      exact rejectFirst cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact rejectFirst cell01 cell01 rfl (by decide)
  | gate =>
      exact rejectFirst cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact rejectFirst cell01 cell11 rfl (by decide)
  | programEnd =>
      exact rejectFirst cell10 cell00 rfl (by decide)
  | outputsEnd =>
      exact rejectFirst cell10 cell01 rfl (by decide)
  | threshold =>
      exact rejectFirst cell10 cell10 rfl (by decide)
  | instanceEnd =>
      exact rejectFirst cell10 cell11 rfl (by decide)

private theorem outputsEndWrongToken_bounded_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token)
    (notOutputsEnd : token ≠ .outputsEnd) :
    BoundedRejectingExecution
      (guardedConfig State.outputsEndFirst parsedPrefix
        (SourceParser.packedTokenCells (token :: suffix)))
      (16 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells
            (token :: suffix)).length + 1)) := by
  let suffixCells := SourceParser.packedTokenCells suffix
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not10 : current ≠ cell10) :
      BoundedRejectingExecution
        (guardedConfig State.outputsEndFirst parsedPrefix
          (SourceParser.packedTokenCells (token :: suffix)))
        (16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1)) := by
    have launch :
        BoundaryCleanupLaunch State.outputsEndFirst parsedPrefix
          (current :: next :: suffixCells) :=
      boundaryCleanupLaunch_immediate
        State.outputsEndFirst parsedPrefix current
          (next :: suffixCells)
        (outputsEndFirstFailure_exact parsedPrefix current
          (next :: suffixCells) not10)
    have wordSafe :
        SafeSourceWord (current :: next :: suffixCells) := by
      simpa [SourceParser.packedTokenCells,
        cellsEq, suffixCells] using
          packedTokenCells_safe (token :: suffix)
    simpa [SourceParser.packedTokenCells,
      cellsEq, suffixCells] using
      boundaryCleanupLaunch_bounded_exact
        State.outputsEndFirst parsedPrefix
        (current :: next :: suffixCells)
        prefixSafe wordSafe launch
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell10, current])
      (not01 : current ≠ cell01) :
      BoundedRejectingExecution
        (guardedConfig State.outputsEndFirst parsedPrefix
          (SourceParser.packedTokenCells (token :: suffix)))
        (16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1)) := by
    have firstSafe : SafeSourceWord [cell10] := by
      intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | impossible
      · decide
      · contradiction
    have launch :
        BoundaryCleanupLaunch State.outputsEndFirst parsedPrefix
          (cell10 :: current :: suffixCells) :=
      boundaryCleanupLaunch_afterOne_retained
        State.outputsEndFirst parsedPrefix
        cell10 current suffixCells firstSafe
        (outputsEndSecondFailure_exact parsedPrefix
          current suffixCells not01)
    have wordSafe :
        SafeSourceWord (cell10 :: current :: suffixCells) := by
      simpa [SourceParser.packedTokenCells,
        cellsEq, suffixCells] using
          packedTokenCells_safe (token :: suffix)
    simpa [SourceParser.packedTokenCells,
      cellsEq, suffixCells] using
      boundaryCleanupLaunch_bounded_exact
        State.outputsEndFirst parsedPrefix
        (cell10 :: current :: suffixCells)
        prefixSafe wordSafe launch
  cases token with
  | version0 =>
      exact rejectFirst cell00 cell00 rfl (by decide)
  | unit =>
      exact rejectFirst cell00 cell01 rfl (by decide)
  | natEnd =>
      exact rejectFirst cell00 cell10 rfl (by decide)
  | input =>
      exact rejectFirst cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact rejectFirst cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact rejectFirst cell01 cell01 rfl (by decide)
  | gate =>
      exact rejectFirst cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact rejectFirst cell01 cell11 rfl (by decide)
  | programEnd =>
      exact rejectSecond cell00 rfl (by decide)
  | outputsEnd =>
      exact False.elim (notOutputsEnd rfl)
  | threshold =>
      exact rejectSecond cell10 rfl (by decide)
  | instanceEnd =>
      exact rejectSecond cell11 rfl (by decide)

private theorem instanceEndWrongToken_bounded_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token)
    (notInstanceEnd : token ≠ .instanceEnd) :
    BoundedRejectingExecution
      (guardedConfig State.instanceEndFirst parsedPrefix
        (SourceParser.packedTokenCells (token :: suffix)))
      (16 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells
            (token :: suffix)).length + 1)) := by
  let suffixCells := SourceParser.packedTokenCells suffix
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not10 : current ≠ cell10) :
      BoundedRejectingExecution
        (guardedConfig State.instanceEndFirst parsedPrefix
          (SourceParser.packedTokenCells (token :: suffix)))
        (16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1)) := by
    have launch :
        BoundaryCleanupLaunch State.instanceEndFirst parsedPrefix
          (current :: next :: suffixCells) :=
      boundaryCleanupLaunch_immediate
        State.instanceEndFirst parsedPrefix current
          (next :: suffixCells)
        (instanceEndFirstFailure_exact parsedPrefix current
          (next :: suffixCells) not10)
    have wordSafe :
        SafeSourceWord (current :: next :: suffixCells) := by
      simpa [SourceParser.packedTokenCells,
        cellsEq, suffixCells] using
          packedTokenCells_safe (token :: suffix)
    simpa [SourceParser.packedTokenCells,
      cellsEq, suffixCells] using
      boundaryCleanupLaunch_bounded_exact
        State.instanceEndFirst parsedPrefix
        (current :: next :: suffixCells)
        prefixSafe wordSafe launch
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell10, current])
      (not11 : current ≠ cell11) :
      BoundedRejectingExecution
        (guardedConfig State.instanceEndFirst parsedPrefix
          (SourceParser.packedTokenCells (token :: suffix)))
        (16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1)) := by
    have firstSafe : SafeSourceWord [cell10] := by
      intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | impossible
      · decide
      · contradiction
    have launch :
        BoundaryCleanupLaunch State.instanceEndFirst parsedPrefix
          (cell10 :: current :: suffixCells) :=
      boundaryCleanupLaunch_afterOne_retained
        State.instanceEndFirst parsedPrefix
        cell10 current suffixCells firstSafe
        (instanceEndSecondFailure_exact parsedPrefix
          current suffixCells not11)
    have wordSafe :
        SafeSourceWord (cell10 :: current :: suffixCells) := by
      simpa [SourceParser.packedTokenCells,
        cellsEq, suffixCells] using
          packedTokenCells_safe (token :: suffix)
    simpa [SourceParser.packedTokenCells,
      cellsEq, suffixCells] using
      boundaryCleanupLaunch_bounded_exact
        State.instanceEndFirst parsedPrefix
        (cell10 :: current :: suffixCells)
        prefixSafe wordSafe launch
  cases token with
  | version0 =>
      exact rejectFirst cell00 cell00 rfl (by decide)
  | unit =>
      exact rejectFirst cell00 cell01 rfl (by decide)
  | natEnd =>
      exact rejectFirst cell00 cell10 rfl (by decide)
  | input =>
      exact rejectFirst cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact rejectFirst cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact rejectFirst cell01 cell01 rfl (by decide)
  | gate =>
      exact rejectFirst cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact rejectFirst cell01 cell11 rfl (by decide)
  | programEnd =>
      exact rejectSecond cell00 rfl (by decide)
  | outputsEnd =>
      exact rejectSecond cell01 rfl (by decide)
  | threshold =>
      exact rejectSecond cell10 rfl (by decide)
  | instanceEnd =>
      exact False.elim (notInstanceEnd rfl)

private theorem finalEOFToken_bounded_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token) :
    BoundedRejectingExecution
      (guardedConfig State.finalEOF parsedPrefix
        (SourceParser.packedTokenCells (token :: suffix)))
      (16 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells
            (token :: suffix)).length + 1)) := by
  let suffixCells := SourceParser.packedTokenCells suffix
  have reject
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (notBlank : current ≠ cellBlank) :
      BoundedRejectingExecution
        (guardedConfig State.finalEOF parsedPrefix
          (SourceParser.packedTokenCells (token :: suffix)))
        (16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1)) := by
    have launch :
        BoundaryCleanupLaunch State.finalEOF parsedPrefix
          (current :: next :: suffixCells) :=
      boundaryCleanupLaunch_immediate
        State.finalEOF parsedPrefix current
          (next :: suffixCells)
        (finalEOFFailure_exact parsedPrefix current
          (next :: suffixCells) notBlank)
    have wordSafe :
        SafeSourceWord (current :: next :: suffixCells) := by
      simpa [SourceParser.packedTokenCells,
        cellsEq, suffixCells] using
          packedTokenCells_safe (token :: suffix)
    simpa [SourceParser.packedTokenCells,
      cellsEq, suffixCells] using
      boundaryCleanupLaunch_bounded_exact
        State.finalEOF parsedPrefix
        (current :: next :: suffixCells)
        prefixSafe wordSafe launch
  cases token with
  | version0 =>
      exact reject cell00 cell00 rfl (by decide)
  | unit =>
      exact reject cell00 cell01 rfl (by decide)
  | natEnd =>
      exact reject cell00 cell10 rfl (by decide)
  | input =>
      exact reject cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact reject cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact reject cell01 cell01 rfl (by decide)
  | gate =>
      exact reject cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact reject cell01 cell11 rfl (by decide)
  | programEnd =>
      exact reject cell10 cell00 rfl (by decide)
  | outputsEnd =>
      exact reject cell10 cell01 rfl (by decide)
  | threshold =>
      exact reject cell10 cell10 rfl (by decide)
  | instanceEnd =>
      exact reject cell10 cell11 rfl (by decide)

private theorem gateDecrementExhaustedForwardWord_bounded_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate)
    (word : List WorkSymbol)
    (wordSafe : SafeSourceWord word) :
    BoundedRejectingExecution
      (configAtWord
        (State.gateDecrementVersionFirst firstWas01)
        [leftGuard]
        (gatePrefix inputs done [] ++
          cursorMark :: word))
      (128 *
        ((gatePrefix inputs done []).length +
          word.length + 1)) := by
  let initial :=
    configAtWord
      (State.gateDecrementVersionFirst firstWas01)
      [leftGuard]
      (gatePrefix inputs done [] ++
        cursorMark :: word)
  let afterHeader :=
    countCells done.length 0 ++
      markedGateListCells done ++
        cursorMark :: word
  let countPrefix :=
    [cell00, cell00] ++ natCells inputs ++
      borrowedCountCells done.length
  let failureRest :=
    markedGateListCells done ++
      cursorMark :: word
  have version :=
    gateDecrementVersion_exact firstWas01 [leftGuard]
      (natCells inputs ++ afterHeader)
  have versionCanonical :
      workRunExact? machine 2 initial =
        some
          (configAtWord
            (State.gateDecrementInputFirst firstWas01)
            [cell00, cell00, leftGuard]
            (natCells inputs ++ afterHeader)) := by
    simpa [initial, afterHeader, gatePrefix,
      SourceParser.gatePrefix, natCells, countCells,
      markedGateListCells, cell00,
      SourceParser.cell00, List.append_assoc] using version
  have input :=
    gateDecrementInput_exact firstWas01 inputs
      [cell00, cell00, leftGuard] afterHeader
  have borrowed :=
    gateDecrementBorrowed_exact firstWas01 done.length
      (pushCrossed (natCells inputs)
        [cell00, cell00, leftGuard])
      (cell00 :: cell10 :: failureRest)
  have borrowedCanonical :
      workRunExact? machine (2 * done.length)
          (configAtWord
            (State.gateDecrementCountFirst firstWas01)
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])
            afterHeader) =
        some
          (configAtWord
            (State.gateDecrementCountFirst firstWas01)
            (pushCrossed (borrowedCountCells done.length)
              (pushCrossed (natCells inputs)
                [cell00, cell00, leftGuard]))
            (cell00 :: cell10 :: failureRest)) := by
    simpa [afterHeader, failureRest,
      countCells_eq_borrowed_append,
      natCells, SourceParser.natCells,
      cell00, cell10, SourceParser.cell00,
      SourceParser.cell10, List.append_assoc] using borrowed
  have leftEq :
      pushCrossed (borrowedCountCells done.length)
          (pushCrossed (natCells inputs)
            [cell00, cell00, leftGuard]) =
        pushCrossed countPrefix [leftGuard] := by
    repeat rw [pushCrossed_eq_reverse_append]
    simp [countPrefix, List.reverse_append,
      List.append_assoc]
  have failed :=
    gateDecrementCountEndFailure_exact firstWas01
      countPrefix failureRest
  have failedCanonical :
      workRunExact? machine 2
          (configAtWord
            (State.gateDecrementCountFirst firstWas01)
            (pushCrossed (borrowedCountCells done.length)
              (pushCrossed (natCells inputs)
                [cell00, cell00, leftGuard]))
            (cell00 :: cell10 :: failureRest)) =
        some
          (cleanupSeekConfiguration
            []
            (cell10 ::
              pushCrossed (countPrefix ++ [cell00]) [])
            failureRest) := by
    rw [leftEq]
    exact failed
  have throughInput :=
    exactRun_add 2 (2 * (inputs + 1))
      _ _ _ versionCanonical input
  have throughBorrowed :=
    exactRun_add (2 + 2 * (inputs + 1))
      (2 * done.length) _ _ _
      throughInput borrowedCanonical
  have launch :=
    exactRun_add
      ((2 + 2 * (inputs + 1)) +
        2 * done.length)
      2 _ _ _ throughBorrowed failedCanonical
  have countPrefixOrdinary :
      ∀ symbol, symbol ∈ countPrefix →
        ordinaryCell symbol := by
    dsimp [countPrefix]
    change
      ∀ symbol,
        symbol ∈
            (([cell00, cell00] ++ natCells inputs) ++
              borrowedCountCells done.length) →
          ordinaryCell symbol
    apply ordinary_append
    · apply ordinary_append
      · intro symbol member
        simp only [List.mem_cons,
          List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · exact cell00_ordinary
        · exact cell00_ordinary
        · contradiction
      · exact natCells_ordinary inputs
    · exact borrowedCountCells_ordinary done.length
  have parsedSafe :
      SafeSourceWord (countPrefix ++ [cell00]) :=
    safe_of_ordinary
      (ordinary_append countPrefixOrdinary
        (by
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell00_ordinary
          · contradiction))
  have markedAndCursorSafe :
      SafeSourceWord
        (markedGateListCells done ++ [cursorMark]) := by
    apply safe_append
    · exact safe_of_ordinary
        (markedGateListCells_ordinary done)
    · intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | impossible
      · decide
      · contradiction
  have restSafe : SafeSourceWord failureRest := by
    dsimp [failureRest]
    simpa [List.append_assoc] using
      safe_append markedAndCursorSafe wordSafe
  have internalSafe :
      SafeSourceWord
        ((countPrefix ++ [cell00]) ++
          cell10 :: failureRest) := by
    apply safe_append parsedSafe
    change SafeSourceWord ([cell10] ++ failureRest)
    apply safe_append
    · intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | impossible
      · decide
      · contradiction
    · exact restSafe
  let launchSteps :=
    (((2 + 2 * (inputs + 1)) +
      2 * done.length) + 2)
  have boundedRun :=
    safeExplicitFailure_bounded_exact
      ((countPrefix ++ [cell00]) ++
        cell10 :: failureRest)
      (countPrefix ++ [cell00])
      cell10 failureRest initial launchSteps
      rfl internalSafe
      (by simpa [launchSteps] using launch)
  rcases boundedRun with
    ⟨steps, final, bounded, run, halted,
      finalState, outputEmpty⟩
  refine
    ⟨steps, final, Nat.le_trans bounded ?_,
      (by simpa [initial] using run),
      halted, finalState, outputEmpty⟩
  have inputCells :
      (natCells inputs).length = 2 * (inputs + 1) :=
    SourceParser.natCells_length inputs
  have borrowedCells :
      (borrowedCountCells done.length).length =
        2 * done.length :=
    SourceParser.borrowedCountCells_length done.length
  dsimp [launchSteps, countPrefix, failureRest]
  simp only [List.length_append, List.length_cons,
    List.length_nil, inputCells, borrowedCells]
  unfold gatePrefix
  simp [SourceParser.gatePrefix,
    SourceParser.countCells_length,
    SourceParser.natCells_length,
    SourceParser.markedGateListCells_length]
  omega

private theorem gateDecrementExhausted_bounded_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (tailSafe : SafeSourceWord (current :: rest)) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart
        (gatePrefix inputs done [])
        (firstSourceCell firstWas01 :: current :: rest))
      (256 *
        ((gatePrefix inputs done []).length +
          (firstSourceCell firstWas01 ::
            current :: rest).length + 1)) := by
  let logicalPrefix := gatePrefix inputs done []
  have launch :=
    gateStartLaunchWord_exact firstWas01 logicalPrefix
      (current :: rest)
  have backward :=
    gateDecrementSeekGuard_scan_exact firstWas01 logicalPrefix
      (cursorMark :: current :: rest)
      (gatePrefix_ordinary inputs done [])
  have guard :=
    gateDecrementGuard_exact firstWas01
      (logicalPrefix ++ cursorMark :: current :: rest)
  have throughBackward :=
    exactRun_add 1 logicalPrefix.length
      _ _ _ launch backward
  have throughGuard :=
    exactRun_add (1 + logicalPrefix.length) 1
      _ _ _ throughBackward guard
  have tail :=
    gateDecrementExhaustedForwardWord_bounded_exact
      firstWas01 inputs done (current :: rest) tailSafe
  have joined :=
    BoundedRejectingExecution.prepend
      ((1 + logicalPrefix.length) + 1)
      (128 *
        ((gatePrefix inputs done []).length +
          (current :: rest).length + 1))
      _ _
      (by simpa [logicalPrefix] using throughGuard)
      tail
  rcases joined with
    ⟨steps, final, bounded, run, halted,
      finalState, outputEmpty⟩
  refine
    ⟨steps, final, Nat.le_trans bounded ?_,
      run, halted, finalState, outputEmpty⟩
  dsimp [logicalPrefix]
  omega

private theorem wrongProgramEndToken_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (token : Token) (suffix : List Token)
    (notProgramEnd : token ≠ .programEnd) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart
        (gatePrefix inputs gates [])
        (SourceParser.packedTokenCells
          (token :: suffix)))
      (256 *
        ((gatePrefix inputs gates []).length +
          (SourceParser.packedTokenCells
            (token :: suffix)).length + 1)) := by
  let suffixCells := SourceParser.packedTokenCells suffix
  have prefixSafe :
      SafeSourceWord (gatePrefix inputs gates []) :=
    safe_of_ordinary
      (gatePrefix_ordinary inputs gates [])
  have packedSafe :=
    packedTokenCells_safe (token :: suffix)
  have tailSafe
      (first current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [first, current]) :
      SafeSourceWord (current :: suffixCells) := by
    intro symbol member
    apply packedSafe symbol
    change
      symbol ∈
        SourceParser.tokenCells token ++ suffixCells
    rw [cellsEq]
    simp only [List.mem_cons] at member
    rcases member with currentEq | member
    · subst symbol
      exact List.mem_append_left suffixCells (by simp)
    · exact List.mem_append_right [first, current] member
  have exhausted
      (firstWas01 : Bool)
      (first current : WorkSymbol)
      (firstEq : firstSourceCell firstWas01 = first)
      (cellsEq :
        SourceParser.tokenCells token = [first, current]) :
      BoundedRejectingExecution
        (guardedConfig State.gateStart
          (gatePrefix inputs gates [])
          (SourceParser.packedTokenCells
            (token :: suffix)))
        (256 *
          ((gatePrefix inputs gates []).length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1)) := by
    have boundedRun :=
      gateDecrementExhausted_bounded_exact
        firstWas01 inputs gates current suffixCells
        (tailSafe first current cellsEq)
    simpa [SourceParser.packedTokenCells,
      cellsEq, suffixCells, firstEq] using boundedRun
  have badSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell10, current])
      (not00 : current ≠ cell00) :
      BoundedRejectingExecution
        (guardedConfig State.gateStart
          (gatePrefix inputs gates [])
          (SourceParser.packedTokenCells
            (token :: suffix)))
        (256 *
          ((gatePrefix inputs gates []).length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1)) := by
    have boundedRun :=
      programEndSecond_bounded_exact
        (gatePrefix inputs gates []) prefixSafe
        current suffixCells
        (tailSafe cell10 current cellsEq) not00
    rcases boundedRun with
      ⟨steps, final, bounded, run, halted,
        finalState, outputEmpty⟩
    have tokenLength :=
      SourceParser.tokenCells_length token
    have linear :
        8 *
            ((gatePrefix inputs gates []).length +
              (cell10 :: current :: suffixCells).length + 1) ≤
          256 *
            ((gatePrefix inputs gates []).length +
              (SourceParser.packedTokenCells
                (token :: suffix)).length + 1) := by
      dsimp [suffixCells]
      simp only [SourceParser.packedTokenCells,
        List.length_append, tokenLength]
      omega
    exact
      ⟨steps, final, Nat.le_trans bounded linear,
        (by
          simpa [SourceParser.packedTokenCells,
            cellsEq, suffixCells] using run),
        halted, finalState, outputEmpty⟩
  cases token with
  | version0 =>
      exact exhausted false cell00 cell00 rfl rfl
  | unit =>
      exact exhausted false cell00 cell01 rfl rfl
  | natEnd =>
      exact exhausted false cell00 cell10 rfl rfl
  | input =>
      exact exhausted false cell00 cell11 rfl rfl
  | constantFalse =>
      exact exhausted true cell01 cell00 rfl rfl
  | constantTrue =>
      exact exhausted true cell01 cell01 rfl rfl
  | gate =>
      exact exhausted true cell01 cell10 rfl rfl
  | gateEnd =>
      exact exhausted true cell01 cell11 rfl rfl
  | programEnd =>
      exact False.elim (notProgramEnd rfl)
  | outputsEnd =>
      exact badSecond cell01 rfl (by decide)
  | threshold =>
      exact badSecond cell10 rfl (by decide)
  | instanceEnd =>
      exact badSecond cell11 rfl (by decide)

private theorem nGatesTokenFailure_bounded_exact
    (inputs : Nat) (done : List RawGate)
    {count : Nat} {tokens : List Token}
    (failure :
      SourceParser.NGatesTokenFailure count tokens) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done count)
        (SourceParser.packedTokenCells tokens))
      (512 * (count + 1) *
        ((failureGatePrefix inputs done count).length +
          (SourceParser.packedTokenCells tokens).length + 1)) := by
  induction failure generalizing done with
  | @left count failedTokens failure =>
      have boundedRun :=
        gateLeftTokenFailure_bounded_exact
          inputs done (remaining := count) failure
      rcases boundedRun with
        ⟨steps, final, bounded, run, halted,
          finalState, outputEmpty⟩
      refine
        ⟨steps, final, Nat.le_trans bounded ?_,
          run, halted, finalState, outputEmpty⟩
      exact Nat.mul_le_mul_right _
        (by omega :
          128 ≤ 512 * ((count + 1) + 1))
  | @right count left failedTokens failure =>
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates count) ++
          sourceCells left
      have leftRun :=
        gateLeft_exact inputs done count left
          (SourceParser.packedTokenCells failedTokens)
      have leftCanonical :
          workRunExact? machine
              (gateLeftSteps inputs done count left)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (count + 1))
                (SourceParser.packedTokenCells
                  (encodeSourceTokens left ++
                    failedTokens))) =
            some
              (guardedConfig
                (State.sourceStart .gateRight)
                parsedPrefix
                (SourceParser.packedTokenCells
                  failedTokens)) := by
        rw [packedTokenCells_append,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [parsedPrefix] using leftRun
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        apply safe_of_ordinary
        dsimp [parsedPrefix]
        exact ordinary_append
          (gateParsingPrefix_ordinary inputs done
            (placeholderGates count))
          (sourceCells_ordinary left)
      have tail :=
        sourceTokenFailure_bounded_exact .gateRight
          parsedPrefix failure parsedSafe
      have joined :=
        BoundedRejectingExecution.prepend
          (gateLeftSteps inputs done count left)
          (16 *
            (parsedPrefix.length +
              (SourceParser.packedTokenCells
                failedTokens).length + 1))
          _ _ leftCanonical tail
      let span :=
        (failureGatePrefix inputs done
            (count + 1)).length +
          (SourceParser.packedTokenCells
            (encodeSourceTokens left ++ failedTokens)).length + 1
      have packedShape :
          (SourceParser.packedTokenCells
              (encodeSourceTokens left ++ failedTokens)).length =
            (sourceCells left ++
              SourceParser.packedTokenCells
                failedTokens).length := by
        rw [packedTokenCells_append,
          SourceParser.packedTokenCells_encodeSourceTokens]
      have stepLinear :
          gateLeftSteps inputs done count left ≤
            8 * span := by
        calc
          gateLeftSteps inputs done count left ≤
              8 *
                ((failureGatePrefix inputs done
                    (count + 1)).length +
                  (sourceCells left ++
                    SourceParser.packedTokenCells
                      failedTokens).length + 1) :=
            gateLeftSteps_le_span inputs done count left
              (SourceParser.packedTokenCells failedTokens)
          _ = 8 * span := by
            dsimp [span]
            rw [packedShape]
      have tailSpan :
          parsedPrefix.length +
                (SourceParser.packedTokenCells
                  failedTokens).length + 1 =
            span := by
        have preserved :=
          gateLeft_span_preserved inputs done count left
            (SourceParser.packedTokenCells failedTokens)
        dsimp [parsedPrefix, span]
        rw [packedShape]
        omega
      have combined :
          gateLeftSteps inputs done count left +
              16 *
                (parsedPrefix.length +
                  (SourceParser.packedTokenCells
                    failedTokens).length + 1) ≤
            24 * span := by
        rw [tailSpan]
        omega
      have coefficient :
          24 * span ≤
            512 * ((count + 1) + 1) * span :=
        Nat.mul_le_mul_right span
          (by omega :
            24 ≤ 512 * ((count + 1) + 1))
      rcases joined with
        ⟨steps, final, bounded, run, halted,
          finalState, outputEmpty⟩
      exact
        ⟨steps, final,
          Nat.le_trans bounded
            (Nat.le_trans combined coefficient),
          run, halted, finalState, outputEmpty⟩
  | missingGateEnd count left right =>
      let gate : RawGate :=
        { left := left, right := right }
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates count) ++
          sourceCells left ++ sourceCells right
      have sources :=
        gateSources_exact inputs done count gate []
      have sourcesCanonical :
          workRunExact? machine
              (gateSourcesSteps inputs done count gate)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (count + 1))
                (SourceParser.packedTokenCells
                  (encodeSourceTokens left ++
                    encodeSourceTokens right))) =
            some
              (guardedConfig State.gateEndFirst
                parsedPrefix []) := by
        rw [packedTokenCells_append,
          SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [gate, parsedPrefix,
          List.append_assoc] using sources
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        apply safe_of_ordinary
        dsimp [parsedPrefix]
        exact ordinary_append
          (ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates count))
            (sourceCells_ordinary left))
          (sourceCells_ordinary right)
      have tail :=
        missingExpected_bounded_exact State.gateEndFirst
          parsedPrefix parsedSafe
          (gateEndMissingFailure_exact parsedPrefix)
      have joined :=
        BoundedRejectingExecution.prepend
          (gateSourcesSteps inputs done count gate)
          (8 * (parsedPrefix.length + 1))
          _ _ sourcesCanonical tail
      let span :=
        (failureGatePrefix inputs done
            (count + 1)).length +
          (SourceParser.packedTokenCells
            (encodeSourceTokens left ++
              encodeSourceTokens right)).length + 1
      have packedShape :
          (SourceParser.packedTokenCells
              (encodeSourceTokens left ++
                encodeSourceTokens right)).length =
            (sourceCells left ++ sourceCells right).length := by
        rw [packedTokenCells_append,
          SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
      have stepLinear :
          gateSourcesSteps inputs done count gate ≤
            16 * span := by
        calc
          gateSourcesSteps inputs done count gate ≤
              16 *
                ((failureGatePrefix inputs done
                    (count + 1)).length +
                  (sourceCells gate.left ++
                    sourceCells gate.right ++ []).length + 1) :=
            gateSourcesSteps_le_span inputs done count gate []
          _ = 16 * span := by
            dsimp [gate, span]
            rw [packedShape]
            simp
      have tailSpan :
          parsedPrefix.length + 1 = span := by
        have preserved :=
          gateSources_span_preserved inputs done count gate []
        dsimp [gate, parsedPrefix, span] at preserved ⊢
        rw [packedShape]
        simp only [List.length_append, List.length_nil,
          Nat.add_zero] at preserved ⊢
        omega
      have combined :
          gateSourcesSteps inputs done count gate +
              8 * (parsedPrefix.length + 1) ≤
            24 * span := by
        rw [tailSpan]
        omega
      have coefficient :
          24 * span ≤
            512 * ((count + 1) + 1) * span :=
        Nat.mul_le_mul_right span
          (by omega :
            24 ≤ 512 * ((count + 1) + 1))
      rcases joined with
        ⟨steps, final, bounded, run, halted,
          finalState, outputEmpty⟩
      exact
        ⟨steps, final,
          Nat.le_trans bounded
            (Nat.le_trans combined coefficient),
          run, halted, finalState, outputEmpty⟩
  | wrongGateEnd count left right token suffix notGateEnd =>
      let gate : RawGate :=
        { left := left, right := right }
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates count) ++
          sourceCells left ++ sourceCells right
      have sources :=
        gateSources_exact inputs done count gate
          (SourceParser.packedTokenCells
            (token :: suffix))
      have sourcesCanonical :
          workRunExact? machine
              (gateSourcesSteps inputs done count gate)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (count + 1))
                (SourceParser.packedTokenCells
                  (encodeSourceTokens left ++
                    encodeSourceTokens right ++
                      token :: suffix))) =
            some
              (guardedConfig State.gateEndFirst
                parsedPrefix
                (SourceParser.packedTokenCells
                  (token :: suffix))) := by
        repeat rw [packedTokenCells_append]
        rw [SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [gate, parsedPrefix,
          List.append_assoc] using sources
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        apply safe_of_ordinary
        dsimp [parsedPrefix]
        exact ordinary_append
          (ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates count))
            (sourceCells_ordinary left))
          (sourceCells_ordinary right)
      have tail :=
        gateEndWrongToken_bounded_exact
          parsedPrefix parsedSafe token suffix notGateEnd
      have joined :=
        BoundedRejectingExecution.prepend
          (gateSourcesSteps inputs done count gate)
          (16 *
            (parsedPrefix.length +
              (SourceParser.packedTokenCells
                (token :: suffix)).length + 1))
          _ _ sourcesCanonical tail
      let span :=
        (failureGatePrefix inputs done
            (count + 1)).length +
          (SourceParser.packedTokenCells
            (encodeSourceTokens left ++
              encodeSourceTokens right ++
                token :: suffix)).length + 1
      have packedShape :
          (SourceParser.packedTokenCells
              (encodeSourceTokens left ++
                encodeSourceTokens right ++
                  token :: suffix)).length =
            (sourceCells left ++ sourceCells right ++
              SourceParser.packedTokenCells
                (token :: suffix)).length := by
        repeat rw [packedTokenCells_append]
        rw [SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
      have stepLinear :
          gateSourcesSteps inputs done count gate ≤
            16 * span := by
        calc
          gateSourcesSteps inputs done count gate ≤
              16 *
                ((failureGatePrefix inputs done
                    (count + 1)).length +
                  (sourceCells gate.left ++
                    sourceCells gate.right ++
                      SourceParser.packedTokenCells
                        (token :: suffix)).length + 1) :=
            gateSourcesSteps_le_span inputs done count gate
              (SourceParser.packedTokenCells
                (token :: suffix))
          _ = 16 * span := by
            dsimp [gate, span]
            rw [packedShape]
      have tailSpan :
          parsedPrefix.length +
                (SourceParser.packedTokenCells
                  (token :: suffix)).length + 1 =
            span := by
        have preserved :=
          gateSources_span_preserved inputs done count gate
            (SourceParser.packedTokenCells
              (token :: suffix))
        dsimp [gate, parsedPrefix, span] at preserved ⊢
        rw [packedShape]
        simp only [List.length_append] at preserved ⊢
        omega
      have combined :
          gateSourcesSteps inputs done count gate +
              16 *
                (parsedPrefix.length +
                  (SourceParser.packedTokenCells
                    (token :: suffix)).length + 1) ≤
            32 * span := by
        rw [tailSpan]
        omega
      have coefficient :
          32 * span ≤
            512 * ((count + 1) + 1) * span :=
        Nat.mul_le_mul_right span
          (by omega :
            32 ≤ 512 * ((count + 1) + 1))
      rcases joined with
        ⟨steps, final, bounded, run, halted,
          finalState, outputEmpty⟩
      exact
        ⟨steps, final,
          Nat.le_trans bounded
            (Nat.le_trans combined coefficient),
          run, halted, finalState, outputEmpty⟩
  | @rest count left right failedTokens failure ih =>
      let gate : RawGate :=
        { left := left, right := right }
      have record :=
        gateRecord_exact inputs done count gate
          (SourceParser.packedTokenCells failedTokens)
      have recordCanonical :
          workRunExact? machine
              (gateRecordSteps inputs done count gate)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (count + 1))
                (SourceParser.packedTokenCells
                  (encodeSourceTokens left ++
                    encodeSourceTokens right ++
                      .gateEnd :: failedTokens))) =
            some
              (guardedConfig State.gateStart
                (failureGatePrefix inputs
                  (done ++ [gate]) count)
                (SourceParser.packedTokenCells
                  failedTokens)) := by
        repeat rw [packedTokenCells_append]
        rw [SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [gate, gateCells,
          SourceParser.gateCells,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          cell01, cell11,
          SourceParser.cell01,
          SourceParser.cell11,
          List.append_assoc] using record
      have tail := ih (done ++ [gate])
      have joined :=
        BoundedRejectingExecution.prepend
          (gateRecordSteps inputs done count gate)
          (512 * (count + 1) *
            ((failureGatePrefix inputs
                (done ++ [gate]) count).length +
              (SourceParser.packedTokenCells
                failedTokens).length + 1))
          _ _ recordCanonical tail
      let span :=
        (failureGatePrefix inputs done
            (count + 1)).length +
          (SourceParser.packedTokenCells
            (encodeSourceTokens left ++
              encodeSourceTokens right ++
                .gateEnd :: failedTokens)).length + 1
      have packedShape :
          (SourceParser.packedTokenCells
              (encodeSourceTokens left ++
                encodeSourceTokens right ++
                  .gateEnd :: failedTokens)).length =
            (gateCells gate ++
              SourceParser.packedTokenCells
                failedTokens).length := by
        repeat rw [packedTokenCells_append]
        rw [SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simp [gate, gateCells, SourceParser.gateCells,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          SourceParser.cell01,
          SourceParser.cell11,
          List.append_assoc]
      have stepLinear :
          gateRecordSteps inputs done count gate ≤
            32 * span := by
        calc
          gateRecordSteps inputs done count gate ≤
              32 *
                ((failureGatePrefix inputs done
                    (count + 1)).length +
                  (gateCells gate ++
                    SourceParser.packedTokenCells
                      failedTokens).length + 1) :=
            gateRecordSteps_le_span inputs done count gate
              (SourceParser.packedTokenCells failedTokens)
          _ = 32 * span := by
            dsimp [span]
            rw [packedShape]
      have tailSpan :
          (failureGatePrefix inputs
                (done ++ [gate]) count).length +
              (SourceParser.packedTokenCells
                failedTokens).length + 1 =
            span := by
        have preserved :=
          gateRecord_span_preserved inputs done count gate
            (SourceParser.packedTokenCells failedTokens)
        dsimp [span]
        rw [packedShape]
        omega
      have combined :
          gateRecordSteps inputs done count gate +
              512 * (count + 1) * span ≤
            512 * ((count + 1) + 1) * span := by
        calc
          gateRecordSteps inputs done count gate +
                512 * (count + 1) * span
              ≤ 32 * span +
                  512 * (count + 1) * span :=
            Nat.add_le_add_right stepLinear _
          _ ≤ 512 * span +
                512 * (count + 1) * span := by
            exact Nat.add_le_add_right
              (Nat.mul_le_mul_right span (by omega)) _
          _ = (512 + 512 * (count + 1)) * span := by
            rw [Nat.add_mul]
          _ = 512 * ((count + 1) + 1) * span := by
            have coefficient :
                512 + 512 * (count + 1) =
                  512 * ((count + 1) + 1) := by
              omega
            rw [coefficient]
      rcases joined with
        ⟨steps, final, bounded, run, halted,
          finalState, outputEmpty⟩
      rw [tailSpan] at bounded
      exact
        ⟨steps, final,
          Nat.le_trans bounded combined,
          run, halted, finalState, outputEmpty⟩

private theorem gatePrefix_length_eq_packedGatesPrefix
    (inputs : Nat) (gates : List RawGate) :
    (gatePrefix inputs gates []).length =
      (SourceParser.packedTokenCells
        (SourceParser.circuitGatesPrefixTokens
          inputs gates)).length := by
  rw [packedCircuitGatesPrefixTokens_eq]
  simp [gatePrefix, SourceParser.gatePrefix,
    headerPrefixCells,
    SourceParser.countCells_length,
    SourceParser.natCells_length,
    SourceParser.markedGateListCells_length]

private theorem outputParsedPrefix_length_eq_packed
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) :
    (outputPrefix inputs gates ++
        sourceCells output).length =
      (SourceParser.packedTokenCells
        (SourceParser.circuitOutputPrefixTokens
          inputs gates output)).length := by
  unfold SourceParser.circuitOutputPrefixTokens
  rw [packedTokenCells_append,
    packedTokenCells_append,
    SourceParser.packedTokenCells_encodeSourceTokens]
  simp [outputPrefix,
    packedCircuitGatesPrefixTokens_eq,
    headerPrefixCells,
    SourceParser.packedTokenCells,
    SourceParser.tokenCells,
    SourceParser.markedGateListCells_length]

private theorem outputPrefix_length_eq_packedProgramPrefix
    (inputs : Nat) (gates : List RawGate) :
    (outputPrefix inputs gates).length =
      (SourceParser.packedTokenCells
        (SourceParser.circuitGatesPrefixTokens
            inputs gates ++ [.programEnd])).length := by
  rw [packedTokenCells_append]
  simp [outputPrefix,
    packedCircuitGatesPrefixTokens_eq,
    headerPrefixCells,
    SourceParser.packedTokenCells,
    SourceParser.tokenCells,
    SourceParser.markedGateListCells_length]

private theorem succ_le_grammarCellCube (cells : Nat) :
    cells + 1 ≤ grammarCellCube cells := by
  have positive : 1 ≤ cells + 1 := by omega
  exact Nat.le_trans
    (by
      simpa using
        Nat.mul_le_mul_left (cells + 1) positive)
    (succSquare_le_grammarCellCube cells)

private theorem BoundedRejectingExecution.widen
    {initial : WorkConfiguration} {small large : Nat}
    (result : BoundedRejectingExecution initial small)
    (bound : small ≤ large) :
    BoundedRejectingExecution initial large := by
  rcases result with
    ⟨steps, final, bounded, run, halted,
      finalState, outputEmpty⟩
  exact
    ⟨steps, final, Nat.le_trans bounded bound,
      run, halted, finalState, outputEmpty⟩

private theorem circuitGatesPrefixWordSteps_le_cube
    (inputs : Nat) (gates : List RawGate) :
    circuitGatesPrefixWordSteps inputs gates ≤
      16 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (SourceParser.circuitGatesPrefixTokens
              inputs gates)).length := by
  let cells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitGatesPrefixTokens
        inputs gates)).length
  have packedEq :=
    packedCircuitGatesPrefixTokens_eq inputs gates
  have headerLength :
      (headerPrefixCells inputs gates.length).length ≤ cells := by
    dsimp [cells]
    rw [packedEq]
    simp
  have headerCost :
      headerPrefixWordSteps inputs gates.length ≤
        3 * grammarCellCube cells := by
    have cellsBound := cell_le_grammarCellCube cells
    have one := one_le_grammarCellCube cells
    unfold headerPrefixWordSteps inputPrefixWordSteps
    simp [headerPrefixCells,
      SourceParser.natCells_length] at headerLength
    omega
  have workspaceEq :
      gateWorkspace inputs [] gates = cells := by
    dsimp [cells, gateWorkspace]
    rw [packedEq]
    simp [SourceParser.gateWorkspace,
      SourceParser.gatePrefix,
      gateListCells,
      headerPrefixCells,
      SourceParser.countCells_length,
      SourceParser.natCells_length,
      SourceParser.markedGateListCells]
    omega
  have gateCount :
      gates.length ≤ cells + 1 := by
    simp [headerPrefixCells,
      SourceParser.natCells_length] at headerLength
    omega
  have gateRun :=
    gatesSteps_le_linearWorkspace inputs [] gates
  rw [workspaceEq] at gateRun
  have product :=
    Nat.mul_le_mul gateCount
      (Nat.le_refl (cells + 1))
  have gatesCost :
      gatesSteps inputs [] gates ≤
        9 * grammarCellCube cells := by
    calc
      gatesSteps inputs [] gates ≤
          gates.length * (9 * (cells + 1)) := gateRun
      _ = 9 * (gates.length * (cells + 1)) := by
        ac_rfl
      _ ≤ 9 * ((cells + 1) * (cells + 1)) :=
        Nat.mul_le_mul_left 9 product
      _ ≤ 9 * grammarCellCube cells :=
        Nat.mul_le_mul_left 9
          (succSquare_le_grammarCellCube cells)
  unfold circuitGatesPrefixWordSteps
  change
    headerPrefixWordSteps inputs gates.length +
        gatesSteps inputs [] gates ≤
      16 * grammarCellCube cells
  omega

private theorem circuitProgramPrefixWordSteps_le_cube
    (inputs : Nat) (gates : List RawGate) :
    circuitProgramPrefixWordSteps inputs gates ≤
      24 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (SourceParser.circuitGatesPrefixTokens
                inputs gates ++ [.programEnd])).length := by
  let gatesCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitGatesPrefixTokens
        inputs gates)).length
  let cells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitGatesPrefixTokens
          inputs gates ++ [.programEnd])).length
  have gatesCost :=
    circuitGatesPrefixWordSteps_le_cube inputs gates
  have prefixLe : gatesCells ≤ cells := by
    dsimp [gatesCells, cells]
    rw [packedTokenCells_append]
    simp
  have cubeLe :=
    grammarCellCube_mono prefixLe
  have gatesCost' :
      circuitGatesPrefixWordSteps inputs gates ≤
        16 * grammarCellCube cells :=
    Nat.le_trans gatesCost
      (Nat.mul_le_mul_left 16 cubeLe)
  have prefixLength :=
    gatePrefix_length_eq_packedGatesPrefix inputs gates
  have prefixCube :
      (gatePrefix inputs gates []).length ≤
        grammarCellCube cells := by
    have base :
        (gatePrefix inputs gates []).length ≤ cells := by
      rw [prefixLength]
      exact prefixLe
    exact Nat.le_trans base
      (cell_le_grammarCellCube cells)
  have one := one_le_grammarCellCube cells
  have programCost :
      programEndSteps inputs gates ≤
        8 * grammarCellCube cells := by
    rw [programEndSteps_eq]
    omega
  unfold circuitProgramPrefixWordSteps
  change
    circuitGatesPrefixWordSteps inputs gates +
        programEndSteps inputs gates ≤
      24 * grammarCellCube cells
  omega

private theorem circuitOutputPrefixWordSteps_le_cube
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) :
    circuitOutputPrefixWordSteps inputs gates output ≤
      25 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
              inputs gates output)).length := by
  let programCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitGatesPrefixTokens
          inputs gates ++ [.programEnd])).length
  let cells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
        inputs gates output)).length
  have programCost :=
    circuitProgramPrefixWordSteps_le_cube inputs gates
  have programLe : programCells ≤ cells := by
    dsimp [programCells, cells]
    unfold SourceParser.circuitOutputPrefixTokens
    repeat rw [packedTokenCells_append]
    simp
  have cubeLe :=
    grammarCellCube_mono programLe
  have programCost' :
      circuitProgramPrefixWordSteps inputs gates ≤
        24 * grammarCellCube cells :=
    Nat.le_trans programCost
      (Nat.mul_le_mul_left 24 cubeLe)
  have outputLe :
      (sourceCells output).length ≤ cells := by
    dsimp [cells]
    unfold SourceParser.circuitOutputPrefixTokens
    repeat rw [packedTokenCells_append]
    rw [SourceParser.packedTokenCells_encodeSourceTokens]
    simp [sourceCells]
    omega
  have outputCost :
      (sourceCells output).length ≤
        grammarCellCube cells :=
    Nat.le_trans outputLe
      (cell_le_grammarCellCube cells)
  unfold circuitOutputPrefixWordSteps
  change
    circuitProgramPrefixWordSteps inputs gates +
        (sourceCells output).length ≤
      25 * grammarCellCube cells
  omega

private theorem circuitMissingVersionFailure_bounded_exact :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells [])))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells []).length) := by
  refine
    ⟨6, emptyRejectConfiguration, ?_, ?_,
      rfl, rfl, emptyRejectConfiguration_outputBits⟩
  · have one := one_le_grammarCellCube 0
    simpa [SourceParser.packedTokenCells] using
      (show 6 ≤ 4096 * grammarCellCube 0 by omega)
  · simpa [rawInputWorkTape, packWorkSymbols,
      SourceParser.packedTokenCells] using malformedEmpty_exact

private theorem circuitWrongVersionFailure_bounded_exact
    (token : Token) (suffix : List Token)
    (notVersion : token ≠ .version0) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (token :: suffix))))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (token :: suffix)).length) := by
  have prefixRun :=
    scannerBootToken_exact token suffix
  have tail :=
    versionWrongToken_bounded_exact
      token suffix notVersion
  have joined :=
    BoundedRejectingExecution.prepend
      2
      (16 *
        ((SourceParser.packedTokenCells
          (token :: suffix)).length + 1))
      _ _ prefixRun tail
  apply BoundedRejectingExecution.widen joined
  have succCube :=
    succ_le_grammarCellCube
      (SourceParser.packedTokenCells
        (token :: suffix)).length
  omega

private theorem circuitInputCountFailure_bounded_exact
    {tokens : List Token}
    (failure : SourceParser.NatTokenFailure tokens) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (.version0 :: tokens))))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (.version0 :: tokens)).length) := by
  have prefixRun :=
    versionPrefixWord_exact
      (SourceParser.packedTokenCells tokens)
  have prefixCanonical :
      workRunExact? machine 4
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (.version0 :: tokens)))) =
        some
          (guardedConfig State.inputCountFirst
            [cell00, cell00]
            (SourceParser.packedTokenCells tokens)) := by
    simpa [SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      cell00, SourceParser.cell00] using prefixRun
  have prefixSafe : SafeSourceWord [cell00, cell00] := by
    intro symbol member
    simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with rfl | rfl | impossible
    · decide
    · decide
    · contradiction
  have tail :=
    natTokenFailure_bounded_exact .inputCount
      [cell00, cell00] failure prefixSafe
  have joined :=
    BoundedRejectingExecution.prepend
      4
      (8 *
        (([cell00, cell00] : List WorkSymbol).length +
          (SourceParser.packedTokenCells tokens).length + 1))
      _ _ prefixCanonical tail
  apply BoundedRejectingExecution.widen joined
  let cells :=
    (SourceParser.packedTokenCells
      (.version0 :: tokens)).length
  have cellsEq :
      cells =
        2 + (SourceParser.packedTokenCells tokens).length := by
    dsimp [cells]
    simp [SourceParser.packedTokenCells,
      SourceParser.tokenCells]
    omega
  have succCube := succ_le_grammarCellCube cells
  change
    4 +
          8 *
            (([cell00, cell00] : List WorkSymbol).length +
              (SourceParser.packedTokenCells tokens).length + 1) ≤
      4096 * grammarCellCube cells
  simp only [List.length_cons, List.length_nil]
  omega

private theorem circuitGateCountFailure_bounded_exact
    (inputs : Nat) {tokens : List Token}
    (failure : SourceParser.NatTokenFailure tokens) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (.version0 ::
              (encodeNatTokens inputs ++ tokens)))))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (.version0 ::
              (encodeNatTokens inputs ++ tokens))).length) := by
  let parsedPrefix :=
    [cell00, cell00] ++ natCells inputs
  have prefixRun :=
    inputPrefixWord_exact inputs
      (SourceParser.packedTokenCells tokens)
  have prefixCanonical :
      workRunExact? machine (inputPrefixWordSteps inputs)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (.version0 ::
                  (encodeNatTokens inputs ++ tokens))))) =
        some
          (guardedConfig State.gateCountFirst
            parsedPrefix
            (SourceParser.packedTokenCells tokens)) := by
    dsimp [parsedPrefix]
    simpa [SourceParser.packedTokenCells,
      SourceParser.tokenCells, packedTokenCells_append,
      SourceParser.packedTokenCells_encodeNatTokens,
      cell00, SourceParser.cell00,
      List.append_assoc] using prefixRun
  have prefixSafe : SafeSourceWord parsedPrefix := by
    have safe :=
      packedTokenCells_safe
        (.version0 :: encodeNatTokens inputs)
    dsimp [parsedPrefix]
    simpa [SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      SourceParser.packedTokenCells_encodeNatTokens,
      cell00, SourceParser.cell00] using safe
  have tail :=
    natTokenFailure_bounded_exact .gateCount
      parsedPrefix failure prefixSafe
  have joined :=
    BoundedRejectingExecution.prepend
      (inputPrefixWordSteps inputs)
      (8 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells tokens).length + 1))
      _ _ prefixCanonical tail
  apply BoundedRejectingExecution.widen joined
  let cells :=
    (SourceParser.packedTokenCells
      (.version0 ::
        (encodeNatTokens inputs ++ tokens))).length
  have cellsEq :
      cells =
        parsedPrefix.length +
          (SourceParser.packedTokenCells tokens).length := by
    dsimp [cells, parsedPrefix]
    simp [SourceParser.packedTokenCells,
      SourceParser.tokenCells, packedTokenCells_append,
      SourceParser.packedTokenCells_encodeNatTokens,
      SourceParser.natCells_length]
    omega
  have prefixCost :
      inputPrefixWordSteps inputs ≤
        3 * grammarCellCube cells := by
    have cellsBound := cell_le_grammarCellCube cells
    have one := one_le_grammarCellCube cells
    unfold inputPrefixWordSteps
    dsimp [parsedPrefix] at cellsEq
    simp [SourceParser.natCells_length] at cellsEq
    omega
  have succCube := succ_le_grammarCellCube cells
  change
    inputPrefixWordSteps inputs +
          8 *
            (parsedPrefix.length +
              (SourceParser.packedTokenCells tokens).length + 1) ≤
      4096 * grammarCellCube cells
  rw [← cellsEq]
  omega

private theorem circuitGatesFailure_bounded_exact
    (inputs gateCount : Nat) {tokens : List Token}
    (failure :
      SourceParser.NGatesTokenFailure gateCount tokens) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitHeaderTokens
                inputs gateCount ++
              tokens))))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (SourceParser.circuitHeaderTokens
                inputs gateCount ++
              tokens)).length) := by
  have headerRun :=
    headerPrefixWord_exact inputs gateCount
      (SourceParser.packedTokenCells tokens)
  have prefixEq :
      failureGatePrefix inputs [] gateCount =
        headerPrefixCells inputs gateCount := by
    simp [failureGatePrefix, placeholderGates,
      gatePrefix, SourceParser.gatePrefix,
      headerPrefixCells,
      SourceParser.markedGateListCells,
      SourceParser.countCells,
      natCells, cell00,
      SourceParser.cell00]
  have headerCanonical :
      workRunExact? machine
          (headerPrefixWordSteps inputs gateCount)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitHeaderTokens
                    inputs gateCount ++
                  tokens)))) =
        some
          (guardedConfig State.gateStart
            (failureGatePrefix inputs [] gateCount)
            (SourceParser.packedTokenCells tokens)) := by
    rw [packedTokenCells_append,
      packedCircuitHeaderTokens_eq, prefixEq]
    exact headerRun
  have tail :=
    nGatesTokenFailure_bounded_exact
      inputs [] failure
  have joined :=
    BoundedRejectingExecution.prepend
      (headerPrefixWordSteps inputs gateCount)
      (512 * (gateCount + 1) *
        ((failureGatePrefix inputs [] gateCount).length +
          (SourceParser.packedTokenCells tokens).length + 1))
      _ _ headerCanonical tail
  apply BoundedRejectingExecution.widen joined
  let cells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitHeaderTokens
          inputs gateCount ++ tokens)).length
  have cellsEq :
      cells =
        (failureGatePrefix inputs [] gateCount).length +
          (SourceParser.packedTokenCells tokens).length := by
    dsimp [cells]
    rw [packedTokenCells_append,
      packedCircuitHeaderTokens_eq, prefixEq]
    simp
  have countLe : gateCount + 1 ≤ cells + 1 := by
    have headerLe :
        (headerPrefixCells inputs gateCount).length ≤ cells := by
      rw [cellsEq, prefixEq]
      omega
    simp [headerPrefixCells,
      SourceParser.natCells_length] at headerLe
    omega
  have headerCost :
      headerPrefixWordSteps inputs gateCount ≤
        3 * grammarCellCube cells := by
    have cellsBound := cell_le_grammarCellCube cells
    have one := one_le_grammarCellCube cells
    have headerLe :
        (headerPrefixCells inputs gateCount).length ≤ cells := by
      rw [cellsEq, prefixEq]
      omega
    unfold headerPrefixWordSteps inputPrefixWordSteps
    simp [headerPrefixCells,
      SourceParser.natCells_length] at headerLe
    omega
  have tailProduct :=
    Nat.mul_le_mul countLe
      (Nat.le_refl (cells + 1))
  have tailCost :
      512 * (gateCount + 1) * (cells + 1) ≤
        512 * grammarCellCube cells := by
    calc
      512 * (gateCount + 1) * (cells + 1) =
          512 * ((gateCount + 1) * (cells + 1)) := by
        ac_rfl
      _ ≤ 512 * ((cells + 1) * (cells + 1)) :=
        Nat.mul_le_mul_left 512 tailProduct
      _ ≤ 512 * grammarCellCube cells :=
        Nat.mul_le_mul_left 512
          (succSquare_le_grammarCellCube cells)
  change
    headerPrefixWordSteps inputs gateCount +
          512 * (gateCount + 1) *
            ((failureGatePrefix inputs [] gateCount).length +
              (SourceParser.packedTokenCells tokens).length + 1) ≤
      4096 * grammarCellCube cells
  rw [← cellsEq]
  exact Nat.le_trans
    (Nat.add_le_add headerCost tailCost)
    (by omega)

private theorem circuitMissingProgramEndFailure_bounded_exact
    (inputs : Nat) (gates : List RawGate) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitGatesPrefixTokens
              inputs gates))))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (SourceParser.circuitGatesPrefixTokens
              inputs gates)).length) := by
  have prefixRun :=
    circuitGatesPrefixWord_exact inputs gates []
  have prefixSafe :
      SafeSourceWord (gatePrefix inputs gates []) :=
    safe_of_ordinary
      (gatePrefix_ordinary inputs gates [])
  have tail :=
    missingExpected_bounded_exact State.gateStart
      (gatePrefix inputs gates []) prefixSafe
      (gateStartMissingFailure_exact
        (gatePrefix inputs gates []))
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitGatesPrefixWordSteps inputs gates)
      (8 * ((gatePrefix inputs gates []).length + 1))
      _ _ (by simpa using prefixRun) tail
  apply BoundedRejectingExecution.widen joined
  let cells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitGatesPrefixTokens
        inputs gates)).length
  have prefixCost :=
    circuitGatesPrefixWordSteps_le_cube inputs gates
  have prefixCost' :
      circuitGatesPrefixWordSteps inputs gates ≤
        16 * grammarCellCube cells := by
    simpa [cells] using prefixCost
  have lengthEq :=
    gatePrefix_length_eq_packedGatesPrefix inputs gates
  have succCube := succ_le_grammarCellCube cells
  have tailCost :
      8 * ((gatePrefix inputs gates []).length + 1) ≤
      8 * grammarCellCube cells := by
    change
      (gatePrefix inputs gates []).length = cells
      at lengthEq
    rw [lengthEq]
    exact Nat.mul_le_mul_left 8 succCube
  change
    circuitGatesPrefixWordSteps inputs gates +
          8 * ((gatePrefix inputs gates []).length + 1) ≤
      4096 * grammarCellCube cells
  exact Nat.le_trans
    (Nat.add_le_add prefixCost' tailCost)
    (by omega)

private theorem circuitWrongProgramEndFailure_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (token : Token) (suffix : List Token)
    (notProgramEnd : token ≠ .programEnd) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitGatesPrefixTokens
                inputs gates ++
              token :: suffix))))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (SourceParser.circuitGatesPrefixTokens
                inputs gates ++
              token :: suffix)).length) := by
  have prefixRun :=
    circuitGatesPrefixWord_exact inputs gates
      (SourceParser.packedTokenCells
        (token :: suffix))
  have prefixCanonical :
      workRunExact? machine
          (circuitGatesPrefixWordSteps inputs gates)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitGatesPrefixTokens
                    inputs gates ++
                  token :: suffix)))) =
        some
          (guardedConfig State.gateStart
            (gatePrefix inputs gates [])
            (SourceParser.packedTokenCells
              (token :: suffix))) := by
    rw [packedTokenCells_append]
    exact prefixRun
  have tail :=
    wrongProgramEndToken_bounded_exact
      inputs gates token suffix notProgramEnd
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitGatesPrefixWordSteps inputs gates)
      (256 *
        ((gatePrefix inputs gates []).length +
          (SourceParser.packedTokenCells
            (token :: suffix)).length + 1))
      _ _ prefixCanonical tail
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitGatesPrefixTokens
        inputs gates)).length
  let cells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitGatesPrefixTokens
          inputs gates ++ token :: suffix)).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    rw [packedTokenCells_append]
    simp
  have prefixCube :=
    grammarCellCube_mono prefixLe
  have prefixCost :
      circuitGatesPrefixWordSteps inputs gates ≤
        16 * grammarCellCube cells :=
    Nat.le_trans
      (circuitGatesPrefixWordSteps_le_cube inputs gates)
      (Nat.mul_le_mul_left 16 prefixCube)
  have spanEq :
      (gatePrefix inputs gates []).length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1 =
        cells + 1 := by
    dsimp [cells]
    rw [packedTokenCells_append,
      gatePrefix_length_eq_packedGatesPrefix]
    simp
  have succCube := succ_le_grammarCellCube cells
  have tailCost :
      256 *
          ((gatePrefix inputs gates []).length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1) ≤
        256 * grammarCellCube cells := by
    rw [spanEq]
    exact Nat.mul_le_mul_left 256 succCube
  change
    circuitGatesPrefixWordSteps inputs gates +
          256 *
            ((gatePrefix inputs gates []).length +
              (SourceParser.packedTokenCells
                (token :: suffix)).length + 1) ≤
      4096 * grammarCellCube cells
  exact Nat.le_trans
    (Nat.add_le_add prefixCost tailCost)
    (by omega)

private theorem circuitOutputFailure_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    {tokens : List Token}
    (failure : SourceParser.SourceTokenFailure tokens) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitGatesPrefixTokens inputs gates ++
              .programEnd :: tokens))))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (SourceParser.circuitGatesPrefixTokens inputs gates ++
              .programEnd :: tokens)).length) := by
  have prefixRun :=
    circuitProgramPrefixWord_exact inputs gates
      (SourceParser.packedTokenCells tokens)
  have prefixCanonical :
      workRunExact? machine
          (circuitProgramPrefixWordSteps inputs gates)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitGatesPrefixTokens
                    inputs gates ++
                  .programEnd :: tokens)))) =
        some
          (guardedConfig (State.sourceStart .output)
            (outputPrefix inputs gates)
            (SourceParser.packedTokenCells tokens)) := by
    rw [packedTokenCells_append] at prefixRun
    rw [packedTokenCells_append]
    simpa [SourceParser.packedTokenCells,
      SourceParser.tokenCells, List.append_assoc] using prefixRun
  have tail :=
    sourceTokenFailure_bounded_exact .output
      (outputPrefix inputs gates) failure
      (safe_of_ordinary
        (outputPrefix_ordinary inputs gates))
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitProgramPrefixWordSteps inputs gates)
      (16 *
        ((outputPrefix inputs gates).length +
          (SourceParser.packedTokenCells tokens).length + 1))
      _ _ prefixCanonical tail
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitGatesPrefixTokens
          inputs gates ++ [.programEnd])).length
  let cells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitGatesPrefixTokens
          inputs gates ++ .programEnd :: tokens)).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    repeat rw [packedTokenCells_append]
    simp [SourceParser.packedTokenCells]
  have prefixCube :=
    grammarCellCube_mono prefixLe
  have prefixCost :
      circuitProgramPrefixWordSteps inputs gates ≤
        24 * grammarCellCube cells :=
    Nat.le_trans
      (circuitProgramPrefixWordSteps_le_cube inputs gates)
      (Nat.mul_le_mul_left 24 prefixCube)
  have spanEq :
      (outputPrefix inputs gates).length +
            (SourceParser.packedTokenCells tokens).length + 1 =
        cells + 1 := by
    dsimp [cells]
    rw [outputPrefix_length_eq_packedProgramPrefix]
    repeat rw [packedTokenCells_append]
    simp [SourceParser.packedTokenCells]
    omega
  have succCube := succ_le_grammarCellCube cells
  have tailCost :
      16 *
          ((outputPrefix inputs gates).length +
            (SourceParser.packedTokenCells tokens).length + 1) ≤
        16 * grammarCellCube cells := by
    rw [spanEq]
    exact Nat.mul_le_mul_left 16 succCube
  change
    circuitProgramPrefixWordSteps inputs gates +
          16 *
            ((outputPrefix inputs gates).length +
              (SourceParser.packedTokenCells tokens).length + 1) ≤
      4096 * grammarCellCube cells
  exact Nat.le_trans
    (Nat.add_le_add prefixCost tailCost)
    (by omega)

private theorem circuitMissingOutputsEndFailure_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
              inputs gates output))))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
              inputs gates output)).length) := by
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  have prefixRun :=
    circuitOutputPrefixWord_exact
      inputs gates output []
  have prefixCanonical :
      workRunExact? machine
          (circuitOutputPrefixWordSteps inputs gates output)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitOutputPrefixTokens
                  inputs gates output)))) =
        some
          (guardedConfig State.outputsEndFirst
            parsedPrefix []) := by
    simpa [parsedPrefix] using prefixRun
  have tail :=
    missingExpected_bounded_exact State.outputsEndFirst
      parsedPrefix
      (outputParsedPrefix_safe inputs gates output)
      (outputsEndMissingFailure_exact parsedPrefix)
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output)
      (8 * (parsedPrefix.length + 1))
      _ _ prefixCanonical tail
  apply BoundedRejectingExecution.widen joined
  let cells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
        inputs gates output)).length
  have prefixCost :=
    circuitOutputPrefixWordSteps_le_cube
      inputs gates output
  have prefixCost' :
      circuitOutputPrefixWordSteps inputs gates output ≤
        25 * grammarCellCube cells := by
    simpa [cells] using prefixCost
  have lengthEq :=
    outputParsedPrefix_length_eq_packed
      inputs gates output
  have succCube := succ_le_grammarCellCube cells
  have tailCost :
      8 * (parsedPrefix.length + 1) ≤
      8 * grammarCellCube cells := by
    change parsedPrefix.length = cells at lengthEq
    rw [lengthEq]
    exact Nat.mul_le_mul_left 8 succCube
  change
    circuitOutputPrefixWordSteps inputs gates output +
          8 * (parsedPrefix.length + 1) ≤
      4096 * grammarCellCube cells
  exact Nat.le_trans
    (Nat.add_le_add prefixCost' tailCost)
    (by omega)

private theorem circuitWrongOutputsEndFailure_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) (token : Token)
    (suffix : List Token)
    (notOutputsEnd : token ≠ .outputsEnd) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
                inputs gates output ++
              token :: suffix))))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
                inputs gates output ++
              token :: suffix)).length) := by
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  have prefixRun :=
    circuitOutputPrefixWord_exact inputs gates output
      (SourceParser.packedTokenCells (token :: suffix))
  have prefixCanonical :
      workRunExact? machine
          (circuitOutputPrefixWordSteps inputs gates output)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitOutputPrefixTokens
                    inputs gates output ++
                  token :: suffix)))) =
        some
          (guardedConfig State.outputsEndFirst parsedPrefix
            (SourceParser.packedTokenCells
              (token :: suffix))) := by
    rw [packedTokenCells_append]
    simpa [parsedPrefix] using prefixRun
  have tail :=
    outputsEndWrongToken_bounded_exact parsedPrefix
      (outputParsedPrefix_safe inputs gates output)
      token suffix notOutputsEnd
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output)
      (16 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells
            (token :: suffix)).length + 1))
      _ _ prefixCanonical tail
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
        inputs gates output)).length
  let cells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
          inputs gates output ++ token :: suffix)).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    rw [packedTokenCells_append]
    simp
  have prefixCube :=
    grammarCellCube_mono prefixLe
  have prefixCost :
      circuitOutputPrefixWordSteps inputs gates output ≤
        25 * grammarCellCube cells :=
    Nat.le_trans
      (circuitOutputPrefixWordSteps_le_cube
        inputs gates output)
      (Nat.mul_le_mul_left 25 prefixCube)
  have spanEq :
      parsedPrefix.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1 =
        cells + 1 := by
    dsimp [parsedPrefix, cells]
    rw [packedTokenCells_append,
      outputParsedPrefix_length_eq_packed]
    simp
  have succCube := succ_le_grammarCellCube cells
  have tailCost :
      16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1) ≤
        16 * grammarCellCube cells := by
    rw [spanEq]
    exact Nat.mul_le_mul_left 16 succCube
  change
    circuitOutputPrefixWordSteps inputs gates output +
          16 *
            (parsedPrefix.length +
              (SourceParser.packedTokenCells
                (token :: suffix)).length + 1) ≤
      4096 * grammarCellCube cells
  exact Nat.le_trans
    (Nat.add_le_add prefixCost tailCost)
    (by omega)

private theorem circuitMissingInstanceEndFailure_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
                inputs gates output ++
              [.outputsEnd]))))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
                inputs gates output ++
              [.outputsEnd])).length) := by
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  let afterOutputs :=
    parsedPrefix ++ [cell10, cell01]
  have prefixRun :=
    circuitOutputPrefixWord_exact inputs gates output
      [cell10, cell01]
  have delimiter :=
    outputsEnd_exact parsedPrefix []
  have through :=
    exactRun_add
      (circuitOutputPrefixWordSteps inputs gates output)
      2 _ _ _ (by simpa [parsedPrefix] using prefixRun)
      delimiter
  have throughCanonical :
      workRunExact? machine
          (circuitOutputPrefixWordSteps inputs gates output + 2)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitOutputPrefixTokens
                    inputs gates output ++
                  [.outputsEnd])))) =
        some
          (guardedConfig State.instanceEndFirst
            afterOutputs []) := by
    simpa [parsedPrefix, afterOutputs,
      packedTokenCells_append,
      SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      cell10, cell01,
      SourceParser.cell10,
      SourceParser.cell01,
      List.append_assoc] using through
  have afterSafe : SafeSourceWord afterOutputs := by
    apply safe_append
      (outputParsedPrefix_safe inputs gates output)
    intro symbol member
    simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with rfl | rfl | impossible
    · decide
    · decide
    · contradiction
  have tail :=
    missingExpected_bounded_exact State.instanceEndFirst
      afterOutputs afterSafe
      (instanceEndMissingFailure_exact afterOutputs)
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output + 2)
      (8 * (afterOutputs.length + 1))
      _ _ throughCanonical tail
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
        inputs gates output)).length
  let cells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
          inputs gates output ++ [.outputsEnd])).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    rw [packedTokenCells_append]
    simp
  have prefixCube :=
    grammarCellCube_mono prefixLe
  have prefixCost :
      circuitOutputPrefixWordSteps inputs gates output ≤
        25 * grammarCellCube cells :=
    Nat.le_trans
      (circuitOutputPrefixWordSteps_le_cube
        inputs gates output)
      (Nat.mul_le_mul_left 25 prefixCube)
  have spanEq :
      afterOutputs.length + 1 = cells + 1 := by
    have parsedLength :=
      outputParsedPrefix_length_eq_packed
        inputs gates output
    dsimp [afterOutputs, parsedPrefix, cells]
    repeat rw [packedTokenCells_append]
    simp only [List.length_append, List.length_cons,
      List.length_nil] at parsedLength ⊢
    simp [SourceParser.packedTokenCells,
      SourceParser.tokenCells] at parsedLength ⊢
    omega
  have succCube := succ_le_grammarCellCube cells
  have one := one_le_grammarCellCube cells
  have tailCost :
      8 * (afterOutputs.length + 1) ≤
        8 * grammarCellCube cells := by
    rw [spanEq]
    exact Nat.mul_le_mul_left 8 succCube
  change
    circuitOutputPrefixWordSteps inputs gates output + 2 +
          8 * (afterOutputs.length + 1) ≤
      4096 * grammarCellCube cells
  omega

private theorem circuitWrongInstanceEndFailure_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) (token : Token)
    (suffix : List Token)
    (notInstanceEnd : token ≠ .instanceEnd) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
                inputs gates output ++
              [.outputsEnd, token] ++ suffix))))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
                inputs gates output ++
              [.outputsEnd, token] ++ suffix)).length) := by
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  let afterOutputs :=
    parsedPrefix ++ [cell10, cell01]
  let tokenCells :=
    SourceParser.packedTokenCells (token :: suffix)
  have prefixRun :=
    circuitOutputPrefixWord_exact inputs gates output
      ([cell10, cell01] ++ tokenCells)
  have delimiter :=
    outputsEnd_exact parsedPrefix tokenCells
  have through :=
    exactRun_add
      (circuitOutputPrefixWordSteps inputs gates output)
      2 _ _ _ (by
        simpa [parsedPrefix, tokenCells] using prefixRun)
      delimiter
  have throughCanonical :
      workRunExact? machine
          (circuitOutputPrefixWordSteps inputs gates output + 2)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitOutputPrefixTokens
                    inputs gates output ++
                  [.outputsEnd, token] ++ suffix)))) =
        some
          (guardedConfig State.instanceEndFirst
            afterOutputs tokenCells) := by
    simpa [parsedPrefix, afterOutputs, tokenCells,
      packedTokenCells_append,
      SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      cell10, cell01,
      SourceParser.cell10,
      SourceParser.cell01,
      List.append_assoc] using through
  have afterSafe : SafeSourceWord afterOutputs := by
    apply safe_append
      (outputParsedPrefix_safe inputs gates output)
    intro symbol member
    simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with rfl | rfl | impossible
    · decide
    · decide
    · contradiction
  have tail :=
    instanceEndWrongToken_bounded_exact
      afterOutputs afterSafe token suffix notInstanceEnd
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output + 2)
      (16 *
        (afterOutputs.length +
          (SourceParser.packedTokenCells
            (token :: suffix)).length + 1))
      _ _ throughCanonical
      (by simpa [tokenCells] using tail)
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
        inputs gates output)).length
  let cells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
          inputs gates output ++
        [.outputsEnd, token] ++ suffix)).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    repeat rw [packedTokenCells_append]
    simp
  have prefixCube :=
    grammarCellCube_mono prefixLe
  have prefixCost :
      circuitOutputPrefixWordSteps inputs gates output ≤
        25 * grammarCellCube cells :=
    Nat.le_trans
      (circuitOutputPrefixWordSteps_le_cube
        inputs gates output)
      (Nat.mul_le_mul_left 25 prefixCube)
  have spanEq :
      afterOutputs.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1 =
        cells + 1 := by
    have parsedLength :=
      outputParsedPrefix_length_eq_packed
        inputs gates output
    dsimp [afterOutputs, parsedPrefix, cells]
    repeat rw [packedTokenCells_append]
    simp only [List.length_append, List.length_cons,
      List.length_nil] at parsedLength ⊢
    simp [SourceParser.packedTokenCells,
      SourceParser.tokenCells] at parsedLength ⊢
    omega
  have succCube := succ_le_grammarCellCube cells
  have one := one_le_grammarCellCube cells
  have tailCost :
      16 *
          (afterOutputs.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1) ≤
        16 * grammarCellCube cells := by
    rw [spanEq]
    exact Nat.mul_le_mul_left 16 succCube
  change
    circuitOutputPrefixWordSteps inputs gates output + 2 +
          16 *
            (afterOutputs.length +
              (SourceParser.packedTokenCells
                (token :: suffix)).length + 1) ≤
      4096 * grammarCellCube cells
  omega

private theorem circuitTrailingTokenFailure_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) (token : Token)
    (suffix : List Token) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
                inputs gates output ++
              [.outputsEnd, .instanceEnd, token] ++ suffix))))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells
            (SourceParser.circuitOutputPrefixTokens
                inputs gates output ++
              [.outputsEnd, .instanceEnd, token] ++ suffix)).length) := by
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  let afterOutputs :=
    parsedPrefix ++ [cell10, cell01]
  let afterInstance :=
    afterOutputs ++ [cell10, cell11]
  let tokenCells :=
    SourceParser.packedTokenCells (token :: suffix)
  have prefixRun :=
    circuitOutputPrefixWord_exact inputs gates output
      ([cell10, cell01, cell10, cell11] ++ tokenCells)
  have outputsRun :=
    outputsEnd_exact parsedPrefix
      ([cell10, cell11] ++ tokenCells)
  have instanceRun :=
    instanceEnd_exact afterOutputs tokenCells
  have throughOutputs :=
    exactRun_add
      (circuitOutputPrefixWordSteps inputs gates output)
      2 _ _ _ (by
        simpa [parsedPrefix, tokenCells] using prefixRun)
      outputsRun
  have throughInstance :=
    exactRun_add
      (circuitOutputPrefixWordSteps inputs gates output + 2)
      2 _ _ _ (by
        simpa [afterOutputs, List.append_assoc] using
          throughOutputs)
      instanceRun
  have throughCanonical :
      workRunExact? machine
          (circuitOutputPrefixWordSteps inputs gates output + 2 + 2)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                (SourceParser.circuitOutputPrefixTokens
                    inputs gates output ++
                  [.outputsEnd, .instanceEnd, token] ++ suffix)))) =
        some
          (guardedConfig State.finalEOF
            afterInstance tokenCells) := by
    simpa [parsedPrefix, afterOutputs, afterInstance,
      tokenCells, packedTokenCells_append,
      SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      cell10, cell01, cell11,
      SourceParser.cell10,
      SourceParser.cell01,
      SourceParser.cell11,
      List.append_assoc] using throughInstance
  have afterSafe : SafeSourceWord afterInstance := by
    apply safe_append
    · apply safe_append
        (outputParsedPrefix_safe inputs gates output)
      intro symbol member
      simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with rfl | rfl | impossible
      · decide
      · decide
      · contradiction
    · intro symbol member
      simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with rfl | rfl | impossible
      · decide
      · decide
      · contradiction
  have tail :=
    finalEOFToken_bounded_exact
      afterInstance afterSafe token suffix
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output + 2 + 2)
      (16 *
        (afterInstance.length +
          (SourceParser.packedTokenCells
            (token :: suffix)).length + 1))
      _ _ throughCanonical
      (by simpa [tokenCells] using tail)
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
        inputs gates output)).length
  let cells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
          inputs gates output ++
        [.outputsEnd, .instanceEnd, token] ++ suffix)).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    repeat rw [packedTokenCells_append]
    simp
  have prefixCube :=
    grammarCellCube_mono prefixLe
  have prefixCost :
      circuitOutputPrefixWordSteps inputs gates output ≤
        25 * grammarCellCube cells :=
    Nat.le_trans
      (circuitOutputPrefixWordSteps_le_cube
        inputs gates output)
      (Nat.mul_le_mul_left 25 prefixCube)
  have spanEq :
      afterInstance.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1 =
        cells + 1 := by
    have parsedLength :=
      outputParsedPrefix_length_eq_packed
        inputs gates output
    dsimp [afterInstance, afterOutputs, parsedPrefix, cells]
    repeat rw [packedTokenCells_append]
    simp only [List.length_append, List.length_cons,
      List.length_nil] at parsedLength ⊢
    simp [SourceParser.packedTokenCells,
      SourceParser.tokenCells] at parsedLength ⊢
    omega
  have succCube := succ_le_grammarCellCube cells
  have one := one_le_grammarCellCube cells
  have tailCost :
      16 *
          (afterInstance.length +
            (SourceParser.packedTokenCells
              (token :: suffix)).length + 1) ≤
        16 * grammarCellCube cells := by
    rw [spanEq]
    exact Nat.mul_le_mul_left 16 succCube
  change
    circuitOutputPrefixWordSteps inputs gates output + 2 + 2 +
          16 *
            (afterInstance.length +
              (SourceParser.packedTokenCells
                (token :: suffix)).length + 1) ≤
      4096 * grammarCellCube cells
  omega

private theorem circuitTokenFailure_bounded_exact
    {tokens : List Token}
    (failure : SourceParser.CircuitTokenFailure tokens) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells tokens)))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells tokens).length) := by
  cases failure with
  | missingVersion =>
      exact circuitMissingVersionFailure_bounded_exact
  | wrongVersion token suffix notVersion =>
      exact circuitWrongVersionFailure_bounded_exact
        token suffix notVersion
  | inputCount failure =>
      exact circuitInputCountFailure_bounded_exact failure
  | gateCount inputs failure =>
      exact circuitGateCountFailure_bounded_exact
        inputs failure
  | gates inputs gateCount failure =>
      exact circuitGatesFailure_bounded_exact
        inputs gateCount failure
  | missingProgramEnd inputs gates =>
      exact circuitMissingProgramEndFailure_bounded_exact
        inputs gates
  | wrongProgramEnd inputs gates token suffix notProgramEnd =>
      exact circuitWrongProgramEndFailure_bounded_exact
        inputs gates token suffix notProgramEnd
  | output inputs gates failure =>
      exact circuitOutputFailure_bounded_exact
        inputs gates failure
  | missingOutputsEnd inputs gates output =>
      exact circuitMissingOutputsEndFailure_bounded_exact
        inputs gates output
  | wrongOutputsEnd inputs gates output token suffix
      notOutputsEnd =>
      exact circuitWrongOutputsEndFailure_bounded_exact
        inputs gates output token suffix notOutputsEnd
  | missingInstanceEnd inputs gates output =>
      exact circuitMissingInstanceEndFailure_bounded_exact
        inputs gates output
  | wrongInstanceEnd inputs gates output token suffix
      notInstanceEnd =>
      exact circuitWrongInstanceEndFailure_bounded_exact
        inputs gates output token suffix notInstanceEnd
  | trailingToken inputs gates output token suffix =>
      exact circuitTrailingTokenFailure_bounded_exact
        inputs gates output token suffix

private theorem tokenMalformedExplicitFailure_bounded_exact
    (basePrefix parsedPrefix : List WorkSymbol)
    (token : Token) (suffix : List Token)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (initial : WorkConfiguration) (launchSteps : Nat)
    (launchBound : launchSteps ≤ 2)
    (prefixSafe : SafeSourceWord basePrefix)
    (shape :
      basePrefix ++
          (SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail) =
        parsedPrefix ++ current :: rest)
    (launch :
      workRunExact? machine launchSteps initial =
        some
          (cleanupSeekConfiguration
            [] (current :: pushCrossed parsedPrefix []) rest)) :
    BoundedRejectingExecution initial
      (16 *
        (basePrefix.length +
          (SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail).length + 1)) := by
  have boundedRun :=
    safeExplicitFailure_bounded_exact
      (basePrefix ++
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail))
      parsedPrefix current rest initial launchSteps shape
      (safe_append prefixSafe
        (safe_append
          (packedTokenCells_safe (token :: suffix))
          (malformedWorkTail_safe malformed)))
      launch
  apply BoundedRejectingExecution.widen boundedRun
  simp only [List.length_append]
  omega

private theorem natTokenFailureWithMalformedTail_bounded_exact
    (reader : NatReader) (parsedPrefix : List WorkSymbol)
    {tokens : List Token}
    (failure : SourceParser.NatTokenFailure tokens)
    (prefixSafe : SafeSourceWord parsedPrefix)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (guardedConfig reader.state parsedPrefix
        (SourceParser.packedTokenCells tokens ++ workTail))
      (32 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells tokens ++
            workTail).length + 1)) := by
  cases failure with
  | missingEnd units =>
      let parsed := parsedPrefix ++ unaryUnitCells units
      have unitsRun :=
        natReaderUnits_exact reader units
          (pushCrossed parsedPrefix [leftGuard]) workTail
      have prefixRun :
          workRunExact? machine (2 * units)
              (guardedConfig reader.state parsedPrefix
                (unaryUnitCells units ++ workTail)) =
            some
              (guardedConfig reader.state parsed workTail) := by
        unfold guardedConfig
        simpa [parsed, pushCrossed_append] using unitsRun
      have parsedSafe :
          SafeSourceWord parsed :=
        safe_append prefixSafe (unaryUnitCells_safe units)
      have tail :=
        simpleMalformedBoundary_bounded_exact
          (.nat reader) parsed parsedSafe malformed
      have joined :=
        BoundedRejectingExecution.prepend
          (2 * units)
          (16 * (parsed.length + workTail.length + 1))
          _ _ (by
            simpa [packedTokenCells_replicate_unit]
              using prefixRun)
          (by
            simpa [SimpleMalformedBoundary.state]
              using tail)
      have normalized :
          BoundedRejectingExecution
            (guardedConfig reader.state parsedPrefix
              (SourceParser.packedTokenCells
                  (List.replicate units Token.unit) ++
                workTail))
            (2 * units +
              16 * (parsed.length + workTail.length + 1)) := by
        simpa [packedTokenCells_replicate_unit] using joined
      apply BoundedRejectingExecution.widen normalized
      rw [packedTokenCells_replicate_unit]
      dsimp [parsed]
      simp only [List.length_append]
      rw [unaryUnitCells_length_bounded]
      omega
  | wrongToken units token suffix notUnit notNatEnd =>
      let tokens :=
        List.replicate units Token.unit ++ token :: suffix
      let parsed := parsedPrefix ++ unaryUnitCells units
      let suffixCells :=
        SourceParser.packedTokenCells suffix ++ workTail
      let initial :=
        guardedConfig reader.state parsedPrefix
          (SourceParser.packedTokenCells tokens ++ workTail)
      have wordShape :
          SourceParser.packedTokenCells tokens ++ workTail =
            unaryUnitCells units ++
              SourceParser.tokenCells token ++ suffixCells := by
        dsimp [tokens, suffixCells]
        rw [packedTokenCells_append,
          packedTokenCells_replicate_unit]
        simp [SourceParser.packedTokenCells, List.append_assoc]
      have unitsRun :=
        natReaderUnits_exact reader units
          (pushCrossed parsedPrefix [leftGuard])
          (SourceParser.tokenCells token ++ suffixCells)
      have prefixRun :
          workRunExact? machine (2 * units) initial =
            some
              (guardedConfig reader.state parsed
                (SourceParser.tokenCells token ++
                  suffixCells)) := by
        unfold initial guardedConfig
        rw [wordShape]
        simpa [parsed, pushCrossed_append] using unitsRun
      have allWordSafe :
          SafeSourceWord
            (parsedPrefix ++
              (SourceParser.packedTokenCells tokens ++
                workTail)) := by
        apply safe_append prefixSafe
        exact
          safe_append
            (packedTokenCells_safe tokens)
            (malformedWorkTail_safe malformed)
      have widen
          (launchSteps : Nat)
          (result :
            BoundedRejectingExecution initial
              (launchSteps +
                2 *
                  (parsedPrefix ++
                    (SourceParser.packedTokenCells tokens ++
                      workTail)).length +
                2))
          (launchBound : launchSteps ≤ 2 * units + 2) :
          BoundedRejectingExecution initial
            (32 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells tokens ++
                  workTail).length + 1)) := by
        apply BoundedRejectingExecution.widen result
        have tokenLength :
            (SourceParser.tokenCells token).length = 2 :=
          SourceParser.tokenCells_length token
        have shapeLength := congrArg List.length wordShape
        simp only [List.length_append, tokenLength] at shapeLength
        rw [unaryUnitCells_length_bounded] at shapeLength
        simp only [List.length_append]
        omega
      have rejectFirst
          (current next : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [current, next])
          (wrong : current ≠ cell00) :
          BoundedRejectingExecution initial
            (32 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells tokens ++
                  workTail).length + 1)) := by
        have failed :=
          natReaderFirstFailure_exact reader parsed
            current (next :: suffixCells) wrong
        have launch :=
          exactRun_add (2 * units) 1
            _ _ _ prefixRun
            (by simpa [cellsEq] using failed)
        have shape :
            parsedPrefix ++
                (SourceParser.packedTokenCells tokens ++
                  workTail) =
              parsed ++ current :: next :: suffixCells := by
          rw [wordShape, cellsEq]
          simp [parsed, List.append_assoc]
        apply widen (2 * units + 1)
        · exact
            safeExplicitFailure_bounded_exact
              (parsedPrefix ++
                (SourceParser.packedTokenCells tokens ++
                  workTail))
              parsed current (next :: suffixCells)
              initial (2 * units + 1)
              shape allWordSafe launch
        · omega
      have rejectSecond
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell00, current])
          (notUnitCell : current ≠ cell01)
          (notEndCell : current ≠ cell10) :
          BoundedRejectingExecution initial
            (32 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells tokens ++
                  workTail).length + 1)) := by
        have failed :=
          natReaderSecondFailure_exact reader parsed current
            suffixCells notUnitCell notEndCell
        have launch :=
          exactRun_add (2 * units) 2
            _ _ _ prefixRun
            (by simpa [cellsEq] using failed)
        have shape :
            parsedPrefix ++
                (SourceParser.packedTokenCells tokens ++
                  workTail) =
              (parsed ++ [cell00]) ++
                current :: suffixCells := by
          rw [wordShape, cellsEq]
          simp [parsed, List.append_assoc]
        apply widen (2 * units + 2)
        · exact
            safeExplicitFailure_bounded_exact
              (parsedPrefix ++
                (SourceParser.packedTokenCells tokens ++
                  workTail))
              (parsed ++ [cell00]) current suffixCells
              initial (2 * units + 2)
              shape allWordSafe launch
        · omega
      cases token with
      | version0 =>
          exact rejectSecond cell00 rfl (by decide) (by decide)
      | unit =>
          exact False.elim (notUnit rfl)
      | natEnd =>
          exact False.elim (notNatEnd rfl)
      | input =>
          exact rejectSecond cell11 rfl (by decide) (by decide)
      | constantFalse =>
          exact rejectFirst cell01 cell00 rfl (by decide)
      | constantTrue =>
          exact rejectFirst cell01 cell01 rfl (by decide)
      | gate =>
          exact rejectFirst cell01 cell10 rfl (by decide)
      | gateEnd =>
          exact rejectFirst cell01 cell11 rfl (by decide)
      | programEnd =>
          exact rejectFirst cell10 cell00 rfl (by decide)
      | outputsEnd =>
          exact rejectFirst cell10 cell01 rfl (by decide)
      | threshold =>
          exact rejectFirst cell10 cell10 rfl (by decide)
      | instanceEnd =>
          exact rejectFirst cell10 cell11 rfl (by decide)

private theorem sourceTokenFailureWithMalformedTail_bounded_exact
    (continuation : SourceContinuation)
    (parsedPrefix : List WorkSymbol)
    {tokens : List Token}
    (failure : SourceParser.SourceTokenFailure tokens)
    (prefixSafe : SafeSourceWord parsedPrefix)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (guardedConfig (State.sourceStart continuation)
        parsedPrefix
        (SourceParser.packedTokenCells tokens ++ workTail))
      (64 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells tokens ++
            workTail).length + 1)) := by
  cases failure with
  | missing =>
      apply BoundedRejectingExecution.widen
        (simpleMalformedBoundary_bounded_exact
          (.source continuation) parsedPrefix
          prefixSafe malformed)
      simp [SourceParser.packedTokenCells]
      omega
  | wrongHead token suffix notInput notFalse notTrue notGate =>
      let suffixCells :=
        SourceParser.packedTokenCells suffix ++ workTail
      let initial :=
        guardedConfig (State.sourceStart continuation)
          parsedPrefix
          (SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail)
      have widenToken
          (result :
            BoundedRejectingExecution initial
              (16 *
                (parsedPrefix.length +
                  (SourceParser.packedTokenCells
                      (token :: suffix) ++
                    workTail).length + 1))) :
          BoundedRejectingExecution initial
            (64 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells
                    (token :: suffix) ++
                  workTail).length + 1)) := by
        apply BoundedRejectingExecution.widen result
        omega
      have rejectFirst
          (current next : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [current, next])
          (not00 : current ≠ cell00)
          (not01 : current ≠ cell01) :
          BoundedRejectingExecution initial
            (64 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells
                    (token :: suffix) ++
                  workTail).length + 1)) := by
        have failed :=
          sourceStartFirstFailure_exact continuation parsedPrefix
            current (next :: suffixCells) not00 not01
        apply widenToken
        apply tokenMalformedExplicitFailure_bounded_exact
          parsedPrefix parsedPrefix token suffix malformed
          current (next :: suffixCells) initial 1
          (by omega) prefixSafe
        · simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells]
        · simpa [initial,
            SourceParser.packedTokenCells,
            cellsEq, suffixCells,
            List.append_assoc] using failed
      have rejectAfter00
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell00, current])
          (not11 : current ≠ cell11) :
          BoundedRejectingExecution initial
            (64 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells
                    (token :: suffix) ++
                  workTail).length + 1)) := by
        have failed :=
          sourceAfter00Failure_exact continuation parsedPrefix
            current suffixCells not11
        apply widenToken
        apply tokenMalformedExplicitFailure_bounded_exact
          parsedPrefix (parsedPrefix ++ [cell00])
          token suffix malformed current suffixCells
          initial 2 (by omega) prefixSafe
        · simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells, List.append_assoc]
        · simpa [initial,
            SourceParser.packedTokenCells,
            cellsEq, suffixCells,
            List.append_assoc] using failed
      have rejectAfter01
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token = [cell01, current])
          (not00 : current ≠ cell00)
          (not01 : current ≠ cell01)
          (not10 : current ≠ cell10) :
          BoundedRejectingExecution initial
            (64 *
              (parsedPrefix.length +
                (SourceParser.packedTokenCells
                    (token :: suffix) ++
                  workTail).length + 1)) := by
        have failed :=
          sourceAfter01Failure_exact continuation parsedPrefix
            current suffixCells not00 not01 not10
        apply widenToken
        apply tokenMalformedExplicitFailure_bounded_exact
          parsedPrefix (parsedPrefix ++ [cell01])
          token suffix malformed current suffixCells
          initial 2 (by omega) prefixSafe
        · simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells, List.append_assoc]
        · simpa [initial,
            SourceParser.packedTokenCells,
            cellsEq, suffixCells,
            List.append_assoc] using failed
      cases token with
      | version0 =>
          exact rejectAfter00 cell00 rfl (by decide)
      | unit =>
          exact rejectAfter00 cell01 rfl (by decide)
      | natEnd =>
          exact rejectAfter00 cell10 rfl (by decide)
      | input =>
          exact False.elim (notInput rfl)
      | constantFalse =>
          exact False.elim (notFalse rfl)
      | constantTrue =>
          exact False.elim (notTrue rfl)
      | gate =>
          exact False.elim (notGate rfl)
      | gateEnd =>
          exact rejectAfter01 cell11 rfl
            (by decide) (by decide) (by decide)
      | programEnd =>
          exact rejectFirst cell10 cell00 rfl
            (by decide) (by decide)
      | outputsEnd =>
          exact rejectFirst cell10 cell01 rfl
            (by decide) (by decide)
      | threshold =>
          exact rejectFirst cell10 cell10 rfl
            (by decide) (by decide)
      | instanceEnd =>
          exact rejectFirst cell10 cell11 rfl
            (by decide) (by decide)
  | @inputIndex indexTokens indexFailure =>
      let nextPrefix := parsedPrefix ++ [cell00, cell11]
      have launch :
          workRunExact? machine 2
              (guardedConfig (State.sourceStart continuation)
                parsedPrefix
                (cell00 :: cell11 ::
                  (SourceParser.packedTokenCells indexTokens ++
                    workTail))) =
            some
              (guardedConfig
                (State.sourceNatFirst continuation)
                nextPrefix
                (SourceParser.packedTokenCells indexTokens ++
                  workTail)) := by
        unfold guardedConfig
        simp [nextPrefix, pushCrossed_append, pushCrossed]
        set_option maxRecDepth 100000 in
          cases continuation <;> rfl
      have nextSafe :
          SafeSourceWord nextPrefix := by
        apply safe_append prefixSafe
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · decide
        · decide
        · contradiction
      have tail :=
        natTokenFailureWithMalformedTail_bounded_exact
          (.source continuation) nextPrefix
          indexFailure nextSafe malformed
      have joined :=
        BoundedRejectingExecution.prepend
          2
          (32 *
            (nextPrefix.length +
              (SourceParser.packedTokenCells indexTokens ++
                workTail).length + 1))
          _ _ (by
            simpa [SourceParser.packedTokenCells,
              SourceParser.tokenCells, NatReader.state,
              cell00, cell11, SourceParser.cell00,
              SourceParser.cell11,
              List.append_assoc] using launch)
          tail
      apply BoundedRejectingExecution.widen joined
      simp only [nextPrefix, List.length_append,
        List.length_cons, List.length_nil,
        SourceParser.packedTokenCells,
        SourceParser.tokenCells_length]
      omega
  | @gateIndex indexTokens indexFailure =>
      let nextPrefix := parsedPrefix ++ [cell01, cell10]
      have launch :
          workRunExact? machine 2
              (guardedConfig (State.sourceStart continuation)
                parsedPrefix
                (cell01 :: cell10 ::
                  (SourceParser.packedTokenCells indexTokens ++
                    workTail))) =
            some
              (guardedConfig
                (State.sourceNatFirst continuation)
                nextPrefix
                (SourceParser.packedTokenCells indexTokens ++
                  workTail)) := by
        unfold guardedConfig
        simp [nextPrefix, pushCrossed_append, pushCrossed]
        set_option maxRecDepth 100000 in
          cases continuation <;> rfl
      have nextSafe :
          SafeSourceWord nextPrefix := by
        apply safe_append prefixSafe
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with rfl | rfl | impossible
        · decide
        · decide
        · contradiction
      have tail :=
        natTokenFailureWithMalformedTail_bounded_exact
          (.source continuation) nextPrefix
          indexFailure nextSafe malformed
      have joined :=
        BoundedRejectingExecution.prepend
          2
          (32 *
            (nextPrefix.length +
              (SourceParser.packedTokenCells indexTokens ++
                workTail).length + 1))
          _ _ (by
            simpa [SourceParser.packedTokenCells,
              SourceParser.tokenCells, NatReader.state,
              cell01, cell10, SourceParser.cell01,
              SourceParser.cell10,
              List.append_assoc] using launch)
          tail
      apply BoundedRejectingExecution.widen joined
      simp only [nextPrefix, List.length_append,
        List.length_cons, List.length_nil,
        SourceParser.packedTokenCells,
        SourceParser.tokenCells_length]
      omega

private theorem gateDecrementExhaustedWord_bounded_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate)
    (word : List WorkSymbol)
    (wordSafe : SafeSourceWord word) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart
        (gatePrefix inputs done [])
        (firstSourceCell firstWas01 :: word))
      (256 *
        ((gatePrefix inputs done []).length +
          (firstSourceCell firstWas01 :: word).length + 1)) := by
  let logicalPrefix := gatePrefix inputs done []
  have launch :=
    gateStartLaunchWord_exact firstWas01 logicalPrefix word
  have backward :=
    gateDecrementSeekGuard_scan_exact firstWas01 logicalPrefix
      (cursorMark :: word)
      (gatePrefix_ordinary inputs done [])
  have guard :=
    gateDecrementGuard_exact firstWas01
      (logicalPrefix ++ cursorMark :: word)
  have throughBackward :=
    exactRun_add 1 logicalPrefix.length
      _ _ _ launch backward
  have throughGuard :=
    exactRun_add (1 + logicalPrefix.length) 1
      _ _ _ throughBackward guard
  have tail :=
    gateDecrementExhaustedForwardWord_bounded_exact
      firstWas01 inputs done word wordSafe
  have joined :=
    BoundedRejectingExecution.prepend
      ((1 + logicalPrefix.length) + 1)
      (128 *
        ((gatePrefix inputs done []).length +
          word.length + 1))
      _ _
      (by simpa [logicalPrefix] using throughGuard)
      tail
  apply BoundedRejectingExecution.widen joined
  dsimp [logicalPrefix]
  omega

private theorem gateMalformedFirstEOF_bounded_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (count : Nat) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done count)
        [firstSourceCell firstWas01])
      (512 *
        ((failureGatePrefix inputs done count).length + 2)) := by
  cases count with
  | zero =>
      have base :=
        gateDecrementExhaustedWord_bounded_exact
          firstWas01 inputs done []
          (by
            intro symbol member
            contradiction)
      apply BoundedRejectingExecution.widen
        (by
          simpa [failureGatePrefix,
            placeholderGates] using base)
      have prefixEq :
          failureGatePrefix inputs done 0 =
            gatePrefix inputs done [] := by
        simp [failureGatePrefix, placeholderGates]
      rw [prefixEq]
      omega
  | succ remaining =>
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates remaining) ++
          [firstSourceCell firstWas01]
      have prefixRun :=
        gateFirstWord_exact
          firstWas01 inputs done remaining []
      have parsedSafe :
          SafeSourceWord parsedPrefix :=
        gateFirstParsedPrefix_safe
          firstWas01 inputs done remaining
      have tail :=
        missingExpected_bounded_exact
          (afterFirstSourceState firstWas01 .gateLeft)
          parsedPrefix parsedSafe
          (sourceAfterFirstMissingFailure_exact
            firstWas01 parsedPrefix)
      have joined :=
        BoundedRejectingExecution.prepend
          (gateFirstSteps inputs done remaining)
          (8 * (parsedPrefix.length + 1))
          _ _
          (by simpa [parsedPrefix] using prefixRun)
          tail
      apply BoundedRejectingExecution.widen joined
      have firstBound :=
        gateFirstSteps_le_span
          inputs done remaining []
      have prefixLength :=
        gateParsingPrefix_failurePrefix_length
          inputs done remaining
      dsimp [parsedPrefix] at firstBound ⊢
      simp only [List.length_append, List.length_cons,
        List.length_nil] at firstBound prefixLength ⊢
      omega

private theorem gateMalformedFirstDangling_bounded_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (count : Nat)
    (bit : Bool) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done count)
        [firstSourceCell firstWas01,
          SourceParser.danglingWorkCell bit])
      (512 *
        ((failureGatePrefix inputs done count).length + 3)) := by
  have danglingSafe :
      SafeSourceWord
        [SourceParser.danglingWorkCell bit] := by
    intro symbol member
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at member
    subst symbol
    cases bit <;> decide
  cases count with
  | zero =>
      have base :=
        gateDecrementExhaustedWord_bounded_exact
          firstWas01 inputs done
          [SourceParser.danglingWorkCell bit]
          danglingSafe
      apply BoundedRejectingExecution.widen
        (by
          simpa [failureGatePrefix,
            placeholderGates] using base)
      have prefixEq :
          failureGatePrefix inputs done 0 =
            gatePrefix inputs done [] := by
        simp [failureGatePrefix, placeholderGates]
      rw [prefixEq]
      omega
  | succ remaining =>
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates remaining) ++
          [firstSourceCell firstWas01]
      have prefixRun :=
        gateFirstWord_exact
          firstWas01 inputs done remaining
          [SourceParser.danglingWorkCell bit]
      have parsedSafe :
          SafeSourceWord parsedPrefix :=
        gateFirstParsedPrefix_safe
          firstWas01 inputs done remaining
      have tail :
          BoundedRejectingExecution
            (guardedConfig
              (afterFirstSourceState firstWas01 .gateLeft)
              parsedPrefix
              [SourceParser.danglingWorkCell bit])
            (8 * (parsedPrefix.length + 2)) := by
        cases firstWas01
        · simpa [afterFirstSourceState] using
            sourceAfter00_bounded_exact
              parsedPrefix parsedSafe
              (SourceParser.danglingWorkCell bit) []
              danglingSafe
              (by cases bit <;> decide)
        · simpa [afterFirstSourceState] using
            sourceAfter01_bounded_exact
              parsedPrefix parsedSafe
              (SourceParser.danglingWorkCell bit) []
              danglingSafe
              (by cases bit <;> decide)
              (by cases bit <;> decide)
              (by cases bit <;> decide)
      have joined :=
        BoundedRejectingExecution.prepend
          (gateFirstSteps inputs done remaining)
          (8 * (parsedPrefix.length + 2))
          _ _
          (by simpa [parsedPrefix] using prefixRun)
          tail
      apply BoundedRejectingExecution.widen joined
      have firstBound :=
        gateFirstSteps_le_span
          inputs done remaining
          [SourceParser.danglingWorkCell bit]
      have prefixLength :=
        gateParsingPrefix_failurePrefix_length
          inputs done remaining
      dsimp [parsedPrefix] at firstBound ⊢
      simp only [List.length_append, List.length_cons,
        List.length_nil] at firstBound prefixLength ⊢
      omega

private theorem gateMalformedTail_bounded_exact
    (inputs : Nat) (done : List RawGate)
    (count : Nat)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done count)
        workTail)
      (512 *
        ((failureGatePrefix inputs done count).length +
          workTail.length + 1)) := by
  let parsedPrefix := failureGatePrefix inputs done count
  have parsedSafe : SafeSourceWord parsedPrefix :=
    failureGatePrefix_safe inputs done count
  cases malformed with
  | reserved third fourth suffix =>
      let rest :=
        SourceParser.boolPairWorkCell third fourth ::
          SourceParser.packedRawBits suffix
      let word := cell11 :: rest
      have launch :
          BoundaryCleanupLaunch State.gateStart
            parsedPrefix word := by
        apply boundaryCleanupLaunch_immediate
        exact gateStartCell11Failure_exact
          parsedPrefix rest
      apply BoundedRejectingExecution.widen
        (boundaryCleanupLaunch_bounded_exact
          State.gateStart parsedPrefix word
          parsedSafe
          (malformedWorkTail_safe
            (SourceParser.MalformedWorkTail.reserved
              third fourth suffix))
          launch)
      dsimp [parsedPrefix, word, rest]
      omega
  | trailingOne bit =>
      let word := [SourceParser.danglingWorkCell bit]
      have launch :
          BoundaryCleanupLaunch State.gateStart
            parsedPrefix word := by
        apply boundaryCleanupLaunch_immediate
        exact gateStartDanglingFailure_exact
          parsedPrefix bit
      apply BoundedRejectingExecution.widen
        (boundaryCleanupLaunch_bounded_exact
          State.gateStart parsedPrefix word
          parsedSafe
          (malformedWorkTail_safe
            (SourceParser.MalformedWorkTail.trailingOne bit))
          launch)
      dsimp [parsedPrefix, word]
      omega
  | trailingTwo first second =>
      cases first <;> cases second
      · exact gateMalformedFirstEOF_bounded_exact
          false inputs done count
      · exact gateMalformedFirstEOF_bounded_exact
          true inputs done count
      · let word := [cell10]
        have launch :
            BoundaryCleanupLaunch State.gateStart
              parsedPrefix word := by
          apply boundaryCleanupLaunch_eof_rewritten
            (stored := cursorMark)
          · intro symbol member
            simp only [List.mem_cons,
              List.not_mem_nil, or_false] at member
            subst symbol
            decide
          · exact gateStartProgramEOFFailure_exact
              parsedPrefix
        apply BoundedRejectingExecution.widen
          (boundaryCleanupLaunch_bounded_exact
            State.gateStart parsedPrefix word
            parsedSafe
            (malformedWorkTail_safe
              (SourceParser.MalformedWorkTail.trailingTwo
                true false))
            launch)
        dsimp [parsedPrefix, word]
        omega
      · let word := [cell11]
        have launch :
            BoundaryCleanupLaunch State.gateStart
              parsedPrefix word := by
          apply boundaryCleanupLaunch_immediate
          exact gateStartCell11Failure_exact
            parsedPrefix []
        apply BoundedRejectingExecution.widen
          (boundaryCleanupLaunch_bounded_exact
            State.gateStart parsedPrefix word
            parsedSafe
            (malformedWorkTail_safe
              (SourceParser.MalformedWorkTail.trailingTwo
                true true))
            launch)
        dsimp [parsedPrefix, word]
        omega
  | trailingThree first second third =>
      cases first <;> cases second
      · exact gateMalformedFirstDangling_bounded_exact
          false inputs done count third
      · exact gateMalformedFirstDangling_bounded_exact
          true inputs done count third
      · have danglingSafe :
            SafeSourceWord
              [SourceParser.danglingWorkCell third] := by
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil, or_false] at member
          subst symbol
          cases third <;> decide
        apply BoundedRejectingExecution.widen
          (programEndSecond_bounded_exact
            parsedPrefix parsedSafe
            (SourceParser.danglingWorkCell third) []
            danglingSafe
            (by cases third <;> decide))
        dsimp [parsedPrefix]
        omega
      · let word :=
          [cell11, SourceParser.danglingWorkCell third]
        have launch :
            BoundaryCleanupLaunch State.gateStart
              parsedPrefix word := by
          apply boundaryCleanupLaunch_immediate
          exact gateStartCell11Failure_exact
            parsedPrefix
              [SourceParser.danglingWorkCell third]
        apply BoundedRejectingExecution.widen
          (boundaryCleanupLaunch_bounded_exact
            State.gateStart parsedPrefix word
            parsedSafe
            (malformedWorkTail_safe
              (SourceParser.MalformedWorkTail.trailingThree
                true true third))
            launch)
        dsimp [parsedPrefix, word]
        omega

private theorem gateEndWrongTokenWithMalformedTail_bounded_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token)
    (notGateEnd : token ≠ .gateEnd)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (guardedConfig State.gateEndFirst parsedPrefix
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail))
      (32 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail).length + 1)) := by
  let suffixCells :=
    SourceParser.packedTokenCells suffix ++ workTail
  let initial :=
    guardedConfig State.gateEndFirst parsedPrefix
      (SourceParser.packedTokenCells
          (token :: suffix) ++
        workTail)
  have packedSafe :
      SafeSourceWord
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail) :=
    safe_append
      (packedTokenCells_safe (token :: suffix))
      (malformedWorkTail_safe malformed)
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not01 : current ≠ cell01) :
      BoundedRejectingExecution initial
        (32 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail).length + 1)) := by
    have launch :=
      gateEndFirstFailure_exact parsedPrefix current
        (next :: suffixCells) not01
    apply BoundedRejectingExecution.widen
      (tokenMalformedExplicitFailure_bounded_exact
        parsedPrefix parsedPrefix token suffix malformed
        current (next :: suffixCells) initial 1
        (by omega) prefixSafe
        (by
          simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells])
        (by
          simpa [initial,
            SourceParser.packedTokenCells,
            cellsEq, suffixCells,
            List.append_assoc] using launch))
    omega
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell01, current])
      (not11 : current ≠ cell11) :
      BoundedRejectingExecution initial
        (32 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail).length + 1)) := by
    let parsedAfterMark := parsedPrefix ++ [gateMark]
    have launch :=
      gateEndSecondFailure_exact parsedPrefix current
        suffixCells not11
    have markerSafe : SafeSourceWord [gateMark] :=
      safe_singleton_gateMark
    have tailSafe :
        SafeSourceWord (current :: suffixCells) := by
      intro symbol member
      apply packedSafe symbol
      have targetMember :
          symbol ∈
            SourceParser.tokenCells token ++ suffixCells := by
        rw [cellsEq]
        simp only [List.mem_cons] at member
        rcases member with currentEq | member
        · subst symbol
          exact List.mem_append_left suffixCells (by simp)
        · exact List.mem_append_right
            [cell01, current] member
      simpa [SourceParser.packedTokenCells,
        suffixCells, List.append_assoc] using targetMember
    have boundedRun :=
      safeExplicitFailure_bounded_exact
        (parsedAfterMark ++ current :: suffixCells)
        parsedAfterMark current suffixCells initial 2
        rfl
        (safe_append
          (safe_append prefixSafe markerSafe)
          tailSafe)
        (by
          simpa [initial, parsedAfterMark,
            SourceParser.packedTokenCells, cellsEq,
            suffixCells, List.append_assoc] using launch)
    apply BoundedRejectingExecution.widen boundedRun
    have tokenLength :=
      SourceParser.tokenCells_length token
    dsimp [parsedAfterMark, suffixCells]
    simp only [List.length_append, List.length_cons,
      List.length_nil, SourceParser.packedTokenCells,
      tokenLength]
    omega
  cases token with
  | version0 =>
      exact rejectFirst cell00 cell00 rfl (by decide)
  | unit =>
      exact rejectFirst cell00 cell01 rfl (by decide)
  | natEnd =>
      exact rejectFirst cell00 cell10 rfl (by decide)
  | input =>
      exact rejectFirst cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact rejectSecond cell00 rfl (by decide)
  | constantTrue =>
      exact rejectSecond cell01 rfl (by decide)
  | gate =>
      exact rejectSecond cell10 rfl (by decide)
  | gateEnd =>
      exact False.elim (notGateEnd rfl)
  | programEnd =>
      exact rejectFirst cell10 cell00 rfl (by decide)
  | outputsEnd =>
      exact rejectFirst cell10 cell01 rfl (by decide)
  | threshold =>
      exact rejectFirst cell10 cell10 rfl (by decide)
  | instanceEnd =>
      exact rejectFirst cell10 cell11 rfl (by decide)

private theorem gateLeftTokenFailureWithMalformedTail_bounded_exact
    (inputs : Nat) (done : List RawGate)
    {remaining : Nat} {tokens : List Token}
    (failure : SourceParser.SourceTokenFailure tokens)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done (remaining + 1))
        (SourceParser.packedTokenCells tokens ++ workTail))
      (1024 *
        ((failureGatePrefix inputs done
            (remaining + 1)).length +
          (SourceParser.packedTokenCells tokens ++
            workTail).length + 1)) := by
  let parsingPrefix :=
    gateParsingPrefix inputs done
      (placeholderGates remaining)
  have startPrefixSafe :
      SafeSourceWord
        (failureGatePrefix inputs done (remaining + 1)) :=
    failureGatePrefix_safe inputs done (remaining + 1)
  have firstPrefixSafe
      (first : WorkSymbol)
      (firstOrdinary : ordinaryCell first) :
      SafeSourceWord (parsingPrefix ++ [first]) := by
    apply safe_of_ordinary
    apply ordinary_append
      (gateParsingPrefix_ordinary inputs done
        (placeholderGates remaining))
    intro symbol member
    simp only [List.mem_cons,
      List.not_mem_nil] at member
    rcases member with rfl | impossible
    · exact firstOrdinary
    · contradiction
  cases failure with
  | missing =>
      have base :=
        gateMalformedTail_bounded_exact
          inputs done (remaining + 1) malformed
      apply BoundedRejectingExecution.widen
        (by
          simpa [SourceParser.packedTokenCells] using base)
      simp [SourceParser.packedTokenCells]
      omega
  | wrongHead token suffix notInput notFalse notTrue notGate =>
      let suffixCells :=
        SourceParser.packedTokenCells suffix ++ workTail
      let initial :=
        guardedConfig State.gateStart
          (failureGatePrefix inputs done (remaining + 1))
          (SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail)
      have packedSafe :
          SafeSourceWord
            (SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail) :=
        safe_append
          (packedTokenCells_safe (token :: suffix))
          (malformedWorkTail_safe malformed)
      have tailSafe
          (first current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token =
              [first, current]) :
          SafeSourceWord (current :: suffixCells) := by
        intro symbol member
        apply packedSafe symbol
        have targetMember :
            symbol ∈
              SourceParser.tokenCells token ++ suffixCells := by
          rw [cellsEq]
          simp only [List.mem_cons] at member
          rcases member with currentEq | member
          · subst symbol
            exact List.mem_append_left suffixCells
              (by simp)
          · exact List.mem_append_right
              [first, current] member
        simpa [SourceParser.packedTokenCells,
          suffixCells, List.append_assoc] using targetMember
      have widen
          {bound : Nat}
          (result : BoundedRejectingExecution initial bound)
          (linear :
            bound ≤
              1024 *
                ((failureGatePrefix inputs done
                    (remaining + 1)).length +
                  (SourceParser.packedTokenCells
                      (token :: suffix) ++
                    workTail).length + 1)) :
          BoundedRejectingExecution initial
            (1024 *
              ((failureGatePrefix inputs done
                  (remaining + 1)).length +
                (SourceParser.packedTokenCells
                    (token :: suffix) ++
                  workTail).length + 1)) :=
        BoundedRejectingExecution.widen result linear
      have after00
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token =
              [cell00, current])
          (not11 : current ≠ cell11) :
          BoundedRejectingExecution initial
            (1024 *
              ((failureGatePrefix inputs done
                  (remaining + 1)).length +
                (SourceParser.packedTokenCells
                    (token :: suffix) ++
                  workTail).length + 1)) := by
        have firstRun :=
          gateFirst_exact false inputs done remaining
            current suffixCells
        have firstCanonical :
            workRunExact? machine
                (gateFirstSteps inputs done remaining)
                initial =
              some
                (guardedConfig
                  (State.sourceAfter00 .gateLeft)
                  (parsingPrefix ++ [cell00])
                  (current :: suffixCells)) := by
          simpa [initial, parsingPrefix,
            SourceParser.packedTokenCells, cellsEq,
            suffixCells, firstSourceCell,
            afterFirstSourceState,
            List.append_assoc] using firstRun
        have tail :=
          sourceAfter00_bounded_exact
            (parsingPrefix ++ [cell00])
            (firstPrefixSafe cell00 cell00_ordinary)
            current suffixCells
            (tailSafe cell00 current cellsEq) not11
        have joined :=
          BoundedRejectingExecution.prepend
            (gateFirstSteps inputs done remaining)
            (8 *
              ((parsingPrefix ++ [cell00]).length +
                (current :: suffixCells).length + 1))
            initial _ firstCanonical tail
        apply widen joined
        have firstBound :=
          gateFirstSteps_le_span
            inputs done remaining
            (current :: suffixCells)
        have prefixLength :=
          gateParsingPrefix_failurePrefix_length
            inputs done remaining
        have tokenLength :=
          SourceParser.tokenCells_length token
        simp only [parsingPrefix, List.length_append,
          List.length_cons, List.length_nil,
          SourceParser.packedTokenCells,
          tokenLength] at firstBound prefixLength ⊢
        dsimp [suffixCells] at firstBound ⊢
        simp only [List.length_append] at firstBound ⊢
        omega
      have after01
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token =
              [cell01, current])
          (not00 : current ≠ cell00)
          (not01 : current ≠ cell01)
          (not10 : current ≠ cell10) :
          BoundedRejectingExecution initial
            (1024 *
              ((failureGatePrefix inputs done
                  (remaining + 1)).length +
                (SourceParser.packedTokenCells
                    (token :: suffix) ++
                  workTail).length + 1)) := by
        have firstRun :=
          gateFirst_exact true inputs done remaining
            current suffixCells
        have firstCanonical :
            workRunExact? machine
                (gateFirstSteps inputs done remaining)
                initial =
              some
                (guardedConfig
                  (State.sourceAfter01 .gateLeft)
                  (parsingPrefix ++ [cell01])
                  (current :: suffixCells)) := by
          simpa [initial, parsingPrefix,
            SourceParser.packedTokenCells, cellsEq,
            suffixCells, firstSourceCell,
            afterFirstSourceState,
            List.append_assoc] using firstRun
        have tail :=
          sourceAfter01_bounded_exact
            (parsingPrefix ++ [cell01])
            (firstPrefixSafe cell01 cell01_ordinary)
            current suffixCells
            (tailSafe cell01 current cellsEq)
            not00 not01 not10
        have joined :=
          BoundedRejectingExecution.prepend
            (gateFirstSteps inputs done remaining)
            (8 *
              ((parsingPrefix ++ [cell01]).length +
                (current :: suffixCells).length + 1))
            initial _ firstCanonical tail
        apply widen joined
        have firstBound :=
          gateFirstSteps_le_span
            inputs done remaining
            (current :: suffixCells)
        have prefixLength :=
          gateParsingPrefix_failurePrefix_length
            inputs done remaining
        have tokenLength :=
          SourceParser.tokenCells_length token
        simp only [parsingPrefix, List.length_append,
          List.length_cons, List.length_nil,
          SourceParser.packedTokenCells,
          tokenLength] at firstBound prefixLength ⊢
        dsimp [suffixCells] at firstBound ⊢
        simp only [List.length_append] at firstBound ⊢
        omega
      have badProgramSecond
          (current : WorkSymbol)
          (cellsEq :
            SourceParser.tokenCells token =
              [cell10, current])
          (not00 : current ≠ cell00) :
          BoundedRejectingExecution initial
            (1024 *
              ((failureGatePrefix inputs done
                  (remaining + 1)).length +
                (SourceParser.packedTokenCells
                    (token :: suffix) ++
                  workTail).length + 1)) := by
        have result :=
          programEndSecond_bounded_exact
            (failureGatePrefix inputs done (remaining + 1))
            startPrefixSafe current suffixCells
            (tailSafe cell10 current cellsEq) not00
        apply widen
          (by
            simpa [initial, SourceParser.packedTokenCells,
              cellsEq, suffixCells,
              List.append_assoc] using result)
        have tokenLength :=
          SourceParser.tokenCells_length token
        simp only [SourceParser.packedTokenCells,
          List.length_append, tokenLength]
        omega
      have prematureProgramEnd
          (cellsEq :
            SourceParser.tokenCells token =
              [cell10, cell00]) :
          BoundedRejectingExecution initial
            (1024 *
              ((failureGatePrefix inputs done
                  (remaining + 1)).length +
                (SourceParser.packedTokenCells
                    (token :: suffix) ++
                  workTail).length + 1)) := by
        have result :=
          programCountRemaining_bounded_exact
            inputs done remaining suffixCells
            (safe_append
              (packedTokenCells_safe suffix)
              (malformedWorkTail_safe malformed))
        apply widen
          (by
            simpa [initial, SourceParser.packedTokenCells,
              cellsEq, suffixCells,
              List.append_assoc] using result)
        have tokenLength :=
          SourceParser.tokenCells_length token
        simp only [SourceParser.packedTokenCells,
          List.length_append, tokenLength]
        omega
      cases token with
      | version0 =>
          exact after00 cell00 rfl (by decide)
      | unit =>
          exact after00 cell01 rfl (by decide)
      | natEnd =>
          exact after00 cell10 rfl (by decide)
      | input =>
          exact False.elim (notInput rfl)
      | constantFalse =>
          exact False.elim (notFalse rfl)
      | constantTrue =>
          exact False.elim (notTrue rfl)
      | gate =>
          exact False.elim (notGate rfl)
      | gateEnd =>
          exact after01 cell11 rfl
            (by decide) (by decide) (by decide)
      | programEnd =>
          exact prematureProgramEnd rfl
      | outputsEnd =>
          exact badProgramSecond cell01 rfl (by decide)
      | threshold =>
          exact badProgramSecond cell10 rfl (by decide)
      | instanceEnd =>
          exact badProgramSecond cell11 rfl (by decide)
  | @inputIndex indexTokens indexFailure =>
      let afterFirst := parsingPrefix ++ [cell00]
      let afterHead := afterFirst ++ [cell11]
      let indexWord :=
        SourceParser.packedTokenCells indexTokens ++ workTail
      have firstRun :=
        gateFirst_exact false inputs done remaining
          cell11 indexWord
      have firstCanonical :
          workRunExact? machine
              (gateFirstSteps inputs done remaining)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done (remaining + 1))
                (SourceParser.packedTokenCells
                    (.input :: indexTokens) ++
                  workTail)) =
            some
              (guardedConfig
                (State.sourceAfter00 .gateLeft)
                afterFirst (cell11 :: indexWord)) := by
        simpa [afterFirst, parsingPrefix, indexWord,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          firstSourceCell, afterFirstSourceState,
          cell00, cell11, SourceParser.cell00,
          SourceParser.cell11, List.append_assoc] using firstRun
      have headRun :=
        sourceAfter00NatLaunch_exact afterFirst indexWord
      have afterHeadSafe :
          SafeSourceWord afterHead := by
        apply safe_of_ordinary
        dsimp [afterHead, afterFirst, parsingPrefix]
        apply ordinary_append
        · apply ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates remaining))
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell00_ordinary
          · contradiction
        · intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell11_ordinary
          · contradiction
      have tail :=
        natTokenFailureWithMalformedTail_bounded_exact
          (.source .gateLeft) afterHead
          indexFailure afterHeadSafe malformed
      have throughHead :=
        BoundedRejectingExecution.prepend
          1
          (32 *
            (afterHead.length + indexWord.length + 1))
          _ _ (by
            simpa [afterHead, NatReader.state] using headRun)
          tail
      have joined :=
        BoundedRejectingExecution.prepend
          (gateFirstSteps inputs done remaining)
          (1 +
            32 *
              (afterHead.length + indexWord.length + 1))
          _ _ firstCanonical throughHead
      apply BoundedRejectingExecution.widen joined
      have firstBound :=
        gateFirstSteps_le_span inputs done remaining
          (cell11 :: indexWord)
      have prefixLength :=
        gateParsingPrefix_failurePrefix_length
          inputs done remaining
      dsimp [afterHead, afterFirst, parsingPrefix,
        indexWord] at firstBound ⊢
      simp only [List.length_append, List.length_cons,
        List.length_nil, SourceParser.packedTokenCells,
        SourceParser.tokenCells_length] at firstBound prefixLength ⊢
      omega
  | @gateIndex indexTokens indexFailure =>
      let afterFirst := parsingPrefix ++ [cell01]
      let afterHead := afterFirst ++ [cell10]
      let indexWord :=
        SourceParser.packedTokenCells indexTokens ++ workTail
      have firstRun :=
        gateFirst_exact true inputs done remaining
          cell10 indexWord
      have firstCanonical :
          workRunExact? machine
              (gateFirstSteps inputs done remaining)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done (remaining + 1))
                (SourceParser.packedTokenCells
                    (.gate :: indexTokens) ++
                  workTail)) =
            some
              (guardedConfig
                (State.sourceAfter01 .gateLeft)
                afterFirst (cell10 :: indexWord)) := by
        simpa [afterFirst, parsingPrefix, indexWord,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          firstSourceCell, afterFirstSourceState,
          cell01, cell10, SourceParser.cell01,
          SourceParser.cell10, List.append_assoc] using firstRun
      have headRun :=
        sourceAfter01NatLaunch_exact afterFirst indexWord
      have afterHeadSafe :
          SafeSourceWord afterHead := by
        apply safe_of_ordinary
        dsimp [afterHead, afterFirst, parsingPrefix]
        apply ordinary_append
        · apply ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates remaining))
          intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell01_ordinary
          · contradiction
        · intro symbol member
          simp only [List.mem_cons,
            List.not_mem_nil] at member
          rcases member with rfl | impossible
          · exact cell10_ordinary
          · contradiction
      have tail :=
        natTokenFailureWithMalformedTail_bounded_exact
          (.source .gateLeft) afterHead
          indexFailure afterHeadSafe malformed
      have throughHead :=
        BoundedRejectingExecution.prepend
          1
          (32 *
            (afterHead.length + indexWord.length + 1))
          _ _ (by
            simpa [afterHead, NatReader.state] using headRun)
          tail
      have joined :=
        BoundedRejectingExecution.prepend
          (gateFirstSteps inputs done remaining)
          (1 +
            32 *
              (afterHead.length + indexWord.length + 1))
          _ _ firstCanonical throughHead
      apply BoundedRejectingExecution.widen joined
      have firstBound :=
        gateFirstSteps_le_span inputs done remaining
          (cell10 :: indexWord)
      have prefixLength :=
        gateParsingPrefix_failurePrefix_length
          inputs done remaining
      dsimp [afterHead, afterFirst, parsingPrefix,
        indexWord] at firstBound ⊢
      simp only [List.length_append, List.length_cons,
        List.length_nil, SourceParser.packedTokenCells,
        SourceParser.tokenCells_length] at firstBound prefixLength ⊢
      omega

private theorem nGatesTokenFailureWithMalformedTail_bounded_exact
    (inputs : Nat) (done : List RawGate)
    {count : Nat} {tokens : List Token}
    (failure :
      SourceParser.NGatesTokenFailure count tokens)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart
        (failureGatePrefix inputs done count)
        (SourceParser.packedTokenCells tokens ++ workTail))
      (2048 * (count + 1) *
        ((failureGatePrefix inputs done count).length +
          (SourceParser.packedTokenCells tokens ++
            workTail).length + 1)) := by
  induction failure generalizing done with
  | @left count failedTokens failure =>
      have boundedRun :=
        gateLeftTokenFailureWithMalformedTail_bounded_exact
          inputs done (remaining := count) failure malformed
      apply BoundedRejectingExecution.widen boundedRun
      exact Nat.mul_le_mul_right _
        (by omega :
          1024 ≤ 2048 * ((count + 1) + 1))
  | @right count left failedTokens failure =>
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates count) ++
          sourceCells left
      let failedWord :=
        SourceParser.packedTokenCells failedTokens ++ workTail
      have leftRun :=
        gateLeft_exact inputs done count left failedWord
      have leftCanonical :
          workRunExact? machine
              (gateLeftSteps inputs done count left)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (count + 1))
                (SourceParser.packedTokenCells
                    (encodeSourceTokens left ++
                      failedTokens) ++
                  workTail)) =
            some
              (guardedConfig
                (State.sourceStart .gateRight)
                parsedPrefix failedWord) := by
        rw [packedTokenCells_append,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [parsedPrefix, failedWord,
          List.append_assoc] using leftRun
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        apply safe_of_ordinary
        dsimp [parsedPrefix]
        exact ordinary_append
          (gateParsingPrefix_ordinary inputs done
            (placeholderGates count))
          (sourceCells_ordinary left)
      have tail :=
        sourceTokenFailureWithMalformedTail_bounded_exact
          .gateRight parsedPrefix failure parsedSafe malformed
      have joined :=
        BoundedRejectingExecution.prepend
          (gateLeftSteps inputs done count left)
          (64 *
            (parsedPrefix.length + failedWord.length + 1))
          _ _ leftCanonical tail
      let span :=
        (failureGatePrefix inputs done
            (count + 1)).length +
          (SourceParser.packedTokenCells
              (encodeSourceTokens left ++ failedTokens) ++
            workTail).length + 1
      have packedShape :
          (SourceParser.packedTokenCells
                (encodeSourceTokens left ++ failedTokens) ++
              workTail).length =
            (sourceCells left ++ failedWord).length := by
        rw [packedTokenCells_append,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simp [failedWord, List.length_append]
      have stepLinear :
          gateLeftSteps inputs done count left ≤
            8 * span := by
        calc
          gateLeftSteps inputs done count left ≤
              8 *
                ((failureGatePrefix inputs done
                    (count + 1)).length +
                  (sourceCells left ++ failedWord).length + 1) :=
            gateLeftSteps_le_span inputs done count left
              failedWord
          _ = 8 * span := by
            dsimp [span]
            rw [packedShape]
      have tailSpan :
          parsedPrefix.length + failedWord.length + 1 =
            span := by
        have preserved :=
          gateLeft_span_preserved inputs done count left
            failedWord
        dsimp [parsedPrefix, span]
        rw [packedShape]
        omega
      have combined :
          gateLeftSteps inputs done count left +
              64 *
                (parsedPrefix.length + failedWord.length + 1) ≤
            72 * span := by
        rw [tailSpan]
        omega
      have coefficient :
          72 * span ≤
            2048 * ((count + 1) + 1) * span :=
        Nat.mul_le_mul_right span
          (by omega :
            72 ≤ 2048 * ((count + 1) + 1))
      apply BoundedRejectingExecution.widen joined
      exact Nat.le_trans combined coefficient
  | missingGateEnd count left right =>
      let gate : RawGate :=
        { left := left, right := right }
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates count) ++
          sourceCells left ++ sourceCells right
      have sources :=
        gateSources_exact inputs done count gate workTail
      have sourcesCanonical :
          workRunExact? machine
              (gateSourcesSteps inputs done count gate)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (count + 1))
                (SourceParser.packedTokenCells
                    (encodeSourceTokens left ++
                      encodeSourceTokens right) ++
                  workTail)) =
            some
              (guardedConfig State.gateEndFirst
                parsedPrefix workTail) := by
        rw [packedTokenCells_append,
          SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [gate, parsedPrefix,
          List.append_assoc] using sources
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        apply safe_of_ordinary
        dsimp [parsedPrefix]
        exact ordinary_append
          (ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates count))
            (sourceCells_ordinary left))
          (sourceCells_ordinary right)
      have tail :=
        simpleMalformedBoundary_bounded_exact
          .gateEnd parsedPrefix parsedSafe malformed
      have joined :=
        BoundedRejectingExecution.prepend
          (gateSourcesSteps inputs done count gate)
          (16 *
            (parsedPrefix.length + workTail.length + 1))
          _ _ sourcesCanonical tail
      let span :=
        (failureGatePrefix inputs done
            (count + 1)).length +
          (SourceParser.packedTokenCells
                (encodeSourceTokens left ++
                  encodeSourceTokens right) ++
              workTail).length + 1
      have packedShape :
          (SourceParser.packedTokenCells
                (encodeSourceTokens left ++
                  encodeSourceTokens right) ++
              workTail).length =
            (sourceCells left ++
              sourceCells right ++ workTail).length := by
        rw [packedTokenCells_append,
          SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
      have stepLinear :
          gateSourcesSteps inputs done count gate ≤
            16 * span := by
        calc
          gateSourcesSteps inputs done count gate ≤
              16 *
                ((failureGatePrefix inputs done
                    (count + 1)).length +
                  (sourceCells gate.left ++
                    sourceCells gate.right ++ workTail).length + 1) :=
            gateSourcesSteps_le_span inputs done count gate
              workTail
          _ = 16 * span := by
            dsimp [gate, span]
            rw [packedShape]
      have tailSpan :
          parsedPrefix.length + workTail.length + 1 =
            span := by
        have preserved :=
          gateSources_span_preserved inputs done count gate
            workTail
        dsimp [gate, parsedPrefix, span] at preserved ⊢
        rw [packedShape]
        simp only [List.length_append] at preserved ⊢
        omega
      have combined :
          gateSourcesSteps inputs done count gate +
              16 *
                (parsedPrefix.length + workTail.length + 1) ≤
            32 * span := by
        rw [tailSpan]
        omega
      have coefficient :
          32 * span ≤
            2048 * ((count + 1) + 1) * span :=
        Nat.mul_le_mul_right span
          (by omega :
            32 ≤ 2048 * ((count + 1) + 1))
      apply BoundedRejectingExecution.widen joined
      exact Nat.le_trans combined coefficient
  | wrongGateEnd count left right token suffix notGateEnd =>
      let gate : RawGate :=
        { left := left, right := right }
      let parsedPrefix :=
        gateParsingPrefix inputs done
            (placeholderGates count) ++
          sourceCells left ++ sourceCells right
      let failedWord :=
        SourceParser.packedTokenCells (token :: suffix) ++
          workTail
      have sources :=
        gateSources_exact inputs done count gate failedWord
      have sourcesCanonical :
          workRunExact? machine
              (gateSourcesSteps inputs done count gate)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (count + 1))
                (SourceParser.packedTokenCells
                    (encodeSourceTokens left ++
                      encodeSourceTokens right ++
                        token :: suffix) ++
                  workTail)) =
            some
              (guardedConfig State.gateEndFirst
                parsedPrefix failedWord) := by
        repeat rw [packedTokenCells_append]
        rw [SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [gate, parsedPrefix, failedWord,
          List.append_assoc] using sources
      have parsedSafe :
          SafeSourceWord parsedPrefix := by
        apply safe_of_ordinary
        dsimp [parsedPrefix]
        exact ordinary_append
          (ordinary_append
            (gateParsingPrefix_ordinary inputs done
              (placeholderGates count))
            (sourceCells_ordinary left))
          (sourceCells_ordinary right)
      have tail :=
        gateEndWrongTokenWithMalformedTail_bounded_exact
          parsedPrefix parsedSafe token suffix
          notGateEnd malformed
      have joined :=
        BoundedRejectingExecution.prepend
          (gateSourcesSteps inputs done count gate)
          (32 *
            (parsedPrefix.length + failedWord.length + 1))
          _ _ sourcesCanonical tail
      let span :=
        (failureGatePrefix inputs done
            (count + 1)).length +
          (SourceParser.packedTokenCells
                (encodeSourceTokens left ++
                  encodeSourceTokens right ++
                    token :: suffix) ++
              workTail).length + 1
      have packedShape :
          (SourceParser.packedTokenCells
                (encodeSourceTokens left ++
                  encodeSourceTokens right ++
                    token :: suffix) ++
              workTail).length =
            (sourceCells left ++ sourceCells right ++
              failedWord).length := by
        repeat rw [packedTokenCells_append]
        rw [SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simp [failedWord, List.append_assoc]
      have stepLinear :
          gateSourcesSteps inputs done count gate ≤
            16 * span := by
        calc
          gateSourcesSteps inputs done count gate ≤
              16 *
                ((failureGatePrefix inputs done
                    (count + 1)).length +
                  (sourceCells gate.left ++
                    sourceCells gate.right ++ failedWord).length + 1) :=
            gateSourcesSteps_le_span inputs done count gate
              failedWord
          _ = 16 * span := by
            dsimp [gate, span]
            rw [packedShape]
      have tailSpan :
          parsedPrefix.length + failedWord.length + 1 =
            span := by
        have preserved :=
          gateSources_span_preserved inputs done count gate
            failedWord
        dsimp [gate, parsedPrefix, span] at preserved ⊢
        rw [packedShape]
        simp only [List.length_append] at preserved ⊢
        omega
      have combined :
          gateSourcesSteps inputs done count gate +
              32 *
                (parsedPrefix.length + failedWord.length + 1) ≤
            48 * span := by
        rw [tailSpan]
        omega
      have coefficient :
          48 * span ≤
            2048 * ((count + 1) + 1) * span :=
        Nat.mul_le_mul_right span
          (by omega :
            48 ≤ 2048 * ((count + 1) + 1))
      apply BoundedRejectingExecution.widen joined
      exact Nat.le_trans combined coefficient
  | @rest count left right failedTokens failure ih =>
      let gate : RawGate :=
        { left := left, right := right }
      let failedWord :=
        SourceParser.packedTokenCells failedTokens ++ workTail
      have record :=
        gateRecord_exact inputs done count gate failedWord
      have recordCanonical :
          workRunExact? machine
              (gateRecordSteps inputs done count gate)
              (guardedConfig State.gateStart
                (failureGatePrefix inputs done
                  (count + 1))
                (SourceParser.packedTokenCells
                    (encodeSourceTokens left ++
                      encodeSourceTokens right ++
                        .gateEnd :: failedTokens) ++
                  workTail)) =
            some
              (guardedConfig State.gateStart
                (failureGatePrefix inputs
                  (done ++ [gate]) count)
                failedWord) := by
        repeat rw [packedTokenCells_append]
        rw [SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simpa [gate, gateCells,
          SourceParser.gateCells,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          cell01, cell11,
          SourceParser.cell01,
          SourceParser.cell11,
          failedWord, List.append_assoc] using record
      have tail := ih (done ++ [gate])
      have joined :=
        BoundedRejectingExecution.prepend
          (gateRecordSteps inputs done count gate)
          (2048 * (count + 1) *
            ((failureGatePrefix inputs
                (done ++ [gate]) count).length +
              failedWord.length + 1))
          _ _ recordCanonical tail
      let span :=
        (failureGatePrefix inputs done
            (count + 1)).length +
          (SourceParser.packedTokenCells
                (encodeSourceTokens left ++
                  encodeSourceTokens right ++
                    .gateEnd :: failedTokens) ++
              workTail).length + 1
      have packedShape :
          (SourceParser.packedTokenCells
                (encodeSourceTokens left ++
                  encodeSourceTokens right ++
                    .gateEnd :: failedTokens) ++
              workTail).length =
            (gateCells gate ++ failedWord).length := by
        repeat rw [packedTokenCells_append]
        rw [SourceParser.packedTokenCells_encodeSourceTokens,
          SourceParser.packedTokenCells_encodeSourceTokens]
        simp [gate, gateCells, SourceParser.gateCells,
          SourceParser.packedTokenCells,
          SourceParser.tokenCells,
          SourceParser.cell01,
          SourceParser.cell11,
          failedWord, List.append_assoc]
      have stepLinear :
          gateRecordSteps inputs done count gate ≤
            32 * span := by
        calc
          gateRecordSteps inputs done count gate ≤
              32 *
                ((failureGatePrefix inputs done
                    (count + 1)).length +
                  (gateCells gate ++ failedWord).length + 1) :=
            gateRecordSteps_le_span inputs done count gate
              failedWord
          _ = 32 * span := by
            dsimp [span]
            rw [packedShape]
      have tailSpan :
          (failureGatePrefix inputs
                (done ++ [gate]) count).length +
              failedWord.length + 1 =
            span := by
        have preserved :=
          gateRecord_span_preserved inputs done count gate
            failedWord
        dsimp [span]
        rw [packedShape]
        omega
      rw [tailSpan] at joined
      apply BoundedRejectingExecution.widen joined
      calc
        gateRecordSteps inputs done count gate +
              2048 * (count + 1) * span
            ≤ 32 * span +
                2048 * (count + 1) * span :=
          Nat.add_le_add_right stepLinear _
        _ ≤ 2048 * span +
              2048 * (count + 1) * span := by
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_right span (by omega)) _
        _ = (2048 + 2048 * (count + 1)) * span := by
          rw [Nat.add_mul]
        _ = 2048 * ((count + 1) + 1) * span := by
          have coefficient :
              2048 + 2048 * (count + 1) =
                2048 * ((count + 1) + 1) := by
            omega
          rw [coefficient]

private theorem versionWrongTokenWithMalformedTail_bounded_exact
    (token : Token) (suffix : List Token)
    (notVersion : token ≠ .version0)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (guardedConfig State.versionFirst []
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail))
      (16 *
        ((SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail).length + 1)) := by
  let suffixCells :=
    SourceParser.packedTokenCells suffix ++ workTail
  let initial :=
    guardedConfig State.versionFirst []
      (SourceParser.packedTokenCells
          (token :: suffix) ++
        workTail)
  have emptySafe : SafeSourceWord [] := by
    intro symbol member
    contradiction
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not00 : current ≠ cell00) :
      BoundedRejectingExecution initial
        (16 *
          ((SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail).length + 1)) := by
    have launch :=
      versionFirstFailure_exact current
        (next :: suffixCells) not00
    have result :=
      tokenMalformedExplicitFailure_bounded_exact
        [] [] token suffix malformed current
          (next :: suffixCells) initial 1 (by omega) emptySafe
        (by
          simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells])
        (by
          simpa [initial, SourceParser.packedTokenCells,
            cellsEq, suffixCells, pushCrossed,
            List.append_assoc] using launch)
    simpa only [List.length_nil, Nat.zero_add] using result
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell00, current])
      (not00 : current ≠ cell00) :
      BoundedRejectingExecution initial
        (16 *
          ((SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail).length + 1)) := by
    have launch :=
      versionSecondFromFirstFailure_exact
        current suffixCells not00
    have result :=
      tokenMalformedExplicitFailure_bounded_exact
        [] [cell00] token suffix malformed current
          suffixCells initial 2 (by omega) emptySafe
        (by
          simp [SourceParser.packedTokenCells, cellsEq,
            suffixCells])
        (by
          simpa [initial, SourceParser.packedTokenCells,
            cellsEq, suffixCells,
            List.append_assoc] using launch)
    simpa only [List.length_nil, Nat.zero_add] using result
  cases token with
  | version0 =>
      exact False.elim (notVersion rfl)
  | unit =>
      exact rejectSecond cell01 rfl (by decide)
  | natEnd =>
      exact rejectSecond cell10 rfl (by decide)
  | input =>
      exact rejectSecond cell11 rfl (by decide)
  | constantFalse =>
      exact rejectFirst cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact rejectFirst cell01 cell01 rfl (by decide)
  | gate =>
      exact rejectFirst cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact rejectFirst cell01 cell11 rfl (by decide)
  | programEnd =>
      exact rejectFirst cell10 cell00 rfl (by decide)
  | outputsEnd =>
      exact rejectFirst cell10 cell01 rfl (by decide)
  | threshold =>
      exact rejectFirst cell10 cell10 rfl (by decide)
  | instanceEnd =>
      exact rejectFirst cell10 cell11 rfl (by decide)

private theorem wrongProgramEndTokenWithMalformedTail_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (token : Token) (suffix : List Token)
    (notProgramEnd : token ≠ .programEnd)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (guardedConfig State.gateStart
        (gatePrefix inputs gates [])
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail))
      (256 *
        ((gatePrefix inputs gates []).length +
          (SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail).length + 1)) := by
  let suffixCells :=
    SourceParser.packedTokenCells suffix ++ workTail
  let initial :=
    guardedConfig State.gateStart
      (gatePrefix inputs gates [])
      (SourceParser.packedTokenCells
          (token :: suffix) ++
        workTail)
  have prefixSafe :
      SafeSourceWord (gatePrefix inputs gates []) :=
    safe_of_ordinary
      (gatePrefix_ordinary inputs gates [])
  have packedSafe :
      SafeSourceWord
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail) :=
    safe_append
      (packedTokenCells_safe (token :: suffix))
      (malformedWorkTail_safe malformed)
  have tailSafe
      (first current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [first, current]) :
      SafeSourceWord (current :: suffixCells) := by
    intro symbol member
    apply packedSafe symbol
    have targetMember :
        symbol ∈
          SourceParser.tokenCells token ++ suffixCells := by
      rw [cellsEq]
      simp only [List.mem_cons] at member
      rcases member with currentEq | member
      · subst symbol
        exact List.mem_append_left suffixCells (by simp)
      · exact List.mem_append_right [first, current] member
    simpa [SourceParser.packedTokenCells,
      suffixCells, List.append_assoc] using targetMember
  have exhausted
      (firstWas01 : Bool)
      (first current : WorkSymbol)
      (firstEq : firstSourceCell firstWas01 = first)
      (cellsEq :
        SourceParser.tokenCells token = [first, current]) :
      BoundedRejectingExecution initial
        (256 *
          ((gatePrefix inputs gates []).length +
            (SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail).length + 1)) := by
    have boundedRun :=
      gateDecrementExhausted_bounded_exact
        firstWas01 inputs gates current suffixCells
        (tailSafe first current cellsEq)
    simpa [initial, SourceParser.packedTokenCells,
      cellsEq, suffixCells, firstEq,
      List.append_assoc] using boundedRun
  have badSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell10, current])
      (not00 : current ≠ cell00) :
      BoundedRejectingExecution initial
        (256 *
          ((gatePrefix inputs gates []).length +
            (SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail).length + 1)) := by
    have boundedRun :=
      programEndSecond_bounded_exact
        (gatePrefix inputs gates []) prefixSafe
        current suffixCells
        (tailSafe cell10 current cellsEq) not00
    apply BoundedRejectingExecution.widen
      (by
        simpa [initial, SourceParser.packedTokenCells,
          cellsEq, suffixCells,
          List.append_assoc] using boundedRun)
    have tokenLength :=
      SourceParser.tokenCells_length token
    simp only [SourceParser.packedTokenCells,
      List.length_append, tokenLength]
    omega
  cases token with
  | version0 =>
      exact exhausted false cell00 cell00 rfl rfl
  | unit =>
      exact exhausted false cell00 cell01 rfl rfl
  | natEnd =>
      exact exhausted false cell00 cell10 rfl rfl
  | input =>
      exact exhausted false cell00 cell11 rfl rfl
  | constantFalse =>
      exact exhausted true cell01 cell00 rfl rfl
  | constantTrue =>
      exact exhausted true cell01 cell01 rfl rfl
  | gate =>
      exact exhausted true cell01 cell10 rfl rfl
  | gateEnd =>
      exact exhausted true cell01 cell11 rfl rfl
  | programEnd =>
      exact False.elim (notProgramEnd rfl)
  | outputsEnd =>
      exact badSecond cell01 rfl (by decide)
  | threshold =>
      exact badSecond cell10 rfl (by decide)
  | instanceEnd =>
      exact badSecond cell11 rfl (by decide)

private theorem outputsEndWrongTokenWithMalformedTail_bounded_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token)
    (notOutputsEnd : token ≠ .outputsEnd)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (guardedConfig State.outputsEndFirst parsedPrefix
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail))
      (16 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail).length + 1)) := by
  let suffixCells :=
    SourceParser.packedTokenCells suffix ++ workTail
  let initial :=
    guardedConfig State.outputsEndFirst parsedPrefix
      (SourceParser.packedTokenCells
          (token :: suffix) ++
        workTail)
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not10 : current ≠ cell10) :
      BoundedRejectingExecution initial
        (16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail).length + 1)) := by
    have launch :=
      outputsEndFirstFailure_exact parsedPrefix current
        (next :: suffixCells) not10
    apply tokenMalformedExplicitFailure_bounded_exact
      parsedPrefix parsedPrefix token suffix malformed
      current (next :: suffixCells) initial 1
      (by omega) prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells,
        List.append_assoc] using launch
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell10, current])
      (not01 : current ≠ cell01) :
      BoundedRejectingExecution initial
        (16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail).length + 1)) := by
    have launch :=
      outputsEndSecondFailure_exact parsedPrefix current
        suffixCells not01
    apply tokenMalformedExplicitFailure_bounded_exact
      parsedPrefix (parsedPrefix ++ [cell10])
      token suffix malformed current suffixCells
      initial 2 (by omega) prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells,
        List.append_assoc] using launch
  cases token with
  | version0 =>
      exact rejectFirst cell00 cell00 rfl (by decide)
  | unit =>
      exact rejectFirst cell00 cell01 rfl (by decide)
  | natEnd =>
      exact rejectFirst cell00 cell10 rfl (by decide)
  | input =>
      exact rejectFirst cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact rejectFirst cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact rejectFirst cell01 cell01 rfl (by decide)
  | gate =>
      exact rejectFirst cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact rejectFirst cell01 cell11 rfl (by decide)
  | programEnd =>
      exact rejectSecond cell00 rfl (by decide)
  | outputsEnd =>
      exact False.elim (notOutputsEnd rfl)
  | threshold =>
      exact rejectSecond cell10 rfl (by decide)
  | instanceEnd =>
      exact rejectSecond cell11 rfl (by decide)

private theorem instanceEndWrongTokenWithMalformedTail_bounded_exact
    (parsedPrefix : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (token : Token) (suffix : List Token)
    (notInstanceEnd : token ≠ .instanceEnd)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (guardedConfig State.instanceEndFirst parsedPrefix
        (SourceParser.packedTokenCells
            (token :: suffix) ++
          workTail))
      (16 *
        (parsedPrefix.length +
          (SourceParser.packedTokenCells
              (token :: suffix) ++
            workTail).length + 1)) := by
  let suffixCells :=
    SourceParser.packedTokenCells suffix ++ workTail
  let initial :=
    guardedConfig State.instanceEndFirst parsedPrefix
      (SourceParser.packedTokenCells
          (token :: suffix) ++
        workTail)
  have rejectFirst
      (current next : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [current, next])
      (not10 : current ≠ cell10) :
      BoundedRejectingExecution initial
        (16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail).length + 1)) := by
    have launch :=
      instanceEndFirstFailure_exact parsedPrefix current
        (next :: suffixCells) not10
    apply tokenMalformedExplicitFailure_bounded_exact
      parsedPrefix parsedPrefix token suffix malformed
      current (next :: suffixCells) initial 1
      (by omega) prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells,
        List.append_assoc] using launch
  have rejectSecond
      (current : WorkSymbol)
      (cellsEq :
        SourceParser.tokenCells token = [cell10, current])
      (not11 : current ≠ cell11) :
      BoundedRejectingExecution initial
        (16 *
          (parsedPrefix.length +
            (SourceParser.packedTokenCells
                (token :: suffix) ++
              workTail).length + 1)) := by
    have launch :=
      instanceEndSecondFailure_exact parsedPrefix current
        suffixCells not11
    apply tokenMalformedExplicitFailure_bounded_exact
      parsedPrefix (parsedPrefix ++ [cell10])
      token suffix malformed current suffixCells
      initial 2 (by omega) prefixSafe
    · simp [SourceParser.packedTokenCells, cellsEq,
        suffixCells, List.append_assoc]
    · simpa [initial, SourceParser.packedTokenCells,
        cellsEq, suffixCells,
        List.append_assoc] using launch
  cases token with
  | version0 =>
      exact rejectFirst cell00 cell00 rfl (by decide)
  | unit =>
      exact rejectFirst cell00 cell01 rfl (by decide)
  | natEnd =>
      exact rejectFirst cell00 cell10 rfl (by decide)
  | input =>
      exact rejectFirst cell00 cell11 rfl (by decide)
  | constantFalse =>
      exact rejectFirst cell01 cell00 rfl (by decide)
  | constantTrue =>
      exact rejectFirst cell01 cell01 rfl (by decide)
  | gate =>
      exact rejectFirst cell01 cell10 rfl (by decide)
  | gateEnd =>
      exact rejectFirst cell01 cell11 rfl (by decide)
  | programEnd =>
      exact rejectSecond cell00 rfl (by decide)
  | outputsEnd =>
      exact rejectSecond cell01 rfl (by decide)
  | threshold =>
      exact rejectSecond cell10 rfl (by decide)
  | instanceEnd =>
      exact False.elim (notInstanceEnd rfl)

private theorem finalEOFWord_bounded_exact
    (parsedPrefix word : List WorkSymbol)
    (prefixSafe : SafeSourceWord parsedPrefix)
    (wordSafe : SafeSourceWord word)
    (wordNonempty : word ≠ []) :
    BoundedRejectingExecution
      (guardedConfig State.finalEOF parsedPrefix word)
      (16 * (parsedPrefix.length + word.length + 1)) := by
  cases word with
  | nil =>
      exact False.elim (wordNonempty rfl)
  | cons current rest =>
      have notBlank : current ≠ cellBlank :=
        (wordSafe current (by simp)).2
      have launch :=
        finalEOFFailure_exact parsedPrefix current
          rest notBlank
      have boundedRun :=
        safeExplicitFailure_bounded_exact
          (parsedPrefix ++ current :: rest)
          parsedPrefix current rest
          (guardedConfig State.finalEOF
            parsedPrefix (current :: rest))
          1 rfl
          (safe_append prefixSafe wordSafe)
          launch
      apply BoundedRejectingExecution.widen boundedRun
      simp only [List.length_append, List.length_cons]
      omega

private theorem linearJoin_le_grammarCellCube
    (cells prefixSteps span prefixCoefficient
      tailCoefficient : Nat)
    (prefixBound :
      prefixSteps ≤
        prefixCoefficient * grammarCellCube cells)
    (spanEq : span = cells + 1)
    (coefficientBound :
      prefixCoefficient + tailCoefficient ≤ 4096) :
    prefixSteps + tailCoefficient * span ≤
      4096 * grammarCellCube cells := by
  have tailBound :
      tailCoefficient * span ≤
        tailCoefficient * grammarCellCube cells := by
    rw [spanEq]
    exact Nat.mul_le_mul_left tailCoefficient
      (succ_le_grammarCellCube cells)
  calc
    prefixSteps + tailCoefficient * span ≤
        prefixCoefficient * grammarCellCube cells +
          tailCoefficient * grammarCellCube cells :=
      Nat.add_le_add prefixBound tailBound
    _ =
        (prefixCoefficient + tailCoefficient) *
          grammarCellCube cells := by
      rw [Nat.add_mul]
    _ ≤ 4096 * grammarCellCube cells :=
      Nat.mul_le_mul_right
        (grammarCellCube cells) coefficientBound

private theorem quadraticJoin_le_grammarCellCube
    (cells prefixSteps count span prefixCoefficient
      tailCoefficient : Nat)
    (prefixBound :
      prefixSteps ≤
        prefixCoefficient * grammarCellCube cells)
    (countBound : count ≤ cells + 1)
    (spanEq : span = cells + 1)
    (coefficientBound :
      prefixCoefficient + tailCoefficient ≤ 4096) :
    prefixSteps + tailCoefficient * count * span ≤
      4096 * grammarCellCube cells := by
  have countProduct :=
    Nat.mul_le_mul countBound
      (Nat.le_refl (cells + 1))
  have tailBound :
      tailCoefficient * count * span ≤
        tailCoefficient * grammarCellCube cells := by
    rw [spanEq]
    calc
      tailCoefficient * count * (cells + 1) =
          tailCoefficient * (count * (cells + 1)) := by
        ac_rfl
      _ ≤
          tailCoefficient *
            ((cells + 1) * (cells + 1)) :=
        Nat.mul_le_mul_left tailCoefficient countProduct
      _ ≤ tailCoefficient * grammarCellCube cells :=
        Nat.mul_le_mul_left tailCoefficient
          (succSquare_le_grammarCellCube cells)
  calc
    prefixSteps + tailCoefficient * count * span ≤
        prefixCoefficient * grammarCellCube cells +
          tailCoefficient * grammarCellCube cells :=
      Nat.add_le_add prefixBound tailBound
    _ =
        (prefixCoefficient + tailCoefficient) *
          grammarCellCube cells := by
      rw [Nat.add_mul]
    _ ≤ 4096 * grammarCellCube cells :=
      Nat.mul_le_mul_right
        (grammarCellCube cells) coefficientBound

private theorem circuitMissingVersionWithMalformedTail_bounded_exact
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells [] ++ workTail)))
      (4096 * grammarCellCube workTail.length) := by
  have prefixRun := scannerBootWord_exact workTail
  have tail :=
    simpleMalformedBoundary_bounded_exact
      .versionFirst [] (by
        intro symbol member
        contradiction) malformed
  have joined :=
    BoundedRejectingExecution.prepend
      2 (16 * workTail.length.succ)
      _ _
      (by
        simpa [SourceParser.packedTokenCells,
          SimpleMalformedBoundary.state] using prefixRun)
      (by
        simpa [Nat.succ_eq_add_one,
          SimpleMalformedBoundary.state] using tail)
  apply BoundedRejectingExecution.widen joined
  apply linearJoin_le_grammarCellCube
    workTail.length 2 workTail.length.succ 2 16
  · have one := one_le_grammarCellCube workTail.length
    omega
  · omega
  · omega

private theorem circuitWrongVersionWithMalformedTail_bounded_exact
    (token : Token) (suffix : List Token)
    (notVersion : token ≠ .version0)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let word :=
      SourceParser.packedTokenCells (token :: suffix) ++
        workTail
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols word))
      (4096 * grammarCellCube word.length) := by
  dsimp only
  let word :=
    SourceParser.packedTokenCells (token :: suffix) ++
      workTail
  have prefixRun := scannerBootWord_exact word
  have tail :=
    versionWrongTokenWithMalformedTail_bounded_exact
      token suffix notVersion malformed
  have joined :=
    BoundedRejectingExecution.prepend
      2 (16 * (word.length + 1))
      _ _ prefixRun
      (by simpa [word] using tail)
  apply BoundedRejectingExecution.widen joined
  apply linearJoin_le_grammarCellCube
    word.length 2 (word.length + 1) 2 16
  · have one := one_le_grammarCellCube word.length
    omega
  · rfl
  · omega

private theorem circuitInputCountWithMalformedTail_bounded_exact
    {tokens : List Token}
    (failure : SourceParser.NatTokenFailure tokens)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let cells :=
      (SourceParser.packedTokenCells
          (.version0 :: tokens) ++
        workTail).length
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (.version0 :: tokens) ++
            workTail)))
      (4096 * grammarCellCube cells) := by
  dsimp only
  let suffixWord :=
    SourceParser.packedTokenCells tokens ++ workTail
  let cells :=
    (SourceParser.packedTokenCells
        (.version0 :: tokens) ++
      workTail).length
  have prefixRun := versionPrefixWord_exact suffixWord
  have prefixCanonical :
      workRunExact? machine 4
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (.version0 :: tokens) ++
                workTail))) =
        some
          (guardedConfig State.inputCountFirst
            [cell00, cell00] suffixWord) := by
    simpa [suffixWord, SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      cell00, SourceParser.cell00,
      List.append_assoc] using prefixRun
  have prefixSafe : SafeSourceWord [cell00, cell00] := by
    intro symbol member
    simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with rfl | rfl | impossible
    · decide
    · decide
    · contradiction
  have tail :=
    natTokenFailureWithMalformedTail_bounded_exact
      .inputCount [cell00, cell00]
      failure prefixSafe malformed
  have joined :=
    BoundedRejectingExecution.prepend
      4
      (32 *
        (([cell00, cell00] : List WorkSymbol).length +
          suffixWord.length + 1))
      _ _ prefixCanonical
      (by
        simpa [suffixWord, NatReader.state] using tail)
  apply BoundedRejectingExecution.widen joined
  have spanEq :
      ([cell00, cell00] : List WorkSymbol).length +
          suffixWord.length + 1 =
        cells + 1 := by
    dsimp [suffixWord, cells]
    simp [SourceParser.packedTokenCells,
      SourceParser.tokenCells]
    omega
  apply linearJoin_le_grammarCellCube
    cells 4
      (([cell00, cell00] : List WorkSymbol).length +
        suffixWord.length + 1)
      4 32
  · have one := one_le_grammarCellCube cells
    omega
  · exact spanEq
  · omega

private theorem circuitGateCountWithMalformedTail_bounded_exact
    (inputs : Nat) {tokens : List Token}
    (failure : SourceParser.NatTokenFailure tokens)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let cells :=
      (SourceParser.packedTokenCells
          (.version0 ::
            (encodeNatTokens inputs ++ tokens)) ++
        workTail).length
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (.version0 ::
                (encodeNatTokens inputs ++ tokens)) ++
            workTail)))
      (4096 * grammarCellCube cells) := by
  dsimp only
  let parsedPrefix :=
    [cell00, cell00] ++ natCells inputs
  let suffixWord :=
    SourceParser.packedTokenCells tokens ++ workTail
  let cells :=
    (SourceParser.packedTokenCells
        (.version0 ::
          (encodeNatTokens inputs ++ tokens)) ++
      workTail).length
  have prefixRun :=
    inputPrefixWord_exact inputs suffixWord
  have prefixCanonical :
      workRunExact? machine (inputPrefixWordSteps inputs)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (.version0 ::
                    (encodeNatTokens inputs ++ tokens)) ++
                workTail))) =
        some
          (guardedConfig State.gateCountFirst
            parsedPrefix suffixWord) := by
    dsimp [parsedPrefix]
    simpa [suffixWord, SourceParser.packedTokenCells,
      SourceParser.tokenCells, packedTokenCells_append,
      SourceParser.packedTokenCells_encodeNatTokens,
      cell00, SourceParser.cell00,
      List.append_assoc] using prefixRun
  have prefixSafe : SafeSourceWord parsedPrefix := by
    have safe :=
      packedTokenCells_safe
        (.version0 :: encodeNatTokens inputs)
    dsimp [parsedPrefix]
    simpa [SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      SourceParser.packedTokenCells_encodeNatTokens,
      cell00, SourceParser.cell00] using safe
  have tail :=
    natTokenFailureWithMalformedTail_bounded_exact
      .gateCount parsedPrefix failure prefixSafe malformed
  have joined :=
    BoundedRejectingExecution.prepend
      (inputPrefixWordSteps inputs)
      (32 *
        (parsedPrefix.length + suffixWord.length + 1))
      _ _ prefixCanonical
      (by
        simpa [suffixWord, NatReader.state] using tail)
  apply BoundedRejectingExecution.widen joined
  have cellsEq :
      cells = parsedPrefix.length + suffixWord.length := by
    dsimp [cells, parsedPrefix, suffixWord]
    simp [SourceParser.packedTokenCells,
      SourceParser.tokenCells, packedTokenCells_append,
      SourceParser.packedTokenCells_encodeNatTokens,
      SourceParser.natCells_length]
    omega
  have prefixCost :
      inputPrefixWordSteps inputs ≤
        3 * grammarCellCube cells := by
    have cellsBound := cell_le_grammarCellCube cells
    have one := one_le_grammarCellCube cells
    unfold inputPrefixWordSteps
    dsimp [parsedPrefix, suffixWord] at cellsEq
    simp [SourceParser.natCells_length] at cellsEq
    omega
  apply linearJoin_le_grammarCellCube
    cells (inputPrefixWordSteps inputs)
      (parsedPrefix.length + suffixWord.length + 1)
      3 32 prefixCost
  · omega
  · omega

private theorem circuitGatesWithMalformedTail_bounded_exact
    (inputs gateCount : Nat) {tokens : List Token}
    (failure :
      SourceParser.NGatesTokenFailure gateCount tokens)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let cells :=
      (SourceParser.packedTokenCells
          (SourceParser.circuitHeaderTokens
              inputs gateCount ++
            tokens) ++
        workTail).length
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (SourceParser.circuitHeaderTokens
                  inputs gateCount ++
                tokens) ++
            workTail)))
      (4096 * grammarCellCube cells) := by
  dsimp only
  let suffixWord :=
    SourceParser.packedTokenCells tokens ++ workTail
  let cells :=
    (SourceParser.packedTokenCells
        (SourceParser.circuitHeaderTokens
            inputs gateCount ++
          tokens) ++
      workTail).length
  have headerRun :=
    headerPrefixWord_exact inputs gateCount suffixWord
  have prefixEq :
      failureGatePrefix inputs [] gateCount =
        headerPrefixCells inputs gateCount := by
    simp [failureGatePrefix, placeholderGates,
      gatePrefix, SourceParser.gatePrefix,
      headerPrefixCells,
      SourceParser.markedGateListCells,
      SourceParser.countCells,
      natCells, cell00,
      SourceParser.cell00]
  have headerCanonical :
      workRunExact? machine
          (headerPrefixWordSteps inputs gateCount)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (SourceParser.circuitHeaderTokens
                      inputs gateCount ++
                    tokens) ++
                workTail))) =
        some
          (guardedConfig State.gateStart
            (failureGatePrefix inputs [] gateCount)
            suffixWord) := by
    rw [packedTokenCells_append,
      packedCircuitHeaderTokens_eq, prefixEq]
    simpa [suffixWord, List.append_assoc] using headerRun
  have tail :=
    nGatesTokenFailureWithMalformedTail_bounded_exact
      inputs [] failure malformed
  have joined :=
    BoundedRejectingExecution.prepend
      (headerPrefixWordSteps inputs gateCount)
      (2048 * (gateCount + 1) *
        ((failureGatePrefix inputs [] gateCount).length +
          suffixWord.length + 1))
      _ _ headerCanonical
      (by simpa [suffixWord] using tail)
  apply BoundedRejectingExecution.widen joined
  have cellsEq :
      cells =
        (failureGatePrefix inputs [] gateCount).length +
          suffixWord.length := by
    dsimp [cells, suffixWord]
    rw [packedTokenCells_append,
      packedCircuitHeaderTokens_eq, prefixEq]
    simp
  have countLe : gateCount + 1 ≤ cells + 1 := by
    have headerLe :
        (headerPrefixCells inputs gateCount).length ≤ cells := by
      rw [cellsEq, prefixEq]
      omega
    simp [headerPrefixCells,
      SourceParser.natCells_length] at headerLe
    omega
  have headerCost :
      headerPrefixWordSteps inputs gateCount ≤
        3 * grammarCellCube cells := by
    have cellsBound := cell_le_grammarCellCube cells
    have one := one_le_grammarCellCube cells
    have headerLe :
        (headerPrefixCells inputs gateCount).length ≤ cells := by
      rw [cellsEq, prefixEq]
      omega
    unfold headerPrefixWordSteps inputPrefixWordSteps
    simp [headerPrefixCells,
      SourceParser.natCells_length] at headerLe
    omega
  apply quadraticJoin_le_grammarCellCube
    cells (headerPrefixWordSteps inputs gateCount)
      (gateCount + 1)
      ((failureGatePrefix inputs [] gateCount).length +
        suffixWord.length + 1)
      3 2048 headerCost countLe
  · omega
  · omega

private theorem circuitMissingProgramEndWithMalformedTail_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let cells :=
      (SourceParser.packedTokenCells
          (SourceParser.circuitGatesPrefixTokens
            inputs gates) ++
        workTail).length
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (SourceParser.circuitGatesPrefixTokens
                inputs gates) ++
            workTail)))
      (4096 * grammarCellCube cells) := by
  dsimp only
  let cells :=
    (SourceParser.packedTokenCells
        (SourceParser.circuitGatesPrefixTokens
          inputs gates) ++
      workTail).length
  have prefixRun :=
    circuitGatesPrefixWord_exact inputs gates workTail
  have tail :=
    gateMalformedTail_bounded_exact inputs gates 0 malformed
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitGatesPrefixWordSteps inputs gates)
      (512 *
        ((gatePrefix inputs gates []).length +
          workTail.length + 1))
      _ _
      (by simpa [List.append_assoc] using prefixRun)
      (by
        simpa [failureGatePrefix,
          placeholderGates] using tail)
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitGatesPrefixTokens
        inputs gates)).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    simp
  have prefixCost :
      circuitGatesPrefixWordSteps inputs gates ≤
        16 * grammarCellCube cells :=
    Nat.le_trans
      (circuitGatesPrefixWordSteps_le_cube inputs gates)
      (Nat.mul_le_mul_left 16
        (grammarCellCube_mono prefixLe))
  have spanEq :
      (gatePrefix inputs gates []).length +
          workTail.length + 1 =
        cells + 1 := by
    dsimp [cells]
    rw [gatePrefix_length_eq_packedGatesPrefix]
    simp
  exact linearJoin_le_grammarCellCube
    cells
    (circuitGatesPrefixWordSteps inputs gates)
    ((gatePrefix inputs gates []).length +
      workTail.length + 1)
    16 512 prefixCost spanEq (by omega)

private theorem circuitWrongProgramEndWithMalformedTail_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (token : Token) (suffix : List Token)
    (notProgramEnd : token ≠ .programEnd)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let cells :=
      (SourceParser.packedTokenCells
          (SourceParser.circuitGatesPrefixTokens
              inputs gates ++
            token :: suffix) ++
        workTail).length
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (SourceParser.circuitGatesPrefixTokens
                  inputs gates ++
                token :: suffix) ++
            workTail)))
      (4096 * grammarCellCube cells) := by
  dsimp only
  let suffixWord :=
    SourceParser.packedTokenCells (token :: suffix) ++
      workTail
  let cells :=
    (SourceParser.packedTokenCells
        (SourceParser.circuitGatesPrefixTokens
            inputs gates ++
          token :: suffix) ++
      workTail).length
  have prefixRun :=
    circuitGatesPrefixWord_exact inputs gates suffixWord
  have prefixCanonical :
      workRunExact? machine
          (circuitGatesPrefixWordSteps inputs gates)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (SourceParser.circuitGatesPrefixTokens
                      inputs gates ++
                    token :: suffix) ++
                workTail))) =
        some
          (guardedConfig State.gateStart
            (gatePrefix inputs gates []) suffixWord) := by
    rw [packedTokenCells_append]
    simpa [suffixWord, List.append_assoc] using prefixRun
  have tail :=
    wrongProgramEndTokenWithMalformedTail_bounded_exact
      inputs gates token suffix notProgramEnd malformed
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitGatesPrefixWordSteps inputs gates)
      (256 *
        ((gatePrefix inputs gates []).length +
          suffixWord.length + 1))
      _ _ prefixCanonical
      (by simpa [suffixWord] using tail)
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitGatesPrefixTokens
        inputs gates)).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    rw [packedTokenCells_append]
    simp
  have prefixCost :
      circuitGatesPrefixWordSteps inputs gates ≤
        16 * grammarCellCube cells :=
    Nat.le_trans
      (circuitGatesPrefixWordSteps_le_cube inputs gates)
      (Nat.mul_le_mul_left 16
        (grammarCellCube_mono prefixLe))
  have spanEq :
      (gatePrefix inputs gates []).length +
          suffixWord.length + 1 =
        cells + 1 := by
    dsimp [suffixWord, cells]
    rw [packedTokenCells_append,
      gatePrefix_length_eq_packedGatesPrefix]
    simp
  exact linearJoin_le_grammarCellCube
    cells
    (circuitGatesPrefixWordSteps inputs gates)
    ((gatePrefix inputs gates []).length +
      suffixWord.length + 1)
    16 256 prefixCost spanEq (by omega)

private theorem circuitOutputWithMalformedTail_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    {tokens : List Token}
    (failure : SourceParser.SourceTokenFailure tokens)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let cells :=
      (SourceParser.packedTokenCells
          (SourceParser.circuitGatesPrefixTokens inputs gates ++
            .programEnd :: tokens) ++
        workTail).length
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (SourceParser.circuitGatesPrefixTokens
                  inputs gates ++
                .programEnd :: tokens) ++
            workTail)))
      (4096 * grammarCellCube cells) := by
  dsimp only
  let suffixWord :=
    SourceParser.packedTokenCells tokens ++ workTail
  let cells :=
    (SourceParser.packedTokenCells
        (SourceParser.circuitGatesPrefixTokens inputs gates ++
          .programEnd :: tokens) ++
      workTail).length
  have prefixRun :=
    circuitProgramPrefixWord_exact inputs gates suffixWord
  have prefixCanonical :
      workRunExact? machine
          (circuitProgramPrefixWordSteps inputs gates)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (SourceParser.circuitGatesPrefixTokens
                      inputs gates ++
                    .programEnd :: tokens) ++
                workTail))) =
        some
          (guardedConfig (State.sourceStart .output)
            (outputPrefix inputs gates) suffixWord) := by
    rw [packedTokenCells_append] at prefixRun
    rw [packedTokenCells_append]
    simpa [suffixWord, SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      List.append_assoc] using prefixRun
  have tail :=
    sourceTokenFailureWithMalformedTail_bounded_exact
      .output (outputPrefix inputs gates) failure
      (safe_of_ordinary
        (outputPrefix_ordinary inputs gates))
      malformed
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitProgramPrefixWordSteps inputs gates)
      (64 *
        ((outputPrefix inputs gates).length +
          suffixWord.length + 1))
      _ _ prefixCanonical
      (by simpa [suffixWord] using tail)
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitGatesPrefixTokens
          inputs gates ++ [.programEnd])).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    repeat rw [packedTokenCells_append]
    simp [SourceParser.packedTokenCells]
  have prefixCost :
      circuitProgramPrefixWordSteps inputs gates ≤
        24 * grammarCellCube cells :=
    Nat.le_trans
      (circuitProgramPrefixWordSteps_le_cube inputs gates)
      (Nat.mul_le_mul_left 24
        (grammarCellCube_mono prefixLe))
  have spanEq :
      (outputPrefix inputs gates).length +
          suffixWord.length + 1 =
        cells + 1 := by
    dsimp [suffixWord, cells]
    rw [outputPrefix_length_eq_packedProgramPrefix]
    repeat rw [packedTokenCells_append]
    simp [SourceParser.packedTokenCells]
    omega
  exact linearJoin_le_grammarCellCube
    cells
    (circuitProgramPrefixWordSteps inputs gates)
    ((outputPrefix inputs gates).length +
      suffixWord.length + 1)
    24 64 prefixCost spanEq (by omega)

private theorem circuitMissingOutputsEndWithMalformedTail_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let cells :=
      (SourceParser.packedTokenCells
          (SourceParser.circuitOutputPrefixTokens
            inputs gates output) ++
        workTail).length
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (SourceParser.circuitOutputPrefixTokens
                inputs gates output) ++
            workTail)))
      (4096 * grammarCellCube cells) := by
  dsimp only
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  let cells :=
    (SourceParser.packedTokenCells
        (SourceParser.circuitOutputPrefixTokens
          inputs gates output) ++
      workTail).length
  have prefixRun :=
    circuitOutputPrefixWord_exact
      inputs gates output workTail
  have tail :=
    simpleMalformedBoundary_bounded_exact
      .outputsEnd parsedPrefix
      (outputParsedPrefix_safe inputs gates output)
      malformed
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output)
      (16 * (parsedPrefix.length + workTail.length + 1))
      _ _
      (by simpa [parsedPrefix,
        SimpleMalformedBoundary.state] using prefixRun)
      (by simpa [SimpleMalformedBoundary.state] using tail)
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
        inputs gates output)).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    simp
  have prefixCost :
      circuitOutputPrefixWordSteps inputs gates output ≤
        25 * grammarCellCube cells :=
    Nat.le_trans
      (circuitOutputPrefixWordSteps_le_cube
        inputs gates output)
      (Nat.mul_le_mul_left 25
        (grammarCellCube_mono prefixLe))
  have spanEq :
      parsedPrefix.length + workTail.length + 1 =
        cells + 1 := by
    have parsedLength :=
      outputParsedPrefix_length_eq_packed
        inputs gates output
    dsimp [parsedPrefix, cells] at parsedLength ⊢
    simp only [List.length_append] at parsedLength ⊢
    omega
  exact linearJoin_le_grammarCellCube
    cells
    (circuitOutputPrefixWordSteps inputs gates output)
    (parsedPrefix.length + workTail.length + 1)
    25 16 prefixCost spanEq (by omega)

private theorem circuitWrongOutputsEndWithMalformedTail_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) (token : Token)
    (suffix : List Token)
    (notOutputsEnd : token ≠ .outputsEnd)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let cells :=
      (SourceParser.packedTokenCells
          (SourceParser.circuitOutputPrefixTokens
              inputs gates output ++
            token :: suffix) ++
        workTail).length
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (SourceParser.circuitOutputPrefixTokens
                  inputs gates output ++
                token :: suffix) ++
            workTail)))
      (4096 * grammarCellCube cells) := by
  dsimp only
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  let suffixWord :=
    SourceParser.packedTokenCells (token :: suffix) ++
      workTail
  let cells :=
    (SourceParser.packedTokenCells
        (SourceParser.circuitOutputPrefixTokens
            inputs gates output ++
          token :: suffix) ++
      workTail).length
  have prefixRun :=
    circuitOutputPrefixWord_exact inputs gates output
      suffixWord
  have prefixCanonical :
      workRunExact? machine
          (circuitOutputPrefixWordSteps inputs gates output)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (SourceParser.circuitOutputPrefixTokens
                      inputs gates output ++
                    token :: suffix) ++
                workTail))) =
        some
          (guardedConfig State.outputsEndFirst
            parsedPrefix suffixWord) := by
    rw [packedTokenCells_append]
    simpa [parsedPrefix, suffixWord,
      List.append_assoc] using prefixRun
  have tail :=
    outputsEndWrongTokenWithMalformedTail_bounded_exact
      parsedPrefix
      (outputParsedPrefix_safe inputs gates output)
      token suffix notOutputsEnd malformed
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output)
      (16 * (parsedPrefix.length + suffixWord.length + 1))
      _ _ prefixCanonical
      (by simpa [suffixWord] using tail)
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
        inputs gates output)).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    rw [packedTokenCells_append]
    simp
  have prefixCost :
      circuitOutputPrefixWordSteps inputs gates output ≤
        25 * grammarCellCube cells :=
    Nat.le_trans
      (circuitOutputPrefixWordSteps_le_cube
        inputs gates output)
      (Nat.mul_le_mul_left 25
        (grammarCellCube_mono prefixLe))
  have spanEq :
      parsedPrefix.length + suffixWord.length + 1 =
        cells + 1 := by
    dsimp [parsedPrefix, suffixWord, cells]
    rw [packedTokenCells_append,
      outputParsedPrefix_length_eq_packed]
    simp
  exact linearJoin_le_grammarCellCube
    cells
    (circuitOutputPrefixWordSteps inputs gates output)
    (parsedPrefix.length + suffixWord.length + 1)
    25 16 prefixCost spanEq (by omega)

private theorem circuitMissingInstanceEndWithMalformedTail_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let cells :=
      (SourceParser.packedTokenCells
          (SourceParser.circuitOutputPrefixTokens
              inputs gates output ++
            [.outputsEnd]) ++
        workTail).length
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (SourceParser.circuitOutputPrefixTokens
                  inputs gates output ++
                [.outputsEnd]) ++
            workTail)))
      (4096 * grammarCellCube cells) := by
  dsimp only
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  let afterOutputs :=
    parsedPrefix ++ [cell10, cell01]
  let cells :=
    (SourceParser.packedTokenCells
        (SourceParser.circuitOutputPrefixTokens
            inputs gates output ++
          [.outputsEnd]) ++
      workTail).length
  have prefixRun :=
    circuitOutputPrefixWord_exact inputs gates output
      ([cell10, cell01] ++ workTail)
  have delimiter :=
    outputsEnd_exact parsedPrefix workTail
  have through :=
    exactRun_add
      (circuitOutputPrefixWordSteps inputs gates output)
      2 _ _ _
      (by simpa [parsedPrefix] using prefixRun)
      delimiter
  have throughCanonical :
      workRunExact? machine
          (circuitOutputPrefixWordSteps inputs gates output + 2)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (SourceParser.circuitOutputPrefixTokens
                      inputs gates output ++
                    [.outputsEnd]) ++
                workTail))) =
        some
          (guardedConfig State.instanceEndFirst
            afterOutputs workTail) := by
    simpa [parsedPrefix, afterOutputs,
      packedTokenCells_append,
      SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      cell10, cell01,
      SourceParser.cell10,
      SourceParser.cell01,
      List.append_assoc] using through
  have afterSafe : SafeSourceWord afterOutputs := by
    apply safe_append
      (outputParsedPrefix_safe inputs gates output)
    intro symbol member
    simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with rfl | rfl | impossible
    · decide
    · decide
    · contradiction
  have tail :=
    simpleMalformedBoundary_bounded_exact
      .instanceEnd afterOutputs afterSafe malformed
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output + 2)
      (16 * (afterOutputs.length + workTail.length + 1))
      _ _ throughCanonical
      (by simpa [SimpleMalformedBoundary.state] using tail)
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
        inputs gates output)).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    rw [packedTokenCells_append]
    simp
  have baseCost :
      circuitOutputPrefixWordSteps inputs gates output ≤
        25 * grammarCellCube cells :=
    Nat.le_trans
      (circuitOutputPrefixWordSteps_le_cube
        inputs gates output)
      (Nat.mul_le_mul_left 25
        (grammarCellCube_mono prefixLe))
  have prefixCost :
      circuitOutputPrefixWordSteps inputs gates output + 2 ≤
        27 * grammarCellCube cells := by
    have one := one_le_grammarCellCube cells
    omega
  have spanEq :
      afterOutputs.length + workTail.length + 1 =
        cells + 1 := by
    have parsedLength :=
      outputParsedPrefix_length_eq_packed
        inputs gates output
    dsimp [afterOutputs, parsedPrefix, cells]
    repeat rw [packedTokenCells_append]
    simp only [List.length_append, List.length_cons,
      List.length_nil] at parsedLength ⊢
    simp [SourceParser.packedTokenCells,
      SourceParser.tokenCells] at parsedLength ⊢
    omega
  exact linearJoin_le_grammarCellCube
    cells
    (circuitOutputPrefixWordSteps inputs gates output + 2)
    (afterOutputs.length + workTail.length + 1)
    27 16 prefixCost spanEq (by omega)

private theorem circuitWrongInstanceEndWithMalformedTail_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) (token : Token)
    (suffix : List Token)
    (notInstanceEnd : token ≠ .instanceEnd)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let cells :=
      (SourceParser.packedTokenCells
          (SourceParser.circuitOutputPrefixTokens
              inputs gates output ++
            [.outputsEnd, token] ++ suffix) ++
        workTail).length
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (SourceParser.circuitOutputPrefixTokens
                  inputs gates output ++
                [.outputsEnd, token] ++ suffix) ++
            workTail)))
      (4096 * grammarCellCube cells) := by
  dsimp only
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  let afterOutputs :=
    parsedPrefix ++ [cell10, cell01]
  let tokenWord :=
    SourceParser.packedTokenCells (token :: suffix) ++
      workTail
  let cells :=
    (SourceParser.packedTokenCells
        (SourceParser.circuitOutputPrefixTokens
            inputs gates output ++
          [.outputsEnd, token] ++ suffix) ++
      workTail).length
  have prefixRun :=
    circuitOutputPrefixWord_exact inputs gates output
      ([cell10, cell01] ++ tokenWord)
  have delimiter :=
    outputsEnd_exact parsedPrefix tokenWord
  have through :=
    exactRun_add
      (circuitOutputPrefixWordSteps inputs gates output)
      2 _ _ _
      (by
        simpa [parsedPrefix, tokenWord] using prefixRun)
      delimiter
  have throughCanonical :
      workRunExact? machine
          (circuitOutputPrefixWordSteps inputs gates output + 2)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (SourceParser.circuitOutputPrefixTokens
                      inputs gates output ++
                    [.outputsEnd, token] ++ suffix) ++
                workTail))) =
        some
          (guardedConfig State.instanceEndFirst
            afterOutputs tokenWord) := by
    simpa [parsedPrefix, afterOutputs, tokenWord,
      packedTokenCells_append,
      SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      cell10, cell01,
      SourceParser.cell10,
      SourceParser.cell01,
      List.append_assoc] using through
  have afterSafe : SafeSourceWord afterOutputs := by
    apply safe_append
      (outputParsedPrefix_safe inputs gates output)
    intro symbol member
    simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with rfl | rfl | impossible
    · decide
    · decide
    · contradiction
  have tail :=
    instanceEndWrongTokenWithMalformedTail_bounded_exact
      afterOutputs afterSafe token suffix
      notInstanceEnd malformed
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output + 2)
      (16 *
        (afterOutputs.length + tokenWord.length + 1))
      _ _ throughCanonical
      (by simpa [tokenWord] using tail)
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
        inputs gates output)).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    repeat rw [packedTokenCells_append]
    simp
  have baseCost :
      circuitOutputPrefixWordSteps inputs gates output ≤
        25 * grammarCellCube cells :=
    Nat.le_trans
      (circuitOutputPrefixWordSteps_le_cube
        inputs gates output)
      (Nat.mul_le_mul_left 25
        (grammarCellCube_mono prefixLe))
  have prefixCost :
      circuitOutputPrefixWordSteps inputs gates output + 2 ≤
        27 * grammarCellCube cells := by
    have one := one_le_grammarCellCube cells
    omega
  have spanEq :
      afterOutputs.length + tokenWord.length + 1 =
        cells + 1 := by
    have parsedLength :=
      outputParsedPrefix_length_eq_packed
        inputs gates output
    dsimp [afterOutputs, parsedPrefix, tokenWord, cells]
    repeat rw [packedTokenCells_append]
    simp only [List.length_append, List.length_cons,
      List.length_nil] at parsedLength ⊢
    simp [SourceParser.packedTokenCells,
      SourceParser.tokenCells] at parsedLength ⊢
    omega
  exact linearJoin_le_grammarCellCube
    cells
    (circuitOutputPrefixWordSteps inputs gates output + 2)
    (afterOutputs.length + tokenWord.length + 1)
    27 16 prefixCost spanEq (by omega)

private theorem circuitTrailingTokenWithMalformedTail_bounded_exact
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) (token : Token)
    (suffix : List Token)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let cells :=
      (SourceParser.packedTokenCells
          (SourceParser.circuitOutputPrefixTokens
              inputs gates output ++
            [.outputsEnd, .instanceEnd, token] ++ suffix) ++
        workTail).length
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (SourceParser.circuitOutputPrefixTokens
                  inputs gates output ++
                [.outputsEnd, .instanceEnd, token] ++ suffix) ++
            workTail)))
      (4096 * grammarCellCube cells) := by
  dsimp only
  let parsedPrefix :=
    outputPrefix inputs gates ++ sourceCells output
  let afterOutputs :=
    parsedPrefix ++ [cell10, cell01]
  let afterInstance :=
    afterOutputs ++ [cell10, cell11]
  let tokenWord :=
    SourceParser.packedTokenCells (token :: suffix) ++
      workTail
  let cells :=
    (SourceParser.packedTokenCells
        (SourceParser.circuitOutputPrefixTokens
            inputs gates output ++
          [.outputsEnd, .instanceEnd, token] ++ suffix) ++
      workTail).length
  have prefixRun :=
    circuitOutputPrefixWord_exact inputs gates output
      ([cell10, cell01, cell10, cell11] ++ tokenWord)
  have outputsRun :=
    outputsEnd_exact parsedPrefix
      ([cell10, cell11] ++ tokenWord)
  have instanceRun :=
    instanceEnd_exact afterOutputs tokenWord
  have throughOutputs :=
    exactRun_add
      (circuitOutputPrefixWordSteps inputs gates output)
      2 _ _ _
      (by
        simpa [parsedPrefix, tokenWord] using prefixRun)
      outputsRun
  have throughInstance :=
    exactRun_add
      (circuitOutputPrefixWordSteps inputs gates output + 2)
      2 _ _ _
      (by
        simpa [afterOutputs,
          List.append_assoc] using throughOutputs)
      instanceRun
  have throughCanonical :
      workRunExact? machine
          (circuitOutputPrefixWordSteps inputs gates output + 2 + 2)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (SourceParser.circuitOutputPrefixTokens
                      inputs gates output ++
                    [.outputsEnd, .instanceEnd, token] ++ suffix) ++
                workTail))) =
        some
          (guardedConfig State.finalEOF
            afterInstance tokenWord) := by
    simpa [parsedPrefix, afterOutputs, afterInstance,
      tokenWord, packedTokenCells_append,
      SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      cell10, cell01, cell11,
      SourceParser.cell10, SourceParser.cell01,
      SourceParser.cell11,
      List.append_assoc] using throughInstance
  have afterSafe : SafeSourceWord afterInstance := by
    apply safe_append
    · apply safe_append
        (outputParsedPrefix_safe inputs gates output)
      intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | rfl | impossible
      · decide
      · decide
      · contradiction
    · intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | rfl | impossible
      · decide
      · decide
      · contradiction
  have tokenWordSafe : SafeSourceWord tokenWord :=
    safe_append
      (packedTokenCells_safe (token :: suffix))
      (malformedWorkTail_safe malformed)
  have tokenWordNonempty : tokenWord ≠ [] := by
    intro empty
    have lengthEq := congrArg List.length empty
    dsimp [tokenWord] at lengthEq
    simp only [List.length_append,
      SourceParser.packedTokenCells,
      SourceParser.tokenCells_length] at lengthEq
    omega
  have tail :=
    finalEOFWord_bounded_exact
      afterInstance tokenWord afterSafe
      tokenWordSafe tokenWordNonempty
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitOutputPrefixWordSteps inputs gates output + 2 + 2)
      (16 *
        (afterInstance.length + tokenWord.length + 1))
      _ _ throughCanonical tail
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
        inputs gates output)).length
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    repeat rw [packedTokenCells_append]
    simp
  have baseCost :
      circuitOutputPrefixWordSteps inputs gates output ≤
        25 * grammarCellCube cells :=
    Nat.le_trans
      (circuitOutputPrefixWordSteps_le_cube
        inputs gates output)
      (Nat.mul_le_mul_left 25
        (grammarCellCube_mono prefixLe))
  have prefixCost :
      circuitOutputPrefixWordSteps inputs gates output + 2 + 2 ≤
        29 * grammarCellCube cells := by
    have one := one_le_grammarCellCube cells
    omega
  have spanEq :
      afterInstance.length + tokenWord.length + 1 =
        cells + 1 := by
    have parsedLength :=
      outputParsedPrefix_length_eq_packed
        inputs gates output
    dsimp [afterInstance, afterOutputs, parsedPrefix,
      tokenWord, cells]
    repeat rw [packedTokenCells_append]
    simp only [List.length_append, List.length_cons,
      List.length_nil] at parsedLength ⊢
    simp [SourceParser.packedTokenCells,
      SourceParser.tokenCells] at parsedLength ⊢
    omega
  exact linearJoin_le_grammarCellCube
    cells
    (circuitOutputPrefixWordSteps inputs gates output + 2 + 2)
    (afterInstance.length + tokenWord.length + 1)
    29 16 prefixCost spanEq (by omega)

private theorem circuitTokenFailureWithMalformedTail_bounded_exact
    {tokens : List Token}
    (failure : SourceParser.CircuitTokenFailure tokens)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells tokens ++ workTail)))
      (4096 *
        grammarCellCube
          (SourceParser.packedTokenCells tokens ++
            workTail).length) := by
  cases failure with
  | missingVersion =>
      simpa [SourceParser.packedTokenCells] using
        circuitMissingVersionWithMalformedTail_bounded_exact
          malformed
  | wrongVersion token suffix notVersion =>
      simpa using
        circuitWrongVersionWithMalformedTail_bounded_exact
          token suffix notVersion malformed
  | inputCount failure =>
      simpa using
        circuitInputCountWithMalformedTail_bounded_exact
          failure malformed
  | gateCount inputs failure =>
      simpa using
        circuitGateCountWithMalformedTail_bounded_exact
          inputs failure malformed
  | gates inputs gateCount failure =>
      simpa using
        circuitGatesWithMalformedTail_bounded_exact
          inputs gateCount failure malformed
  | missingProgramEnd inputs gates =>
      simpa using
        circuitMissingProgramEndWithMalformedTail_bounded_exact
          inputs gates malformed
  | wrongProgramEnd inputs gates token suffix notProgramEnd =>
      simpa using
        circuitWrongProgramEndWithMalformedTail_bounded_exact
          inputs gates token suffix notProgramEnd malformed
  | output inputs gates failure =>
      simpa using
        circuitOutputWithMalformedTail_bounded_exact
          inputs gates failure malformed
  | missingOutputsEnd inputs gates output =>
      simpa using
        circuitMissingOutputsEndWithMalformedTail_bounded_exact
          inputs gates output malformed
  | wrongOutputsEnd inputs gates output token suffix
      notOutputsEnd =>
      simpa using
        circuitWrongOutputsEndWithMalformedTail_bounded_exact
          inputs gates output token suffix notOutputsEnd malformed
  | missingInstanceEnd inputs gates output =>
      simpa using
        circuitMissingInstanceEndWithMalformedTail_bounded_exact
          inputs gates output malformed
  | wrongInstanceEnd inputs gates output token suffix
      notInstanceEnd =>
      simpa using
        circuitWrongInstanceEndWithMalformedTail_bounded_exact
          inputs gates output token suffix notInstanceEnd malformed
  | trailingToken inputs gates output token suffix =>
      simpa using
        circuitTrailingTokenWithMalformedTail_bounded_exact
          inputs gates output token suffix malformed

private theorem canonicalCircuitWithMalformedTail_bounded_exact
    (raw : RawCircuit)
    {rawTail : BitString} {workTail : List WorkSymbol}
    (malformed :
      SourceParser.MalformedWorkTail rawTail workTail) :
    let cells :=
      (SourceParser.packedTokenCells
          (encodeCircuitTokens raw) ++
        workTail).length
    BoundedRejectingExecution
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (SourceParser.packedTokenCells
              (encodeCircuitTokens raw) ++
            workTail)))
      (4096 * grammarCellCube cells) := by
  dsimp only
  let parsedPrefix :=
    outputPrefix raw.inputCount raw.gates ++
      sourceCells raw.output
  let afterOutputs :=
    parsedPrefix ++ [cell10, cell01]
  let afterInstance :=
    afterOutputs ++ [cell10, cell11]
  let cells :=
    (SourceParser.packedTokenCells
        (encodeCircuitTokens raw) ++
      workTail).length
  have prefixRun :=
    circuitOutputPrefixWord_exact
      raw.inputCount raw.gates raw.output
      ([cell10, cell01, cell10, cell11] ++ workTail)
  have outputsRun :=
    outputsEnd_exact parsedPrefix
      ([cell10, cell11] ++ workTail)
  have instanceRun :=
    instanceEnd_exact afterOutputs workTail
  have throughOutputs :=
    exactRun_add
      (circuitOutputPrefixWordSteps
        raw.inputCount raw.gates raw.output)
      2 _ _ _
      (by simpa [parsedPrefix] using prefixRun)
      outputsRun
  have throughInstance :=
    exactRun_add
      (circuitOutputPrefixWordSteps
          raw.inputCount raw.gates raw.output + 2)
      2 _ _ _
      (by
        simpa [afterOutputs, List.append_assoc] using
          throughOutputs)
      instanceRun
  have throughCanonical :
      workRunExact? machine
          (circuitOutputPrefixWordSteps
            raw.inputCount raw.gates raw.output + 2 + 2)
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (SourceParser.packedTokenCells
                  (encodeCircuitTokens raw) ++
                workTail))) =
        some
          (guardedConfig State.finalEOF
            afterInstance workTail) := by
    rw [show
      encodeCircuitTokens raw =
        SourceParser.circuitOutputPrefixTokens
            raw.inputCount raw.gates raw.output ++
          [.outputsEnd, .instanceEnd] by
        simp [encodeCircuitTokens,
          SourceParser.circuitOutputPrefixTokens,
          SourceParser.circuitGatesPrefixTokens,
          SourceParser.circuitHeaderTokens,
          List.append_assoc]]
    repeat rw [packedTokenCells_append]
    simpa [parsedPrefix, afterOutputs, afterInstance,
      SourceParser.packedTokenCells,
      SourceParser.tokenCells,
      cell10, cell01, cell11,
      SourceParser.cell10, SourceParser.cell01,
      SourceParser.cell11,
      List.append_assoc] using throughInstance
  have afterSafe : SafeSourceWord afterInstance := by
    apply safe_append
    · apply safe_append
        (outputParsedPrefix_safe
          raw.inputCount raw.gates raw.output)
      intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | rfl | impossible
      · decide
      · decide
      · contradiction
    · intro symbol member
      simp only [List.mem_cons,
        List.not_mem_nil] at member
      rcases member with rfl | rfl | impossible
      · decide
      · decide
      · contradiction
  have tail :=
    simpleMalformedBoundary_bounded_exact
      .finalEOF afterInstance afterSafe malformed
  have joined :=
    BoundedRejectingExecution.prepend
      (circuitOutputPrefixWordSteps
        raw.inputCount raw.gates raw.output + 2 + 2)
      (16 *
        (afterInstance.length + workTail.length + 1))
      _ _ throughCanonical
      (by simpa [SimpleMalformedBoundary.state] using tail)
  apply BoundedRejectingExecution.widen joined
  let prefixCells :=
    (SourceParser.packedTokenCells
      (SourceParser.circuitOutputPrefixTokens
        raw.inputCount raw.gates raw.output)).length
  have tokensEq :
      encodeCircuitTokens raw =
        SourceParser.circuitOutputPrefixTokens
            raw.inputCount raw.gates raw.output ++
          [.outputsEnd, .instanceEnd] := by
    simp [encodeCircuitTokens,
      SourceParser.circuitOutputPrefixTokens,
      SourceParser.circuitGatesPrefixTokens,
      SourceParser.circuitHeaderTokens,
      List.append_assoc]
  have prefixLe : prefixCells ≤ cells := by
    dsimp [prefixCells, cells]
    rw [tokensEq]
    repeat rw [packedTokenCells_append]
    simp
  have baseCost :
      circuitOutputPrefixWordSteps
          raw.inputCount raw.gates raw.output ≤
        25 * grammarCellCube cells :=
    Nat.le_trans
      (circuitOutputPrefixWordSteps_le_cube
        raw.inputCount raw.gates raw.output)
      (Nat.mul_le_mul_left 25
        (grammarCellCube_mono prefixLe))
  have prefixCost :
      circuitOutputPrefixWordSteps
          raw.inputCount raw.gates raw.output + 2 + 2 ≤
        29 * grammarCellCube cells := by
    have one := one_le_grammarCellCube cells
    omega
  have spanEq :
      afterInstance.length + workTail.length + 1 =
        cells + 1 := by
    have parsedLength :=
      outputParsedPrefix_length_eq_packed
        raw.inputCount raw.gates raw.output
    dsimp [afterInstance, afterOutputs, parsedPrefix, cells]
    rw [tokensEq]
    repeat rw [packedTokenCells_append]
    simp only [List.length_append, List.length_cons,
      List.length_nil] at parsedLength ⊢
    simp [SourceParser.packedTokenCells,
      SourceParser.tokenCells] at parsedLength ⊢
    omega
  exact linearJoin_le_grammarCellCube
    cells
    (circuitOutputPrefixWordSteps
      raw.inputCount raw.gates raw.output + 2 + 2)
    (afterInstance.length + workTail.length + 1)
    29 16 prefixCost spanEq (by omega)

private theorem framingFailure_bounded_exact
    (bits : BitString)
    (failure : SourceParser.TokenDecodeFailure bits) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (rawInputWorkTape bits))
      (grammarWorkBound bits.length) := by
  rcases failure.packedShape with
    ⟨tokens, rawTail, workTail, malformed,
      _bitsEq, packedEq⟩
  have packedTokensEq :
      SourceParser.packedRawBits (encodeTokens tokens) =
        SourceParser.packedTokenCells tokens := by
    simpa [SourceParser.packedRawBits] using
      SourceParser.pack_encodeTokens tokens
  have inputEq :
      rawInputWorkTape bits =
        WorkTape.ofSymbols
          (SourceParser.packedTokenCells tokens ++
            workTail) := by
    unfold rawInputWorkTape
    change
      WorkTape.ofSymbols
          (SourceParser.packedRawBits bits) =
        WorkTape.ofSymbols
          (SourceParser.packedTokenCells tokens ++
            workTail)
    rw [packedEq, packedTokensEq]
  have rejection :
      BoundedRejectingExecution
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            (SourceParser.packedTokenCells tokens ++
              workTail)))
        (4096 *
          grammarCellCube
            (SourceParser.packedTokenCells tokens ++
              workTail).length) := by
    cases circuitEq : decodeCircuitTokens tokens with
    | none =>
        have grammarFailure :=
          (SourceParser.decodeCircuitTokens_eq_none_iff_failure
            tokens).mp circuitEq
        exact
          circuitTokenFailureWithMalformedTail_bounded_exact
            grammarFailure malformed
    | some raw =>
        have tokensEq :=
          encodeCircuitTokens_eq_of_decodeCircuitTokens_eq_some
            tokens raw circuitEq
        simpa [tokensEq] using
          (canonicalCircuitWithMalformedTail_bounded_exact
            raw malformed)
  rw [inputEq]
  apply BoundedRejectingExecution.widen rejection
  have packedLengthEq :
      (SourceParser.packedTokenCells tokens ++
          workTail).length =
        (SourceParser.packedRawBits bits).length := by
    have lengthEq := congrArg List.length packedEq
    rw [packedTokensEq] at lengthEq
    omega
  have packedLe :
      (SourceParser.packedTokenCells tokens ++
          workTail).length ≤
        bits.length := by
    rw [packedLengthEq]
    exact SourceParser.packedRawBits_length_le bits
  have cubeBound := grammarCellCube_mono packedLe
  have scaled := Nat.mul_le_mul_left 4096 cubeBound
  simpa [grammarWorkBound, grammarCellCube,
    SourceParser.validWorkBound, Nat.mul_assoc] using scaled

private theorem malformed_bounded_execution
    (bits : BitString)
    (malformed : decodeCircuit bits = none) :
    BoundedRejectingExecution
      (workStartConfiguration machine
        (rawInputWorkTape bits))
      (grammarWorkBound bits.length) := by
  cases tokenEq : decodeTokens bits with
  | none =>
      have framingFailure :=
        (SourceParser.decodeTokens_eq_none_iff_failure
          bits).mp tokenEq
      exact framingFailure_bounded_exact bits framingFailure
  | some tokens =>
      have grammarMalformed :
          decodeCircuitTokens tokens = none := by
        unfold decodeCircuit at malformed
        rw [tokenEq] at malformed
        exact malformed
      have grammarFailure :=
        (SourceParser.decodeCircuitTokens_eq_none_iff_failure
          tokens).mp grammarMalformed
      have rejection :=
        circuitTokenFailure_bounded_exact grammarFailure
      have bitsEq :=
        encodeTokens_eq_of_decodeTokens_eq_some
          bits tokens tokenEq
      have inputEq :
          rawInputWorkTape bits =
            WorkTape.ofSymbols
              (SourceParser.packedTokenCells tokens) := by
        rw [← bitsEq]
        unfold rawInputWorkTape
        rw [SourceParser.pack_encodeTokens]
      rw [inputEq]
      apply BoundedRejectingExecution.widen rejection
      have packedLe :
          (SourceParser.packedTokenCells tokens).length ≤
            bits.length := by
        have packedEq :
            SourceParser.packedRawBits
                (encodeTokens tokens) =
              SourceParser.packedTokenCells tokens := by
          simpa [SourceParser.packedRawBits] using
            SourceParser.pack_encodeTokens tokens
        rw [← bitsEq, ← packedEq]
        exact SourceParser.packedRawBits_length_le
          (encodeTokens tokens)
      have cubeBound := grammarCellCube_mono packedLe
      have scaled := Nat.mul_le_mul_left 4096 cubeBound
      simpa [grammarWorkBound, grammarCellCube,
        SourceParser.validWorkBound, Nat.mul_assoc] using scaled

/-- Every strict-v0 decoder failure has a constructively exhibited scanner
rejection within the public cubic bit-length envelope.  The witness is built
from the literal grammar and cleanup traces; no caller certificate or
host-side decoder lookup is used by the machine. -/
theorem malformed_bounded_exact
    (bits : BitString)
    (malformed : decodeCircuit bits = none) :
    ∃ steps final,
      steps ≤ grammarWorkBound bits.length ∧
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      machine.isHalted final = true ∧
      final.state = State.reject ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  exact malformed_bounded_execution bits malformed

end PNP.Concrete.LockedNAND.TargetEmitterGrammarScanner

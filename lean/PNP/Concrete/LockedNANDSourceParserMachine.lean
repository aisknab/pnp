/-
Copyright (c) 2026 PNP Labs.

A literal finite work machine for the strict-v0 locked-NAND source grammar.
The machine consumes the packed `rawInputWorkTape` layout: each work cell
holds two consecutive source bits.  Valid encodings therefore contain exactly
two ordinary work cells per four-bit token.

The executable rule table does not call the semantic decoder.  It recognizes
the token grammar directly, crosses unary source indices against the declared
input count or the already completed gate anchors, and crosses the number of
parsed gates against the declared gate count.  All temporary marks have one
statically known original cell, so the successful path restores the source
word exactly.  Every malformed path first erases the guarded source region and
only then enters the reject halt.
-/

import PNP.Concrete.LockedNANDSourceParserSpec
import PNP.Concrete.TapeBlankEquivalence

namespace PNP.Concrete.LockedNAND.SourceParser

/-! ### Fixed work alphabet and marker discipline -/

def cellBlank : WorkSymbol := WorkSymbol.blank
def leftGuard : WorkSymbol := WorkSymbol.blankZero
def cursorMark : WorkSymbol := WorkSymbol.blankOne
def cell00 : WorkSymbol := WorkSymbol.zeroZero
def cell01 : WorkSymbol := WorkSymbol.zeroOne
def countMark : WorkSymbol := WorkSymbol.zeroBlank
def cell10 : WorkSymbol := WorkSymbol.oneZero
def cell11 : WorkSymbol := WorkSymbol.oneOne
def gateMark : WorkSymbol := WorkSymbol.oneBlank

/-- Compiler-order enumeration of the complete nine-symbol work alphabet. -/
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

inductive ReferenceBound where
  | input
  | priorGate
deriving BEq, DecidableEq, Repr

namespace ReferenceBound

def code : ReferenceBound → Nat
  | .input => 0
  | .priorGate => 1

def all : List ReferenceBound :=
  [.input, .priorGate]

end ReferenceBound

/-! ### Disjoint finite state namespace -/

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
  60 + 4 * continuation.code

def sourceStart (continuation : SourceContinuation) : Nat :=
  sourceBase continuation

def sourceAfter00 (continuation : SourceContinuation) : Nat :=
  sourceBase continuation + 1

def sourceAfter01 (continuation : SourceContinuation) : Nat :=
  sourceBase continuation + 2

private def referenceCode (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  3 * bound.code + continuation.code

private def referenceBase (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  100 + 32 * referenceCode bound continuation

def indexFirst (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation

def indexSecond (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 1

def consumeSeekGuard (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 2

def consumeInputVersionFirst (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 3

def consumeInputVersionSecond (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 4

def consumeInputFirst (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 5

def consumeInputSecond (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 6

def consumeGateAnchor (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 7

def consumeSeekCursor (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 8

def finishSeekGuard (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 9

def finishInputVersionFirst (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 10

def finishInputVersionSecond (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 11

def finishInputCheckFirst (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 12

def finishInputCheckSecond (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 13

def finishInputReturnGuard (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 14

def finishInputRestoreVersionFirst (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 15

def finishInputRestoreVersionSecond (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 16

def finishInputRestoreFirst (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 17

def finishInputRestoreSecond (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 18

def finishGateCheckAnchor (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 19

def finishGateReturnGuard (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 20

def finishGateVersionFirst (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 21

def finishGateVersionSecond (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 22

def finishGateInputFirst (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 23

def finishGateInputSecond (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 24

def finishGateCountFirst (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 25

def finishGateCountSecond (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 26

def finishGateRestore (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 27

def finishInputSeekCursor (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  referenceBase bound continuation + 28

end State

/-! ### Total nine-way state programs -/

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

private def afterSourceState : SourceContinuation → Nat
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
        (keepAction (State.indexFirst .input continuation)
          .right cell11) }
  , { state := State.sourceAfter01 continuation
      action := expectThree cell00 cell01 cell10
        (keepAction (afterSourceState continuation) .right cell00)
        (keepAction (afterSourceState continuation) .right cell01)
        (keepAction (State.indexFirst .priorGate continuation)
          .right cell10) }
  ]

private def allSourcePrograms : List StateProgram :=
  SourceContinuation.all.flatMap sourcePrograms

private def referencePrograms (bound : ReferenceBound)
    (continuation : SourceContinuation) : List StateProgram :=
  [ { state := State.indexFirst bound continuation
      action := expectOne cell00
        (keepAction (State.indexSecond bound continuation)
          .right cell00) }
  , { state := State.indexSecond bound continuation
      action := expectTwo cell01 cell10
        (writeAction (State.consumeSeekGuard bound continuation)
          cursorMark .left)
        (writeAction (State.finishSeekGuard bound continuation)
          cursorMark .left) }
  , { state := State.consumeSeekGuard bound continuation
      action := fun symbol =>
        if symbol == leftGuard then
          match bound with
          | .input =>
              keepAction
                (State.consumeInputVersionFirst bound continuation)
                .right symbol
          | .priorGate =>
              keepAction (State.consumeGateAnchor bound continuation)
                .right symbol
        else
          keepAction (State.consumeSeekGuard bound continuation)
            .left symbol }
  , { state := State.consumeInputVersionFirst bound continuation
      action := expectOne cell00
        (keepAction
          (State.consumeInputVersionSecond bound continuation)
          .right cell00) }
  , { state := State.consumeInputVersionSecond bound continuation
      action := expectOne cell00
        (keepAction (State.consumeInputFirst bound continuation)
          .right cell00) }
  , { state := State.consumeInputFirst bound continuation
      action := expectOne cell00
        (keepAction (State.consumeInputSecond bound continuation)
          .right cell00) }
  , { state := State.consumeInputSecond bound continuation
      action := fun symbol =>
        if symbol == countMark then
          keepAction (State.consumeInputFirst bound continuation)
            .right symbol
        else if symbol == cell01 then
          writeAction (State.consumeSeekCursor bound continuation)
            countMark .right
        else
          cleanupAction symbol }
  , { state := State.consumeGateAnchor bound continuation
      action := fun symbol =>
        if symbol == gateMark then
          writeAction (State.consumeSeekCursor bound continuation)
            countMark .right
        else if symbol == cursorMark then
          cleanupAction symbol
        else if symbol == cellBlank then
          cleanupAction symbol
        else
          keepAction (State.consumeGateAnchor bound continuation)
            .right symbol }
  , { state := State.consumeSeekCursor bound continuation
      action := fun symbol =>
        if symbol == cursorMark then
          writeAction (State.indexFirst bound continuation)
            cell01 .right
        else if symbol == cellBlank then
          cleanupAction symbol
        else
          keepAction (State.consumeSeekCursor bound continuation)
            .right symbol }
  , { state := State.finishSeekGuard bound continuation
      action := fun symbol =>
        if symbol == leftGuard then
          match bound with
          | .input =>
              keepAction
                (State.finishInputVersionFirst bound continuation)
                .right symbol
          | .priorGate =>
              keepAction
                (State.finishGateCheckAnchor bound continuation)
                .right symbol
        else
          keepAction (State.finishSeekGuard bound continuation)
            .left symbol }
  , { state := State.finishInputVersionFirst bound continuation
      action := expectOne cell00
        (keepAction
          (State.finishInputVersionSecond bound continuation)
          .right cell00) }
  , { state := State.finishInputVersionSecond bound continuation
      action := expectOne cell00
        (keepAction (State.finishInputCheckFirst bound continuation)
          .right cell00) }
  , { state := State.finishInputCheckFirst bound continuation
      action := expectOne cell00
        (keepAction (State.finishInputCheckSecond bound continuation)
          .right cell00) }
  , { state := State.finishInputCheckSecond bound continuation
      action := fun symbol =>
        if symbol == countMark then
          keepAction (State.finishInputCheckFirst bound continuation)
            .right symbol
        else if symbol == cell01 then
          keepAction (State.finishInputReturnGuard bound continuation)
            .left symbol
        else
          cleanupAction symbol }
  , { state := State.finishInputReturnGuard bound continuation
      action := fun symbol =>
        if symbol == leftGuard then
          keepAction
            (State.finishInputRestoreVersionFirst bound continuation)
            .right symbol
        else
          keepAction (State.finishInputReturnGuard bound continuation)
            .left symbol }
  , { state := State.finishInputRestoreVersionFirst bound continuation
      action := expectOne cell00
        (keepAction
          (State.finishInputRestoreVersionSecond bound continuation)
          .right cell00) }
  , { state := State.finishInputRestoreVersionSecond bound continuation
      action := expectOne cell00
        (keepAction
          (State.finishInputRestoreFirst bound continuation)
          .right cell00) }
  , { state := State.finishInputRestoreFirst bound continuation
      action := expectOne cell00
        (keepAction
          (State.finishInputRestoreSecond bound continuation)
          .right cell00) }
  , { state := State.finishInputRestoreSecond bound continuation
      action := fun symbol =>
        if symbol == countMark then
          writeAction
            (State.finishInputRestoreFirst bound continuation)
            cell01 .right
        else if symbol == cell01 then
          keepAction
            (State.finishInputRestoreFirst bound continuation)
            .right symbol
        else if symbol == cell10 then
          keepAction
            (State.finishInputSeekCursor bound continuation)
            .right symbol
        else
          cleanupAction symbol }
  , { state := State.finishGateCheckAnchor bound continuation
      action := fun symbol =>
        if symbol == gateMark then
          keepAction (State.finishGateReturnGuard bound continuation)
            .left symbol
        else if symbol == cursorMark then
          cleanupAction symbol
        else if symbol == cellBlank then
          cleanupAction symbol
        else
          keepAction (State.finishGateCheckAnchor bound continuation)
            .right symbol }
  , { state := State.finishGateReturnGuard bound continuation
      action := fun symbol =>
        if symbol == leftGuard then
          keepAction (State.finishGateVersionFirst bound continuation)
            .right symbol
        else
          keepAction (State.finishGateReturnGuard bound continuation)
            .left symbol }
  , { state := State.finishGateVersionFirst bound continuation
      action := expectOne cell00
        (keepAction
          (State.finishGateVersionSecond bound continuation)
          .right cell00) }
  , { state := State.finishGateVersionSecond bound continuation
      action := expectOne cell00
        (keepAction (State.finishGateInputFirst bound continuation)
          .right cell00) }
  , { state := State.finishGateInputFirst bound continuation
      action := expectOne cell00
        (keepAction (State.finishGateInputSecond bound continuation)
          .right cell00) }
  , { state := State.finishGateInputSecond bound continuation
      action := expectTwo cell01 cell10
        (keepAction (State.finishGateInputFirst bound continuation)
          .right cell01)
        (keepAction (State.finishGateCountFirst bound continuation)
          .right cell10) }
  , { state := State.finishGateCountFirst bound continuation
      action := expectOne cell00
        (keepAction (State.finishGateCountSecond bound continuation)
          .right cell00) }
  , { state := State.finishGateCountSecond bound continuation
      action := expectThree countMark cell01 cell10
        (keepAction (State.finishGateCountFirst bound continuation)
          .right countMark)
        (keepAction (State.finishGateCountFirst bound continuation)
          .right cell01)
        (keepAction (State.finishGateRestore bound continuation)
          .right cell10) }
  , { state := State.finishGateRestore bound continuation
      action := fun symbol =>
        if symbol == countMark then
          writeAction (State.finishGateRestore bound continuation)
            gateMark .right
        else if symbol == cursorMark then
          writeAction (afterSourceState continuation) cell10 .right
        else if symbol == cellBlank then
          cleanupAction symbol
        else
          keepAction (State.finishGateRestore bound continuation)
            .right symbol }
  , { state := State.finishInputSeekCursor bound continuation
      action := fun symbol =>
        if symbol == cursorMark then
          writeAction (afterSourceState continuation) cell10 .right
        else if symbol == cellBlank then
          cleanupAction symbol
        else
          keepAction (State.finishInputSeekCursor bound continuation)
            .right symbol }
  ]

private def allReferencePrograms : List StateProgram :=
  ReferenceBound.all.flatMap (fun bound =>
    SourceContinuation.all.flatMap (referencePrograms bound))

/-- Complete fixed state program.  Its functions are evaluated only while
materializing the literal list of `WorkRule` records below; they are not part
of the resulting machine's executable syntax. -/
def statePrograms : List StateProgram :=
  corePrograms ++ allGateDecrementPrograms ++ allSourcePrograms ++
    allReferencePrograms

/-- The complete literal finite rule table.  Every listed control state has
exactly one transition for each of the nine work symbols. -/
def rules : List WorkRule :=
  statePrograms.flatMap stateRules

/-- Standalone parser/validator over `rawInputWorkTape`. -/
def machine : WorkMachine :=
  { rules := rules
    startState := State.boot
    acceptState := State.accept
    rejectState := State.reject }

/-- Literal three-symbol single-tape compilation of the standalone parser. -/
def compiledMachine : Machine :=
  compileWorkMachine machine

/-- Query distinctness is the determinism property used by later exact-trace
proofs and by machine composition. -/
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

/-- No two literal rules compete for the same state/symbol query. -/
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

theorem statePrograms_length :
    statePrograms.length = 228 := by
  rfl

/-- Exact literal rule count: 228 control states times nine work symbols. -/
def ruleCount : Nat := 2052

theorem rules_length : rules.length = ruleCount := by
  change (statePrograms.flatMap stateRules).length = 2052
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

end PNP.Concrete.LockedNAND.SourceParser

/-
Copyright (c) 2026 PNP Labs.

Literal terminal raw-output packing for the boundary-marked pipeline.

The finite work machine below consumes the canonical represented-output
handoff layout.  It groups consecutive logical bits into the two raw cells of
one work symbol, so the ordinary compilation of the final work tape contains
one contiguous raw bit prefix followed by a blank delimiter.  Arbitrary cells
outside both input boundaries are permitted and remain outside the observable
output.

This module is only the terminal packing stage.  It does not prove termination
of an arbitrary simulated target, compose the complete pipeline, establish a
RawRefinement, supply an external encoded-input-size polynomial for that
pipeline, prove CNF-SAT in P or NP-completeness, or prove P = NP.
-/

import PNP.Concrete.PipelineOutputHandoff
import PNP.Concrete.Complexity

namespace PNP.Concrete

namespace TerminalOutputPacker

open PipelineTape

/-! ### Finite control and literal rule table -/

def allWorkSymbols : List WorkSymbol :=
  [WorkSymbol.blank, WorkSymbol.blankZero, WorkSymbol.blankOne,
   WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
   WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

def outputSymbols : List WorkSymbol :=
  [WorkSymbol.zeroBlank, WorkSymbol.oneBlank,
   WorkSymbol.zeroZero, WorkSymbol.zeroOne,
   WorkSymbol.oneZero, WorkSymbol.oneOne]

def sourceBlankSymbols : List WorkSymbol :=
  [WorkSymbol.blank, WorkSymbol.zeroBlank, WorkSymbol.oneBlank]

def startState : Nat := 0
def seekPackedState : Nat := 1
def rememberFirstZeroState : Nat := 2
def rememberFirstOneState : Nat := 3
def rememberPackedZeroState : Nat := 4
def rememberPackedOneState : Nat := 5

def firstCarryZeroZeroState : Nat := 6
def firstCarryZeroOneState : Nat := 7
def firstCarryOneZeroState : Nat := 8
def firstCarryOneOneState : Nat := 9

def firstWriteZeroState : Nat := 10
def firstWriteOneState : Nat := 11
def firstWriteZeroZeroState : Nat := 12
def firstWriteZeroOneState : Nat := 13
def firstWriteOneZeroState : Nat := 14
def firstWriteOneOneState : Nat := 15

def packedCarryZeroZeroState : Nat := 16
def packedCarryZeroOneState : Nat := 17
def packedCarryOneZeroState : Nat := 18
def packedCarryOneOneState : Nat := 19

def seekOuterZeroState : Nat := 20
def seekOuterOneState : Nat := 21
def seekOuterZeroZeroState : Nat := 22
def seekOuterZeroOneState : Nat := 23
def seekOuterOneZeroState : Nat := 24
def seekOuterOneOneState : Nat := 25

def installOuterState : Nat := 26
def returnOutputState : Nat := 27
def returnSourceState : Nat := 28
def acceptState : Nat := 29
def rejectState : Nat := 30

def firstRememberState : Bool → Nat
  | false => rememberFirstZeroState
  | true => rememberFirstOneState

def packedRememberState : Bool → Nat
  | false => rememberPackedZeroState
  | true => rememberPackedOneState

def firstCarryState : Bool → Bool → Nat
  | false, false => firstCarryZeroZeroState
  | false, true => firstCarryZeroOneState
  | true, false => firstCarryOneZeroState
  | true, true => firstCarryOneOneState

def firstWriteSingleState : Bool → Nat
  | false => firstWriteZeroState
  | true => firstWriteOneState

def firstWritePairState : Bool → Bool → Nat
  | false, false => firstWriteZeroZeroState
  | false, true => firstWriteZeroOneState
  | true, false => firstWriteOneZeroState
  | true, true => firstWriteOneOneState

def packedCarryState : Bool → Bool → Nat
  | false, false => packedCarryZeroZeroState
  | false, true => packedCarryZeroOneState
  | true, false => packedCarryOneZeroState
  | true, true => packedCarryOneOneState

def seekOuterSingleState : Bool → Nat
  | false => seekOuterZeroState
  | true => seekOuterOneState

def seekOuterPairState : Bool → Bool → Nat
  | false, false => seekOuterZeroZeroState
  | false, true => seekOuterZeroOneState
  | true, false => seekOuterOneZeroState
  | true, true => seekOuterOneOneState

def keepRule (source : Nat) (read : WorkSymbol) (target : Nat)
    (move : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := read
    move := move }

def writeRule (source : Nat) (read : WorkSymbol) (target : Nat)
    (write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

def writeAllRules (source target : Nat) (write : WorkSymbol)
    (move : HeadMove) : List WorkRule :=
  allWorkSymbols.map (fun read =>
    writeRule source read target write move)

def carryRules (source writeState : Nat) : List WorkRule :=
  [keepRule source WorkSymbol.zeroBlank source .right,
   keepRule source WorkSymbol.oneBlank source .right,
   keepRule source rightMarker writeState .right]

def seekOuterRules (source : Nat) (write : WorkSymbol) : List WorkRule :=
  outputSymbols.map (fun read => keepRule source read source .right) ++
    [writeRule source leftMarker installOuterState write .right]

def terminalOutputPackerRules : List WorkRule :=
  [writeRule startState WorkSymbol.blank acceptState WorkSymbol.blank .stay,
   writeRule startState WorkSymbol.zeroBlank rememberFirstZeroState
      WorkSymbol.blank .right,
   writeRule startState WorkSymbol.oneBlank rememberFirstOneState
      WorkSymbol.blank .right,
   writeRule seekPackedState WorkSymbol.blank seekPackedState
      WorkSymbol.blank .right,
   writeRule seekPackedState WorkSymbol.zeroBlank rememberPackedZeroState
      WorkSymbol.blank .right,
   writeRule seekPackedState WorkSymbol.oneBlank rememberPackedOneState
      WorkSymbol.blank .right,
   keepRule seekPackedState rightMarker acceptState .right,
   writeRule rememberFirstZeroState WorkSymbol.zeroBlank
      firstCarryZeroZeroState WorkSymbol.blank .right,
   writeRule rememberFirstZeroState WorkSymbol.oneBlank
      firstCarryZeroOneState WorkSymbol.blank .right,
   keepRule rememberFirstZeroState rightMarker firstWriteZeroState .right,
   writeRule rememberFirstOneState WorkSymbol.zeroBlank
      firstCarryOneZeroState WorkSymbol.blank .right,
   writeRule rememberFirstOneState WorkSymbol.oneBlank
      firstCarryOneOneState WorkSymbol.blank .right,
   keepRule rememberFirstOneState rightMarker firstWriteOneState .right,
   writeRule rememberPackedZeroState WorkSymbol.zeroBlank
      packedCarryZeroZeroState WorkSymbol.blank .right,
   writeRule rememberPackedZeroState WorkSymbol.oneBlank
      packedCarryZeroOneState WorkSymbol.blank .right,
   keepRule rememberPackedZeroState rightMarker seekOuterZeroState .right,
   writeRule rememberPackedOneState WorkSymbol.zeroBlank
      packedCarryOneZeroState WorkSymbol.blank .right,
   writeRule rememberPackedOneState WorkSymbol.oneBlank
      packedCarryOneOneState WorkSymbol.blank .right,
   keepRule rememberPackedOneState rightMarker seekOuterOneState .right] ++
  carryRules firstCarryZeroZeroState firstWriteZeroZeroState ++
  carryRules firstCarryZeroOneState firstWriteZeroOneState ++
  carryRules firstCarryOneZeroState firstWriteOneZeroState ++
  carryRules firstCarryOneOneState firstWriteOneOneState ++
  writeAllRules firstWriteZeroState installOuterState
    WorkSymbol.zeroBlank .right ++
  writeAllRules firstWriteOneState installOuterState
    WorkSymbol.oneBlank .right ++
  writeAllRules firstWriteZeroZeroState installOuterState
    WorkSymbol.zeroZero .right ++
  writeAllRules firstWriteZeroOneState installOuterState
    WorkSymbol.zeroOne .right ++
  writeAllRules firstWriteOneZeroState installOuterState
    WorkSymbol.oneZero .right ++
  writeAllRules firstWriteOneOneState installOuterState
    WorkSymbol.oneOne .right ++
  carryRules packedCarryZeroZeroState seekOuterZeroZeroState ++
  carryRules packedCarryZeroOneState seekOuterZeroOneState ++
  carryRules packedCarryOneZeroState seekOuterOneZeroState ++
  carryRules packedCarryOneOneState seekOuterOneOneState ++
  seekOuterRules seekOuterZeroState WorkSymbol.zeroBlank ++
  seekOuterRules seekOuterOneState WorkSymbol.oneBlank ++
  seekOuterRules seekOuterZeroZeroState WorkSymbol.zeroZero ++
  seekOuterRules seekOuterZeroOneState WorkSymbol.zeroOne ++
  seekOuterRules seekOuterOneZeroState WorkSymbol.oneZero ++
  seekOuterRules seekOuterOneOneState WorkSymbol.oneOne ++
  writeAllRules installOuterState returnOutputState leftMarker .left ++
  outputSymbols.map (fun read =>
    keepRule returnOutputState read returnOutputState .left) ++
  [keepRule returnOutputState rightMarker returnSourceState .left] ++
  sourceBlankSymbols.map (fun read =>
    keepRule returnSourceState read returnSourceState .left) ++
  [keepRule returnSourceState leftMarker seekPackedState .right]

/-- Finite work machine that removes the interleaved tag blanks from the
observable compiled output by packing two logical bits per work cell. -/
def terminalOutputPacker : WorkMachine :=
  { rules := terminalOutputPackerRules
    startState := startState
    acceptState := acceptState
    rejectState := rejectState }

/-! ### Packed words and explicit budgets -/

def bitSymbol : Bool → WorkSymbol
  | false => WorkSymbol.zeroBlank
  | true => WorkSymbol.oneBlank

def pairSymbol : Bool → Bool → WorkSymbol
  | false, false => WorkSymbol.zeroZero
  | false, true => WorkSymbol.zeroOne
  | true, false => WorkSymbol.oneZero
  | true, true => WorkSymbol.oneOne

def bitSymbols (bits : BitString) : List WorkSymbol :=
  bits.map bitSymbol

def packedSymbols : BitString → List WorkSymbol
  | [] => []
  | [bit] => [bitSymbol bit]
  | first :: second :: rest => pairSymbol first second :: packedSymbols rest

def packedCellCount : BitString → Nat
  | [] => 0
  | [_] => 1
  | _ :: _ :: rest => packedCellCount rest + 1

def packedLoopSteps (total outputCells : Nat) : BitString → Nat
  | [] => total + 1
  | [_] =>
      (2 * total + 2 * outputCells + 6) +
        packedLoopSteps total (outputCells + 1) []
  | _ :: _ :: rest =>
      (2 * total + 2 * outputCells + 6) +
        packedLoopSteps total (outputCells + 1) rest

/-- Exact number of successful work transitions from a represented canonical
handoff word to the designated terminal output configuration. -/
def terminalOutputPackerWorkSteps (bits : BitString) : Nat :=
  match bits with
  | [] => 1
  | _ :: _ => packedLoopSteps bits.length 0 bits

/-- Conservative raw compiled runtime polynomial in logical output length. -/
def terminalOutputPackerRawTimeBound : NatPolynomial :=
  .add (.quadratic 18 6) (.linear 36 0)

/-! ### Private exact-run infrastructure -/

private def tapeAtWord (leftSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := leftSide, head := WorkSymbol.blank, right := [] }
  | head :: suffix => { left := leftSide, head := head, right := suffix }

private def configAtWord (state : Nat) (leftSide word : List WorkSymbol) :
    WorkConfiguration :=
  { state := state, tape := tapeAtWord leftSide word }

private def tapeAtLeftWord (rightSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := [], head := WorkSymbol.blank, right := rightSide }
  | head :: leftTail => { left := leftTail, head := head, right := rightSide }

private def configAtLeftWord (state : Nat)
    (leftWord rightSide : List WorkSymbol) : WorkConfiguration :=
  { state := state, tape := tapeAtLeftWord rightSide leftWord }

private def outsideTail : List WorkSymbol → List WorkSymbol
  | [] => []
  | _ :: rest => rest

private def pushLeft : List WorkSymbol → List WorkSymbol → List WorkSymbol
  | [], leftSide => leftSide
  | symbol :: rest, leftSide => pushLeft rest (symbol :: leftSide)

private theorem pushLeft_append_far (word left right : List WorkSymbol) :
    pushLeft word (left ++ right) = pushLeft word left ++ right := by
  induction word generalizing left with
  | nil => rfl
  | cons symbol rest ih => exact ih (symbol :: left)

private theorem pushLeft_append_word (first second farSide : List WorkSymbol) :
    pushLeft (first ++ second) farSide =
      pushLeft second (pushLeft first farSide) := by
  induction first generalizing farSide with
  | nil => rfl
  | cons symbol rest ih => exact ih (symbol :: farSide)

private theorem pushLeft_cons_far (word : List WorkSymbol)
    (symbol : WorkSymbol) :
    pushLeft word [symbol] = pushLeft word [] ++ [symbol] := by
  change pushLeft word ([] ++ [symbol]) = _
  exact pushLeft_append_far word [] [symbol]

private theorem pushLeft_cancel (word farSide : List WorkSymbol) :
    pushLeft (pushLeft word []) farSide = word ++ farSide := by
  induction word with
  | nil => rfl
  | cons symbol rest ih =>
      change pushLeft (pushLeft rest [symbol]) farSide =
        symbol :: (rest ++ farSide)
      rw [pushLeft_cons_far]
      rw [pushLeft_append_word]
      change symbol :: pushLeft (pushLeft rest []) farSide = _
      exact congrArg (List.cons symbol) ih

private theorem pushLeft_length (word farSide : List WorkSymbol) :
    (pushLeft word farSide).length = word.length + farSide.length := by
  induction word generalizing farSide with
  | nil => exact (Nat.zero_add farSide.length).symm
  | cons first rest ih =>
      change (pushLeft rest (first :: farSide)).length =
        Nat.succ rest.length + farSide.length
      rw [ih]
      rw [Nat.succ_add]
      exact Nat.add_succ rest.length farSide.length

private theorem pushLeft_property (Property : WorkSymbol → Prop)
    (word farSide : List WorkSymbol)
    (hWord : ∀ symbol, List.Mem symbol word → Property symbol)
    (hFar : ∀ symbol, List.Mem symbol farSide → Property symbol) :
    ∀ symbol, List.Mem symbol (pushLeft word farSide) → Property symbol := by
  induction word generalizing farSide with
  | nil => exact hFar
  | cons first rest ih =>
      apply ih (first :: farSide)
      · intro symbol found
        exact hWord symbol (List.Mem.tail first found)
      · intro symbol found
        cases found with
        | head => exact hWord first (List.Mem.head rest)
        | tail _ tailMem => exact hFar symbol tailMem

private theorem workRunExact_compose (machine : WorkMachine)
    (first second : Nat) (start middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first start = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) start = some final := by
  induction first generalizing start with
  | zero =>
      change some start = some middle at hFirst
      have hStart : start = middle := Option.some.inj hFirst
      rw [Nat.zero_add, hStart]
      exact hSecond
  | succ first ih =>
      cases hStep : workStep? machine start with
      | none =>
          change
            (match workStep? machine start with
             | none => none
             | some next => workRunExact? machine first next) =
              some middle at hFirst
          rw [hStep] at hFirst
          contradiction
      | some next =>
          have hTail : workRunExact? machine first next = some middle := by
            change
              (match workStep? machine start with
               | none => none
               | some next => workRunExact? machine first next) =
                some middle at hFirst
            rw [hStep] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? machine start with
             | none => none
             | some next => workRunExact? machine (first + second) next) =
              some final
          rw [hStep]
          exact ih next hTail

private theorem workRunExact_one (machine : WorkMachine)
    (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change (match workStep? machine start with
    | none => none
    | some result => some result) = some next
  rw [hStep]

private theorem scanRightExact (machine : WorkMachine) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? machine (configAtWord state leftSide (head :: suffix)) =
        some (configAtWord state (head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtWord state leftSide (word ++ suffix)) =
      some (configAtWord state (pushLeft word leftSide) suffix) := by
  induction word generalizing leftSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, List.Mem symbol rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (configAtWord state leftSide (head :: (rest ++ suffix))) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep leftSide head (rest ++ suffix) hHead]
      exact ih (head :: leftSide) hRest

private theorem scanLeftExact (machine : WorkMachine) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? machine
          (configAtLeftWord state (head :: leftTail) rightSide) =
        some (configAtLeftWord state leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtLeftWord state (word ++ leftSuffix) rightSide) =
      some (configAtLeftWord state leftSuffix
        (pushLeft word rightSide)) := by
  induction word generalizing rightSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, List.Mem symbol rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (configAtLeftWord state (head :: (rest ++ leftSuffix))
            rightSide) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide hHead]
      exact ih (head :: rightSide) hRest

private inductive OutputCell : WorkSymbol → Prop where
  | zero : OutputCell WorkSymbol.zeroBlank
  | one : OutputCell WorkSymbol.oneBlank
  | zeroZero : OutputCell WorkSymbol.zeroZero
  | zeroOne : OutputCell WorkSymbol.zeroOne
  | oneZero : OutputCell WorkSymbol.oneZero
  | oneOne : OutputCell WorkSymbol.oneOne

private inductive SourceCell : WorkSymbol → Prop where
  | blank : SourceCell WorkSymbol.blank
  | zero : SourceCell WorkSymbol.zeroBlank
  | one : SourceCell WorkSymbol.oneBlank

private inductive BitCell : WorkSymbol → Prop where
  | zero : BitCell WorkSymbol.zeroBlank
  | one : BitCell WorkSymbol.oneBlank

private theorem bitSymbol_outputCell (bit : Bool) :
    OutputCell (bitSymbol bit) := by
  cases bit with
  | false => exact .zero
  | true => exact .one

private theorem pairSymbol_outputCell (first second : Bool) :
    OutputCell (pairSymbol first second) := by
  cases first <;> cases second
  · exact .zeroZero
  · exact .zeroOne
  · exact .oneZero
  · exact .oneOne

private theorem bitSymbol_sourceCell (bit : Bool) :
    SourceCell (bitSymbol bit) := by
  cases bit with
  | false => exact .zero
  | true => exact .one

private theorem bitSymbol_bitCell (bit : Bool) :
    BitCell (bitSymbol bit) := by
  cases bit with
  | false => exact .zero
  | true => exact .one

private theorem bitSymbols_length (bits : BitString) :
    (bitSymbols bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => exact congrArg Nat.succ ih

private theorem bitSymbols_areBitCells (bits : BitString) :
    ∀ symbol, List.Mem symbol (bitSymbols bits) → BitCell symbol := by
  induction bits with
  | nil => intro _ found; contradiction
  | cons bit rest ih =>
      intro symbol found
      cases found with
      | head => exact bitSymbol_bitCell bit
      | tail _ tailMem => exact ih symbol tailMem

private theorem bitSymbols_areSourceCells (bits : BitString) :
    ∀ symbol, List.Mem symbol (bitSymbols bits) → SourceCell symbol := by
  induction bits with
  | nil => intro _ found; contradiction
  | cons bit rest ih =>
      intro symbol found
      cases found with
      | head => exact bitSymbol_sourceCell bit
      | tail _ tailMem => exact ih symbol tailMem

private theorem packedSymbols_areOutputCells :
    (bits : BitString) →
    ∀ symbol, List.Mem symbol (packedSymbols bits) → OutputCell symbol
  | [] => by
      intro _ found
      contradiction
  | [bit] => by
      intro symbol found
      cases found with
      | head => exact bitSymbol_outputCell bit
      | tail _ tailMem => contradiction
  | first :: second :: rest => by
      intro symbol found
      cases found with
      | head => exact pairSymbol_outputCell first second
      | tail _ tailMem =>
          exact packedSymbols_areOutputCells rest symbol tailMem

private theorem outputCells_append (left right : List WorkSymbol)
    (hLeft : ∀ symbol, List.Mem symbol left → OutputCell symbol)
    (hRight : ∀ symbol, List.Mem symbol right → OutputCell symbol) :
    ∀ symbol, List.Mem symbol (left ++ right) → OutputCell symbol := by
  induction left with
  | nil => exact hRight
  | cons first rest ih =>
      intro symbol found
      cases found with
      | head => exact hLeft first (List.Mem.head rest)
      | tail _ tailMem =>
          apply ih
          · intro candidate candidateMem
            exact hLeft candidate (List.Mem.tail first candidateMem)
          · exact tailMem

private theorem sourceCells_append (left right : List WorkSymbol)
    (hLeft : ∀ symbol, List.Mem symbol left → SourceCell symbol)
    (hRight : ∀ symbol, List.Mem symbol right → SourceCell symbol) :
    ∀ symbol, List.Mem symbol (left ++ right) → SourceCell symbol := by
  induction left with
  | nil => exact hRight
  | cons first rest ih =>
      intro symbol found
      cases found with
      | head => exact hLeft first (List.Mem.head rest)
      | tail _ tailMem =>
          apply ih
          · intro candidate candidateMem
            exact hLeft candidate (List.Mem.tail first candidateMem)
          · exact tailMem

private theorem replicate_blank_sourceCells (count : Nat) :
    ∀ symbol, List.Mem symbol (List.replicate count WorkSymbol.blank) →
      SourceCell symbol := by
  induction count with
  | zero => intro _ found; contradiction
  | succ count ih =>
      intro symbol found
      cases found with
      | head => exact .blank
      | tail _ tailMem => exact ih symbol tailMem

private theorem replicate_blank_length (count : Nat) :
    (List.replicate count WorkSymbol.blank).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg Nat.succ ih

private theorem listLength_append (left right : List WorkSymbol) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (Nat.zero_add right.length).symm
  | cons first rest ih =>
      change Nat.succ (rest ++ right).length =
        Nat.succ rest.length + right.length
      rw [Nat.succ_add]
      exact congrArg Nat.succ ih

private theorem listAppend_assoc (first second third : List WorkSymbol) :
    (first ++ second) ++ third = first ++ (second ++ third) := by
  induction first with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

private theorem listNil_append (right : List WorkSymbol) :
    ([] : List WorkSymbol) ++ right = right := by
  rfl

private theorem listCons_append (head : WorkSymbol)
    (tail right : List WorkSymbol) :
    (head :: tail) ++ right = head :: (tail ++ right) := by
  rfl

private theorem listAppend_nil (word : List WorkSymbol) :
    word ++ [] = word := by
  induction word with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

private def sourceSymbols (processed : Nat) (remaining : BitString) :
    List WorkSymbol :=
  List.replicate processed WorkSymbol.blank ++ bitSymbols remaining

private theorem sourceSymbols_length (processed : Nat)
    (remaining : BitString) :
    (sourceSymbols processed remaining).length =
      processed + remaining.length := by
  unfold sourceSymbols
  rw [listLength_append, replicate_blank_length, bitSymbols_length]

private theorem sourceSymbols_areSourceCells (processed : Nat)
    (remaining : BitString) :
    ∀ symbol, List.Mem symbol (sourceSymbols processed remaining) →
      SourceCell symbol := by
  exact sourceCells_append
    (List.replicate processed WorkSymbol.blank) (bitSymbols remaining)
    (replicate_blank_sourceCells processed)
    (bitSymbols_areSourceCells remaining)

private theorem pushedSource_areSourceCells (processed : Nat)
    (remaining : BitString) :
    ∀ symbol, List.Mem symbol (pushLeft (sourceSymbols processed remaining) []) →
      SourceCell symbol := by
  apply pushLeft_property SourceCell (sourceSymbols processed remaining) []
  · exact sourceSymbols_areSourceCells processed remaining
  · intro _ found
    contradiction

private theorem pushedOutput_areOutputCells (output : List WorkSymbol)
    (hOutput : ∀ symbol, List.Mem symbol output → OutputCell symbol) :
    ∀ symbol, List.Mem symbol (pushLeft output []) → OutputCell symbol := by
  apply pushLeft_property OutputCell output [] hOutput
  intro _ found
  contradiction

private theorem replicateBlank_append (first second : Nat) :
    List.replicate first WorkSymbol.blank ++
        List.replicate second WorkSymbol.blank =
      List.replicate (first + second) WorkSymbol.blank := by
  induction first with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first ih =>
      rw [Nat.succ_add]
      exact congrArg (List.cons WorkSymbol.blank) ih

private theorem replicateBlank_succEnd (count : Nat) :
    List.replicate (count + 1) WorkSymbol.blank =
      List.replicate count WorkSymbol.blank ++ [WorkSymbol.blank] := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg (List.cons WorkSymbol.blank) ih

private theorem pushLeft_replicate_add (first second : Nat)
    (farSide : List WorkSymbol) :
    pushLeft (List.replicate second WorkSymbol.blank)
        (pushLeft (List.replicate first WorkSymbol.blank) farSide) =
      pushLeft (List.replicate (first + second) WorkSymbol.blank) farSide := by
  rw [← replicateBlank_append]
  exact (pushLeft_append_word
    (List.replicate first WorkSymbol.blank)
    (List.replicate second WorkSymbol.blank) farSide).symm

private theorem pushLeft_replicate (count : Nat)
    (farSide : List WorkSymbol) :
    pushLeft (List.replicate count WorkSymbol.blank) farSide =
      List.replicate count WorkSymbol.blank ++ farSide := by
  induction count generalizing farSide with
  | zero => rfl
  | succ count ih =>
      change
        pushLeft (List.replicate count WorkSymbol.blank)
            (WorkSymbol.blank :: farSide) =
          WorkSymbol.blank ::
            (List.replicate count WorkSymbol.blank ++ farSide)
      rw [ih]
      change
        List.replicate count WorkSymbol.blank ++
            ([WorkSymbol.blank] ++ farSide) =
          List.replicate (count + 1) WorkSymbol.blank ++ farSide
      rw [← listAppend_assoc]
      rw [← replicateBlank_succEnd]

private theorem pushLeft_single_blank (farSide : List WorkSymbol) :
    pushLeft [WorkSymbol.blank] farSide = WorkSymbol.blank :: farSide := by
  rfl

private theorem pushLeft_source_after (processed consumed : Nat)
    (remaining : BitString) (farSide : List WorkSymbol) :
    pushLeft (bitSymbols remaining)
        (pushLeft (List.replicate consumed WorkSymbol.blank)
          (pushLeft (List.replicate processed WorkSymbol.blank) farSide)) =
      pushLeft (sourceSymbols (processed + consumed) remaining) farSide := by
  rw [pushLeft_replicate_add]
  unfold sourceSymbols
  exact (pushLeft_append_word
    (List.replicate (processed + consumed) WorkSymbol.blank)
    (bitSymbols remaining) farSide).symm

private theorem pushLeft_newOutput (output : WorkSymbol)
    (existing farSide : List WorkSymbol) :
    pushLeft (output :: pushLeft existing []) farSide =
      existing ++ output :: farSide := by
  change pushLeft (pushLeft existing []) (output :: farSide) = _
  exact pushLeft_cancel existing (output :: farSide)

private theorem addTwoBefore (left right : Nat) :
    (left + 2) + right = left + (right + 1 + 1) := by
  calc
    (left + 2) + right = left + (2 + right) :=
      Nat.add_assoc left 2 right
    _ = left + (right + 2) :=
      congrArg (Nat.add left) (Nat.add_comm 2 right)
    _ = left + (right + 1 + 1) := rfl

private theorem zeroAddSafe (value : Nat) : 0 + value = value := by
  induction value with
  | zero => rfl
  | succ value ih => exact congrArg Nat.succ ih

private theorem succAddSafe (left right : Nat) :
    (left + 1) + right = (left + right) + 1 := by
  induction right with
  | zero => rfl
  | succ right ih => exact congrArg Nat.succ ih

private theorem addAssocSafe (left middle right : Nat) :
    (left + middle) + right = left + (middle + right) := by
  induction right with
  | zero => rfl
  | succ right ih => exact congrArg Nat.succ ih

private theorem addCommSafe (left right : Nat) :
    left + right = right + left := by
  induction right with
  | zero => exact (zeroAddSafe left).symm
  | succ right ih =>
      change (left + right) + 1 = (right + 1) + left
      calc
        (left + right) + 1 = (right + left) + 1 :=
          congrArg (fun value => value + 1) ih
        _ = (right + 1) + left := (succAddSafe right left).symm

private theorem addSwapMiddleSafe (left middle right : Nat) :
    (left + middle) + right = (left + right) + middle := by
  calc
    (left + middle) + right = left + (middle + right) :=
      addAssocSafe left middle right
    _ = left + (right + middle) :=
      congrArg (Nat.add left) (addCommSafe middle right)
    _ = (left + right) + middle :=
      (addAssocSafe left right middle).symm

private theorem twoMulSafe (value : Nat) : 2 * value = value + value := by
  induction value with
  | zero => rfl
  | succ value ih =>
      calc
        2 * (value + 1) = 2 * value + 2 := rfl
        _ = (value + value) + 2 :=
          congrArg (fun result => result + 2) ih
        _ = ((value + 1) + value) + 1 :=
          congrArg (fun result => result + 1)
            (succAddSafe value value).symm
        _ = (value + 1) + (value + 1) := rfl

private theorem appendFiveSafe (base first second third fourth fifth : Nat) :
    (((((base + first) + second) + third) + fourth) + fifth) =
      base + ((((first + second) + third) + fourth) + fifth) := by
  calc
    (((((base + first) + second) + third) + fourth) + fifth) =
        ((((base + (first + second)) + third) + fourth) + fifth) :=
      congrArg (fun value => ((value + third) + fourth) + fifth)
        (addAssocSafe base first second)
    _ = (((base + ((first + second) + third)) + fourth) + fifth) :=
      congrArg (fun value => (value + fourth) + fifth)
        (addAssocSafe base (first + second) third)
    _ = (base + (((first + second) + third) + fourth)) + fifth :=
      congrArg (fun value => value + fifth)
        (addAssocSafe base ((first + second) + third) fourth)
    _ = base + ((((first + second) + third) + fourth) + fifth) :=
      addAssocSafe base (((first + second) + third) + fourth) fifth

private theorem outputSegmentArithmetic (existingLength outputWordLength : Nat)
    (hOutput : outputWordLength = existingLength + 1) :
    ((((existingLength + 1) + 1) + outputWordLength) + 1) =
      2 * existingLength + 4 := by
  rw [hOutput]
  calc
    ((((existingLength + 1) + 1) + (existingLength + 1)) + 1) =
        ((((existingLength + 1) + (existingLength + 1)) + 1) + 1) :=
      congrArg (fun value => value + 1)
        (addSwapMiddleSafe (existingLength + 1) 1
          (existingLength + 1))
    _ = ((existingLength + 1) + (existingLength + 1)) + 2 := rfl
    _ = 2 * (existingLength + 1) + 2 :=
      congrArg (fun value => value + 2)
        (twoMulSafe (existingLength + 1)).symm
    _ = 2 * existingLength + 4 := rfl

private theorem groupedIterationFuelArithmetic (total existingLength : Nat) :
    (((total + 1) + (2 * existingLength + 4)) + total) + 1 =
      2 * total + 2 * existingLength + 6 := by
  calc
    (((total + 1) + (2 * existingLength + 4)) + total) + 1 =
        (((total + 1) + total) + (2 * existingLength + 4)) + 1 :=
      congrArg (fun value => value + 1)
        (addSwapMiddleSafe (total + 1) (2 * existingLength + 4) total)
    _ = (((total + total) + 1) + (2 * existingLength + 4)) + 1 :=
      congrArg (fun value => (value + (2 * existingLength + 4)) + 1)
        (succAddSafe total total)
    _ = (((total + total) + (2 * existingLength + 4)) + 1) + 1 :=
      congrArg (fun value => value + 1)
        (addSwapMiddleSafe (total + total) 1 (2 * existingLength + 4))
    _ = ((total + total) + (2 * existingLength + 4)) + 2 := rfl
    _ = (total + total) + ((2 * existingLength + 4) + 2) :=
      addAssocSafe (total + total) (2 * existingLength + 4) 2
    _ = (total + total) + (2 * existingLength + 6) := rfl
    _ = 2 * total + (2 * existingLength + 6) :=
      congrArg (fun value => value + (2 * existingLength + 6))
        (twoMulSafe total).symm
    _ = 2 * total + 2 * existingLength + 6 :=
      (addAssocSafe (2 * total) (2 * existingLength) 6).symm

private theorem packedPairIterationFuelArithmetic
    (processed restLength existingLength outputWordLength total : Nat)
    (hTotal : (processed + 2) + restLength = total)
    (hOutput : outputWordLength = existingLength + 1) :
    (((((((((((processed + 1) + 1) + restLength) + 1) +
        existingLength) + 1) + 1) + outputWordLength) + 1) + total) + 1) =
      2 * total + 2 * existingLength + 6 := by
  have hPrefix : (((processed + 1) + 1) + restLength) + 1 =
      total + 1 := by
    have hBeforeMarker : ((processed + 1) + 1) + restLength = total := by
      change (processed + 2) + restLength = total
      exact hTotal
    exact congrArg (fun value => value + 1) hBeforeMarker
  have hOutputSegment :=
    outputSegmentArithmetic existingLength outputWordLength hOutput
  calc
    (((((((((((processed + 1) + 1) + restLength) + 1) +
          existingLength) + 1) + 1) + outputWordLength) + 1) + total) + 1) =
        ((((((processed + 1) + 1) + restLength) + 1) +
          ((((existingLength + 1) + 1) + outputWordLength) + 1)) +
          total) + 1 :=
      congrArg (fun value => (value + total) + 1)
        (appendFiveSafe ((((processed + 1) + 1) + restLength) + 1)
          existingLength 1 1 outputWordLength 1)
    _ = (((total + 1) +
          ((((existingLength + 1) + 1) + outputWordLength) + 1)) +
          total) + 1 :=
      congrArg (fun value => ((value +
        ((((existingLength + 1) + 1) + outputWordLength) + 1)) + total) + 1)
        hPrefix
    _ = (((total + 1) + (2 * existingLength + 4)) + total) + 1 :=
      congrArg (fun value => (((total + 1) + value) + total) + 1)
        hOutputSegment
    _ = 2 * total + 2 * existingLength + 6 :=
      groupedIterationFuelArithmetic total existingLength

private theorem packedSingleIterationFuelArithmetic
    (processed existingLength outputWordLength total : Nat)
    (hTotal : processed + 1 = total)
    (hOutput : outputWordLength = existingLength + 1) :
    (((((((((processed + 1) + 1) + existingLength) + 1) + 1) +
        outputWordLength) + 1) + total) + 1) =
      2 * total + 2 * existingLength + 6 := by
  have hPrefix : (processed + 1) + 1 = total + 1 :=
    congrArg (fun value => value + 1) hTotal
  have hOutputSegment :=
    outputSegmentArithmetic existingLength outputWordLength hOutput
  calc
    (((((((((processed + 1) + 1) + existingLength) + 1) + 1) +
          outputWordLength) + 1) + total) + 1) =
        ((((processed + 1) + 1) +
          ((((existingLength + 1) + 1) + outputWordLength) + 1)) +
          total) + 1 :=
      congrArg (fun value => (value + total) + 1)
        (appendFiveSafe ((processed + 1) + 1)
          existingLength 1 1 outputWordLength 1)
    _ = (((total + 1) +
          ((((existingLength + 1) + 1) + outputWordLength) + 1)) +
          total) + 1 :=
      congrArg (fun value => ((value +
        ((((existingLength + 1) + 1) + outputWordLength) + 1)) + total) + 1)
        hPrefix
    _ = (((total + 1) + (2 * existingLength + 4)) + total) + 1 :=
      congrArg (fun value => (((total + 1) + value) + total) + 1)
        hOutputSegment
    _ = 2 * total + 2 * existingLength + 6 :=
      groupedIterationFuelArithmetic total existingLength

private theorem firstPairFuelArithmetic (restLength total : Nat)
    (hTotal : 2 + restLength = total) :
    1 + 1 + restLength + 1 + 1 + 1 + 1 + 1 + total + 1 =
      2 * total + 6 := by
  have hPrefix : ((1 + 1) + restLength) + 1 = total + 1 :=
    congrArg (fun value => value + 1) hTotal
  have hOutputSegment := outputSegmentArithmetic 0 1 rfl
  calc
    1 + 1 + restLength + 1 + 1 + 1 + 1 + 1 + total + 1 =
        ((((1 + 1) + restLength) + 1) +
          ((((0 + 1) + 1) + 1) + 1) + total) + 1 := rfl
    _ = (((total + 1) + ((((0 + 1) + 1) + 1) + 1)) + total) + 1 :=
      congrArg (fun value => ((value + ((((0 + 1) + 1) + 1) + 1)) +
        total) + 1) hPrefix
    _ = (((total + 1) + (2 * 0 + 4)) + total) + 1 :=
      congrArg (fun value => (((total + 1) + value) + total) + 1)
        hOutputSegment
    _ = 2 * total + 2 * 0 + 6 :=
      groupedIterationFuelArithmetic total 0
    _ = 2 * total + 6 := rfl

private theorem firstSingleFuelArithmetic (total : Nat)
    (hTotal : 1 = total) :
    1 + 1 + 1 + 1 + 1 + 1 + total + 1 = 2 * total + 6 := by
  have hPrefix : 1 + 1 = total + 1 :=
    congrArg (fun value => value + 1) hTotal
  have hOutputSegment := outputSegmentArithmetic 0 1 rfl
  calc
    1 + 1 + 1 + 1 + 1 + 1 + total + 1 =
        (1 + 1 + ((((0 + 1) + 1) + 1) + 1) + total) + 1 := rfl
    _ = (((total + 1) + ((((0 + 1) + 1) + 1) + 1)) + total) + 1 :=
      congrArg (fun value => ((value + ((((0 + 1) + 1) + 1) + 1)) +
        total) + 1) hPrefix
    _ = (((total + 1) + (2 * 0 + 4)) + total) + 1 :=
      congrArg (fun value => (((total + 1) + value) + total) + 1)
        hOutputSegment
    _ = 2 * total + 2 * 0 + 6 :=
      groupedIterationFuelArithmetic total 0
    _ = 2 * total + 6 := rfl

private def packedLoopOutside : BitString → List WorkSymbol → List WorkSymbol
  | [], outside => outside
  | [_], outside => outsideTail outside
  | _ :: _ :: rest, outside =>
      packedLoopOutside rest (outsideTail outside)

def terminalOutputPackerOutside :
    BitString → List WorkSymbol → List WorkSymbol
  | [], outside => outside
  | [_], outside => outsideTail (outsideTail outside)
  | _ :: _ :: rest, outside =>
      packedLoopOutside rest (outsideTail (outsideTail outside))

private def packedLoopConfiguration (processed : Nat)
    (remaining : BitString) (existing : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol) : WorkConfiguration :=
  configAtWord seekPackedState (leftMarker :: outsideLeft)
    (sourceSymbols processed remaining ++
      rightMarker :: existing ++ leftMarker :: outsideRight)

private def packedFinalConfiguration (total : Nat)
    (output : List WorkSymbol) (outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord acceptState
    (rightMarker ::
      pushLeft (List.replicate total WorkSymbol.blank)
        (leftMarker :: outsideLeft))
    (output ++ leftMarker :: outsideRight)

private theorem start_empty_step (left right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord startState left (WorkSymbol.blank :: right)) =
      some (configAtWord acceptState left (WorkSymbol.blank :: right)) := by
  rfl

private theorem start_bit_step (bit : Bool) (left : List WorkSymbol)
    (next : WorkSymbol) (right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord startState left
          (bitSymbol bit :: next :: right)) =
      some (configAtWord (firstRememberState bit)
        (WorkSymbol.blank :: left) (next :: right)) := by
  cases bit <;> rfl

private theorem seekPacked_blank_step (left right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord seekPackedState left
          (WorkSymbol.blank :: right)) =
      some (configAtWord seekPackedState
        (WorkSymbol.blank :: left) right) := by
  rfl

private theorem seekPacked_bit_step (bit : Bool)
    (left : List WorkSymbol) (next : WorkSymbol)
    (right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord seekPackedState left
          (bitSymbol bit :: next :: right)) =
      some (configAtWord (packedRememberState bit)
        (WorkSymbol.blank :: left) (next :: right)) := by
  cases bit <;> rfl

private theorem seekPacked_done_step (left : List WorkSymbol)
    (firstOutput : WorkSymbol) (right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord seekPackedState left
          (rightMarker :: firstOutput :: right)) =
      some (configAtWord acceptState (rightMarker :: left)
        (firstOutput :: right)) := by
  rfl

private theorem rememberFirst_pair_step (first second : Bool)
    (left : List WorkSymbol) (next : WorkSymbol)
    (right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (firstRememberState first) left
          (bitSymbol second :: next :: right)) =
      some (configAtWord (firstCarryState first second)
        (WorkSymbol.blank :: left) (next :: right)) := by
  cases first <;> cases second <;> rfl

private theorem rememberFirst_single_step (first : Bool)
    (left : List WorkSymbol) (outsideHead : WorkSymbol)
    (outsideRight : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (firstRememberState first) left
          (rightMarker :: outsideHead :: outsideRight)) =
      some (configAtWord (firstWriteSingleState first)
        (rightMarker :: left) (outsideHead :: outsideRight)) := by
  cases first <;> rfl

private theorem rememberPacked_pair_step (first second : Bool)
    (left : List WorkSymbol) (next : WorkSymbol)
    (right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (packedRememberState first) left
          (bitSymbol second :: next :: right)) =
      some (configAtWord (packedCarryState first second)
        (WorkSymbol.blank :: left) (next :: right)) := by
  cases first <;> cases second <;> rfl

private theorem rememberPacked_single_step (first : Bool)
    (left : List WorkSymbol) (firstOutput : WorkSymbol)
    (right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (packedRememberState first) left
          (rightMarker :: firstOutput :: right)) =
      some (configAtWord (seekOuterSingleState first)
        (rightMarker :: left) (firstOutput :: right)) := by
  cases first <;> rfl

private theorem firstCarry_bit_step (first second current : Bool)
    (left right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (firstCarryState first second) left
          (bitSymbol current :: right)) =
      some (configAtWord (firstCarryState first second)
        (bitSymbol current :: left) right) := by
  cases first <;> cases second <;> cases current <;> rfl

private theorem firstCarry_marker_step (first second : Bool)
    (left : List WorkSymbol) (outsideHead : WorkSymbol)
    (outsideRight : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (firstCarryState first second) left
          (rightMarker :: outsideHead :: outsideRight)) =
      some (configAtWord (firstWritePairState first second)
        (rightMarker :: left) (outsideHead :: outsideRight)) := by
  cases first <;> cases second <;> rfl

private theorem packedCarry_bit_step (first second current : Bool)
    (left right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (packedCarryState first second) left
          (bitSymbol current :: right)) =
      some (configAtWord (packedCarryState first second)
        (bitSymbol current :: left) right) := by
  cases first <;> cases second <;> cases current <;> rfl

private theorem packedCarry_marker_step (first second : Bool)
    (left : List WorkSymbol) (firstOutput : WorkSymbol)
    (right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (packedCarryState first second) left
          (rightMarker :: firstOutput :: right)) =
      some (configAtWord (seekOuterPairState first second)
        (rightMarker :: left) (firstOutput :: right)) := by
  cases first <;> cases second <;> rfl

private theorem firstWrite_single_step (bit : Bool)
    (left : List WorkSymbol) (read : WorkSymbol)
    (right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (firstWriteSingleState bit) left (read :: right)) =
      some (configAtWord installOuterState
        (bitSymbol bit :: left) right) := by
  cases bit
  · rcases read with ⟨first, second⟩
    cases first <;> cases second <;> rfl
  · rcases read with ⟨first, second⟩
    cases first <;> cases second <;> rfl

private theorem firstWrite_pair_step (first second : Bool)
    (left : List WorkSymbol) (read : WorkSymbol)
    (right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (firstWritePairState first second) left
          (read :: right)) =
      some (configAtWord installOuterState
        (pairSymbol first second :: left) right) := by
  cases first <;> cases second
  all_goals
    rcases read with ⟨readFirst, readSecond⟩
    cases readFirst <;> cases readSecond <;> rfl

private def seekOuterStateFor : WorkSymbol → Nat
  | ⟨.blank, .blank⟩ => seekOuterZeroState
  | ⟨.blank, .zero⟩ => seekOuterZeroState
  | ⟨.blank, .one⟩ => seekOuterZeroState
  | ⟨.zero, .blank⟩ => seekOuterZeroState
  | ⟨.one, .blank⟩ => seekOuterOneState
  | ⟨.zero, .zero⟩ => seekOuterZeroZeroState
  | ⟨.zero, .one⟩ => seekOuterZeroOneState
  | ⟨.one, .zero⟩ => seekOuterOneZeroState
  | ⟨.one, .one⟩ => seekOuterOneOneState

private theorem seekOuterStateFor_pair (first second : Bool) :
    seekOuterStateFor (pairSymbol first second) =
      seekOuterPairState first second := by
  cases first <;> cases second <;> rfl

private theorem seekOuterStateFor_single (bit : Bool) :
    seekOuterStateFor (bitSymbol bit) = seekOuterSingleState bit := by
  cases bit <;> rfl

private theorem seekOuter_output_step (output read : WorkSymbol)
    (hOutput : OutputCell output) (hRead : OutputCell read)
    (left right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (seekOuterStateFor output)
          left (read :: right)) =
      some (configAtWord
        (seekOuterStateFor output)
        (read :: left) right) := by
  cases hOutput <;> cases hRead <;> rfl

private theorem seekOuter_marker_step (output : WorkSymbol)
    (hOutput : OutputCell output) (left : List WorkSymbol)
    (outsideHead : WorkSymbol) (outsideRight : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (seekOuterStateFor output) left
          (leftMarker :: outsideHead :: outsideRight)) =
      some (configAtWord installOuterState (output :: left)
        (outsideHead :: outsideRight)) := by
  cases hOutput <;> rfl

private theorem installOuter_step (output : WorkSymbol)
    (hOutput : OutputCell output) (leftTail : List WorkSymbol)
    (read : WorkSymbol) (right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord installOuterState (output :: leftTail)
          (read :: right)) =
      some (configAtWord returnOutputState leftTail
        (output :: leftMarker :: right)) := by
  cases hOutput
  all_goals
    rcases read with ⟨first, second⟩
    cases first <;> cases second <;> rfl

private theorem returnOutput_step (output : WorkSymbol)
    (hOutput : OutputCell output) (leftTail right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtLeftWord returnOutputState
          (output :: leftTail) right) =
      some (configAtLeftWord returnOutputState
        leftTail (output :: right)) := by
  cases hOutput <;> rfl

private theorem returnOutput_marker_step (leftTail right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtLeftWord returnOutputState
          (rightMarker :: leftTail) right) =
      some (configAtLeftWord returnSourceState
        leftTail (rightMarker :: right)) := by
  rfl

private theorem returnSource_step (source : WorkSymbol)
    (hSource : SourceCell source) (leftTail right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtLeftWord returnSourceState
          (source :: leftTail) right) =
      some (configAtLeftWord returnSourceState
        leftTail (source :: right)) := by
  cases hSource <;> rfl

private theorem returnSource_marker_step (outsideLeft right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtLeftWord returnSourceState
          (leftMarker :: outsideLeft) right) =
      some (configAtWord seekPackedState
        (leftMarker :: outsideLeft) right) := by
  rfl

private theorem firstWrite_single_word_step (bit : Bool)
    (left outside : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (firstWriteSingleState bit) left outside) =
      some (configAtWord installOuterState
        (bitSymbol bit :: left) (outsideTail outside)) := by
  cases outside with
  | nil => exact firstWrite_single_step bit left WorkSymbol.blank []
  | cons read right => exact firstWrite_single_step bit left read right

private theorem firstWrite_pair_word_step (first second : Bool)
    (left outside : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (firstWritePairState first second) left outside) =
      some (configAtWord installOuterState
        (pairSymbol first second :: left) (outsideTail outside)) := by
  cases outside with
  | nil =>
      exact firstWrite_pair_step first second left WorkSymbol.blank []
  | cons read right => exact firstWrite_pair_step first second left read right

private theorem installOuter_word_step (output : WorkSymbol)
    (hOutput : OutputCell output) (leftTail outside : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord installOuterState (output :: leftTail) outside) =
      some (configAtLeftWord returnOutputState
        (output :: leftTail) (leftMarker :: outsideTail outside)) := by
  cases outside with
  | nil =>
      exact installOuter_step output hOutput leftTail WorkSymbol.blank []
  | cons read right => exact installOuter_step output hOutput leftTail read right

private theorem seekOuter_marker_word_step (output : WorkSymbol)
    (hOutput : OutputCell output) (left outside : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (seekOuterStateFor output) left
          (leftMarker :: outside)) =
      some (configAtWord installOuterState (output :: left) outside) := by
  cases outside with
  | nil =>
      cases hOutput <;> rfl
  | cons outsideHead outsideRight =>
      exact seekOuter_marker_step output hOutput left outsideHead outsideRight

private theorem rememberFirst_pair_bits_step (first second : Bool)
    (rest : BitString) (left : List WorkSymbol)
    (next : WorkSymbol) (right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (firstRememberState first) left
          (bitSymbol second :: bitSymbols rest ++ next :: right)) =
      some (configAtWord (firstCarryState first second)
        (WorkSymbol.blank :: left)
        (bitSymbols rest ++ next :: right)) := by
  cases rest with
  | nil => exact rememberFirst_pair_step first second left next right
  | cons head tail =>
      exact rememberFirst_pair_step first second left (bitSymbol head)
        (bitSymbols tail ++ next :: right)

private theorem rememberPacked_pair_bits_step (first second : Bool)
    (rest : BitString) (left : List WorkSymbol)
    (next : WorkSymbol) (right : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (packedRememberState first) left
          (bitSymbol second :: bitSymbols rest ++ next :: right)) =
      some (configAtWord (packedCarryState first second)
        (WorkSymbol.blank :: left)
        (bitSymbols rest ++ next :: right)) := by
  cases rest with
  | nil => exact rememberPacked_pair_step first second left next right
  | cons head tail =>
      exact rememberPacked_pair_step first second left (bitSymbol head)
        (bitSymbols tail ++ next :: right)

private theorem firstCarry_marker_word_step (first second : Bool)
    (left outside : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (firstCarryState first second) left
          (rightMarker :: outside)) =
      some (configAtWord (firstWritePairState first second)
        (rightMarker :: left) outside) := by
  cases outside with
  | nil => cases first <;> cases second <;> rfl
  | cons outsideHead outsideRight =>
      exact firstCarry_marker_step first second left outsideHead outsideRight

private theorem rememberFirst_single_word_step (bit : Bool)
    (left outside : List WorkSymbol) :
    workStep? terminalOutputPacker
        (configAtWord (firstRememberState bit) left
          (rightMarker :: outside)) =
      some (configAtWord (firstWriteSingleState bit)
        (rightMarker :: left) outside) := by
  cases outside with
  | nil => cases bit <;> rfl
  | cons outsideHead outsideRight =>
      exact rememberFirst_single_step bit left outsideHead outsideRight

private theorem seekPacked_blanks_exact (count : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? terminalOutputPacker count
        (configAtWord seekPackedState left
          (List.replicate count WorkSymbol.blank ++ suffix)) =
      some (configAtWord seekPackedState
        (pushLeft (List.replicate count WorkSymbol.blank) left)
        suffix) := by
  have hRun :
      workRunExact? terminalOutputPacker
          (List.replicate count WorkSymbol.blank).length
          (configAtWord seekPackedState left
            (List.replicate count WorkSymbol.blank ++ suffix)) =
        some (configAtWord seekPackedState
          (pushLeft (List.replicate count WorkSymbol.blank) left)
          suffix) := by
    apply scanRightExact terminalOutputPacker seekPackedState
      (fun symbol => symbol = WorkSymbol.blank)
    · intro leftSide head rest hHead
      cases hHead
      exact seekPacked_blank_step leftSide rest
    · intro symbol found
      induction count with
      | zero => contradiction
      | succ count ih =>
          cases found with
          | head => rfl
          | tail _ tailMem => exact ih tailMem
  rw [replicate_blank_length count] at hRun
  exact hRun

private theorem firstCarry_bits_exact (first second : Bool)
    (bits : BitString) (left suffix : List WorkSymbol) :
    workRunExact? terminalOutputPacker bits.length
        (configAtWord (firstCarryState first second) left
          (bitSymbols bits ++ suffix)) =
      some (configAtWord (firstCarryState first second)
        (pushLeft (bitSymbols bits) left) suffix) := by
  rw [← bitSymbols_length bits]
  apply scanRightExact terminalOutputPacker
    (firstCarryState first second) BitCell
  · intro leftSide head rest hHead
    cases hHead with
    | zero => exact firstCarry_bit_step first second false leftSide rest
    | one => exact firstCarry_bit_step first second true leftSide rest
  · exact bitSymbols_areBitCells bits

private theorem packedCarry_bits_exact (first second : Bool)
    (bits : BitString) (left suffix : List WorkSymbol) :
    workRunExact? terminalOutputPacker bits.length
        (configAtWord (packedCarryState first second) left
          (bitSymbols bits ++ suffix)) =
      some (configAtWord (packedCarryState first second)
        (pushLeft (bitSymbols bits) left) suffix) := by
  rw [← bitSymbols_length bits]
  apply scanRightExact terminalOutputPacker
    (packedCarryState first second) BitCell
  · intro leftSide head rest hHead
    cases hHead with
    | zero => exact packedCarry_bit_step first second false leftSide rest
    | one => exact packedCarry_bit_step first second true leftSide rest
  · exact bitSymbols_areBitCells bits

private theorem seekOuter_output_exact (output : WorkSymbol)
    (hOutput : OutputCell output) (existing : List WorkSymbol)
    (left suffix : List WorkSymbol)
    (hExisting : ∀ symbol, List.Mem symbol existing → OutputCell symbol) :
    workRunExact? terminalOutputPacker existing.length
        (configAtWord (seekOuterStateFor output) left
          (existing ++ suffix)) =
      some (configAtWord (seekOuterStateFor output)
        (pushLeft existing left) suffix) := by
  apply scanRightExact terminalOutputPacker
    (seekOuterStateFor output) OutputCell
  · intro leftSide head rest hHead
    exact seekOuter_output_step output head hOutput hHead leftSide rest
  · exact hExisting

private theorem returnOutput_exact (outputWord : List WorkSymbol)
    (leftSuffix right : List WorkSymbol)
    (hOutput : ∀ symbol, List.Mem symbol outputWord → OutputCell symbol) :
    workRunExact? terminalOutputPacker outputWord.length
        (configAtLeftWord returnOutputState
          (outputWord ++ leftSuffix) right) =
      some (configAtLeftWord returnOutputState leftSuffix
        (pushLeft outputWord right)) := by
  apply scanLeftExact terminalOutputPacker returnOutputState OutputCell
  · intro head leftTail rightSide hHead
    exact returnOutput_step head hHead leftTail rightSide
  · exact hOutput

private theorem returnSource_exact (sourceWord : List WorkSymbol)
    (leftSuffix right : List WorkSymbol)
    (hSource : ∀ symbol, List.Mem symbol sourceWord → SourceCell symbol) :
    workRunExact? terminalOutputPacker sourceWord.length
        (configAtLeftWord returnSourceState
          (sourceWord ++ leftSuffix) right) =
      some (configAtLeftWord returnSourceState leftSuffix
        (pushLeft sourceWord right)) := by
  apply scanLeftExact terminalOutputPacker returnSourceState SourceCell
  · intro head leftTail rightSide hHead
    exact returnSource_step head hHead leftTail rightSide
  · exact hSource

private theorem packed_pair_iteration_exact (total processed : Nat)
    (first second : Bool) (rest : BitString)
    (existingFirst : WorkSymbol) (existingRest : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol)
    (hTotal : processed + (first :: second :: rest).length = total)
    (hExisting : ∀ symbol,
      List.Mem symbol (existingFirst :: existingRest) → OutputCell symbol) :
    workRunExact? terminalOutputPacker
        (2 * total + 2 * (existingFirst :: existingRest).length + 6)
        (packedLoopConfiguration processed (first :: second :: rest)
          (existingFirst :: existingRest) outsideLeft outsideRight) =
      some (packedLoopConfiguration (processed + 2) rest
        ((existingFirst :: existingRest) ++ [pairSymbol first second])
        outsideLeft (outsideTail outsideRight)) := by
  let boundary : List WorkSymbol := leftMarker :: outsideLeft
  let sourceLeft : List WorkSymbol :=
    pushLeft (bitSymbols rest)
      (WorkSymbol.blank :: WorkSymbol.blank ::
        pushLeft (List.replicate processed WorkSymbol.blank) boundary)
  let output := pairSymbol first second
  let existing := existingFirst :: existingRest
  let outputWord := output :: pushLeft existing []
  let outputRight :=
    pushLeft outputWord (leftMarker :: outsideTail outsideRight)
  let initial := packedLoopConfiguration processed
    (first :: second :: rest) existing outsideLeft outsideRight
  let afterBlanks := configAtWord seekPackedState
    (pushLeft (List.replicate processed WorkSymbol.blank) boundary)
    (bitSymbol first :: bitSymbol second :: bitSymbols rest ++
      rightMarker :: existing ++ leftMarker :: outsideRight)
  let afterFirst := configAtWord (packedRememberState first)
    (WorkSymbol.blank ::
      pushLeft (List.replicate processed WorkSymbol.blank) boundary)
    (bitSymbol second :: bitSymbols rest ++
      rightMarker :: existing ++ leftMarker :: outsideRight)
  let afterSecond := configAtWord (packedCarryState first second)
    (WorkSymbol.blank :: WorkSymbol.blank ::
      pushLeft (List.replicate processed WorkSymbol.blank) boundary)
    (bitSymbols rest ++
      rightMarker :: existing ++ leftMarker :: outsideRight)
  let afterCarry := configAtWord (packedCarryState first second)
    sourceLeft (rightMarker :: existing ++ leftMarker :: outsideRight)
  let afterMarker := configAtWord (seekOuterPairState first second)
    (rightMarker :: sourceLeft)
    (existing ++ leftMarker :: outsideRight)
  let afterSeek := configAtWord (seekOuterPairState first second)
    (pushLeft existing (rightMarker :: sourceLeft))
    (leftMarker :: outsideRight)
  let afterOuter := configAtWord installOuterState
    (output :: pushLeft existing (rightMarker :: sourceLeft)) outsideRight
  let afterInstall := configAtLeftWord returnOutputState
    (outputWord ++ rightMarker :: sourceLeft)
    (leftMarker :: outsideTail outsideRight)
  let afterReturnOutput := configAtLeftWord returnOutputState
    (rightMarker :: sourceLeft) outputRight
  let afterReturnMarker := configAtLeftWord returnSourceState
    ((pushLeft (sourceSymbols (processed + 2) rest) []) ++ boundary)
    (rightMarker :: outputRight)
  let afterReturnSource := configAtLeftWord returnSourceState boundary
    (sourceSymbols (processed + 2) rest ++
      rightMarker :: outputRight)
  let final := packedLoopConfiguration (processed + 2) rest
    (existing ++ [output]) outsideLeft (outsideTail outsideRight)
  have hSourceLeft : sourceLeft =
      pushLeft (sourceSymbols (processed + 2) rest) boundary := by
    dsimp [sourceLeft]
    change
      pushLeft (bitSymbols rest)
          (pushLeft (List.replicate 2 WorkSymbol.blank)
            (pushLeft (List.replicate processed WorkSymbol.blank) boundary)) = _
    exact pushLeft_source_after processed 2 rest boundary
  have hOutput : OutputCell output := by
    dsimp [output]
    exact pairSymbol_outputCell first second
  have hExisting' : ∀ symbol, List.Mem symbol existing →
      OutputCell symbol := by
    dsimp [existing]
    exact hExisting
  have hOutputWord : ∀ symbol, List.Mem symbol outputWord →
      OutputCell symbol := by
    dsimp [outputWord]
    intro symbol found
    cases found with
    | head => exact hOutput
    | tail _ tailMem =>
        exact pushedOutput_areOutputCells existing hExisting' symbol tailMem
  have hBlanks : workRunExact? terminalOutputPacker processed initial =
      some afterBlanks := by
    dsimp [initial, afterBlanks, packedLoopConfiguration, boundary,
      existing, sourceSymbols, bitSymbols]
    simpa only [bitSymbols, listNil_append, listCons_append,
      listAppend_nil, listAppend_assoc] using
      seekPacked_blanks_exact processed (leftMarker :: outsideLeft)
        (bitSymbol first :: bitSymbol second :: bitSymbols rest ++
          rightMarker :: existingFirst :: existingRest ++
            leftMarker :: outsideRight)
  have hFirst : workRunExact? terminalOutputPacker 1 afterBlanks =
      some afterFirst := by
    apply workRunExact_one
    dsimp [afterBlanks, afterFirst]
    exact seekPacked_bit_step first
      (pushLeft (List.replicate processed WorkSymbol.blank) boundary)
      (bitSymbol second)
      (bitSymbols rest ++ rightMarker :: existing ++
        leftMarker :: outsideRight)
  have hSecond : workRunExact? terminalOutputPacker 1 afterFirst =
      some afterSecond := by
    apply workRunExact_one
    dsimp [afterFirst, afterSecond]
    simpa only [listNil_append, listCons_append, listAppend_nil,
      listAppend_assoc] using
      rememberPacked_pair_bits_step first second rest
      (WorkSymbol.blank ::
        pushLeft (List.replicate processed WorkSymbol.blank) boundary)
      rightMarker (existing ++ leftMarker :: outsideRight)
  have hCarry : workRunExact? terminalOutputPacker rest.length afterSecond =
      some afterCarry := by
    dsimp [afterSecond, afterCarry]
    simpa only [sourceLeft, listNil_append, listCons_append,
      listAppend_nil, listAppend_assoc] using
      packedCarry_bits_exact first second rest
      (WorkSymbol.blank :: WorkSymbol.blank ::
        pushLeft (List.replicate processed WorkSymbol.blank) boundary)
      (rightMarker :: existing ++ leftMarker :: outsideRight)
  have hMarker : workRunExact? terminalOutputPacker 1 afterCarry =
      some afterMarker := by
    apply workRunExact_one
    dsimp [afterCarry, afterMarker]
    exact packedCarry_marker_step first second sourceLeft existingFirst
      (existingRest ++ leftMarker :: outsideRight)
  have hSeek : workRunExact? terminalOutputPacker existing.length afterMarker =
      some afterSeek := by
    dsimp [afterMarker, afterSeek]
    simpa only [output, seekOuterStateFor_pair] using
      seekOuter_output_exact output hOutput existing
        (rightMarker :: sourceLeft) (leftMarker :: outsideRight) hExisting'
  have hOuter : workRunExact? terminalOutputPacker 1 afterSeek =
      some afterOuter := by
    apply workRunExact_one
    dsimp [afterSeek, afterOuter]
    simpa only [output, seekOuterStateFor_pair] using
      seekOuter_marker_word_step output hOutput
        (pushLeft existing (rightMarker :: sourceLeft)) outsideRight
  have hOuterNormalized : afterOuter = configAtWord installOuterState
      (output :: pushLeft existing (rightMarker :: sourceLeft))
      outsideRight := rfl
  have hInstall : workRunExact? terminalOutputPacker 1 afterOuter =
      some afterInstall := by
    apply workRunExact_one
    rw [hOuterNormalized]
    have hStep := installOuter_word_step output hOutput
      (pushLeft existing (rightMarker :: sourceLeft)) outsideRight
    dsimp [afterInstall, outputWord]
    rw [← pushLeft_append_far existing [] (rightMarker :: sourceLeft)]
    exact hStep
  have hReturnOutput : workRunExact? terminalOutputPacker outputWord.length
      afterInstall = some afterReturnOutput := by
    dsimp [afterInstall, afterReturnOutput]
    exact returnOutput_exact outputWord (rightMarker :: sourceLeft)
      (leftMarker :: outsideTail outsideRight) hOutputWord
  have hReturnMarker : workRunExact? terminalOutputPacker 1
      afterReturnOutput = some afterReturnMarker := by
    apply workRunExact_one
    dsimp [afterReturnOutput, afterReturnMarker]
    rw [hSourceLeft]
    have hSplit :
        pushLeft (sourceSymbols (processed + 2) rest) boundary =
          pushLeft (sourceSymbols (processed + 2) rest) [] ++ boundary := by
      change pushLeft (sourceSymbols (processed + 2) rest) ([] ++ boundary) = _
      exact pushLeft_append_far
        (sourceSymbols (processed + 2) rest) [] boundary
    rw [hSplit]
    exact returnOutput_marker_step
        (pushLeft (sourceSymbols (processed + 2) rest) [] ++ boundary)
        outputRight
  have hSourceLength :
      (pushLeft (sourceSymbols (processed + 2) rest) []).length = total := by
    rw [pushLeft_length, sourceSymbols_length]
    simp only [List.length_nil, Nat.add_zero]
    rw [addTwoBefore]
    change processed + (rest.length + 1 + 1) = total at hTotal
    exact hTotal
  have hReturnSource : workRunExact? terminalOutputPacker total
      afterReturnMarker = some afterReturnSource := by
    have hRun := returnSource_exact
      (pushLeft (sourceSymbols (processed + 2) rest) []) boundary
      (rightMarker :: outputRight)
      (pushedSource_areSourceCells (processed + 2) rest)
    rw [hSourceLength] at hRun
    dsimp [afterReturnMarker, afterReturnSource]
    rw [pushLeft_cancel] at hRun
    exact hRun
  have hBoundary : workRunExact? terminalOutputPacker 1 afterReturnSource =
      some final := by
    apply workRunExact_one
    dsimp [afterReturnSource, final, packedLoopConfiguration, boundary]
    have hStep := returnSource_marker_step outsideLeft
      (sourceSymbols (processed + 2) rest ++
        rightMarker :: outputRight)
    dsimp [outputRight, outputWord] at hStep ⊢
    rw [pushLeft_newOutput output existing
      (leftMarker :: outsideTail outsideRight)] at hStep ⊢
    simpa only [listNil_append, listCons_append, listAppend_nil,
      listAppend_assoc] using hStep
  have throughFirst := workRunExact_compose terminalOutputPacker processed 1
    initial afterBlanks afterFirst hBlanks hFirst
  have throughSecond := workRunExact_compose terminalOutputPacker
    (processed + 1) 1 initial afterFirst afterSecond throughFirst hSecond
  have throughCarry := workRunExact_compose terminalOutputPacker
    ((processed + 1) + 1) rest.length initial afterSecond afterCarry
    throughSecond hCarry
  have throughMarker := workRunExact_compose terminalOutputPacker
    (((processed + 1) + 1) + rest.length) 1 initial afterCarry afterMarker
    throughCarry hMarker
  have throughSeek := workRunExact_compose terminalOutputPacker
    ((((processed + 1) + 1) + rest.length) + 1) existing.length
    initial afterMarker afterSeek throughMarker hSeek
  have throughOuter := workRunExact_compose terminalOutputPacker
    (((((processed + 1) + 1) + rest.length) + 1) + existing.length) 1
    initial afterSeek afterOuter throughSeek hOuter
  have throughInstall := workRunExact_compose terminalOutputPacker
    ((((((processed + 1) + 1) + rest.length) + 1) + existing.length) + 1) 1
    initial afterOuter afterInstall throughOuter hInstall
  have throughReturnOutput := workRunExact_compose terminalOutputPacker
    (((((((processed + 1) + 1) + rest.length) + 1) + existing.length) + 1) + 1)
    outputWord.length initial afterInstall afterReturnOutput throughInstall
    hReturnOutput
  have throughReturnMarker := workRunExact_compose terminalOutputPacker
    ((((((((processed + 1) + 1) + rest.length) + 1) + existing.length) + 1) + 1) +
      outputWord.length) 1 initial afterReturnOutput afterReturnMarker
    throughReturnOutput hReturnMarker
  have throughReturnSource := workRunExact_compose terminalOutputPacker
    (((((((((processed + 1) + 1) + rest.length) + 1) + existing.length) + 1) + 1) +
      outputWord.length) + 1) total initial afterReturnMarker afterReturnSource
    throughReturnMarker hReturnSource
  have complete := workRunExact_compose terminalOutputPacker
    ((((((((((processed + 1) + 1) + rest.length) + 1) + existing.length) + 1) + 1) +
      outputWord.length) + 1) + total) 1 initial afterReturnSource final
    throughReturnSource hBoundary
  have hOutputWordLength : outputWord.length = existing.length + 1 := by
    dsimp [outputWord]
    rw [pushLeft_length]
    change existing.length + 0 + 1 = existing.length + 1
    rw [Nat.add_zero]
  have hSteps :
      (((((((((((processed + 1) + 1) + rest.length) + 1) + existing.length) + 1) + 1) +
        outputWord.length) + 1) + total) + 1) =
        2 * total + 2 * existing.length + 6 := by
    apply packedPairIterationFuelArithmetic processed rest.length
      existing.length outputWord.length total
    · rw [addTwoBefore]
      change processed + (rest.length + 1 + 1) = total at hTotal
      exact hTotal
    · exact hOutputWordLength
  rw [hSteps] at complete
  dsimp [initial, final, existing, output] at complete ⊢
  exact complete

private theorem packed_single_iteration_exact (total processed : Nat)
    (bit : Bool) (existingFirst : WorkSymbol)
    (existingRest outsideLeft outsideRight : List WorkSymbol)
    (hTotal : processed + [bit].length = total)
    (hExisting : ∀ symbol,
      List.Mem symbol (existingFirst :: existingRest) → OutputCell symbol) :
    workRunExact? terminalOutputPacker
        (2 * total + 2 * (existingFirst :: existingRest).length + 6)
        (packedLoopConfiguration processed [bit]
          (existingFirst :: existingRest) outsideLeft outsideRight) =
      some (packedLoopConfiguration (processed + 1) []
        ((existingFirst :: existingRest) ++ [bitSymbol bit])
        outsideLeft (outsideTail outsideRight)) := by
  let boundary : List WorkSymbol := leftMarker :: outsideLeft
  let sourceLeft : List WorkSymbol :=
    WorkSymbol.blank ::
      pushLeft (List.replicate processed WorkSymbol.blank) boundary
  let output := bitSymbol bit
  let existing := existingFirst :: existingRest
  let outputWord := output :: pushLeft existing []
  let outputRight :=
    pushLeft outputWord (leftMarker :: outsideTail outsideRight)
  let initial := packedLoopConfiguration processed [bit]
    existing outsideLeft outsideRight
  let afterBlanks := configAtWord seekPackedState
    (pushLeft (List.replicate processed WorkSymbol.blank) boundary)
    (bitSymbol bit :: rightMarker :: existing ++ leftMarker :: outsideRight)
  let afterBit := configAtWord (packedRememberState bit) sourceLeft
    (rightMarker :: existing ++ leftMarker :: outsideRight)
  let afterRemember := configAtWord (seekOuterSingleState bit)
    (rightMarker :: sourceLeft) (existing ++ leftMarker :: outsideRight)
  let afterSeek := configAtWord (seekOuterSingleState bit)
    (pushLeft existing (rightMarker :: sourceLeft))
    (leftMarker :: outsideRight)
  let afterOuter := configAtWord installOuterState
    (output :: pushLeft existing (rightMarker :: sourceLeft)) outsideRight
  let afterInstall := configAtLeftWord returnOutputState
    (outputWord ++ rightMarker :: sourceLeft)
    (leftMarker :: outsideTail outsideRight)
  let afterReturnOutput := configAtLeftWord returnOutputState
    (rightMarker :: sourceLeft) outputRight
  let afterReturnMarker := configAtLeftWord returnSourceState
    ((pushLeft (sourceSymbols (processed + 1) []) []) ++ boundary)
    (rightMarker :: outputRight)
  let afterReturnSource := configAtLeftWord returnSourceState boundary
    (sourceSymbols (processed + 1) [] ++ rightMarker :: outputRight)
  let final := packedLoopConfiguration (processed + 1) []
    (existing ++ [output]) outsideLeft (outsideTail outsideRight)
  have hSourceLeft : sourceLeft =
      pushLeft (sourceSymbols (processed + 1) []) boundary := by
    dsimp [sourceLeft]
    change
      pushLeft (bitSymbols [])
          (pushLeft (List.replicate 1 WorkSymbol.blank)
            (pushLeft (List.replicate processed WorkSymbol.blank) boundary)) = _
    exact pushLeft_source_after processed 1 [] boundary
  have hOutput : OutputCell output := by
    dsimp [output]
    exact bitSymbol_outputCell bit
  have hExisting' : ∀ symbol, List.Mem symbol existing →
      OutputCell symbol := by
    dsimp [existing]
    exact hExisting
  have hOutputWord : ∀ symbol, List.Mem symbol outputWord →
      OutputCell symbol := by
    dsimp [outputWord]
    intro symbol found
    cases found with
    | head => exact hOutput
    | tail _ tailMem =>
        exact pushedOutput_areOutputCells existing hExisting' symbol tailMem
  have hBlanks : workRunExact? terminalOutputPacker processed initial =
      some afterBlanks := by
    dsimp [initial, afterBlanks, packedLoopConfiguration, boundary,
      existing, sourceSymbols, bitSymbols]
    simpa only [bitSymbols, listNil_append, listCons_append,
      listAppend_nil, listAppend_assoc] using
      seekPacked_blanks_exact processed (leftMarker :: outsideLeft)
        (bitSymbol bit :: rightMarker :: existingFirst :: existingRest ++
          leftMarker :: outsideRight)
  have hBit : workRunExact? terminalOutputPacker 1 afterBlanks =
      some afterBit := by
    apply workRunExact_one
    dsimp [afterBlanks, afterBit, sourceLeft]
    exact seekPacked_bit_step bit
      (pushLeft (List.replicate processed WorkSymbol.blank) boundary)
      rightMarker (existing ++ leftMarker :: outsideRight)
  have hRemember : workRunExact? terminalOutputPacker 1 afterBit =
      some afterRemember := by
    apply workRunExact_one
    dsimp [afterBit, afterRemember]
    exact rememberPacked_single_step bit sourceLeft existingFirst
      (existingRest ++ leftMarker :: outsideRight)
  have hSeek : workRunExact? terminalOutputPacker existing.length afterRemember =
      some afterSeek := by
    dsimp [afterRemember, afterSeek]
    simpa only [output, seekOuterStateFor_single] using
      seekOuter_output_exact output hOutput existing
        (rightMarker :: sourceLeft) (leftMarker :: outsideRight) hExisting'
  have hOuter : workRunExact? terminalOutputPacker 1 afterSeek =
      some afterOuter := by
    apply workRunExact_one
    dsimp [afterSeek, afterOuter]
    simpa only [output, seekOuterStateFor_single] using
      seekOuter_marker_word_step output hOutput
        (pushLeft existing (rightMarker :: sourceLeft)) outsideRight
  have hInstall : workRunExact? terminalOutputPacker 1 afterOuter =
      some afterInstall := by
    apply workRunExact_one
    dsimp [afterOuter]
    have hStep := installOuter_word_step output hOutput
      (pushLeft existing (rightMarker :: sourceLeft)) outsideRight
    dsimp [afterInstall, outputWord]
    rw [← pushLeft_append_far existing [] (rightMarker :: sourceLeft)]
    exact hStep
  have hReturnOutput : workRunExact? terminalOutputPacker outputWord.length
      afterInstall = some afterReturnOutput := by
    dsimp [afterInstall, afterReturnOutput]
    exact returnOutput_exact outputWord (rightMarker :: sourceLeft)
      (leftMarker :: outsideTail outsideRight) hOutputWord
  have hReturnMarker : workRunExact? terminalOutputPacker 1
      afterReturnOutput = some afterReturnMarker := by
    apply workRunExact_one
    dsimp [afterReturnOutput, afterReturnMarker]
    rw [hSourceLeft]
    have hSplit :
        pushLeft (sourceSymbols (processed + 1) []) boundary =
          pushLeft (sourceSymbols (processed + 1) []) [] ++ boundary := by
      change pushLeft (sourceSymbols (processed + 1) []) ([] ++ boundary) = _
      exact pushLeft_append_far (sourceSymbols (processed + 1) []) [] boundary
    rw [hSplit]
    exact returnOutput_marker_step
      (pushLeft (sourceSymbols (processed + 1) []) [] ++ boundary)
      outputRight
  have hSourceLength :
      (pushLeft (sourceSymbols (processed + 1) []) []).length = total := by
    rw [pushLeft_length, sourceSymbols_length]
    simp only [List.length_nil, Nat.add_zero]
    change processed + 1 = total at hTotal
    exact hTotal
  have hReturnSource : workRunExact? terminalOutputPacker total
      afterReturnMarker = some afterReturnSource := by
    have hRun := returnSource_exact
      (pushLeft (sourceSymbols (processed + 1) []) []) boundary
      (rightMarker :: outputRight)
      (pushedSource_areSourceCells (processed + 1) [])
    rw [hSourceLength] at hRun
    dsimp [afterReturnMarker, afterReturnSource]
    rw [pushLeft_cancel] at hRun
    exact hRun
  have hBoundary : workRunExact? terminalOutputPacker 1 afterReturnSource =
      some final := by
    apply workRunExact_one
    dsimp [afterReturnSource, final, packedLoopConfiguration, boundary]
    have hStep := returnSource_marker_step outsideLeft
      (sourceSymbols (processed + 1) [] ++ rightMarker :: outputRight)
    dsimp [outputRight, outputWord] at hStep ⊢
    rw [pushLeft_newOutput output existing
      (leftMarker :: outsideTail outsideRight)] at hStep ⊢
    simpa only [listNil_append, listCons_append, listAppend_nil,
      listAppend_assoc] using hStep
  have throughBit := workRunExact_compose terminalOutputPacker processed 1
    initial afterBlanks afterBit hBlanks hBit
  have throughRemember := workRunExact_compose terminalOutputPacker
    (processed + 1) 1 initial afterBit afterRemember throughBit hRemember
  have throughSeek := workRunExact_compose terminalOutputPacker
    ((processed + 1) + 1) existing.length initial afterRemember afterSeek
    throughRemember hSeek
  have throughOuter := workRunExact_compose terminalOutputPacker
    (((processed + 1) + 1) + existing.length) 1 initial afterSeek afterOuter
    throughSeek hOuter
  have throughInstall := workRunExact_compose terminalOutputPacker
    ((((processed + 1) + 1) + existing.length) + 1) 1
    initial afterOuter afterInstall throughOuter hInstall
  have throughReturnOutput := workRunExact_compose terminalOutputPacker
    (((((processed + 1) + 1) + existing.length) + 1) + 1)
    outputWord.length initial afterInstall afterReturnOutput throughInstall
    hReturnOutput
  have throughReturnMarker := workRunExact_compose terminalOutputPacker
    ((((((processed + 1) + 1) + existing.length) + 1) + 1) +
      outputWord.length) 1 initial afterReturnOutput afterReturnMarker
    throughReturnOutput hReturnMarker
  have throughReturnSource := workRunExact_compose terminalOutputPacker
    (((((((processed + 1) + 1) + existing.length) + 1) + 1) +
      outputWord.length) + 1) total initial afterReturnMarker afterReturnSource
    throughReturnMarker hReturnSource
  have complete := workRunExact_compose terminalOutputPacker
    ((((((((processed + 1) + 1) + existing.length) + 1) + 1) +
      outputWord.length) + 1) + total) 1 initial afterReturnSource final
    throughReturnSource hBoundary
  have hOutputWordLength : outputWord.length = existing.length + 1 := by
    dsimp [outputWord]
    rw [pushLeft_length]
    change existing.length + 0 + 1 = existing.length + 1
    rw [Nat.add_zero]
  have hSteps :
      (((((((((processed + 1) + 1) + existing.length) + 1) + 1) +
        outputWord.length) + 1) + total) + 1) =
        2 * total + 2 * existing.length + 6 := by
    apply packedSingleIterationFuelArithmetic processed existing.length
      outputWord.length total
    · change processed + 1 = total at hTotal
      exact hTotal
    · exact hOutputWordLength
  rw [hSteps] at complete
  dsimp [initial, final, existing, output] at complete ⊢
  exact complete

private theorem packed_loop_done_exact (total processed : Nat)
    (existingFirst : WorkSymbol)
    (existingRest outsideLeft outsideRight : List WorkSymbol)
    (hTotal : processed + ([] : BitString).length = total) :
    workRunExact? terminalOutputPacker
        (packedLoopSteps total (existingFirst :: existingRest).length [])
        (packedLoopConfiguration processed []
          (existingFirst :: existingRest) outsideLeft outsideRight) =
      some (packedFinalConfiguration total (existingFirst :: existingRest)
        outsideLeft outsideRight) := by
  let boundary : List WorkSymbol := leftMarker :: outsideLeft
  let initial := packedLoopConfiguration processed []
    (existingFirst :: existingRest) outsideLeft outsideRight
  let afterBlanks := configAtWord seekPackedState
    (pushLeft (List.replicate processed WorkSymbol.blank) boundary)
    (rightMarker :: existingFirst :: existingRest ++
      leftMarker :: outsideRight)
  let final := packedFinalConfiguration total
    (existingFirst :: existingRest) outsideLeft outsideRight
  have hBlanks : workRunExact? terminalOutputPacker processed initial =
      some afterBlanks := by
    dsimp [initial, afterBlanks, packedLoopConfiguration, sourceSymbols,
      bitSymbols, boundary]
    simpa only [listNil_append, listCons_append, listAppend_nil,
      listAppend_assoc] using
      seekPacked_blanks_exact processed (leftMarker :: outsideLeft)
        (rightMarker :: existingFirst :: existingRest ++
          leftMarker :: outsideRight)
  have hDone : workRunExact? terminalOutputPacker 1 afterBlanks =
      some final := by
    apply workRunExact_one
    dsimp [afterBlanks, final, packedFinalConfiguration, boundary]
    simp only [List.length_nil, Nat.add_zero] at hTotal
    subst total
    exact seekPacked_done_step
      (pushLeft (List.replicate processed WorkSymbol.blank)
        (leftMarker :: outsideLeft))
      existingFirst (existingRest ++ leftMarker :: outsideRight)
  have complete := workRunExact_compose terminalOutputPacker processed 1
    initial afterBlanks final hBlanks hDone
  simp only [List.length_nil, Nat.add_zero] at hTotal
  subst total
  dsimp [packedLoopSteps]
  exact complete

private theorem bitString_twoStepInduction {Property : BitString → Prop}
    (empty : Property [])
    (single : ∀ bit, Property [bit])
    (pair : ∀ first second rest,
      Property rest → Property (first :: second :: rest)) :
    ∀ bits, Property bits := by
  have strong : ∀ bits,
      Property bits ∧ ∀ first, Property (first :: bits) := by
    intro bits
    induction bits with
    | nil => exact ⟨empty, single⟩
    | cons second rest ih =>
        exact
          ⟨ih.2 second,
           fun first => pair first second rest ih.1⟩
  intro bits
  exact (strong bits).1

private theorem packed_loop_exact (remaining : BitString) :
    ∀ (total processed : Nat) (existingFirst : WorkSymbol)
      (existingRest outsideLeft outsideRight : List WorkSymbol),
      processed + remaining.length = total →
      (∀ symbol,
        List.Mem symbol (existingFirst :: existingRest) →
          OutputCell symbol) →
      workRunExact? terminalOutputPacker
          (packedLoopSteps total (existingFirst :: existingRest).length
            remaining)
          (packedLoopConfiguration processed remaining
            (existingFirst :: existingRest) outsideLeft outsideRight) =
        some (packedFinalConfiguration total
          ((existingFirst :: existingRest) ++ packedSymbols remaining)
          outsideLeft (packedLoopOutside remaining outsideRight)) := by
  apply bitString_twoStepInduction
    (Property := fun remaining =>
      ∀ (total processed : Nat) (existingFirst : WorkSymbol)
        (existingRest outsideLeft outsideRight : List WorkSymbol),
        processed + remaining.length = total →
        (∀ symbol,
          List.Mem symbol (existingFirst :: existingRest) →
            OutputCell symbol) →
        workRunExact? terminalOutputPacker
            (packedLoopSteps total (existingFirst :: existingRest).length
              remaining)
            (packedLoopConfiguration processed remaining
              (existingFirst :: existingRest) outsideLeft outsideRight) =
          some (packedFinalConfiguration total
            ((existingFirst :: existingRest) ++ packedSymbols remaining)
            outsideLeft (packedLoopOutside remaining outsideRight)))
  · intro total processed existingFirst existingRest outsideLeft outsideRight
      hTotal _
    simpa only [packedSymbols, packedLoopOutside, listNil_append,
      listCons_append, listAppend_nil] using
      packed_loop_done_exact total processed existingFirst existingRest
        outsideLeft outsideRight hTotal
  · intro bit total processed existingFirst existingRest outsideLeft
      outsideRight hTotal hExisting
    let output := bitSymbol bit
    have hIteration := packed_single_iteration_exact total processed bit
      existingFirst existingRest outsideLeft outsideRight hTotal hExisting
    have hNextTotal : (processed + 1) + ([] : BitString).length = total := by
      simpa only [List.length_cons, List.length_nil] using hTotal
    have hDone := packed_loop_done_exact total (processed + 1)
      existingFirst (existingRest ++ [output]) outsideLeft
      (outsideTail outsideRight) hNextTotal
    have complete := workRunExact_compose terminalOutputPacker
      (2 * total + 2 * (existingFirst :: existingRest).length + 6)
      (packedLoopSteps total
        (existingFirst :: existingRest ++ [output]).length [])
      (packedLoopConfiguration processed [bit]
        (existingFirst :: existingRest) outsideLeft outsideRight)
      (packedLoopConfiguration (processed + 1) []
        (existingFirst :: existingRest ++ [output])
        outsideLeft (outsideTail outsideRight))
      (packedFinalConfiguration total
        (existingFirst :: existingRest ++ [output])
        outsideLeft (outsideTail outsideRight))
      hIteration hDone
    dsimp [output] at complete ⊢
    simpa only [packedLoopSteps, packedSymbols, packedLoopOutside,
      listNil_append, listCons_append, listAppend_nil, listLength_append,
      List.length, listAppend_assoc, Nat.add_zero] using complete
  · intro first second rest ih total processed existingFirst existingRest
      outsideLeft outsideRight hTotal hExisting
    let output := pairSymbol first second
    have hIteration := packed_pair_iteration_exact total processed first second
      rest existingFirst existingRest outsideLeft outsideRight hTotal hExisting
    have hNextTotal : (processed + 2) + rest.length = total := by
      rw [addTwoBefore]
      change processed + (rest.length + 1 + 1) = total at hTotal
      exact hTotal
    have hExistingNext : ∀ symbol,
        List.Mem symbol
          (existingFirst :: (existingRest ++ [output])) →
          OutputCell symbol := by
      intro symbol found
      cases found with
      | head => exact hExisting existingFirst (List.Mem.head existingRest)
      | tail _ tailMem =>
          apply outputCells_append existingRest [output]
          · intro candidate candidateMem
            exact hExisting candidate
              (List.Mem.tail existingFirst candidateMem)
          · intro candidate candidateMem
            cases candidateMem with
            | head =>
                dsimp [output]
                exact pairSymbol_outputCell first second
            | tail _ impossible => contradiction
          · exact tailMem
    have hTail := ih total (processed + 2) existingFirst
      (existingRest ++ [output]) outsideLeft (outsideTail outsideRight)
      hNextTotal hExistingNext
    have complete := workRunExact_compose terminalOutputPacker
      (2 * total + 2 * (existingFirst :: existingRest).length + 6)
      (packedLoopSteps total
        (existingFirst :: existingRest ++ [output]).length rest)
      (packedLoopConfiguration processed (first :: second :: rest)
        (existingFirst :: existingRest) outsideLeft outsideRight)
      (packedLoopConfiguration (processed + 2) rest
        (existingFirst :: existingRest ++ [output])
        outsideLeft (outsideTail outsideRight))
      (packedFinalConfiguration total
        ((existingFirst :: existingRest ++ [output]) ++
          packedSymbols rest)
        outsideLeft
        (packedLoopOutside rest (outsideTail outsideRight)))
      hIteration hTail
    dsimp [output] at complete ⊢
    simpa only [packedLoopSteps, packedSymbols, packedLoopOutside,
      listNil_append, listCons_append, listAppend_nil, listLength_append,
      List.length, listAppend_assoc, Nat.add_zero] using complete

private theorem first_pair_iteration_exact (total : Nat)
    (first second : Bool) (rest : BitString)
    (outsideLeft outsideRight : List WorkSymbol)
    (hTotal : (first :: second :: rest).length = total) :
    workRunExact? terminalOutputPacker (2 * total + 6)
        (configAtWord startState (leftMarker :: outsideLeft)
          (bitSymbol first :: bitSymbol second :: bitSymbols rest ++
            rightMarker :: outsideRight)) =
      some (packedLoopConfiguration 2 rest [pairSymbol first second]
        outsideLeft (outsideTail (outsideTail outsideRight))) := by
  let boundary : List WorkSymbol := leftMarker :: outsideLeft
  let sourceLeft : List WorkSymbol :=
    pushLeft (bitSymbols rest)
      (WorkSymbol.blank :: WorkSymbol.blank :: boundary)
  let output := pairSymbol first second
  let initial := configAtWord startState boundary
    (bitSymbol first :: bitSymbol second :: bitSymbols rest ++
      rightMarker :: outsideRight)
  let afterFirst := configAtWord (firstRememberState first)
    (WorkSymbol.blank :: boundary)
    (bitSymbol second :: bitSymbols rest ++
      rightMarker :: outsideRight)
  let afterSecond := configAtWord (firstCarryState first second)
    (WorkSymbol.blank :: WorkSymbol.blank :: boundary)
    (bitSymbols rest ++ rightMarker :: outsideRight)
  let afterCarry := configAtWord (firstCarryState first second)
    sourceLeft (rightMarker :: outsideRight)
  let afterMarker := configAtWord (firstWritePairState first second)
    (rightMarker :: sourceLeft) outsideRight
  let afterWrite := configAtWord installOuterState
    (output :: rightMarker :: sourceLeft) (outsideTail outsideRight)
  let afterInstall := configAtLeftWord returnOutputState
    (output :: rightMarker :: sourceLeft)
    (leftMarker :: outsideTail (outsideTail outsideRight))
  let afterReturnOutput := configAtLeftWord returnOutputState
    (rightMarker :: sourceLeft)
    (output :: leftMarker :: outsideTail (outsideTail outsideRight))
  let afterReturnMarker := configAtLeftWord returnSourceState
    ((pushLeft (sourceSymbols 2 rest) []) ++ boundary)
    (rightMarker :: output :: leftMarker ::
      outsideTail (outsideTail outsideRight))
  let afterReturnSource := configAtLeftWord returnSourceState boundary
    (sourceSymbols 2 rest ++ rightMarker :: output :: leftMarker ::
      outsideTail (outsideTail outsideRight))
  let final := packedLoopConfiguration 2 rest [output]
    outsideLeft (outsideTail (outsideTail outsideRight))
  have hSourceLeft : sourceLeft =
      pushLeft (sourceSymbols 2 rest) boundary := by
    dsimp [sourceLeft]
    change
      pushLeft (bitSymbols rest)
          (pushLeft (List.replicate 2 WorkSymbol.blank)
            (pushLeft (List.replicate 0 WorkSymbol.blank) boundary)) = _
    exact pushLeft_source_after 0 2 rest boundary
  have hOutput : OutputCell output := by
    dsimp [output]
    exact pairSymbol_outputCell first second
  have hStart : workRunExact? terminalOutputPacker 1 initial =
      some afterFirst := by
    apply workRunExact_one
    dsimp [initial, afterFirst]
    exact start_bit_step first boundary (bitSymbol second)
      (bitSymbols rest ++ rightMarker :: outsideRight)
  have hSecond : workRunExact? terminalOutputPacker 1 afterFirst =
      some afterSecond := by
    apply workRunExact_one
    dsimp [afterFirst, afterSecond]
    simpa only [listNil_append, listCons_append, listAppend_nil,
      listAppend_assoc] using
      rememberFirst_pair_bits_step first second rest
        (WorkSymbol.blank :: boundary) rightMarker
        outsideRight
  have hCarry : workRunExact? terminalOutputPacker rest.length afterSecond =
      some afterCarry := by
    dsimp [afterSecond, afterCarry]
    simpa only [sourceLeft, listNil_append, listCons_append,
      listAppend_nil, listAppend_assoc] using
      firstCarry_bits_exact first second rest
        (WorkSymbol.blank :: WorkSymbol.blank :: boundary)
        (rightMarker :: outsideRight)
  have hMarker : workRunExact? terminalOutputPacker 1 afterCarry =
      some afterMarker := by
    apply workRunExact_one
    dsimp [afterCarry, afterMarker]
    exact firstCarry_marker_word_step first second sourceLeft outsideRight
  have hWrite : workRunExact? terminalOutputPacker 1 afterMarker =
      some afterWrite := by
    apply workRunExact_one
    dsimp [afterMarker, afterWrite]
    exact firstWrite_pair_word_step first second
      (rightMarker :: sourceLeft) outsideRight
  have hInstall : workRunExact? terminalOutputPacker 1 afterWrite =
      some afterInstall := by
    apply workRunExact_one
    dsimp [afterWrite, afterInstall]
    exact installOuter_word_step output hOutput (rightMarker :: sourceLeft)
      (outsideTail outsideRight)
  have hReturnOutput : workRunExact? terminalOutputPacker 1 afterInstall =
      some afterReturnOutput := by
    dsimp [afterInstall, afterReturnOutput]
    exact returnOutput_exact [output] (rightMarker :: sourceLeft)
      (leftMarker :: outsideTail (outsideTail outsideRight))
      (by
        intro symbol found
        cases found with
        | head => exact hOutput
        | tail _ tailMem => contradiction)
  have hReturnMarker : workRunExact? terminalOutputPacker 1
      afterReturnOutput = some afterReturnMarker := by
    apply workRunExact_one
    dsimp [afterReturnOutput, afterReturnMarker]
    rw [hSourceLeft]
    have hSplit : pushLeft (sourceSymbols 2 rest) boundary =
        pushLeft (sourceSymbols 2 rest) [] ++ boundary := by
      change pushLeft (sourceSymbols 2 rest) ([] ++ boundary) = _
      exact pushLeft_append_far (sourceSymbols 2 rest) [] boundary
    rw [hSplit]
    exact returnOutput_marker_step
      (pushLeft (sourceSymbols 2 rest) [] ++ boundary)
      (output :: leftMarker :: outsideTail (outsideTail outsideRight))
  have hSourceLength : (pushLeft (sourceSymbols 2 rest) []).length =
      total := by
    rw [pushLeft_length, sourceSymbols_length]
    simp only [List.length_nil, Nat.add_zero]
    change rest.length + 1 + 1 = total at hTotal
    calc
      2 + rest.length = rest.length + 2 := Nat.add_comm 2 rest.length
      _ = rest.length + 1 + 1 := rfl
      _ = total := hTotal
  have hReturnSource : workRunExact? terminalOutputPacker total
      afterReturnMarker = some afterReturnSource := by
    have hRun := returnSource_exact (pushLeft (sourceSymbols 2 rest) [])
      boundary
      (rightMarker :: output :: leftMarker ::
        outsideTail (outsideTail outsideRight))
      (pushedSource_areSourceCells 2 rest)
    rw [hSourceLength] at hRun
    dsimp [afterReturnMarker, afterReturnSource]
    rw [pushLeft_cancel] at hRun
    exact hRun
  have hBoundary : workRunExact? terminalOutputPacker 1 afterReturnSource =
      some final := by
    apply workRunExact_one
    dsimp [afterReturnSource, final, packedLoopConfiguration, boundary]
    simpa only [listNil_append, listCons_append, listAppend_nil,
      listAppend_assoc] using
      returnSource_marker_step outsideLeft
        (sourceSymbols 2 rest ++ rightMarker :: output :: leftMarker ::
          outsideTail (outsideTail outsideRight))
  have throughSecond := workRunExact_compose terminalOutputPacker 1 1
    initial afterFirst afterSecond hStart hSecond
  have throughCarry := workRunExact_compose terminalOutputPacker (1 + 1)
    rest.length initial afterSecond afterCarry throughSecond hCarry
  have throughMarker := workRunExact_compose terminalOutputPacker
    ((1 + 1) + rest.length) 1 initial afterCarry afterMarker
    throughCarry hMarker
  have throughWrite := workRunExact_compose terminalOutputPacker
    (((1 + 1) + rest.length) + 1) 1 initial afterMarker afterWrite
    throughMarker hWrite
  have throughInstall := workRunExact_compose terminalOutputPacker
    ((((1 + 1) + rest.length) + 1) + 1) 1 initial afterWrite afterInstall
    throughWrite hInstall
  have throughReturnOutput := workRunExact_compose terminalOutputPacker
    (((((1 + 1) + rest.length) + 1) + 1) + 1) 1
    initial afterInstall afterReturnOutput throughInstall hReturnOutput
  have throughReturnMarker := workRunExact_compose terminalOutputPacker
    ((((((1 + 1) + rest.length) + 1) + 1) + 1) + 1) 1
    initial afterReturnOutput afterReturnMarker throughReturnOutput hReturnMarker
  have throughReturnSource := workRunExact_compose terminalOutputPacker
    (((((((1 + 1) + rest.length) + 1) + 1) + 1) + 1) + 1) total
    initial afterReturnMarker afterReturnSource throughReturnMarker
    hReturnSource
  have complete := workRunExact_compose terminalOutputPacker
    ((((((((1 + 1) + rest.length) + 1) + 1) + 1) + 1) + 1) + total) 1
    initial afterReturnSource final throughReturnSource hBoundary
  have hSteps :
      1 + 1 + rest.length + 1 + 1 + 1 + 1 + 1 + total + 1 =
        2 * total + 6 := by
    apply firstPairFuelArithmetic rest.length total
    change rest.length + 1 + 1 = total at hTotal
    calc
      2 + rest.length = rest.length + 2 := Nat.add_comm 2 rest.length
      _ = rest.length + 1 + 1 := rfl
      _ = total := hTotal
  rw [hSteps] at complete
  dsimp [initial, final, output, boundary] at complete ⊢
  exact complete

private theorem first_single_iteration_exact (total : Nat) (bit : Bool)
    (outsideLeft outsideRight : List WorkSymbol)
    (hTotal : [bit].length = total) :
    workRunExact? terminalOutputPacker (2 * total + 6)
        (configAtWord startState (leftMarker :: outsideLeft)
          (bitSymbol bit :: rightMarker :: outsideRight)) =
      some (packedLoopConfiguration 1 [] [bitSymbol bit]
        outsideLeft (outsideTail (outsideTail outsideRight))) := by
  let boundary : List WorkSymbol := leftMarker :: outsideLeft
  let sourceLeft : List WorkSymbol := WorkSymbol.blank :: boundary
  let output := bitSymbol bit
  let initial := configAtWord startState boundary
    (bitSymbol bit :: rightMarker :: outsideRight)
  let afterStart := configAtWord (firstRememberState bit) sourceLeft
    (rightMarker :: outsideRight)
  let afterRemember := configAtWord (firstWriteSingleState bit)
    (rightMarker :: sourceLeft) outsideRight
  let afterWrite := configAtWord installOuterState
    (output :: rightMarker :: sourceLeft) (outsideTail outsideRight)
  let afterInstall := configAtLeftWord returnOutputState
    (output :: rightMarker :: sourceLeft)
    (leftMarker :: outsideTail (outsideTail outsideRight))
  let afterReturnOutput := configAtLeftWord returnOutputState
    (rightMarker :: sourceLeft)
    (output :: leftMarker :: outsideTail (outsideTail outsideRight))
  let afterReturnMarker := configAtLeftWord returnSourceState
    ((pushLeft (sourceSymbols 1 []) []) ++ boundary)
    (rightMarker :: output :: leftMarker ::
      outsideTail (outsideTail outsideRight))
  let afterReturnSource := configAtLeftWord returnSourceState boundary
    (sourceSymbols 1 [] ++ rightMarker :: output :: leftMarker ::
      outsideTail (outsideTail outsideRight))
  let final := packedLoopConfiguration 1 [] [output]
    outsideLeft (outsideTail (outsideTail outsideRight))
  have hSourceLeft : sourceLeft =
      pushLeft (sourceSymbols 1 []) boundary := by
    rfl
  have hOutput : OutputCell output := by
    dsimp [output]
    exact bitSymbol_outputCell bit
  have hStart : workRunExact? terminalOutputPacker 1 initial =
      some afterStart := by
    apply workRunExact_one
    dsimp [initial, afterStart, sourceLeft]
    exact start_bit_step bit boundary rightMarker outsideRight
  have hRemember : workRunExact? terminalOutputPacker 1 afterStart =
      some afterRemember := by
    apply workRunExact_one
    dsimp [afterStart, afterRemember]
    exact rememberFirst_single_word_step bit sourceLeft outsideRight
  have hWrite : workRunExact? terminalOutputPacker 1 afterRemember =
      some afterWrite := by
    apply workRunExact_one
    dsimp [afterRemember, afterWrite]
    exact firstWrite_single_word_step bit (rightMarker :: sourceLeft)
      outsideRight
  have hInstall : workRunExact? terminalOutputPacker 1 afterWrite =
      some afterInstall := by
    apply workRunExact_one
    dsimp [afterWrite, afterInstall]
    exact installOuter_word_step output hOutput (rightMarker :: sourceLeft)
      (outsideTail outsideRight)
  have hReturnOutput : workRunExact? terminalOutputPacker 1 afterInstall =
      some afterReturnOutput := by
    dsimp [afterInstall, afterReturnOutput]
    exact returnOutput_exact [output] (rightMarker :: sourceLeft)
      (leftMarker :: outsideTail (outsideTail outsideRight))
      (by
        intro symbol found
        cases found with
        | head => exact hOutput
        | tail _ tailMem => contradiction)
  have hReturnMarker : workRunExact? terminalOutputPacker 1
      afterReturnOutput = some afterReturnMarker := by
    apply workRunExact_one
    dsimp [afterReturnOutput, afterReturnMarker]
    rw [hSourceLeft]
    have hSplit : pushLeft (sourceSymbols 1 []) boundary =
        pushLeft (sourceSymbols 1 []) [] ++ boundary := by
      change pushLeft (sourceSymbols 1 []) ([] ++ boundary) = _
      exact pushLeft_append_far (sourceSymbols 1 []) [] boundary
    rw [hSplit]
    exact returnOutput_marker_step
      (pushLeft (sourceSymbols 1 []) [] ++ boundary)
      (output :: leftMarker :: outsideTail (outsideTail outsideRight))
  have hSourceLength : (pushLeft (sourceSymbols 1 []) []).length =
      total := by
    rw [pushLeft_length, sourceSymbols_length]
    simp only [List.length_nil, Nat.add_zero]
    simpa only [List.length_cons, List.length_nil] using hTotal
  have hReturnSource : workRunExact? terminalOutputPacker total
      afterReturnMarker = some afterReturnSource := by
    have hRun := returnSource_exact (pushLeft (sourceSymbols 1 []) [])
      boundary
      (rightMarker :: output :: leftMarker ::
        outsideTail (outsideTail outsideRight))
      (pushedSource_areSourceCells 1 [])
    rw [hSourceLength] at hRun
    dsimp [afterReturnMarker, afterReturnSource]
    rw [pushLeft_cancel] at hRun
    exact hRun
  have hBoundary : workRunExact? terminalOutputPacker 1 afterReturnSource =
      some final := by
    apply workRunExact_one
    dsimp [afterReturnSource, final, packedLoopConfiguration, boundary]
    simpa only [listNil_append, listCons_append, listAppend_nil,
      listAppend_assoc] using
      returnSource_marker_step outsideLeft
        (sourceSymbols 1 [] ++ rightMarker :: output :: leftMarker ::
          outsideTail (outsideTail outsideRight))
  have throughRemember := workRunExact_compose terminalOutputPacker 1 1
    initial afterStart afterRemember hStart hRemember
  have throughWrite := workRunExact_compose terminalOutputPacker (1 + 1) 1
    initial afterRemember afterWrite throughRemember hWrite
  have throughInstall := workRunExact_compose terminalOutputPacker
    ((1 + 1) + 1) 1 initial afterWrite afterInstall throughWrite hInstall
  have throughReturnOutput := workRunExact_compose terminalOutputPacker
    (((1 + 1) + 1) + 1) 1 initial afterInstall afterReturnOutput
    throughInstall hReturnOutput
  have throughReturnMarker := workRunExact_compose terminalOutputPacker
    ((((1 + 1) + 1) + 1) + 1) 1 initial afterReturnOutput
    afterReturnMarker throughReturnOutput hReturnMarker
  have throughReturnSource := workRunExact_compose terminalOutputPacker
    (((((1 + 1) + 1) + 1) + 1) + 1) total initial afterReturnMarker
    afterReturnSource throughReturnMarker hReturnSource
  have complete := workRunExact_compose terminalOutputPacker
    ((((((1 + 1) + 1) + 1) + 1) + 1) + total) 1 initial
    afterReturnSource final throughReturnSource hBoundary
  have hSteps : 1 + 1 + 1 + 1 + 1 + 1 + total + 1 =
      2 * total + 6 := by
    apply firstSingleFuelArithmetic total
    change 1 = total at hTotal
    exact hTotal
  rw [hSteps] at complete
  dsimp [initial, final, output, boundary] at complete ⊢
  exact complete

/-! ### Public exact terminal-packing surface -/

/-- Canonical represented-output input to the terminal packer, with arbitrary
cells beyond both logical boundary markers. -/
def terminalOutputPackerInputTape (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) : WorkTape :=
  frameWithGarbage (Tape.ofInput bits) outsideLeft outsideRight

/-- Exact terminal work tape.  The original framed source has been blanked,
the old right marker is immediately to its right, and packed output starts at
the focus.  The new outer marker shields every unconsumed exterior cell. -/
def terminalOutputPackerFinalTape :
    BitString → List WorkSymbol → List WorkSymbol → WorkTape
  | [], outsideLeft, outsideRight =>
      { left := leftMarker :: outsideLeft
        head := WorkSymbol.blank
        right := rightMarker :: outsideRight }
  | [bit], outsideLeft, outsideRight =>
      { left := rightMarker ::
          (List.replicate [bit].length WorkSymbol.blank ++
            leftMarker :: outsideLeft)
        head := bitSymbol bit
        right := leftMarker ::
          terminalOutputPackerOutside [bit] outsideRight }
  | first :: second :: rest, outsideLeft, outsideRight =>
      { left := rightMarker ::
          (List.replicate (first :: second :: rest).length
            WorkSymbol.blank ++ leftMarker :: outsideLeft)
        head := pairSymbol first second
        right := packedSymbols rest ++ leftMarker ::
          terminalOutputPackerOutside
            (first :: second :: rest) outsideRight }

def terminalOutputPackerFinalConfiguration (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) : WorkConfiguration :=
  { state := terminalOutputPacker.acceptState
    tape := terminalOutputPackerFinalTape bits outsideLeft outsideRight }

private theorem dataSymbol_ofBool_eq_bitSymbol (bit : Bool) :
    dataSymbol (TapeSymbol.ofBool bit) = bitSymbol bit := by
  cases bit <;> rfl

private theorem map_data_ofBool_eq_bitSymbols (bits : BitString) :
    (bits.map TapeSymbol.ofBool).map dataSymbol = bitSymbols bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit with
      | false => exact congrArg (List.cons WorkSymbol.zeroBlank) ih
      | true => exact congrArg (List.cons WorkSymbol.oneBlank) ih

private theorem map_dataOfBool_comp_eq_bitSymbols (bits : BitString) :
    bits.map (dataSymbol ∘ TapeSymbol.ofBool) = bitSymbols bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit with
      | false => exact congrArg (List.cons WorkSymbol.zeroBlank) ih
      | true => exact congrArg (List.cons WorkSymbol.oneBlank) ih

/-- Every canonical represented output, with arbitrary exterior garbage,
reaches the explicit packed accept configuration in exactly the displayed
number of successful work transitions. -/
theorem terminalOutputPacker_workRunExact (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    workRunExact? terminalOutputPacker (terminalOutputPackerWorkSteps bits)
        (workStartConfiguration terminalOutputPacker
          (terminalOutputPackerInputTape bits outsideLeft outsideRight)) =
      some (terminalOutputPackerFinalConfiguration
        bits outsideLeft outsideRight) := by
  cases bits with
  | nil =>
      apply workRunExact_one
      dsimp [terminalOutputPackerWorkSteps, terminalOutputPackerInputTape,
        terminalOutputPackerFinalConfiguration,
        terminalOutputPackerFinalTape, frameWithGarbage, Tape.ofInput,
        workStartConfiguration]
      exact start_empty_step (leftMarker :: outsideLeft)
        (rightMarker :: outsideRight)
  | cons first tail =>
      cases tail with
      | nil =>
          have hFirst := first_single_iteration_exact 1 first
            outsideLeft outsideRight rfl
          have hLoop := packed_loop_exact [] 1 1 (bitSymbol first) []
            outsideLeft (outsideTail (outsideTail outsideRight)) rfl
            (by
              intro symbol found
              cases found with
              | head => exact bitSymbol_outputCell first
              | tail _ tailMem => contradiction)
          have complete := workRunExact_compose terminalOutputPacker
            (2 * 1 + 6) (packedLoopSteps 1 [bitSymbol first].length [])
            (configAtWord startState (leftMarker :: outsideLeft)
              (bitSymbol first :: rightMarker :: outsideRight))
            (packedLoopConfiguration 1 [] [bitSymbol first]
              outsideLeft (outsideTail (outsideTail outsideRight)))
            (packedFinalConfiguration 1 [bitSymbol first] outsideLeft
              (outsideTail (outsideTail outsideRight)))
            hFirst hLoop
          simpa only [terminalOutputPackerWorkSteps,
            terminalOutputPackerInputTape,
            terminalOutputPackerFinalConfiguration,
            terminalOutputPackerFinalTape, terminalOutputPackerOutside,
            packedLoopSteps, packedLoopOutside, packedSymbols,
            packedFinalConfiguration,
            frameWithGarbage, Tape.ofInput, workStartConfiguration,
            terminalOutputPacker, dataSymbol_ofBool_eq_bitSymbol,
            map_data_ofBool_eq_bitSymbols, pushLeft_replicate,
            pushLeft_single_blank, configAtWord, tapeAtWord,
            listNil_append, listCons_append, listAppend_nil,
            listAppend_assoc, List.length, List.map, Nat.zero_add,
            Nat.add_zero, Nat.mul_zero, Nat.mul_one] using complete
      | cons second rest =>
          let total := (first :: second :: rest).length
          have hFirst := first_pair_iteration_exact total first second rest
            outsideLeft outsideRight rfl
          have hLoopTotal : 2 + rest.length = total := by
            dsimp [total]
            calc
              2 + rest.length = rest.length + 2 := Nat.add_comm 2 rest.length
              _ = rest.length + 1 + 1 := rfl
          have hLoop := packed_loop_exact rest total 2
            (pairSymbol first second) [] outsideLeft
            (outsideTail (outsideTail outsideRight)) hLoopTotal
            (by
              intro symbol found
              cases found with
              | head => exact pairSymbol_outputCell first second
              | tail _ tailMem => contradiction)
          have complete := workRunExact_compose terminalOutputPacker
            (2 * total + 6)
            (packedLoopSteps total [pairSymbol first second].length rest)
            (configAtWord startState (leftMarker :: outsideLeft)
              (bitSymbol first :: bitSymbol second :: bitSymbols rest ++
                rightMarker :: outsideRight))
            (packedLoopConfiguration 2 rest [pairSymbol first second]
              outsideLeft (outsideTail (outsideTail outsideRight)))
            (packedFinalConfiguration total
              (pairSymbol first second :: packedSymbols rest)
              outsideLeft
              (packedLoopOutside rest
                (outsideTail (outsideTail outsideRight))))
            hFirst hLoop
          dsimp [total] at complete ⊢
          simpa only [terminalOutputPackerWorkSteps,
            terminalOutputPackerInputTape,
            terminalOutputPackerFinalConfiguration,
            terminalOutputPackerFinalTape, terminalOutputPackerOutside,
            packedLoopSteps, packedSymbols, packedFinalConfiguration,
            frameWithGarbage, Tape.ofInput, workStartConfiguration,
            terminalOutputPacker, dataSymbol_ofBool_eq_bitSymbol,
            map_data_ofBool_eq_bitSymbols,
            map_dataOfBool_comp_eq_bitSymbols, pushLeft_replicate,
            configAtWord, tapeAtWord,
            listNil_append, listCons_append, listAppend_nil,
            listAppend_assoc, List.length, List.map, Nat.zero_add,
            Nat.add_zero, Nat.mul_zero, Nat.mul_one] using complete

/-- Every exported terminal configuration is the packer's designated accept
halt. -/
theorem terminalOutputPackerFinal_isHalted (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    terminalOutputPacker.isHalted
      (terminalOutputPackerFinalConfiguration
        bits outsideLeft outsideRight) = true := by
  rfl

private theorem decode_packedSymbols (bits : BitString) :
    ∀ suffix,
      Tape.decodeOutputCells
          (encodeWorkRight
            (packedSymbols bits ++ leftMarker :: suffix)) = bits := by
  apply bitString_twoStepInduction
    (Property := fun bits => ∀ suffix,
      Tape.decodeOutputCells
          (encodeWorkRight
            (packedSymbols bits ++ leftMarker :: suffix)) = bits)
  · intro suffix
    rfl
  · intro bit suffix
    cases bit <;> rfl
  · intro first second rest ih suffix
    cases first <;> cases second
    all_goals
      apply congrArg (List.cons _)
      apply congrArg (List.cons _)
      exact ih suffix

/-- The ordinary raw blank-delimited output convention reads exactly the
logical input word from the packed final work tape. -/
theorem terminalOutputPacker_output_eq (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    Tape.outputBits
        (encodeWorkTape
          (terminalOutputPackerFinalTape
            bits outsideLeft outsideRight)) = bits := by
  cases bits with
  | nil => rfl
  | cons first tail =>
      cases tail with
      | nil =>
          simpa only [terminalOutputPackerFinalTape, packedSymbols,
            Tape.outputBits, encodeWorkTape, encodeWorkRight,
            listNil_append, listCons_append, listAppend_nil] using
            decode_packedSymbols [first]
              (terminalOutputPackerOutside [first] outsideRight)
      | cons second rest =>
          simpa only [terminalOutputPackerFinalTape, packedSymbols,
            Tape.outputBits, encodeWorkTape, encodeWorkRight,
            listNil_append, listCons_append, listAppend_nil,
            listAppend_assoc] using
            decode_packedSymbols (first :: second :: rest)
              (terminalOutputPackerOutside
                (first :: second :: rest) outsideRight)

/-- Compilation simulates the exact terminal-packer trace at six raw
transitions per proved work transition.  Its start is an encoded internal
pipeline configuration, not a raw external `startConfig`. -/
theorem run_compileTerminalOutputPacker_exact (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    run (compileWorkMachine terminalOutputPacker)
        (6 * terminalOutputPackerWorkSteps bits)
        (encodeWorkConfiguration
          (workStartConfiguration terminalOutputPacker
            (terminalOutputPackerInputTape
              bits outsideLeft outsideRight))) =
      encodeWorkConfiguration
        (terminalOutputPackerFinalConfiguration
          bits outsideLeft outsideRight) := by
  exact run_compileWorkMachine_mul_of_workRunExact terminalOutputPacker
    (terminalOutputPackerWorkSteps bits)
    (workStartConfiguration terminalOutputPacker
      (terminalOutputPackerInputTape bits outsideLeft outsideRight))
    (terminalOutputPackerFinalConfiguration bits outsideLeft outsideRight)
    (terminalOutputPacker_workRunExact bits outsideLeft outsideRight)

private theorem threeMulSafe (value : Nat) :
    3 * value = 2 * value + value := by
  exact Nat.succ_mul 2 value

private theorem addMulSafe (left right multiplier : Nat) :
    (left + right) * multiplier =
      left * multiplier + right * multiplier := by
  induction multiplier with
  | zero => rfl
  | succ multiplier ih =>
      calc
        (left + right) * (multiplier + 1) =
            (left + right) * multiplier + (left + right) := rfl
        _ = (left * multiplier + right * multiplier) +
              (left + right) :=
          congrArg (fun value => value + (left + right)) ih
        _ = ((left * multiplier + right * multiplier) + left) + right :=
          (addAssocSafe
            (left * multiplier + right * multiplier) left right).symm
        _ = ((left * multiplier + left) + right * multiplier) + right :=
          congrArg (fun value => value + right)
            (addSwapMiddleSafe
              (left * multiplier) (right * multiplier) left)
        _ = (left * multiplier + left) +
              (right * multiplier + right) :=
          addAssocSafe (left * multiplier + left)
            (right * multiplier) right
        _ = left * (multiplier + 1) + right * (multiplier + 1) := rfl

private theorem mulAssocSafe (left middle right : Nat) :
    (left * middle) * right = left * (middle * right) := by
  induction right with
  | zero => rfl
  | succ right ih =>
      calc
        (left * middle) * (right + 1) =
            (left * middle) * right + left * middle := rfl
        _ = left * (middle * right) + left * middle :=
          congrArg (fun value => value + left * middle) ih
        _ = left * (middle * right + middle) :=
          (Nat.mul_add left (middle * right) middle).symm
        _ = left * (middle * (right + 1)) := rfl

private theorem packedCost_le_of_one (total outputCells : Nat)
    (hInvariant : 2 * outputCells + 1 ≤ total) :
    2 * total + 2 * outputCells + 6 ≤ 3 * total + 5 := by
  have hAdded := Nat.add_le_add_left hInvariant (2 * total + 5)
  have hLeft :
      (2 * total + 5) + (2 * outputCells + 1) =
        2 * total + 2 * outputCells + 6 := by
    calc
      (2 * total + 5) + (2 * outputCells + 1) =
          ((2 * total + 5) + 2 * outputCells) + 1 :=
        (addAssocSafe (2 * total + 5) (2 * outputCells) 1).symm
      _ = ((2 * total + 2 * outputCells) + 5) + 1 :=
        congrArg (fun value => value + 1)
          (addSwapMiddleSafe (2 * total) 5 (2 * outputCells))
      _ = (2 * total + 2 * outputCells) + (5 + 1) :=
        addAssocSafe (2 * total + 2 * outputCells) 5 1
      _ = 2 * total + 2 * outputCells + 6 := rfl
  have hRight : (2 * total + 5) + total = 3 * total + 5 := by
    calc
      (2 * total + 5) + total = (2 * total + total) + 5 :=
        addSwapMiddleSafe (2 * total) 5 total
      _ = 3 * total + 5 :=
        congrArg (fun value => value + 5) (threeMulSafe total).symm
  rw [hLeft, hRight] at hAdded
  exact hAdded

private theorem nextInvariantArithmetic (outputCells restLength : Nat) :
    2 * (outputCells + 1) + restLength =
      2 * outputCells + (restLength + 1 + 1) := by
  change (2 * outputCells + 2) + restLength = _
  exact addTwoBefore (2 * outputCells) restLength

private theorem loopTailSlack (restLength coefficient total : Nat) :
    coefficient + (restLength * coefficient + total + 1) ≤
      (restLength + 1 + 1) * coefficient + total + 1 := by
  have hAdd := Nat.le_add_right
    (coefficient + (restLength * coefficient + total + 1)) coefficient
  have hReorder :
      (coefficient + (restLength * coefficient + total + 1)) + coefficient =
        ((restLength * coefficient + coefficient) + coefficient) + total + 1 := by
    calc
      (coefficient + (restLength * coefficient + total + 1)) + coefficient =
          ((coefficient + restLength * coefficient) + (total + 1)) +
            coefficient :=
        congrArg (fun value => value + coefficient)
          (addAssocSafe coefficient (restLength * coefficient)
            (total + 1)).symm
      _ = ((coefficient + restLength * coefficient) + coefficient) +
            (total + 1) :=
        addSwapMiddleSafe (coefficient + restLength * coefficient)
          (total + 1) coefficient
      _ = ((restLength * coefficient + coefficient) + coefficient) +
            (total + 1) :=
        congrArg (fun value => (value + coefficient) + (total + 1))
          (addCommSafe coefficient (restLength * coefficient))
      _ = (((restLength * coefficient + coefficient) + coefficient) +
            total) + 1 :=
        (addAssocSafe
          ((restLength * coefficient + coefficient) + coefficient)
          total 1).symm
  have hExpanded :
      (restLength + 1 + 1) * coefficient + total + 1 =
        ((restLength * coefficient + coefficient) + coefficient) +
          total + 1 := by
    rw [addMulSafe, addMulSafe, Nat.one_mul]
  rw [hReorder, ← hExpanded] at hAdd
  exact hAdd

private theorem packedLoopSteps_le (remaining : BitString) :
    ∀ total outputCells,
      2 * outputCells + remaining.length ≤ total →
      packedLoopSteps total outputCells remaining ≤
        remaining.length * (3 * total + 5) + total + 1 := by
  apply bitString_twoStepInduction
    (Property := fun remaining =>
      ∀ total outputCells,
        2 * outputCells + remaining.length ≤ total →
        packedLoopSteps total outputCells remaining ≤
          remaining.length * (3 * total + 5) + total + 1)
  · intro total outputCells _
    simp only [packedLoopSteps, List.length_nil, Nat.zero_mul, Nat.zero_add]
    exact Nat.le_refl _
  · intro bit total outputCells hInvariant
    have hCost : 2 * total + 2 * outputCells + 6 ≤
        3 * total + 5 := by
      change 2 * outputCells + 1 ≤ total at hInvariant
      exact packedCost_le_of_one total outputCells hInvariant
    simp only [packedLoopSteps, List.length_cons, List.length_nil,
      Nat.zero_add]
    calc
      (2 * total + 2 * outputCells + 6) + (total + 1) =
          ((2 * total + 2 * outputCells + 6) + total) + 1 :=
        (addAssocSafe (2 * total + 2 * outputCells + 6) total 1).symm
      _ ≤ ((3 * total + 5) + total) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_right hCost total) 1
      _ = 1 * (3 * total + 5) + total + 1 :=
        congrArg (fun value => value + total + 1)
          (Nat.one_mul (3 * total + 5)).symm
  · intro first second rest ih total outputCells hInvariant
    have hCost : 2 * total + 2 * outputCells + 6 ≤
        3 * total + 5 := by
      change 2 * outputCells + (rest.length + 1 + 1) ≤ total at hInvariant
      have hOneWithin : 2 * outputCells + 1 ≤
          2 * outputCells + (rest.length + 1 + 1) :=
        Nat.add_le_add_left (Nat.le_add_left 1 (rest.length + 1))
          (2 * outputCells)
      exact packedCost_le_of_one total outputCells
        (Nat.le_trans hOneWithin hInvariant)
    have hNext : 2 * (outputCells + 1) + rest.length ≤ total := by
      change 2 * outputCells + (rest.length + 1 + 1) ≤ total at hInvariant
      rw [nextInvariantArithmetic]
      exact hInvariant
    have hTail := ih total (outputCells + 1) hNext
    change
      (2 * total + 2 * outputCells + 6) +
          packedLoopSteps total (outputCells + 1) rest ≤
        (rest.length + 1 + 1) * (3 * total + 5) + total + 1
    calc
      (2 * total + 2 * outputCells + 6) +
            packedLoopSteps total (outputCells + 1) rest ≤
          (3 * total + 5) +
            (rest.length * (3 * total + 5) + total + 1) :=
        Nat.add_le_add hCost hTail
      _ ≤ (rest.length + 1 + 1) * (3 * total + 5) +
          total + 1 := by
        exact loopTailSlack rest.length (3 * total + 5) total

private theorem terminalOutputPackerWorkSteps_le (bits : BitString) :
    terminalOutputPackerWorkSteps bits ≤
      bits.length * (3 * bits.length + 5) + bits.length + 1 := by
  cases bits with
  | nil => exact Nat.le_refl _
  | cons first rest =>
      change packedLoopSteps (first :: rest).length 0 (first :: rest) ≤ _
      apply packedLoopSteps_le (first :: rest) (first :: rest).length 0
      rw [Nat.mul_zero, Nat.zero_add]
      exact Nat.le_refl _

private theorem mulLinearTerms (left right input : Nat) :
    (left * input) * (right * input) =
      (left * right) * input * input := by
  calc
    (left * input) * (right * input) =
        ((left * input) * right) * input :=
      (mulAssocSafe (left * input) right input).symm
    _ = (right * (left * input)) * input :=
      congrArg (fun value => value * input)
        (Nat.mul_comm (left * input) right)
    _ = ((right * left) * input) * input :=
      congrArg (fun value => value * input)
        (mulAssocSafe right left input).symm
    _ = ((left * right) * input) * input :=
      congrArg (fun value => value * input)
        (congrArg (fun value => value * input)
          (Nat.mul_comm right left))

private theorem mulRightCoefficient (left input right : Nat) :
    left * (input * right) = (left * right) * input := by
  calc
    left * (input * right) = (left * input) * right :=
      (mulAssocSafe left input right).symm
    _ = right * (left * input) := Nat.mul_comm _ _
    _ = (right * left) * input :=
      (mulAssocSafe right left input).symm
    _ = (left * right) * input :=
      congrArg (fun value => value * input) (Nat.mul_comm right left)

private theorem scaledLoopBody (length : Nat) :
    6 * (length * (3 * length + 5)) =
      18 * length * length + 30 * length := by
  calc
    6 * (length * (3 * length + 5)) =
        6 * (length * (3 * length) + length * 5) :=
      congrArg (Nat.mul 6) (Nat.mul_add length (3 * length) 5)
    _ = 6 * (length * (3 * length)) + 6 * (length * 5) :=
      Nat.mul_add 6 _ _
    _ = (6 * length) * (3 * length) + 6 * (length * 5) :=
      congrArg (fun value => value + 6 * (length * 5))
        (mulAssocSafe 6 length (3 * length)).symm
    _ = (6 * 3) * length * length + 6 * (length * 5) :=
      congrArg (fun value => value + 6 * (length * 5))
        (mulLinearTerms 6 3 length)
    _ = 18 * length * length + (6 * 5) * length :=
      congrArg (Nat.add (18 * length * length))
        (mulRightCoefficient 6 length 5)
    _ = 18 * length * length + 30 * length := rfl

private theorem terminalRawBoundArithmetic (length : Nat) :
    6 * (length * (3 * length + 5) + length + 1) =
      (18 * length * length + 6) + (36 * length + 0) := by
  calc
    6 * (length * (3 * length + 5) + length + 1) =
        6 * (length * (3 * length + 5) + length) + 6 :=
      Nat.mul_add 6 _ 1
    _ = (6 * (length * (3 * length + 5)) + 6 * length) + 6 :=
      congrArg (fun value => value + 6)
        (Nat.mul_add 6 (length * (3 * length + 5)) length)
    _ = (18 * length * length + 30 * length + 6 * length) + 6 :=
      congrArg (fun value => (value + 6 * length) + 6)
        (scaledLoopBody length)
    _ = (18 * length * length +
          (30 * length + 6 * length)) + 6 :=
      congrArg (fun value => value + 6)
        (addAssocSafe (18 * length * length)
          (30 * length) (6 * length))
    _ = (18 * length * length + 36 * length) + 6 := by
      have hLinear : 30 * length + 6 * length = 36 * length := by
        calc
          30 * length + 6 * length = (30 + 6) * length :=
            (addMulSafe 30 6 length).symm
          _ = 36 * length := rfl
      exact congrArg
        (fun value => (18 * length * length + value) + 6) hLinear
    _ = (18 * length * length + 6) + 36 * length :=
      addSwapMiddleSafe (18 * length * length) (36 * length) 6
    _ = (18 * length * length + 6) + (36 * length + 0) := rfl

/-- Six raw compiler transitions per proved work step fit the explicit
quadratic polynomial in the logical output length. -/
theorem terminalOutputPacker_runtime_le (bits : BitString) :
    6 * terminalOutputPackerWorkSteps bits ≤
      terminalOutputPackerRawTimeBound.eval bits.length := by
  have hScaled := Nat.mul_le_mul_left 6
    (terminalOutputPackerWorkSteps_le bits)
  calc
    6 * terminalOutputPackerWorkSteps bits ≤
        6 * (bits.length * (3 * bits.length + 5) + bits.length + 1) :=
      hScaled
    _ = terminalOutputPackerRawTimeBound.eval bits.length := by
      change
        6 * (bits.length * (3 * bits.length + 5) + bits.length + 1) =
          (18 * bits.length * bits.length + 6) +
            (36 * bits.length + 0)
      exact terminalRawBoundArithmetic bits.length

/-- At the advertised raw polynomial budget, compilation reaches the exact
encoded packed accept configuration and remains there. -/
theorem run_compileTerminalOutputPacker (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    run (compileWorkMachine terminalOutputPacker)
        (terminalOutputPackerRawTimeBound.eval bits.length)
        (encodeWorkConfiguration
          (workStartConfiguration terminalOutputPacker
            (terminalOutputPackerInputTape
              bits outsideLeft outsideRight))) =
      encodeWorkConfiguration
        (terminalOutputPackerFinalConfiguration
          bits outsideLeft outsideRight) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    terminalOutputPacker (terminalOutputPackerWorkSteps bits)
    (terminalOutputPackerRawTimeBound.eval bits.length)
    (workStartConfiguration terminalOutputPacker
      (terminalOutputPackerInputTape bits outsideLeft outsideRight))
    (terminalOutputPackerFinalConfiguration bits outsideLeft outsideRight)
    (terminalOutputPacker_workRunExact bits outsideLeft outsideRight)
    (terminalOutputPackerFinal_isHalted bits outsideLeft outsideRight)
    (terminalOutputPacker_runtime_le bits)

/-- Raw blank-delimited output after the compiled run equals the logical word.
Despite the compatibility-oriented name, the run starts from an encoded
internal pipeline configuration, not from external `startConfig`. -/
theorem machineOutput_compileTerminalOutputPacker_eq (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    Tape.outputBits
        (run (compileWorkMachine terminalOutputPacker)
          (terminalOutputPackerRawTimeBound.eval bits.length)
          (encodeWorkConfiguration
            (workStartConfiguration terminalOutputPacker
              (terminalOutputPackerInputTape
                bits outsideLeft outsideRight)))).tape = bits := by
  rw [run_compileTerminalOutputPacker bits outsideLeft outsideRight]
  exact terminalOutputPacker_output_eq bits outsideLeft outsideRight

private theorem workRunExact_succ_split_last (machine : WorkMachine) :
    ∀ (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? machine (steps + 1) initial = some final →
      ∃ before,
        workRunExact? machine steps initial = some before ∧
        workStep? machine before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final hRun
      cases hStep : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => some next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hNext : next = final := by
            change
              (match workStep? machine initial with
               | none => none
               | some next => some next) = some final at hRun
            rw [hStep] at hRun
            exact Option.some.inj hRun
          subst final
          exact ⟨initial, rfl, hStep⟩
  | succ steps ih =>
      intro initial final hRun
      cases hStep : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => workRunExact? machine (steps + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? machine (steps + 1) next =
              some final := by
            change
              (match workStep? machine initial with
               | none => none
               | some next => workRunExact? machine (steps + 1) next) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases ih next final hTail with ⟨before, hPrefix, hLast⟩
          refine ⟨before, ?_, hLast⟩
          change
            (match workStep? machine initial with
             | none => none
             | some next => workRunExact? machine steps next) = some before
          rw [hStep]
          exact hPrefix

private theorem isHalted_false_of_workStep_some (machine : WorkMachine)
    (config next : WorkConfiguration)
    (hStep : workStep? machine config = some next) :
    machine.isHalted config = false := by
  cases hHalted : machine.isHalted config with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

private theorem positive_of_six_add (value suffix : Nat) :
    0 < (value + 6) + suffix := by
  have hSix : 6 ≤ value + 6 := Nat.le_add_left 6 value
  have hTotal : 6 ≤ (value + 6) + suffix :=
    Nat.le_trans hSix (Nat.le_add_right (value + 6) suffix)
  exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 5) hTotal

private theorem terminalOutputPackerWorkSteps_pos (bits : BitString) :
    0 < terminalOutputPackerWorkSteps bits := by
  cases bits with
  | nil =>
      dsimp [terminalOutputPackerWorkSteps]
      exact Nat.zero_lt_succ 0
  | cons first rest =>
      cases rest with
      | nil =>
          dsimp [terminalOutputPackerWorkSteps, packedLoopSteps]
          exact Nat.zero_lt_succ 9
      | cons second tail =>
          dsimp [terminalOutputPackerWorkSteps, packedLoopSteps]
          exact positive_of_six_add _ _

private theorem subOneAddOne_of_pos (value : Nat) :
    0 < value → value - 1 + 1 = value := by
  cases value with
  | zero =>
      intro impossible
      contradiction
  | succ value =>
      intro _
      rfl

/-- Removing exactly one proved work transition leaves a nonhalting state, so
the bounded verdict is timeout rather than an accidental rejection. -/
theorem terminalOutputPacker_one_step_short_timeout (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    workBoundedDecide terminalOutputPacker
        (terminalOutputPackerWorkSteps bits - 1)
        (terminalOutputPackerInputTape bits outsideLeft outsideRight) =
      .timeout := by
  let short := terminalOutputPackerWorkSteps bits - 1
  let initial := workStartConfiguration terminalOutputPacker
    (terminalOutputPackerInputTape bits outsideLeft outsideRight)
  let final := terminalOutputPackerFinalConfiguration
    bits outsideLeft outsideRight
  have hSucc : short + 1 = terminalOutputPackerWorkSteps bits := by
    dsimp [short]
    have hPositive := terminalOutputPackerWorkSteps_pos bits
    exact subOneAddOne_of_pos (terminalOutputPackerWorkSteps bits) hPositive
  have hExact := terminalOutputPacker_workRunExact
    bits outsideLeft outsideRight
  change workRunExact? terminalOutputPacker
      (terminalOutputPackerWorkSteps bits) initial = some final at hExact
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last terminalOutputPacker short initial final
      hExact with ⟨before, hPrefix, hLast⟩
  have hRun : workRun terminalOutputPacker short initial = before :=
    workRun_eq_of_workRunExact terminalOutputPacker short initial before hPrefix
  have hNotHalted : terminalOutputPacker.isHalted before = false :=
    isHalted_false_of_workStep_some terminalOutputPacker before final hLast
  cases hAccept : (before.state == terminalOutputPacker.acceptState) with
  | true =>
      unfold WorkMachine.isHalted at hNotHalted
      rw [hAccept] at hNotHalted
      contradiction
  | false =>
      cases hReject : (before.state == terminalOutputPacker.rejectState) with
      | true =>
          unfold WorkMachine.isHalted at hNotHalted
          rw [hAccept, hReject] at hNotHalted
          contradiction
      | false =>
          dsimp [short, initial] at hRun ⊢
          unfold workBoundedDecide
          dsimp
          rw [hRun, hAccept, hReject]
          rfl

end TerminalOutputPacker

end PNP.Concrete
